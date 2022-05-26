{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE StrictData            #-}

module PlutusCore.Builtin.KnownType
    ( KnownTypeError
    , throwKnownTypeErrorWithCause
    , KnownBuiltinTypeIn
    , KnownBuiltinType
    , MakeKnownM (..)
    , ReadKnownM
    , liftReadKnownM
    , readKnownConstant
    , MakeKnownIn (..)
    , MakeKnown
    , ReadKnownIn (..)
    , ReadKnown
    , makeKnownOrFail
    , readKnownSelf
    ) where

import PlutusCore.Builtin.Emitter
import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result

import Control.Monad.Except
import Data.Coerce
import Data.DList (DList)
import Data.Either.Extras
import Data.String
import Data.Text (Text)
import GHC.Exts (inline, oneShot)
import GHC.TypeLits
import Universe

-- | A constraint for \"@a@ is a 'ReadKnownIn' and 'MakeKnownIn' by means of being included
-- in @uni@\".
type KnownBuiltinTypeIn uni val a = (HasConstantIn uni val, GShow uni, GEq uni, uni `Contains` a)

-- | A constraint for \"@a@ is a 'ReadKnownIn' and 'MakeKnownIn' by means of being included
-- in @UniOf term@\".
type KnownBuiltinType val a = KnownBuiltinTypeIn (UniOf val) val a

{- Note [Performance of ReadKnownIn and MakeKnownIn instances]
It's critically important that 'readKnown' runs in the concrete 'Either' rather than a general
'MonadError'. Changing from the latter to the former gave us a speedup of up to 19%, see
https://github.com/input-output-hk/plutus/pull/4307

Replacing the @AsUnliftingError err, AsEvaluationFailure err@ constraints with the dedicated
'KnownTypeError' data type gave us a speedup of up to 4%.

All the same considerations apply to 'makeKnown': https://github.com/input-output-hk/plutus/pull/4421

It's beneficial to inline 'readKnown' and 'makeKnown' not only because we use them directly over
concrete types once 'toBuiltinsRuntime' is inlined, but also because otherwise GHC compiles each of
them to two definitions (one calling the other) for some reason.
So always add an @INLINE@ pragma to all definitions of 'makeKnown' and 'readKnown' unless you have
a specific reason not to.

Some 'readKnown' implementations require inserting a call to 'oneShot'. E.g. if 'oneShot' is not
used in 'readKnownConstant' then 'GHC pulls @gshow uniExp@ out of the 'Nothing' branch, thus
allocating a thunk of type 'String' that is completely redundant whenever there's no error,
which is the majority of cases. And putting 'oneShot' as the outermost call results in
worse Core.

Any change to an instance of 'ReadKnownIn' or 'MakeKnownIn', even completely trivial, requires
looking into the generated Core, since compilation of these instances is extremely brittle
optimization-wise.

Things to watch out for are unnecessary sharing (for example, a @let@ appearing outside of a @case@
allocates a thunk and if that thunk is not referenced inside of one of the branches, then it's
wasteful, especially when it's not referenced in the most commonly chosen branch) and type class
methods not being extracted from the dictionary and used directly instead (i.e. if you see
multiple @pure@ and @>>=@ in the code, that's not good). Note that neither @let@ nor @>>=@ are bad
in general, we certainly do need to allocate thunks occasionally, it's just that when it comes to
builtins this is rarely the case as most of the time we want aggressive inlining and specialization
and the "just compute the damn thing" behavior.
-}

{- Note [Unlifting values of built-in types]
It's trivial to unlift from a term a value of a monomorphic type like 'Integer': just check that
the term is a constant, extract the type tag and check it for equality with the type tag of
'Integer'.

Things work the same way for a fully monomorphized polymorphic type, i.e. @(Integer, Bool@) is not
any different from just 'Integer' unlifting-wise.

However there's no sensible way of unlifting a value of, say, @[a]@ where @a@ in not a built-in
type. So let's say we instantiated @a@ to an @Opaque val rep@ like we do for polymorphic functions
that don't deal with polymorphic built-in types (e.g. @id@, @ifThenElse@ etc). That would mean we'd
need to write a function from a @[a]@ for some arbitrary built-in @a@ to @[Opaque val a]@. Which
is really easy to do: it's just @map makeKnown@. But the problem is, unlifting is supposed to be
cheap and that @map@ is O(n), so for example 'MkCons' would become an O(n) operation making
perfectly linear algorithms quadratic. See https://github.com/input-output-hk/plutus/pull/4215 for
how that would look like.

So the problem is that we can't convert in O(1) time a @[a]@ coming from a constant of
statically-unknown type (that @a@ is existential) to @[a']@ where @a'@ is known statically.
Thus it's impossible to instantiate @a@ in Haskell's

    nullList :: [a] -> Bool

so that there's a 'TypeScheme' for this function.

One non-solution would be to instantiate @a@, then recurse on the type, construct a new function
that defers to the original @nullList@ but wraps its argument in a specific way (more on that below)
making it possible to assign a 'TypeScheme' to the resulting function. Astonishingly enough, that
could actually work and if we ever write a paper on builtins, we should mention that example, but:

1. such a trick requires a generic machinery that knows how to check that the head of the builtin
   application is a particular built-in type. We used to have that, but it was just way too slow
2. that would only work for functions that don't care about @a@ at all. But for example when
   elaborating @cons :: a -> [a] -> [a]@ as a Plutus builtin we need to unlift both the arguments
   and check that their @a@s are equal
   (See Note [Representable built-in functions over polymorphic built-in types])
   and it's either way too complex or even impossible to do that automatically within some generic
   machinery

So what we do is we simply require the user to write

    nullList :: SomeConstant uni [a] -> Bool

and unlift a @[a]@ manually within the definition of the builtin. This works, because the
existential @a@ never escapes the definition of the builtin. I.e. it's fine to unpack an existential
and use it immediately without ever exposing the existential parts to the outside and it's not fine
to try to return a value having an existential inside of it, which is what unlifting of @[a]@ would
amount to.

Could we somehow align the unlifting machinery so that it does not construct values of particular
types, but rather feeds them to a continuation or something, so that the existential parts never
try to escape? Maybe, but see point 2 from the above, we do want to get our hands on the particular
universes sometimes and point 1 prevents us from doing that generically, so it doesn't seem like
we could do that within some automated machinery.

Overall, asking the user to manually unlift from @SomeConstant uni [a]@ is just always going to be
faster than any kind of fancy encoding.
-}

{- Note [Alignment of ReadKnownIn and MakeKnownIn]
We keep 'ReadKnownIn' and 'MakeKnownIn' separate, because values of some types can only be lifted
and not unlifted, for example 'EvaluationResult' and 'Emitter' can't appear in argument position.

'KnownTypeAst' is not a superclass of ReadKnownIn and MakeKnownIn. This is due to the fact that
polymorphic built-in types are only liftable/unliftable when they're fully monomorphized, while
'toTypeAst' works for polymorphic built-in types that have type variables in them, and so the
constraints are completely different in the two cases and we keep the two concepts apart
(there doesn't seem to be any cons to that).
-}

-- | Throw a @ErrorWithCause KnownTypeError cause@.
throwKnownTypeErrorWithCause
    :: (MonadError (ErrorWithCause err cause) m, AsUnliftingError err, AsEvaluationFailure err)
    => cause -> KnownTypeError -> m void
throwKnownTypeErrorWithCause cause = \case
    KnownTypeUnliftingError unlErr -> throwingWithCause _UnliftingError unlErr $ Just cause
    KnownTypeEvaluationFailure     -> throwingWithCause _EvaluationFailure () $ Just cause

typeMismatchError
    :: GShow uni
    => uni (Esc a)
    -> uni (Esc b)
    -> UnliftingError
typeMismatchError uniExp uniAct = fromString $ concat
    [ "Type mismatch: "
    , "expected: " ++ gshow uniExp
    , "; actual: " ++ gshow uniAct
    ]
-- Just for tidier Core to get generated, we don't care about performance here, since it's just a
-- failure message and evaluation is about to be shut anyway.
{-# NOINLINE typeMismatchError #-}

-- | The monad that 'makeKnown' runs in.
-- Equivalent to @ExceptT KnownTypeError Emitter@, except optimized in two ways:
--
-- 1. everything is strict
-- 2. has the 'MakeKnownSuccess' constructor that is used for returning a value with no logs
--    attached, which is the most common case for us, so it helps a lot not to construct and
--    deconstruct a redundant tuple
--
-- Moving from @ExceptT KnownTypeError Emitter@ to this data type gave us a speedup of 8% of total
-- evaluation time.
--
-- Logs are represented as a 'DList', because we don't particularly care about the efficiency of
-- logging, since there's no logging on the chain and builtins don't emit much anyway. Otherwise
-- we'd have to use @text-builder@ or @text-builder-linear@ or something of this sort.
data MakeKnownM a
    = MakeKnownFailure (DList Text) KnownTypeError
    | MakeKnownSuccess a
    | MakeKnownSuccessWithLogs (DList Text) a

-- | Prepend logs to a 'MakeKnownM' computation.
withLogs :: DList Text -> MakeKnownM a -> MakeKnownM a
withLogs logs1 = \case
    MakeKnownFailure logs2 err       -> MakeKnownFailure (logs1 <> logs2) err
    MakeKnownSuccess x               -> MakeKnownSuccessWithLogs logs1 x
    MakeKnownSuccessWithLogs logs2 x -> MakeKnownSuccessWithLogs (logs1 <> logs2) x
{-# INLINE withLogs #-}

instance Functor MakeKnownM where
    fmap _ (MakeKnownFailure logs err)       = MakeKnownFailure logs err
    fmap f (MakeKnownSuccess x)              = MakeKnownSuccess (f x)
    fmap f (MakeKnownSuccessWithLogs logs x) = MakeKnownSuccessWithLogs logs (f x)
    {-# INLINE fmap #-}

    -- Written out explicitly just in case (see @fmap@ above for what the case might be).
    _ <$ MakeKnownFailure logs err       = MakeKnownFailure logs err
    x <$ MakeKnownSuccess _              = MakeKnownSuccess x
    x <$ MakeKnownSuccessWithLogs logs _ = MakeKnownSuccessWithLogs logs x
    {-# INLINE (<$) #-}

instance Applicative MakeKnownM where
    pure = MakeKnownSuccess
    {-# INLINE pure #-}

    MakeKnownFailure logs err       <*> _ = MakeKnownFailure logs err
    MakeKnownSuccess f              <*> a = fmap f a
    MakeKnownSuccessWithLogs logs f <*> a = withLogs logs $ fmap f a
    {-# INLINE (<*>) #-}

    -- Better than the default implementation, because the value in the 'MakeKnownSuccess' case
    -- doesn't need to be retained.
    MakeKnownFailure logs err       *> _ = MakeKnownFailure logs err
    MakeKnownSuccess _              *> a = a
    MakeKnownSuccessWithLogs logs _ *> a = withLogs logs a
    {-# INLINE (*>) #-}

instance Monad MakeKnownM where
    MakeKnownFailure logs err       >>= _ = MakeKnownFailure logs err
    MakeKnownSuccess x              >>= f = f x
    MakeKnownSuccessWithLogs logs x >>= f = withLogs logs $ f x
    {-# INLINE (>>=) #-}

    (>>) = (*>)
    {-# INLINE (>>) #-}

-- Normally it's a good idea for an exported abstraction not to be a type synonym, since a @newtype@
-- is cheap, looks good in error messages and clearly emphasize an abstraction barrier. However we
-- make 'ReadKnownM' type synonyms for convenience: that way we don't need to derive all the
-- instances (and add new ones whenever we need them), wrap and unwrap all the time
-- (including in user code), which can be non-trivial for such performance-sensitive code (see e.g.
-- 'coerceVia' and 'coerceArg') and there is no abstraction barrier anyway.
-- | The monad that 'readKnown' runs in.
type ReadKnownM = Either KnownTypeError

-- | Lift a 'ReadKnownM' computation into 'MakeKnownM'.
liftReadKnownM :: ReadKnownM a -> MakeKnownM a
liftReadKnownM (Left err) = MakeKnownFailure mempty err
liftReadKnownM (Right x)  = MakeKnownSuccess x
{-# INLINE liftReadKnownM #-}

-- See Note [Unlifting values of built-in types].
-- | Convert a constant embedded into a PLC term to the corresponding Haskell value.
readKnownConstant :: forall val a. KnownBuiltinType val a => val -> ReadKnownM a
-- Note [Performance of ReadKnownIn and MakeKnownIn instances]
readKnownConstant val = asConstant val >>= oneShot \case
    Some (ValueOf uniAct x) -> do
        let uniExp = knownUni @_ @(UniOf val) @a
        -- 'geq' matches on its first argument first, so we make the type tag that will be known
        -- statically (because this function will be inlined) go first in order for GHC to
        -- optimize some of the matching away.
        case uniExp `geq` uniAct of
            Just Refl -> pure x
            Nothing   -> Left . KnownTypeUnliftingError $ typeMismatchError uniExp uniAct
{-# INLINE readKnownConstant #-}

{- Note [Cause of failure]
'readKnown' and 'makeKnown' each take a @Maybe cause@ argument to report the cause of a potential
failure. @cause@ is different to @val@ to support evaluators that distinguish between terms and
values (@makeKnown@ normally constructs a value, but it's convenient to report the cause of a failure
as a term). Note that an evaluator might require the cause to be computed lazily for best
performance on the happy path and @Maybe@ ensures that even if we somehow force the argument,
the cause stored in it is not forced due to @Maybe@ being a lazy data type.
-}

-- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
class uni ~ UniOf val => MakeKnownIn uni val a where
    -- See Note [Cause of failure].
    -- | Convert a Haskell value to the corresponding PLC val.
    -- The inverse of 'readKnown'.
    makeKnown :: a -> MakeKnownM val
    default makeKnown :: KnownBuiltinType val a => a -> MakeKnownM val
    -- Everything on evaluation path has to be strict in production, so in theory we don't need to
    -- force anything here. In practice however all kinds of weird things happen in tests and @val@
    -- can be non-strict enough to cause trouble here, so we're forcing the argument. Looking at the
    -- generated Core, the forcing amounts to pulling a @case@ out of the 'fromConstant' call,
    -- which doesn't affect the overall cost and benchmarking results suggest the same.
    --
    -- Note that the value is only forced to WHNF, so care must be taken to ensure that every value
    -- of a type from the universe gets forced to NF whenever it's forced to WHNF.
    makeKnown x = pure . fromConstant . someValue $! x
    {-# INLINE makeKnown #-}

type MakeKnown val = MakeKnownIn (UniOf val) val

-- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
class uni ~ UniOf val => ReadKnownIn uni val a where
    -- See Note [Cause of failure].
    -- | Convert a PLC val to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown :: val -> ReadKnownM a
    default readKnown :: KnownBuiltinType val a => val -> ReadKnownM a
    -- If 'inline' is not used, proper inlining does not happen for whatever reason.
    readKnown = inline readKnownConstant
    {-# INLINE readKnown #-}

type ReadKnown val = ReadKnownIn (UniOf val) val

-- | Same as 'makeKnown', but allows for neither emitting nor storing the cause of a failure.
makeKnownOrFail :: MakeKnownIn uni val a => a -> EvaluationResult val
makeKnownOrFail x = case makeKnown x of
    MakeKnownFailure _ _           -> EvaluationFailure
    MakeKnownSuccess val           -> EvaluationSuccess val
    MakeKnownSuccessWithLogs _ val -> EvaluationSuccess val
{-# INLINE makeKnownOrFail #-}

-- | Same as 'readKnown', but the cause of a potential failure is the provided term itself.
readKnownSelf
    :: ( ReadKnown val a
       , AsUnliftingError err, AsEvaluationFailure err
       )
    => val -> Either (ErrorWithCause err val) a
readKnownSelf val = fromRightM (throwKnownTypeErrorWithCause val) $ readKnown val
{-# INLINE readKnownSelf #-}

instance MakeKnownIn uni val a => MakeKnownIn uni val (EvaluationResult a) where
    makeKnown EvaluationFailure     = MakeKnownFailure mempty KnownTypeEvaluationFailure
    makeKnown (EvaluationSuccess x) = makeKnown x
    {-# INLINE makeKnown #-}

-- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
-- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
-- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
-- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
-- I.e. it would essentially allow us to catch errors and handle them in a programmable way.
-- We forbid this, because it complicates code and isn't supported by evaluation engines anyway.
instance
        ( TypeError ('Text "‘EvaluationResult’ cannot appear in the type of an argument")
        , uni ~ UniOf val
        ) => ReadKnownIn uni val (EvaluationResult a) where
    readKnown _ = throwing _UnliftingError "Panic: 'TypeError' was bypassed"

instance MakeKnownIn uni val a => MakeKnownIn uni val (Emitter a) where
    makeKnown a = case runEmitter a of
        (x, logs) -> withLogs logs $ makeKnown x
    {-# INLINE makeKnown #-}

instance
        ( TypeError ('Text "‘Emitter’ cannot appear in the type of an argument")
        , uni ~ UniOf val
        ) => ReadKnownIn uni val (Emitter a) where
    readKnown _ = throwing _UnliftingError "Panic: 'TypeError' was bypassed"

instance HasConstantIn uni val => MakeKnownIn uni val (SomeConstant uni rep) where
    makeKnown = coerceArg $ pure . fromConstant
    {-# INLINE makeKnown #-}

instance HasConstantIn uni val => ReadKnownIn uni val (SomeConstant uni rep) where
    readKnown = coerceVia (fmap SomeConstant .) asConstant
    {-# INLINE readKnown #-}

instance uni ~ UniOf val => MakeKnownIn uni val (Opaque val rep) where
    makeKnown = coerceArg pure  -- A faster @pure . Opaque@.
    {-# INLINE makeKnown #-}

instance uni ~ UniOf val => ReadKnownIn uni val (Opaque val rep) where
    readKnown = coerceArg pure  -- A faster @pure . Opaque@.
    {-# INLINE readKnown #-}

-- Utils

-- | Coerce the second argument to the result type of the first one. The motivation for this
-- function is that it's often more annoying to explicitly specify a target type for 'coerce' than
-- to construct an explicit coercion function, so this combinator can be used in cases like that.
-- Plus the code reads better, as it becomes clear what and where gets wrapped/unwrapped.
coerceVia :: Coercible a b => (a -> b) -> a -> b
coerceVia _ = coerce
{-# INLINE coerceVia #-}

-- | Same as @\f -> f . coerce@, but does not create any closures and so is completely free.
coerceArg :: Coercible a b => (a -> r) -> b -> r
coerceArg = coerce
{-# INLINE coerceArg #-}
