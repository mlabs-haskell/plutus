{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

-- | A type for intervals and associated functions.
module Plutus.V1.Ledger.Interval(
      Interval(..)
    , UpperBound(..)
    , LowerBound(..)
    , Extended(..)
    , Closure
    , member
    , interval
    , from
    , to
    , always
    , never
    , singleton
    , hull
    , intersection
    , overlaps
    , contains
    , isEmpty
    , before
    , after
    , strictLowerBound
    , strictUpperBound
    ) where

import           Codec.Serialise.Class (Serialise)
import           Control.DeepSeq       (NFData)
import           Data.Aeson            (FromJSON, ToJSON)
import           Data.Hashable         (Hashable)
import           GHC.Generics          (Generic)
import qualified Prelude               as Haskell

import qualified PlutusTx              as PlutusTx
import           PlutusTx.Lift         (makeLift)
import           PlutusTx.Prelude

-- | An interval of @a@s.
--
--   The interval may be either closed or open at either end, meaning
--   that the endpoints may or may not be included in the interval.
--
--   The interval can also be unbounded on either side.
data Interval a = Interval { ivFrom :: LowerBound a, ivTo :: UpperBound a }
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Serialise, Hashable, NFData)

-- | A set extended with a positive and negative infinity.
data Extended a = NegInf | Finite a | PosInf
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Serialise, Hashable, NFData)

-- | Whether a bound is inclusive or not.
type Closure = Bool

-- | The upper bound of an interval.
data UpperBound a = UpperBound (Extended a) Closure
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Serialise, Hashable, NFData)

-- | The lower bound of an interval.
data LowerBound a = LowerBound (Extended a) Closure
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Serialise, Hashable, NFData)

PlutusTx.makeIsDataIndexed ''Extended [('NegInf,0),('Finite,1),('PosInf,2)]
PlutusTx.makeIsDataIndexed ''UpperBound [('UpperBound,0)]
PlutusTx.makeIsDataIndexed ''LowerBound [('LowerBound,0)]
PlutusTx.makeIsDataIndexed ''Interval [('Interval,0)]

makeLift ''Extended
makeLift ''LowerBound
makeLift ''UpperBound
makeLift ''Interval

instance Eq a => Eq (Extended a) where
    {-# NOINLINE (==) #-}
    NegInf   == NegInf   = True
    PosInf   == PosInf   = True
    Finite l == Finite r = l == r
    _        == _        = False

instance Ord a => Ord (Extended a) where
    {-# NOINLINE compare #-}
    NegInf   `compare` NegInf   = EQ
    NegInf   `compare` _        = LT
    _        `compare` NegInf   = GT
    PosInf   `compare` PosInf   = EQ
    _        `compare` PosInf   = LT
    PosInf   `compare` _        = GT
    Finite l `compare` Finite r = l `compare` r

instance Eq a => Eq (UpperBound a) where
    {-# NOINLINE (==) #-}
    UpperBound v1 in1 == UpperBound v2 in2 = v1 == v2 && in1 == in2

instance Ord a => Ord (UpperBound a) where
    {-# NOINLINE compare #-}
    UpperBound v1 in1 `compare` UpperBound v2 in2 = case v1 `compare` v2 of
        LT -> LT
        GT -> GT
        -- A closed upper bound is bigger than an open upper bound. This corresponds
        -- to the normal order on Bool.
        EQ -> in1 `compare` in2

instance Eq a => Eq (LowerBound a) where
    {-# NOINLINE (==) #-}
    LowerBound v1 in1 == LowerBound v2 in2 = v1 == v2 && in1 == in2

instance Ord a => Ord (LowerBound a) where
    {-# NOINLINE compare #-}
    LowerBound v1 in1 `compare` LowerBound v2 in2 = case v1 `compare` v2 of
        LT -> LT
        GT -> GT
        -- An open lower bound is bigger than a closed lower bound. This corresponds
        -- to the *reverse* of the normal order on Bool.
        EQ -> in2 `compare` in1

{-# NOINLINE strictUpperBound #-}
strictUpperBound :: a -> UpperBound a
strictUpperBound a = UpperBound (Finite a) False

{-# NOINLINE strictLowerBound #-}
strictLowerBound :: a -> LowerBound a
strictLowerBound a = LowerBound (Finite a) False

{-# NOINLINE lowerBound #-}
lowerBound :: a -> LowerBound a
lowerBound a = LowerBound (Finite a) True

{-# NOINLINE upperBound #-}
upperBound :: a -> UpperBound a
upperBound a = UpperBound (Finite a) True

instance Ord a => JoinSemiLattice (Interval a) where
    {-# NOINLINE (\/) #-}
    (\/) = hull

instance Ord a => BoundedJoinSemiLattice (Interval a) where
    {-# NOINLINE bottom #-}
    bottom = never

instance Ord a => MeetSemiLattice (Interval a) where
    {-# NOINLINE (/\) #-}
    (/\) = intersection

instance Ord a => BoundedMeetSemiLattice (Interval a) where
    {-# NOINLINE top #-}
    top = always

instance Eq a => Eq (Interval a) where
    {-# NOINLINE (==) #-}
    l == r = ivFrom l == ivFrom r && ivTo l == ivTo r

{-# NOINLINE interval #-}
-- | @interval a b@ includes all values that are greater than or equal
--   to @a@ and smaller than @b@. Therefore it includes @a@ but not it
--   does not include @b@.
interval :: a -> a -> Interval a
interval s s' = Interval (lowerBound s) (upperBound s')

{-# NOINLINE singleton #-}
singleton :: a -> Interval a
singleton s = interval s s

{-# NOINLINE from #-}
-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@.
from :: a -> Interval a
from s = Interval (lowerBound s) (UpperBound PosInf True)

{-# NOINLINE to #-}
-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than @a@.
to :: a -> Interval a
to s = Interval (LowerBound NegInf True) (upperBound s)

{-# NOINLINE always #-}
-- | An 'Interval' that covers every slot.
always :: Interval a
always = Interval (LowerBound NegInf True) (UpperBound PosInf True)

{-# NOINLINE never #-}
-- | An 'Interval' that is empty.
never :: Interval a
never = Interval (LowerBound PosInf True) (UpperBound NegInf True)

{-# NOINLINE member #-}
-- | Check whether a value is in an interval.
member :: Ord a => a -> Interval a -> Bool
member a i = i `contains` singleton a

{-# NOINLINE overlaps #-}
-- | Check whether two intervals overlap, that is, whether there is a value that
--   is a member of both intervals.
overlaps :: Ord a => Interval a -> Interval a -> Bool
overlaps l r = isEmpty (l `intersection` r)

{-# NOINLINE intersection #-}
-- | 'intersection a b' is the largest interval that is contained in 'a' and in
--   'b', if it exists.
intersection :: Ord a => Interval a -> Interval a -> Interval a
intersection (Interval l1 h1) (Interval l2 h2) = Interval (max l1 l2) (min h1 h2)

{-# NOINLINE hull #-}
-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull :: Ord a => Interval a -> Interval a -> Interval a
hull (Interval l1 h1) (Interval l2 h2) = Interval (min l1 l2) (max h1 h2)

{-# NOINLINE contains #-}
-- | @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
--   @a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
--   @member s a@.
contains :: Ord a => Interval a -> Interval a -> Bool
contains (Interval l1 h1) (Interval l2 h2) = l1 <= l2 && h2 <= h1

{-# NOINLINE isEmpty #-}
-- | Check if an 'Interval' is empty.
isEmpty :: Ord a => Interval a -> Bool
isEmpty (Interval (LowerBound v1 in1) (UpperBound v2 in2)) = case v1 `compare` v2 of
    LT -> True
    GT -> False
    EQ -> not (in1 && in2)

{-# NOINLINE before #-}
-- | Check if a value is earlier than the beginning of an 'Interval'.
before :: Ord a => a -> Interval a -> Bool
before h (Interval f _) = lowerBound h < f

{-# NOINLINE after #-}
-- | Check if a value is later than the end of a 'Interval'.
after :: Ord a => a -> Interval a -> Bool
after h (Interval _ t) = upperBound h > t
