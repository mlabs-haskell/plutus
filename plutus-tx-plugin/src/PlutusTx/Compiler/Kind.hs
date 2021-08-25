{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC kinds into PlutusCore kinds.
module PlutusTx.Compiler.Kind (compileKind) where

import           PlutusTx.Compiler.Error
import           PlutusTx.Compiler.Types
import           PlutusTx.Compiler.Utils

import qualified GhcPlugins              as GHC

import qualified PlutusCore              as PLC

compileKind :: Compiling uni fun m => GHC.Kind -> m (PLC.Kind ())
compileKind k = withContextM 2 (sdToTxt $ "Compiling kind:" GHC.<+> GHC.ppr k) $ case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isLiftedTypeKind -> True)         -> pure $ PLC.Type ()
    (GHC.splitFunTy_maybe -> Just (i, o)) | GHC.classifiesTypeWithValues i -> compileKind o
    (GHC.splitFunTy_maybe -> Just (i, o))  -> PLC.KindArrow () <$> compileKind i <*> compileKind o
    -- TODO: should construct a proper kind of unboxed tuple
    (GHC.splitPiTy_maybe -> Just (_, ty)) -> compileKind ty

    -- (GHC.kindRep_maybe -> Just ty) -> throwSd UnsupportedError $ "Kindrep:" GHC.<+> (GHC.ppr (ty, GHC.isUnboxedTupleType)
    -- (GHC.splitPiTy_maybe -> Just (_, ty)) -> case GHC.splitFunTy_maybe ty of
    --     Just (arg, funTy) | GHC.classifiesTypeWithValues arg -> throwSd UnsupportedError (GHC.ppr $ GHC.dropForAlls k)
    --     _ -> compileKind ty
    -- (isUnboxedTuplesKind -> True)          -> throwSd UnsupportedError $ GHC.ppr k  -- pure $ PLC.KindArrow () (PLC.Type ()) (PLC.KindArrow () (PLC.Type ()) (PLC.Type ()))
    -- Treat 'RunTimeRep' as type
    -- (GHC.isRuntimeRepTy -> True)           -> pure $ PLC.Type ()
    -- Treat 'TYPE rep' as type
    (GHC.classifiesTypeWithValues -> True) -> pure $ PLC.Type ()
    _                                      -> unsupportedKind
    where
        unsupportedKind = throwSd UnsupportedError $ "Kind:" GHC.<+> (GHC.ppr k)
        preds = [GHC.isKindLevPoly, GHC.classifiesTypeWithValues, GHC.isUnliftedTypeKind, GHC.isLiftedTypeKind, GHC.isRuntimeRepKindedTy, GHC.isUnliftedType, GHC.isUnliftedRuntimeRep, GHC.isLiftedRuntimeRep, GHC.isUnboxedTupleType]

-- | We match on pi type (unboxed tuples has two pi types) and deconstruct two arrow types
isUnboxedTuplesKind :: GHC.Kind -> Bool
isUnboxedTuplesKind k = case k of
    (GHC.splitPiTy_maybe -> Just _) -> case GHC.splitFunTy_maybe (GHC.dropForAlls k) of
        Just (_, funTy) -> case GHC.splitFunTy_maybe funTy of
            Just (_, ty) -> GHC.isUnliftedTypeKind ty
            _            -> False
        _ -> False
    _ -> False
