{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module PlutusIR.Transform.LetSplit
    (letSplit) where

import qualified PlutusCore.Constant                  as PLC
import qualified PlutusCore.Name                      as PLC
import           PlutusIR
import           PlutusIR.Analysis.Dependencies

import qualified Algebra.Graph.AdjacencyMap           as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap  as AMN
import           Control.Lens
import           Data.Either
import           Data.Foldable                        (foldl')
import qualified Data.List.NonEmpty                   as NE
import qualified Data.Map                             as M
import qualified Data.Set                             as S

{-|
Recursively apply let merging cancellation.
-}
letSplit
    :: forall uni fun a name tyname.
      (PLC.HasUnique tyname PLC.TypeUnique,
       PLC.HasUnique name PLC.TermUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> Term tyname name uni fun a
letSplit pir = transformOf termSubterms letSplitStep pir
  where
    depGraph :: AM.AdjacencyMap PLC.Unique
    depGraph = AM.induceJust $
               -- we remove Root because we do not care about it
               AM.gmap (\case { Variable u -> Just u; Root -> Nothing}) $
               fst $ runTermDeps pir

    {-| a single non-recursive application of let-merging cancellation.
    -}
    letSplitStep
        :: Term tyname name uni fun a
        -> Term tyname name uni fun a
    letSplitStep = \case
        Let a Rec bs t ->
            let
                bindingsTable :: M.Map PLC.Unique (Binding tyname name uni fun a)
                bindingsTable = M.fromList . NE.toList $ fmap (\ b -> (b^.principal, b)) bs
                hereIds = S.fromList $ bs^..traversed.bindingIds
                hereGraph = AM.closure $ AM.induce (`S.member` hereIds) depGraph
                hereSccs = AM.gmap (\ scc -> (AMN.vertexSet scc, if AM.isAcyclic $ AMN.fromNonEmpty scc then NonRec else Rec)) $ AM.scc hereGraph
                topSortSccs = fromRight (error "Cycle detected in the scc-graph. This shouldn't happen in the first place.") $ AM.topSort hereSccs
            in foldl' (\ acc (vs, recurs) -> Let a recurs (NE.fromList . M.elems $ M.restrictKeys bindingsTable vs) acc) t topSortSccs
        t  -> t



-- | A getter that returns a single 'Unique' for a particular binding.
-- We need this because let-datatypes introduce multiple identifiers, but in our 'RhsTable', we use a single Unique as the key.
-- See Note [Principal]. See also: 'bindingIds'.
principal :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
            => Getting r (Binding tyname name uni fun a) PLC.Unique
principal = to $ \case TermBind _ _ (VarDecl _ n _) _                            -> n ^. PLC.theUnique
                       TypeBind _ (TyVarDecl _ n _) _                            -> n ^. PLC.theUnique
                       -- arbitrary: uses the type construtors' unique as the principal unique of this data binding group
                       DatatypeBind _ (Datatype _ (TyVarDecl _ tConstr _) _ _ _) -> tConstr ^. PLC.theUnique
