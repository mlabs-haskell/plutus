{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}

module PlutusLedgerApi.Test.V3.MintValue where

import Data.Coerce (coerce)
import PlutusLedgerApi.V1.Value (CurrencySymbol (..), TokenName (..))
import PlutusLedgerApi.V3.MintValue (MintValue (..))
import PlutusTx.AssocMap qualified as Map
import PlutusTx.List qualified as List
import Test.QuickCheck (Arbitrary)

-- | Convert a list representation of a 'MintValue' to the 'MintValue'.
listsToMintValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> MintValue
listsToMintValue = coerce . Map.unsafeFromList . List.map (fmap Map.unsafeFromList)

-- | Convert a 'MintValue' to its list representation.
mintValueToLists :: MintValue -> [(CurrencySymbol, [(TokenName, Integer)])]
mintValueToLists = List.map (fmap Map.toList) . Map.toList . coerce

newtype Quantity = Quantity {unQuantity :: Integer}
  deriving newtype (Arbitrary, Show)