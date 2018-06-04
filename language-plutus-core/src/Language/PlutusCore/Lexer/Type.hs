{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Lexer.Type ( BuiltinName (..)
                                      , Version (..)
                                      , Keyword (..)
                                      , Special (..)
                                      , Token (..)
                                      , TypeBuiltin (..)
                                      ) where

import qualified Data.ByteString.Lazy     as BSL
import           Language.PlutusCore.Name
import           PlutusPrelude

-- | A builtin type
data TypeBuiltin = TyByteString
                 | TyInteger
                 | TySize
                 deriving (Show, Eq, Generic, NFData)

-- | Builtin functions
data BuiltinName = AddInteger
                 | SubtractInteger
                 | MultiplyInteger
                 | DivideInteger
                 | RemainderInteger
                 | LessThanInteger
                 | LessThanEqInteger
                 | GreaterThanInteger
                 | GreaterThanEqInteger
                 | EqInteger
                 | IntToByteString
                 | Concatenate
                 | TakeByteString
                 | DropByteString
                 | ResizeByteString
                 | SHA2
                 | SHA3
                 | VerifySignature
                 | EqByteString
                 | TxHash
                 | BlockNum
                 | BlockTime
                 deriving (Show, Eq, Generic, NFData)

-- | Version of Plutus Core to be used for the program.
data Version a = Version a Natural Natural Natural
               deriving (Show, Eq, Functor, Generic, NFData)

-- | A keyword in Plutus Core.
data Keyword = KwAbs
             | KwLam
             | KwFix
             | KwFun
             | KwForall
             | KwByteString
             | KwInteger
             | KwSize
             | KwType
             | KwProgram
             | KwCon
             | KwWrap
             | KwUnwrap
             | KwError
             deriving (Show, Eq, Generic, NFData)

-- | A special character. This type is only used internally between the lexer
-- and the parser.
data Special = OpenParen
             | CloseParen
             | OpenBracket
             | CloseBracket
             | Dot
             | Exclamation
             | OpenBrace
             | CloseBrace
             deriving (Show, Eq, Generic, NFData)

-- | A token generated by the lexer.
data Token a = LexName { loc        :: a
                       , name       :: BSL.ByteString
                       , identifier :: Unique -- ^ A 'Unique' assigned to the identifier during lexing.
                       }
             | LexInt { loc :: a, int :: Integer }
             | LexBS { loc :: a, bytestring :: BSL.ByteString }
             | LexBuiltin { loc :: a, builtin :: BuiltinName }
             | LexNat { loc :: a, nat :: Natural }
             | LexKeyword { loc :: a, keyword :: Keyword }
             | LexSpecial { loc :: a, special :: Special }
             | EOF { loc :: a }
             deriving (Show, Eq, Generic, NFData)

instance Pretty BuiltinName where
    pretty AddInteger           = "addInteger"
    pretty SubtractInteger      = "subtractInteger"
    pretty MultiplyInteger      = "multiplyInteger"
    pretty DivideInteger        = "divideInteger"
    pretty RemainderInteger     = "remainderInteger"
    pretty LessThanInteger      = "lessThanInteger"
    pretty LessThanEqInteger    = "lessThanEqualsInteger"
    pretty GreaterThanInteger   = "greaterThanInteger"
    pretty GreaterThanEqInteger = "greaterThanEqualsInteger"
    pretty EqInteger            = "equalsInteger"
    pretty IntToByteString      = "intToByteString"
    pretty Concatenate          = "concatenate"
    pretty TakeByteString       = "takeByteString"
    pretty DropByteString       = "dropByteString"
    pretty ResizeByteString     = "resizeByteString"
    pretty EqByteString         = "equalsByteString"
    pretty SHA2                 = "sha2_256"
    pretty SHA3                 = "sha3_256"
    pretty VerifySignature      = "verifySignature"
    pretty TxHash               = "txhash"
    pretty BlockNum             = "blocknum"
    pretty BlockTime            = "blocktime"

instance Pretty TypeBuiltin where
    pretty TyInteger    = "integer"
    pretty TyByteString = "bytestring"
    pretty TySize       = "size"

instance Pretty (Version a) where
    pretty (Version _ i j k) = pretty i <> "." <> pretty j <> "." <> pretty k
