-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Types
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}

module Combinators.Types (
    SType(..),
    TypeAtom,
    typeVarGen
) where

import Combinators.BinaryTree
import qualified Text.PrettyPrint as PP (text, sep, parens, Doc)
import qualified Text.Parsec as PA
import Text.Parsec.String (Parser)

-----------------------------------------------------------------------------
-- * Simple Types

type TypeAtom = String

data SType where
    SAtom :: TypeAtom -> SType
    (:->:) :: SType -> SType -> SType

-- Bind application to the left.
infixr 5 :->:

typeVarGen :: [String]
typeVarGen = [ c: n | n <- ("" : map show [(1:: Int)..]), c <- "abcdefg"]

deriving instance Show SType
deriving instance Eq SType
deriving instance Ord SType

instance BinaryTree SType where
    decompose (a :->: b) = Just (a,b)
    decompose (SAtom _) = Nothing
    a @@ b              = a :->: b

-----------------------------------------------------------------------------
-- ** Printing and parsing

instance PP SType where
    pp = pp' False
    pparser = parseType []

pp' :: Bool -> SType -> PP.Doc
pp' True (a :->: b)   = PP.parens (pp' False (a :->: b))
pp' False (a :->: b)  = PP.sep [pp' True a, PP.text "->", pp' False b]
pp' _ (SAtom s)      = PP.text s


parseType :: [SType] -> Parser SType
parseType left = do
    PA.try $ do
        atom <- sAtomParse
        PA.option (foldr (:->:) atom (reverse left)) (do
            PA.spaces
            PA.string "->"
            parseType (atom : left))
    PA.<|> do
            PA.spaces
            PA.char '('
            t <- parseType []
            PA.spaces
            PA.char ')'
            PA.option (foldr (:->:) t (reverse left)) (do
                PA.spaces
                PA.string "->"
                parseType (t:left))
    PA.<?> "Type"

sAtomParse :: Parser SType
sAtomParse = do
        PA.spaces
        start <- PA.lower
        rest <- PA.many (PA.noneOf " ()\t\n\r\f\v.")
        return (SAtom (start:rest))
    PA.<?> "sAtom"


