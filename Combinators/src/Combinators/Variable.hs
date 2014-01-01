{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
--
-- Module      :  Variable
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-----------------------------------------------------------------------------

module Combinators.Variable where

import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA ((<?>), noneOf, many, lower,spaces)

-----------------------------------------------------------------------------
-- * Variables
-----------------------------------------------------------------------------


-- | A variable can be
--
-- * shown
-- * compared for equality
-- * ordered
class (Show v, Eq v, Ord v) => Variable v where

-----------------------------------------------------------------------------
-- ** VarString

-- | The representation of variables as strings
type VarString = String

instance Variable VarString

varPp :: VarString -> String
varPp = id

varParse :: Parser VarString
varParse = do
            PA.spaces
            start <- PA.lower
            rest <- PA.many (PA.noneOf " ()\t\n\r\f\v.")
            return (start:rest)
        PA.<?> "varParse for SimpleVar"

-----------------------------------------------------------------------------
-- ** VarIndex

-- | The representation of variables as de Bruin indices
type VarInt = Int

instance Variable VarInt

nameGen :: [String]
nameGen = [ c: n | n <- ("" : map show [(1:: Int)..]), c <- "uvwxyz"]

nameGenFV  :: [String]
nameGenFV = map (++ "'") nameGen
