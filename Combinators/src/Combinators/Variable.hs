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

-- | An instance of variable can be:
--
-- * shown
--
-- * compared for equality
--
-- * compared for order

class (Show v, Eq v, Ord v) => Variable v where

-----------------------------------------------------------------------------
-- ** VarString

-- | The representation of variables as strings
--
--   A string variable has to start with a lowercase letter.
--   Followed by any character, which does not include:
--
-- > " :,;()[]\t\n\r\f\v."
type VarString = String

instance Variable VarString

-- | Prints a variable, which is just identity
varPp :: VarString -> String
varPp = id

-- | Parses a variable
--
varParse :: Parser VarString
varParse = do
            start <- PA.lower
            rest <- PA.many (PA.noneOf " :,;()[]\t\n\r\f\v.")
            PA.spaces
            return (start:rest)
        PA.<?> "varParse for SimpleVar"

-- | Generates an infinite stream of variable names:
--
-- > [u,v,w,x,y,z,u1,v1,w1,x1,y1,z1,u2...]
nameGen :: [String]
nameGen = [ c: n | n <- ("" : map show [(1:: Int)..]), c <- "uvwxyz"]

-- | Generates an infinite stream of variable names with a hyphen at the end:
--
-- > [u',v',w',x',y',z',u1',v1',w1',x1',y1',z1',u2'...]
nameGenFV  :: [String]
nameGenFV = map (++ "'") nameGen

-----------------------------------------------------------------------------
-- ** VarIndex

-- | The representation of variables as de Bruin indices
type VarInt = Int

instance Variable VarInt


