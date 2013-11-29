{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
--
-- Module      :  Variable
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Combinators.Variable where

import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA ((<?>), noneOf, many, lower,spaces)

-- | A variable can be
--
-- * printed
-- * parsed
-- * instantiated from a string representation
--
-- * compared for equality

class (Show v, Eq v) => Variable v where
    varPp     :: v -> String
        -- ^ needs to start with lower case character
    varParse  :: Parser v
    varString :: VarString -> v -- Fixme with state
    varGen    :: Int -> [v]

-- | The representation of variables as strings
type VarString = String

instance Variable VarString where
    varPp = id
    varParse = do
            PA.spaces
            start <- PA.lower
            rest <- PA.many (PA.noneOf " ()\t\n\r\f\v.")
            return (start:rest)
        PA.<?> "varParse for SimpleVar"
    varString = id
    varGen i = map (\i' -> "v_" ++ show i') [1 .. i]




