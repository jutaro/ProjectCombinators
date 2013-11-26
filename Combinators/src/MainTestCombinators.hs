-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main (
    main
) where

import Combinators
import Test.Framework


main :: IO ()
main = defaultMain $
            testCombinators ++
            testLambda

testCombinators :: [Test]
testCombinators = testLanguage ++ testProperties ++ testBasis


