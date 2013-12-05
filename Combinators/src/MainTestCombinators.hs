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

import Combinators.CombinatorTest
import Combinators.LambdaTest
import Combinators.CombinatorBasisTest
import Combinators.PropertiesTest
import Combinators.CombGenerator


import Test.Framework


main :: IO ()
main = defaultMain $
            testCombinators ++
            testLambda

testCombinators :: [Test]
testCombinators = testLanguage ++ testProperties ++ testBasis ++ testCombGenerator


