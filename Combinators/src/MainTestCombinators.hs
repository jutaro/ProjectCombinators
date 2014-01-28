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
import Combinators.CombGeneratorTest
import Combinators.TypesTest
import Combinators.CombLambdaTest (testCombLambda)
import Combinators.LambdaTypedTest (testLambdaTyped)

import Test.Framework


main :: IO ()
main = defaultMain $
            testCombinators
            ++ testLambda
            ++ testTypes
            ++ testCombLambda
            ++ testLambdaTyped

testCombinators :: [Test]
testCombinators = testLanguage
                ++ testProperties
                ++ testBasis
                ++ testCombGenerator


