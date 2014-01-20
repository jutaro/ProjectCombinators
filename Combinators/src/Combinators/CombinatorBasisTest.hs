-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombinatorBasisTest
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

module Combinators.CombinatorBasisTest where

import Combinators.CombinatorBasis
import Combinators.Combinator

import Test.HUnit.Base (Assertion)
import Test.HUnit (assertBool)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)
import Combinators.BinaryTree (PP(..))
import Combinators.Reduction
       (instrumentedContext, NormalForm(..), reduceIt)


testWK :: Assertion
testWK  = assertBool "testWK" $ (pparse :: String -> CTerm IKBCW) "x" ==
            (reduceIt instrumentedContext NormalForm . pparse) "W K x"

testS :: Assertion
testS  = assertBool "testS" $ (pparse :: String -> CTerm IKBCW) "x z (y z)" ==
            (reduceIt instrumentedContext NormalForm . pparse) "B (B (B W) C) (B B) x y z"

testS2 :: Assertion
testS2  = assertBool "testS2" $ (pparse :: String -> CTerm IKBCW) "x z (y z)" ==
            (reduceIt instrumentedContext NormalForm . pparse) "B (B W) (B B C) x y z"


testBasis :: [Test]
testBasis = [testCase "testWK" testWK,
             testCase "testS" testS,
             testCase "testS2" testS2   ]


