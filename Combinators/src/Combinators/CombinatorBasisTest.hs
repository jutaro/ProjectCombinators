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
import Test.HUnit ((@=?))
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)
import Combinators.BinaryTree (PP(..))


testWK :: Assertion
testWK  = (pparse :: String -> CTerm IBCWK) "x" @=? (normalOrderReduction . pparse) "W K x"

testS :: Assertion
testS  = (pparse :: String -> CTerm IBCWK) "x z (y z)" @=? (normalOrderReduction . pparse) "B (B (B W) C) (B B) x y z"

testS2 :: Assertion
testS2  = (pparse :: String -> CTerm IBCWK) "x z (y z)" @=? (normalOrderReduction . pparse) "B (B W) (B B C) x y z"


testBasis :: [Test]
testBasis = [testCase "testWK" testWK,
             testCase "testS" testS,
             testCase "testS2" testS2   ]


