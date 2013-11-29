-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombinatorBasisTest
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

module Combinators.CombinatorBasisTest where

import Combinators.CombinatorBasis
import Combinators.Combinator

import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?))
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)


testWK :: Assertion
testWK  = parseBCKW "x" @=? (normalOrderReduction . parseBCKW) "W K x"

testS :: Assertion
testS  = parseBCKW "x z (y z)" @=? (normalOrderReduction . parseBCKW) "B (B (B W) C) (B B) x y z"

testS2 :: Assertion
testS2  = parseBCKW "x z (y z)" @=? (normalOrderReduction . parseBCKW) "B (B W) (B B C) x y z"


testBasis :: [Test]
testBasis = [testCase "testWK" testWK,
             testCase "testS" testS,
             testCase "testS2" testS2   ]


