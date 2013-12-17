{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.LambdaTest
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

module Combinators.LambdaTest where

import Combinators

import Test.QuickCheck
       (Arbitrary(..), elements, frequency)
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Control.Monad (liftM2, liftM)
import Test.HUnit ((@=?), Assertion)
import Test.Framework.Providers.HUnit (testCase)


-- ** Testing

instance Arbitrary (LTerm VarString) where
    arbitrary = frequency
        [(8,liftM LVar (elements ["u","v","w","x","y","z"]))
        ,(6,liftM2 (:@:) arbitrary arbitrary)
        ,(8,liftM2 ((:@:) . LAbst) (elements ["u","v","w","x","y","z"]) arbitrary)
        ]

--  For any term: print and parse give the original term
prop_printParse :: LTerm VarString -> Bool
prop_printParse term = --trace ("\n\n" ++ ppl term ++ "\n" ++ ppl (parseLambda (ppl term))
                       --     ++ "\n\n" ++ show term ++ "\n" ++ show (parseLambda (ppl term))) $
                            term == parseLambda ((show . pp) term)

testLambda :: [Test]
testLambda = [testProperty "prop_printParse" prop_printParse
             , testCase "testReduction1" testReduction1
             , testCase "testReduction2" testReduction2
             , testCase "testReduction3" testReduction3
             , testCase "testReduction4" testReduction4
             , testCase "testReduction5" testReduction5
             , testCase "testReduction6" testReduction6
             , testCase "testReduction7" testReduction7
             , testCase "testReduction8" testReduction8
             , testCase "testReduction9" testReduction9
             , testCase "testReduction10" testReduction10
             , testCase "testReduction11" testReduction11
             ]

testReduction1 :: Assertion
testReduction1 =
    parseLambda "y y y" @=? (reduceIt instrumentedContext NormalForm . parseLambda) "(\\x.x x) y y"

testReduction2 :: Assertion
testReduction2 =
    parseLambda "\\s.s s" @=? (reduceIt instrumentedContext NormalForm . parseLambda) "(\\f.f) (\\x.x) \\s.s s"

testReduction3 :: Assertion
testReduction3 =
    parseLambda "\\t. (y y y)" @=? (reduceIt instrumentedContext NormalForm . parseLambda) "\\t.(\\x.x x) y y"

testReduction4 :: Assertion
testReduction4 =
    parseLambda "y (y y y)" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x. x) y ((\\x.x x) y y)"

testReduction5 :: Assertion
testReduction5 =
    parseLambda "x" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\t. x) y"

-- | two tie theta
testReduction6 :: Assertion
testReduction6 =
    parseLambda "y" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x.(\\x.y) x) x"

testReduction7 :: Assertion
testReduction7 =
    parseLambda "x x (x x (x x)) \\z.z z" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x. (\\y. y(y y)) x) (x x) (\\z.z z)"

testReduction8 :: Assertion
testReduction8 =
    parseLambda "\\y.x x y (x x y)" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\ z y. x x y (x x y)) x"

testReduction9 :: Assertion
testReduction9 =
    parseLambda "y (v v)" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x. x) y ((\\z. z z) v)"

testReduction10 :: Assertion
testReduction10 =
    parseLambda "y" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x. x y) \\z. z"

testReduction11 :: Assertion
testReduction11 =
    parseLambda "x" @=? (reduceIt instrumentedContext NormalForm . parseLambda)
                "(\\x. x) ((\\y z. z(y y z))(\\y z. z(y y z))x)"
