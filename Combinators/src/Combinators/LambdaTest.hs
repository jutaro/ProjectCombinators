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


testLambda :: [Test]
testLambda = [testProperty "prop_printParse" prop_printParse
             , testProperty "prop_lambdaB" prop_lambdaB
             , testProperty "prop_testReduction" prop_testReduction
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
             , testCase "testReduction12" testReduction12
             , testCase "testReductionB1" testReductionB1
             , testCase "testReductionB2" testReductionB2
             , testCase "testReductionB3" testReductionB3
             , testCase "testReductionB4" testReductionB4
             , testCase "testReductionB5" testReductionB5
             , testCase "testReductionB6" testReductionB6
             , testCase "testReductionB7" testReductionB7
             , testCase "testReductionB8" testReductionB8
             , testCase "testReductionB9" testReductionB9
             , testCase "testReductionB10" testReductionB10
             , testCase "testReductionB11" testReductionB11
             , testCase "testReductionB12" testReductionB12

             ]

instance Arbitrary (LTerm VarString Untyped) where
    arbitrary = frequency
        [(8,liftM LVar (elements ["u","v","w","x","y","z"]))
        ,(6,liftM2 (:@:) arbitrary arbitrary)
        ,(8,liftM2 ((:@:) . flip LAbst Untyped) (elements ["u","v","w","x","y","z"]) arbitrary)
        ]

--  For any term: print and parse give the original term
prop_printParse :: LTerm VarString Untyped -> Bool
prop_printParse term = --trace ("\n\n" ++ ppl term ++ "\n" ++ ppl (parseLambda (ppl term))
                       --     ++ "\n\n" ++ show term ++ "\n" ++ show (parseLambda (ppl term))) $
                            term == pparse ((show . pp) term)

prop_lambdaB :: LTerm VarString Untyped -> Bool
prop_lambdaB term = --trace ("\n\n" ++ ppl term ++ "\n" ++ ppl (parseLambda (ppl term))
                       --     ++ "\n\n" ++ show term ++ "\n" ++ show (parseLambda (ppl term))) $
                            term == fromLambdaB (toLambdaB term)

prop_testReduction :: LTerm VarString Untyped -> Bool
prop_testReduction term = (case reduceS term of
                            Nothing -> Nothing
                            Just t -> Just (toLambdaB t))  == reduceS (toLambdaB term)
testReduction1 :: Assertion
testReduction1 =
    (pparse :: String -> LTerm VarString Untyped) "y y y" @=? (reduceIt instrumentedContext NormalForm . pparse) "(\\x.x x) y y"

testReduction2 :: Assertion
testReduction2 =
    (pparse :: String -> LTerm VarString Untyped) "\\s.s s" @=? (reduceIt instrumentedContext NormalForm . pparse) "(\\f.f) (\\x.x) \\s.s s"

testReduction3 :: Assertion
testReduction3 =
    (pparse :: String -> LTerm VarString Untyped) "\\t. (y y y)" @=? (reduceIt instrumentedContext NormalForm . pparse) "\\t.(\\x.x x) y y"

testReduction4 :: Assertion
testReduction4 =
    (pparse :: String -> LTerm VarString Untyped) "y (y y y)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x) y ((\\x.x x) y y)"

testReduction5 :: Assertion
testReduction5 =
    (pparse :: String -> LTerm VarString Untyped) "x" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\t. x) y"

-- | two tie theta
testReduction6 :: Assertion
testReduction6 =
    (pparse :: String -> LTerm VarString Untyped) "y" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x.(\\x.y) x) x"

testReduction7 :: Assertion
testReduction7 =
    (pparse :: String -> LTerm VarString Untyped) "x x (x x (x x)) \\z.z z" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. (\\y. y(y y)) x) (x x) (\\z.z z)"

testReduction8 :: Assertion
testReduction8 =
    (pparse :: String -> LTerm VarString Untyped) "\\y.x x y (x x y)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\ z y. x x y (x x y)) x"

testReduction9 :: Assertion
testReduction9 =
    (pparse :: String -> LTerm VarString Untyped) "y (v v)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x) y ((\\z. z z) v)"

testReduction10 :: Assertion
testReduction10 =
    (pparse :: String -> LTerm VarString Untyped) "y" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x y) \\z. z"

-- infinite reduction
testReduction11 :: Assertion
testReduction11 =
    Nothing @=? (reduce instrumentedContext NormalForm . (pparse :: String -> LTerm VarString Untyped))
                "(\\x. x) ((\\y z. z(y y z))(\\y z. z(y y z))x)"

-- composite beta reduction
testReduction12 :: Assertion
testReduction12 =
    (pparse :: String -> LTerm VarString Untyped) "y (v v)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x.x) y ((\\z.z z) v)"

-- name clashes (alpha renaming, de bruijn indices  (b b) is wrong (a b) is correct.
testReduction13 :: Assertion
testReduction13 =
    (pparse :: String -> LTerm VarString Untyped) "a b" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\f a.f a) a b"

testReductionB1 :: Assertion
testReductionB1 =
    (pparse :: String -> LTerm VarInt Untyped) "y y y" @=? (reduceIt instrumentedContext NormalForm . pparse) "(\\x.x x) y y"

testReductionB2 :: Assertion
testReductionB2 =
    (pparse :: String -> LTerm VarInt Untyped) "\\s.s s" @=? (reduceIt instrumentedContext NormalForm . pparse) "(\\f.f) (\\x.x) \\s.s s"

testReductionB3 :: Assertion
testReductionB3 =
    (pparse :: String -> LTerm VarInt Untyped) "\\t. (y y y)" @=? (reduceIt instrumentedContext NormalForm . pparse) "\\t.(\\x.x x) y y"

testReductionB4 :: Assertion
testReductionB4 =
    (pparse :: String -> LTerm VarInt Untyped) "y (y y y)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x) y ((\\x.x x) y y)"

testReductionB5 :: Assertion
testReductionB5 =
    (pparse :: String -> LTerm VarInt Untyped) "x" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\t. x) y"

-- | two tie theta
testReductionB6 :: Assertion
testReductionB6 =
    (pparse :: String -> LTerm VarInt Untyped) "y" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x.(\\x.y) x) x"

testReductionB7 :: Assertion
testReductionB7 =
    (pparse :: String -> LTerm VarInt Untyped) "x x (x x (x x)) \\z.z z" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. (\\y. y(y y)) x) (x x) (\\z.z z)"

testReductionB8 :: Assertion
testReductionB8 =
    (pparse :: String -> LTerm VarInt Untyped) "\\y.x x y (x x y)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\ z y. x x y (x x y)) x"

testReductionB9 :: Assertion
testReductionB9 =
    (pparse :: String -> LTerm VarInt Untyped) "y (v v)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x) y ((\\z. z z) v)"

testReductionB10 :: Assertion
testReductionB10 =
    (pparse :: String -> LTerm VarInt Untyped) "y" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x. x y) \\z. z"

-- infinite reduction
testReductionB11 :: Assertion
testReductionB11 =
    Nothing @=? (reduce instrumentedContext NormalForm . (pparse :: String -> LTerm VarInt Untyped))
                "(\\x. x) ((\\y z. z(y y z))(\\y z. z(y y z))x)"

-- composite beta reduction
testReductionB12 :: Assertion
testReductionB12 =
    (pparse :: String -> LTerm VarInt Untyped) "y (v v)" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\x.x) y ((\\z.z z) v)"

-- name clashes (alpha renaming, de bruijn indices  (b b) is wrong (a b) is correct.
testReductionB13 :: Assertion
testReductionB13 =
    (pparse :: String -> LTerm VarInt Untyped) "a b" @=? (reduceIt instrumentedContext NormalForm . pparse)
                "(\\f a.f a) a b"
