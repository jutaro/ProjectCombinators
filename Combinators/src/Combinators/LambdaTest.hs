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
-- import Test.Framework.Providers.HUnit (testCase)


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
                            term == parseLambda (pp term)

testLambda :: [Test]
testLambda = [testProperty "prop_printParse" prop_printParse
             -- , testCase "testReduction1" testReduction1
             -- , testCase "testReduction2" testReduction2
              ]

testReduction1 :: Assertion
testReduction1 =
    parseLambda "y y y" @=? (reduceIt nullContext NormalForm . parseLambda) "(\\x.x x) y y"

testReduction2 :: Assertion
testReduction2 =
    parseLambda "\\x.x" @=? (reduceIt nullContext NormalForm . parseLambda) "(\\f.f \\x.x) \\s.s s"
