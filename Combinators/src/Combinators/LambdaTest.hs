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

import Combinators.Lambda

import Test.QuickCheck
       (Arbitrary(..), elements, frequency)
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Combinators.Variable (VarString)
import Control.Monad (liftM2, liftM)
import Debug.Trace (trace)


-- ** Testing

instance Arbitrary (LTerm VarString) where
    arbitrary = frequency
        [(8,liftM LVar (elements ["u","v","w","x","y","z"]))
        ,(6,liftM2 (:@:) arbitrary arbitrary)
        ,(8,liftM2 (:.:) (elements ["u","v","w","x","y","z"]) arbitrary)
        ]

--  For any term: print and parse give the original term
prop_printParse :: LTerm VarString -> Bool
prop_printParse term = trace ("\n\n" ++ ppl term ++ "\n" ++ ppl (parseStringVarL (ppl term))
                            ++ "\n\n" ++ show term ++ "\n" ++ show (parseStringVarL (ppl term))) $
                            term == parseStringVarL (ppl term)

testLambda :: [Test]
testLambda = [testProperty "prop_printParse" prop_printParse]

