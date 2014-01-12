-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombLambdaTest
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

{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Combinators.CombLambdaTest (
    testCombLambda
) where

import Combinators.BinaryTree (PP(..))
import Combinators.Combinator (KS, CTerm)
import Combinators.CombinatorTest ()
import Combinators.CombLambda (BracketAbstract(..), combToLambda)
import Combinators.Reduction (reduceS)
import Combinators.Lambda (canonicalizeLambda, LTerm)
import Combinators.LambdaTest ()
import Combinators.Variable (VarString)
import Combinators.Types (Untyped(..))

import Debug.Trace (trace)
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Combinators.CombinatorBasis (IKBCW, IKS)

testCombLambda :: [Test]
testCombLambda = [-- testProperty "prop_combToLambda" prop_combToLambda
                    testProperty "prop_LambdaToCombKS" prop_LambdaToCombKS
                  , testProperty "prop_LambdaToCombIKS" prop_LambdaToCombIKS
                  , testProperty "prop_LambdaToCombIKBCW" prop_LambdaToCombIKBCW
                 ]


prop_LambdaToCombKS :: LTerm VarString Untyped -> Bool
prop_LambdaToCombKS term = case prop of
                                Nothing -> trace ("failed reduction term: "  ++
                                                pps (canonicalizeLambda term)) $ True
                                Just b -> b
  where
    prop = do
        let term' = canonicalizeLambda term
        lr <- reduceS term'
        let ct :: CTerm KS =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        if lr == resRed
            then (trace' "prop_LambdaToCombKS" lr cr resRed) $ return True
            else (trace' "prop_LambdaToCombKS" lr cr resRed) $ return False

trace' :: forall a t t1 t2.
        (PP (LTerm VarString t), PP t1, PP (LTerm VarString t2)) =>
        [Char] -> LTerm VarString t -> t1 -> LTerm VarString t2 -> a -> a

trace' name lr cr resRed a =
    trace
        (name ++ "\nin:\n" ++ pps (canonicalizeLambda lr) ++ "\ncon:\n" ++
         pps cr ++ "\nres:\n" ++
         pps (canonicalizeLambda resRed)) a

prop_LambdaToCombIKS :: LTerm VarString Untyped -> Bool
prop_LambdaToCombIKS term = case prop of
                                Nothing -> trace ("failed reduction term: "  ++
                                                pps (canonicalizeLambda term)) $ True
                                Just b -> b
  where
    prop = do
        let term' = canonicalizeLambda term
        lr <- reduceS term'
        let ct :: CTerm IKS =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        if lr == resRed
            then (trace' "prop_LambdaToCombIKS" lr cr resRed) $ return True
            else (trace' "prop_LambdaToCombIKS" lr cr resRed) $ return False

prop_LambdaToCombIKBCW :: LTerm VarString Untyped -> Bool
prop_LambdaToCombIKBCW term = case prop of
                                Nothing -> trace ("failed reduction term: "  ++
                                                pps (canonicalizeLambda term)) $ True
                                Just b -> b
  where
    prop = do
        let term' = canonicalizeLambda term
        lr <- reduceS term'
        let ct :: CTerm IKBCW =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        if lr == resRed
            then (trace' "prop_LambdaToCombIKBCW" lr cr resRed) $ return True
            else (trace' "prop_LambdaToCombIKBCW" lr cr resRed) $ return False


{- Not working in this form, maybe with reduction?
prop_combToLambda :: CTerm IKS -> Bool
prop_combToLambda term =
    let lambda = combToLambda term
    in case reduceS lambda of
        Nothing -> True
        Just reducedLambda ->
            let combTerm2 = bracketAbstract reducedLambda
                reducedResult = reduceS combTerm2
                reducedInput = reduceS term
            in if reducedInput == reducedResult
                        then True
                        else trace ("prop_combToLambda in:" ++ pps reducedInput ++ " res: " ++
                                    pps reducedLambda ++
                                    pps reducedResult) $ False
-}
