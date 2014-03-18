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

import Combinators.Combinator (CTerm(..), KS, CTerm)
import Combinators.CombinatorTest ()
import Combinators.CombLambda (BracketAbstract(..), combToLambda)
import Combinators.Reduction (Term(..), reduceS)
import Combinators.Lambda (LTerm)
import Combinators.LambdaTest ()
import Combinators.Variable (VarString)
import Combinators.Types (Untyped(..))

import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Combinators.CombinatorBasis (KBCW(..), IKBCW, IKS)
import Combinators.PrintingParsing (PP, PP(..))
import Test.HUnit ((@=?), Assertion)
import Test.Framework.Providers.HUnit (testCase)
import Data.Maybe (fromMaybe)

trace :: a -> b -> b
trace _a b = b

testCombLambda :: [Test]
testCombLambda = [-- testProperty "prop_combToLambda" prop_combToLambda
                    testProperty "prop_LambdaToCombKS" prop_LambdaToCombKS
                  , testProperty "prop_LambdaToCombIKS" prop_LambdaToCombIKS
                  , testProperty "prop_LambdaToCombIKBCW" prop_LambdaToCombIKBCW
                  , testCase "test_C_KBCW_Abst" test_C_KBCW_Abst
                  , testCase "test_C_KS_Abst" test_C_KS_Abst
                  , testCase "test_C_IKBCW_Abst" test_C_IKBCW_Abst
                  , testCase "test_C_IKS_Abst" test_C_IKS_Abst
                  , testCase "test_B_KBCW_Abst" test_B_KBCW_Abst
                  , testCase "test_B_KS_Abst" test_B_KS_Abst
                  , testCase "test_B_IKBCW_Abst" test_B_IKBCW_Abst
                  , testCase "test_B_IKS_Abst" test_B_IKS_Abst
                  , testCase "test_W_KBCW_Abst" test_W_KBCW_Abst
                  , testCase "test_W_KS_Abst" test_W_KS_Abst
                  , testCase "test_W_IKBCW_Abst" test_W_IKBCW_Abst
                  , testCase "test_W_IKS_Abst" test_W_IKS_Abst
                  , testCase "test_S_KBCW_Abst" test_S_KBCW_Abst
                  , testCase "test_S_KS_Abst" test_S_KS_Abst
                  , testCase "test_S_IKBCW_Abst" test_S_IKBCW_Abst
                  , testCase "test_S_IKS_Abst" test_S_IKS_Abst
                 ]


prop_LambdaToCombKS :: LTerm VarString Untyped -> Bool
prop_LambdaToCombKS term = fromMaybe
                              (trace ("failed reduction term: " ++ pps (canonicalize term)) True)
                              prop
  where
    prop = do
        let term' = canonicalize term
        lr <- reduceS term'
        let ct :: CTerm KS =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        trace' "prop_LambdaToCombKS" lr cr resRed
           (return (lr == resRed))

trace' :: (Ord t, Ord t2) =>
                 (PP (LTerm VarString t), PP t1, PP (LTerm VarString t2)) =>
                 String -> LTerm VarString t -> t1 -> LTerm VarString t2 -> a -> a

trace' name lr cr resRed =
    trace
        (name ++ "\nin:\n" ++ pps (canonicalize lr) ++ "\ncon:\n" ++
         pps cr ++ "\nres:\n" ++
         pps (canonicalize resRed))

prop_LambdaToCombIKS :: LTerm VarString Untyped -> Bool
prop_LambdaToCombIKS term = fromMaybe
                               (trace ("failed reduction term: " ++ pps (canonicalize term)) True)
                               prop
  where
    prop = do
        let term' = canonicalize term
        lr <- reduceS term'
        let ct :: CTerm IKS =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        trace' "prop_LambdaToCombIKS" lr cr resRed
            return (lr == resRed)

prop_LambdaToCombIKBCW :: LTerm VarString Untyped -> Bool
prop_LambdaToCombIKBCW term = fromMaybe
                                 (trace ("failed reduction term: " ++ pps (canonicalize term)) True)
                                 prop
  where
    prop = do
        let term' = canonicalize term
        lr <- reduceS term'
        let ct :: CTerm IKBCW =  bracketAbstract lr
        cr <- reduceS ct
        let t2 = combToLambda cr
        resRed <- reduceS t2
        trace' "prop_LambdaToCombIKBCW" lr cr resRed
           (return (lr == resRed))

-- B BCKW
test_B_KBCW_Abst :: Assertion
test_B_KBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x (y z)"
    rterm = pparse "x (y z)"
    cterm :: CTerm KBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- B KS
test_B_KS_Abst :: Assertion
test_B_KS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x (y z)"
    rterm = pparse "x (y z)"
    cterm :: CTerm KS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- B IKBCW
test_B_IKBCW_Abst :: Assertion
test_B_IKBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x (y z)"
    rterm = pparse "x (y z)"
    cterm :: CTerm KBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- B IKS
test_B_IKS_Abst :: Assertion
test_B_IKS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x (y z)"
    rterm = pparse "x (y z)"
    cterm :: CTerm IKS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'


-- C KBCW
test_C_KBCW_Abst :: Assertion
test_C_KBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z y"
    rterm = pparse "x z y"
    cterm :: CTerm KBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- C KS
test_C_KS_Abst :: Assertion
test_C_KS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z y"
    rterm = pparse "x z y"
    cterm :: CTerm KS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- C IKBCW
test_C_IKBCW_Abst :: Assertion
test_C_IKBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z y"
    rterm = pparse "x z y"
    cterm :: CTerm IKBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- C IKS
test_C_IKS_Abst :: Assertion
test_C_IKS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z y"
    rterm = pparse "x z y"
    cterm :: CTerm IKS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- W KBCW
test_W_KBCW_Abst :: Assertion
test_W_KBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y. x y y"
    rterm = pparse "x y y"
    cterm :: CTerm KBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y"
    condReduced = reduceS cterm'

-- W KS
test_W_KS_Abst :: Assertion
test_W_KS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y. x y y"
    rterm = pparse "x y y"
    cterm :: CTerm KS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y"
    condReduced = reduceS cterm'

-- W IKBCW
test_W_IKBCW_Abst :: Assertion
test_W_IKBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y. x y y"
    rterm = pparse "x y y"
    cterm :: CTerm IKBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y"
    condReduced = reduceS cterm'

-- W IKS
test_W_IKS_Abst :: Assertion
test_W_IKS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y. x y y"
    rterm = pparse "x y y"
    cterm :: CTerm IKS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y"
    condReduced = reduceS cterm'

-- S KBCW
test_S_KBCW_Abst :: Assertion
test_S_KBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z (y z)"
    rterm = pparse "x z (y z)"
    cterm :: CTerm KBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- S KS
test_S_KS_Abst :: Assertion
test_S_KS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z (y z)"
    rterm = pparse "x z (y z)"
    cterm :: CTerm KS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- S IKBCW
test_S_IKBCW_Abst :: Assertion
test_S_IKBCW_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z (y z)"
    rterm = pparse "x z (y z)"
    cterm :: CTerm IKBCW     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'

-- S IKS
test_S_IKS_Abst :: Assertion
test_S_IKS_Abst =
    Just rterm @=? condReduced
  where
    lterm :: LTerm VarString Untyped = pparse "\\x y z.x z (y z)"
    rterm = pparse "x z (y z)"
    cterm :: CTerm IKS     = bracketAbstract lterm
    cterm'  = cterm :@ Var "x" :@ Var "y" :@ Var "z"
    condReduced = reduceS cterm'


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
