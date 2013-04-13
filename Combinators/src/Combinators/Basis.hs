{-# LANGUAGE EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC  #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Basis
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Alternative basis for Combinatory logic
--
-----------------------------------------------------------------------------

module Combinators.Basis where

import Combinators.Language
import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?))
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)

data BCKW

-- | Definition of the combinators for the IKS Basis
bBCKW, cBCKW, kBCKW, wBCKW :: Variable v => Combinator BCKW v

bBCKW = Combinator "B" [varString "__x",varString "__y",varString "__z"] 
            (Var (varString "__x") :@ (Var (varString "__y") :@ Var (varString "__z")))
cBCKW = Combinator "C" [varString "__x",varString "__y",varString "__z"] 
            ((Var (varString "__x") :@ Var (varString "__z")) :@ Var (varString "__y"))
kBCKW = Combinator "K" [varString "__x", varString "__y"] 
            (Var (varString "__x"))
wBCKW = Combinator "W" [varString "__x", varString "__y"]
            (Var (varString "__x") :@ Var (varString"__y") :@ Var (varString "__y"))
 

instance Variable v => Basis BCKW v where
    primCombs = [bBCKW, cBCKW, kBCKW, wBCKW]

parseBCKW :: String -> Term BCKW VarString
parseBCKW = parse :: String -> Term BCKW VarString
    
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
    