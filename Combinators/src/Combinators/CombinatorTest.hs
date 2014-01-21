{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombinatorTest
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

module Combinators.CombinatorTest where

import Combinators

import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?), assertBool)
import Test.QuickCheck
       (elements, oneof, sized,Arbitrary(..))
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)
import Control.Monad (liftM2, liftM)
import Data.Maybe (fromJust)
import Data.List (nub)

parseIKS :: String -> CTerm IKS
parseIKS = pparse

sIKS, kIKS, iIKS :: Combinator IKS
sIKS = s
iIKS = i
kIKS = k

--  For any term: print and parse give the original term
prop_spineLength :: CTerm IKS -> Bool
prop_spineLength term = length (leftSpine term) == leftSpineLength term

-- example
testPp :: Assertion
testPp = assertBool "pp"
    ((pparse "S K (K v)" :: CTerm IKS) == (Const sIKS :@ Const kIKS)
                                                    :@ (Const kIKS :@ Var "v"))

-- example
testParse :: Assertion
testParse = assertBool "parse"
    ((show . pp) (pparse "S K (K v)" :: CTerm IKS) == "S K (K v)")

-- ** Testing

instance Arbitrary (CTerm IKS) where
    arbitrary = sized $ \_n -> oneof
        [liftM Const (elements primCombs),
            liftM Var (elements ["u","v","w","x","y","z"]),
            liftM2 (:@) arbitrary arbitrary]



--  For any term: print and parse give the original term
prop_printParse :: CTerm IKS -> Bool
prop_printParse term = term == parseIKS ((show . pp) term)

-----------------------------------------------------------------------------
-- * Subterms

-- example:
testSubterm :: Assertion
testSubterm = assertBool "subterm"
        (subterm (Const iIKS :@ Var "x") (Var "x" :@ (Const iIKS :@ Var "x") :@ Var "y"))

-- example
testAllSubterms :: Assertion
testAllSubterms = assertBool "allSubterms"
    (length (nub (allSubterms  (Var "x" :@ (Const iIKS :@ Var "x") :@ Var "y"))) == 6)

-----------------------------------------------------------------------------
-- * Substitution

-- example
testSubstitute :: Assertion
testSubstitute =  assertBool "testSubstitute"
    (substitute "y" (Var "y" :@ Var "y")
        (substitute "x" (Const iIKS) (Const sIKS :@ Var "x" :@ Var "y" :@ Var "z"))
            == ((Const sIKS :@ Const iIKS) :@ (Var "y" :@ Var "y")) :@ Var "z")

--example
testLeftAssociated :: Assertion
testLeftAssociated =  assertBool "testLeftAssociated"
    (leftAssociated (Const iIKS :@ Var "x" :@ Var "y") &&
    not (leftAssociated (Const iIKS :@ (Var "x" :@ Var "y"))))

-----------------------------------------------------------------------------
-- * Head Reduction

-- example
testRedex :: Assertion
testRedex =   assertBool "testRedex"
    (redex (Const iIKS :@ Var "x" :@ Var "y") == Just (iIKS,[Var "x", Var "y"]))


-- example
testZipTerm :: Assertion
testZipTerm =
    term @=? unzipper (zipper term)
  where
    term = parseIKS "S K K x"

-- examples
testZipMove1 :: Assertion
testZipMove1 =
    term @=? (unzipper . fromJust . zipUp . fromJust . zipDownLeft . zipper) term
  where
    term = parseIKS "S K K x"

testZipMove2 :: Assertion
testZipMove2 =
    term @=? (unzipper . fromJust . zipUp .  fromJust . zipUp .  fromJust .
                zipDownLeft .  fromJust . zipDownRight . zipper) term
  where
    term = parseIKS "S K (K x)"

-- examples
testZipRoot :: Assertion
testZipRoot =
    term @=? (zipSelected . zipRoot . fromJust . zipDownRight .
            fromJust . zipDownLeft . fromJust . zipDownLeft . zipper) term
  where
    term = parseIKS "S K K x"

testZipIsRoot :: Assertion
testZipIsRoot =  assertBool "testZipIsRoot"  $
    (zipIsRoot . zipRoot .  fromJust . zipDownLeft .  fromJust . zipDownRight . zipper) term
  where
    term = parseIKS "S K (K x)"

testZipIsNotRoot :: Assertion
testZipIsNotRoot =  assertBool "testZipIsNotRoot"
    ( not ((zipIsRoot . fromJust . zipDownLeft .  fromJust . zipDownRight . zipper) term))
  where
    term = parseIKS "S K (K x)"

-- example
--  (map pp . map zipSelected . zipEnum . zipper) (parseIKS "S (K x) (K x)")

-- ** Testing

instance Arbitrary (BTZipper (CTerm IKS)) where
    arbitrary = do
        term <- arbitrary
        elements (zipEnum (zipper term))

-- | A root is a root
prop_zipRoot :: BTZipper (CTerm IKS) -> Bool
prop_zipRoot m = zipIsRoot (zipRoot m)

-- | up after down is identity
prop_upDown1 :: BTZipper (CTerm IKS) -> Bool
prop_upDown1 zip' = case zipSelected zip' of
                    _ :@ _ -> zip' == (fromJust . zipUp . fromJust . zipDownLeft) zip'
                    _ -> True

-- | down after up is identity, when the position is recovered
prop_upDown2 ::  BTZipper (CTerm IKS) -> Bool
prop_upDown2 zip' = case zipAnchestors zip' of
                    []          -> True
                    Left _ : _  -> zip' == (fromJust . zipDownRight . fromJust . zipUp) zip'
                    Right _ : _ -> zip' == (fromJust . zipDownLeft . fromJust . zipUp) zip'

-- example
testReduction1 :: Assertion
testReduction1 =
    parseIKS "v" @=? (reduceSForce . parseIKS) "S K (K x y) (I v)"

testReduction2 :: Assertion
testReduction2 =
    parseIKS "x" @=? (reduceSForce . parseIKS) "S(S(K S)(S(K K)K))(K(S(K K))) x y"

testReduction3 :: Assertion
testReduction3 =
    parseIKS "x z(y z)" @=? (reduceSForce . parseIKS)
                            "S(S(K S)(S(K(S(K S)))(S(K(S(K K)))S)))(K(K(S K K))) x y z"
testReduction4 :: Assertion
testReduction4 =
    parseIKS "K (x y)" @=? (reduceSForce . parseIKS) "S (K K) x y"

testReduction5 :: Assertion
testReduction5 =
    parseIKS "x y" @=? (reduceSForce . parseIKS) "S(S(K S)(S(K K)(S(K S)K)))(K K) x y z"

testReduction6 :: Assertion
testReduction6 =
    parseIKS "x z" @=? (reduceSForce . parseIKS) "S(K S)(S(K K)) x y z"

testReduction7 :: Assertion
testReduction7 =
    parseIKS "x z" @=? (reduceSForce . parseIKS)
                            "S(K K)(S(S(K S)(S(K K)(S K K)))(K(S K K))) x y z"

testReduction8 :: Assertion
testReduction8 =
    parseIKS "x u (z u) (y u (z u))" @=? (reduceSForce . parseIKS)
                            "S(K(S(K S)))(S(K S)(S(K S))) x y z u"

testReduction9 :: Assertion
testReduction9 =
    parseIKS "x u (z u) (y u (z u))" @=? (reduceSForce . parseIKS)
                            "S(S(K S)(S(K K)(S(K S)(S(K(S(K S)))S))))(K S) x y z u"

testReduction10 :: Assertion
testReduction10 =
    parseIKS "x" @=? (reduceSForce . parseIKS)
                           "S K K x"

testReduction11 :: Assertion
testReduction11 =
    parseIKS "x y" @=? (reduceSForce . parseIKS)
                           "S(S(K S)K)(K(S K K)) x y"

testReduction12 :: Assertion
testReduction12 =
    parseIKS "x y" @=? (reduceSForce . parseIKS)
                           "S(S(K S)K)(K I) x y"

testReduction13 :: Assertion
testReduction13 =
    parseIKS "x z" @=? (reduceSForce . parseIKS)
                           "S(K S)(S(K K)) x y z"


testLanguage :: [Test]
testLanguage = [testCase "testSubterm" testSubterm,
                    testCase "testAllSubterms" testAllSubterms,
                    testProperty "testSpineLength" prop_spineLength,
                    testCase "testPp" testPp,
                    testCase "testParse" testParse,
                    testProperty "prop_printParse" prop_printParse,
                    testCase "testSubstitute" testSubstitute,
                    testCase "testLeftAssociated" testLeftAssociated,
                    testCase "testRedex" testRedex,
                    testCase "testZipTerm" testZipTerm,
                    testCase "testZipMove1" testZipMove1,
                    testCase "testZipMove2" testZipMove2,
                    testCase "testZipRoot" testZipRoot,
                    testCase "testZipIsRoot" testZipIsRoot,
                    testCase "testZipIsNotRoot" testZipIsNotRoot    ,
                    testProperty "prop_zipRoot" prop_zipRoot,
                    testProperty "prop_upDown1" prop_upDown1,
                    testProperty "prop_upDown2" prop_upDown2,
                    testCase "testReduction1" testReduction1,
                    testCase "testReduction2" testReduction2,
                    testCase "testReduction3" testReduction3,
                    testCase "testReduction4" testReduction4,
                    testCase "testReduction5" testReduction5,
                    testCase "testReduction6" testReduction6,
                    testCase "testReduction7" testReduction7,
                    testCase "testReduction8" testReduction8,
                    testCase "testReduction9" testReduction9,
                    testCase "testReduction10" testReduction10,
                    testCase "testReduction11" testReduction11,
                    testCase "testReduction12" testReduction12,
                    testCase "testReduction13" testReduction13
                                        ]


