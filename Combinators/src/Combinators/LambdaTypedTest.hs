-----------------------------------------------------------------------------
--
-- Module      :  Combinators.LambdaTypedTest
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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.LambdaTypedTest (
    testLambdaTyped
) where

import Combinators.LambdaTest ()
import Combinators.LambdaTyped (inhabitants, typeLambda')
import Combinators.Types (Untyped(..), SType)
import Combinators.PrintingParsing (PP(..))
import Combinators.Lambda (LTerm)
import Combinators.Variable (VarString)

import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit ((@=?), Assertion)

import Test.QuickCheck (Arbitrary)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Debug.Trace (trace)
import Data.List (sort)

-- ** Testing

testLambdaTyped :: [Test]
testLambdaTyped = [testCase "testInhabitant1" testInhabitant1
                , testCase "testInhabitant2" testInhabitant2
                , testCase "testInhabitant3" testInhabitant3
                , testCase "testInhabitant4" testInhabitant4
                , testCase "testInhabitant5" testInhabitant5
                , testCase "testInhabitant6" testInhabitant6
                , testCase "testInhabitant7" testInhabitant7
                , testCase "testInhabitant8" testInhabitant8
                , testProperty "prop_printParse" prop_printParse
             ]

instance Arbitrary (LTerm VarString SType) where
    arbitrary = do
        t :: LTerm VarString Untyped <- arbitrary
        case typeLambda' t of
            Just tl -> return tl
            Nothing -> arbitrary

--  For any term: print and parse give the original term
prop_printParse :: LTerm VarString SType -> Bool
prop_printParse term = trace ("\n\n" ++ pps term ++ "\n" ++
                                    pps ((pparse :: String -> LTerm VarString SType) (pps term))
                            ++ "\n\n" ++ show term ++ "\n" ++
                                    show ((pparse :: String -> LTerm VarString SType) (pps term))) $
                                        term == pparse (pps term)

-- | Identity
testInhabitant1 :: Assertion
testInhabitant1 =
    let typeString = "a -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 5
    in inh @=? (pparse :: String -> [LTerm VarString SType]) "[\\u:a.u]"

-- | Cancellator
testInhabitant2 :: Assertion
testInhabitant2 =
    let typeString = "a -> a -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 5
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType]) "[\\u:a v:a.u, \\u:a v:a.v]")

-- |
testInhabitant3 :: Assertion
testInhabitant3 =
    let typeString = "a -> ((c -> b) -> a) -> b -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 5
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType])
        "[\\u:a v:(c -> b) -> a w:b.a,\\u:a v:(c -> b) -> a w:b.v(\\x:c.w)]")

-- | Pierces Law
testInhabitant4 :: Assertion
testInhabitant4 =
    let typeString = "((a -> b) -> a) -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 5
    in sort inh @=? []

-- | Church Numerals
testInhabitant5 :: Assertion
testInhabitant5 =
    let typeString = "(a -> a) -> a -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 3
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType])
                        "[\\u:a -> a v:a.v,\n \\u:a -> a v:a.u v,\n \\u:a -> a v:a.u (u v)]")

-- | Words over alphabet
testInhabitant6 :: Assertion
testInhabitant6 =
    let typeString = "(a -> a) -> (a -> a) -> a -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 3
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType])
                        ("[\\u:a -> a v:a -> a w:a.w,"
                         ++ "\\u:a -> a v:a -> a w:a.v w,"
                         ++ "\\u:a -> a v:a -> a w:a.u w,"
                         ++ "\\u:a -> a v:a -> a w:a.v (v w),"
                         ++ "\\u:a -> a v:a -> a w:a.u (v w),"
                         ++ "\\u:a -> a v:a -> a w:a.v (u w),"
                         ++ "\\u:a -> a v:a -> a w:a.u (u w)]"))

-- |
testInhabitant7 :: Assertion
testInhabitant7 =
    let typeString = "(a -> b -> c) -> b -> a -> c"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 3
    in inh @=? ((pparse :: String -> [LTerm VarString SType])
                        "[\\u:a -> b -> c v:b w:a.u v v]")

-- | New binder
testInhabitant8 :: Assertion
testInhabitant8 =
    let typeString = "((a -> a) -> a) -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 4
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType])
                        ("[\\u:(a -> a) -> a.u \\v:a.v,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.w,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.v,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.x,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.w,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.v]"))

-- | Monster
testInhabitant9 :: Assertion
testInhabitant9 =
    let typeString = "(((a -> a) -> a) -> a) -> a -> a"
        tst = (pparse :: String -> SType) typeString
        inh = inhabitants tst 4
    in sort inh @=? sort ((pparse :: String -> [LTerm VarString SType])
                        ("[\\u:(a -> a) -> a.u \\v:a.v,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.w,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.v,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.x,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.w,"
                         ++ "\\u:(a -> a) -> a.u \\v:a.u \\w:a.u \\x:a.v]"))

