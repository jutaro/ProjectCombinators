-----------------------------------------------------------------------------
--
-- Module      :  Combinators.PropertiesTest
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

module Combinators.PropertiesTest where

import Combinators

import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?), assertBool)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)

parseIKS :: String -> CTerm IKS
parseIKS = pparse

-- example
testWeakEqual1 :: Assertion
testWeakEqual1 =  assertBool "testWeakEqual1"
    (isWeakEqual (parseIKS "S K (K x y) (I v)") (parseIKS "z"))
testWeakEqual2 :: Assertion
testWeakEqual2 =  assertBool "testWeakEqual2"
    (isWeakEqual (parseIKS "S(S(K S)(S(K K)K))(K(S(K K))) x y") (parseIKS "K z v"))
testWeakEqual3 :: Assertion
testWeakEqual3 =  assertBool "testWeakEqual3"
    (not (isWeakEqual (parseIKS "S(S(K S)(S(K K)K))(K(S(K K)))") (parseIKS "K")))

-- example
testArity1 :: Assertion
testArity1 =
    Just 3 @=? arity (parseIKS "S")

testArity2 :: Assertion
testArity2 =
    Just 2 @=? arity (parseIKS "S (I I)")

testArity3 :: Assertion
testArity3 =
    Nothing @=? arity (parseIKS "v (I I)")


-- example
--testIdentity1 :: Assertion
--testIdentity1 =   assertBool "testIdentity1"
--    $ isIdentity (parseIKS "I")
--testIdentity2 :: Assertion
--testIdentity2 =   assertBool "testIdentity2"
--    $ isIdentity (parseIKS "I (S K K)")
--testIdentity3 :: Assertion
--testIdentity3 =   assertBool "testIdentity3"
--    $ isIdentity (parseIKS "S (K S) K I")
--testIdentity4 :: Assertion
--testIdentity4 =   assertBool "testIdentity4"
--    $ not (isIdentity (parseIKS "S (K K) K I"))

{-
--example
testAssociator1 :: Assertion
testAssociator1 =   assertBool "testAssociator1"
    $ isAssociator (parseIKS "S (K S) K")

testAssociator2 :: Assertion
testAssociator2 =   assertBool "testAssociator2"
    $ isAssociator (parseIKS "I (S K K)")

testAssociator3 :: Assertion
testAssociator3 =   assertBool "testAssociator3"
    $ isAssociator (parseIKS "S (K S) K I")

testAssociator4 :: Assertion
testAssociator4 =   assertBool "testAssociator4"
    $ not (isAssociator (parseIKS "S (K S) K"))
-}


testProperties :: [Test]
testProperties = [testCase "testWeakEqual1" testWeakEqual1,
                    testCase "testWeakEqual2" testWeakEqual2,
                    testCase "testWeakEqual3" testWeakEqual3,
                    testCase "testArity1" testArity1,
                    testCase "testArity2" testArity2,
                    testCase "testArity3" testArity3
--                    testCase "testIdentity1" testIdentity1,
--                    testCase "testIdentity2" testIdentity2,
--                    testCase "testIdentity3" testIdentity3,
--                    testCase "testIdentity4" testIdentity4
                    ]
{-
                    testCase "testAssociator1" testAssociator1,
                    testCase "testAssociator2" testAssociator2,
                    testCase "testAssociator3" testAssociator3,
                    testCase "testAssociator4" testAssociator4
-}
