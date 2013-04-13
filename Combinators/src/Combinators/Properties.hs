-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Properties
-- Copyright   :  
-- License     :  AllRightsReserved
--
-- Maintainer  :  
-- Stability   :  
-- Portability :  
--
-- | Properties of combinators
--
-----------------------------------------------------------------------------
 
module Combinators.Properties (
    testProperties
) where

import Combinators.Language
import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?), assertBool)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)

-----------------------------------------------------------------------------
-- * Properties of combinators

-- | A term t is in weak normal form, iff M contains no redexes.
_isWeakNormal :: Basis basis v => Term basis v -> Bool
_isWeakNormal t = case oneStepReduction normalOrderStrategy t of
                    Left _ -> False
                    Right _ -> True -- term not changed, so no redex

-- | Is this weak extensional equality?
-- TODO
isWeakEqual :: Basis basis v => Term basis v -> Term basis v -> Bool
isWeakEqual t1 t2 = primTermEqual (normalOrderReduction t1) (normalOrderReduction t2)

primTermEqual :: Basis basis v => Term basis v -> Term basis v -> Bool
primTermEqual t1 t2 = snd (primTermEqual' [] t1 t2)
  where
    primTermEqual' env (Const a) (Const b) = (env,a == b)
    primTermEqual' env (Var a) (Var b) =
        case [(v1,v2) | (v1,v2) <- env, v1 == a] of
            [] -> ((a,b) : env, True)
            (_,v2):_ -> (env, b == v2)
    primTermEqual' env (l1 :@ r1) (l2 :@ r2) =
        let (newEnv,res) = primTermEqual' env l1 l2
        in if not res
                then (newEnv,False)
                else primTermEqual' newEnv r1 r2
    primTermEqual' env _ _ = (env,False)

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

-- | Computes the arity of a term
arity :: Basis basis v => Term basis v -> Maybe Int
arity t = arity' 0 (normalOrderReduction t)
  where
    arity' count (Const c) = Just (primArity c - count)
    arity' _count (Var _)  = Nothing
    arity' count (l :@ _)  = arity' (1 + count) l

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


spineList :: Basis basis v => Term basis v -> [Term basis v]
spineList = reverse . spineList'
  where
    spineList' co@(Const _)  = [co]
    spineList' va@(Var _)    = [va]
    spineList' (l :@ r)      = r : spineList l


-- | Is this combinator an identity combinator (like I) of any arity
isIdentity :: Basis basis v => Term basis v -> Bool
isIdentity term =
    case arity term of
        Nothing -> False
        Just i ->
            let vars     = map Var (varGen i)
                inTerm   = foldl (:@) term vars
                outTerm  = normalOrderReduction inTerm
                computed = spineList outTerm
            in vars == computed

-- example
testIdentity1 :: Assertion
testIdentity1 =   assertBool "testIdentity1"
    $ isIdentity (parseIKS "I")
testIdentity2 :: Assertion
testIdentity2 =   assertBool "testIdentity2"
    $ isIdentity (parseIKS "I (S K K)")
testIdentity3 :: Assertion
testIdentity3 =   assertBool "testIdentity3"
    $ isIdentity (parseIKS "S (K S) K I")
testIdentity4 :: Assertion
testIdentity4 =   assertBool "testIdentity4"
    $ not (isIdentity (parseIKS "S (K K) K I"))

{-
-- | Is this combinator an associator combinator (like B) of any arity > 3
isAssociator :: Basis basis v => Term basis v -> Bool
isAssociator term =
    case arity term of
        Nothing -> trace "no arity" False
        Just i | i < 3 -> trace ("i: " ++ show i) False
               | otherwise ->
            let vars     = trace ("i: " ++ show i) $ map Var (varGen i)
                inTerm   = trace ("vars" ++ show vars) $ foldl (:@) term vars
                outTerm  = trace ("inTerm" ++ show inTerm) $ normalOrderReduction inTerm
            in trace ("outTerm" ++ show outTerm) $ not (leftAssociated outTerm)


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
                    testCase "testArity3" testArity3,
                    testCase "testIdentity1" testIdentity1,
                    testCase "testIdentity2" testIdentity2,
                    testCase "testIdentity3" testIdentity3,
                    testCase "testIdentity4" testIdentity4]
{-                    
                    testCase "testAssociator1" testAssociator1,
                    testCase "testAssociator2" testAssociator2,
                    testCase "testAssociator3" testAssociator3,
                    testCase "testAssociator4" testAssociator4
-}    



