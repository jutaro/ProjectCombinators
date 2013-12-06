{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombGenerator
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- | Generation/Enumerations of Combinators with rank, unrank and length functions
--
-----------------------------------------------------------------------------

module Combinators.CombGenerator where

import Combinators.Combinator
import Combinators.Variable
import Combinators.Term

import Data.Array.Unboxed
import qualified Data.Map as Map
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Control.Monad (replicateM)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (atomicModifyIORef, IORef, readIORef, newIORef)

-- | Produces a list of catalan numbers
catalans :: [Integer]
catalans = 1 : map (\n -> sum $ zipWith (*) (reverse (take n catalans)) catalans) [1..]

-- Encoding of binary trees
-- True stands for an internal node
-- False stands for a leaf
-- The order is a preorder traversal
-- The last leaf is left out
type BinaryTreeStruct = UArray Int Bool

-- | Generate all possible binary trees with n nodes in B-order
--  Algorithm from Ahrabian
-- |
genBinaryTreeStructs :: Int -> [BinaryTreeStruct]
genBinaryTreeStructs n = gen initialArray n (n-1) 1
  where
    initialArray = array (1,n*2) [(i, i <= n) | i <- [1..n*2]]
    gen seq k l q = let newSeq = if k < n then seq // [(2*n-k-l,False),(2*n-k-l+1,True)] else seq
                    in newSeq : (if k > 1
                                    then (gen newSeq (k-1) 1 l) ++
                                        if l < k && l < q
                                            then gen newSeq k (l+1) q
                                            else []
                                    else [])

rankTreeStruct :: BinaryTreeStruct -> Integer
rankTreeStruct seq = rank' 0 n 1 (n - 1)
  where
    n = div (fromIntegral $ snd (bounds seq)) 2
    rank' r k i m | i <= 2 * n && m >= 0 = if seq ! i == True
                                        then rank' r k (i+1) (m-1)
                                        else rank' (r+gfunc k m) (k-1) (i+1) m
                  | otherwise     = r + 1


gfunc :: Int -> Int -> Integer
gfunc 1 _ = 1
gfunc _ 0 = 1
gfunc k l = 1 + sum (map (\ j -> gfunc (k-1) j) [1..l])

{-
gfuncMem :: Map.Map (Int,Int) Integer -> Int -> Int -> Integer
gfuncMem _gmap 1 _ = 1
gfuncMem _gmap _ 0 = 1
gfuncMem  gmap k l = case Map.lookup (k,l) map  of
                        Nothing  -> let res = 1 + sum (map (\ j -> gfuncMem (k-1) j) [1..l])
                                    in Map.insert (k,l) res map
                        Just n -> n

gfunc :: Int -> Int -> Integer
gfunc 1 _ = 1
gfunc _ 0 = 1
gfunc k l = gfunc k (l-1) + gfunc (k-1) l
-- gfunc k l | otherwise = error "CombGenerator>>gfunc: Illegal parameter l >= k"
-}



printStruct :: BinaryTreeStruct -> String
printStruct a = map (\e -> if e then '1' else '0') (elems a)

-- | Generates an infinite List of all possible combinators of this basis
genCombs :: (PP (CTerm basis v),Variable v, Basis basis v) => [CTerm basis v]
genCombs = concatMap genCombsN [0..]

-- | Generate instances of a combinatory basis with n + 1 combinators.
genCombsN :: forall b v.(PP (CTerm b v),Variable v, Basis b v) => Int -> [CTerm b v]
genCombsN n = concatMap (genCombsTree n) permutations
  where
    primitiveCombinators :: [Combinator b v] = primCombs
    permutations = replicateM (n+1) primitiveCombinators

-- | Generate combinators with n nodes (and n+1 leaves), with all structures and filled with array
-- contents
genCombsTree :: (PP (CTerm basis v),Variable v, Basis basis v) =>
                    Int -> [Combinator basis v] -> [CTerm basis v]
genCombsTree n combs =
    let treeStructs = genBinaryTreeStructs n
    in map ((\ (r,_,_) -> r) . (gen combs 1)) treeStructs
      where
        gen combList index ts | index > snd (bounds ts) || not (ts ! index) =
            (Const (head combList), index+1,(tail combList))
                              | otherwise =
            let (left,index', combList') = gen combList (index +1) ts
                (right,index'', combList'') = gen combList' (index') ts
            in (left :@ right,index'',combList'')

sizeGenCombsN :: forall b. Basis b VarString => b -> [Integer]
sizeGenCombsN _ = map (\n -> (catalans !! n) * (fromIntegral (length primitiveCombinators) ^ (n+1))) [0..]
  where
    primitiveCombinators :: [Combinator b VarString] = primCombs

-- * Testing
prop_TreeGen :: Int -> Bool
prop_TreeGen n =  if n >= 1 && n < 15
                    then  length (genBinaryTreeStructs n) == fromIntegral (catalans !! n)
                    else True

-- * Testing
prop_CombGen :: Int -> Bool
prop_CombGen n =  if n >= 1 && n < 10
                    then  fromIntegral (length (genCombsN n :: [CTerm KS VarString])) ==
                            (sizeGenCombsN (undefined :: KS) !! n)
                    else True

testCombGenerator :: [Test]
testCombGenerator = [testProperty "prop_TreeGen" prop_TreeGen]

