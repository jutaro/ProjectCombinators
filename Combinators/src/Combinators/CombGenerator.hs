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
-- |
--
-----------------------------------------------------------------------------

module Combinators.CombGenerator where

import Combinators.Combinator
import Combinators.Variable
import Combinators.Term

import Data.Array.Unboxed
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)

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

printStruct :: BinaryTreeStruct -> String
printStruct a = map (\e -> if e then '1' else '0') (elems a)

-- Generate combinators with n nodes (and n+1 leaves), with all structures and filled with array
-- contents
genCombs :: (PP (CTerm basis v),Variable v, Basis basis v) => Int -> [Combinator basis v] -> [CTerm basis v]
genCombs n combs =
    let treeStructs = genBinaryTreeStructs n
    in map ((\ (r,_,_) -> r) . (gen combs 1)) treeStructs
      where
        gen combList index ts | index > snd (bounds ts) || not (ts ! index) =
            (Const (head combList), index+1,(tail combList))
                              | otherwise =
            let (left,index', combList') = gen combList (index +1) ts
                (right,index'', combList'') = gen combList' (index') ts
            in (left :@ right,index'',combList'')

allCombsN :: (PP (CTerm basis v),Variable v, Basis basis v) => Int -> [CTerm basis v]
allCombsN = undefined

allCombs :: (PP (CTerm basis v),Variable v, Basis basis v) => [CTerm basis v]
allCombs = concatMap allCombsN [2..]

-- * Testing
prop_TreeGen :: Int -> Bool
prop_TreeGen n =  if n >= 1 && n < 20
                    then  length (genBinaryTreeStructs n) == fromIntegral (catalans !! n)
                    else True

testCombGenerator :: [Test]
testCombGenerator = [testProperty "prop_TreeGen" prop_TreeGen]

