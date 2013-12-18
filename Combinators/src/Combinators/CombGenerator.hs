{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, GADTs #-}
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
-----------------------------------------------------------------------------

module Combinators.CombGenerator where

import Combinators.Combinator
import Combinators.BinaryTree

import Data.Array.Unboxed
import Control.Monad (replicateM)
import Data.List (findIndex, foldl')

-----------------------------------------------------------------------------
-- * Generation/Enumerations of Combinators with rank, unrank and length functions
-----------------------------------------------------------------------------

-- | Produces a list of catalan numbers
catalans :: [Integer]
catalans = 1 : map (\n -> sum $ zipWith (*) (reverse (take n catalans)) catalans) [1..]

-- Encoding of binary trees
-- True stands for an internal node
-- False stands for a leaf
-- The order is a preorder traversal
-- The last leaf is left out
type BinaryTreeStruct = UArray Int Bool

-- | preorderLeaves
treeStructFromBinaryTree :: BinaryTree t => t -> BinaryTreeStruct
treeStructFromBinaryTree t = array (1,length btList) (zip [1..] btList)
  where
    btList = makeList t
    makeList t = case decompose t of
                        Nothing -> [False]
                        Just (l,r)  -> True : makeList l ++ makeList r

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

-- | Number of internal nodes of the given tree struct
treeStructNodes :: BinaryTreeStruct -> Int
treeStructNodes seq =  div (fromIntegral $ snd (bounds seq)) 2

-- | Ranking for a certain number of internal noes
rankTreeStruct :: BinaryTreeStruct -> Integer
rankTreeStruct seq = rank' 0 n 1 (n - 1)
  where
    table = initGFuncTable n
    n = treeStructNodes seq
    rank' r k i m | i <= 2 * n && m >= 0 = if seq ! i == True
                                        then rank' r k (i+1) (m-1)
                                        else rank' (r + gfunc table k m) (k-1) (i+1) m
                  | otherwise     = r + 1

-- | Unranking for a certain number of internal noes
unrankTreeStruct :: Int -> Integer -> BinaryTreeStruct
unrankTreeStruct n r = unrank' initialArray 1 (n-1) n r
  where
    initialArray = array (1,n*2) [(i, False) | i <- [1..n*2]]
    table = initGFuncTable n
    unrank' array i m k r'
        | i <= 2 * n && m >= 0 = let t = gfunc table k m
                              in if r' > t
                                then unrank' array (i+1) m (k-1) (r'-t)
                                else unrank' (array // [(i,True)]) (i+1) (m-1) k r'
        | otherwise         = array

-- | Ranking for any number of internal noes
grankTreeStruct :: BinaryTreeStruct -> Integer
grankTreeStruct ts = let n = treeStructNodes ts
                     in (sum (take n catalans)) + rankTreeStruct ts

-- | Unranking for any number of internal noes
gunrankTreeStruct :: Integer -> BinaryTreeStruct
gunrankTreeStruct r = unrank 0 r
  where
    unrank n r' = let c = catalans !! n
                  in if r' <= c
                        then unrankTreeStruct n r'
                        else unrank (n + 1) (r' - c)

-- Returns a two dimensional array with precomputed values
initGFuncTable :: Int -> [[Integer]]
initGFuncTable n = reverse $ foldl' (\ accu k' -> computeRow k' accu) [] [1..n]
  where
    computeRow :: Int -> [[Integer]] -> [[Integer]]
    computeRow _k' [] =  [[1]]
    computeRow k' accu@(last:_) =
        map (\ l' -> 1 + sum (take l' last)) [1..k'] : accu

gfunc ::  [[Integer]] -> Int -> Int -> Integer
gfunc _table 1 _ =  1
gfunc _table _ 0 =  1
gfunc table k l =  (table !! (k-1)) !! (l-1)

printStruct :: BinaryTreeStruct -> String
printStruct a = map (\e -> if e then '1' else '0') (elems a)

-- | Generates an infinite List of all possible combinators of this basis
genCombs :: (PP (CTerm basis), Basis basis) => [CTerm basis]
genCombs = concatMap genCombsN [0..]

-- | Generate instances of a combinatory basis with n + 1 combinators.
genCombsN :: forall b.(PP (CTerm b),Basis b) => Int -> [CTerm b]
genCombsN n = concatMap (genCombsTree n) permutations
  where
    primitiveCombinators :: [Combinator b] = primCombs
    permutations = replicateM (n+1) primitiveCombinators

-- | Generate combinators with n nodes (and n+1 leaves), with all structures and filled with array
-- contents
genCombsTree :: (PP (CTerm basis), Basis basis) =>
                    Int -> [Combinator basis] -> [CTerm basis]
genCombsTree n combs =
    let treeStructs = genBinaryTreeStructs n
    in map ((\ (r,_,_) -> r) . (gen combs 1)) treeStructs

-- Helper function for Term building
gen :: Basis basis =>
         [Combinator basis]
         -> Int -> BinaryTreeStruct -> (CTerm basis, Int, [Combinator basis])
gen combList index ts | index > snd (bounds ts) || not (ts ! index) =
    (Const (head combList), index+1,(tail combList))
                      | otherwise =
    let (left,index', combList') = gen combList (index +1) ts
        (right,index'', combList'') = gen combList' (index') ts
    in (left :@ right,index'',combList'')

sizeGenCombsN :: forall b. Basis b => b -> [Integer]
sizeGenCombsN _ = map (\n -> (catalans !! n) * (fromIntegral (length primitiveCombinators) ^ (n+1))) [0..]
  where
    primitiveCombinators :: [Combinator b] = primCombs

-- | Ranking for any number of internal noes
rankComb :: forall basis . Basis basis => CTerm basis -> Integer
rankComb term = -- trace ("n: " ++ show n ++
--                        " rank: " ++ show rankNum ++
--                        " perm: " ++ show permNum ++
--                        " cata: " ++   show cataNum) $
                rankNum + permNum + cataNum
  where
    rankNum = rankTreeStruct ts
    permNum = (catalans !! n) * fromIntegral permIndex
    cataNum = sum (map (\i -> (catalans !! (i-1)) *
                        ((fromIntegral (length primCombis)) ^ i)) [1..n])

    n = nodeSize term
    primCombis = primCombs :: [Combinator basis]
    perm = replicateM (n+1) primCombs
    leaves = preorderLeaves term
    permIndex = case findIndex (== (map (\ t -> case t of
                                                (Const c)  -> c
                                                (Var _v)   -> error "CombGenerator>>rankCombs: not a pure combinator"
                                                (_l :@ _r) -> error "CombGenerator>>rankCombs: impossible in leave"
                                                ) leaves)) perm of
                Just i -> i
                Nothing -> error "CombGenerator>>rankCombs: unknown permutation index"
    ts = treeStructFromBinaryTree term

-- | Unranking for any number of internal noes
unrankComb :: forall basis. Basis basis => Integer -> CTerm basis
unrankComb r = unrank 0 (r - 1)
  where
    unrank n r' = let c = catalans !! n
                      num = c * (fromIntegral (length primCombinators) ^ (n+1))
                  in -- trace ("unrank' n: " ++ show n ++ " r':" ++ show r' ++ " num: " ++ show num) $
                     if r' >= num
                        then unrank (n + 1) (r' - num)
                        else
                            let (permIndex,tsIndex) = divMod r' c
                                ts = unrankTreeStruct n (tsIndex +1)
                                permutations = replicateM (n+1) primCombinators
                                perm = permutations !! fromIntegral permIndex
                                (r,_,_) = gen perm 1 ts
                            in --trace ("n: " ++ show n ++ " c: " ++ show c ++ " permIndex: " ++ show permIndex ++
                               --         " tsIndex: " ++ show tsIndex) $
                               r
    primCombinators :: [Combinator basis] = primCombs

