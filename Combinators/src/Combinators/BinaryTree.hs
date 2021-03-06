{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.ARS
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-----------------------------------------------------------------------------

module Combinators.BinaryTree where

import Data.Maybe (isNothing)

-----------------------------------------------------------------------------
-- * Binary tree class and a Zipper for it
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** A class for a binary tree
-----------------------------------------------------------------------------

-- | A binary tree may have a right or left subpart
class BinaryTree t where
    decompose :: t -> Maybe (t,t)
    -- ^ Returns the left and right subparts of a tree, if it is not a leaf
    (@@) :: t -> t -> t
    -- ^ Constructs a tree from its left and right subparts
    isLeaf :: t -> Bool
    isLeaf = isNothing . decompose
    -- ^ Is this a leaf

-----------------------------------------------------------------------------
-- ** Basic functions on binary trees
-----------------------------------------------------------------------------

-- | The leaves of the tree as a list in preorder
preorderLeaves :: BinaryTree t => t -> [t]
preorderLeaves t = case decompose t of
                    Just (l,r) -> preorderLeaves l ++ preorderLeaves r
                    Nothing -> [t]

-- | The left spine of the tree as a list
leftSpine :: BinaryTree t => t -> [t]
leftSpine = reverse . spine'
  where
    spine' t = case decompose t of
                Just (l,r) -> (r : spine' l)
                Nothing -> [t]

-- | The length of the left spine of the tree
leftSpineLength :: BinaryTree t => t -> Int
leftSpineLength t = case decompose t of
                 Just (l,_r) ->  1 + leftSpineLength l
                 _ -> 1

-- | The right spine of the tree as a list
rightSpine :: BinaryTree t => t -> [t]
rightSpine = reverse . spine'
  where
    spine' t = case decompose t of
                Just (l,r) -> (l : spine' r)
                Nothing -> [t]

-- | The length of the right spine of the tree
rightSpineLength :: BinaryTree t => t -> Int
rightSpineLength t = case decompose t of
                 Just (_l,r) ->  1 + rightSpineLength r
                 _ -> 1

-- | The number of nodes of the tree
nodeSize :: BinaryTree t => t -> Int
nodeSize t = case decompose t of
                Nothing -> 0
                Just (l,r) -> 1 + nodeSize l + nodeSize r

-- | The number of leaves of the tree
leafSize :: BinaryTree t => t -> Int
leafSize t = case decompose t of
                Nothing -> 1
                Just (l,r) -> leafSize l + leafSize r

-----------------------------------------------------------------------------
-- ** Zipper
-----------------------------------------------------------------------------

-- | This is a zipper for a term, which is a structure which carries a term and a
-- position in the term, without the possibility of an invalid position.
data BTZipper t where
    BTZipper :: BinaryTree t =>
        {zipSelected :: t,
        zipAnchestors :: [Either t t]} ->  BTZipper t

deriving instance Eq t => Eq (BTZipper t)
deriving instance Show t => Show (BTZipper t)

-- | Construct a 'BTZipper' from a 'Term' with the root as selected element.
zipper :: BinaryTree t => t -> BTZipper t
zipper term = BTZipper
  { zipSelected     = term
  , zipAnchestors   =   []
  }

-- | Returns the (root) 'Term' in the zipper
unzipper :: BinaryTree t => BTZipper t -> t
unzipper = zipSelected . zipRoot

-- | Navigate to the topmost term of the given 'BTZipper'.
zipRoot :: BinaryTree t => BTZipper t -> BTZipper t
zipRoot zipper = maybe zipper zipRoot (zipUp zipper)

-- | Is the position of this 'BTZipper' the root position?
zipIsRoot :: BTZipper t -> Bool
zipIsRoot term | null (zipAnchestors term) = True
               | otherwise = False

-- | Navigate to the parent of the given position.
--
-- Returns 'Nothing' if this is the root, else return 'Just' the 'BTZipper'.
zipUp :: BinaryTree t => BTZipper t -> Maybe (BTZipper t)
zipUp zipper =
  case zipAnchestors zipper of
    (Left t:tail') -> Just
      BTZipper { zipSelected = t @@ zipSelected zipper
                  , zipAnchestors  = tail'}
    (Right t:tail') -> Just
      BTZipper { zipSelected = zipSelected zipper @@ t
                  , zipAnchestors  = tail'}
    [] -> Nothing

-- | Navigate to the parent of the given position if this is a right child.
--
-- Returns 'Nothing' if this is the root or a left child,
-- else return 'Just' the 'BTZipper'.
zipUpLeft :: BinaryTree t => BTZipper t -> Maybe (BTZipper t)
zipUpLeft zipper =
  case zipAnchestors zipper of
    (Left _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Navigate to the parent of the given position if this is a left child.
--
-- Returns 'Nothing' if this is the root or a right child,
-- else return 'Just' the 'BTZipper'.
zipUpRight :: BinaryTree t => BTZipper t -> Maybe (BTZipper t)
zipUpRight zipper =
  case zipAnchestors zipper of
    (Right _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Select the left child.
--
zipDownLeft ::  BinaryTree t => BTZipper t -> Maybe (BTZipper t)
zipDownLeft zipper = case decompose (zipSelected zipper) of
    Just (l,r) ->
      Just BTZipper{zipSelected = l,
                      zipAnchestors = Right r : zipAnchestors zipper}
    _ -> Nothing

-- | Select the right child.
--
zipDownRight ::  BinaryTree t => BTZipper t -> Maybe (BTZipper t)
zipDownRight zipper = case decompose (zipSelected zipper) of
    Just (l,r) ->
      Just BTZipper{zipSelected = r,
                      zipAnchestors = Left l : zipAnchestors zipper}
    _ -> Nothing


-- | Enumerates all positions for a zipper
zipEnum :: BinaryTree t => BTZipper t -> [BTZipper t]
zipEnum zipper =  zipEnum' [] (Just (zipRoot zipper))
  where
    zipEnum' accu (Just zipper') =
        let accu'   = zipper' : accu
            accu''  = zipEnum' accu' (zipDownLeft zipper')
        in zipEnum' accu'' (zipDownRight zipper')
    zipEnum' accu Nothing = accu

-- | Gets the current position in the zipper in a
--zipperGetPath :: BinaryTree t => BTZipper t -> [Int]
--zipperGetPath z = reverse (zipperGetPath' [] (reverse (zipAnchestors z)))
--  where
--    zipperGetPath' accu [] = accu
--    zipperGetPath' accu (Left term: rest)   = zipperGetPath' (leftSpineLength term:accu) rest
--    zipperGetPath' accu (Right _term: [])   = 0:accu
--    zipperGetPath' accu (Right _term: rest) = zipperGetPath' accu rest



