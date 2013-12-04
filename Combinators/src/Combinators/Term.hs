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
-- | Abstract Reduction System
--
-----------------------------------------------------------------------------

module Combinators.Term where

import Control.Monad (MonadPlus(..))
import Data.Maybe (isNothing)
import Debug.Trace (trace)

-- | A binary tree may have a right or left subpart
class BinaryTree t where
    decompose :: t -> Maybe (t,t)
    -- ^ Returns the left and right subparts of a tree, if it is not a leaf
    (@@) :: t -> t -> t
    -- ^ Constructs a tree from its left and right subparts
    isLeaf :: t -> Bool
    isLeaf = isNothing . decompose

class PP t where
    pp :: t -> String

-- | A term is a binary tree, which can be reduced one or many times.
class (BinaryTree t , PP t) => Term t where
    reduceOnce' :: (Strategy t) -> TermZipper t -> Either (TermZipper t) (TermZipper t)
    -- ^ One step reduction. Returns Left t if possible, or Right t with the original term,
    --   if no reduction was possible
    reduce' :: (Strategy t) -> TermZipper t -> Maybe (TermZipper t)
    reduce' strategy zipper = case reduceOnce' strategy zipper of
        Left zipper' -> trace (pp (unzipper zipper')) $ reduce' strategy zipper'
        Right zipper' -> Just zipper'


    -- ^ The transitive closure of reduceOnce. Returns Just t if reduction was possible,
    -- or Nothing in case an infinie reduction was detected, which depends on the implementation
    -- ^ Constructs a tree from its left and right subparts
    isTerminal :: t -> Bool
    -- ^ This information is used for reduction

--  This is not guaranteed to terminate.
reduce :: Term t => Strategy t -> t -> Maybe t
reduce strategy t = case (reduce' strategy) (zipper t) of
                        Just t' -> Just (unzipper t')
                        Nothing -> Nothing

--  This is not guaranteed to terminate.
reduceIt :: Term t => Strategy t -> t -> t
reduceIt strategy t = case (reduce strategy) t of
                        Just t' -> t'
                        Nothing -> error "Term>>reduceIt: Nontermination detected?"

--
reduceOnce :: Term t => Strategy t -> t -> Either t t
reduceOnce strategy t = case (reduceOnce' strategy) (zipper t) of
                            Left t' -> Left (unzipper t')
                            Right t' -> Right (unzipper t')

-- | A strategy fixes the order of reduction.
-- It takes a term in zipper form (see below), and returns the zipper in a form with just the
-- next head to be reduced selected, or Nothing if no further reduction selection is possible

type {- Term t => -} Strategy t = TermZipper t -> Maybe (TermZipper t)

normalOrder :: Term t => Strategy t
normalOrder = \ zipper ->
    let res = mplus (down zipper) (up zipper)
    in --trace ("normalOrderStrategy from: " ++ show (zipSelected zipper) ++
       --         " to: " ++ case res of Nothing -> show res; Just z -> show (zipSelected z) ) $
       res
  where
    down zipper' = case zipDownLeft' zipper' of
                    Nothing -> zipDownRight' zipper'
                    Just z -> Just z
    up zipper' = case zipUpLeft zipper' of
                    Nothing -> case zipUpRight zipper' of
                                Nothing -> Nothing
                                Just z' -> zipDownRight' z'
                    Just z -> up z

-- | Select the left child if it is not a terminal.
--
zipDownLeft' ::  Term t => TermZipper t -> Maybe (TermZipper t)
zipDownLeft' zipper = case decompose (zipSelected zipper) of
    Just (l,r) | not (isTerminal l) ->
      Just TermZipper{zipSelected = l,
                      zipAnchestors = Right r : zipAnchestors zipper}
    _ -> Nothing

-- | Select the right child if it is not a terminal.
--
zipDownRight' ::  Term t => TermZipper t -> Maybe (TermZipper t)
zipDownRight' zipper = case decompose (zipSelected zipper) of
    Just (l,r) | not (isLeaf r) ->
      Just TermZipper{zipSelected = r,
                      zipAnchestors = Left l : zipAnchestors zipper}
    _ -> Nothing


-----------------------------------------------------------------------------
-- * Term Zipper

-- | This is a zipper for a term, which is a structure which carries a term and a
-- position in the term, without the possibility of an invalid position.
data TermZipper t where
    TermZipper :: BinaryTree t =>
        {zipSelected :: t,
        zipAnchestors :: [Either t t]} ->  TermZipper t

deriving instance Eq t => Eq (TermZipper t)
deriving instance Show t => Show (TermZipper t)

-- | Construct a 'TermZipper' from a 'Term' with the root as selected element.
zipper :: Term t => t -> TermZipper t
zipper term = TermZipper
  { zipSelected     = term
  , zipAnchestors   =   []
  }

-- | Returns the (root) 'Term' in the zipper
unzipper :: Term t => TermZipper t -> t
unzipper = zipSelected . zipRoot

-- | Navigate to the topmost term of the given 'TermZipper'.
zipRoot :: Term t => TermZipper t -> TermZipper t
zipRoot zipper = maybe zipper zipRoot (zipUp zipper)

-- | Is the position of this 'TermZipper' the root position?
zipIsRoot :: Term t => TermZipper t -> Bool
zipIsRoot term | null (zipAnchestors term) = True
               | otherwise = False

-- | Navigate to the parent of the given position.
--
-- Returns 'Nothing' if this is the root, else return 'Just' the 'TermZipper'.
zipUp :: Term t => TermZipper t -> Maybe (TermZipper t)
zipUp zipper =
  case zipAnchestors zipper of
    (Left t:tail') -> Just
      TermZipper { zipSelected = t @@ zipSelected zipper
                  , zipAnchestors  = tail'}
    (Right t:tail') -> Just
      TermZipper { zipSelected = zipSelected zipper @@ t
                  , zipAnchestors  = tail'}
    [] -> Nothing

-- | Navigate to the parent of the given position if this is a right child.
--
-- Returns 'Nothing' if this is the root or a left child,
-- else return 'Just' the 'TermZipper'.
zipUpLeft :: Term t => TermZipper t -> Maybe (TermZipper t)
zipUpLeft zipper =
  case zipAnchestors zipper of
    (Left _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Navigate to the parent of the given position if this is a left child.
--
-- Returns 'Nothing' if this is the root or a right child,
-- else return 'Just' the 'TermZipper'.
zipUpRight :: Term t => TermZipper t -> Maybe (TermZipper t)
zipUpRight zipper =
  case zipAnchestors zipper of
    (Right _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Select the left child.
--
zipDownLeft ::  Term t => TermZipper t -> Maybe (TermZipper t)
zipDownLeft zipper = case decompose (zipSelected zipper) of
    Just (l,r) ->
      Just TermZipper{zipSelected = l,
                      zipAnchestors = Right r : zipAnchestors zipper}
    _ -> Nothing

-- | Select the right child.
--
zipDownRight ::  Term t => TermZipper t -> Maybe (TermZipper t)
zipDownRight zipper = case decompose (zipSelected zipper) of
    Just (l,r) ->
      Just TermZipper{zipSelected = r,
                      zipAnchestors = Left l : zipAnchestors zipper}
    _ -> Nothing


-- | Enumerates all positions for a zipper
zipEnum :: Term t => TermZipper t -> [TermZipper t]
zipEnum zipper =  zipEnum' [] (Just (zipRoot zipper))
  where
    zipEnum' accu (Just zipper') =
        let accu'   = zipper' : accu
            accu''  = zipEnum' accu' (zipDownLeft zipper')
        in zipEnum' accu'' (zipDownRight zipper')
    zipEnum' accu Nothing = accu

spine :: Term t => t -> [t]
spine = reverse . spine'
  where
    spine' t = case decompose t of
                Just (l,r) -> (r : spine' l)
                Nothing -> [t]

spineLength :: Term t => t -> Int
spineLength t = case decompose t of
                 Just (l,_r) ->  1 + spineLength l
                 _ -> 1

zipperGetPath :: Term t => TermZipper t -> [Int]
zipperGetPath z = reverse (zipperGetPath' [] (reverse (zipAnchestors z)))
  where
    zipperGetPath' accu [] = accu
    zipperGetPath' accu (Left term: rest)   = zipperGetPath' (spineLength term:accu) rest
    zipperGetPath' accu (Right _term: [])   = 0:accu
    zipperGetPath' accu (Right _term: rest) = zipperGetPath' accu rest

