{-# LANGUAGE EmptyDataDecls, ScopedTypeVariables, MultiParamTypeClasses, Rank2Types #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Reduction
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- | Abstract reduction and reductionStrategy properties
--
-----------------------------------------------------------------------------

module Combinators.Reduction (
    NormalOrder(..),
    Strategy,
    Reduction (..),
    ReductionContext(..),
    NullContext,
    nullContext,
    Term(..),
    reduceCont,
    reduce,
    reduceIt,
    reduceOnceCont,
    reduceOnce
) where

import Combinators.BinaryTree
import Data.Functor.Identity

-----------------------------------------------------------------------------
-- * Abstract strategies
-----------------------------------------------------------------------------

-- | Instances of this class represent an evaluation strategy
class Strategy s

-- | Normal order is weak head reduction
data NormalOrder = NormalOrder
instance Strategy NormalOrder

-----------------------------------------------------------------------------
-- * Reduction context
-----------------------------------------------------------------------------

class Monad c => ReductionContext c where
    runContext :: c a -> a

instance ReductionContext Identity where
    runContext (Identity a) = a

type NullContext = Identity

nullContext :: Identity (Maybe a)
nullContext = Identity Nothing

-----------------------------------------------------------------------------
-- * Term, Strategy and abstract reduction
-----------------------------------------------------------------------------

class BinaryTree t => Term t where
    isTerminal :: t -> Bool
    -- ^ This information is used for reduction

-- | A term is a binary tree, which can be reduced one or many times.
class (BinaryTree t , PP t, Strategy s, ReductionContext c) => Reduction t s c where
    reduce' :: s -> BTZipper t -> c (Maybe (BTZipper t))
    -- ^ The transitive closure of reduceOnce. Returns Just t if reduction was possible,
    -- or Nothing in case an infinie reduction was detected, which depends on the implementation
    -- ^ Constructs a tree from its left and right subparts
    reduceOnce' :: s -> BTZipper t -> c (Either (BTZipper t) (BTZipper t))

--  This is not guaranteed to terminate.
reduceCont :: Reduction t s c => s -> t -> c (Maybe t)
reduceCont s t = do
    r <- (reduce' s)  (zipper t)
    case r of
        Just t' -> return $ Just (unzipper t')
        Nothing -> return $ Nothing

--  This is not guaranteed to terminate.
reduce :: forall t s c a. Reduction t s c => c a -> s -> t -> Maybe t
reduce _c s t =  (runContext :: c (Maybe t) -> Maybe t)  (reduceCont s t)


--  This is not guaranteed to terminate.
reduceIt :: Reduction t s c => c a -> s -> t -> t
reduceIt c s t = case reduce c s t of
                        Just t' -> t'
                        Nothing -> error "Term>>reduceIt: Nontermination detected?"

--
reduceOnceCont ::  Reduction t s c => s -> t -> c (Either t t)
reduceOnceCont s t = do
    r <- reduceOnce' s (zipper t)
    case r of
        Left t' -> return (Left (unzipper t'))
        Right t' -> return (Right (unzipper t'))

--  This is not guaranteed to terminate.
reduceOnce :: forall c s t a. Reduction t s c =>  c a -> s -> t -> (Either t t)
reduceOnce _c strategy t = (runContext :: c (Either t t) -> (Either t t)) (reduceOnceCont strategy t)