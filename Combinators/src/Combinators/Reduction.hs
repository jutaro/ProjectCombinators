{-# LANGUAGE EmptyDataDecls, ScopedTypeVariables, MultiParamTypeClasses, TypeSynonymInstances,
    FlexibleInstances, FlexibleContexts, Rank2Types #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Reduction
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-----------------------------------------------------------------------------

module Combinators.Reduction (
-----------------------------------------------------------------------------
-- * Abstract Reduction, Reduction strategies and reduction contexts
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- ** Reduction Strategies
    NormalForm(..),
    HeadNormalForm(..),
    Strategy,
-----------------------------------------------------------------------------
-- ** Reduction Context
    ReductionContext(..),
    NullContext,
    nullContext,
    TracingContext,
    tracingContext,
-----------------------------------------------------------------------------
-- ** Term, and abstract Reduction with convenience functions
    Term(..),
    Reduction (..),
    reduceCont,
    reduce,
    reduceIt,
    reduceOnceCont,
    reduceOnce
) where

import Combinators.BinaryTree
import Data.Functor.Identity
import Control.Monad (liftM)
import Control.Monad.Trans.State
import Debug.Trace (trace)

-----------------------------------------------------------------------------
-- ** Abstract Reduction, Reduction strategies and reduction contexts
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** Reduction Strategies
-----------------------------------------------------------------------------

-- | Instances of this class represent an evaluation strategy
class Strategy s where
    reduce' :: (Reduction t s c) => s -> BTZipper t -> c (Maybe (BTZipper t))
    -- ^ The transitive closure of reduceOnce. Returns Just t if reduction was possible,
    -- or Nothing in case an infinie reduction was detected, which depends on the implementation
    -- ^ Constructs a tree from its left and right subparts


-- | Normal form means reduction of all redexes
data NormalForm = NormalForm

instance Strategy NormalForm where
    reduce' strategy zipper = do
        startReduction zipper
        reduce'' zipper
      where
        reduce'' zipper =  do
            r <- reduceOnce' strategy zipper
            case r of
                Just zipper' ->  do
                    r' <- stepReduction zipper'
                    case r' of
                        Nothing -> do
                            stopReduction zipper'
                            return Nothing
                        Just z' ->
                            reduce'' z'
                Nothing -> liftM Just (stopReduction zipper)


-- | Head normal form means reduction of all head redexes
data HeadNormalForm = HeadNormalForm

instance Strategy HeadNormalForm where
    reduce' strategy zipper = do
        startReduction zipper
        reduce'' zipper
      where
        reduce'' zipper =  do
            r <- reduceOnce' strategy zipper
            case r of
                Just zipper' -> do
                        r' <- stepReduction zipper'
                        case r' of
                            Nothing -> do
                                stopReduction zipper'
                                return Nothing
                            Just z' ->
                                reduce'' z'
                Nothing -> case goUp zipper of
                                Nothing -> liftM Just (stopReduction zipper)
                                Just z ->  reduce'' z


-----------------------------------------------------------------------------
-- ** Reduction Context

class Monad c => ReductionContext c where
    runContext :: c a -> a
    startReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (BTZipper t)
    stepReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (Maybe (BTZipper t))
    stopReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (BTZipper t)

instance ReductionContext Identity where
    runContext (Identity a) = a
    startReduction tz = return tz
    stepReduction tz = return (Just tz)
    stopReduction tz = return tz

type NullContext = Identity

nullContext :: Identity (Maybe a)
nullContext = Identity Nothing

instance ReductionContext TracingContext where
    runContext tracing =
        let (a, (s,_i)) = runState tracing ("",0)
        in  trace s a
    startReduction tz = do
        modify (\(log,count) -> (log ++ "\nstart: " ++ pp (unzipper tz), count))
        return tz
    stepReduction tz =  do
        modify (\(log,count) -> (log ++ "\nstep" ++ show (count + 1) ++ ": "
                                ++ pp (unzipper tz), count+1))
        return (Just tz)
    stopReduction tz = do
        return tz

type TracingContext = State (String,Int)

tracingContext :: TracingContext (Maybe a)
tracingContext = state (\ s -> (Nothing,s))

-----------------------------------------------------------------------------
-- ** Term, and abstract Reduction with convenience functions
-----------------------------------------------------------------------------

class BinaryTree t => Term t where
    isTerminal :: t -> Bool
    -- ^ This information is used for reduction

-- | A term is a binary tree, which can be reduced one or many times.
class (ReductionContext c, BinaryTree t , PP t, Strategy s) => Reduction t s c where
    reduceOnce' :: s -> BTZipper t -> c (Maybe (BTZipper t))
    -- ^ One step reduction. Returns Left t if possible, or Right t with the original term,
    --   if no reduction was possible


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
reduceOnceCont ::  Reduction t s c => s -> t -> c (Maybe t)
reduceOnceCont s t = do
    r <- reduceOnce' s (zipper t)
    case r of
        Just t' -> return (Just (unzipper t'))
        Nothing -> return Nothing

--  This is not guaranteed to terminate.
reduceOnce :: forall c s t a. Reduction t s c =>  c a -> s -> t -> Maybe t
reduceOnce _c strategy t = (runContext :: c (Maybe t) -> (Maybe t)) (reduceOnceCont strategy t)
