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
    InstrumentedContext,
    instrumentedContext,
-----------------------------------------------------------------------------
-- ** Term, and abstract Reduction with convenience functions
    Term(..),
    Reduction (..),
    reduceCont,
    reduce,
    reduceS,
    reduceIt,
    reduceOnceCont,
    reduceOnce
) where

import Combinators.BinaryTree
import Data.Functor.Identity
import Control.Monad (liftM)
import Control.Monad.Trans.State
import qualified Data.Set as Set (member, insert, empty, Set)

trace :: a -> b -> b
trace _x s = s

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

class (Monad c, BinaryTree t, PP t) => ReductionContext c t where
    runContext :: c (Maybe t) -> Maybe t
    startReduction :: () => (BTZipper t) -> c (BTZipper t)
    stepReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (Maybe (BTZipper t))
    stopReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (BTZipper t)



-----------------------------------------------------------------------------
-- *** Null Context
type NullContext = Identity

instance (PP t, BinaryTree t) => ReductionContext Identity t where
    runContext (Identity a) = a
    startReduction tz = return tz
    stepReduction tz = return (Just tz)
    stopReduction tz = return tz

nullContext :: Identity (Maybe a)
nullContext = Identity Nothing

maxcount :: Int
maxcount = 1000

-----------------------------------------------------------------------------
-- *** Instrumented Context

instance (PP t, BinaryTree t, Ord t) => ReductionContext (InstrumentedContext t) t  where
    runContext tracing =
        let (a, (s,_i,_l)) = runState tracing (id,0,Set.empty)
        in  trace (take 3000 (s "")) a
    startReduction tz = do
        let t = unzipper tz
        modify (\(log,count,l) -> (log . showString "\nstart: " . ppsh t, count,Set.insert t l))
        return tz
    stepReduction tz =  do
        let t = unzipper tz
        (_,count,l) <- get
        if Set.member t l
            then do
                modify (\(log,count,l) ->
                    (log . showString "\nCycle detected: " . ppsh t,
                    count + 1,
                    l))
                return Nothing
            else if count + 1 > maxcount
                then do
                    modify (\(log,count,l) ->
                        (log . showString "\nMax reductions reached: " . shows count,
                        count + 1,
                        l))
                    return Nothing
                else do
                    modify (\(log,count,l) ->
                        (log . showString "\nstep" . shows (count + 1) . showString ": " . ppsh t,
                        count+1,
                        Set.insert t l
                        ))
                    return (Just tz)
    stopReduction tz = do
        return tz

type InstrumentedContext t = State (ShowS,Int,Set.Set t)

instrumentedContext :: InstrumentedContext t (Maybe t)
instrumentedContext = state (\ s -> (Nothing,s))



-----------------------------------------------------------------------------
-- ** Term, and abstract Reduction with convenience functions
-----------------------------------------------------------------------------

class BinaryTree t => Term t where
    isTerminal :: t -> Bool
    -- ^ This information is used for reduction

-- | A term is a binary tree, which can be reduced one or many times.
class (ReductionContext c t, BinaryTree t , PP t, Strategy s) => Reduction t s c where
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
reduce :: forall c t s. (ReductionContext c t, Reduction t s c) => c (Maybe t) -> s -> t -> Maybe t
reduce _c s t =  (runContext :: c (Maybe t) -> Maybe t) (reduceCont s t)

reduceS :: (Reduction t NormalForm (InstrumentedContext t), Term t) =>  t -> Maybe t
reduceS = reduce instrumentedContext NormalForm

--  This is not guaranteed to terminate.
reduceIt :: (ReductionContext c t, Reduction t s c) => c (Maybe t) -> s -> t -> t
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
reduceOnce :: forall t s c . Reduction t s c =>  c (Maybe t) -> s -> t -> Maybe t
reduceOnce _c strategy t = (runContext :: c (Maybe t) -> (Maybe t)) (reduceOnceCont strategy t)
