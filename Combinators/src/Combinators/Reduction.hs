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
    TermString(..),
    Reduction (..),
    reduce,
    reduceS,
    reduceSForce,
    reduceOnce,
    reduceOnceS
) where

import Combinators.BinaryTree
import Data.Functor.Identity
import Control.Monad (liftM)
import Control.Monad.Trans.State
import qualified Data.Set as Set (member, insert, empty, Set)
import Combinators.Variable (VarString)
import Combinators.PrintingParsing (PP(..), PP)


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
    runContext :: Int -> c (Maybe t) -> (Maybe t,ShowS,Int,[t])
    startReduction :: () => (BTZipper t) -> c (BTZipper t)
    stepReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (Maybe (BTZipper t))
    stopReduction :: (BinaryTree t, PP t) => (BTZipper t) -> c (BTZipper t)



-----------------------------------------------------------------------------
-- *** Null Context
type NullContext = Identity

instance (PP t, BinaryTree t) => ReductionContext Identity t where
    runContext _ (Identity a) = (a,id,0,[])
    startReduction tz = return tz
    stepReduction tz = return (Just tz)
    stopReduction tz = return tz

nullContext :: Identity (Maybe a)
nullContext = Identity Nothing

-----------------------------------------------------------------------------
-- *** Instrumented Context

instance (PP t, BinaryTree t, Ord t) => ReductionContext (InstrumentedContext t) t  where
    runContext maxc tracing =
        let (a, (s,_maxc,i,_set,li)) = runState tracing (id,maxc,0,Set.empty,[])
        in  (a,s,i,li)
    startReduction tz = do
        let t = unzipper tz
        modify (\(log,max,count,set,li) ->
                    (log, max, count,Set.insert t set,t:li))
        return tz
    stepReduction tz =  do
        let t = unzipper tz
        (_,maxc,count,set,_li) <- get
        if Set.member t set
            then do
                modify (\(log,maxc,count,set,li) ->
                    (log . showString "\nCycle detected: " . ppsh t,
                    maxc,
                    count + 1,
                    set,
                    li))
                return Nothing
            else if count + 1 > maxc
                then do
                    modify (\(log,maxc,count,set,li) ->
                        (log . showString "\nMax reductions reached: " . shows count,
                        maxc,
                        count + 1,
                        set,
                        li))
                    return Nothing
                else do
                    modify (\(log,maxc,count,set,li) -> (
                        log, -- . showString "\nstep" . shows (count + 1) . showString ": " . ppsh t,
                        maxc,
                        count+1,
                        Set.insert t set,
                        t:li
                        ))
                    return (Just tz)
    stopReduction tz = do
        return tz

type InstrumentedContext t = State (ShowS,Int,Int,Set.Set t,[t])

instrumentedContext :: InstrumentedContext t (Maybe t)
instrumentedContext = state (\ s -> (Nothing,s))

maxcount :: Int
maxcount = 150

-----------------------------------------------------------------------------
-- ** Term, and abstract Reduction with convenience functions
-----------------------------------------------------------------------------

class (BinaryTree t, Ord t, Eq t) => Term t where
    isTerminal :: t -> Bool
    -- ^ This information is used for reduction
    canonicalize :: t -> t

class BinaryTree t => TermString t where
    occurs :: VarString -> t -> Bool
    -- ^ Does variable v occurst in the term?
    freeVars :: t -> [VarString]
    -- | Returns a list of free Vars in the term

-- | A term is a binary tree, which can be reduced one or many times.
class (ReductionContext c t, BinaryTree t , PP t, Strategy s) => Reduction t s c where
    reduceOnce' :: s -> BTZipper t -> c (Maybe (BTZipper t))
    -- ^ One step reduction. Returns Left t if possible, or Right t with the original term,
    --   if no reduction was possible



--  This is not guaranteed to terminate.
reduce :: forall c t s. (ReductionContext c t, Reduction t s c) => c (Maybe t) -> s -> Int -> t ->
                            (Maybe t,ShowS,Int,[t])
reduce _c s n t =  (runContext :: Int -> c (Maybe t) ->  (Maybe t,ShowS,Int,[t])) n (reduceCont s t)
  where
    reduceCont s t = do
        r <- (reduce' s)  (zipper t)
        case r of
            Just t' -> return $ Just (unzipper t')
            Nothing -> return $ Nothing

reduceS :: (Reduction t NormalForm (InstrumentedContext t), Term t) =>  t -> Maybe t
reduceS = (\(a,_,_,_) -> a) . reduce instrumentedContext NormalForm maxcount

reduceSForce :: (Reduction t NormalForm (InstrumentedContext t), Term t) => t -> t
reduceSForce t = case reduce instrumentedContext NormalForm maxcount t of
                        (Just t',_,_,_) -> t'
                        (Nothing,s,_,_) -> error ("Term>>reduceIt: " ++  (s ""))

--

--  This is not guaranteed to terminate.
reduceOnce :: forall t s c . Reduction t s c =>  c (Maybe t) -> s -> t -> (Maybe t,ShowS,Int,[t])
reduceOnce _c strategy t = (runContext :: Int -> c (Maybe t) ->  (Maybe t,ShowS,Int,[t])) maxcount
                                (reduceOnceCont strategy t)
  where
    reduceOnceCont s t = do
        r <- reduceOnce' s (zipper t)
        case r of
            Just t' -> return (Just (unzipper t'))
            Nothing -> return Nothing

reduceOnceS :: (Reduction t NormalForm (InstrumentedContext t), Term t) =>  t -> Maybe t
reduceOnceS = (\(a,_,_,_) -> a) . reduceOnce instrumentedContext NormalForm
