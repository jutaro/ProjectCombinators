-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Properties
-- Copyright   :
-- License     :  AllRightsReserved
--
--
-----------------------------------------------------------------------------

module Combinators.Properties (
    isWeakNormal,
    arity,
    isWeakEqual,
    isIdentity,
    isCancelator,
    isDuplicator,
    isAssociator,
    isPermutator,
    isRegular,
    isProper,
    notProper
) where

import Combinators.Combinator
import Combinators.Reduction
import Combinators.Variable (nameGen)
import Debug.Trace (trace)
import Combinators.BinaryTree (BinaryTree(..), leftSpine)
import Data.List ((\\), nub, sort)
import Control.Monad (liftM2, liftM)
-- import Combinators.Variable

-----------------------------------------------------------------------------
-- * Properties of combinators
-----------------------------------------------------------------------------

-- | A term t is in weak normal form, iff M contains no redexes.
isWeakNormal :: Basis basis => CTerm basis -> Bool
isWeakNormal t = case reduceOnce nullContext NormalForm t of
                    Just _ -> False
                    Nothing -> True -- term not changed, so no redex


-- | Computes the arity of a term
arity :: Basis basis => CTerm basis -> Maybe Int
arity t = do
    nt <- reduceS t
    arity' 0 nt
  where
    arity' count (Const c) = Just (primArity c - count)
    arity' _count (Var _)  = Nothing
    arity' count (l :@ _)  = arity' (1 + count) l


-- | Is this weak extensional equality?
isWeakEqual :: Basis basis => CTerm basis -> CTerm basis -> Maybe Bool
isWeakEqual t1 t2 = do
    t1r <- reduceS t1
    t2r <- reduceS t2
    return (canonicalize t1r == canonicalize t2r)


-- | Is this combinator an identity combinator (like I) of any arity
isIdentity :: Basis basis => Int -> CTerm basis -> Maybe Bool
isIdentity arity term = do
    let vars     = map Var (take arity nameGen)
        inTerm   = foldl (:@) term vars
    outTerm <-  reduceS inTerm
    let computed = leftSpine outTerm
    return (vars == computed)

-- | Is this combinator a cancellator?
isCancelator :: Basis basis => Int -> CTerm basis -> Maybe Bool
isCancelator i term = do
    let vars     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let varList  = filter (\t -> case t of
                            Var _ -> True
                            _     -> False)
                                (allSubterms outTerm)
    return (or (map (\v -> not (elem v varList)) vars))

-- | Is this combinator a duplicator?
isDuplicator :: Basis basis => Int -> CTerm basis -> Maybe Bool
isDuplicator i term = do
    let vars     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let varList  = filter (\t -> case t of
                            Var _ -> True
                            _     -> False)
                                (allSubterms outTerm)
    return (or (map (\v -> length (filter (== v) varList) > 1) vars))

-- | Is this combinator an associator?
isAssociator :: Basis basis => Int -> CTerm basis -> Maybe Bool
isAssociator i term = do
    let vars     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let computed = leftSpine outTerm
    return (not $ null $ (filter (not . isLeaf) computed))

-- | Is this combinator a permutator?
isPermutator :: Basis basis => Int -> CTerm basis -> Maybe Bool
isPermutator i term = do
    let vars     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let varList  = filter (\t -> case t of
                            Var _ -> True
                            _     -> False)
                                (allSubterms outTerm)
    return (varList /= sort varList)

-- | Is this combinator a permutator?
isRegular :: Basis basis => Int -> CTerm basis -> Maybe Bool
isRegular 0 term = Nothing
isRegular i term = do
    let vars@(hv:_)     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let computed = leftSpine outTerm
    case computed of
        (hv2:_) | hv2 == hv -> return True
        _                  -> return False

-- | Is this combinator a permutator?
isProper :: Basis basis => Int -> CTerm basis -> Maybe Bool
isProper i term = do
    let vars     = map Var (take i nameGen)
        inTerm   = foldl (:@) term vars
    outTerm  <- reduceS inTerm
    let varConstList  = filter (\t -> case t of
                            Var _ -> True
                            Const _ -> True
                            _     -> False)
                                (allSubterms outTerm)
    return (null (nub varConstList \\ nub vars))

notProper :: Basis basis => Int -> CTerm basis -> Maybe Bool
notProper i term = case isProper i term of
                    Nothing -> Nothing
                    Just b -> Just (not b)

