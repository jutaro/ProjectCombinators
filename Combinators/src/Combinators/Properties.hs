-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Properties
-- Copyright   :
-- License     :  AllRightsReserved
--
--
-----------------------------------------------------------------------------

module Combinators.Properties where

import Combinators.Combinator
import Combinators.Reduction
-- import Combinators.Variable

-----------------------------------------------------------------------------
-- * Properties of combinators
-----------------------------------------------------------------------------


-- | A term t is in weak normal form, iff M contains no redexes.
_isWeakNormal :: Basis basis v => CTerm basis v -> Bool
_isWeakNormal t = case reduceOnce nullContext HeadNormalForm t of
                    Just _ -> False
                    Nothing -> True -- term not changed, so no redex

-- | Is this weak extensional equality?
-- TODO
isWeakEqual :: Basis basis v => CTerm basis v -> CTerm basis v -> Bool
isWeakEqual t1 t2 = primTermEqual (normalOrderReduction t1) (normalOrderReduction t2)

primTermEqual :: Basis basis v => CTerm basis v -> CTerm basis v -> Bool
primTermEqual t1 t2 = snd (primTermEqual' [] t1 t2)
  where
    primTermEqual' env (Const a) (Const b) = (env,a == b)
    primTermEqual' env (Var a) (Var b) =
        case [(v1,v2) | (v1,v2) <- env, v1 == a] of
            [] -> ((a,b) : env, True)
            (_,v2):_ -> (env, b == v2)
    primTermEqual' env (l1 :@ r1) (l2 :@ r2) =
        let (newEnv,res) = primTermEqual' env l1 l2
        in if not res
                then (newEnv,False)
                else primTermEqual' newEnv r1 r2
    primTermEqual' env _ _ = (env,False)


-- | Computes the arity of a term
arity :: Basis basis v => CTerm basis v -> Maybe Int
arity t = arity' 0 (normalOrderReduction t)
  where
    arity' count (Const c) = Just (primArity c - count)
    arity' _count (Var _)  = Nothing
    arity' count (l :@ _)  = arity' (1 + count) l



spineList :: Basis basis v => CTerm basis v -> [CTerm basis v]
spineList = reverse . spineList'
  where
    spineList' co@(Const _)  = [co]
    spineList' va@(Var _)    = [va]
    spineList' (l :@ r)      = r : spineList l

{-
-- | Is this combinator an identity combinator (like I) of any arity
isIdentity :: Basis basis v => CTerm basis v -> Bool
isIdentity term =
    case arity term of
        Nothing -> False
        Just i ->
            let vars     = map Var (varGen i)
                inTerm   = foldl (:@) term vars
                outTerm  = normalOrderReduction inTerm
                computed = spineList outTerm
            in vars == computed
-}
{-
-- | Is this combinator an associator combinator (like B) of any arity > 3
isAssociator :: Basis basis v => Term basis v -> Bool
isAssociator term =
    case arity term of
        Nothing -> trace "no arity" False
        Just i | i < 3 -> trace ("i: " ++ show i) False
               | otherwise ->
            let vars     = trace ("i: " ++ show i) $ map Var (varGen i)
                inTerm   = trace ("vars" ++ show vars) $ foldl (:@) term vars
                outTerm  = trace ("inTerm" ++ show inTerm) $ normalOrderReduction inTerm
            in trace ("outTerm" ++ show outTerm) $ not (leftAssociated outTerm)
-}

