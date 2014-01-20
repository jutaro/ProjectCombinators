-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Basis
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-----------------------------------------------------------------------------

{-# LANGUAGE EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses #-}

module Combinators.CombinatorBasis where

import Combinators.Combinator
import Combinators.CombLambda
import Combinators.Lambda
import Combinators.Types (SType(..))

-----------------------------------------------------------------------------
-- * Alternative bases for Combinatory logic
-----------------------------------------------------------------------------
-- ** IKS

data IKS = IKS

i :: Basis b => Combinator b
i = Combinator "I" ["u#"] (Var ("u#"))
            (SAtom "a" :->: SAtom "a")

instance Basis IKS where
    primCombs = [i,k,s]

instance BracketAbstract IKS where
    -- nested abstractions are passed to the helper function
    bracketAbstract ((LAbst v _ty) :@: ((LAbst v2 ty2) :@: r)) =
        bracketAbstract' v  (bracketAbstract ((LAbst v2 ty2) :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract ((LAbst v _) :@: LVar r) | v == r = Const i
    -- eta shortcut
    bracketAbstract (((LAbst v _ty) :@: l) :@: _r) | not (occurs v l) = bracketAbstract l
    -- constant case
    bracketAbstract ((LAbst v _) :@: r) | not (occurs v r) = Const k :@ bracketAbstract r
    -- application case
    bracketAbstract ((LAbst v ty) :@: (l :@: r))   = Const s :@  bracketAbstract ((LAbst v ty) :@: l)
                                                    :@ bracketAbstract ((LAbst v ty) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

    -- identity case
    bracketAbstract' v (Var n) | v == n     = Const i
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r)            = Const s :@ bracketAbstract' v l :@ bracketAbstract' v r



-----------------------------------------------------------------------------
-- ** IKBCW

-- | Definition of the combinators for the IKSBCW Basis
data IKBCW = IKBCW
b,c,w :: Basis b => Combinator b

b = Combinator "B" ["u#","v#","w#"]
            (Var ("u#") :@ (Var ("v#") :@ Var ("w#")))
                ((SAtom "a" :->: SAtom "b") :->: (SAtom "c" :->: SAtom "a") :->: SAtom "c" :->: SAtom "b")

c = Combinator "C" ["u#","v#","w#"]
            ((Var ("u#") :@ Var ("w#")) :@ Var ("v#"))
                ((SAtom "a" :->: SAtom "b" :->: SAtom "c") :->: SAtom "b" :->: SAtom "a" :->: SAtom "c")

w = Combinator "W" ["u#", "v#"]
            (Var ("u#") :@ Var ("v#") :@ Var ("v#"))
                ((SAtom "a" :->: SAtom "a" :->: SAtom "b") :->: SAtom "a" :->: SAtom "b")

instance Basis IKBCW where
    primCombs = [i,k,b,c,w]

instance BracketAbstract IKBCW where
    -- nested abstractions are passed to the helper function
    bracketAbstract ((LAbst v _ty) :@: ((LAbst v2 ty2) :@: r)) =
        bracketAbstract' v  (bracketAbstract ((LAbst v2 ty2) :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract ((LAbst v _) :@: LVar r) | v == r = Const i
    -- eta shortcut
    bracketAbstract (((LAbst v _ty) :@: l) :@: _r) | not (occurs v l) = bracketAbstract l
    -- constant case
    bracketAbstract ((LAbst v _) :@: r) | not (occurs v r) = Const k :@ bracketAbstract r
    -- application case
    bracketAbstract ((LAbst v ty) :@: (l :@: r))
    -- v notElem l
                                        | not (occurs v l) = Const b :@  bracketAbstract l :@
                                                                bracketAbstract ((LAbst v ty) :@: r)
    -- v notElem r
                                        | not (occurs v r) = Const c
                                                                :@  bracketAbstract ((LAbst v ty) :@: l)
                                                                :@  bracketAbstract r
    -- v elem r && v elem l
                                        | otherwise = Const w :@ ((Const b :@ (Const c
                                                         :@ bracketAbstract ((LAbst v ty) :@: l)))
                                                    :@ bracketAbstract ((LAbst v ty) :@: r))
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

    -- identity case
    bracketAbstract' v (Var n) | v == n     = Const i
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r) | not (occurs v l) = Const b :@ l :@ bracketAbstract' v r
                                | not (occurs v r) = Const c :@ bracketAbstract' v l :@ r
                                | otherwise       = Const w :@ ((Const b :@ (Const c
                                                                :@ bracketAbstract' v l))
                                                                :@ bracketAbstract' v r)

-----------------------------------------------------------------------------
-- ** KBCW

-- | Definition of the combinators for the IKSBCW Basis
data KBCW = KBCW

instance Basis KBCW where
    primCombs = [k,b,c,w]

instance BracketAbstract KBCW where
    -- nested abstractions are passed to the helper function
    bracketAbstract ((LAbst v _ty) :@: ((LAbst v2 ty2) :@: r)) =
        bracketAbstract' v  (bracketAbstract ((LAbst v2 ty2) :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract ((LAbst v _) :@: LVar r) | v == r = Const k :@ Const w
    -- eta shortcut
    bracketAbstract (((LAbst v _ty) :@: l) :@: _r) | not (occurs v l) = bracketAbstract l
    -- constant case
    bracketAbstract ((LAbst v _) :@: r) | not (occurs v r) = Const k :@ bracketAbstract r
    -- application case
    bracketAbstract ((LAbst v ty) :@: (l :@: r))
    -- v notElem l
                                        | not (occurs v l) = Const b :@  bracketAbstract l :@
                                                                bracketAbstract ((LAbst v ty) :@: r)
    -- v notElem r
                                        | not (occurs v r) = Const c
                                                                :@  bracketAbstract ((LAbst v ty) :@: l)
                                                                :@  bracketAbstract r
    -- v elem r && v elem l
                                        | otherwise = Const w :@ ((Const b :@ (Const c
                                                         :@ bracketAbstract ((LAbst v ty) :@: l)))
                                                    :@ bracketAbstract ((LAbst v ty) :@: r))
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

    -- identity case
    bracketAbstract' v (Var n) | v == n     = Const k :@ Const w
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r) | not (occurs v l) = Const b :@ l :@ bracketAbstract' v r
                                | not (occurs v r) = Const c :@ bracketAbstract' v l :@ r
                                | otherwise       = Const w :@ ((Const b :@ (Const c
                                                                :@ bracketAbstract' v l))
                                                                :@ bracketAbstract' v r)



