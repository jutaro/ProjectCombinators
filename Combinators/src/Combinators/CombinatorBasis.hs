{-# LANGUAGE EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Basis
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-----------------------------------------------------------------------------

module Combinators.CombinatorBasis where

import Combinators.Combinator
import Combinators.CombLambda
import Combinators.Lambda
import Combinators.Types (SType(..))

-----------------------------------------------------------------------------
-- * Alternative bases for Combinatory logic
-----------------------------------------------------------------------------

-- ** IBCWK

-- | Definition of the combinators for the IBCWK Basis
data IBCWK

iIBCWK, bIBCWK, cIBCWK, kIBCWK, wIBCWK :: Combinator IBCWK

iIBCWK = Combinator "I" ["_u"] (Var ("_u"))
                (SAtom "a" :->: SAtom "a")
bIBCWK = Combinator "B" ["_u","_v","_w"]
            (Var ("_u") :@ (Var ("_v") :@ Var ("_w")))
                (SAtom "a" :->: SAtom "a")
cIBCWK = Combinator "C" ["_u","_v","_w"]
            ((Var ("_u") :@ Var ("_w")) :@ Var ("_v"))
                (SAtom "a" :->: SAtom "a")
kIBCWK = Combinator "K" ["_u", "_v"]
            (Var ("_u"))
            (SAtom "a" :->: SAtom "b" :->: SAtom "a")
wIBCWK = Combinator "W" ["_u", "_v"]
            (Var ("_u") :@ Var ("_v") :@ Var ("_v"))
            (SAtom "a" :->: SAtom "b" :->: SAtom "a")

instance Basis IBCWK where
    primCombs = [iIBCWK, bIBCWK, cIBCWK, kIBCWK, wIBCWK]

{-
instance Variable v => BracketAbstract IBCWK v where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1) :@: r) | LVar v1 == r = Const iIKS
    bracketAbstract ((LAbst v1) :@: r) | not (occurs v1 r) = Const kIKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1) :@: (l :@: r))   = Const sIKS :@  bracketAbstract ((LAbst v1) :@: l)
                                                    :@ bracketAbstract ((LAbst v1) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v
-}

-- ** IKS

data IKS

iIKS, kIKS, sIKS :: Combinator IKS
iIKS = Combinator "I" ["_u"] (Var ("_u"))
            (SAtom "a" :->: SAtom "a")
kIKS = Combinator "K" ["_u", "_v"] (Var ("_u"))
            (SAtom "a" :->: SAtom "b" :->: SAtom "a")
sIKS = Combinator "S" ["_u", "_v", "_w"]
            (Var ("_u") :@ Var ("_w") :@
            (Var ("_v") :@ Var ("_w")))
            ((SAtom "a" :->: SAtom "b" :->: SAtom "c") :->: (SAtom "a" :->: SAtom "b") :->: SAtom "a" :->: SAtom "c")

instance Basis IKS where
    primCombs = [iIKS,kIKS,sIKS]

instance BracketAbstract IKS where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1 _) :@: r) | LVar v1 == r = Const iIKS
    bracketAbstract ((LAbst v1 _) :@: r) | not (occurs v1 r) = Const kIKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1 ty) :@: (l :@: r))   = Const sIKS :@  bracketAbstract ((LAbst v1 ty) :@: l)
                                                    :@ bracketAbstract ((LAbst v1 ty) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

