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

-----------------------------------------------------------------------------
-- * Alternative bases for Combinatory logic
-----------------------------------------------------------------------------

-- ** IBCWK

-- | Definition of the combinators for the IBCWK Basis
data IBCWK

iIBCWK, bIBCWK, cIBCWK, kIBCWK, wIBCWK :: Combinator IBCWK

iIBCWK = Combinator "I" ["_u"] (Var ("_u"))
bIBCWK = Combinator "B" ["_u","_v","_w"]
            (Var ("_u") :@ (Var ("_v") :@ Var ("_w")))
cIBCWK = Combinator "C" ["_u","_v","_w"]
            ((Var ("_u") :@ Var ("_w")) :@ Var ("_v"))
kIBCWK = Combinator "K" ["_u", "_v"]
            (Var ("_u"))
wIBCWK = Combinator "W" ["_u", "_v"]
            (Var ("_u") :@ Var ("_v") :@ Var ("_v"))

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

parseIBCWK :: String -> CTerm IBCWK
parseIBCWK = parse :: String -> CTerm IBCWK

-- ** IKS

data IKS

iIKS, kIKS, sIKS :: Combinator IKS
iIKS = Combinator "I" ["_u"] (Var ("_u"))
kIKS = Combinator "K" ["_u", "_v"] (Var ("_u"))
sIKS = Combinator "S" ["_u", "_v", "_w"]
            (Var ("_u") :@ Var ("_w") :@
            (Var ("_v") :@ Var ("_w")))

instance Basis IKS where
    primCombs = [iIKS,kIKS,sIKS]

instance BracketAbstract IKS where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1) :@: r) | LVar v1 == r = Const iIKS
    bracketAbstract ((LAbst v1) :@: r) | not (occurs v1 r) = Const kIKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1) :@: (l :@: r))   = Const sIKS :@  bracketAbstract ((LAbst v1) :@: l)
                                                    :@ bracketAbstract ((LAbst v1) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

parseIKS :: String -> CTerm IKS
parseIKS = parse
