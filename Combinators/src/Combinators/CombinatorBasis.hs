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
import Combinators.Variable
import Combinators.CombLambda
import Combinators.Lambda

-----------------------------------------------------------------------------
-- * Alternative bases for Combinatory logic
-----------------------------------------------------------------------------

-- ** IBCWK

-- | Definition of the combinators for the IBCWK Basis
data IBCWK

iIBCWK, bIBCWK, cIBCWK, kIBCWK, wIBCWK :: Variable v => Combinator IBCWK v

iIBCWK = Combinator "I" [varString "_u"] (Var (varString "_u"))
bIBCWK = Combinator "B" [varString "_u",varString "_v",varString "_w"]
            (Var (varString "_u") :@ (Var (varString "_v") :@ Var (varString "_w")))
cIBCWK = Combinator "C" [varString "_u",varString "_v",varString "_w"]
            ((Var (varString "_u") :@ Var (varString "_w")) :@ Var (varString "_v"))
kIBCWK = Combinator "K" [varString "_u", varString "_v"]
            (Var (varString "_u"))
wIBCWK = Combinator "W" [varString "_u", varString "_v"]
            (Var (varString "_u") :@ Var (varString"_v") :@ Var (varString "_v"))

instance Variable v => Basis IBCWK v where
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

parseIBCWK :: String -> CTerm IBCWK VarString
parseIBCWK = parse :: String -> CTerm IBCWK VarString

-- ** IKS

data IKS

iIKS, kIKS, sIKS :: Variable v => Combinator IKS v
iIKS = Combinator "I" [varString "_u"] (Var (varString "_u"))
kIKS = Combinator "K" [varString "_u", varString "_v"] (Var (varString "_u"))
sIKS = Combinator "S" [varString "_u", varString "_v", varString"_w"]
            (Var (varString "_u") :@ Var (varString"_w") :@
            (Var (varString "_v") :@ Var (varString "_w")))

instance Variable v => Basis IKS v where
    primCombs = [iIKS,kIKS,sIKS]

instance BracketAbstract IKS VarString where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1) :@: r) | LVar v1 == r = Const iIKS
    bracketAbstract ((LAbst v1) :@: r) | not (occurs v1 r) = Const kIKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1) :@: (l :@: r))   = Const sIKS :@  bracketAbstract ((LAbst v1) :@: l)
                                                    :@ bracketAbstract ((LAbst v1) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

parseIKS :: String -> CTerm IKS VarString
parseIKS = parse :: String -> CTerm IKS VarString
