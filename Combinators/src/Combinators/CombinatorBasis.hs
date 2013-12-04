{-# LANGUAGE EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Basis
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Alternative basis for Combinatory logic
--
-----------------------------------------------------------------------------

module Combinators.CombinatorBasis where

import Combinators.Combinator
import Combinators.Variable
import Combinators.CombLambda
import Combinators.Lambda


-- | Definition of the combinators for the IBCWK Basis
data IBCWK

iIBCWK, bIBCWK, cIBCWK, kIBCWK, wIBCWK :: Variable v => Combinator IBCWK v

iIBCWK = Combinator "I" [varString "__x"] (Var (varString "__x"))
bIBCWK = Combinator "B" [varString "__x",varString "__y",varString "__z"]
            (Var (varString "__x") :@ (Var (varString "__y") :@ Var (varString "__z")))
cIBCWK = Combinator "C" [varString "__x",varString "__y",varString "__z"]
            ((Var (varString "__x") :@ Var (varString "__z")) :@ Var (varString "__y"))
kIBCWK = Combinator "K" [varString "__x", varString "__y"]
            (Var (varString "__x"))
wIBCWK = Combinator "W" [varString "__x", varString "__y"]
            (Var (varString "__x") :@ Var (varString"__y") :@ Var (varString "__y"))

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
parseIBCWK = undefined -- parse :: String -> CTerm IBCWK VarString

-- * Definition of the combinators for the IKS Basis

data IKS

iIKS, kIKS, sIKS :: Variable v => Combinator IKS v
iIKS = Combinator "I" [varString "__x"] (Var (varString "__x"))
kIKS = Combinator "K" [varString "__x", varString "__y"] (Var (varString "__x"))
sIKS = Combinator "S" [varString "__x", varString "__y", varString"__z"]
            (Var (varString "__x") :@ Var (varString"__z") :@
            (Var (varString "__y") :@ Var (varString "__z")))

instance Variable v => Basis IKS v where
    primCombs = [iIKS,kIKS,sIKS]

instance Variable v => BracketAbstract IKS v where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1) :@: r) | LVar v1 == r = Const iIKS
    bracketAbstract ((LAbst v1) :@: r) | not (occurs v1 r) = Const kIKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1) :@: (l :@: r))   = Const sIKS :@  bracketAbstract ((LAbst v1) :@: l)
                                                    :@ bracketAbstract ((LAbst v1) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

parseIKS :: String -> CTerm IKS VarString
parseIKS = parse :: String -> CTerm IKS VarString
