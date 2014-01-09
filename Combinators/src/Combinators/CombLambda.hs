{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, StandaloneDeriving, GADTs #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombLambda
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-----------------------------------------------------------------------------

module Combinators.CombLambda where


import Combinators.Lambda
import Combinators.Combinator
import Combinators.Variable

-----------------------------------------------------------------------------
-- * Comb Lambda - back and forth between combinatory logic and lamnbda calculus
-----------------------------------------------------------------------------

-- Converts a term of combinatory logic into an untyped lambda term
combToLambda :: CTerm basis -> LTerm VarString Untyped
combToLambda = combToLambda'

combToLambda' :: CTerm basis -> LTerm VarString Untyped
combToLambda' (Var v) = LVar v
combToLambda' (l :@ r) = combToLambda' l :@: combToLambda' r
combToLambda' (Const comb) =  reductToLambda (combVars comb) (combReduct comb)

reductToLambda :: [VarString] -> CTerm basis -> LTerm VarString Untyped
reductToLambda vars term = foldr (\v t -> LAbst v Untyped :@: t) (combToLambda'' term) vars
  where
    combToLambda'' (Var v)    = LVar v
    combToLambda'' (l :@ r)   = combToLambda'' l :@: combToLambda'' r
    combToLambda'' (Const c)  = error $ "CombLambda>>reductToLambda: Const in reduct not allowed " ++
                                show (combName c)



class Basis b => BracketAbstract b where
    bracketAbstract :: LTerm VarString t -> CTerm b
    bracketAbstract' :: VarString -> CTerm b -> CTerm b


instance BracketAbstract KS where
    bracketAbstract ((LAbst v1 _ty) :@: ((LAbst v2 ty2) :@: r)) =
        bracketAbstract' v1  (bracketAbstract ((LAbst v2 ty2) :@: r))
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1 _) :@: LVar r) | v1 == r = Const sKS :@ Const kKS :@ Const kKS
    bracketAbstract ((LAbst v1 _) :@: r) | not (occurs v1 r) = Const kKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1 ty) :@: (l :@: r))   = Const sKS :@  bracketAbstract ((LAbst v1 ty) :@: l)
                                                    :@ bracketAbstract ((LAbst v1 ty) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v _) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v

    bracketAbstract' v (Var n) | v == n     = Const sKS :@ Const kKS :@ Const kKS
                               | otherwise = Const kKS :@ Var n
    bracketAbstract' _v (Const c)          = Const kKS :@ Const c
    bracketAbstract' v r | not (occursC v r) = Const kKS :@ r
    bracketAbstract' v (l :@ r)            = Const sKS :@ bracketAbstract' v l :@ bracketAbstract' v r



