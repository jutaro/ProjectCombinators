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
import Combinators.Reduction

-----------------------------------------------------------------------------
-- * Comb Lambda - back and forth between combinatory logic and lamnbda calculus
-----------------------------------------------------------------------------

-- | Converts a term of combinatory logic into an untyped lambda term
combToLambda :: CTerm basis -> LTerm VarString Untyped
combToLambda = canonicalize . combToLambda'

combToLambda' :: CTerm basis -> LTerm VarString Untyped
combToLambda' (Var v)      = LVar v
combToLambda' (l :@ r)     = combToLambda' l :@: combToLambda' r
combToLambda' (Const comb) = reductToLambda (combVars comb) (combReduct comb)

reductToLambda :: [VarString] -> CTerm basis -> LTerm VarString Untyped
reductToLambda vars term  = foldr (\v t -> LAbst v Untyped :@: t) (combToLambda'' term) vars
  where
    combToLambda'' (Var v)    = LVar v
    combToLambda'' (l :@ r)   = combToLambda'' l :@: combToLambda'' r
    combToLambda'' (Const c)  = error $ "CombLambda>>reductToLambda: Const in reduct not allowed " ++
                                show (combName c)


-- | This is a class that serves to convert a term of combinatory logic to a lambda term.
class Basis b => BracketAbstract b where
    bracketAbstract :: LTerm VarString t -> CTerm b
    -- ^ Implement / Call this to convert a combinatory term to a lambda term
    bracketAbstract' :: VarString -> CTerm b -> CTerm b
    -- ^ Implement this as a helper for nested abstrations

instance BracketAbstract KS where
    -- nested abstractions are passed to the helper function
    bracketAbstract ((LAbst v _ty) :@: ((LAbst v2 ty2) :@: r)) =
        bracketAbstract' v  (bracketAbstract ((LAbst v2 ty2) :@: r))
    bracketAbstract (LVar v) = Var v
    -- identity case
    bracketAbstract ((LAbst v _) :@: LVar r) | v == r = Const s :@ Const k :@ Const k
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
    bracketAbstract' v (Var n) | v == n     = Const s :@ Const k :@ Const k
    -- constant case
                               | otherwise = Const k :@ Var n
    bracketAbstract' _v (Const c)          = Const k :@ Const c
    bracketAbstract' v r | not (occurs v r) = Const k :@ r
    -- application case
    bracketAbstract' v (l :@ r)            = Const s :@ bracketAbstract' v l :@ bracketAbstract' v r




