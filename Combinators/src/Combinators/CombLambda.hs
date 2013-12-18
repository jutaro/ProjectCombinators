{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, StandaloneDeriving, GADTs #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombLambda
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-----------------------------------------------------------------------------

module Combinators.CombLambda where

-- import Combinators.BinaryTree
import Combinators.Reduction
import Combinators.Lambda
import Combinators.Combinator
import Combinators.Variable

-----------------------------------------------------------------------------
-- * Comb Lambda - back and forth between combinatory logic and lamnbda calculus
-----------------------------------------------------------------------------

combToLambda' :: CTerm basis VarString -> LTerm VarString
combToLambda' (Var v) = LVar v
combToLambda' (l :@ r) = combToLambda' l :@: combToLambda' r
combToLambda' (Const comb) =  reductToLambda (combVars comb) (combReduct comb)

reductToLambda :: [VarString] -> CTerm basis VarString -> LTerm VarString
reductToLambda vars term = foldr (\v t -> LAbst v :@: t) (combToLambda'' term) vars
  where
    combToLambda'' (Var v)    = LVar v
    combToLambda'' (l :@ r)   = combToLambda'' l :@: combToLambda'' r
    combToLambda'' (Const c)  = error $ "CombLambda>>reductToLambda: Const in reduct not allowed " ++
                                show (combName c)

combToLambda :: CTerm basis VarString -> LTerm VarString
combToLambda = reduceIt instrumentedContext NormalForm . combToLambda

class Basis b v => BracketAbstract b v where
    bracketAbstract :: LTerm v -> CTerm b v

instance BracketAbstract KS VarString where
    bracketAbstract (LVar v) = Var v
    bracketAbstract ((LAbst v1) :@: r) | LVar v1 == r = Const sKS :@ Const kKS :@ Const kKS
    bracketAbstract ((LAbst v1) :@: r) | not (occurs v1 r) = Const kKS :@ bracketAbstract r
    bracketAbstract ((LAbst v1) :@: (l :@: r))   = Const sKS :@  bracketAbstract ((LAbst v1) :@: l)
                                                    :@ bracketAbstract ((LAbst v1) :@: r)
    bracketAbstract (l :@: r) = bracketAbstract l :@ bracketAbstract r
    bracketAbstract (LAbst v) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show v




