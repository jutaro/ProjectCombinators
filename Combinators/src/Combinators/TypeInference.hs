-----------------------------------------------------------------------------
--
-- Module      :  Combinators.TypeInference
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances, DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.TypeInference (
    Typeable(..),
    genList
) where

import Combinators.BinaryTree (PP(..))
import Combinators.Reduction
       (NormalForm(..), instrumentedContext, reduceIt, Term)
import Combinators.Lambda
import Combinators.Variable
import Combinators.Types
import Combinators.CombGenerator (genCombs)
import Combinators.CombLambda (combToLambda)
import Combinators.Combinator (CTerm, KS)

-- import Debug.Trace (trace)
trace :: a -> b -> b
trace _ s = s

-----------------------------------------------------------------------------
-- * Type inference

-- | A class that describe a possible Typeable Term
class Term t =>  Typeable t where
    inferSTypeClosed :: t -> Maybe SType
    -- ^ Infers just the simple type of a closed Term or returns Nothing, if the
    -- term is not typeable
    inferSType :: t -> Maybe (SType, TypeEnv VarString)
    -- ^ Infers just the simple type and environment of a Term or returns Nothing,
    -- if the term is not typeable.

-----------------------------------------------------------------------------
-- ** Lambda with Strings

instance Typeable (LTerm VarInt) where
    inferSType term = inferSType $ fromLambdaB term
    inferSTypeClosed term = inferSTypeClosed $ fromLambdaB term

instance Typeable (LTerm VarString) where
    inferSTypeClosed term | isClosed term = case inferSType' (0,[]) term of
                                                Just (_,_,r) -> Just (canonicalizeType r)
                                                Nothing    -> Nothing
                          | otherwise     = error "TypeInference>>inferSTypeClosed: Term has free varibles"
    inferSType term   = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  case inferSType' (length env,env) term of
                                Just (_,env,r) -> Just $ canonicalizeTypeEnv (r,env)
                                Nothing    -> Nothing

-- | Infer a simple type for a lambda term
inferSType' :: (Int,TypeEnv VarString) -> LTerm VarString -> Maybe (Int,TypeEnv VarString, SType)
inferSType' (index,env) (LVar s) =
    case lookup s env of
        Nothing -> error ("TypeInference>>inferSType': Unbound variableV: " ++ s ++ " env: " ++ show env)
        Just t  -> Just (index, env,t)
inferSType' (index,env) (LAbst s :@: term) =
    let newType = SAtom $ typeVarGen !! index
    in case inferSType' (index + 1,(s,newType):env) term of
                Nothing                  -> Nothing
                Just (_ind, env',nt)     -> case lookup s env' of
                                                Nothing -> error ("TypeInference>>inferSType': Unbound variableL: "
                                                                ++ s ++ " env: " ++ show env')
                                                Just t  -> Just (index,tail env',t :->: nt)
inferSType' (index,env) (l :@: r) =
    let newType = SAtom $ typeVarGen !! index
    in case inferSType' (index+1,env) r of
        Nothing                   -> Nothing
        Just (index',env',tr) ->
            case inferSType' (index',env') l of
                Nothing                 -> Nothing
                Just (index'',env'',tl) ->
                    case unify tl (tr :->: newType)  of
                        Nothing -> Nothing
                        Just subst ->
                            let newEnv = substituteEnv subst env''
                            in trace ("inferStypeA index: " ++ show index'' ++ " env: " ++ show newEnv ++
                                            " term: " ++ pps newType) $ Just (index'',newEnv,newType)
inferSType' _ (LAbst _) = error "LambdaType>>inferSType: Lonely LAbst"

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
unify :: SType -> SType -> Maybe Substitutor
unify t1 t2 | t1 == t2                         = Just []
unify (SAtom s) b | not (elem s (typeVars b))   = Just [(s,b)]
                  | otherwise                 = Nothing
unify (l :->: r) (SAtom s)                     = unify (SAtom s) (l :->: r)
unify (l1 :->: r1) (l2 :->: r2)                 = case unify r1 r2 of
                                                Nothing -> Nothing
                                                Just substr ->
                                                    case unify (substituteType substr l1)
                                                               (substituteType substr l2) of
                                                        Nothing -> Nothing
                                                        Just substl -> Just (substl ++ substr)

-- genList :: Int -> [(String, String, String, String, String)]
genList n = map (\c ->
                    let reducedCombinator = reduceIt instrumentedContext NormalForm c
                        lambda            = combToLambda reducedCombinator
                        reducedLambda     = reduceIt instrumentedContext NormalForm (toLambdaB lambda)
                        itype             = inferSType lambda
                    in (pps c,pps reducedCombinator{-,pps lambda, pps reducedLambda,pps itype-} ))
                $ take n (genCombs :: [CTerm KS])

-----------------------------------------------------------------------------
-- ** Combinators

{-
instance Basis b => Typeable (CTerm b) where
    inferSType comb = snd $ inferSType' (0,[]) comb

primType :: Int -> Combinator c -> (Int,SType)
primType ind comb = let ((ind',_),t) = replaceVars (ind,[]) (combType comb)
                    in (ind',t)
  where
    replaceVars (ind,binds) (SAtom s) =
        case lookup s binds of
            Nothing -> ((ind + 1,(s,ind):binds),SAtom (typeVarGen !! ind))
            Just i -> ((ind,binds), SAtom (typeVarGen !! i))
    replaceVars (ind,binds) (l :->: r) =
        let ((ind',binds'),l') = replaceVars (ind,binds) l
            ((ind'',binds''),r') = replaceVars (ind',binds') r
        in ((ind'',binds''), l' :->: r')



inferSType' :: Basis b => (Int,[(String,Int)]) -> CTerm b -> ((Int,[(String,Int)]),SType)
inferSType' (ind,binds) (Const c) = let (newInd, newType) = primType ind c
                                    in ((newInd,binds),newType)
inferSType' (ind,binds) (Var s)   = case lookup s binds of
                                        Nothing -> ((ind + 1,(s,ind):binds),SAtom (typeVarGen !! ind))
                                        Just i -> ((ind,binds), SAtom (typeVarGen !! i))
inferSType' (ind,binds) (l :@ r)  = let ((ind',binds'),l') = inferSType' (ind,binds) l
                                        ((ind'',binds''),r') = inferSType' (ind',binds') r
                                    in ((ind'',binds''), l' :->: r')

unifyTypes :: SType -> SType -> Maybe ([String,SType], SType)
unifyTypes = unifyTypes' []
  where
    unifyTypes' env l (Var r)           =   case lookup r env of
                                                Nothing -> (r,l):env
                                                Just t -> unifyTypes' env l t
    unifyTypes' env (Var l) (r1 :@ r2)  =   case lookup r env of
                                                Nothing -> (r,l):env
                                                Just t -> unifyTypes' env l t
-}

