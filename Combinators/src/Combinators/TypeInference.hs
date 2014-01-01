{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.TypeInference
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Combinators.TypeInference (
    Typeable(..)
) where

import Combinators.BinaryTree (BinaryTree)
import Combinators.Reduction (Term)
import Combinators.Types
import Combinators.Lambda
import Combinators.Variable
import Data.Maybe (fromJust)


-----------------------------------------------------------------------------
-- * Type inference


-- | A type environment binds atomic types, represented as Strings to types.
-- In this representation types may be unassigned
type TypeEnv = [(VarString,SType)]

-- | A substituor binds the type that should be substituted to a type variable
type Substitutor = [(TypeAtom,SType)]

-- | A class that describe a possible Typeable Term
class (BinaryTree t, Term t) =>  Typeable t where
    inferSTypeClosed :: t -> Maybe SType
    -- ^ Infers just the simple type of a closed Term or returns Nothing, if the
    -- term is not typeable
    inferSType :: t -> Maybe (SType, TypeEnv)
    -- ^ Infers just the simple type and environment of a Term or returns Nothing,
    -- if the term is not typeable.

-----------------------------------------------------------------------------
-- ** Lambda with Strings

-- | List all type atoms of a type
typeVars :: SType -> [TypeAtom]
typeVars (SAtom n)       = [n]
typeVars (l :->: r)       = typeVars l ++ typeVars r

-- | Apply a substitutor to a type
substituteType :: Substitutor -> SType -> SType
substituteType subst (SAtom a) = case lookup a subst of
                                    Nothing -> (SAtom a)
                                    Just replace -> replace
substituteType subst (l :->: r) = substituteType subst l :->: substituteType subst r

-- | Apply a substitutor to an environment
substituteEnv :: Substitutor -> TypeEnv -> TypeEnv
substituteEnv subst env = map (substitute' subst) env
  where
    substitute' ((str,newType):rest) (str2,oldType) | str == str2 = (str,newType)
                                                    | otherwise  = substitute' rest (str2,oldType)
    substitute' [] pair                                          = pair

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
unify :: SType -> SType -> Maybe Substitutor
unify t1 t2 | t1 == t2                       = Just []
unify (SAtom s) b | not (elem s (typeVars b)) = Just [(s,b)]
                  | otherwise               = Nothing
unify (l :->: r) (SAtom s)                   = unify (SAtom s) (l :->: r)
unify (l1 :->: r1) (l2 :->: r2)               = case unify r1 r2 of
                                                Nothing -> Nothing
                                                Just substr ->
                                                    case unify (substituteType substr l1)
                                                               (substituteType substr l2) of
                                                        Nothing -> Nothing
                                                        Just substl -> Just (substl ++ substr)


instance Typeable (LTerm VarString) where
    inferSTypeClosed term | isClosed term = case inferSType' (0,[]) term of
                                                Just (_,r) -> Just r
                                                Nothing    -> Nothing
                          | otherwise     = error "TypeInference>>inferSTypeClosed: Term has free varibles"
    inferSType term   = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  case inferSType' (length env,env) term of
                                Just ((_,env),r) -> Just (r,env)
                                Nothing    -> Nothing

inferSType' :: (Int,TypeEnv) -> LTerm VarString -> Maybe ((Int,TypeEnv), SType)
inferSType' (index,env) (LVar s)  =
    case lookup s env of
        Nothing -> error ("TypeInference>>inferSType': Unbound variable: " ++ s ++ " env: " ++ show env)
        Just t  -> Just ((index, env),t)

inferSType' (index,env) (LAbst s :@: t) =
    let newType = SAtom $ typeVarGen !! index
    in case inferSType' (index + 1,(s,newType):env) t of
                Nothing                 -> Nothing
                Just ((_ind,env'),nt)   -> Just ((index,tail env'),newType :->: nt)

inferSType' (index,env) (l :@: r) =
    case inferSType' (index,env) l of
        Nothing                 -> Nothing
        Just ((index',env'),tl) ->
            case inferSType' (index',env') r of
                Nothing                   -> Nothing
                Just ((index'',env''),tr) -> case unify (SAtom "_res") (tl :->: tr) of
                                                Nothing -> Nothing
                                                Just subst -> case lookup "_res" subst of
                                                                Nothing -> error $ "Missing _res" ++ show subst
                                                                Just t -> Just ((index'',substituteEnv subst env''),
                                                                    substituteType subst t
                                                                        )  -- Another infer type?
inferSType' _ (LAbst _) = error "LambdaType>>inferSType: Lonely LAbst"


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

