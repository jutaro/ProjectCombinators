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

{-# LANGUAGE FlexibleInstances, DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.TypeInference (
    Typeable(..)
) where

import Combinators.BinaryTree (PP(..), BinaryTree)
import Combinators.Reduction (Term)
import Combinators.Lambda
import Combinators.Variable
import Combinators.Types
       (typeVarGen, SType(..), TypeAtom, SType)

import Text.PrettyPrint
       ((<>), parens, brackets, ($$), (<+>), text, braces, empty, Doc)
import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA (char, many)

-- import Debug.Trace (trace)
trace :: a -> b -> b
trace _ s = s

-----------------------------------------------------------------------------
-- * Type inference


-- | A type environment binds atomic types, represented as Strings to types.
-- In this representation types may be unassigned
type TypeEnv = [(VarString,SType)]

instance PP TypeEnv where
    pp          = brackets . ppEnv
    pparser     = parseEnv

instance PP (SType,TypeEnv) where
    pp(st,te)   = parens (pp st <> text " , " <> pp te)
    pparser     = do
        PA.char '('
        st <- pparser
        PA.char ','
        te <- pparser
        PA.char ')'
        return (st,te)

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

ppEnv :: TypeEnv -> Doc
ppEnv []           = empty
ppEnv ((ta,tp):tl) = braces (text ta <+> text "=" <+> pp tp) $$ ppEnv tl

parseEnv :: Parser TypeEnv
parseEnv = do
   PA.char '['
   r <- PA.many parseEnvEntry
   PA.char ']'
   return r

parseEnvEntry :: Parser (TypeAtom,SType)
parseEnvEntry = do
    PA.char '('
    l <- varParse
    PA.char '='
    r <- pparser
    PA.char ')'
    return (l,r)

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
substituteEnv subst env = map (\(n,t) -> (n,substituteType subst t)) env

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
unify,unify' :: SType -> SType -> Maybe Substitutor
unify t1 t2 = trace ("unify t1: " ++ pps t1 ++ " t2: " ++ pps t2) $ unify' t1 t2
unify' t1 t2 | t1 == t2                       = Just []
unify' (SAtom s) b | not (elem s (typeVars b)) = Just [(s,b)]
                  | otherwise               = Nothing
unify' (l :->: r) (SAtom s)                   = unify (SAtom s) (l :->: r)
unify' (l1 :->: r1) (l2 :->: r2)               = case unify r1 r2 of
                                                Nothing -> Nothing
                                                Just substr ->
                                                    case unify (substituteType substr l1)
                                                               (substituteType substr l2) of
                                                        Nothing -> Nothing
                                                        Just substl -> Just (substl ++ substr)


instance Typeable (LTerm VarString) where
    inferSTypeClosed term | isClosed term = case inferSType' (0,[]) term of
                                                Just (_,_,r) -> Just r
                                                Nothing    -> Nothing
                          | otherwise     = error "TypeInference>>inferSTypeClosed: Term has free varibles"
    inferSType term   = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  case inferSType' (length env,env) term of
                                Just (_,env,r) -> Just (r,env)
                                Nothing    -> Nothing

inferSType',inferSType'' :: (Int,TypeEnv) -> LTerm VarString -> Maybe (Int,TypeEnv, SType)
inferSType' (index,env) t = trace ("inferStype' index: " ++ show index ++ " env: " ++ show env ++
                                " term: " ++ pps t) $ inferSType'' (index,env) t

inferSType'' (index,env) (LVar s) =
    case lookup s env of
        Nothing -> error ("TypeInference>>inferSType': Unbound variableV: " ++ s ++ " env: " ++ show env)
        Just t  -> Just (index, env,t)

inferSType'' (index,env) (LAbst s :@: term) =
    let newType = SAtom $ typeVarGen !! index
    in case inferSType' (index + 1,(s,newType):env) term of
                Nothing                  -> Nothing
                Just (_ind, env',nt)     -> case lookup s env' of
                                                Nothing -> error ("TypeInference>>inferSType': Unbound variableL: "
                                                                ++ s ++ " env: " ++ show env')
                                                Just t  -> Just (index,tail env',t :->: nt)

inferSType'' (index,env) (l :@: r) =
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
inferSType'' _ (LAbst _) = error "LambdaType>>inferSType: Lonely LAbst"

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

