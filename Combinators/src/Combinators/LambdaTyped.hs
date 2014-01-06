-----------------------------------------------------------------------------
--
-- Module      :  Combinators.LambdaTyped
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

{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.LambdaTyped (
    STyped(..),
) where

import Combinators.BinaryTree (PP(..), PP)
import Combinators.Lambda
import Combinators.Types
       (substituteType, typeVars, Substitutor, substituteEnv, SType(..),
        TypeContext, canonicalizeTypeContext, typeVarGen, canonicalizeType,
        Typeable(..), Typeable, parseType, SType)
import Combinators.Variable (VarInt, varParse, varPp, VarString)
import qualified Text.PrettyPrint as PP
       ((<+>), fsep, fcat, parens, text, Doc)
import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA
       (many1, (<|>), char, (<?>), try, option, spaces)
import Debug.Trace (trace)



-----------------------------------------------------------------------------
-- ** Lambda terms with simple types

data STyped = STyped SType
    deriving (Eq,Ord,Show)

instance Typed STyped where
    typed (STyped t) = Just t

instance PP (LTerm VarString STyped) where
    pp = ppSt' True True []
    pparser = parseTermSt Nothing

-- | Pretty prints a lambda term with simple types.
ppSt' :: Bool -> Bool -> [(VarString,SType)] -> LTerm VarString STyped -> PP.Doc
ppSt' _ _ _ (LVar v)                          = PP.text (varPp v)
ppSt' il rm l ((LAbst v (STyped ty1)) :@: ((LAbst v' ty2) :@: t'))
                                              = ppSt' il rm ((v,ty1) : l) ((LAbst v' ty2) :@: t')
ppSt' il False l ((LAbst v ty) :@: t)         = PP.parens $ ppSt' il True l ((LAbst v ty) :@: t)
ppSt' _ True l ((LAbst v (STyped ty)) :@: t)  = PP.fcat [PP.text "\\",
                                                PP.fsep (map (\(v,ty) -> (PP.text (varPp v)) PP.<+> pp ty)
                                                    (reverse ((v,ty):l))),
                                                        PP.text ".", ppSt' True True [] t]
ppSt' True rm _ (l :@: r)                     = PP.fsep [ppSt' True False [] l, ppSt' False rm [] r]
ppSt' False _ _ (l :@: r)                     = PP.parens (ppSt' True True [] (l :@: r))
ppSt' _ _ _ (LAbst _ _)                         = error "Lambda>>ppSt': Lonely LAbst"

parseTermSt :: Maybe (LTerm VarString STyped) -> Parser (LTerm VarString STyped)
parseTermSt Nothing = do
    PA.spaces
    do
        t <- parsePartSt
        PA.option t $ PA.try (parseTermSt (Just t))
    PA.<?> "parseTermSt Nothing"
parseTermSt (Just l) = do
    PA.spaces
    do
        t <- parsePartSt
        PA.option (l :@: t) $ PA.try (parseTermSt (Just (l :@: t)))
    PA.<?> "parseTermSt Just"

parsePartSt :: Parser (LTerm VarString STyped)
parsePartSt = do
    PA.spaces
    do
        PA.char '('
        l <- parseTermSt Nothing
        PA.spaces
        PA.char ')'
        return l
    PA.<|> do
        PA.char '\\'
        PA.spaces
        vl <- PA.many1 typedVarParse
        PA.spaces
        PA.char '.'
        t <- parseTermSt Nothing
        return (foldr (\ (v,ty) t -> t :@: LAbst v (STyped ty)) t vl)
    PA.<|> do
        v <- varParse
        return (LVar v)

    PA.<?> "parsePartST"

typedVarParse :: Parser (VarString,SType)
typedVarParse = do
    v <- varParse
    PA.spaces
    PA.char ':'
    PA.spaces
    ty <- parseType []
    return (v,ty)
    PA.<?> "typedVarParse"


-----------------------------------------------------------------------------
-- ** Type reconstruction

instance Typeable (LTerm VarInt Untyped) where
    typeof term = typeof $ fromLambdaB term
    typeofC term = typeofC $ fromLambdaB term

instance Typeable (LTerm VarString Untyped) where
    typeofC term | isClosed term = case inferSType' (0,[]) term of
                                                Just (_,_,r) -> Just (canonicalizeType r)
                                                Nothing    -> Nothing
                          | otherwise     = error "TypeInference>>inferSTypeClosed: Term has free varibles"
    typeof term   = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  case inferSType' (length env,env) term of
                                Just (_,env,r) -> Just $ canonicalizeTypeContext (r,env)
                                Nothing    -> Nothing

-- | Infer a simple type for a lambda term
inferSType' :: (Int,TypeContext VarString) -> LTerm VarString t -> Maybe (Int,TypeContext VarString, SType)
inferSType' (index,env) (LVar s) =
    case lookup s env of
        Nothing -> error ("TypeInference>>inferSType': Unbound variableV: " ++ s ++ " env: " ++ show env)
        Just t  -> Just (index, env,t)
inferSType' (index,env) (LAbst s _ :@: term) =
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
inferSType' _ (LAbst _ _) = error "LambdaType>>inferSType: Lonely LAbst"

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
