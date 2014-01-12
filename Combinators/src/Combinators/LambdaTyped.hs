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
    typeLambda,
    untypeLambda
) where

import Combinators.BinaryTree (PP(..), PP)
import Combinators.Lambda
import Combinators.Types
import Combinators.Variable (VarInt, varParse, varPp, VarString)

import qualified Text.PrettyPrint as PP
       ((<+>), fsep, fcat, parens, text, Doc)
import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA
       (many1, (<|>), char, (<?>), try, option, spaces)
-- import Debug.Trace (trace)

-----------------------------------------------------------------------------
-- ** Lambda terms with simple types

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
-- ** Type checking

-- TODO Type checking deBruijn
instance Typeable (LTerm VarInt SType) where
    typeof env term = typeof env $ fromLambdaB term
    typeof' term    = typeof' $ fromLambdaB term
    typeofC term    = typeofC $ fromLambdaB term

instance Typeable (LTerm VarString SType) where
    typeof env term   = case getType env term of
                                Just r     -> Just $ (canonicalizeType r,[])
                                Nothing    -> Nothing
    typeof' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeof env term
    typeofC term | isClosed term = case typeof [] term of
                                                Just (r,_) -> Just r
                                                Nothing    -> Nothing
                 | otherwise = error "Types>>typeOfC: Term not closed"

-- | Get type for typed term (Lambda church calculus, a term is annotated with types)
getType :: (TypeContext VarString) -> LTerm VarString SType -> Maybe SType
getType cont (LVar s) =
    case lookup s cont of
        Nothing -> error ("LambdaTyped>>getType: Unbound variableV: " ++ s ++ " env: " ++ show cont)
        Just t  -> Just t
getType cont (LAbst s ty :@: term) =
    case getType ((s,ty):cont) term of
                Nothing                  -> Nothing
                Just nt                  -> Just (ty :->: nt)
getType cont (l :@: r) =
    let tl = getType cont l
        tr = getType cont r
    in case tl of
        Just (tl1 :->: tl2) | Just tl1 == tr -> Just tl2
        _                                  -> Nothing
getType _ (LAbst _ _) = error "LambdaType>>getType: Lonely LAbst"

-----------------------------------------------------------------------------
-- ** Type reconstruction

-- TODO Type reconstruction deBruijn
instance Typeable (LTerm VarInt Untyped) where
    typeof env term = typeof env $ fromLambdaB term
    typeof' term    = typeof' $ fromLambdaB term
    typeofC term    = typeofC $ fromLambdaB term

-- TODO Checking correctness of reconstruction
instance Typeable (LTerm VarString Untyped) where
    typeof env term   = case reconstructType (length env,env) term of
                                Just (_,env,r,_) -> Just $ canonicalizeTypeContext (r,env)
                                Nothing    -> Nothing
    typeof' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeof env term
    typeofC term | isClosed term = case typeof [] term of
                                                Just (r,_) -> Just r
                                                Nothing    -> Nothing
                 | otherwise = error "Types>>typeOfC: Term not closed"

-- | Convert an untyped term to a typed term if possible
typeLambda :: TypeContext VarString -> LTerm VarString Untyped -> Maybe (LTerm VarString STyped)
typeLambda env term = case reconstructType (length env,env) term of
                            Just (_,_,_,nt) -> Just $ nt
                            Nothing    -> Nothing

-- | Convert an typed term to an untyped term
untypeLambda :: LTerm VarString SType -> LTerm VarString Untyped
untypeLambda (LVar s)             = (LVar s)
untypeLambda (LAbst s _ :@: term) = (LAbst s Untyped :@: untypeLambda term)
untypeLambda (l :@: r)            = untypeLambda l :@: untypeLambda r
untypeLambda (LAbst _ _)          = error "LambdaType>>untypeLambda: Lonely LAbst"


-- | Infer a simple type for a lambda term
reconstructType :: (Int,TypeContext VarString) -> LTerm VarString t ->
                        Maybe (Int,TypeContext VarString, SType, LTerm VarString STyped)
reconstructType (index,env) (LVar s) =
    case lookup s env of
        Nothing -> error ("LambdaTyped>>reconstructType: Unbound variableV: " ++ s ++ " env: " ++ show env)
        Just t  -> Just (index, env,t,LVar s)
reconstructType (index,env) (LAbst s _ :@: term) =
    let newType = SAtom $ typeVarGen !! index
    in case reconstructType (index + 1,(s,newType):env) term of
                Nothing                  -> Nothing
                Just (_ind, env',nt,nterm) -> case lookup s env' of
                                                Nothing -> error ("LambdaTyped>>reconstructType: Unbound variableL: "
                                                                ++ s ++ " env: " ++ show env')
                                                Just t  -> Just (index,tail env',t :->: nt,
                                                                (LAbst s (STyped t) :@: nterm))
reconstructType (index,env) (l :@: r) =
    let newType = SAtom $ typeVarGen !! index
    in case reconstructType (index+1,env) r of
        Nothing                   -> Nothing
        Just (index',env',tr,ntr) ->
            case reconstructType (index',env') l of
                Nothing                 -> Nothing
                Just (index'',env'',tl,ntl) ->
                    case unifyTypes tl (tr :->: newType)  of
                        Nothing -> Nothing
                        Just subst ->
                            let newEnv = substituteEnv subst env''
                            in Just (index'',newEnv,newType,ntl :@: ntr)
reconstructType _ (LAbst _ _) = error "LambdaTyped>>inferSType: Lonely LAbst"



