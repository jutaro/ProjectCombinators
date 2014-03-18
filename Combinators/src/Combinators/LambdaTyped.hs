-----------------------------------------------------------------------------
--
-- Module      :  Combinators.LambdaTyped
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

{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.LambdaTyped (
-----------------------------------------------------------------------------
-- * Simple Types for lambda terms
-----------------------------------------------------------------------------
    typeLambda,
    typeLambda',
    untypeLambda,
-----------------------------------------------------------------------------
-- ** Lambda terms inhabitants for simple types
    inhabitants,
--    inhabitants''
) where

import Combinators.BinaryTree
       (rightSpine, BinaryTree(..))
import Combinators.Lambda
import Combinators.Types
import Combinators.Variable
       (nameGen, VarInt, varParse, varPp, VarString)

import qualified Text.PrettyPrint as PP
       ((<>), fsep, fcat, parens, text, Doc)

import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA

import Data.List (transpose)
import Debug.Trace (trace)
import Combinators.PrintingParsing (PP(..), parens', symbol', dot', colon')
import Combinators.Reduction (StringTerm(..))
import Control.Arrow (Arrow(..))

-----------------------------------------------------------------------------
-- ** Lambda terms with simple types

instance PP (LTerm VarString SType) where
    pp = ppSt' True True []
    pparser = parseTermSt Nothing

-- | Pretty prints a lambda term with simple types.
ppSt' :: Bool -> Bool -> [(VarString,SType)] -> LTerm VarString SType -> PP.Doc
ppSt' _ _ _ (LVar v)                          = PP.text (varPp v)
ppSt' il rm l (LAbst v ty1 :@: (LAbst v' ty2 :@: t'))
                                              = ppSt' il rm ((v,ty1) : l) (LAbst v' ty2 :@: t')
ppSt' il False l (LAbst v ty :@: t)         = PP.parens $ ppSt' il True l (LAbst v ty :@: t)
ppSt' _ True l (LAbst v ty :@: t)  = PP.fcat [PP.text "\\",
                                                PP.fsep (map (\(v,ty) -> PP.text (varPp v) PP.<>
                                                                        PP.text ":" PP.<>pp ty)
                                                    (reverse ((v,ty):l))),
                                                        PP.text ".", ppSt' True True [] t]
ppSt' True rm _ (l :@: r)                     = PP.fsep [ppSt' True False [] l, ppSt' False rm [] r]
ppSt' False _ _ (l :@: r)                     = PP.parens (ppSt' True True [] (l :@: r))
ppSt' _ _ _ (LAbst _ _)                         = error "Lambda>>ppSt': Lonely LAbst"

parseTermSt :: Maybe (LTerm VarString SType) -> Parser (LTerm VarString SType)
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

parsePartSt :: Parser (LTerm VarString SType)
parsePartSt = do
    PA.spaces
    parens' (parseTermSt Nothing)
    PA.<|> do
        symbol' "\\"
        vl <- PA.many1 (PA.try typedVarParse)
        dot'
        t <- parseTermSt Nothing
        return (foldr (\ (v,ty) t -> LAbst v ty :@: t) t vl)
    PA.<|> do
        v <- varParse
        return (LVar v)

    PA.<?> "parsePartST"

typedVarParse :: Parser (VarString,SType)
typedVarParse = do
    v <- varParse
    colon'
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
                                Just r -> Just (canonicalizeType r, [])
                                Nothing    -> Nothing
    typeof' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeof env term
    typeofC term | isClosed term = case typeof [] term of
                                                Just (r,_) -> Just r
                                                Nothing    -> Nothing
                 | otherwise = error ("Types>>typeOfC: Term not closed: " ++ pps term)

-- | Get type for typed term (Lambda church calculus, a term is annotated with types)
getType :: TypeContext VarString -> LTerm VarString SType -> Maybe SType
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
    typeof env term   = case reconstructType False (length env,env) term of
                                Just (_,env,r,_) -> Just $ canonicalizeTypeContext (r,env)
                                Nothing    -> Nothing
    typeof' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeof env term
    typeofC term | isClosed term = case typeof [] term of
                                                Just (r,_) -> Just r
                                                Nothing    -> Nothing
                 | otherwise = error ("Types>>typeOfC: Term not closed: " ++ pps term)

-- | Convert an untyped term to a typed term if possible
typeLambda :: TypeContext VarString -> LTerm VarString Untyped -> Maybe (LTerm VarString SType)
typeLambda env term = case reconstructType False (length env,env) term of
                            Just (_,_,_,nt) -> Just nt
                            Nothing    -> Nothing

-- | Convert an untyped term to a typed term if possible, generate any types for free variables
typeLambda' :: LTerm VarString Untyped -> Maybe (LTerm VarString SType)
typeLambda' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeLambda env term

-- | Convert an typed term to an untyped term
untypeLambda :: LTerm VarString SType -> LTerm VarString Untyped
untypeLambda (LVar s)             = LVar s
untypeLambda (LAbst s _ :@: term) = LAbst s Untyped :@: untypeLambda term
untypeLambda (l :@: r)            = untypeLambda l :@: untypeLambda r
untypeLambda (LAbst _ _)          = error "LambdaType>>untypeLambda: Lonely LAbst"


-- | Infer a simple type for a lambda term
reconstructType, reconstructType' :: Bool -> (Int,TypeContext VarString) -> LTerm VarString Untyped ->
                        Maybe (Int,TypeContext VarString, SType, LTerm VarString SType)


reconstructType' _b (index,env) (LVar s) =
    case lookup s env of
        Nothing -> error ("LambdaTyped>>reconstructType: Unbound variableV: " ++ s ++ " env: " ++ show env)
        Just t  -> Just (index, env,t,LVar s)
reconstructType' b (index,env) (LAbst s _ :@: term) =
    let newType = SAtom $ typeVarGen !! index
    in case reconstructType b (index + 1,(s,newType):env) term of
                Nothing                  -> Nothing
                Just (ind, env',nt,nterm) ->
                    case lookup s env' of
                        Nothing -> error ("LambdaTyped>>reconstructType: Unbound variableL: "
                                        ++ s ++ " env: " ++ show env')
                        Just t  -> Just (ind, tail env', t :->: nt, LAbst s t :@: nterm)
reconstructType' b (index,env) (l :@: r) = do
        (index',env',tr,ntr)   <- reconstructType b (index,env) r
        (index'',("_res",tr'):env'',tl,ntl) <- reconstructType b (index',("_res",tr):env') l
        case tl of
            SAtom _ ->  do
                let newType = SAtom $ typeVarGen !! index''
                subst <- unifyTypes b tl (tr' :->: newType)
                let newEnv   = substContext subst env''
                    newType' = substType subst newType
                return (index''+1,newEnv,newType',ntl :@: ntr)
            (ll :->: lr) -> do
                subst <- unifyTypes b ll tr'
                let newEnv   = substContext subst env''
                    newType' = substType subst lr
                return (index''+1,newEnv,newType',ntl :@: ntr)

reconstructType' _ _ (LAbst _ _) = error "LambdaTyped>>inferSType: Lonely LAbst"

reconstructType traceIt (index,env) t =
    let res = if traceIt
                then
                    trace ("reconstructType (index,env) " ++ show (index,env) ++ " t: " ++ pps t) $
                        reconstructType' traceIt (index,env) t
                else
                    reconstructType' traceIt (index,env) t
    in if traceIt
            then trace ("reconstructType res: " ++ show res) res
            else res

-----------------------------------------------------------------------------
-- ** Type inhabitation for simple types

type InhContext = (Int,TypeContext VarString,[((Int,SType,TypeContext VarString),[LTerm VarString SType])])

-- | Generates all inhabitants of the type with maximum level elements
inhabitants :: SType -> Int -> [LTerm VarString SType]
inhabitants st level = fst $ inhabitants' st (0,[],[]) level

inhabitants', inhabitants'' :: SType -> InhContext ->  Int ->
        ([LTerm VarString SType],InhContext)
inhabitants' st (i,cont,mem) level  = --trace ("inhabitants type: " ++ pps st ++ " cont: " ++ show cont
                                      --          ++ " level: " ++ show level) $
    let res'@(_r',(_i,_cont',_mem)) = case lookup (level,st,cont) mem of
                Just r -> (r,(i,cont,mem))
                Nothing ->
                    let (res,(i',cont',mem')) = -- trace ("cont: " ++ show cont) $
                            inhabitants'' st (i,cont,mem) level
                    in (res,(i',cont',((level,st,cont),res):mem'))
    in -- trace ("inhabitants type: " ++ pps st ++ " res: " ++ pps r' ++ " cont': " ++ show cont') $
        res'

inhabitants'' (l :->: r)  (i,cont,mem) level =
    let name = nameGen !! i
        (rec,(_i',_cont',mem')) = inhabitants' r (i+1,(name,l):cont,mem) level
    in (map (LAbst name l :@:) rec,(i,cont,mem'))

inhabitants'' (SAtom s) (i,cont,mem) level
                                | level == 0 = ([],(i,cont,mem))
                                | otherwise  =
    let tupels = map (second rightRest)
                    $ filter (\ (_, t) -> resultType t == SAtom s) cont
        (res,(i',cont',mem')) = foldl (\ (accu,(i',cont',mem')) (s,tl) ->
                                    let (res,(i'',cont'',mem'')) =
                                                foldl calc ([LVar s],(i',cont',mem')) tl
                                    in (res : accu,(i'',cont'',mem'')))
                                        ([],(i,cont,mem)) tupels
    in (concat (transpose res),(i',cont',mem'))

  where
            -- for one tupel find solutions
--    calc :: SType -> ([LTerm VarString SType],InhContext) ->
--                        ([LTerm VarString SType],InhContext)
    calc (te,(i,cont,mem)) st  = -- trace ("calc type: " ++ pps st ++ " cont: " ++ show cont ) $
        let (te',(i',cont',mem')) = inhabitants' st (i,cont,mem) (level - 1)
        in ([l :@: r | l <- te , r <- te' ],(i',cont',mem'))

    resultType :: SType -> SType
    resultType a = head (rightSpine a)

    rightRest :: BinaryTree t => t -> [t]
    rightRest t = case decompose t of
                    Nothing -> []
                    Just _ -> reverse (tail (rightSpine t))





