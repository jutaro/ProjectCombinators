{-# LANGUAGE ParallelListComp #-}
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
    typeLambda,
    untypeLambda,
    reconstructType,
    inhabitants,
    inhabitants''
) where

import Combinators.BinaryTree
       (rightSpine, BinaryTree(..), BinaryTree, PP(..), PP)
import Combinators.Lambda
import Combinators.Types
import Combinators.Variable
       (nameGen, VarInt, varParse, varPp, VarString)

import qualified Text.PrettyPrint as PP
       ((<>), fsep, fcat, parens, text, Doc)
import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA
       (many1, (<|>), char, (<?>), try, option, spaces)
import Debug.Trace (trace)
import Control.Monad.Trans.Reader (runReader, Reader)
import Control.Monad.Trans.State (get, modify, State, runState)
import Control.Monad (liftM, foldM)
import Data.List (transpose)

-----------------------------------------------------------------------------
-- ** Lambda terms with simple types

instance PP (LTerm VarString SType) where
    pp = ppSt' True True []
    pparser = parseTermSt Nothing

-- | Pretty prints a lambda term with simple types.
ppSt' :: Bool -> Bool -> [(VarString,SType)] -> LTerm VarString SType -> PP.Doc
ppSt' _ _ _ (LVar v)                          = PP.text (varPp v)
ppSt' il rm l ((LAbst v ty1) :@: ((LAbst v' ty2) :@: t'))
                                              = ppSt' il rm ((v,ty1) : l) ((LAbst v' ty2) :@: t')
ppSt' il False l ((LAbst v ty) :@: t)         = PP.parens $ ppSt' il True l ((LAbst v ty) :@: t)
ppSt' _ True l ((LAbst v ty) :@: t)  = PP.fcat [PP.text "\\",
                                                PP.fsep (map (\(v,ty) -> (PP.text (varPp v))
                                                            PP.<> PP.text ":" PP.<>pp ty)
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
        return (foldr (\ (v,ty) t -> t :@: LAbst v ty) t vl)
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
                                Just r -> Just $ (canonicalizeType r,[])
                                Nothing    -> Nothing
    typeof' term = let env = map (\(v,i) -> (v, SAtom (typeVarGen !! i))) $ zip (freeVars term) [0..]
                        in  typeof env term
    typeofC term | isClosed term = case typeof [] term of
                                                Just (r,_) -> Just r
                                                Nothing    -> Nothing
                 | otherwise = error ("Types>>typeOfC: Term not closed: " ++ pps term)

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
                            Just (_,_,_,nt) -> Just $ nt
                            Nothing    -> Nothing

-- | Convert an typed term to an untyped term
untypeLambda :: LTerm VarString SType -> LTerm VarString Untyped
untypeLambda (LVar s)             = (LVar s)
untypeLambda (LAbst s _ :@: term) = (LAbst s Untyped :@: untypeLambda term)
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
                        Just t  -> Just (ind,tail env',t :->: nt, (LAbst s t :@: nterm))
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
            then trace ("reconstructType res: " ++ show res) $ res
            else res

-----------------------------------------------------------------------------
-- ** Type inhabitation for simple types



inhabitants :: SType -> [LTerm VarString SType]
inhabitants t = fst $ runState (inhabitants' t) (0,[])

inhabitants', inhabitants'' :: SType -> State (Int,TypeContext VarString) [LTerm VarString SType]
inhabitants'' (l :->: r) = do
    (iu,_) <- get
    modify (\ (i,cont) -> (i+1,(nameGen !! i,l):cont))
    rec <- inhabitants' r
    return (map (LAbst (nameGen !! iu) l :@:) rec)

inhabitants'' (SAtom s)  = do
    (_,cont) <- get
    let tupels = map (\ (v,t) -> (v,rightRest t))
                    $ (filter (\(_,t) -> resultType t == (SAtom s)))
                        cont
    res <- -- trace ("tupels: " ++ show tupels) $
            -- for every tupel find solutions
                mapM (\(s,tl) ->  foldM calc [LVar s] tl) tupels
    return (concat res)

  where
            -- for one tupel find solutions
    calc :: [LTerm VarString SType] -> SType -> State (Int,TypeContext VarString) [LTerm VarString SType]
    calc s t = do
        t' <- inhabitants' t
        return [l :@:r| l <- s , r <- t']

--         let res = concat ll
--         trace ("calcRes: " ++ show res ++ " ll: " ++ show ll ++ " s: " ++ show s) $ return res

inhabitants' st = -- trace ("inhabitants type: " ++ pps st) $
    do
        (_,cont) <- get
        res <- -- trace ("cont: " ++ show cont) $
                inhabitants'' st
        return (res)

resultType :: SType -> SType
resultType a = head (rightSpine a)

rightRest :: BinaryTree t => t -> [t]
rightRest t = case decompose t of
                Nothing -> []
                Just _ -> reverse (tail (rightSpine t))

