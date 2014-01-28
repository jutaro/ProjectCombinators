-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Lambda
-- Copyright   :  Jürgen <jutaro> Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving, FlexibleContexts, MultiParamTypeClasses,
      ScopedTypeVariables #-}


module Combinators.Lambda (
-----------------------------------------------------------------------------
-- * Lambda calculus implementation
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- ** LTerm type
    LTerm(..),
    Untyped(..),
    Typed,
-----------------------------------------------------------------------------
-- ** Properties
    occurs,
    freeVars,
    boundVars,
    isClosed,
    arityLambda,
-----------------------------------------------------------------------------
-- ** Convenience
    reduceLambda,
-----------------------------------------------------------------------------
-- ** De Bruijn indices
    toLambdaB,
    fromLambdaB
) where

import Combinators.Variable
import Combinators.BinaryTree
import Combinators.Reduction
import Combinators.Types

import Text.Parsec.String (Parser)
import qualified Text.Parsec as PA
import qualified Text.PrettyPrint as PP
import Data.List (nub, delete)
import Data.Maybe (fromJust)
import qualified Data.List as List
       (lookup, elemIndex, elem, intersect, nub)
import Control.Monad (liftM)
import Combinators.PrintingParsing (PP(..), parens',symbol',dot')

-----------------------------------------------------------------------------
-- * Lambda calculus implementation
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** LTerm type

-- | A 'Term' in (untyped) lambda calculus is either
--
-- * a variable
-- * an application
-- * a lambda abstraction
--
-- We choose to parametrize on the type of variables, which is a something of class Variable.
-- This makes it possible to use either strings, or de bruijn indices
--
-- As well we really represent here a family of terms, as we form untyped,
-- or different typed terms via the t type variable.
--
-- Abstractions are used together with a pseudo application, to make a term a natural instance
-- of a binary tree, with the burden always to handle the error case of a lonely abstration

data LTerm v t where
      LVar ::  Variable v => v -> LTerm v t
      LAbst :: Typed t => VarString -> t -> LTerm v t
      (:@:) :: Variable v => LTerm v t -> LTerm v t -> LTerm v t

deriving instance Show t => Show (LTerm v t)

instance Eq (LTerm VarString t) where
    a == b = toLambdaB a == toLambdaB b

instance Ord t => Ord (LTerm VarString t) where
    a `compare` b = toLambdaB a `compare` toLambdaB b

instance Eq (LTerm VarInt t) where
    a == b = canonicalizeLambdaB a =:= canonicalizeLambdaB b

(=:=) :: Variable v => LTerm v t -> LTerm v t -> Bool
LVar x1 =:= LVar y1         = x1 == y1
LAbst _x1 x2 =:= LAbst _y1 y2 = x2 == y2 -- don't care about names
(:@:) x1 x2 =:= (:@:) y1 y2 = x1 =:= y1 && x2 =:= y2
_ =:= _                     = False

instance Ord t => Ord (LTerm VarInt t) where
    compare a b = canonicalizeLambdaB a `compare'` canonicalizeLambdaB b

compare' :: Ord t => LTerm v t -> LTerm v t -> Ordering
compare' a b = check a b
  where check (LVar x1) (LVar y1) = compare x1 y1 `_then` EQ
        check (LAbst _x1 x2) (LAbst _y1 y2)
          = compare x2 y2 `_then` EQ -- don't care about names
        check ((:@:) x1 x2) ((:@:) y1 y2)
          = compare' x1 y1 `_then` compare' x2 y2 `_then` EQ
        check x y = compare (tag x) (tag y)
        _then EQ x = x
        _then x _ = x
        tag (LVar{}) = 0 :: Int
        tag (LAbst{}) = 1 :: Int
        tag ((:@:){}) = 2 :: Int

instance Variable v => BinaryTree (LTerm v t) where
    decompose (tl :@: tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@: tr

-- Bind application to the left.
infixl 5 :@:

instance Ord t => Term (LTerm VarInt t) where
    isTerminal (LVar _)         = True
    isTerminal (LAbst _ _)      = True
    isTerminal (LVar _ :@: _r)  = True
    isTerminal (LAbst _ _ :@: _r) = True
    isTerminal _                = False
    canonicalize                = canonicalizeLambdaB

instance Ord t => Term (LTerm VarString t) where
    isTerminal (LVar _)         = True
    isTerminal (LAbst _ _)      = True
    isTerminal (LVar _ :@: _r)  = True
    isTerminal (LAbst _ _ :@: _r) = True
    isTerminal _                = False
    canonicalize                = canonicalizeLambda

instance TermString (LTerm VarString t) where
    occurs v (LVar n)                      = v == n
    occurs v (LAbst n _ :@: t) | v == n     = False
                             | otherwise   = occurs v t
    occurs v (l :@: r)                     = occurs v l || occurs v r
    occurs _v (LAbst n _)                  = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show n

    freeVars (LVar n)          = [n]
    freeVars (LAbst n _ :@: t) = delete n (nub (freeVars t))
    freeVars (l :@: r)         = freeVars l ++ freeVars r
    freeVars (LAbst n _)       = error $ "CombLambda>>freeVars: Lonely Abstraction " ++ show n


-----------------------------------------------------------------------------
-- ** Priniting and parsing

instance PP (LTerm VarString Untyped) where
    pp t = pp' True True [] t
    pparser = parseTerm Nothing

instance PP (LTerm VarInt Untyped) where
    pp = pp . fromLambdaB
    pparser = liftM toLambdaB (parseTerm Nothing)

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
-- The first Boolean value is true if it is a left subterm.
-- The second Boolean Term is true, if it  is a right most subterm
--    (which is closed with brackets anyway)
pp' :: Bool -> Bool -> [VarString] -> LTerm VarString Untyped -> PP.Doc
pp' _ _ _ (LVar v)                          = PP.text (varPp v)
pp' il rm l ((LAbst v _) :@: ((LAbst v' _) :@: t'))
                                            = pp' il rm (v : l) ((LAbst v' Untyped) :@: t')
pp' il False l ((LAbst v _) :@: t)          = {-PP.parens $-} pp' il True l ((LAbst v Untyped) :@: t)
pp' _ True l ((LAbst v _) :@: t)            = PP.parens $ PP.fcat [PP.text "\\",
                                                PP.fsep (map (PP.text .varPp) (reverse (v:l))),
                                                PP.text ".", pp' True True [] t]
pp' True rm _ (l :@: r)                     = PP.fsep [pp' True False [] l, pp' False rm [] r]
pp' False _ _ (l :@: r)                     = PP.parens (pp' True True [] (l :@: r))
pp' _ _ _ (LAbst _ _)                         = error "Lambda>>pp': Lonely LAbst"


parseTerm :: Maybe (LTerm VarString Untyped) -> Parser (LTerm VarString Untyped)
parseTerm Nothing = do
    PA.spaces
    do
        t <- parsePart
        PA.option t $ PA.try (parseTerm (Just t))
    PA.<?> "parseTerm Nothing"
parseTerm (Just l) = do
    PA.spaces
    do
        t <- parsePart
        PA.option (l :@: t) $ PA.try (parseTerm (Just (l :@: t)))
    PA.<?> "parseTerm Just"

parsePart :: Parser (LTerm VarString Untyped)
parsePart = do
    PA.spaces
    do
        parens' (parseTerm Nothing)
    PA.<|> do
        symbol' "\\"
        vl <- PA.many1 varParse
        dot'
        t <- parseTerm Nothing
        return (foldr ((:@:) . flip LAbst Untyped) t vl)
    PA.<|> do
        v <- varParse
        return (LVar v)

    PA.<?> "parsePart Nothing"

-----------------------------------------------------------------------------
-- ** Properties


-- | Returns a list of bound Vars in the term
boundVars :: LTerm VarString t -> [VarString]
boundVars (LVar _n)         = []
boundVars (LAbst n _ :@: t) = n : boundVars t
boundVars (l :@: r)         = boundVars l ++ boundVars r
boundVars (LAbst n _)       = error $ "CombLambda>>freeVars: Lonely Abstraction " ++ show n

-- | Is this a closed term, which means it has no free variables?
isClosed :: LTerm VarString t -> Bool
isClosed = null . freeVars

-- | Give canonical variable names for a term
canonicalizeLambda :: LTerm VarString t -> LTerm VarString t
canonicalizeLambda t =
    let fvs = freeVars t
        env = zip fvs (map negate [0..])
    in (\(_,_,r) -> r) $ canonicalizeLambda' (length fvs) env t

canonicalizeLambda' :: Int -> [(String,Int)] -> LTerm VarString t -> (Int, [(String,Int)], LTerm VarString t)
canonicalizeLambda' i env (LVar s) =
    case lookup s env of
        Just ind | ind >= 0   ->  (i,env,LVar (nameGen !! ind))
                 | otherwise ->  (i,env,LVar (nameGenFV !! negate ind))
        Nothing -> error ("Lambda>>canonicalizeLambda: Not closed, found: " ++ s)
canonicalizeLambda' i env (LAbst s t :@: r) =
    let (_i',_env',r') = canonicalizeLambda' (i+1) ((s,i):env) r
    in (i,env,(LAbst (nameGen !! i) t :@: r'))
canonicalizeLambda' i env (l :@: r) =
    let (i',env',l')   = canonicalizeLambda' i env l
        (i'',env'',r') = canonicalizeLambda' i' env' r
    in (i'',env'',l' :@: r')
canonicalizeLambda' _i _env (LAbst _s _) = error "Lambda>>canonicalizeLambda: Lonely Abst"

-- | Because of disappearing free vars during reduction two equal Lambda deBruijn representations can become
-- unequal if not canonicalized
canonicalizeLambdaB :: LTerm VarInt t -> LTerm VarInt t
canonicalizeLambdaB t = (\(_,_,t) -> t) $ canonicalizeLambdaB' 0 0 [] t
  where
    canonicalizeLambdaB' :: Int -> Int -> [(Int,Int)] -> LTerm VarInt t -> (Int,[(Int,Int)],LTerm VarInt t)
    canonicalizeLambdaB' fvIndex abstIndex env (LVar i) =
        case List.lookup (i - abstIndex) env of
            Just ni -> (fvIndex,env,LVar ni)
            Nothing -> (fvIndex+1,(i - abstIndex,fvIndex):env,LVar fvIndex)
    canonicalizeLambdaB' fvIndex abstIndex env (LAbst str ty :@: t) =
        let (fvIndex',env',newTerm) = canonicalizeLambdaB' fvIndex (abstIndex +1) env t
        in (fvIndex',env',LAbst str ty :@: newTerm)
    canonicalizeLambdaB' fvIndex abstIndex env (lt :@: rt) =
        let (fvIndex',env',lt') = canonicalizeLambdaB' fvIndex abstIndex env lt
            (fvIndex'',env'',rt') = canonicalizeLambdaB' fvIndex' abstIndex env' rt
        in (fvIndex'',env'',lt' :@: rt')
    canonicalizeLambdaB' _ _ _ (LAbst n _) =
        error $ "Lambda>>toLambdaB': Lonely Abstraction " ++ show n

arityLambda :: LTerm v t -> Int
arityLambda te@(LAbst _ _ :@: _t) = arityLambda' te
  where
    arityLambda' (LAbst _ _ :@: t) = 1 +  arityLambda' t
    arityLambda' _ = 0
arityLambda (l :@: _r) = arityLambda l - 1
arityLambda _ = 0

-----------------------------------------------------------------------------n
-- ** Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substitutel :: VarString -> LTerm VarString t -> LTerm VarString t -> LTerm VarString t
substitutel var replace (LVar v) | v == var          = replace
                                 | otherwise        = LVar v
substitutel var replace (LAbst v ty :@: t) | v == var = LAbst v ty :@: t
                                        | otherwise = LAbst v ty :@: substitutel var replace t
substitutel var replace (x :@: y)                   = substitutel var replace x :@: substitutel var replace y
substitutel _ _ (LAbst _ _)                         = error "Lambda>>substitutel: Lonely LAbst"

-- | Substitution with alpha conversion
subsititueAlpha  :: Show t => VarString -> LTerm VarString t -> LTerm VarString t -> LTerm VarString t
subsititueAlpha  var replace replaceIn =
    let freeVars'    = nub $ freeVars replace
        boundVars'   = nub $ boundVars replaceIn
        renamingVars = List.nub $ List.intersect freeVars' boundVars'
        newVarNames  = foldr (findNewName 0) [] renamingVars
        replacePairs = zip renamingVars newVarNames
        replaceIn'   = foldr (renameBoundVar False) replaceIn replacePairs
        res          = substitutel var replace replaceIn'
    in res
  where
    findNewName :: Int -> VarString -> [VarString] -> [VarString]
    findNewName ind var accu =
        let proposedVariable =  varPp var ++ show ind
        in if List.elem proposedVariable accu ||
                occurs proposedVariable replace ||
                occurs proposedVariable replaceIn
                then findNewName (ind+1) var accu
                else proposedVariable : accu

renameBoundVar :: Show t => Bool -> (VarString,VarString) ->  LTerm VarString t -> LTerm VarString t
renameBoundVar ib (old,new)(LVar n) | n == old && ib  = LVar new
                                     | otherwise     = LVar n
renameBoundVar ib (old,new)(LAbst n ty :@: t) | n == old
                                                = LAbst new ty :@: renameBoundVar True (old,new) t
                                 | otherwise    = LAbst n ty :@: renameBoundVar ib (old,new) t
renameBoundVar ib (old,new) (l :@: r)               = renameBoundVar ib (old,new) l
                                                  :@: renameBoundVar ib (old,new) r
renameBoundVar _ (_old,_new) (LAbst n _ty)         = error $ "CombLambda>>renameFreeVar: Lonely Abstraction " ++ show n

-----------------------------------------------------------------------------
-- ** Reduction

instance (Strategy s, ReductionContext c (LTerm VarString t), Show t)  => Reduction (LTerm VarString t) s c where
    reduceOnce' s zipper =
        case zipSelected zipper of
            (((LAbst v _) :@: b) :@: c)
                | LVar v == c  && not (elem v (freeVars b)) -> return (Just $ zipper {zipSelected = b})
                                --eta redex
                | otherwise  -> return (Just $ zipper {zipSelected = subsititueAlpha v c b})
                                --beta redex, may need alpha conversion
            (LAbst x ty) :@: _t -> do
                r <- reduceOnce' s (fromJust $ zipDownRight zipper)
                case r of
                    Just t' -> return (Just $ zipper {zipSelected = (LAbst x ty) :@: zipSelected t'})
                    Nothing -> return Nothing
            tl :@: tr -> do
                r1 <- reduceOnce' s (fromJust $ zipDownLeft zipper)
                case r1 of
                    Just tl' -> return (Just $ zipper {zipSelected = zipSelected tl' :@: tr})
                    Nothing -> do
                        r2 <- reduceOnce' s  (fromJust $ zipDownRight zipper)
                        case r2 of
                            Nothing -> return Nothing
                            Just tr' -> return (Just $ zipper {zipSelected = tl :@: zipSelected tr'})
            (LVar _) -> return $ Nothing
            (LAbst _ _) -> error $ "Lambda>>reduceOnce': Lonely Abstraction "

-----------------------------------------------------------------------------
-- ** Convenience

-- | Takes a string, parses it, applies normalOrderReduction and prints the result.
reduceLambda :: String -> String
reduceLambda = show . pp . reduceSForce . (pparse :: String -> LTerm VarInt Untyped)

-----------------------------------------------------------------------------
-- ** With de Bruijn indices

toLambdaB :: LTerm VarString t -> LTerm VarInt t
toLambdaB t =
    let fvs = freeVars t
    in toLambdaB' fvs t
  where
    toLambdaB' :: [String] -> LTerm VarString t -> LTerm VarInt t
    toLambdaB' env (LVar str)           = case List.elemIndex str env of
                                                    Just i -> (LVar i)
                                                    Nothing -> error ""
    toLambdaB' env (LAbst str ty :@: t) = let newTerm = toLambdaB' (str:env) t
                                                in LAbst str ty :@: newTerm
    toLambdaB' env (lt :@: rt)          = toLambdaB' env lt :@:
                                                toLambdaB' env rt
    toLambdaB' _ (LAbst n _)            = error $ "Lambda>>toLambdaB': Lonely Abstraction " ++ show n

fromLambdaB :: LTerm VarInt t -> LTerm VarString t
fromLambdaB = fromLambdaB' []
  where
    fromLambdaB' env (LVar ind)        = case env !!! ind of
                                            Just s -> LVar s
                                            Nothing -> if ind < 0
                                                            then LVar "grook"
                                                            else LVar (nameGenFV !! (ind - length env))
    fromLambdaB' env (LAbst str ty :@: t) =
        if elem str env
            then let newName = findNewName str env (0:: Int)
                 in LAbst newName ty :@: fromLambdaB' (newName:env) t
            else LAbst str ty :@: fromLambdaB' (str:env) t
      where
        findNewName str env n =
            if elem (str ++ show n) env
                then findNewName str env (n+1)
                else (str ++ show n)
    fromLambdaB' env (lt :@: rt)       = fromLambdaB' env lt :@: fromLambdaB' env rt
    fromLambdaB' _env (LAbst n _)        = error $ "Lambda>>toLambdaB': Lonely Abstraction " ++ show n



(!!!)                :: [a] -> Int -> Maybe a
_      !!! n | n < 0 =  Nothing
[]     !!! _         =  Nothing
(x:_)  !!! 0         =  Just x
(_:xs) !!! n         =  xs !!! (n-1)

-----------------------------------------------------------------------------
-- ** Reduction de Bruijn

isFreeVar :: Int -> LTerm VarInt t -> Bool
isFreeVar c (LVar i)              = i == c
isFreeVar c (LAbst _str _ :@: t)  = isFreeVar (c+1) t
isFreeVar c (l :@: r)             = isFreeVar c l || isFreeVar c r
isFreeVar _c (LAbst n _)          = error $ "Lambda>>isFreeVar: Lonely Abstraction " ++ show n

termShift :: Int -> LTerm VarInt t -> LTerm VarInt t
termShift d t = walk 0 t
  where
    walk c (LVar i) | i >= c       = LVar (i+d)
                    | otherwise   = LVar i
    walk c (LAbst str ty :@: t)   = LAbst str ty :@: walk (c+1) t
    walk c (l :@: r)              = walk c l :@: walk c r
    walk _c (LAbst n _)           = error $ "Lambda>>termShift: Lonely Abstraction " ++ show n

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substituteb :: VarInt -> LTerm VarInt t -> LTerm VarInt t -> LTerm VarInt t
substituteb var replace t = walk 0 t
  where
    walk c (LVar v) | v == var + c  = termShift c replace
                    | otherwise    = LVar v
    walk c (LAbst v ty :@: t)      = LAbst v ty :@: walk (c+1) t
    walk c (x :@: y)               = walk c x :@: walk c y
    walk _c (LAbst _ _)            = error "Lambda>>substituteb: Lonely LAbst"

substituteTop :: LTerm VarInt t -> LTerm VarInt t -> LTerm VarInt t
substituteTop s t = termShift (-1) (substituteb 0 (termShift 1 s) t)

instance (Strategy s, ReductionContext c (LTerm VarInt t))  => Reduction (LTerm VarInt t) s c where
    reduceOnce' s zipper =
        case zipSelected zipper of
            (((LAbst _ _) :@: b) :@: c) ->
                case c of
                    LVar 0 | not (isFreeVar 0 b)
                        -> return (Just $ zipper {zipSelected = termShift (-1) b})
                            -- eta redex
                    _   -> return (Just $ zipper {zipSelected = substituteTop c b})
                            -- beta redex
            (LAbst x ty) :@: _t -> do
                r <- reduceOnce' s (fromJust $ zipDownRight zipper)
                case r of
                    Just t' -> return (Just $ zipper {zipSelected = (LAbst x ty) :@: zipSelected t'})
                    Nothing -> return Nothing
            tl :@: tr -> do
                r1 <- reduceOnce' s (fromJust $ zipDownLeft zipper)
                case r1 of
                    Just tl' -> return (Just $ zipper {zipSelected = zipSelected tl' :@: tr})
                    Nothing -> do
                        r2 <- reduceOnce' s  (fromJust $ zipDownRight zipper)
                        case r2 of
                            Nothing -> return Nothing
                            Just tr' -> return (Just $ zipper {zipSelected = tl :@: zipSelected tr'})
            (LVar _) -> return $ Nothing
            (LAbst _ _ ) -> error $ "Lambda>>reduceOnce': Lonely Abstraction "

