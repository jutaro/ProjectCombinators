{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving, FlexibleContexts, MultiParamTypeClasses,
      ScopedTypeVariables #-}
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

module Combinators.Lambda (
-----------------------------------------------------------------------------
-- * Lambda calculus implementation
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- ** LTerm type
    LTerm(..),
-----------------------------------------------------------------------------
-- ** Priniting and parsing
    parseLambda,
    parseLambdaB,
-----------------------------------------------------------------------------
-- ** Properties
    occurs,
    freeVars,
    isClosed,
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

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
import Data.List (delete)
import Data.Maybe (fromJust)
import qualified Data.List as List
       (elemIndex, elem, intersect, nub)
import Debug.Trace (trace)

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
-- Abstractions are used together with a pseudo application, to make a term a natural instance
-- of a binary tree, with the burden always to handle the error case of a lonely abstration

data LTerm v where
      LVar ::  Variable v => v -> LTerm v
      LAbst :: VarString -> LTerm v
      (:@:) :: Variable v => LTerm v -> LTerm v -> LTerm v

deriving instance Show (LTerm v)

deriving instance Eq (LTerm VarInt)

instance Eq (LTerm VarString) where
    a == b = toLambdaB a == toLambdaB b

deriving instance Ord (LTerm VarInt)

instance Ord (LTerm VarString) where
    a `compare` b = toLambdaB a `compare` toLambdaB b

instance Variable v => BinaryTree (LTerm v) where
    decompose (tl :@: tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@: tr

-- Bind application to the left.
infixl 5 :@:

instance Variable v => Term (LTerm v) where
    isTerminal (LVar _)         = True
    isTerminal (LAbst _)        = True
    isTerminal (LVar _ :@: _r)  = True
    isTerminal (LAbst _ :@: _r) = True
    isTerminal _                = False
-----------------------------------------------------------------------------
-- ** Priniting and parsing

instance PP (LTerm VarString) where
    pp = pp' True True []

instance PP (LTerm VarInt) where
    pp = pp . fromLambdaB

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
--ppl :: Variable v => LTerm v -> String
--ppl t = PP.render (pp' True True [] t)

-- | The first Boolean value is true if it is a left subterm.
-- The second Boolean Term is true, if it  is a right most subterm
--    (which is closed with brackets anyway)
pp' :: Bool -> Bool -> [VarString] -> LTerm VarString -> PP.Doc
pp' _ _ _ (LVar v)                          = PP.text (varPp v)
pp' il rm l ((LAbst v) :@: ((LAbst v') :@: t'))
                                            = pp' il rm (v : l) ((LAbst v') :@: t')
pp' il False l ((LAbst v) :@: t)            = PP.parens $ pp' il True l ((LAbst v) :@: t)
pp' _ True l ((LAbst v) :@: t)              = PP.fcat [PP.text "\\",
                                                PP.fsep (map (PP.text .varPp) (reverse (v:l))),
                                                PP.text ".", pp' True True [] t]
pp' True rm _ (l :@: r)                     = PP.fsep [pp' True False [] l, pp' False rm [] r]
pp' False _ _ (l :@: r)                     = PP.parens (pp' True True [] (l :@: r))
pp' _ _ _ (LAbst _)                         = error "Lambda>>pp': Lonely LAbst"

-- | Takes a String and returns a Term
--
parseLambda :: String -> LTerm VarString
parseLambda str = let res = parse str
                  in -- trace (show res)
                        res

parseLambdaB :: String -> LTerm VarInt
parseLambdaB str = let res = parse str
                  in -- trace (show res)
                        toLambdaB res


-- | Throws an error, when the String can't be parsed
parse ::  String -> LTerm VarString
parse str = case parse' str of
                Left err    -> error (show err)
                Right term  -> term

parse' :: String -> Either PA.ParseError (LTerm VarString)
parse' = PA.parse (parseTerm Nothing) ""

parseTerm :: Maybe (LTerm VarString) -> Parser (LTerm VarString)
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

parsePart :: Parser (LTerm VarString)
parsePart = do
    PA.spaces
    do
        PA.char '('
        l <- parseTerm Nothing
        PA.spaces
        PA.char ')'
        return l
    PA.<|> do
        PA.char '\\'
        PA.spaces
        vl <- PA.many1 varParse
        PA.spaces
        PA.char '.'
        t <- parseTerm Nothing
        return (foldr ((:@:) . LAbst) t vl)
    PA.<|> do
        v <- varParse
        return (LVar v)

    PA.<?> "parsePart Nothing"

-----------------------------------------------------------------------------
-- ** Properties

-- | Does variable v occurst in the term?
occurs :: VarString -> LTerm VarString -> Bool
occurs v (LVar n)                    = v == n
occurs v (LAbst n :@: t) | v == n    = False
                         | otherwise = occurs v t
occurs v (l :@: r)                   = occurs v l || occurs v r
occurs _v (LAbst n)                  = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show n

freeVars :: LTerm VarString -> [VarString]
freeVars (LVar n)        = [n]
freeVars (LAbst n :@: t) = delete n (freeVars t)
freeVars (l :@: r)       = freeVars l ++ freeVars r
freeVars (LAbst n)       = error $ "CombLambda>>freeVars: Lonely Abstraction " ++ show n

boundVars :: LTerm VarString -> [VarString]
boundVars (LVar _n)       = []
boundVars (LAbst n :@: t) = n : boundVars t
boundVars (l :@: r)       = boundVars l ++ boundVars r
boundVars (LAbst n)       = error $ "CombLambda>>freeVars: Lonely Abstraction " ++ show n

isClosed :: LTerm VarString -> Bool
isClosed = null . freeVars

-----------------------------------------------------------------------------
-- ** Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substitutel :: VarString -> LTerm VarString -> LTerm VarString -> LTerm VarString
substitutel var replace (LVar v) | v == var          = replace
                                 | otherwise        = LVar v
substitutel var replace (LAbst v :@: t) | v == var   = LAbst v :@: t
                                        | otherwise = LAbst v :@: substitutel var replace t
substitutel var replace (x :@: y)                   = substitutel var replace x :@: substitutel var replace y
substitutel _ _ (LAbst _)                           = error "Lambda>>substitutel: Lonely LAbst"

-- | Substitution with alpha conversion
subsititueAlpha  :: VarString -> LTerm VarString -> LTerm VarString -> LTerm VarString
subsititueAlpha  var replace replaceIn =
    let freeVars'    = freeVars replace
        boundVars'   = boundVars replaceIn
        renamingVars = List.nub $ List.intersect freeVars' boundVars'
        newVarNames  = foldr (findNewName 0) [] renamingVars
        replaceIn'   = foldr (renameVar True) replaceIn (zip renamingVars newVarNames)
    in substitutel var replace replaceIn'
  where
    findNewName :: Int -> VarString -> [VarString] -> [VarString]
    findNewName ind var accu =
        let proposedVariable =  varPp var ++ show ind
        in if List.elem proposedVariable accu ||
                occurs proposedVariable replace ||
                occurs proposedVariable replaceIn
                then findNewName (ind+1) var accu
                else proposedVariable : accu

renameVar :: Bool -> (VarString,VarString) ->  LTerm VarString -> LTerm VarString
renameVar _b (old,new) (LVar n) | n == old         = LVar new
                                | otherwise       = LVar n
renameVar b (old,new) (LAbst n :@: t) | n == old && b
                                                  = LAbst new :@: renameVar False (old,new) t
                                      | otherwise = LAbst n :@: renameVar b (old,new) t
renameVar b (old,new) (l :@: r)                   = renameVar b (old,new) l :@: renameVar b (old,new) r
renameVar _b (_old,_new) (LAbst n)                = error $ "CombLambda>>renameVar: Lonely Abstraction " ++ show n

-----------------------------------------------------------------------------
-- ** Reduction

instance (Strategy s, ReductionContext c (LTerm VarString))  => Reduction (LTerm VarString) s c where
    reduceOnce' s zipper =
        case zipSelected zipper of
            (((LAbst v) :@: b) :@: c)
                | LVar v == c  && not (elem v (freeVars b)) -> return (Just $ zipper {zipSelected = b})
                                --eta redex
                | otherwise  -> return (Just $ zipper {zipSelected = subsititueAlpha v c b})
                                --beta redex, may need alpha conversion
            (LAbst x) :@: _t -> do
                r <- reduceOnce' s (fromJust $ zipDownRight zipper)
                case r of
                    Just t' -> return (Just $ zipper {zipSelected = (LAbst x) :@: zipSelected t'})
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
            (LAbst _ ) -> error $ "Lambda>>reduceOnce': Lonely Abstraction "

-----------------------------------------------------------------------------
-- ** Convenience

-- | Takes a string, parses it, applies normalOrderReduction and prints the result.
reduceLambda :: String -> String
reduceLambda = show . pp . reduceIt instrumentedContext NormalForm . parseLambda

-----------------------------------------------------------------------------
-- ** With de Bruijn indices

toLambdaB :: LTerm VarString -> LTerm VarInt
toLambdaB = fst . toLambdaB' [] []
  where
    toLambdaB' env fvEnv (LVar str)        =
                                case List.elemIndex str env of
                                    Just i -> (LVar i,fvEnv)
                                    Nothing -> case List.elemIndex str fvEnv of
                                                Just i -> (LVar (length env + i), fvEnv)
                                                Nothing -> let fvEnv' = fvEnv ++ [str]
                                                          in (LVar (length env + length fvEnv' - 1), fvEnv')
    toLambdaB' env fvEnv (LAbst str :@: t) =
                                let (newTerm,fvEnv') = toLambdaB' (str:env) fvEnv t
                                in (LAbst str :@: newTerm,fvEnv')
    toLambdaB' env fvEnv (lt :@: rt)       =
                                let (l',fvEnv')  = toLambdaB' env fvEnv lt
                                    (r',fvEnv'') = toLambdaB' env fvEnv' rt
                                in (l' :@: r', fvEnv'')
    toLambdaB' _env _fvEnv (LAbst n)       = error $ "Lambda>>toLambdaB': Lonely Abstraction " ++ show n

fromLambdaB :: LTerm VarInt -> LTerm VarString
fromLambdaB = fromLambdaB' []
  where
    fromLambdaB' env (LVar ind)        = case env !!! ind of
                                            Just s -> LVar s
                                            Nothing -> if ind < 0
                                                            then LVar "grook"
                                                            else LVar (nameGenFV !! (ind - length env))
    fromLambdaB' env (LAbst str :@: t) = LAbst str :@: fromLambdaB' (str:env) t
    fromLambdaB' env (lt :@: rt)       = fromLambdaB' env lt :@: fromLambdaB' env rt
    fromLambdaB' _env (LAbst n)        = error $ "Lambda>>toLambdaB': Lonely Abstraction " ++ show n

(!!!)                :: [a] -> Int -> Maybe a
_      !!! n | n < 0 =  Nothing
[]     !!! _         =  Nothing
(x:_)  !!! 0         =  Just x
(_:xs) !!! n         =  xs !!! (n-1)

-----------------------------------------------------------------------------
-- ** Reduction de Bruijn

isFreeVar :: Int -> LTerm VarInt -> Bool
isFreeVar c (LVar i)             = i == c
isFreeVar c (LAbst _str :@: t)   = isFreeVar (c+1) t
isFreeVar c (l :@: r)            = isFreeVar c l || isFreeVar c r
isFreeVar _c (LAbst n)           = error $ "Lambda>>isFreeVar: Lonely Abstraction " ++ show n

termShift :: Int -> LTerm VarInt -> LTerm VarInt
termShift d t = walk 0 t
  where
    walk c (LVar i) | i >= c     = LVar (i+d)
                    | otherwise = LVar i
    walk c (LAbst str :@: t)    = LAbst str :@: walk (c+1) t
    walk c (l :@: r)            = walk c l :@: walk c r
    walk _c (LAbst n)           = error $ "Lambda>>termShift: Lonely Abstraction " ++ show n

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substituteb :: VarInt -> LTerm VarInt -> LTerm VarInt -> LTerm VarInt
substituteb var replace t = walk 0 t
  where
    walk c (LVar v) | v == var + c  = termShift c replace
                    | otherwise    = LVar v
    walk c (LAbst v :@: t)         = LAbst v :@: walk (c+1) t
    walk c (x :@: y)               = walk c x :@: walk c y
    walk _c (LAbst _)              = error "Lambda>>substituteb: Lonely LAbst"

substituteTop :: LTerm VarInt -> LTerm VarInt -> LTerm VarInt
substituteTop s t = termShift (-1) (substituteb 0 (termShift 1 s) t)

instance (Strategy s, ReductionContext c (LTerm VarInt))  => Reduction (LTerm VarInt) s c where
    reduceOnce' s zipper =
        case zipSelected zipper of
            (((LAbst _) :@: b) :@: c) ->
                case c of
                    LVar 0 | not (isFreeVar 0 b)
                        -> trace "etaB" $ return (Just $ zipper {zipSelected = termShift (-1) b})
                            -- eta redex
                    _   -> return (Just $ zipper {zipSelected = substituteTop c b})
                            -- beta redex
            (LAbst x) :@: _t -> do
                r <- reduceOnce' s (fromJust $ zipDownRight zipper)
                case r of
                    Just t' -> return (Just $ zipper {zipSelected = (LAbst x) :@: zipSelected t'})
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
            (LAbst _ ) -> error $ "Lambda>>reduceOnce': Lonely Abstraction "

