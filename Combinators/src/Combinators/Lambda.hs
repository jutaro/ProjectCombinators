{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving, FlexibleContexts, MultiParamTypeClasses #-}
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
-----------------------------------------------------------------------------
-- ** Properties
    occurs,
    freeVars,
    isClosed,
-----------------------------------------------------------------------------
-- ** Convenience
    reduceLambda
) where

import Combinators.Variable
import Combinators.BinaryTree
import Combinators.Reduction

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
import Data.List (delete)
import Data.Maybe (fromJust)

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
-- Problems here:
-- * How to represent variables? Do we prefer Strings or de Bruijn?
--      we choose to parametrize on the type of variables, which is a something of class Variable

data LTerm v where
      LVar :: Variable v => v -> LTerm v
      LAbst :: Variable v => v -> LTerm v
      (:@:) :: Variable v => LTerm v -> LTerm v -> LTerm v

deriving instance Eq (LTerm v)
deriving instance Ord (LTerm v)
deriving instance Show (LTerm v)

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

instance Variable v => PP (LTerm v) where
    pp = pp' True True []

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
--ppl :: Variable v => LTerm v -> String
--ppl t = PP.render (pp' True True [] t)

-- | The first Boolean value is true if it is a left subterm.
-- The second Boolean Term is true, if it  is a right most subterm
--    (which is closed with brackets anyway)
pp' :: Bool -> Bool -> [v] -> LTerm v -> PP.Doc
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

-- | Throws an error, when the String can't be parsed
parse ::  Variable v => String -> LTerm v
parse str = case parse' str of
                Left err    -> error (show err)
                Right term  -> term

parse' :: Variable v => String -> Either PA.ParseError (LTerm v)
parse' = PA.parse (parseTerm Nothing) ""

parseTerm :: Variable v => Maybe (LTerm v) -> Parser (LTerm v)
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

parsePart :: Variable v => Parser (LTerm v)
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
occurs :: v -> LTerm v -> Bool
occurs v (LVar n) = v == n
occurs v (LAbst n :@: t) = if v == n then False else occurs n t
occurs v (l :@: r) = occurs v l || occurs v r
occurs _v (LAbst n) = error $ "CombLambda>>bracketAbstract: Lonely Abstraction " ++ show n

freeVars :: LTerm v -> [v]
freeVars (LVar n) = [n]
freeVars (LAbst n :@: t) = delete n (freeVars t)
freeVars (l :@: r) = freeVars l ++ freeVars r
freeVars (LAbst n) = error $ "CombLambda>>freeVars: Lonely Abstraction " ++ show n

isClosed :: LTerm v -> Bool
isClosed = null . freeVars

-----------------------------------------------------------------------------
-- ** Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substitutel :: v -> LTerm v -> LTerm v -> LTerm v
substitutel var replace (LVar v) | v == var          = replace
                                 | otherwise        = LVar v
substitutel var replace (LAbst v :@: t) | v == var   = LAbst v :@: t
                                        | otherwise = LAbst v :@: substitutel var replace t
substitutel var replace (x :@: y)                   = substitutel var replace x :@: substitutel var replace y
substitutel _ _ (LAbst _)                           = error "Lambda>>substitutel: Lonely LAbst"

-----------------------------------------------------------------------------
-- ** Reduction

instance (Strategy s, Variable v, ReductionContext c (LTerm v))  => Reduction (LTerm v) s c where
    reduceOnce' s zipper =
        case zipSelected zipper of
            (((LAbst v) :@: b) :@: c) | LVar v == c -> return (Just $ zipper {zipSelected = b})
                                --theta redex
                           | otherwise -> return (Just $ zipper {zipSelected = substitutel v c b})
                                --beta redex
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
reduceLambda = show . pp . reduceIt tracingContext HeadNormalForm . parseLambda



