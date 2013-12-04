{-# LANGUAGE FlexibleInstances, GADTs, StandaloneDeriving, FlexibleContexts #-}
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
-- | Lambda calculus implementation
--
-----------------------------------------------------------------------------

module Combinators.Lambda (
    LTerm(..),
    parseLambda,
    reduceLambda,
    occurs,
    freeVars,
    isClosed
) where

import Combinators.Variable
import Combinators.Term

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
import Data.List (delete)

-----------------------------------------------------------------------------
-- * Basic types

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
deriving instance Show (LTerm v)

instance Variable v => BinaryTree (LTerm v) where
    decompose (tl :@: tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@: tr

-- Bind application to the left.
infixl 5 :@:

-----------------------------------------------------------------------------
-- * Priniting and parsing

instance Variable v => PP (LTerm v) where
    pp = ppl

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
ppl :: Variable v => LTerm v -> String
ppl t = PP.render (pp' True True [] t)

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
parseLambda = parse

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
-- * Properties

-- | The substitution of a variable "var" with a term "replace" in the matched term
--   Returns the resulting term.
substitutel :: v -> LTerm v -> LTerm v -> LTerm v
substitutel var n (LVar v) | v == var          = n
                           | otherwise        = LVar v
substitutel var n (LAbst v :@: t) | v == var   = LAbst v :@: t
                                  | otherwise = LAbst v :@: substitutel var n t
substitutel var n (x :@: y)                   = substitutel var n x :@: substitutel var n y
substitutel _ _ (LAbst _)                     = error "Lambda>>substitutel: Lonely LAbst"

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
-- * Reduction

-- | Type, which means (\\v.t1) t2
type Redex v = (v,LTerm v, LTerm v)

-- | Returns a redex, if the given term matches
redex :: LTerm v -> Maybe (Redex v)
redex (((LAbst v) :@: b) :@: c) = Just (v,b,c)
redex _ = Nothing


instance Variable v => Term (LTerm v) where
    reduceOnce' strategy zipper = {- trace ("reduceOnce'" ++ show (zipSelected zipper)) $ -}
        case applyStrategy strategy zipper of
            Just (zipper',redex) -> Left (reduceBeta zipper' redex)
            Nothing -> Right zipper

    isTerminal (LVar _)         = True
    isTerminal (LAbst _)        = True
    isTerminal (LVar _ :@: _r)  = True
    isTerminal (LAbst _ :@: _r) = True
    isTerminal _                = False

    -- ^ One step reduction. Returns Left t if possible, or Right t with the original term,
    --   if no reduction was possible

-- | Applying a strategy means to test if a redex is at the current position.
-- If the current position has no redex, use the strategy to select a new position,
-- and retry if its a redex.
applyStrategy :: Strategy (LTerm v) ->  TermZipper (LTerm v) ->
            Maybe (TermZipper (LTerm v), Redex v)
applyStrategy strategy zipper =
    case redex (zipSelected zipper) of
         Just r ->  Just (zipper,r)
         Nothing -> case strategy zipper of
            Nothing -> Nothing
            Just zipper' -> applyStrategy strategy zipper'


reduceBeta :: TermZipper (LTerm v) -> Redex v -> TermZipper (LTerm v)
reduceBeta tz (v,b,c) = tz{zipSelected=substitutel v c b}


-- | Takes a string, parses it, applies normalOrderReduction and prints the result.
reduceLambda :: String -> String
reduceLambda = pp . reduceIt normalOrder . parseLambda

-----------------------------------------------------------------------------
-- * Substitution

