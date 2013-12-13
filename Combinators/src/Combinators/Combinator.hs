{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Combinatory logic implementation inspired by Katalin Bimbo's book.
--
-----------------------------------------------------------------------------

module Combinators.Combinator (
-----------------------------------------------------------------------------
-- * Basic types
    CTerm(..),
    Basis(..),
    Combinator(..),
    primArity,
-----------------------------------------------------------------------------
-- * Basis
-- ** IKS
    KS,
    kKS,
    sKS,
    parseKS,
-----------------------------------------------------------------------------
-- * Priniting and parsing
    pp,
    pprint,
    parse,
    parseErr,
-----------------------------------------------------------------------------
-- * Subterms
    subterm,
    allSubterms,
-----------------------------------------------------------------------------
-- * Substitution
    substitute,
    leftAssociated,
    isApp,
-----------------------------------------------------------------------------
-- * Reduction
    Redex,
    redex,
    isRedex,
-----------------------------------------------------------------------------
-- * Convenience
    normalOrderReduction,
--    strReduction,

 ) where

import Combinators.Variable
import Combinators.BinaryTree
import Combinators.Reduction

import Data.List (nub)
import Data.Maybe (fromJust, isJust)
import Control.Monad (liftM)

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
import Debug.Trace (trace)


-----------------------------------------------------------------------------
-- * Basic types

-- | A 'Term' in combinatory logic is either
--
-- * a primitive combinator
-- * a variable
-- * an application
--
-- Two problems here:
-- * How to represent a combinatory Basis?
--     we choose to parametrize on the type of basis, which is a something of class Basis
--
-- * How to represent variables? Do we prefer Strings or de Bruijn?
--      we choose to parametrize on the type of variables, which is a something of class Variable

data CTerm basis v where
    Const :: (Variable v, Basis basis v) => ! (Combinator basis v) -> CTerm basis v
    Var :: ! v -> CTerm basis v
    (:@) :: ! (CTerm basis v) -> ! (CTerm basis v) -> CTerm basis v

deriving instance Eq v => Eq (CTerm basis v)
deriving instance Show v => Show (CTerm basis v)

instance (Variable v, Basis basis v) => BinaryTree (CTerm basis v) where
    decompose (tl :@ tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@ tr

instance (Variable v, Basis basis v) => Term (CTerm basis v) where
    isTerminal (Var _)          = True
    isTerminal (Const _)        = True
    isTerminal _                = False


-- | A 'Basis' defines the primitive combinators.
--
-- We might add here bracket abstraction?
class (Variable v) => Basis basis v where
    primCombs :: [Combinator basis v]

-- | A (primitive) combinator belongs to a Basis.
--
-- it has
--
--  * a name
--
--  * an axiom, represented by
--
--
--      * a list of variables, representing the arguments
--
--      * a term, in which the variables will be replaced
--
data Combinator basis v where
    Combinator :: (Basis basis v, Variable v) =>
        {combName   :: ! String, -- ^ needs to start with upper case character
         combVars   :: ! [v],
         combReduct :: ! (CTerm basis v)} -> Combinator basis v

deriving instance Eq (Combinator basis v)

instance Show (Combinator basis v) where
    show = combName

-- | The arity of a primitive combinator is defined by the length
-- of the variables in its axiom
primArity :: Combinator basis v -> Int
primArity = length . combVars

-----------------------------------------------------------------------------
-- * Basis

-- ** IKS

-- | A combinatory Basis is represented purely as a type.
-- It has no data constructors, so can never be instantiated.
--
-- This is the Basis with combinators I, K, S
--

data KS

-- | Definition of the combinators for the IKS Basis
kKS, sKS :: Variable v => Combinator KS v
kKS = Combinator "K" [varString "u", varString "v"] (Var (varString "u"))
sKS = Combinator "S" [varString "u", varString "v", varString"w"]
            (Var (varString "u") :@ Var (varString"w") :@
            (Var (varString "v") :@ Var (varString "w")))

instance Variable v => Basis KS v where
    primCombs = [kKS,sKS]

parseKS :: String -> CTerm KS VarString
parseKS = parse

-----------------------------------------------------------------------------
-- * Variables
-----------------------------------------------------------------------------
-- * Priniting and parsing

instance Basis basis v => PP (CTerm basis v) where
    pp = ppC

-- | Pretty prints a term.
--
-- Avoids printing outer parenthesis and left parenthesis.
ppC :: Basis basis v => CTerm basis v -> String
ppC t = PP.render (pp' False t)

pp' :: Basis basis v => Bool -> CTerm basis v -> PP.Doc
pp' _ (Const c)     = PP.text (combName c)
pp' _ (Var v)       = PP.text (varPp v)
pp' False (l :@ r)  = PP.sep [pp' False l, pp' True r]
pp' True (l :@ r)   = PP.text "("  PP.<> PP.sep [pp' False l, pp' True r] PP.<> PP.text ")"

pprint :: Basis basis v => CTerm basis v -> String
pprint = pprint' False

pprint' :: Basis basis v => Bool -> CTerm basis v -> String
pprint' _ (Const c)     = combName c
pprint' _ (Var v)       = varPp v
pprint' False (l :@ r)  = pprint' False l ++ " " ++  pprint' True r
pprint' True (l :@ r)   = "("  ++ pprint' False l ++ " " ++  pprint' True r ++ ")"


-- | Takes a String and returns a Term
--
-- Throws an error, when the String can't be parsed
parse ::  Basis b v => String -> CTerm b v
parse str = case parse' str of
                Left err    -> error (show err)
                Right term  -> term

parseErr ::  Basis b v => String -> Either String (CTerm b v)
parseErr str = case parse' str of
                Left err    -> Left (show err)
                Right term  -> Right term




parse' :: Basis b v => String -> Either PA.ParseError (CTerm b v)
parse' = PA.parse (parseTerm Nothing) ""

parseComb, parsePrim, parseVar
    :: (Basis basis v) => Parser (CTerm basis v)
parseComb = do
    start <- PA.upper
    rest  <- PA.many (PA.noneOf " ()\t\n\r\f\v")
    case filter (\pc -> combName pc == start:rest) primCombs of
                [c] -> return (Const c)
                _ -> PA.unexpected $ "unknown primitive combinator: " ++ start:rest
    PA.<?> "parseComb"

parseVar = liftM Var varParse

parsePrim = parseVar PA.<|> parseComb PA.<?> "parsePrim"

parseTerm, parseTerm' :: (Basis basis v) => Maybe (CTerm basis v)
                                        -> Parser (CTerm basis v)
parseTerm condL = do
    PA.spaces
    parseTerm' condL

parseLeft :: (Basis basis v) => Parser (CTerm basis v)
parseLeft = do
    PA.char '('
    t <- parseTerm Nothing
    PA.spaces
    PA.char ')'
    return t

parseTerm' Nothing =
    do
        t <- parseLeft
        PA.option t $ PA.try (parseTerm (Just t))
    PA.<|> do
        l <- parsePrim
        PA.option l $ PA.try (parseTerm (Just l))
    PA.<?> "parseTerm' Nothing"

parseTerm' (Just l') =
    do
        t <- parseLeft
        PA.option (l' :@ t) $ PA.try (parseTerm (Just (l' :@ t)))
    PA.<|> do
        l <- parsePrim
        PA.option (l' :@ l) $ PA.try (parseTerm (Just (l' :@ l)))
    PA.<?> "parseTerm'"


-----------------------------------------------------------------------------
-- * Subterms

-- | Is the first term a subterm of the second
subterm :: Basis basis v => CTerm basis v -> CTerm basis v -> Bool
subterm (Var a1) (Var a2)     | a1 == a2 = True
                              | otherwise = False
subterm (Const a1) (Const a2) | a1 == a2 = True
                              | otherwise = False
subterm x (a1 :@ a2)          = x == (a1 :@ a2) || subterm x a1 || subterm x a2
subterm _x _y                 = False

-- | Returns all subterms of a term. Does not return duplicates
allSubterms :: Basis basis v => CTerm basis v -> [CTerm basis v]
allSubterms (Var a1) = [Var a1]
allSubterms (Const a1) = [Const a1]
allSubterms (a1 :@ a2) = (a1 :@ a2) : nub (allSubterms a1 ++ allSubterms a2)


-----------------------------------------------------------------------------
-- * Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--
-- Returns the resulting term.
substitute :: Basis basis v  => v -> CTerm basis v -> CTerm basis v -> CTerm basis v
substitute _var _replace (Const x) = Const x
substitute var replace (Var x) | x == var = replace
                               | otherwise = Var x
substitute var replace (x :@ y) = substitute var replace x :@ substitute var replace y

-- * Helpers

-- | Is this combinator left associated (can be written without parenthesis in standard notation)
leftAssociated :: (Basis basis v, Variable v) => CTerm basis v -> Bool
leftAssociated (Var _x) = True
leftAssociated (Const _x) = True
leftAssociated (x :@ y) = leftAssociated x && not (isApp y)

-- | Is this combinator an application
isApp :: Basis basis v => CTerm basis v -> Bool
isApp (_ :@ _) = True
isApp _ = False

-----------------------------------------------------------------------------
-- * Reduction

type Redex basis v = (Combinator basis v, [CTerm basis v])

-- | A term is a redex,  if
--      * the head is a primitive combinator
--      * the number of args are equal or greater then the arity of the primitive combinator
--
--   Returns just a pair of redexHead and redexArgs, when the term is an redex.
--   Returns Nothing, if the input term is not a redex
redex :: Basis basis v => CTerm basis v -> Maybe (Redex basis v)
redex = redex' []
  where
    redex' accu (Const c)
        | length accu  >= primArity c    = Just (c, accu)
        | otherwise                     = Nothing
    redex' _ (Var _)                    = Nothing
    redex' accu (l :@ arg)              = redex' (arg : accu) l

-- | Is this term an redex?
isRedex :: Basis basis v => CTerm basis v -> Bool
isRedex = isJust . redex

instance (Variable v, Basis basis v) => Reduction (CTerm basis v) HeadNormalForm NullContext where
    reduce' strategy zipper = do
        r <- reduceOnce' strategy zipper
        case r of
            Just zipper' ->  reduce' strategy zipper'
            Nothing -> return (Just zipper)
    reduceOnce'  = reduceOnce''

instance (Variable v, Basis basis v) => Reduction (CTerm basis v) NormalForm NullContext where
    reduce' strategy zipper = do
        r <- reduceOnce' strategy zipper
        case r of
            Just zipper' ->  trace ((pp . unzipper) zipper') $
                                reduce' strategy zipper'
            Nothing -> case goUp zipper of
                            Nothing -> return (Just zipper)
                            Just z ->  reduce' strategy z
    reduceOnce'  = reduceOnce''

reduceOnce'' :: (Basis basis v, Reduction (CTerm basis v) s c) =>
                    s -> BTZipper (CTerm basis v) -> c (Maybe (BTZipper (CTerm basis v)))
reduceOnce'' s zipper =
    case redex (zipSelected zipper) of
         Just redex ->  return (Just (applyCombinator (zipper,redex)))
         Nothing ->
            case zipSelected zipper of
                Const _ -> return Nothing
                Var _ -> return Nothing
                (l :@ r) -> do
                    r1 <- reduceOnce' s (fromJust $ zipDownLeft zipper)
                    case r1 of
                        Just l' -> return (Just $ zipper {zipSelected = zipSelected l' :@ r})
                        Nothing -> do
                            r2 <- reduceOnce' s (fromJust $ zipDownRight zipper)
                            case r2 of
                                Nothing -> return Nothing
                                Just r' -> return (Just $ zipper {zipSelected =  l :@ zipSelected r'})

-- | Apply the Combinator comb on the term list
applyCombinator :: Basis basis v =>
                (BTZipper (CTerm basis v), (Combinator basis v, [CTerm basis v]))
                -> BTZipper (CTerm basis v)
applyCombinator (zipper,(comb,args)) =
    let replaced = foldr (\ (var,arg) term -> substitute var arg term)
                            (combReduct comb)
                            (zip (combVars comb) args)
    in zipper {zipSelected = if length args == primArity comb
                                    then replaced
                                    else foldl (:@) replaced (drop (primArity comb) args)}

-----------------------------------------------------------------------------
-- * Convenience

-- | Normal order reduction for a term.
--
--  This is not guaranteed to terminate.
normalOrderReduction :: Basis basis v => CTerm basis v -> CTerm basis v
normalOrderReduction = reduceIt nullContext NormalForm

--
---- | Takes a string, parses it, applies normalOrderReduction and prints the result.
--strReduction :: String -> String
--strReduction = pp . normalOrderReduction . parseKS

