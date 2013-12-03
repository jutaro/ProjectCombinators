{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-orphans #-}
{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, StandaloneDeriving, GADTs #-}
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
    IKS,
    iIKS,
    kIKS,
    sIKS,
-----------------------------------------------------------------------------
-- * Priniting and parsing
    pp,
    pprint,
    parse,
    parseErr,
    parseIKS,
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
-- * Head Reduction
    Redex,
    redex,
    isRedex,
    oneStepHeadReduction,
    weakHeadReduction,
-----------------------------------------------------------------------------
-- * Normal order reduction
    normalOrderStrategy,
    applyStrategy,
    applyCombinator,
    normalOrderReduction,
    strReduction,

 ) where

import Combinators.Variable
import Combinators.Term

import Data.List (nub)
import Data.Maybe (isJust)
import Control.Monad (liftM)

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA


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
        -- ^ Bind application to the left.

deriving instance Eq v => Eq (CTerm basis v)
deriving instance Show v => Show (CTerm basis v)

instance (Variable v, Basis basis v) => BinaryTree (CTerm basis v) where
    decompose (tl :@ tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@ tr

-- Bind application to the left.
infixl 5 :@

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

data IKS

-- | Definition of the combinators for the IKS Basis
iIKS, kIKS, sIKS :: Variable v => Combinator IKS v
iIKS = Combinator "I" [varString "__x"] (Var (varString "__x"))
kIKS = Combinator "K" [varString "__x", varString "__y"] (Var (varString "__x"))
sIKS = Combinator "S" [varString "__x", varString "__y", varString"__z"]
            (Var (varString "__x") :@ Var (varString"__z") :@
            (Var (varString "__y") :@ Var (varString "__z")))


instance Variable v => Basis IKS v where
    primCombs = [iIKS,kIKS,sIKS]

-----------------------------------------------------------------------------
-- * Variables
-----------------------------------------------------------------------------
-- * Priniting and parsing

-- | Pretty prints a term.
--
-- Avoids printing outer parenthesis and left parenthesis.
pp :: Basis basis v => CTerm basis v -> String
pp t = PP.render (pp' False t)

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



parseIKS :: String -> CTerm IKS VarString
parseIKS = parse :: String -> CTerm IKS VarString

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
-- * Head Reduction

-- ** Simple

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

-- | This is the precursor to reduction with strategies, and thus obsolete
-- | A "Left" term is returned if reduction has changed the term, else a "Right" term.
oneStepHeadReduction :: (Variable v, Basis basis v)
                            => CTerm basis v -> Either (CTerm basis v) (CTerm basis v)
oneStepHeadReduction term =
    case redex term of
        Just (comb,args) ->  let replaced = foldr (\ (var,arg) term' -> substitute var arg term')
                                                    (combReduct comb)
                                            (zip (combVars comb) args)
                            in Left (if length args == primArity comb
                                        then replaced
                                        else foldl (:@) replaced (drop (primArity comb) args))
        Nothing -> Right term

-- | This is the precursor to reduction with strategies, and thus obsolete
-- | Reducing a head redex repeatedly, until it does not change any more.
--
--  This is not guaranteed to terminate.
weakHeadReduction :: Basis basis v => CTerm basis v -> CTerm basis v
weakHeadReduction t =
    case oneStepHeadReduction t of
        Left t' -> {-trace (show t) $-} weakHeadReduction t'
        Right t' -> t'




-----------------------------------------------------------------------------
-- * Normal order reduction

-- | A strategy takes a 'TermZipper', and returns 'Just' a 'TermZipper',
-- when it finds a new position.
--
-- Otherwise return 'Nothing'

instance (Variable v, Basis basis v) => Term (CTerm basis v) where
    reduceOnce' strategy zipper =
        case applyStrategy strategy zipper of
            Just (zipper',redex) -> Left (applyCombinator (zipper',redex))
            Nothing -> Right zipper
    -- ^ One step reduction. Returns Left t if possible, or Right t with the original term,
    --   if no reduction was possible
    isTerminal (Var _)          = True
    isTerminal (Const _)        = True
    isTerminal _                = False


-- | Applying a strategy means to test if a redex is at the current position.
-- If the current position has no redex, apply the strategy to select a new position,
-- and retry if its a redex.
applyStrategy :: (Variable v, Basis basis v) =>
         Strategy (CTerm basis v) ->  TermZipper (CTerm basis v) ->
            Maybe (TermZipper (CTerm basis v), Redex basis v)
applyStrategy strategy zipper =
    case redex (zipSelected zipper) of
         Just r ->  Just (zipper,r)
         Nothing -> case strategy zipper of
            Nothing -> Nothing
            Just zipper' -> applyStrategy strategy zipper'



-- | Apply the Combinator comb on the term list
applyCombinator :: Basis basis v =>
                (TermZipper (CTerm basis v), (Combinator basis v, [CTerm basis v]))
                -> TermZipper (CTerm basis v)
applyCombinator (zipper',(comb,args)) =
    let replaced = foldr (\ (var,arg) term -> substitute var arg term)
                            (combReduct comb)
                            (zip (combVars comb) args)
    in zipper' {zipSelected = if length args == primArity comb
                                    then replaced
                                    else foldl (:@) replaced (drop (primArity comb) args)}


-- | Normal order reduction for a term.
--
--  This is not guaranteed to terminate.
normalOrderReduction :: (Show v, Basis basis v) => CTerm basis v -> CTerm basis v
normalOrderReduction = reduceIt normalOrderStrategy

-- | Takes a string, parses it, applies normalOrderReduction and prints the result.
strReduction :: String -> String
strReduction = pp . normalOrderReduction . parseIKS
