{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-----------------------------------------------------------------------------

module Combinators.Combinator (
-----------------------------------------------------------------------------
-- * Combinatory logic
-----------------------------------------------------------------------------
-- ** Basic types
    CTerm(..),
    Basis(..),
    Combinator(..),
    primArity,
-----------------------------------------------------------------------------
-- ** Basis KS
    KS(..),
    k,
    s,
-----------------------------------------------------------------------------
-- ** Subterms
    subterm,
    allSubterms,
-----------------------------------------------------------------------------
-- ** Substitution
    substitute,
    leftAssociated,
    isApp,
-----------------------------------------------------------------------------
-- ** Reduction
    Redex,
    redex,
    isRedex,
-----------------------------------------------------------------------------
-- ** Convenience
    normalOrderReduction,
--    strReduction,

 ) where

import Combinators.Variable
import Combinators.BinaryTree
import Combinators.Reduction
import Combinators.Types

import Data.List (nub)
import Data.Maybe (fromJust, isJust)
import Control.Monad (liftM)

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
-- import Debug.Trace (trace)

-- (inspired by Katalin Bimbo's book).

-----------------------------------------------------------------------------
-- ** Basic types

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

data CTerm basis where
    Const :: Basis basis => ! (Combinator basis) -> CTerm basis
    Var   :: ! VarString -> CTerm basis
    (:@)  :: ! (CTerm basis) -> ! (CTerm basis) -> CTerm basis

deriving instance Eq (CTerm basis)
deriving instance Ord (CTerm basis)
deriving instance Show (CTerm basis)

instance Basis basis => BinaryTree (CTerm basis) where
    decompose (tl :@ tr) = Just (tl,tr)
    decompose _ = Nothing
    tl @@ tr = tl :@ tr

instance Basis basis => Term (CTerm basis) where
    isTerminal (Var _)          = True
    isTerminal (Const _)        = True
    isTerminal _                = False

instance Basis basis => TermString (CTerm basis) where
    occurs v (Var n)                      = v == n
    occurs v (l :@ r)                     = occurs v l || occurs v r
    occurs _v (Const _)                   = False

    freeVars (Var n)          = [n]
    freeVars (l :@ r)         = freeVars l ++ freeVars r
    freeVars (Const _)        = []

-- Bind application to the left.
infixl 5 :@


-- | A 'Basis' defines the primitive combinators.
--

class Basis basis where
    primCombs :: [Combinator basis]

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
data Combinator basis where
    Combinator :: (Basis basis) =>
        {combName   :: ! String, -- ^ needs to start with upper case character
         combVars   :: ! [VarString],
         combReduct :: ! (CTerm basis),
         combType   :: ! SType} -> Combinator basis

deriving instance Eq (Combinator basis)
deriving instance Ord (Combinator basis)

instance Show (Combinator basis) where
    show = combName

-- | The arity of a primitive combinator is defined by the length
-- of the variables in its axiom
primArity :: Combinator basis -> Int
primArity = length . combVars

-----------------------------------------------------------------------------
-- ** Basis

-- ** KS

-- | A combinatory Basis is represented purely as a type.
-- It has no data constructors, so can never be instantiated.
--
-- This is the Basis with combinators K, S
--

data KS = KS
k,s :: Basis b => Combinator b
k = Combinator "K" ["u#", "v#"] (Var ("u#"))
            (SAtom "a" :->: SAtom "b" :->: SAtom "a")
s = Combinator "S" ["u#", "v#", "w#"]
            (Var ("u#") :@ Var ("w#") :@
            (Var ("v#") :@ Var ("w#")))
            ((SAtom "a" :->: SAtom "b" :->: SAtom "c") :->: (SAtom "a" :->: SAtom "b") :->: SAtom "a" :->: SAtom "c")

-- | Definition of the combinators for the IKS Basis
instance Basis KS where
    primCombs = [k,s]


-----------------------------------------------------------------------------
-- ** Priniting and parsing

instance Basis basis => PP (CTerm basis) where
    pp = pp' False
    pparser = parseTerm Nothing

-- | Pretty prints a term.
--

pp' :: Basis basis => Bool -> CTerm basis -> PP.Doc
pp' _ (Const c)     = PP.text (combName c)
pp' _ (Var v)       = PP.text v
pp' False (l :@ r)  = PP.sep [pp' False l, pp' True r]
pp' True (l :@ r)   = PP.text "("  PP.<> PP.sep [pp' False l, pp' True r] PP.<> PP.text ")"


parseComb, parsePrim, parseVar
    :: (Basis basis) => Parser (CTerm basis)
parseComb = do
    start <- PA.upper
    rest  <- PA.many (PA.noneOf " ()\t\n\r\f\v")
    case filter (\pc -> combName pc == start:rest) primCombs of
                [c] -> return (Const c)
                _ -> PA.unexpected $ "unknown primitive combinator: " ++ start:rest
    PA.<?> "parseComb"

parseVar = liftM Var varParse

parsePrim = parseVar PA.<|> parseComb PA.<?> "parsePrim"

parseTerm, parseTerm' :: (Basis basis) => Maybe (CTerm basis)
                                        -> Parser (CTerm basis)
parseTerm condL = do
    PA.spaces
    parseTerm' condL

parseLeft :: (Basis basis) => Parser (CTerm basis)
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
-- ** Subterms

-- | Is the first term a subterm of the second
subterm :: Basis basis => CTerm basis -> CTerm basis -> Bool
subterm (Var a1) (Var a2)     | a1 == a2 = True
                              | otherwise = False
subterm (Const a1) (Const a2) | a1 == a2 = True
                              | otherwise = False
subterm x (a1 :@ a2)          = x == (a1 :@ a2) || subterm x a1 || subterm x a2
subterm _x _y                 = False

-- | Returns all subterms of a term. Does not return duplicates
allSubterms :: Basis basis => CTerm basis -> [CTerm basis]
allSubterms (Var a1) = [Var a1]
allSubterms (Const a1) = [Const a1]
allSubterms (a1 :@ a2) = (a1 :@ a2) : nub (allSubterms a1 ++ allSubterms a2)

-----------------------------------------------------------------------------
-- ** Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--
-- Returns the resulting term.
substitute :: Basis basis  => VarString -> CTerm basis -> CTerm basis -> CTerm basis
substitute _var _replace (Const x) = Const x
substitute var replace (Var x) | x == var = replace
                               | otherwise = Var x
substitute var replace (x :@ y) = substitute var replace x :@ substitute var replace y

-- ** Helpers

-- | Is this combinator left associated (can be written without parenthesis in standard notation)
leftAssociated :: Basis basis => CTerm basis -> Bool
leftAssociated (Var _x) = True
leftAssociated (Const _x) = True
leftAssociated (x :@ y) = leftAssociated x && not (isApp y)

-- | Is this combinator an application
isApp :: Basis basis => CTerm basis -> Bool
isApp (_ :@ _) = True
isApp _ = False

-----------------------------------------------------------------------------
-- ** Reduction

type Redex basis v = (Combinator basis, [CTerm basis])

-- | A term is a redex,  if
--      * the head is a primitive combinator
--      * the number of args are equal or greater then the arity of the primitive combinator
--
--   Returns just a pair of redexHead and redexArgs, when the term is an redex.
--   Returns Nothing, if the input term is not a redex
redex :: Basis basis => CTerm basis -> Maybe (Redex basis v)
redex = redex' []
  where
    redex' accu (Const c)
        | length accu  >= primArity c    = Just (c, accu)
        | otherwise                     = Nothing
    redex' _ (Var _)                    = Nothing
    redex' accu (l :@ arg)              = redex' (arg : accu) l

-- | Is this term an redex?
isRedex :: Basis basis => CTerm basis -> Bool
isRedex = isJust . redex

instance (ReductionContext c (CTerm basis), Basis basis, Strategy s) =>
                Reduction (CTerm basis) s c where
    reduceOnce' s zipper =
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
applyCombinator :: Basis basis =>
                (BTZipper (CTerm basis), (Combinator basis, [CTerm basis]))
                -> BTZipper (CTerm basis)
applyCombinator (zipper,(comb,args)) =
    let replaced = foldr (\ (var,arg) term -> substitute var arg term)
                            (combReduct comb)
                            (zip (combVars comb) args)
    in zipper {zipSelected = if length args == primArity comb
                                    then replaced
                                    else foldl (:@) replaced (drop (primArity comb) args)}

-----------------------------------------------------------------------------
-- ** Convenience

-- | Normal order reduction for a term.
--
--  This is not guaranteed to terminate.
normalOrderReduction :: Basis basis => CTerm basis -> CTerm basis
normalOrderReduction = reduceIt instrumentedContext NormalForm

--
---- | Takes a string, parses it, applies normalOrderReduction and prints the result.
--strReduction :: String -> String
--strReduction = pp . normalOrderReduction . parseKS

