{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-orphans #-}
{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Combinatory logic implementation inspired by Katalin Bimbo's book.
--
-----------------------------------------------------------------------------

module Combinators.Language (
-----------------------------------------------------------------------------
-- * Basic types
    Term(..),
    Basis(..),
    Combinator(..),
    primArity,
    spine,
    spineLength,
-----------------------------------------------------------------------------
-- * Basis
-- ** IKS
    IKS,
    iIKS,
    kIKS,
    sIKS,
-----------------------------------------------------------------------------
-- * Variables
    Variable(..),
    VarString,
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
-- * Term Zipper
    TermZipper(..),
    constrZipper,
    zipTerm,
    zipRoot,
    zipIsRoot,
    zipUp,
    zipUpLeft,
    zipUpRight,
    zipDownLeft,
    zipDownLeft',
    zipDownRight,
    zipDownRight',
    zipEnum,
    zipperGetPath,
-----------------------------------------------------------------------------
-- * Normal order reduction
    Strategy,
    normalOrderStrategy,
    oneStepReduction,
    oneStepReduction',
    applyStrategy,
    applyCombinator,
    reduction,
    reduction',
    normalOrderReduction,
    strReduction,
    testLanguage

 ) where

import Variable

import Data.List (nub)
import Data.Maybe (fromJust, isJust)
import Control.Monad (liftM2, liftM, mplus)

import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA

import Test.HUnit.Base (Assertion)
import Test.HUnit ((@=?), assertBool)
import Test.QuickCheck
       (elements, oneof, sized,Arbitrary(..))
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework (Test)

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

data (Variable v, Basis basis v) => Term basis v =
    Const ! (Combinator basis v)
    | Var ! v
    | ! (Term basis v) :@ ! (Term basis v)
        -- ^ Bind application to the left.
     deriving (Eq, Show)

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
data Combinator basis v = Combinator
    {combName   :: ! String, -- ^ needs to start with upper case character
     combVars   :: ! [v],
     combReduct :: ! (Term basis v)}
     deriving (Eq)

instance Show (Combinator basis v) where
    show = combName

-- | The arity of a primitive combinator is defined by the length
-- of the variables in its axiom
primArity :: Combinator basis v -> Int
primArity = length . combVars

spine :: (Basis basis v) => Term basis v -> [Term basis v]
spine = reverse . spine'
  where
    spine' (a :@ b) = b : spine' a
    spine' t' = [t']

spineLength :: (Basis basis v) => Term basis v -> Int
spineLength (a :@ _b) = 1 + spineLength a
spineLength _ = 1

--  For any term: print and parse give the original term
prop_spineLength :: Term IKS VarString -> Bool
prop_spineLength term = length (spine term) == spineLength term

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
pp :: Basis basis v => Term basis v -> String
pp t = PP.render (pp' False t)

pp' :: Basis basis v => Bool -> Term basis v -> PP.Doc
pp' _ (Const c)     = PP.text (combName c)
pp' _ (Var v)       = PP.text (varPp v)
pp' False (l :@ r)  = PP.sep [pp' False l, pp' True r]
pp' True (l :@ r)   = PP.text "("  PP.<> PP.sep [pp' False l, pp' True r] PP.<> PP.text ")"

pprint :: Basis basis v => Term basis v -> String
pprint = pprint' False

pprint' :: Basis basis v => Bool -> Term basis v -> String
pprint' _ (Const c)     = combName c
pprint' _ (Var v)       = varPp v
pprint' False (l :@ r)  = pprint' False l ++ " " ++  pprint' True r
pprint' True (l :@ r)   = "("  ++ pprint' False l ++ " " ++  pprint' True r ++ ")"

-- example
testPp :: Assertion
testPp = assertBool "pp"
    ((parse "S K (K v)" :: Term IKS VarString) == (Const sIKS :@ Const kIKS)
                                                    :@ (Const kIKS :@ Var "v"))

-- | Takes a String and returns a Term
--
-- Throws an error, when the String can't be parsed
parse ::  Basis b v => String -> Term b v
parse str = case parse' str of
                Left err    -> error (show err)
                Right term  -> term

parseErr ::  Basis b v => String -> Either String (Term b v)
parseErr str = case parse' str of
                Left err    -> Left (show err)
                Right term  -> Right term


-- example
testParse :: Assertion
testParse = assertBool "parse"
    (pp (parse "S K (K v)" :: Term IKS VarString) == "S K (K v)")

parseIKS :: String -> Term IKS VarString
parseIKS = parse :: String -> Term IKS VarString

parse' :: Basis b v => String -> Either PA.ParseError (Term b v)
parse' = PA.parse (parseTerm Nothing) ""


parseComb, parsePrim, parseVar
    :: (Basis basis v) => Parser (Term basis v)
parseComb = do
    start <- PA.upper
    rest  <- PA.many (PA.noneOf " ()\t\n\r\f\v")
    case filter (\pc -> combName pc == start:rest) primCombs of
                [c] -> return (Const c)
                _ -> PA.unexpected $ "unknown primitive combinator: " ++ start:rest
    PA.<?> "parseComb"

parseVar = liftM Var varParse

parsePrim = parseVar PA.<|> parseComb PA.<?> "parsePrim"

parseTerm, parseTerm' :: (Basis basis v) => Maybe (Term basis v)
                                        -> Parser (Term basis v)
parseTerm condL = do
    PA.spaces
    parseTerm' condL

parseLeft :: (Basis basis v) => Parser (Term basis v)
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

-- ** Testing

instance Arbitrary (Term IKS VarString) where
    arbitrary = sized $ \_n -> oneof
        [liftM Const (elements primCombs),
            liftM Var (elements ["u","v","w","x","y","z"]),
            liftM2 (:@) arbitrary arbitrary]

--  For any term: print and parse give the original term
prop_printParse :: Term IKS VarString -> Bool
prop_printParse term = term == parseIKS (pp term)

-----------------------------------------------------------------------------
-- * Subterms

-- | Is the first term a subterm of the second
subterm :: Basis basis v => Term basis v -> Term basis v -> Bool
subterm (Var a1) (Var a2)     | a1 == a2 = True
                              | otherwise = False
subterm (Const a1) (Const a2) | a1 == a2 = True
                              | otherwise = False
subterm x (a1 :@ a2)          = x == (a1 :@ a2) || subterm x a1 || subterm x a2
subterm _x _y                 = False

-- example:
testSubterm :: Assertion
testSubterm = assertBool "subterm"
        (subterm (Const iIKS :@ Var "x") (Var "x" :@ (Const iIKS :@ Var "x") :@ Var "y"))

-- | Returns all subterms of a term. Does not return duplicates
allSubterms :: Basis basis v => Term basis v -> [Term basis v]
allSubterms (Var a1) = [Var a1]
allSubterms (Const a1) = [Const a1]
allSubterms (a1 :@ a2) = (a1 :@ a2) : nub (allSubterms a1 ++ allSubterms a2)

-- example
testAllSubterms :: Assertion
testAllSubterms = assertBool "allSubterms"
    (length (allSubterms  (Var "x" :@ (Const iIKS :@ Var "x") :@ Var "y")) == 6)

-----------------------------------------------------------------------------
-- * Substitution

-- | The substitution of a variable "var" with a term "replace" in the matched term
--
-- Returns the resulting term.
substitute :: Basis basis v  => v -> Term basis v -> Term basis v -> Term basis v
substitute _var _replace (Const x) = Const x
substitute var replace (Var x) | x == var = replace
                               | otherwise = Var x
substitute var replace (x :@ y) = substitute var replace x :@ substitute var replace y

-- example
testSubstitute :: Assertion
testSubstitute =  assertBool "testSubstitute"
    (substitute "y" (Var "y" :@ Var "y")
        (substitute "x" (Const iIKS) (Const sIKS :@ Var "x" :@ Var "y" :@ Var "z"))
            == ((Const sIKS :@ Const iIKS) :@ (Var "y" :@ Var "y")) :@ Var "z")

-- * Helpers

-- | Is this combinator left associated (can be written without parenthesis in standard notation)
leftAssociated :: (Basis basis v, Variable v) => Term basis v -> Bool
leftAssociated (Var _x) = True
leftAssociated (Const _x) = True
leftAssociated (x :@ y) = leftAssociated x && not (isApp y)

--example
testLeftAssociated :: Assertion
testLeftAssociated =  assertBool "testLeftAssociated"
    (leftAssociated (Const iIKS :@ Var "x" :@ Var "y") &&
    not (leftAssociated (Const iIKS :@ (Var "x" :@ Var "y"))))

-- | Is this combinator an application
isApp :: Basis basis v => Term basis v -> Bool
isApp (_ :@ _) = True
isApp _ = False

-----------------------------------------------------------------------------
-- * Head Reduction

-- ** Simple

type Redex basis v = (Combinator basis v, [Term basis v])

-- | A term is a redex,  if
--      * the head is a primitive combinator
--      * the number of args are equal or greater then the arity of the primitive combinator
--
--   Returns just a pair of redexHead and redexArgs, when the term is an redex.
--   Returns Nothing, if the input term is not a redex
redex :: Basis basis v => Term basis v -> Maybe (Redex basis v)
redex = redex' []
  where
    redex' accu (Const c)
        | length accu  >= primArity c    = Just (c, accu)
        | otherwise                     = Nothing
    redex' _ (Var _)                    = Nothing
    redex' accu (l :@ arg)              = redex' (arg : accu) l

-- | Is this term an redex?
isRedex :: Basis basis v => Term basis v -> Bool
isRedex = isJust . redex

-- example
testRedex :: Assertion
testRedex =   assertBool "testRedex"
    (redex (Const iIKS :@ Var "x" :@ Var "y") == Just (iIKS,[Var "x", Var "y"]))

-- | A "Left" term is returned if reduction has changed the term, else a "Right" term.
oneStepHeadReduction :: (Variable v, Basis basis v)
                            => Term basis v -> Either (Term basis v) (Term basis v)
oneStepHeadReduction term =
    case redex term of
        Just (comb,args) ->  let replaced = foldr (\ (var,arg) term' -> substitute var arg term')
                                                    (combReduct comb)
                                            (zip (combVars comb) args)
                            in Left (if length args == primArity comb
                                        then replaced
                                        else foldl (:@) replaced (drop (primArity comb) args))
        Nothing -> Right term

-- examples
testOneStepHeadReduction :: Assertion
testOneStepHeadReduction =
    Left (Var "x" :@ Var "y") @=? oneStepHeadReduction (Const iIKS :@ Var "x" :@ Var "y")
testOneStepHeadReduction2 :: Assertion
testOneStepHeadReduction2 =
     Left (((Var "a" :@ Var "c") :@ (Var "b" :@ Var "c")) :@ Const kIKS) @=?
     oneStepHeadReduction (Const sIKS :@ Var "a" :@ Var "b" :@ Var "c" :@ Const kIKS)

-- | Reducing a head redex repeatedly, until it does not change any more.
--
--  This is not guaranteed to terminate.
weakHeadReduction :: Basis basis v => Term basis v -> Term basis v
weakHeadReduction t =
    case oneStepHeadReduction t of
        Left t' -> {-trace (show t) $-} weakHeadReduction t'
        Right t' -> t'

-- example
testWeakHeadReduction :: Assertion
testWeakHeadReduction =
    Var "x" @=? weakHeadReduction (Const sIKS :@ Const kIKS :@ Const kIKS :@ Var "x")


-----------------------------------------------------------------------------
-- * Term Zipper

-- | This is a zipper for a term, which is a structure which carries a term and a
-- position in the term, without the possibility of an invalid position.
data TermZipper basis v = TermZipper
  { zipSelected      :: Term basis v
        -- ^ The currently selected term.
  , zipAnchestors   ::  [Either (Term basis v) (Term basis v)]
        -- ^ The topmost (root) anchestor comes last.
        --
        --
  }  deriving (Eq,Show)

-- | Construct a 'TermZipper' from a 'Term' with the root as selected element.
constrZipper :: Term basis v -> TermZipper basis v
constrZipper term = TermZipper
  { zipSelected     = term
  , zipAnchestors   =   []
  }

-- | Returns the (root) 'Term' in the zipper
zipTerm :: (Variable v, Basis basis v) => TermZipper basis v -> Term basis v
zipTerm = zipSelected . zipRoot

-- example
testZipTerm :: Assertion
testZipTerm =
    term @=? zipTerm (constrZipper term)
  where
    term = parseIKS "S K K x"


-- | Navigate to the parent of the given position.
--
-- Returns 'Nothing' if this is the root, else return 'Just' the 'TermZipper'.
zipUp :: (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipUp zipper =
  case zipAnchestors zipper of
    (Left t:tail') -> Just
      TermZipper { zipSelected = t :@ zipSelected zipper
                  , zipAnchestors  = tail'}
    (Right t:tail') -> Just
      TermZipper { zipSelected = zipSelected zipper :@ t
                  , zipAnchestors  = tail'}
    [] -> Nothing

-- | Navigate to the parent of the given position if this is a right child.
--
-- Returns 'Nothing' if this is the root or a left child,
-- else return 'Just' the 'TermZipper'.
zipUpLeft :: (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipUpLeft zipper =
  case zipAnchestors zipper of
    (Left _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Navigate to the parent of the given position if this is a left child.
--
-- Returns 'Nothing' if this is the root or a right child,
-- else return 'Just' the 'TermZipper'.
zipUpRight :: (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipUpRight zipper =
  case zipAnchestors zipper of
    (Right _t:_tail') -> zipUp zipper
    _ -> Nothing

-- | Select the left child.
--
-- Returns 'Nothing' if this is a 'Var' or a 'Const'.
zipDownLeft ::  (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipDownLeft zipper = case zipSelected zipper of
    l :@ r ->
      Just TermZipper{zipSelected = l,
                      zipAnchestors = Right r : zipAnchestors zipper}
    _ -> Nothing

-- | Select the left child if available, but don't go to primitives
--
-- Returns 'Nothing' if this is a 'Var' or a 'Const',
-- or the left child contains a 'Var' or a 'Const'.
zipDownLeft' ::  (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipDownLeft' zipper = case zipSelected zipper of
    Var _ :@ _r   -> Nothing
    Const _ :@ _r -> Nothing
    _       -> zipDownLeft zipper

-- | Select the right child.
--
-- Returns 'Nothing' if this is a 'Var' or a 'Const'.
zipDownRight ::  (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipDownRight zipper = case zipSelected zipper of
    l :@ r ->
      Just TermZipper{zipSelected = r,
                      zipAnchestors = Left l : zipAnchestors zipper}
    _ -> Nothing

-- | Select the right child if available, but don't go to primitives
--
-- Returns 'Nothing' if this is a 'Var' or a 'Const',
-- or the right child contains a 'Var' or a 'Const'.
zipDownRight' ::  (Variable v, Basis basis v) => TermZipper basis v -> Maybe (TermZipper basis v)
zipDownRight' zipper = case zipSelected zipper of
    _l :@ Var _   -> Nothing
    _l :@ Const _ -> Nothing
    _       -> zipDownRight zipper

-- examples
testZipMove1 :: Assertion
testZipMove1 =
    term @=? (zipTerm . fromJust . zipUp . fromJust . zipDownLeft . constrZipper) term
  where
    term = parseIKS "S K K x"

testZipMove2 :: Assertion
testZipMove2 =
    term @=? (zipTerm . fromJust . zipUp .  fromJust . zipUp .  fromJust .
                zipDownLeft .  fromJust . zipDownRight . constrZipper) term
  where
    term = parseIKS "S K (K x)"

-- | Navigate to the topmost term of the given 'TermZipper'.
zipRoot :: (Variable v, Basis basis v) => TermZipper basis v -> TermZipper basis v
zipRoot zipper = maybe zipper zipRoot (zipUp zipper)

-- | Is the position of this 'TermZipper' the root position?
zipIsRoot :: TermZipper basis v -> Bool
zipIsRoot term | null (zipAnchestors term) = True
               | otherwise = False

-- examples
testZipRoot :: Assertion
testZipRoot =
    term @=? (zipSelected . zipRoot . fromJust . zipDownRight .
            fromJust . zipDownLeft . fromJust . zipDownLeft . constrZipper) term
  where
    term = parseIKS "S K K x"

testZipIsRoot :: Assertion
testZipIsRoot =  assertBool "testZipIsRoot"  $
    (zipIsRoot . zipRoot .  fromJust . zipDownLeft .  fromJust . zipDownRight . constrZipper) term
  where
    term = parseIKS "S K (K x)"

testZipIsNotRoot :: Assertion
testZipIsNotRoot =  assertBool "testZipIsNotRoot"
    ( not ((zipIsRoot . fromJust . zipDownLeft .  fromJust . zipDownRight . constrZipper) term))
  where
    term = parseIKS "S K (K x)"

-- | Enumerates all positions for a zipper
zipEnum :: (Variable v, Basis basis v) => TermZipper basis v -> [TermZipper basis v]
zipEnum zipper =  zipEnum' [] (Just (zipRoot zipper))
  where
    zipEnum' accu (Just zipper') =
        let accu'   = zipper' : accu
            accu''  = zipEnum' accu' (zipDownLeft zipper')
        in zipEnum' accu'' (zipDownRight zipper')
    zipEnum' accu Nothing = accu

-- example
--  (map pp . map zipSelected . zipEnum . constrZipper) (parseIKS "S (K x) (K x)")

-- ** Testing

instance Arbitrary (TermZipper IKS VarString) where
    arbitrary = do
        term <- arbitrary
        elements (zipEnum (constrZipper term))

-- | A root is a root
prop_zipRoot :: TermZipper IKS VarString -> Bool
prop_zipRoot m = zipIsRoot (zipRoot m)

-- | up after down is identity
prop_upDown1 :: TermZipper IKS VarString -> Bool
prop_upDown1 zip' = case zipSelected zip' of
                    _ :@ _ -> zip' == (fromJust . zipUp . fromJust . zipDownLeft) zip'
                    _ -> True

-- | down after up is identity, when the position is recovered
prop_upDown2 ::  TermZipper IKS VarString -> Bool
prop_upDown2 zip' = case zipAnchestors zip' of
                    []          -> True
                    Left _ : _  -> zip' == (fromJust . zipDownRight . fromJust . zipUp) zip'
                    Right _ : _ -> zip' == (fromJust . zipDownLeft . fromJust . zipUp) zip'

-- | Makes a path from the position in the TermZipper from cigol:Combinators/Language module,
-- according to the path concept in the OntoZipper implementation.
-- zipperGetPath from root -> []
-- zipperGetPath (x (y z) !v!) -> [2]
-- zipperGetPath (x (y !z!) v) -> [1,1]

zipperGetPath :: Basis basis v => TermZipper basis v -> [Int]
zipperGetPath z = reverse (zipperGetPath' [] (reverse (zipAnchestors z)))
  where
    zipperGetPath' accu [] = accu
    zipperGetPath' accu (Left term: rest)   = zipperGetPath' (spineLength term:accu) rest
    zipperGetPath' accu (Right _term: [])   = 0:accu
    zipperGetPath' accu (Right _term: rest) = zipperGetPath' accu rest

-----------------------------------------------------------------------------
-- * Normal order reduction

-- | A strategy takes a 'TermZipper', and returns 'Just' a 'TermZipper',
-- when it finds a new position.
--
-- Otherwise return 'Nothing'
type Strategy basis v =  TermZipper basis v -> Maybe (TermZipper basis v)

-- |
normalOrderStrategy :: (Variable v, Basis basis v) => Strategy basis v
normalOrderStrategy zipper = mplus (down zipper) (up zipper)
  where
    down zipper' = case zipDownLeft' zipper' of
                    Nothing -> zipDownRight zipper'
                    Just z -> down z
    up zipper' = case zipUpLeft zipper' of
                    Nothing -> case zipUpRight zipper' of
                                Nothing -> Nothing
                                Just z' -> zipDownRight z'
                    Just z -> up z

-- | Applying a strategy means to try to reduce the current selected position.
-- If the current position has no redex, apply the strategy to select a new position,
-- and retry if its a redex.
applyStrategy :: (Variable v, Basis basis v) =>
         Strategy basis v ->  TermZipper basis v -> Maybe (TermZipper basis v, Redex basis v)
applyStrategy strategy zipper =
    case redex (zipSelected zipper) of
         Just r ->  Just (zipper,r)
         Nothing -> case strategy zipper of
            Nothing -> Nothing
            Just zipper' -> applyStrategy strategy zipper'

-- | A one step reduction, which applies a 'Strategy' and takes a term and returns a term.
--
-- A "Left" term is returned if reduction has changed the term,
-- else a "Right" term.
oneStepReduction :: Basis basis v
                            => Strategy basis v -> Term basis v -> Either (Term basis v) (Term basis v)
oneStepReduction strategy term =
    let zipper = constrZipper term
    in case applyStrategy strategy zipper of
            Just (zipper',(comb,args)) -> Left (zipTerm (applyCombinator (zipper',(comb,args))))
            Nothing -> Right term

-- | A one step reduction, which applies a 'Strategy' and takes a 'TermZipper'
-- and returns a 'TermZipper'.
--
-- A "Left" 'TermZipper' is returned if reduction has changed the term,
-- else a "Right" 'TermZipper'.
oneStepReduction' :: Basis basis v
                            => Strategy basis v -> TermZipper basis v
                                -> Either (TermZipper basis v) (TermZipper basis v)
oneStepReduction' strategy zipper = {-trace ("reduceStep: " ++ pp (zipSelected zipper)) $-}
    case applyStrategy strategy zipper of
        Just (zipper',(comb,args)) -> Left (applyCombinator (zipper',(comb,args)))
        Nothing -> Right zipper

-- | Apply the Combinator comb on the term list
applyCombinator :: Basis basis v =>
                (TermZipper basis v, (Combinator basis v, [Term basis v]))
                -> TermZipper basis v
applyCombinator (zipper',(comb,args)) =
    let replaced = foldr (\ (var,arg) term -> substitute var arg term)
                            (combReduct comb)
                            (zip (combVars comb) args)
    in zipper' {zipSelected = if length args == primArity comb
                                    then replaced
                                    else foldl (:@) replaced (drop (primArity comb) args)}

-- | A repeated reduction, which applies a 'Strategy' and takes a 'TermZipper'
-- and returns a 'TermZipper'.
--
--  This is not guaranteed to terminate.
reduction' :: Basis basis v => Strategy basis v -> TermZipper basis v -> TermZipper basis v
reduction' strategy zipper =
    case oneStepReduction' strategy zipper of
        Left zipper' -> {-trace (show t) $-} reduction' strategy zipper'
        Right zipper' -> zipper'

-- | A repeated reduction, which applies a 'Strategy' and takes a 'Term'
-- and returns a 'Term'.
--
--  This is not guaranteed to terminate.
reduction :: Basis basis v => Strategy basis v -> Term basis v -> Term basis v
reduction strategy = zipTerm . reduction' strategy . constrZipper

-- | Normal order reduction for a term.
--
--  This is not guaranteed to terminate.
normalOrderReduction :: (Show v, Basis basis v) => Term basis v -> Term basis v
normalOrderReduction = reduction normalOrderStrategy

-- | Takes a string, parses it, applies normalOrderReduction and prints the result.
strReduction :: String -> String
strReduction = pp . normalOrderReduction . parseIKS

-- example
testReduction1 :: Assertion
testReduction1 =
    parseIKS "v" @=? (normalOrderReduction . parseIKS) "S K (K x y) (I v)"

testReduction2 :: Assertion
testReduction2 =
    parseIKS "x" @=? (normalOrderReduction . parseIKS) "S(S(K S)(S(K K)K))(K(S(K K))) x y"

testReduction3 :: Assertion
testReduction3 =
    parseIKS "x z(y z)" @=? (normalOrderReduction . parseIKS)
                            "S(S(K S)(S(K(S(K S)))(S(K(S(K K)))S)))(K(K(S K K))) x y z"
testReduction4 :: Assertion
testReduction4 =
    parseIKS "K (x y)" @=? (normalOrderReduction . parseIKS) "S (K K) x y"

testReduction5 :: Assertion
testReduction5 =
    parseIKS "x y" @=? (normalOrderReduction . parseIKS) "S(S(K S)(S(K K)(S(K S)K)))(K K) x y z"

testReduction6 :: Assertion
testReduction6 =
    parseIKS "x z" @=? (normalOrderReduction . parseIKS) "S(K S)(S(K K)) x y z"

testReduction7 :: Assertion
testReduction7 =
    parseIKS "x z" @=? (normalOrderReduction . parseIKS)
                            "S(K K)(S(S(K S)(S(K K)(S K K)))(K(S K K))) x y z"

testReduction8 :: Assertion
testReduction8 =
    parseIKS "x u (z u) (y u (z u))" @=? (normalOrderReduction . parseIKS)
                            "S(K(S(K S)))(S(K S)(S(K S))) x y z u"

testReduction9 :: Assertion
testReduction9 =
    parseIKS "x u (z u) (y u (z u))" @=? (normalOrderReduction . parseIKS)
                            "S(S(K S)(S(K K)(S(K S)(S(K(S(K S)))S))))(K S) x y z u"

testReduction10 :: Assertion
testReduction10 =
    parseIKS "x" @=? (normalOrderReduction . parseIKS)
                           "S K K x"

testReduction11 :: Assertion
testReduction11 =
    parseIKS "x y" @=? (normalOrderReduction . parseIKS)
                           "S(S(K S)K)(K(S K K)) x y"

testReduction12 :: Assertion
testReduction12 =
    parseIKS "x y" @=? (normalOrderReduction . parseIKS)
                           "S(S(K S)K)(K I) x y"

testReduction13 :: Assertion
testReduction13 =
    parseIKS "x z" @=? (normalOrderReduction . parseIKS)
                           "S(K S)(S(K K)) x y z"


testLanguage :: [Test]
testLanguage = [testCase "testSubterm" testSubterm,
                    testCase "testAllSubterms" testAllSubterms,
                    testProperty "testSpineLength" prop_spineLength,
                    testCase "testPp" testPp,
                    testCase "testParse" testParse,
                    testProperty "prop_printParse" prop_printParse,
                    testCase "testSubstitute" testSubstitute,
                    testCase "testLeftAssociated" testLeftAssociated,
                    testCase "testRedex" testRedex,
                    testCase "testOneStepHeadReduction" testOneStepHeadReduction,
                    testCase "testOneStepHeadReduction2" testOneStepHeadReduction2,
                    testCase "testWeakHeadReduction" testWeakHeadReduction,
                    testCase "testZipTerm" testZipTerm,
                    testCase "testZipMove1" testZipMove1,
                    testCase "testZipMove2" testZipMove2,
                    testCase "testZipRoot" testZipRoot,
                    testCase "testZipIsRoot" testZipIsRoot,
                    testCase "testZipIsNotRoot" testZipIsNotRoot,
                    testProperty "prop_zipRoot" prop_zipRoot,
                    testProperty "prop_upDown1" prop_upDown1,
                    testProperty "prop_upDown2" prop_upDown2,
                    testCase "testReduction1" testReduction1,
                    testCase "testReduction2" testReduction2,
                    testCase "testReduction3" testReduction3,
                    testCase "testReduction4" testReduction4,
                    testCase "testReduction5" testReduction5,
                    testCase "testReduction6" testReduction6,
                    testCase "testReduction7" testReduction7,
                    testCase "testReduction8" testReduction8,
                    testCase "testReduction9" testReduction9,
                    testCase "testReduction10" testReduction10,
                    testCase "testReduction11" testReduction11,
                    testCase "testReduction12" testReduction12,
                    testCase "testReduction13" testReduction13
                                        ]

