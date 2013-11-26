{-# LANGUAGE FlexibleInstances #-}
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
    testLambda,
    parseStringVar,
    ppl
) where

import Variable

import Test.QuickCheck
       (Arbitrary(..), elements, frequency)
import Control.Monad (liftM, liftM2)
import Text.Parsec.String (Parser)
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as PA
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Debug.Trace (trace)

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

data Variable v => LTerm v =
      LVar v
    | LTerm v :@: LTerm v
        -- ^ Bind application to the left.
    | v :.: LTerm v
     deriving (Eq, Show)

-- Bind application to the left.
infixl 5 :@:
-- Bind abstraction to the left.
-- FIXME
infixl 5 :.:

-----------------------------------------------------------------------------
-- * Priniting and parsing

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
ppl :: Variable v => LTerm v -> String
ppl t = PP.render (pp' True True [] t)

-- | The first Boolean value is true if it is a left subterm.
-- The second Boolean Term is true, if it  is a right most subterm
--    (which is closed with brackets anyway)
pp' :: Variable v => Bool -> Bool -> [v] -> LTerm v -> PP.Doc
pp' _ _ _ (LVar v)        = PP.text (varPp v)
pp' True rm _ (l :@: r)   = PP.fsep [pp' True False [] l, pp' False rm [] r]
pp' False _ _ (l :@: r)   = PP.parens (pp' True True [] (l :@: r))
pp' il rm l (v :.: (v' :.: t')) = pp' il rm (v : l) (v' :.: t')
pp' il False l (v :.: t)  = PP.parens $ pp' il True l (v :.: t)
pp' _ True l (v :.: t)    = PP.fcat [PP.text "\\",
                                PP.fsep (map (PP.text .varPp) (reverse (v:l))),
                                PP.text ".", pp' True True [] t]

-- | Takes a String and returns a Term
--
-- Throws an error, when the String can't be parsed
parse ::  Variable v => String -> LTerm v
parse str = case parse' str of
                Left err    -> error (show err)
                Right term  -> term

parseStringVar :: String -> LTerm VarString
parseStringVar = parse

--parseErr ::  Variable v => String -> Either String (LTerm v)
--parseErr str = case parse' str of
--                Left err    -> Left (show err)
--                Right term  -> Right term

parse' :: Variable v => String -> Either PA.ParseError (LTerm v)
parse' = PA.parse (parseTerm Nothing) ""

-- example
--testParse :: Assertion
--testParse = assertBool "parse"
--    (pp (parse "\\x. \\y. x y (x y)" :: LTerm VarString) == "S K (K v)")

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
        return (foldr (:.:) t vl)
    PA.<|> do
        v <- varParse
        return (LVar v)

    PA.<?> "parsePart Nothing"

-----------------------------------------------------------------------------
-- * Substitution
-- | The substitution of a variable "var" with a term "replace" in the matched term
--
-- Returns the resulting term.
substitute :: Variable v  => v -> LTerm v -> LTerm v -> LTerm v
substitute var replace (LVar x) | x == var = replace
                                | otherwise = LVar x
substitute var replace (x :@: y) = substitute var replace x :@: substitute var replace y
substitute var replace (v :.: t) | v == var = undefined -- rename v and replace
                                 | otherwise = v :.: substitute var replace t

-- | Is this combinator an application
isVal :: Variable v => LTerm v -> Bool
isVal (_ :.: _) = True
isVal _ = False

-- | A "Left" term is returned if reduction has changed the term, else a "Right" term.
oneStepHeadReduction :: Variable v => LTerm v -> Either (LTerm v) (LTerm v)
oneStepHeadReduction term =
    case redex term of
        Just (comb,args) ->  let replaced = foldr (\ (var,arg) term' -> substitute var arg term')
                                                    (combReduct comb)
                                            (zip (combVars comb) args)
                            in Left (if length args == primArity comb
                                        then replaced
                                        else foldl (:@) replaced (drop (primArity comb) args))
        Nothing -> Right term

-- ** Testing

instance Arbitrary (LTerm VarString) where
    arbitrary = frequency
        [(8,liftM LVar (elements ["u","v","w","x","y","z"]))
        ,(6,liftM2 (:@:) arbitrary arbitrary)
        ,(8,liftM2 (:.:) (elements ["u","v","w","x","y","z"]) arbitrary)
        ]

--  For any term: print and parse give the original term
prop_printParse :: LTerm VarString -> Bool
prop_printParse term = trace ("\n\n" ++ ppl term ++ "\n" ++ ppl (parseStringVar (ppl term))
                            ++ "\n\n" ++ show term ++ "\n" ++ show (parseStringVar (ppl term))) $
                            term == parse (ppl term)

testLambda :: [Test]
testLambda = [testProperty "prop_printParse" prop_printParse]
