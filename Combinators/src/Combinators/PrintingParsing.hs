-----------------------------------------------------------------------------
--
-- Module      :  Combinators.PrintingParsing
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



module Combinators.PrintingParsing (
-----------------------------------------------------------------------------
-- * Printing and parsing for terms, types, ...
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** A class for printing and parsing
-----------------------------------------------------------------------------
    PP(..),
-----------------------------------------------------------------------------
-- ** Helpers for Parsec based parsers. Some lexer defaults
-----------------------------------------------------------------------------

    lexer,
    brackets',
    commaSep',
    parens',
    colon',
    symbol',
    dot'
)where

import Text.PrettyPrint
       (punctuate, vcat, brackets, text, style, renderStyle, Doc)
import qualified Text.Parsec.String as PP (Parser)
import Text.PrettyPrint.HughesPJ (Mode(..), Style(..))
import qualified Text.Parsec as PP
       ((<?>), (<|>), parse, ParseError)
import Text.Parsec.Token (GenTokenParser)
import Data.Functor.Identity (Identity(..))
import qualified Text.Parsec.Token as PP
       (dot, symbol, colon, parens, commaSep, brackets, makeTokenParser)
import Text.Parsec.Language (emptyDef)

-----------------------------------------------------------------------------
-- ** A class for printing and parsing
-----------------------------------------------------------------------------

class PP t where
    pp :: t -> Doc
    -- ^ Pretty prints it to a Doc.
    --
    -- Need to implement this for instances
    pparser :: PP.Parser t
    -- ^ Parses it
    --
    -- Need to implement this for instances

    pps :: t -> String
    -- ^ Pretty prints it to a String
    pps = renderStyle style . pp

    ppsh :: t -> ShowS
    -- ^ Pretty prints it to a ShowS
    ppsh = showString . pps

    ppsNoNewline :: t -> String
    -- ^ Pretty prints it to a String all in one line
    ppsNoNewline = renderStyle style{mode = OneLineMode} . pp

    pparseError :: String -> Either PP.ParseError t
    -- ^ Parses it from a string with possible error handling
    pparseError = PP.parse pparser ""

    pparse :: String -> t
    -- ^ Parses it from a string and throw an error if this is not possible
    pparse str = case pparseError str of
                    Left err -> error (show err)
                    Right t  -> t


instance PP t => PP [t] where
    pp [] = text "[]"
    pp l = brackets (vcat (punctuate (text ",") (map pp l)))
    pparser = parseList pparser


instance PP t => PP (Maybe t) where
    pp Nothing = text "Nothing"
    pp (Just t) = pp t
    pparser = parseMaybe pparser


parseMaybe :: PP.Parser t -> PP.Parser (Maybe t)
parseMaybe parser = do
        v <- parser
        return (Just v)
    PP.<|> return Nothing
    PP.<?> "parseMaybe"

parseList :: PP.Parser t -> PP.Parser [t]
parseList parser = brackets' (commaSep' parser)

-----------------------------------------------------------------------------
-- ** Helpers for parsec based parsers. Some lexer defaults
-----------------------------------------------------------------------------

lexer :: GenTokenParser String u Identity
lexer = PP.makeTokenParser emptyDef

brackets' :: PP.Parser a -> PP.Parser a
brackets'  = PP.brackets     lexer

commaSep' :: PP.Parser a -> PP.Parser [a]
commaSep'   = PP.commaSep   lexer

parens' :: PP.Parser a -> PP.Parser a
parens'  = PP.parens     lexer

colon' :: PP.Parser String
colon'  = PP.colon lexer

symbol' :: String -> PP.Parser String
symbol'  = PP.symbol   lexer

dot' :: PP.Parser String
dot'  = PP.dot   lexer

