-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Types
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

{-# LANGUAGE DataKinds, GADTs, StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, Rank2Types #-}

module Combinators.Types (
    SType(..),
    TypeAtom,
    Typeable(..),
    typeVarGen,
    canonicalizeType,
    canonicalizeTypeContext,
    TypeContext,
    Substitutor,
    substituteType,
    substituteEnv,
    typeVars,
    parseType
) where

import Combinators.BinaryTree
import qualified Text.PrettyPrint as PP (text, sep, parens, Doc)
import qualified Text.Parsec as PA
import Text.Parsec.String (Parser)
import Combinators.Variable (varParse, VarString)
import Text.PrettyPrint
       (($$), (<+>), braces, empty, Doc, text, (<>), parens, brackets)
import Combinators.Reduction (Term)

-----------------------------------------------------------------------------
-- * Simple Types

type TypeAtom = String

data SType where
    SAtom :: TypeAtom -> SType
    (:->:) :: SType -> SType -> SType

-- Bind type constructor to the right.
infixr 5 :->:

deriving instance Show SType
deriving instance Eq SType
deriving instance Ord SType

instance BinaryTree SType where
    decompose (a :->: b) = Just (a,b)
    decompose (SAtom _) = Nothing
    a @@ b              = a :->: b

-----------------------------------------------------------------------------
-- * Type inference

-- | A class that describe a possible Typeable Term
class Term t =>  Typeable t where
    typeof :: t -> Maybe (SType, TypeContext VarString)
    -- ^ Infers just the simple type and environment of a Term or returns Nothing,
    -- if the term is not typeable.
    typeofC :: t -> Maybe SType
    -- ^ Infers just the simple type of a closed Term or returns Nothing, if the
    -- term is not typeable

typeVarGen :: [String]
typeVarGen = [ c: n | n <- ("" : map show [(1:: Int)..]), c <- "abcdefg"]

canonicalizeType :: SType -> SType
canonicalizeType t = (\(_,_,r) -> r) $ canonicalizeType' 0 [] t

canonicalizeTypeContext :: (SType,TypeContext a) -> (SType,TypeContext a)
canonicalizeTypeContext (t,enviro) =
    let (index,env,res) = canonicalizeType' 0 [] t
        (_,_,res'') = foldr (\(k,t) (i,env,newEnv) ->
                                let (index',env',res') = canonicalizeType' i env t
                                in (index',env',(k,res') : newEnv))
                            (index,env,[]) enviro
    in (res,res'')

canonicalizeType' :: Int -> [(String,Int)] -> SType -> (Int, [(String,Int)], SType)
canonicalizeType' i env (SAtom s) =
    case lookup s env of
        Just ind ->  (i,env,SAtom (typeVarGen !! ind))
        Nothing -> (i+1,(s,i):env,SAtom (typeVarGen !! i))
canonicalizeType' i env (l :->: r) =
    let (i',env',l')   = canonicalizeType' i env l
        (i'',env'',r') = canonicalizeType' i' env' r
    in (i'',env'',l' :->: r')

-----------------------------------------------------------------------------
-- ** Printing and parsing

instance PP SType where
    pp = pp' False
    pparser = parseType []

pp' :: Bool -> SType -> PP.Doc
pp' True (a :->: b)   = PP.parens (pp' False (a :->: b))
pp' False (a :->: b)  = PP.sep [pp' True a, PP.text "->", pp' False b]
pp' _ (SAtom s)      = PP.text s


parseType :: [SType] -> Parser SType
parseType left = do
    PA.try $ do
        atom <- sAtomParse
        PA.option (foldr (:->:) atom (reverse left)) (do
            PA.spaces
            PA.string "->"
            parseType (atom : left))
    PA.<|> do
            PA.spaces
            PA.char '('
            t <- parseType []
            PA.spaces
            PA.char ')'
            PA.option (foldr (:->:) t (reverse left)) (do
                PA.spaces
                PA.string "->"
                parseType (t:left))
    PA.<?> "Type"

sAtomParse :: Parser SType
sAtomParse = do
        PA.spaces
        start <- PA.lower
        rest <- PA.many (PA.noneOf " ()\t\n\r\f\v.")
        return (SAtom (start:rest))
    PA.<?> "sAtom"

-----------------------------------------------------------------------------
-- ** Type environment


-- | A type environment binds atomic types, represented as Strings to types.
-- In this representation types may be unassigned
type TypeContext v = [(v,SType)]

instance PP (TypeContext VarString) where
    pp          = brackets . ppEnv
    pparser     = parseEnv

instance PP (SType,TypeContext VarString) where
    pp(st,te)   = parens (pp st <> text " , " <> pp te)
    pparser     = do
        PA.char '('
        st <- pparser
        PA.char ','
        te <- pparser
        PA.char ')'
        return (st,te)

ppEnv :: TypeContext VarString -> Doc
ppEnv []           = empty
ppEnv ((ta,tp):tl) = braces (text ta <+> text "=" <+> pp tp) $$ ppEnv tl

parseEnv :: Parser (TypeContext VarString)
parseEnv = do
   PA.char '['
   r <- PA.many parseEnvEntry
   PA.char ']'
   return r

parseEnvEntry :: Parser (VarString,SType)
parseEnvEntry = do
    PA.char '('
    l <- varParse
    PA.char '='
    r <- pparser
    PA.char ')'
    return (l,r)

-- | A substituor binds the type that should be substituted to a type variable
type Substitutor = [(TypeAtom,SType)]

-----------------------------------------------------------------------------
-- ** Helpers

-- | List all type atoms of a type
typeVars :: SType -> [TypeAtom]
typeVars (SAtom n)       = [n]
typeVars (l :->: r)       = typeVars l ++ typeVars r

-- | Apply a substitutor to a type
substituteType :: Substitutor -> SType -> SType
substituteType subst (SAtom a) = case lookup a subst of
                                    Nothing -> (SAtom a)
                                    Just replace -> replace
substituteType subst (l :->: r) = substituteType subst l :->: substituteType subst r

-- | Apply a substitutor to an environment
substituteEnv :: Substitutor -> TypeContext v -> TypeContext v
substituteEnv subst env = map (\(n,t) -> (n,substituteType subst t)) env
