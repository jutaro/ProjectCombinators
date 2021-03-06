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

{-# LANGUAGE DataKinds, GADTs, StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, Rank2Types,
    OverlappingInstances  #-}

module Combinators.Types (
-----------------------------------------------------------------------------
-- * Simple Types
-----------------------------------------------------------------------------
    SType(..),
    TypeAtom,
-----------------------------------------------------------------------------
-- ** Making types optional
    Typed,
    Untyped(..),
-----------------------------------------------------------------------------
-- ** Type inference
    Typeable(..),
    typeVarGen,

-----------------------------------------------------------------------------
-- ** Type contexts and substitution
    TypeContext,
    canonicalizeType,
    canonicalizeTypeContext,
-----------------------------------------------------------------------------
-- ** Type substitution and unification
    Substitution,
    idSubstitution,
    substType,
    substContext,
    unifyTypes,
    unifyTypesR,
-----------------------------------------------------------------------------
-- ** Properties and helpers
    typeVars,
    arityType,
    parseType
) where

import Combinators.BinaryTree
import qualified Text.PrettyPrint as PP (text, sep, parens, Doc)
import qualified Text.Parsec as PA
import Text.Parsec.String (Parser)
import Combinators.Variable (varParse, VarString)
import Text.PrettyPrint
       (($$), (<+>), braces, empty, Doc, text, (<>), parens, brackets)
import Data.Maybe (isJust)
import Debug.Trace (trace)
import Combinators.Reduction (Term(..))
import Combinators.PrintingParsing (PP(..), symbol', parens')
import Control.Arrow (Arrow(..))

-----------------------------------------------------------------------------
-- * Simple Types

-- | A type atom is some type variable
type TypeAtom = String

-- | A simple type is either an atom, or a function type
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

instance Term SType where
    isTerminal (SAtom _)        = True
    isTerminal _                = False
    canonicalize                = canonicalizeType

instance PP SType where
    pp = pp' False
    pparser = parseType []

-----------------------------------------------------------------------------
-- ** Making types optional

-- | A class that has instances for untyped, simple types and maybe other types.
--   This can be used to uniformly represent terms of different kinds
class Eq t => Typed t where

-- | A type that represents an untyped behavior
data Untyped = Untyped
    deriving (Eq,Ord,Show)

instance Typed Untyped where

-- | A type that represents a behavior with simple types
instance Typed SType where

-----------------------------------------------------------------------------
-- * Type inference

-- | A class that describe a possible Typeable Term
class Typeable t where
    typeof :: TypeContext VarString -> t -> Maybe (SType, TypeContext VarString)
    -- ^ Infers just the simple type and environment of a Term or returns Nothing,
    -- if the term is not typeable.
    typeof' :: t -> Maybe (SType, TypeContext VarString)
    -- ^ Infers just the simple type and environment of a Term or returns Nothing,
    -- if the term is not typeable.
    typeofC :: t -> Maybe SType
    -- ^ Infers just the simple type of a closed Term or returns Nothing, if the
    -- term is not typeable
    isTypeable :: t -> Bool
    isTypeable t =  isJust (typeof' t)
    -- ^ Is this a typeable term

-- | Generate an endless stream of type variables:
--
-- >> "a b c d e f g a1 b1 c1 d1 e1 f1 g1 a2 ..."
typeVarGen :: [String]
typeVarGen = [c : n | n <- "" : map show [(1 :: Int) ..], c <- "abcdefg"]

-- | Name type variables in a type in a canonical way
canonicalizeType :: SType -> SType
canonicalizeType t = (\(_,_,r) -> r) $ canonicalizeType' 0 [] t

canonicalizeType' :: Int -> [(String,Int)] -> SType -> (Int, [(String,Int)], SType)
canonicalizeType' i env (SAtom s) =
    case lookup s env of
        Just ind ->  (i,env,SAtom (typeVarGen !! ind))
        Nothing -> (i+1,(s,i):env,SAtom (typeVarGen !! i))
canonicalizeType' i env (l :->: r) =
    let (i',env',l')   = canonicalizeType' i env l
        (i'',env'',r') = canonicalizeType' i' env' r
    in (i'',env'',l' :->: r')

-- | Name type variables in a type with a context in a canonical way
canonicalizeTypeContext :: (SType,TypeContext a) -> (SType,TypeContext a)
canonicalizeTypeContext (t,enviro) =
    let (index,env,res) = canonicalizeType' 0 [] t
        (_,_,res'') = foldr (\(k,t) (i,env,newEnv) ->
                                let (index',env',res') = canonicalizeType' i env t
                                in (index',env',(k,res') : newEnv))
                            (index,env,[]) enviro
    in (res,res'')


-----------------------------------------------------------------------------
-- ** Printing and parsing



pp' :: Bool -> SType -> PP.Doc
pp' True (a :->: b)   = PP.parens (pp' False (a :->: b))
pp' False (a :->: b)  = PP.sep [pp' True a, PP.text "->", pp' False b]
pp' _ (SAtom s)      = PP.text s

parseType :: [SType] -> Parser SType
parseType left = do
    PA.spaces
    PA.try $ do
        atom <- sAtomParse
        PA.option (foldr (:->:) atom (reverse left)) (do
            symbol' "->"
            parseType (atom : left))
    PA.<|> do
            t <- parens' (parseType [])
            PA.option (foldr (:->:) t (reverse left)) (do
                symbol' "->"
                parseType (t:left))
    PA.<?> "Type"

sAtomParse :: Parser SType
sAtomParse = do
        PA.spaces
        start <- PA.lower
        rest <- PA.many (PA.noneOf " :;,()[]\t\n\r\f\v.")
        PA.spaces
        return (SAtom (start:rest))
    PA.<?> "sAtom"

-----------------------------------------------------------------------------
-- ** Type contexts

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

-----------------------------------------------------------------------------
-- ** Type substitution and unification

-- | A substition binds the type that should be substituted to a type
type Substitution = [(String,SType)]

-- | The identity substitution
idSubstitution :: Substitution
idSubstitution = []

-- | Add a new substitutor to a substitution
updateSubst  :: (String, SType) -> Substitution -> Substitution
updateSubst (atom,typ) subst = (atom,typ):subst

-- | Apply a substitutor to a type
substType :: Substitution -> SType -> SType
substType s typ = foldr (\  (subs,repl) t -> substType' (subs,repl) t) typ s
  where
    substType' (subs,repl) (t1 :->: t2) = substType' (subs, repl) t1 :->: substType' (subs, repl) t2
    substType' (subs,repl) (SAtom x) | x == subs         = repl
                                     | otherwise         = SAtom x

-- | Apply a substitutor to an environment
substContext :: Substitution -> TypeContext v -> TypeContext v
substContext subst = map (second (substType subst))

-- | List all type atoms of a type
typeVars :: SType -> [TypeAtom]
typeVars (SAtom n)       = [n]
typeVars (l :->: r)       = typeVars l ++ typeVars r

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
-- Equal type var names in both STypes means equal types in both formulars,
-- if you dont want these use unifyTypesR
unifyTypes, unifyTypes' :: Bool -> SType -> SType -> Maybe Substitution
unifyTypes' _ t1 t2       | t1 == t2                   = Just idSubstitution
unifyTypes' _ (SAtom s) b | s `notElem` typeVars b  = Just (updateSubst (s,b) idSubstitution)
                          | otherwise                  = Nothing
unifyTypes' b(l :->: r) (SAtom s)                       = unifyTypes b (SAtom s) (l :->: r)
unifyTypes' b (l1 :->: r1) (l2 :->: r2)                = do
    s1 <- unifyTypes b l1 l2
    s2 <- unifyTypes b (substType s1 r1) (substType s1 r2)
    return (s2 ++ s1)

unifyTypes b t1 t2 =
    let res = if b
                then trace ("unifyTypes t1: " ++ pps t1 ++ " t2: " ++ pps t2) $
                        unifyTypes' b t1 t2
                else unifyTypes' b t1 t2
         in if b
            then trace ("unifyTypes res: " ++ show res) res
            else res

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
-- Equal type var names in both STypes gets renamed in the second formula before unification
unifyTypesR :: Bool -> SType -> SType -> (SType,Maybe Substitution)
unifyTypesR trace type1 type2 =
    let varNames = typeVars type1
        renamed = renameType type2 varNames
    in (renamed, unifyTypes trace type1 renamed)
  where
    renameType (SAtom s) atomList | s `elem` atomList = renameType (SAtom (s++"'")) atomList
                                  | otherwise       = SAtom s
    renameType (l :->: r) atomList                   = renameType l atomList :->: renameType r atomList

-----------------------------------------------------------------------------
-- ** Properties

arityType :: SType -> Int
arityType t = arityType' t - 1
  where
    arityType' (SAtom _ )  = 1
    arityType' (_l :->: r) = 1 + arityType' r
