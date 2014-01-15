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
    Typed,
    Untyped(..),
    typeVarGen,
    canonicalizeType,
    canonicalizeTypeContext,
    TypeContext,
    Substitutor,
    substituteType,
    substituteContext,
    unifyTypes,
    unifyTypesR,
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
import Data.Maybe (isJust)
import Debug.Trace (trace)

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

-- | Generate an endless stream of type variables
typeVarGen :: [String]
typeVarGen = [ c: n | n <- ("" : map show [(1:: Int)..]), c <- "abcdefg"]

-- | Name type variables in a type in a canonical way
canonicalizeType :: SType -> SType
canonicalizeType t = (\(_,_,r) -> r) $ canonicalizeType' 0 [] t

-- | Name type variables in a type with a context in a canonical way
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

-----------------------------------------------------------------------------
-- ** Type substitution and unification

-- | A substituor binds the type that should be substituted to a type
type Substitutor = [(TypeAtom,SType)]

-- | Apply a substitutor to a type
substituteType :: Substitutor -> SType -> SType
substituteType subst (SAtom a) = case lookup a subst of
                                    Nothing -> (SAtom a)
                                    Just replace -> replace
substituteType subst (l :->: r) = substituteType subst l :->: substituteType subst r

-- | Apply a substitutor to an environment
substituteContext :: Substitutor -> TypeContext v -> TypeContext v
substituteContext subst env = map (\(n,t) -> (n,substituteType subst t)) env

substituteSubstitutor :: Substitutor -> Substitutor -> Substitutor
substituteSubstitutor subsAppliable subsToApply =
    map (\ (fst,t) -> (fst, substituteType subsAppliable t)) subsToApply

-- | List all type atoms of a type
typeVars :: SType -> [TypeAtom]
typeVars (SAtom n)       = [n]
typeVars (l :->: r)       = typeVars l ++ typeVars r

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
-- Equal type var names in both STypes means equal types in both formulars,
-- if you dont want these use unifyTypesR
unifyTypes, unifyTypes' :: SType -> SType -> Maybe Substitutor
unifyTypes' t1 t2       | t1 == t2                   = Just []
unifyTypes' (SAtom s) b | not (elem s (typeVars b))   = Just [(s,b)]
                       | otherwise                 = Nothing
unifyTypes' (l :->: r) (SAtom s)                     = unifyTypes (SAtom s) (l :->: r)
unifyTypes' (l1 :->: r1) (l2 :->: r2)                 =
    case unifyTypes r1 r2 of
        Nothing -> Nothing
        Just substr ->
            case unifyTypes (substituteType substr l1)
                       (substituteType substr l2) of
                Nothing -> Nothing
                Just substl -> Just (substl ++ (substituteSubstitutor substl substr))

unifyTypes t1 t2 = let res = unifyTypes' t1 t2
                   in trace ("unifyTypes t1: " ++ pps t1 ++ " t2: " ++ pps t2 ++ " res: " ++ show res)
                        res

-- | Unify two types and returns just a substitution if possible,
-- and Nothing if it is not possible
-- Equal type var names in both STypes gets renamed in the second formula
unifyTypesR :: SType -> SType -> (SType,Maybe Substitutor)
unifyTypesR type1 type2 =
    let varNames = typeVars type1
        renamed = renameType type2 varNames
    in (renamed, unifyTypes type1 renamed)
  where
    renameType (SAtom s) atomList | elem s atomList = renameType (SAtom (s++"'")) atomList
                                  | otherwise       = (SAtom s)
    renameType (l :->: r) atomList                   = renameType l atomList :->: renameType r atomList

