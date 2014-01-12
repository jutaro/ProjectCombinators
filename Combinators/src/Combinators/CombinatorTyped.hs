-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombinatorTyped
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

{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.CombinatorTyped (

) where

import Combinators.Types
       (TypeContext, SType, Typeable(..), typeVarGen, SType(..), Typeable)
import Combinators.Combinator
       (Combinator(..), CTerm(..), CTerm, Basis)
import Combinators.Variable (VarString)
import Combinators.Reduction (TermString(..))

-----------------------------------------------------------------------------
-- ** Combinators

instance Basis b => Typeable (CTerm b) where
    typeof context term = case primTypeOf context (length context) term of
                            Nothing -> Nothing
                            Just (ty,cont,_) -> Just (ty,cont)

    typeof' term =
        let fv = zip (freeVars term) (map (\i -> SAtom (typeVarGen !! i))  [0..])
        in typeof fv term

    typeofC term | not (null (freeVars term)) = error ""
                 | otherwise                = case typeof [] term of
                                                Nothing -> Nothing
                                                Just p -> Just (fst p)


primTypeOf :: Basis b => TypeContext VarString -> Int -> CTerm b -> Maybe (SType, TypeContext VarString, Int)
primTypeOf context ind (Const c) = let (newInd, newType) = primitiveType ind c
                                   in Just (newType,context,newInd)
primTypeOf context ind (Var s)   = case lookup s context of
                                        Nothing -> let newType = SAtom (typeVarGen !! ind)
                                                  in Just (newType,(s,newType):context,ind + 1)
                                        Just nt -> Just (nt,context,ind)
primTypeOf context ind (l :@ r)  = do
                                    (l',cont',ind') <- primTypeOf context ind l
                                    (r',cont'',ind'') <- primTypeOf cont' ind' r
                                    return (l' :->: r',cont'',ind'')

primitiveType :: Int -> Combinator c -> (Int,SType)
primitiveType ind comb = let ((ind',_),t) = replaceVars (ind,[]) (combType comb)
                    in (ind',t)
  where
    replaceVars (ind,binds) (SAtom s) =
        case lookup s binds of
            Nothing -> ((ind + 1,(s,ind):binds),SAtom (typeVarGen !! ind))
            Just i -> ((ind,binds), SAtom (typeVarGen !! i))
    replaceVars (ind,binds) (l :->: r) =
        let ((ind',binds'),l') = replaceVars (ind,binds) l
            ((ind'',binds''),r') = replaceVars (ind',binds') r
        in ((ind'',binds''), l' :->: r')


