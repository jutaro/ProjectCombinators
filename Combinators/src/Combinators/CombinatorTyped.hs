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
    reconstructTypeC
) where

import Combinators.Types
       (substType, substContext, unifyTypes, TypeContext,
        Typeable(..), typeVarGen, SType(..),)
import Combinators.Combinator
       (Combinator(..), CTerm(..), CTerm, Basis)
import Combinators.Variable (VarString)
import Combinators.Reduction (TermString(..))
import Debug.Trace (trace)
import Combinators.PrintingParsing (PP(..))

-----------------------------------------------------------------------------
-- ** Combinators

instance Basis b => Typeable (CTerm b) where
    typeof context term = case reconstructTypeC False context (length context) term of
                            Nothing -> Nothing
                            Just (ty,cont,_) -> Just (ty,cont)
    typeof' term =
        let fv = zip (freeVars term) (map (\i -> SAtom (typeVarGen !! i))  [0..])
        in typeof fv term
    typeofC term | not (null (freeVars term)) = error ("CombinatorTyped>>typeOfC: Term not closed: " ++ pps term)
                 | otherwise                = case typeof [] term of
                                                Nothing -> Nothing
                                                Just p -> Just (fst p)


reconstructTypeC, reconstructType' :: Basis b => Bool -> TypeContext VarString -> Int -> CTerm b -> Maybe (SType, TypeContext VarString, Int)
reconstructType' _ cont ind (Const c) =
    let (newInd, newType) = primitiveType ind c
    in Just (newType,cont,newInd)
reconstructType' _ cont ind (Var s)   =
    case lookup s cont of
        Nothing -> let newType = SAtom (typeVarGen !! ind)
                  in Just (newType,(s,newType):cont,ind + 1)
        Just nt -> Just (nt,cont,ind)
reconstructType' b cont ind (l :@ r)  = do
    (l',cont',ind') <- reconstructTypeC b cont (ind+1) l
    (r',("_res",l''):cont'',ind'') <- reconstructTypeC b (("_res",l'):cont') ind' r
    case l'' of
        SAtom _ ->  do
            let newType = SAtom $ typeVarGen !! ind
            subst <- unifyTypes b l'' (r' :->: newType)
            let newCont = substContext subst cont''
                newType' = substType subst newType
            return (newType',newCont,ind'')
        (ll :->: lr) -> do
            subst <- unifyTypes b ll r'
            let newCont  = substContext subst cont''
                newType' = substType subst lr
            return (newType',newCont,ind'')

reconstructTypeC traceIt cont ind t =
    let res = if traceIt
                then
                    trace ("reconstructType cont: " ++ show cont ++ " t: " ++ pps t) $
                        reconstructType' traceIt cont ind t
                else
                    reconstructType' traceIt cont ind t
    in if traceIt
            then trace ("reconstructType res: " ++ show res) $ res
            else res


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

