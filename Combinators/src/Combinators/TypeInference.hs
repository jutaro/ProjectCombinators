-----------------------------------------------------------------------------
--
-- Module      :  Combinators.TypeInference
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

{-# LANGUAGE FlexibleInstances, DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.TypeInference (
    Typeable(..),
--    genList
) where

import Combinators.BinaryTree (PP(..))
import Combinators.Reduction
import Combinators.Lambda
import Combinators.Variable
import Combinators.Types


-- import Debug.Trace (trace)
trace :: a -> b -> b
trace _ s = s




{-
-- genList :: Int -> [(String, String, String, String, String)]
genList n = map (\c ->
                    let reducedCombinator = reduceIt instrumentedContext NormalForm c
                        lambda            = combToLambda reducedCombinator
                        reducedLambda     = reduceIt instrumentedContext NormalForm (toLambdaB lambda)
                        itype             = inferSType lambda
                    in (pps c,pps reducedCombinator{-,pps lambda, pps reducedLambda,pps itype-} ))
                $ take n (genCombs :: [CTerm KS])
-}

-----------------------------------------------------------------------------
-- ** Combinators

{-
instance Basis b => Typeable (CTerm b) where
    inferSType comb = snd $ inferSType' (0,[]) comb

primType :: Int -> Combinator c -> (Int,SType)
primType ind comb = let ((ind',_),t) = replaceVars (ind,[]) (combType comb)
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



inferSType' :: Basis b => (Int,[(String,Int)]) -> CTerm b -> ((Int,[(String,Int)]),SType)
inferSType' (ind,binds) (Const c) = let (newInd, newType) = primType ind c
                                    in ((newInd,binds),newType)
inferSType' (ind,binds) (Var s)   = case lookup s binds of
                                        Nothing -> ((ind + 1,(s,ind):binds),SAtom (typeVarGen !! ind))
                                        Just i -> ((ind,binds), SAtom (typeVarGen !! i))
inferSType' (ind,binds) (l :@ r)  = let ((ind',binds'),l') = inferSType' (ind,binds) l
                                        ((ind'',binds''),r') = inferSType' (ind',binds') r
                                    in ((ind'',binds''), l' :->: r')

unifyTypes :: SType -> SType -> Maybe ([String,SType], SType)
unifyTypes = unifyTypes' []
  where
    unifyTypes' env l (Var r)           =   case lookup r env of
                                                Nothing -> (r,l):env
                                                Just t -> unifyTypes' env l t
    unifyTypes' env (Var l) (r1 :@ r2)  =   case lookup r env of
                                                Nothing -> (r,l):env
                                                Just t -> unifyTypes' env l t
-}

