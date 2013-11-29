{-# LANGUAGE EmptyDataDecls, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC  #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Basis
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Alternative basis for Combinatory logic
--
-----------------------------------------------------------------------------

module Combinators.CombinatorBasis where

import Combinators.Combinator
import Combinators.Variable



data BCKW

-- | Definition of the combinators for the IKS Basis
bBCKW, cBCKW, kBCKW, wBCKW :: Variable v => Combinator BCKW v

bBCKW = Combinator "B" [varString "__x",varString "__y",varString "__z"]
            (Var (varString "__x") :@ (Var (varString "__y") :@ Var (varString "__z")))
cBCKW = Combinator "C" [varString "__x",varString "__y",varString "__z"]
            ((Var (varString "__x") :@ Var (varString "__z")) :@ Var (varString "__y"))
kBCKW = Combinator "K" [varString "__x", varString "__y"]
            (Var (varString "__x"))
wBCKW = Combinator "W" [varString "__x", varString "__y"]
            (Var (varString "__x") :@ Var (varString"__y") :@ Var (varString "__y"))


instance Variable v => Basis BCKW v where
    primCombs = [bBCKW, cBCKW, kBCKW, wBCKW]

parseBCKW :: String -> CTerm BCKW VarString
parseBCKW = parse :: String -> CTerm BCKW VarString
