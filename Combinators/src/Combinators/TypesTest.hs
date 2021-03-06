-----------------------------------------------------------------------------
--
-- Module      :  Combinators.TypesTest
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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Combinators.TypesTest where

import Combinators.Types (SType(..))

import Test.QuickCheck
       (frequency, elements, Arbitrary)
import Control.Monad (liftM2, liftM)
import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Combinators.PrintingParsing (PP(..))

instance Arbitrary SType where
    arbitrary = frequency
        [(8,liftM SAtom (elements ["a","b","c","d","e","f"])),
         (6,liftM2 (:->:) arbitrary arbitrary)]

--  For any term: print and parse give the original term
prop_printParse :: SType -> Bool
prop_printParse stype = stype == pparse (pps stype)

testTypes :: [Test]
testTypes = [testProperty "prop_printParse" prop_printParse
            ]

