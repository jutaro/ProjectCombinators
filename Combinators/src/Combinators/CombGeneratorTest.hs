-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombGeneratorTest
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL (Just (Version {versionBranch = [2], versionTags = []}))
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Combinators.CombGeneratorTest where

import Combinators.CombGenerator
import Combinators.Combinator
import Combinators.Variable

import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)

-- * Testing
prop_rankTreeStruct :: Int -> Integer -> Bool
prop_rankTreeStruct n m =
                  if n > 0 && n < 25 && m > 1 && m <= (catalans !! n)
                    then let ts = unrankTreeStruct n m
                         in rankTreeStruct ts == m
                    else True

prop_grankTreeStruct :: Integer -> Bool
prop_grankTreeStruct n =
                  if n > 0
                    then let ts = gunrankTreeStruct n
                         in grankTreeStruct ts == n
                    else True

-- * Testing
prop_gfunc :: Int -> Int -> Bool
prop_gfunc n m =
    if n >= 1 && n < 20 && m >= 1 && m < n
        then
            let table = initGFuncTable (max n m)
            in gfunc n m  == gfunc' table n m
        else True

-- * Testing
prop_TreeGen :: Int -> Bool
prop_TreeGen n =  if n >= 1 && n < 15
                    then  length (genBinaryTreeStructs n) == fromIntegral (catalans !! n)
                    else True

-- * Testing
prop_CombGen :: Int -> Bool
prop_CombGen n =  if n >= 1 && n < 10
                    then  fromIntegral (length (genCombsN n :: [CTerm KS VarString])) ==
                            (sizeGenCombsN (undefined :: KS) !! n)
                    else True

testCombGenerator :: [Test]
testCombGenerator = [testProperty "prop_TreeGen" prop_TreeGen,
                        testProperty "prop_CombGen" prop_CombGen,
                        testProperty "prop_gfunc" prop_gfunc,
                        testProperty "prop_rankTreeStruct" prop_rankTreeStruct,
                        testProperty "prop_grankTreeStruct" prop_grankTreeStruct
                        ]



