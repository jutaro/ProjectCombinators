{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.CombGeneratorTest
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

module Combinators.CombGeneratorTest where

import Combinators.CombGenerator
import Combinators.Combinator

import Test.Framework (Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Control.Monad (liftM2, liftM)

instance Arbitrary (CTerm KS) where
    arbitrary = frequency
        [(7,liftM Const (elements primCombs)),
            (3,liftM2 (:@) arbitrary arbitrary)]

prop_rankTreeStruct :: Int -> Integer -> Bool
prop_rankTreeStruct n m =
                  not (n > 0 && n < 25 && m > 1 && m <= (catalans !! n)) ||
                     (let ts = unrankTreeStruct n m in rankTreeStruct ts == m)

prop_grankTreeStruct :: Integer -> Bool
prop_grankTreeStruct n =
                  (n <= 0) ||
                     (let ts = gunrankTreeStruct n in grankTreeStruct ts == n)


prop_TreeGen :: Int -> Bool
prop_TreeGen n =  not (n >= 1 && n < 15) ||
                     (length (genBinaryTreeStructs n) == fromIntegral (catalans !! n))

prop_CombGen :: Int -> Bool
prop_CombGen n =  not (n >= 1 && n < 10) ||
                     (fromIntegral (length (genCombsN n :: [CTerm KS])) ==
                        (sizeGenCombsN (undefined :: KS) !! n))

prop_RankGen :: CTerm KS -> Bool
prop_RankGen t =  let ind = rankComb t
                  in -- trace ("prop_RankGen t: " ++ show t ++ " index: " ++ show ind) $
                    ((ind > 10000) ||
                        (head (take 1 (drop (fromIntegral (ind - 1)) genCombs)) == t))

prop_RankUnrank :: CTerm KS -> Bool
prop_RankUnrank t = let ind = rankComb t
                    in -- trace ("prop_RankUnrank t: " ++ show t ++ " index: " ++ show ind) $
                        ((ind > 1000000) || (unrankComb ind == t))


testCombGenerator :: [Test]
testCombGenerator = [testProperty "prop_TreeGen" prop_TreeGen
                        ,testProperty "prop_CombGen" prop_CombGen
                        ,testProperty "prop_rankTreeStruct" prop_rankTreeStruct
                        ,testProperty "prop_grankTreeStruct" prop_grankTreeStruct
                        ,testProperty "prop_RankGen" prop_RankGen
                        ,testProperty "prop_RankUnrank" prop_RankUnrank
                        ]



