-----------------------------------------------------------------------------
--
-- Module      :  BenchCigol
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- | Benchmarks for the cigol package
--
-----------------------------------------------------------------------------

module Main where

import Criterion.Config
import Criterion.Main
import Combinators
import Control.Seq

myConfig :: Config
myConfig = defaultConfig

parseIKS :: String -> CTerm IKS
parseIKS = pparse


main :: IO ()
main = defaultMainWith myConfig (return ()) [
          bench "parse1" $ whnf parseIKS t1,
          bench "parse2" $ whnf parseIKS t2,
          bench "parse3" $ whnf parseIKS t3,

          bench "pp1" $ whnf pp (withStrategy rseq (parseIKS t1)),
          bench "pp2" $ whnf pp (withStrategy rseq (parseIKS t2)),
          bench "pp3" $ whnf pp (withStrategy rseq (parseIKS t3)),

          bench "pprint1" $ whnf pps (withStrategy rseq (parseIKS t1)),
          bench "pprint2" $ whnf pps (withStrategy rseq (parseIKS t2)),
          bench "pprint3" $ whnf pps (withStrategy rseq (parseIKS t3)),

          bench "red1" $ whnf reduceSForce (withStrategy rseq (parseIKS t1)),
          bench "red2" $ whnf reduceSForce (withStrategy rseq (parseIKS t2)),
          bench "red3" $ whnf reduceSForce (withStrategy rseq (parseIKS t1))
        ]

t1, t2, t3 :: String
t1 = "S(K K)(S(S(K S)(S(K K)(S K K)))(K(S K K))) x y z"
t2 = "S(K K)(S(S(K S)(S(K K)(S K K)))(K(S K K))) x y z"
t3 = "S(S(K S)(S(K K)(S(K S)(S(K(S(K S)))S))))(K S) x y z u"
