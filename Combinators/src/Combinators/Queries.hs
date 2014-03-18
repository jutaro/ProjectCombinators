-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Queries
-- Copyright   :  All rights reserved, Jürgen Nicklisch-Franken
-- License     :  GPL 2.0
--
-- Maintainer  :  Jürgen Nicklisch-Franken
-- Stability   :  provisional
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Combinators.Queries
where

import Combinators.Reduction
       (NormalOrder(..), instrumentedContext, reduce, reduceS, Term(..))
import Combinators.CombLambda (combToLambda)
import Combinators.Lambda
       (arityLambda, fromLambdaB, toLambdaB)
import Combinators.CombGenerator
       (sizeGenCombsN, unrankComb, genCombs)
import Combinators.Combinator (CTerm(..), Basis, CTerm)
import Combinators.Types (canonicalizeType, Typeable(..))
import Combinators.LambdaTyped ()
import Combinators.Variable (nameGen)
import Combinators.Properties
       (notProper, isRegular, isPermutator, isAssociator,
        isDuplicator, isCancelator, isIdentity)

import Data.List (intercalate)
import Control.Monad (liftM)
import qualified Text.PrettyPrint as PP
       (sep, ($+$), Doc, render, (<+>), text, empty, int)
import System.IO
       (hFlush, hClose, stderr, hPutStr, hPutStrLn, openFile)
import GHC.IO.IOMode (IOMode(..))
import Control.Seq (rseq, withStrategy)
import Control.Exception (bracket)
import Combinators.PrintingParsing (PP(..))

-----------------------------------------------------------------------------
-- * Queries
-----------------------------------------------------------------------------

findComb :: forall b. Basis b => Int -> Int -> (CTerm b-> Bool) -> CSV
findComb from to decision = go fromNum
  where
    go current | current > toNum = []
               | otherwise       = let comb = unrankComb current
                                   in if decision comb
                                        then [show current, pps comb] : go (current + 1)
                                        else go (current + 1)
    fromNum = 1+sum (take (from - 1) (sizeGenCombsN (undefined :: b)))
    toNum = sum (take to (sizeGenCombsN (undefined :: b)))

isI :: Basis b => CTerm b -> Bool
isI t = let term' = t :@ Var "x"
        in reduceS term' == Just (Var "x")

isK :: Basis b => CTerm b -> Bool
isK t = let term' = t :@ Var "x" :@ Var "y"
        in reduceS term' == Just (Var "x")

isS :: Basis b => CTerm b -> Bool
isS t = let term' = t :@ Var "x" :@ Var "y" :@ Var "z"
        in reduceS term' == Just (Var "x":@ Var "z" :@ (Var "y":@ Var "z"))

genList :: forall b . (Basis b, Typeable (CTerm b)) => b -> Int -> CSV
genList _ n =  map (map PP.render) $ headers : map presentIt (filter filterIt genIt)

  where
    genIt = map (\c -> case reduceAndType c of
                        Just tupel -> Left tupel
                        Nothing -> Right c)
                            $ take n (genCombs :: [CTerm b])
    reduceAndType c = do
        reducedCombinator <- reduceS c
        let lambda =  canonicalize $ combToLambda c
            lambda2 = canonicalize $ combToLambda reducedCombinator
        reducedLambda1 <- liftM (canonicalize . fromLambdaB) (reduceS (toLambdaB lambda))
        reducedLambda2 <- liftM (canonicalize . fromLambdaB) (reduceS (toLambdaB lambda2))
        let condItype             = liftM canonicalize $ typeofC lambda
            condItype2            = liftM canonicalize $ typeofC reducedLambda1
            condCtype             = liftM canonicalize $ typeofC c
            condCtype2            = liftM canonicalize $ typeofC reducedCombinator
        return (c,reducedCombinator,lambda,lambda2,reducedLambda1,reducedLambda2,
                condItype,condItype2,condCtype,condCtype2)

    headers = [PP.text "Comb", PP.text "Reduct", PP.text "Lambda", PP.text "SType", PP.text "Remarks",
                PP.text "ArityT", PP.text "ArityC", PP.text "Properties"]


    presentIt (Right c) = let condCType = liftM canonicalizeType $ typeofC c
                              lambda =  canonicalize $ combToLambda c
                              condLambdaRed = reduceS (toLambdaB lambda)
                              lambdaReal = case condLambdaRed of
                                            Nothing -> lambda
                                            Just lr -> fromLambdaB lr
                              arityT = arityLambda lambda
                              reportReduce' = reportReduce c
                          in [pp c, reportReduce' ,pp lambdaReal,pp condCType,PP.empty,PP.int arityT,
                                reportProperties arityT c PP.<+> PP.text "Reduce failed"]

    presentIt (Left (c,_reducedCombinator,_lambda,_lambda2,reducedLambda1,_reducedLambda2,
                            condItype,condItype2,condCtype,condCtype2))
                      = let (ptype,typeRemark) = if (condCtype == condItype)
                                && (condCtype == condItype2)
                                && (condCtype == condCtype2)
                                then (condCtype,PP.empty)
                                else
                                    let remark1 =  if condCtype /= condCtype2 then
                                                      PP.text "Red. Comb" PP.<+> pp condCtype2 else PP.empty
                                        remark2 =  if condCtype /= condItype then
                                                      PP.text "Raw Lambda" PP.<+> pp condItype else PP.empty
                                        remark3 =  if condCtype /= condItype2 then
                                                      PP.text "Red. Lambda " PP.<+> pp condItype2 else PP.empty
                                        remark = remark1 PP.<+> remark2 PP.<+> remark3

                                    in  (condCtype,remark)
                            arityT = arityLambda reducedLambda1
                            (ct,reduct) = let cterm = foldl (:@) c (map Var $ take arityT nameGen)
                                          in (Just cterm,reduceS cterm)
                        in  [pp c, pp ct PP.<+> PP.text "=" PP.<+> pp reduct,pp reducedLambda1,pp ptype,typeRemark,
                                PP.int arityT,reportProperties arityT c]

    -- Give a report for failed reductions
    reportReduce c = case reduce instrumentedContext NormalOrder 150 c of
                        (Just reduct,_,_,_) -> PP.text "Wonder" PP.<+> pp reduct
                        (Nothing,rep,_steps,li) -> PP.text (rep "") PP.$+$ PP.sep (map pp (take 5 (reverse li)))

    filterIt  (Right _c)          = True
    filterIt  (Left (c,reducedCombinator,_lambda,_lambda2,_reducedLambda1,_reducedLambda2,
                            _condItype,_condItype2,_condCtype,_condCtype2))
                                 = reducedCombinator == c

reportProperties :: Basis b => Int -> CTerm b -> PP.Doc
reportProperties i c =
    foldl (\ accu (f,s)  -> (case f i c of
                        Just True -> (PP.<+> PP.text s)
                        _ -> id) accu)
                        PP.empty
                        [(isCancelator,"Cancelator"),
                         (isIdentity,"Identity"),
                         (isDuplicator,"Duplicator"),
                         (isAssociator,"Associator"),
                         (isPermutator,"Permutator"),
                         (isRegular,"Regular"),
                         (notProper,"NotProper")]

-- ** CSV Export

-- | A CSV file is a series of records. According to the RFC, the
-- records all have to have the same length. As an extension, I
-- allow variable length records.
type CSV = [Record]

-- | A record is a series of fields
type Record = [Field]

-- | A field is a string
type Field = String

-- | Given an object of type CSV, generate a CSV formatted
-- string. Always uses escaped fields.
printCSV :: CSV -> String
printCSV records = unlines (printRecord `map` records)
    where printRecord = intercalate ";" . map printField
          printField f = "\"" ++ concatMap escape f ++ "\""
          escape '"' = "\"\""
          escape x = [x]

-- | Given an object of type CSV, generate a CSV formatted
-- string. Always uses escaped fields.
printCSVUnescaped :: CSV -> String
printCSVUnescaped records = unlines (printRecord `map` records)
    where printRecord = intercalate ";" . map printField
          printField f = f

-- e.g  writeCSV "KS-1000.csv" $ genList KS 1000

writeCSV :: String -> CSV -> IO ()
writeCSV fileName csv =
    bracket
        (openFile fileName WriteMode)
        (\hnd -> do
            hClose hnd
            putProgress "")
        (\hnd -> writeIt hnd csv (1:: Int))
  where
    writeIt hnd (hd:tl) i = do
        let line = withStrategy rseq (printRecord hd)
        hPutStrLn hnd line
        hFlush hnd
        putProgress $ "line: " ++ show i
        writeIt hnd tl (i+1)
    writeIt _hnd [] _i = return ()
    putProgress s = hPutStr stderr $ "\r\ESC[K" ++ s
    printRecord = intercalate ";" . map printField
    printField f = "\"" ++ concatMap escape f ++ "\""
    escape '"' = "\"\""
    escape x = [x]


