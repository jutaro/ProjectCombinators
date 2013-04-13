{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
--
-- Module      :  Combinators.Lambda
-- Copyright   :  Jürgen <jutaro> Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- Maintainer  :  
-- Stability   :  
-- Portability :  
--
-- | Lambda calculus implementation
--
-----------------------------------------------------------------------------

module Combinators.Lambda where

import Combinators.Language
import qualified Text.PrettyPrint as PP
import Test.QuickCheck (Arbitrary(..), elements, oneof, sized)
import Control.Monad (liftM, liftM2)

-----------------------------------------------------------------------------
-- * Basic types

-- | A 'Term' in lambda calculus is either
--
-- * a variable
-- * an application
-- * a lambda abstraction
--
-- Problems here:
-- * How to represent variables? Do we prefer Strings or de Bruijn?
--      we choose to parametrize on the type of variables, which is a something of class Variable
 
data Variable v => LTerm v =
      LVar v
    | LTerm v :@: LTerm v
        -- ^ Bind application to the left.
    | v :.: LTerm v
     deriving (Eq, Show)

-- Bind application to the left.
infixl 5 :@:
-- Bind abstraction to the left.
-- FIXME
infixl 5 :.:

-----------------------------------------------------------------------------
-- * Priniting and parsing

-- | Pretty prints a lambda term.
--
-- Avoids printing outer parenthesis and left parenthesis.
pp :: Variable v => LTerm v -> String
pp t = PP.render (pp' False t)

pp' :: Variable v => Bool -> LTerm v -> PP.Doc
pp' _ (LVar v)       = PP.text (varPp v)
pp' False (l :@: r)  = PP.sep [pp' False l, pp' True r]
pp' True (l :@: r)   = PP.text "("  PP.<> PP.sep [pp' False l, pp' True r] PP.<> PP.text ")"

pp' _ (v :.: t)  = PP.text "\\" PP.<> PP.text (varPp v) PP.<> PP.text "." PP.<> pp' False t 
 
 
instance Arbitrary (LTerm VarString) where
    arbitrary = sized $ \_n -> oneof
        [liftM LVar (elements ["u","v","w","x","y","z"]),
         liftM2 (:@:) arbitrary arbitrary,
         liftM2 (:.:) (elements ["u","v","w","x","y","z"]) arbitrary]
            
