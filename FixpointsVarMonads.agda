{-# OPTIONS --type-in-type #-}
module FixpointsVarMonads where

open import AgdaAsciiPrelude.AsciiPrelude
open import Fixpoints public
open import VarMonads public
open import ConstraintProperties

open import Category.Functor using () renaming (RawFunctor to Functor)
open Functor {{...}}

open import Category.Applicative using () renaming (RawApplicative to Applicative)
--open Applicative {{...}}

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

open ConstrBaseVarMonad {{...}}

foldKBVM : {{bvm : ConstrBaseVarMonad K M V}} ->
  {{func : Functor F}} ->
  {{ConservesVar K V}} ->
  KAlgebra K F (M A) -> KFix K (F o V) -> M A
foldKBVM {V = V} alg = KfoldF \ R f [[_]] -> alg (V R) f (read >=> [[_]])
