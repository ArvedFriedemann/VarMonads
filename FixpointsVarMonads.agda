{-# OPTIONS --type-in-type #-}
module FixpointsVarMonads where

open import AgdaAsciiPrelude.AsciiPrelude
open import Fixpoints
open import VarMonads

open import Category.Functor using () renaming (RawFunctor to Functor)
open Functor {{...}} --renaming (_<$>_ to _<$>'_)

open import Category.Applicative using () renaming (RawApplicative to Applicative)
--open Applicative {{...}}

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

record Traversable (T : Set -> Set) : Set where
  field
    traverse : {{apl : Applicative F}} ->
      (A -> F B) -> T A -> F (T B)
    sequenceA : {{apl : Applicative F}} ->
      T (F A) -> F (T A)
open Traversable {{...}}

open ConstrBaseVarMonad {{...}}

--seems to have to be an MAlgebra at this point...
foldBVM : {{bvm : BaseVarMonad M V}} ->
  {{func : Functor F}} ->
  {{tr : Traversable F}} ->
  Algebra F (M A) -> Fix (F o V) -> M A
foldBVM {V = V} alg = foldF \ R f [[_]] -> alg (V R) f (read >=> [[_]])
