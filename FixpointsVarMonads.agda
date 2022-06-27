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

open ConstrBaseVarMonad {{...}}

--seems to have to be an MAlgebra at this point...
foldKBVM : {{bvm : ConstrBaseVarMonad K M V}} ->
  {{func : Functor F}} ->
  {{kv : forall {R} -> {{kr : K R}} -> K (V R)}} ->
  KAlgebra K F (M A) -> KFix K (F o V) -> M A
foldKBVM {V = V} alg = KfoldF \ R f [[_]] -> alg (V R) f (read >=> [[_]])
