{-# OPTIONS --type-in-type #-}
module BasicVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

open import BasicVarMonads.BaseVarMonad

private
  variable
    V : Set -> Set

record PolyVar (V : Set -> Set) (A : Set) : Set where
  constructor PV
  field
    C : Set
    CVar : V C
    t : C -> A


PolyVarFunctor : Functor (PolyVar V)
PolyVarFunctor = record { _<$>_ = \{ f (PV C v t) -> PV C v (f o t) } }
