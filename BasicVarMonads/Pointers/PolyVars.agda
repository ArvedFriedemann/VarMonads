{-# OPTIONS --type-in-type #-}
module BasicVarMonads.Pointers.PolyVars where

open import AgdaAsciiPrelude.AsciiPrelude
open import MTC.MTCBijective

private
  variable
    V : Set -> Set

record PolyVar (V : Set -> Set) (A : Set) : Set where
  constructor PV
  field
    Orig : Set
    CVar : V Orig
    t : Orig <-*-> A
  open _<-*->_ t public


PolyVarFunctor : BijFunctor (PolyVar V)
PolyVarFunctor = record { _<$>_ = \{ f (PV C v t) -> PV C v (f <o> t) } }
