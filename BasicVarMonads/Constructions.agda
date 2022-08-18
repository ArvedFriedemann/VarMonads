{-# OPTIONS --type-in-type #-}
module BasicVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

open import BasicVarMonads.BaseVarMonad

open import MTC.MTCBijective

private
  variable
    A B C : Set
    F M V : Set -> Set

record PolyVar (V : Set -> Set) (A : Set) : Set where
  constructor PV
  field
    Orig : Set
    CVar : V Orig
    t : Orig <-*-> A
  open _<-*->_ t public


PolyVarFunctor : BijFunctor (PolyVar V)
PolyVarFunctor = record { _<$>_ = \{ f (PV C v t) -> PV C v (f <o> t) } }

open BaseVarMonad {{...}}

BVMToPolyVar : {{bvm : BaseVarMonad M V}} -> BaseVarMonad M (PolyVar V)
BVMToPolyVar = record {
  new = \ {A} a -> (\v -> PV A v (id <,> id)) <$> new a ;
  read = \ {(PV A v (to <,> _)) -> to <$> read v } ;
  write = \ {(PV A v ( _ <,> from)) k -> write v (from k)} }
