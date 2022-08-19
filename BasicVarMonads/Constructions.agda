{-# OPTIONS --type-in-type #-}
module BasicVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

open import BasicVarMonads.BaseVarMonad

open import MTC.MTCBijective
open import BasicVarMonads.Pointers.PolyVars

private
  variable
    A B C : Set
    F M V : Set -> Set

open BaseVarMonad {{...}}

BVMToPolyVar : {{bvm : BaseVarMonad M V}} -> BaseVarMonad M (PolyVar V)
BVMToPolyVar = record {
  new = \ {A} a -> (\v -> PV A v (id <,> id)) <$> new a ;
  read = \ {(PV A v (to <,> _)) -> to <$> read v } ;
  write = \ {(PV A v ( _ <,> from)) k -> write v (from k)} }
