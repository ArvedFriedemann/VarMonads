{-# OPTIONS --type-in-type #-}
module BasicVarMonads.LatticeVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Lattice
open import Util.Eq
open import BasicVarMonads.ConstrainedVarMonad

private
  variable
    A : Set

record LatVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  K : Set -> Set
  K A = Eq A -x- BoundedMeetSemilattice A
  open Eq {{...}} public
  open BoundedMeetSemilattice {{...}} public

  field
    cvm : ConstrVarMonad K M V
    overlap {{mon}} : Monad M
  open ConstrVarMonad cvm public

  instance
    KEq : {{k : K A}} -> Eq A
    KEq {{(eq , _ )}} = eq
    KBMSL : {{k : K A}} -> BoundedMeetSemilattice A
    KBMSL {{(_ , kbmsl )}} = kbmsl
    
  new' : {{K A}} -> M (V A)
  new' = new top
