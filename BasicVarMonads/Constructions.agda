{-# OPTIONS --type-in-type #-}
module BasicVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

open import BasicVarMonads.BaseVarMonad
open import BasicVarMonads.ConstrainedVarMonad

open import MTC.MTCBijective
open import BasicVarMonads.Pointers.PolyVars

open import Util.Eq
open import Util.Lattice
open import Util.Derivation

private
  variable
    A B C : Set
    F M V K : Set -> Set

module BaseVarMonadConstructions where
  open BaseVarMonad {{...}}

  BaseVarMonad=>PolyVar : {{bvm : BaseVarMonad M V}} -> BaseVarMonad M (PolyVar V)
  BaseVarMonad=>PolyVar = record {
    new = \ {A} a -> (\v -> PV A v (id <,> id)) <$> new a ;
    read = \ {(PV A v (to <,> _)) -> to <$> read v } ;
    write = \ {(PV A v ( _ <,> from)) k -> write v (from k)} }


  open import BasicVarMonads.ConstrainedVarMonad

  BaseVarMonad=>ConstrVarMonad : {{bvm : BaseVarMonad M V}} -> ConstrVarMonad K M V
  BaseVarMonad=>ConstrVarMonad = record {
    new = new ;
    read = read ;
    write = write }
open BaseVarMonadConstructions public

module LatticeVarMonadConstructions where
  open import BasicVarMonads.LatticeVarMonad
  open ConstrVarMonad {{...}}
  open Eq {{...}}
  open BoundedMeetSemilattice {{...}}

  ConstrVarMonad=>LatVarMonad :
    {{cvm : ConstrVarMonad K M V}} ->
    {{K derives BoundedMeetSemilattice}} ->
    {{(\A -> Eq A -x- BoundedMeetSemilattice A) derives K}} ->
    LatVarMonad M V
  ConstrVarMonad=>LatVarMonad = record {
    cvm = record {
      new = new ;
      read = read ;
      write = \v x -> read v >>= \x' -> write v (x /\ x') } }

open LatticeVarMonadConstructions public
