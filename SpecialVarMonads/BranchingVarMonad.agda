{-# OPTIONS --type-in-type #-}

module SpecialVarMonads.BranchingVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ConstrainedVarMonad

record BranchingVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (S : Set) : Set where
  field
    cvm : ConstrDefVarMonad K M V
    newBranch : M (V S)
  open ConstrDefVarMonad cvm public
