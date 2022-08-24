{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.FixedValueVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set

record FixedDefValVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (B : Set) : Set where
  field
    new : M (V A)
    read : V A -> M B
    write : V A -> B -> M T
