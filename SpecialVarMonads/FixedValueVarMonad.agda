{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.FixedValueVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set

record ConstrDefDepModFixedValVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (B : Set -> Set) : Set where
  field
    new : {{K A}} -> M (V A)
    read : {{K A}} -> V A -> M (B A)
    write : {{K A}} -> V A -> (B A) -> M T
