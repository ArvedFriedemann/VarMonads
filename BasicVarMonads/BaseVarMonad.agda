{-# OPTIONS --type-in-type #-}
module BasicVarMonads.BaseVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

variable
  A B : Set

record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    read : V A -> M A
    write : V A -> A -> M T
