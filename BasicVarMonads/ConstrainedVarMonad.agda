{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ConstrainedVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set

record ConstrVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{K A}} -> A -> M (V A)
    read : {{K A}} -> V A -> M A
    write : {{K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M
