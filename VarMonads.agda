{-# OPTIONS --type-in-type #-}

module VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

record BaseVarMonad
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    read : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

record ModifyVarMonad
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    read : V A -> M A
    modify : V A -> (A -x- B) -> M B
    overlap {{mon}} : Monad M

record ConstrBaseVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    read : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M

record ConstrModifyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    read : {{k : K A}} -> V A -> M A
    modify : {{k : K A}} -> V A -> (A -x- B) -> M B
    overlap {{mon}} : Monad M
