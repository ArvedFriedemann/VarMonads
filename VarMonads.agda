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
