{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ModifyVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    M V K : Set -> Set

record ConstrDefModifyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{K A}} -> M (V A)
    modify : {{K A}} -> V A -> (A -> A -x- B) -> M B
    overlap {{mon}} : Monad M

  read : {{K A}} -> V A -> M A
  read v = modify v \x -> (x , x)

  write' : {{K A}} -> V A -> (A -> A) -> M T
  write' v f = modify v \x -> (f x , tt)

  write : {{K A}} -> V A -> A -> M T
  write v a = write' v (const a)

record ConstrDefWriteModifyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{K A}} -> M (V A)
    write : {{K A}} -> V A -> A -> M (V A)
    modify : {{K A}} -> V A -> (A -> A -x- B) -> M B
    overlap {{mon}} : Monad M

  read : {{K A}} -> V A -> M A
  read v = modify v \x -> (x , x)

  write' : {{K A}} -> V A -> (A -> A) -> M T
  write' v f = modify v \x -> (f x , tt)
