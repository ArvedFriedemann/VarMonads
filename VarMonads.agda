{-# OPTIONS --type-in-type #-}

module VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

-------------------------------------------
--Constrained VarMonads
-------------------------------------------

record ConstrBaseVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    read : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M


--TODO modify gives extra read!!

record ConstrModifyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    modify : {{k : K A}} -> V A -> (A -> A -x- B) -> M B
    overlap {{mon}} : Monad M

  read : {{k : K A}} -> V A -> M A
  read p = modify p \ x -> x , x

  modify' : {{k : K A}} -> V A -> (A -> A) -> M T
  modify' p f = modify p \ x -> f x , tt

  write : {{k : K A}} -> V A -> A -> M T
  write p v = modify' p (const v)


--------------------------------------------------
--Unconstrained VarMonads
--------------------------------------------------
--TODO do make those separate monads and make a construction from a T constrianed monad


BaseVarMonad : (M : Set -> Set) -> (V : Set -> Set) -> Set
BaseVarMonad = ConstrBaseVarMonad (const T)

ModifyVarMonad : (M : Set -> Set) -> (V : Set -> Set) -> Set
ModifyVarMonad = ConstrModifyVarMonad (const T)
