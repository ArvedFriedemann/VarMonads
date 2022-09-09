{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ModifyVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    M M' V K : Set -> Set

record ModifyVarMonad
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    modify : V A -> (A -> A -x- B) -> M B
    overlap {{mon}} : Monad M

  read : V A -> M A
  read v = modify v \x -> (x , x)

  write' : V A -> (A -> A) -> M T
  write' v f = modify v \x -> (f x , tt)

  write : V A -> A -> M T
  write v a = write' v (const a)

liftModifyVarMonad :
  {{mon' : Monad M'}} ->
  (forall {A} -> M A -> M' A) ->
  ModifyVarMonad M V ->
  ModifyVarMonad M' V
liftModifyVarMonad liftT mvm = record {
    new = liftT o new ;
    modify = \v f -> liftT (modify v f) }
  where open ModifyVarMonad mvm

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
