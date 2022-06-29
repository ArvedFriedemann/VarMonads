{-# OPTIONS --type-in-type #-}
module SpecialVarMonads where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonads public

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

ConstrAsmCont : (K : Set -> Set) -> (V : Set -> Set) -> Set
ConstrAsmCont K V = Sigma Set \ A -> K A -x- A -x- V A

ConstrAsm : (K : Set -> Set) -> (V : Set -> Set) -> (C : Set -> Set) -> Set
ConstrAsm K V C = C $ ConstrAsmCont K V

record ConstrTrackVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (C : Set -> Set) : Set where
  field
    overlap {{bvm}} : ConstrBaseVarMonad K M V
    getCurrAssignments : M (ConstrAsm K V C)

record ConstrSpecVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (B : Set) : Set where
  field
    read : {{k : K A}} -> V A -> M B
    write : {{k : K A}} -> V A -> B -> M B
