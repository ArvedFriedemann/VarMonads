{-# OPTIONS --type-in-type #-}
module SpecialVarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

-----------------------------------------------------------------
--Unconstrained Special VarMonads
-----------------------------------------------------------------

AsmCont : (V : Set -> Set) -> (C : Set -> Set) -> Set
AsmCont V C = Sigma Set \ A -> A -x- V A

record TrackVarMonad
    (M : Set -> Set)
    (V : Set -> Set)
    (C : Set -> Set) : Set where
  field
    overlap {{bvm}} : BaseVarMonad M V
    getCurrAssignments : M (AsmCont V C)
