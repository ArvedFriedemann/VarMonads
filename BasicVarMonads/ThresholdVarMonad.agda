{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ThresholdVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances

open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation
open import Util.Lattice

private
  variable
    A B : Set
    V : Set -> Set

record InvTFunc (A : Set) (B : Set) : Set where
  constructor _<,>_
  field
    Tfunc : A -> Maybe B
    Tfunc-1 : B -> A

--ThresholdVar
record TVar (V : Set -> Set) (A : Set) : Set where
  constructor TVarC
  field
    OrigT : Set
    OVar : V OrigT
    f : InvTFunc OrigT A

instance
  monadMaybe = MonadMaybe

subVar : TVar V A -> InvTFunc A B -> TVar V B
subVar (TVarC T v (TtoA <,> AtoT)) (AtoB <,> BtoA) =
  TVarC T v ((TtoA >=> AtoB) <,> (AtoT o BtoA))

record ThresholdVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    cvm : NewConstrDefVarMonad K M (TVar V)
    overlap {{KEq}} : K derives Eq
    overlap {{KBMSL}} : K derives BoundedMeetSemilattice
  open NewConstrDefVarMonad cvm public
