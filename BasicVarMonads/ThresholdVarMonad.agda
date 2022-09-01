{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ThresholdVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances

open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation
open import Util.Lattice

private
  variable
    A B C : Set
    V K : Set -> Set

record BijTFunc (A : Set) (B : Set) : Set where
  constructor _<,>_
  field
    Tfunc : A -> Maybe B
    Tfunc-1 : B -> A

record BijTFunctor (F : Set -> Set) : Set where
  field
    _<bt$>_ : BijTFunc A B -> F A -> F B

--ThresholdVar
record TVar (K : Set -> Set) (V : Set -> Set) (A : Set) : Set where
  constructor TVarC
  field
    OrigT : Set
    {{origK}} : K OrigT
    OVar : V OrigT
    f : BijTFunc OrigT A

instance
  monadMaybe = MonadMaybe

_<o>_ : BijTFunc B C -> BijTFunc A B -> BijTFunc A C
_<o>_ (BtoC <,> CtoB) (AtoB <,> BtoA) = (BtoC <=< AtoB) <,> (BtoA o CtoB)

_<$o$>_ : BijTFunc A B -> TVar K V A -> TVar K V B
_<$o$>_ t (TVarC T v f) = TVarC T v (t <o> f)


TVarBijTFunctor : BijTFunctor (TVar K V)
TVarBijTFunctor = record { _<bt$>_ = _<$o$>_ }

record ThresholdVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    cvm : NewConstrDefVarMonad K M V
    tvbf : BijTFunctor V
    overlap {{KEq}} : K derives Eq
    overlap {{KBMSL}} : K derives BoundedMeetSemilattice
  open NewConstrDefVarMonad cvm public
  open BijTFunctor tvbf public
