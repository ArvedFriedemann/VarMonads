{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
module SpecialVarMonads.Propagators.BasicPropagators where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ConstrainedVarMonad
open import MiscMonads.ConcurrentMonad
open import Util.Derivation
open import Util.Lattice

private
  variable
    A B : Set

module EqPropagators {K M V : Set -> Set} {{nvm : NewConstrDefVarMonad K M V}} where
  open NewConstrDefVarMonad nvm
  open BoundedMeetSemilattice {{...}}

  {-# TERMINATING #-} --this only terminates if the propagators is never called twice on a certain size
  continuous : V A -> (A -> M B) ->  M T
  continuous v f = read v >>= f >> continuous v f

  _=p>_ : V A -> V A -> M T
  v1 =p> v2 = continuous v1 (write v2)

open import BasicVarMonads.ThresholdVarMonad

module EqTPropagators {K M V : Set -> Set}
  {{tvm : ThresholdVarMonad K M V}}
  {{mf : MonadFork M}} where
  open MonadFork mf
  open ThresholdVarMonad tvm
  open BoundedMeetSemilattice {{...}}

  eqThreshold : {{Eq A}} -> A -> BijTFunc A A
  eqThreshold a = (\a' -> if a == a' then nothing else just a') <,> id

  {-# TERMINATING #-}
  continuous : {{eq : Eq A}} -> V A -> A -> (A -> M B) -> M T
  continuous v a f = do
    a' <- read (eqThreshold a <bt$> v)
    f a' >> continuous v a' f

  _=p>_ : {{eq : Eq A}} ->
          {{bms : BoundedMeetSemilattice A}} ->
          V A -> V A -> M T
  v1 =p> v2 = fork $ continuous v1 top (write v2)

  _=p=_ : {{eq : Eq A}} ->
          {{bms : BoundedMeetSemilattice A}} ->
          V A -> V A -> M T
  v1 =p= v2 = v1 =p> v2 >> v2 =p> v1


  -- _=p>_[_] :
  --   (v1 : V A) -> (v2 : V B) ->
  --   (sameOrigT v1 v2) ->
  --   M T
  -- v1 =p> v2 [ eq ] with transOf v1 | transOf v2
  -- v1 =p> v2 [ refl ] | (TVarC OrigT {{origK}} f1 vo1) | (TVarC OrigT f2 vo2) =
  --                           _=p>_ {{KEq {{origK}}}} {{KBMSL {{origK}}}} vo1 vo2

record MonadEq (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    _=p=_ : {{k : K A}} -> V A -> V A -> M T
    overlap {{keq}} : K derives Eq
    overlap {{kbmsl}} : K derives BoundedMeetSemilattice
