{-# OPTIONS --type-in-type #-}
module GeneralTheory.GeneralTheory where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Lattice
open import MTC.MTCMendler
open import AgdaAsciiPrelude.Instances
open import Util.Derivation
open import MTC.FunctorToolkit.FunctorToolkit renaming (C to KC; K to KK)


private
  variable 
    L A B C : Set
    K : Set -> Set

record PropLat (L : Set) : Set where
  field
    withProp : (L -> L) -> L
    getProps : L -> (L -> L)
    {- 
    properties:
    getProps o withProp = id
    withProp o getProps = id
    -}

open PropLat {{...}}


{-# TERMINATING #-}
propagate : {{Eq L}} -> {{PropLat L}} -> L -> L
propagate l with l' <- (getProps l) l | l == l'
...| true = l'
...| false = propagate l'

record TFunc (L A : Set) : Set where
  constructor _tf_
  field
    from : L -> Maybe A
    to : A -> L

_o-tf_ : TFunc B C -> TFunc A B -> TFunc A C
(bc tf cb) o-tf (ab tf ba) = (ab >=> bc) tf (ba o cb)
  where 
    instance 
      _ = MonadMaybe

record ConNewLat (K : Set -> Set) (L : Set) : Set where
  field
    new : {A : Set} -> {{k : K A}} -> L -> TFunc L A -x- L

open ConNewLat{{...}}



data FreeConSOPF (K : Set -> Set) (R : Set) : Set where
  FK : {A : Set} -> {{K A}} -> FreeConSOPF K R
  _F:*:_ : R -> R -> FreeConSOPF K R
  _F:+:_ : R -> R -> FreeConSOPF K R

FreeConSOP : (K : Set -> Set) -> Set
FreeConSOP K = Fix $ FreeConSOPF K

[_]func : FreeConSOP K -> Set -> Set
[_]func = foldF \{
    [[_]] (FK {A}) -> KK A
  ; [[_]] (a F:*: b) -> [[ a ]] :*: [[ b ]]
  ; [[_]] (a F:+: b) -> [[ a ]] :+: [[ b ]]}

record SOPNewLat (K : Set -> Set) (L : Set) : Set where
  field
    new : (F : FreeConSOP K) -> State L (Fix [ F ]func )







record BranchLat (L : Set) : Set where
  field
    mkBranch : L -> TFunc L L -x- L

open import Util.Lattice
open BoundedMeetSemilattice {{...}}

add : {{BoundedMeetSemilattice L}} -> L -> State L T
add = modify o _/\_
  where 
    open MonadState{{...}} using (modify)
    instance
      _ = MonadStateStateTId


ConNewLat=>BranchLat : 
  {{ConNewLat K L}} -> 
  {{PropLat L}} -> 
  {{BoundedMeetSemilattice L}} ->
  {{K L}} ->
  BranchLat L
ConNewLat=>BranchLat {L = L} = record { 
  mkBranch = do
    (f tf t) <- new {A = L}
    add (withProp t)
    return (f tf t)
  }
  where 
    instance 
      _ = MonadStateTId
      _ = MonadStateStateTId