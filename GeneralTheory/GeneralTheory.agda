{-# OPTIONS --type-in-type #-}
module GeneralTheory.GeneralTheory where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Lattice
open import MTC.MTCMendler
open import AgdaAsciiPrelude.Instances

private
  variable 
    L A B C : Set

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

record NewLat (L : Set) : Set where
  field
    new : {A : Set} -> L -> TFunc L A -x- L

open NewLat{{...}}

record BranchLat (L : Set) : Set where
  field
    mkBranch : L -> TFunc L L -x- L

open import Util.Lattice
open BoundedMeetSemilattice {{...}}

add : {{BoundedMeetSemilattice L}} -> L -> StateT L id T
add = modify o _/\_
  where 
    open MonadState{{...}} using (modify)
    instance
      _ = MonadStateStateTId


NewLat=>BranchLat : 
  {{NewLat L}} -> 
  {{PropLat L}} -> 
  {{BoundedMeetSemilattice L}} ->
  BranchLat L
NewLat=>BranchLat {L} = record { 
  mkBranch = do
    (f tf t) <- new {A = L}
    add (withProp t)
    return (f tf t)
  }
  where 
    instance 
      _ = MonadStateTId
      _ = MonadStateStateTId