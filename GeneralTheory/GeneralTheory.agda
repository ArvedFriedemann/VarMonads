{-# OPTIONS --type-in-type #-}
module GeneralTheory.GeneralTheory where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Lattice
open import MTC.MTCMendler

private
  variable 
    L : Set
{-
record PropLat (L : Set) : Set where
  constructor PL
  field
    content : L
    props : L -> L
-}

{-
record PropLat (L : Set) : Set where
  field
    inj-prop : (L -> L) -> L
    proj-prop : L -> (L -> L)

    -- property : forall l -> let l' = (inj-prop f) /\ l in (proj-prop l') l' leq f l'

open PropLat {{...}}

{-# TERMINATING #-}
propagate : {{PropLat L}} -> {{Eq L}} -> L -> L
propagate l with l' <- (proj-prop l) l | l == l'
...| true = l
...| false = propagate l'
-}

{-# NO_POSITIVITY_CHECK #-}
record PropLat (L : Set) : Set where
  constructor PL 
  field
    content : L
    propagator : (PropLat L -> PropLat L)

open BoundedLattice{{...}}

{-# TERMINATING #-}
PL-meet : {{BoundedLattice L}} -> PropLat L -> PropLat L -> PropLat L
PL-meet (PL c1 p1) (PL c2 p2) = PL (c1 /\ c2) (\ x -> PL-meet (p1 x) (p2 x))

PL-top : {{BoundedLattice L}} -> PropLat L
PL-top = PL top id

{-# TERMINATING #-}
PL-join : {{BoundedLattice L}} -> PropLat L -> PropLat L -> PropLat L
PL-join (PL c1 p1) (PL c2 p2) = PL (c1 \/ c2) (\ x -> PL-join (p1 x) (p2 x))

PL-bot : {{BoundedLattice L}} -> PropLat L
PL-bot = PL bot id

PropLatLattice : {{BoundedLattice L}} -> BoundedLattice (PropLat L)
PropLatLattice = record { 
  meet-bsl = record { bsl = record { 
    sl = record { _<>_ = PL-meet } ; 
    neut = PL top (const PL-top) } } ; 
  join-bsl = record { bsl = record { 
    sl = record { _<>_ = PL-join } ; 
    neut = PL-bot } } }
