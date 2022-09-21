module Util.Lattice where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set

record Semilattice (A : Set) : Set where
  field
    _<>_ : A -> A -> A

record BoundedSemilattice (A : Set) : Set where
  field
    sl : Semilattice A
    neut : A
  open Semilattice sl public

record BoundedJoinSemilattice (A : Set) : Set where
  field
    bsl : BoundedSemilattice A
  open BoundedSemilattice bsl renaming (_<>_ to _\/_; neut to bot) public

record BoundedMeetSemilattice (A : Set) : Set where
  field
    bsl : BoundedSemilattice A
  open BoundedSemilattice bsl renaming (_<>_ to _/\_; neut to top) public


record Lattice (A : Set) : Set where
  field
    meet-sl : Semilattice A
    join-sl : Semilattice A
  open Semilattice meet-sl renaming (_<>_ to _/\_) public
  open Semilattice join-sl renaming (_<>_ to _\/_) public

record BoundedLattice (A : Set) : Set where
  field
    meet-bsl : BoundedMeetSemilattice A
    join-bsl : BoundedJoinSemilattice A
  open BoundedMeetSemilattice meet-bsl public
  open BoundedJoinSemilattice join-bsl public

lat-leq : {{eq : Eq A}} -> {{lat : BoundedMeetSemilattice A}} ->
  A -> A -> Bool
lat-leq x y = y == (x /\ y)
  where
    open BoundedMeetSemilattice {{...}}

data TrivLat (A : Set) : Set where
  trivtop   : TrivLat A
  trivcont  : A -> TrivLat A
  trivbot   : TrivLat A

trivialBoundedLattice : {{eq : Eq A}} -> BoundedLattice (TrivLat A)
trivialBoundedLattice {A = A} = record {
  meet-bsl = record { bsl = record {
    sl = record { _<>_ = trivMeet } ;
    neut = trivtop } } ;
  join-bsl = record { bsl = record {
    sl = record { _<>_ = trivJoin } ;
    neut = trivbot } } }
  where
    trivMeet : TrivLat A -> TrivLat A -> TrivLat A
    trivMeet trivtop y = y
    trivMeet y trivtop = y
    trivMeet (trivcont x) (trivcont y) with x == y
    ... | false = trivbot
    ... | true = trivcont x
    trivMeet trivbot y = trivbot
    trivMeet y trivbot = trivbot

    trivJoin : TrivLat A -> TrivLat A -> TrivLat A
    trivJoin trivtop y = trivtop
    trivJoin y trivtop = trivtop
    trivJoin (trivcont x) (trivcont y) with x == y
    ... | false = trivtop
    ... | true = trivcont x
    trivJoin trivbot y = y
    trivJoin y trivbot = y

trivialEq : {{eq : Eq A}} -> Eq (TrivLat A)
trivialEq = record { _==_ = \ {
  trivtop trivtop -> true ;
  trivbot trivbot -> true ;
  (trivcont x) (trivcont y) -> x == y ;
  _ _ -> false } }
