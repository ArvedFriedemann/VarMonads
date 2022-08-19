module Util.Lattice where

open import AgdaAsciiPrelude.AsciiPrelude

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
