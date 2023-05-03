{-# OPTIONS --type-in-type #-}
module GeneralTheory.GeneralTheory where

open import Util.Lattice

{-# NO_POSITIVITY_CHECK #-}
record PropLat (M : Set) : Set where
  inductive
  field
    content : M
    props : PropLat M -> PropLat M

