{-# OPTIONS --type-in-type #-}
module Util.PointerEquality where

open import AgdaAsciiPrelude.AsciiPrelude

record PEq (V : Set -> Set) : Set where
  field
    _=p=_ : forall {A B} -> V A -> V B -> Bool
