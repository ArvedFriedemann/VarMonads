{-# OPTIONS --type-in-type #-}
module Util.Eq where

open import AgdaAsciiPrelude.AsciiPrelude

record Eq (A : Set) : Set where
  field
    _==_ : A -> A -> Bool
