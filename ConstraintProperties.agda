{-# OPTIONS --type-in-type #-}
module ConstraintProperties where

open import AgdaAsciiPrelude.AsciiPrelude

ConservesVar : (K : Set -> Set) -> (V : Set -> Set) -> Set
ConservesVar K V = forall {A} -> {{ka : K A}} -> K (V A)

ConservesProd : (K : Set -> Set) -> Set
ConservesProd K = forall {A B} -> {{ka : K A}} -> {{kb : K B}} -> K (A -x- B)
