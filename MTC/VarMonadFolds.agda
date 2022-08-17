module MTC.VarMonadFolds where

open import AgdaAsciiPrelude.AsciiPrelude
open import MTC.MTCMendler
open import BasicVarMonads.BaseVarMonad

private
  variable
    A : Set
    F M V : Set -> Set

open BaseVarMonad {{...}}

foldBVM : {{bvm : BaseVarMonad M V}} ->
  Algebra F (M A) -> Fix (F o V) -> M A
foldBVM alg = foldF \ _ [[_]] f -> alg _ (read >=> [[_]]) f
