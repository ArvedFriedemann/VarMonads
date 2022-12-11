{-# OPTIONS --type-in-type #-}
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
foldBVM alg = foldF \ [[_]] f -> alg (read >=> [[_]]) f

open import Assembly.StdVarMonad

instance
  _ = defaultVarMonad
  _ = BaseVarMonad.mon defaultVarMonad


testMTC : (ListF Nat o NatPtr) (Fix (ListF Nat o NatPtr))
testMTC = runDefVarMonad do
  v1 <- new {A = Fix (ListF Nat o NatPtr)} nil
  v2 <- new {A = Fix (ListF Nat o NatPtr)} (cons 1 v1)
  OutF <$> (read v2)
