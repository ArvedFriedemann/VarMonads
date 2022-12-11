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


testMTC : (ListF Bool o NatPtr) (Fix (ListF Bool o NatPtr))
--testMTC : Bool
testMTC = runDefVarMonad do
  v1 <- new {A = Fix (ListF Bool o NatPtr)} nil
  v2 <- new {A = Fix (ListF Bool o NatPtr)} (cons true v1)
  OutF <$> (read v2)
  {-
  --this creates an infinite data type. Termination checker does not catch it!
  write v2 (cons false v2)
  --lst <- read v2
  read v2 >>= foldBVM {F = ListF Bool} (\{
    [[_]] nilF -> return false;
    [[_]] (consF x xs) -> (| pure x  || [[ xs ]] |)})
  -}
