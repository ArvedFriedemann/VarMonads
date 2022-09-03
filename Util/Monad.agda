{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module Util.Monad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set

module _ {M : Set -> Set} {{mon : Monad M}} where

  void : M A -> M T
  void m = m >> return tt

  iterateM : Nat -> (A -> M A)-> A -> M A
  iterateM 0 _ x = return x
  iterateM (suc n) f x = f x >>= iterateM n f

  when : Bool -> M A -> M T
  when true m = void m
  when false m = return tt

  loop : List A -> M B -> (A -> B -> M B) -> M B
  loop {A} {B} lst def f = def >>= loop' lst f
    where
      loop' : List A -> (A -> B -> M B) -> B -> M B
      loop' [] f b0 = return b0
      loop' (x :: lst) f b0 = f x b0 >>= loop' lst f
