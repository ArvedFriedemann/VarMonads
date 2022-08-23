module Util.Monad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set
    M : Set -> Set

void : {{mon : Monad M}} -> M A -> M T
void m = m >> return tt

iterateM : {{mon : Monad M}} -> Nat -> (A -> M A)-> A -> M A
iterateM 0 _ x = return x
iterateM (suc n) f x = f x >>= iterateM n f
