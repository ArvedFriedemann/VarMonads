module Util.Monad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set
    M : Set -> Set

void : {{mon : Monad M}} -> M A -> M T
void m = m >> return tt
