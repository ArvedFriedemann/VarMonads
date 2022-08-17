{-# OPTIONS --type-in-type #-}
module MTC.MTCCasual where

open import AgdaAsciiPrelude.AsciiPrelude
open Functor {{...}} renaming (_<$>_ to _<$>f_)

variable
  A : Set
  F : Set -> Set

Algebra : (Set -> Set) -> Set -> Set
Algebra F A = F A -> A

Fix : (Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg f = f _ alg

In : {{func : Functor F}} -> F (Fix F) -> Fix F
In f A alg = alg (foldF alg <$>f f)

Ex : {{func : Functor F}} -> Fix F -> F (Fix F)
Ex = foldF (In <$>f_)
