{-# OPTIONS --type-in-type #-}
module MTC.MTCMendler where

open import AgdaAsciiPrelude.AsciiPrelude
open Functor {{...}} renaming (_<$>_ to _<$>f_)

private
  variable
    A : Set
    F : Set -> Set

Algebra : (Set -> Set) -> Set -> Set
Algebra F A = forall R -> (R -> A) -> F R -> A

Fix : (Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg f = f _ alg

In : F (Fix F) -> Fix F
In f A alg = alg _ (foldF alg) f

Ex : {{func : Functor F}} -> Fix F -> F (Fix F)
Ex = foldF \ _ [[_]] -> (In o [[_]]) <$>f_
