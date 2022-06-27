{-# OPTIONS --type-in-type #-}
module Fixpoints where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

Algebra : (F : Set -> Set) -> (A : Set) -> Set
Algebra F A = forall R -> F R -> (R -> A) -> A

Fix : (F : Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg f = f _ alg

KAlgebra : (K : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
KAlgebra K F A = forall R -> {{k : K R}} -> F R -> (R -> A) -> A

KFix : (K : Set -> Set) -> (F : Set -> Set) -> Set
KFix K F = forall A -> KAlgebra K F A -> A

KfoldF : KAlgebra K F A -> KFix K F -> A
KfoldF alg f = f _ alg
