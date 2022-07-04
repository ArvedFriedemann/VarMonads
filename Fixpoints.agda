{-# OPTIONS --type-in-type #-}
module Fixpoints where

open import AgdaAsciiPrelude.AsciiPrelude

open import Category.Functor using () renaming (RawFunctor to Functor)
open Functor {{...}} renaming (_<$>_ to _<$>'_)

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

In : F (Fix F) -> Fix F
In f A alg = alg _ f (foldF alg)

Ex : {{func : Functor F}} -> Fix F -> F (Fix F)
Ex = foldF \ R f [[_]] -> In o [[_]] <$>' f

KAlgebra : (K : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
KAlgebra K F A = forall R -> {{k : K R}} -> F R -> (R -> A) -> A

KFix : (K : Set -> Set) -> (F : Set -> Set) -> Set
KFix K F = forall A -> KAlgebra K F A -> A

KfoldF : KAlgebra K F A -> KFix K F -> A
KfoldF alg f = f _ alg

KIn : {{k : K (KFix K F)}} -> F (KFix K F) -> KFix K F
KIn f A alg = alg _ f (KfoldF alg)
