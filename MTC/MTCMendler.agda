{-# OPTIONS --type-in-type #-}
module MTC.MTCMendler where

open import AgdaAsciiPrelude.AsciiPrelude
open Functor {{...}} renaming (_<$>_ to _<$>f_)

private
  variable
    A : Set
    F V : Set -> Set

Algebra : (Set -> Set) -> Set -> Set
Algebra F A = forall R -> (R -> A) -> F R -> A

Fix : (Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg f = f _ alg

In : F (Fix F) -> Fix F
In f A alg = alg _ (foldF alg) f

Out : {{func : Functor F}} -> Fix F -> F (Fix F)
Out = foldF \ _ [[_]] -> (In o [[_]]) <$>f_

open import AgdaAsciiPrelude.TrustMe

OutF : {{func : Functor F}} -> Fix (F o V) -> (F o V) (Fix (F o V))
OutF = foldF \R [[_]] f -> trustVal <$>f f

data ListF (A : Set) (B : Set) : Set where
  nilF : ListF A B
  consF : A -> B -> ListF A B

instance
  LiftFFunctor : Functor (ListF A)
  LiftFFunctor = record { _<$>_ = \{ f nilF -> nilF; f (consF x xs) -> consF x (f xs) } }

nil : Fix (ListF A o V)
nil = In nilF

cons : A -> V (Fix (ListF A o V)) -> Fix (ListF A o V)
cons x xs = In (consF x xs)
