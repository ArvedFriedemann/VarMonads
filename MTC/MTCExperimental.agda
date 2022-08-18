{-# OPTIONS --type-in-type #-}
module MTC.MTCExperimental where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    R A : Set
    F : Set -> Set
    n : Nat

{-}
Algebra : (Set -> Set) -> Set -> Set -> Set
Algebra F R A = (R -> A) -> F R -> A

Fix : Set -> (Set -> Set) -> Set
Fix R F = forall A -> Algebra F R A -> A

foldF : Algebra F R A -> Fix R F -> A
foldF alg f = f _ alg


In : F (Fix R F) -> Fix (Fix R F) F
In {F} f _ alg = alg (foldF {F = F} {!!}) f


Ex : Fix R F -> F R
Ex {F = F} = foldF {F = F} (const id)
-}


Algebra : (Set -> Set) -> Set -> Set -> Set
Algebra F R A = (R -> A) -> F R -> A

Fix : Nat -> (Set -> Set) -> Set
Fix 0 F = BOT
Fix (suc n) F = forall A -> Algebra F (Fix n F) A -> A

foldF : Algebra F (Fix n F) A -> Fix (suc n) F -> A
foldF alg f = f _ alg

In : F (Fix n F) -> Fix (suc n) F
In f _ alg = alg {!!} f

Ex : Fix (suc n) F -> F (Fix n F)
Ex = foldF (const id)
