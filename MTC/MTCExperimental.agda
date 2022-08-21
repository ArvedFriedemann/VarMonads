{-# OPTIONS --type-in-type #-}
module MTC.MTCExperimental where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    R A : Set
    F : Set -> Set
    n n1 n2 : Nat


Algebra : (Set -> Set) -> Set -> Set -> Set
Algebra F R A = (R -> A) -> F R -> A
{-}
Fix : Set -> (Set -> Set) -> Set
Fix R F = forall A -> Algebra F R A -> A

foldF : Algebra F R A -> Fix R F -> A
foldF alg f = f _ alg

Out : Fix R F -> F R
Out {F = F} = foldF {F = F} (const id)

In : F (Fix R F) -> Fix (Fix R F) F
In {F = F} f _ alg = alg (foldF {F = F} {!!}) f

-}
Fix : Nat -> (Set -> Set) -> Set
Fix 0 F = BOT
Fix (suc n) F = forall A -> (Algebra F (Fix n F) A) -> A

foldF : Algebra F (Fix n F) A -> Fix (suc n) F -> A
foldF alg f = f _ alg

Out : Fix (suc n) F -> F (Fix n F)
Out = foldF (const id)

raiseFix : Fix n F -> Fix (suc n) F
raiseFix {suc n} f _ alg = {!!}

redAlg : Algebra F (Fix (suc n) F) A -> Algebra F (Fix n F) A
redAlg alg [[_]] f = alg (foldF {!!}) {!   !}
{-}
In : F (Fix n F) -> Fix (suc n) F
In {n = zero} f _ alg = alg absurd f
In {n = suc n} f _ alg = alg (foldF (redAlg alg)) f
-}
In : F (Fix n F) -> Fix (suc n) F
In f _ alg = alg {!!} f