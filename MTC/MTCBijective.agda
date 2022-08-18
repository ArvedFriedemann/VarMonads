{-# OPTIONS --type-in-type #-}
module MTC.MTCBijective where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B C : Set
    F : Set -> Set

record _<-*->_ (A : Set) (B : Set) : Set where
  constructor _<,>_
  field
    to : A -> B
    from : B -> A

_<o>_ : B <-*-> C -> A <-*-> B -> A <-*-> C
b1 <o> b2 = (BtoC o AtoB) <,> (BtoA o CtoB)
  where
    open _<-*->_ b1 renaming (to to BtoC; from to CtoB)
    open _<-*->_ b2 renaming (to to AtoB; from to BtoA)


record BijectionProp (bij : A <-*-> B) : Set where
  open _<-*->_ bij
  field
    bij-prop-to : to o from === id
    bij-prop-from : from o to === id

record BijFunctor (F : Set -> Set) : Set where
  field
    _<$>_ : A <-*-> B -> F A -> F B

open BijFunctor {{...}} renaming (_<$>_ to _<$>bf_)

Algebra : (Set -> Set) -> Set -> Set
Algebra F A = forall R -> (R <-*-> A) -> F R -> A

Fix : (Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg f = f _ alg

In : F (Fix F) -> Fix F
In f _ alg = alg _ ((foldF alg) <,> \ a _ alg2 -> {!!}) f

Ex : {{bf : BijFunctor F}} -> Fix F -> F (Fix F)
Ex = foldF \ _ [[_]] f -> ( {!!} <$>bf f)
