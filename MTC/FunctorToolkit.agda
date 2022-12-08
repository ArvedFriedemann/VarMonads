{-# OPTIONS --type-in-type #-}
module MTC.FunctorToolkit where
open import AgdaAsciiPrelude.AsciiPrelude

data I (B : Set) : Set where
  Ic : B -> I B

data K (A : Set) (B : Set) : Set where
  Kc : A -> K A B

data _:+:_ (F G : Set -> Set) (B : Set) : Set where
  inl : F B -> (F :+: G) B
  inr : G B -> (F :+: G) B

data _:*:_ (F G : Set -> Set) (B : Set) : Set where
  _:c*:_ : F B -> G B -> (F :*: G) B

ListF : Set -> Set -> Set
ListF A = I :+: (K A :*: I)
