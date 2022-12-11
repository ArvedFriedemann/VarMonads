{-# OPTIONS --type-in-type #-}
module MTC.FunctorToolkit.FunctorToolkit where
open import AgdaAsciiPrelude.AsciiPrelude hiding ([]; _::_)
open import MTC.MTCMendler hiding (ListF)
open import Util.Lattice

variable
  A B : Set
  F G H M : Set -> Set

data K (A : Set) (B : Set) : Set where
  Kc : A -> K A B

I : Set -> Set
I B = K B B

C : Set -> Set
C = K T

infixl 5 _:*:_
data _:*:_ (F G : Set -> Set) (B : Set) : Set where
  _:c*:_ : F B -> G B -> (F :*: G) B

infixr 6 _:+:_
data _:+:_ (F G : Set -> Set) (B : Set) : Set where
  inl : F B -> (F :+: G) B
  inr : G B -> (F :+: G) B

infixr 1 _:o:_
data _:o:_ (F G : Set -> Set) (B : Set) : Set where
  uc : (F o G) B -> (F :o: G) B

open Functor {{...}} renaming (_<$>_ to _<$>'_)

functor-K : Functor (K A)
functor-K = record { _<$>_ = \ {_ (Kc x) -> Kc x  } }

functor-:*: : {{Functor F}} -> {{Functor G}} -> Functor (F :*: G)
functor-:*: = record { _<$>_ = \{h (f :c*: g) -> (h <$>' f) :c*: (h <$>' g)} }

functor-:+: : {{Functor F}} -> {{Functor G}} -> Functor (F :+: G)
functor-:+:  = record {
  _<$>_ = \{
    h (inl f) -> inl (h <$>' f);
    h (inr g) -> inr (h <$>' g)
  } }

functor-:o: : {{Functor F}} -> {{Functor G}} -> Functor (F :o: G)
functor-:o: = record { _<$>_ =
  \{h (uc fog) -> uc ((h <$>'_) <$>' fog)} }


open import Util.Lattice

open Semilattice {{...}}

semilattice-K : {{Semilattice A}} -> Semilattice (K A B)
semilattice-K = record { _<>_ = \{
  (Kc x) (Kc y) -> Kc (x <> y) } }

semilattice-:*: : {{Semilattice (F B)}} -> {{Semilattice (G B)}} -> Semilattice ((F :*: G) B)
semilattice-:*: = record { _<>_ =
  \{(f1 :c*: g1) (f2 :c*: g2) -> (f1 <> f2) :c*: (g1 <> g2) } }
