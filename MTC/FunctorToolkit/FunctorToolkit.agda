{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module MTC.FunctorToolkit.FunctorToolkit where
open import AgdaAsciiPrelude.AsciiPrelude hiding ([]; _::_)
open import MTC.MTCMendler hiding (ListF)
open import Util.Lattice

variable
  A B : Set
  F G H J M : Set -> Set

data K (A : Set) (B : Set) : Set where
  Kc : A -> K A B

I : Set -> Set
I B = K B B

C : Set -> Set
C = K T

infixl 5 _:*:_
data _:*:_ (F G : Set -> Set) (B : Set) : Set where
  _:c*:_ : F B -> G B -> (F :*: G) B

infixl 6 _:+:_
data _:+:_ (F G : Set -> Set) (B : Set) : Set where
  inl : F B -> (F :+: G) B
  inr : G B -> (F :+: G) B

infixr 1 _:o:_
data _:o:_ (F G : Set -> Set) (B : Set) : Set where
  uc : (F o G) B -> (F :o: G) B

record _<:_ (F G : Set -> Set) : Set where
  field
    inj : F A -> G A
    prj : G A -> Maybe (F A)


module _ where
  open _<:_ {{...}}

  idSC : F <: F
  idSC = record {
    inj = id ;
    prj = just }

  FSC : {{F <: G}} -> F <: (G :+: H)
  FSC = record {
    inj = inl o inj ;
    prj = \{
      (inl g) -> prj g;
      (inr h) -> nothing} }

  GSC : {{F <: H}} -> F <: (G :+: H)
  GSC = record {
    inj = inr o inj ;
    prj = \{
      (inl g) -> nothing;
      (inr h) -> prj h} }



open Functor {{...}} renaming (_<$>_ to _<$>'_)

Functor-K : Functor (K A)
Functor-K = record { _<$>_ = \ {_ (Kc x) -> Kc x  } }

Functor-:*: : {{Functor F}} -> {{Functor G}} -> Functor (F :*: G)
Functor-:*: = record { _<$>_ = \{h (f :c*: g) -> (h <$>' f) :c*: (h <$>' g)} }

Functor-:+: : {{Functor F}} -> {{Functor G}} -> Functor (F :+: G)
Functor-:+:  = record {
  _<$>_ = \{
    h (inl f) -> inl (h <$>' f);
    h (inr g) -> inr (h <$>' g)
  } }

Functor-:o: : {{Functor F}} -> {{Functor G}} -> Functor (F :o: G)
Functor-:o: = record { _<$>_ =
  \{h (uc fog) -> uc ((h <$>'_) <$>' fog)} }


open import Util.Lattice

open Semilattice {{...}}

Semilattice-K : {{Semilattice A}} -> Semilattice (K A B)
Semilattice-K = record { _<>_ = \{
  (Kc x) (Kc y) -> Kc (x <> y) } }

Semilattice-:*: : {{Semilattice (F B)}} -> {{Semilattice (G B)}} -> Semilattice ((F :*: G) B)
Semilattice-:*: = record { _<>_ =
  \{(f1 :c*: g1) (f2 :c*: g2) -> (f1 <> f2) :c*: (g1 <> g2) } }

data FTop : Set where
  ftt : FTop

Semilattice-FTop : Semilattice FTop
Semilattice-FTop = record { _<>_ = \_ _ -> ftt }

data FBot : Set where
  fbb : FBot

Semilattice-FBot : Semilattice FBot
Semilattice-FBot = record { _<>_ = \_ _ -> fbb }

Semilattice-T : Semilattice T
Semilattice-T = record { _<>_ = \_ _ -> tt }
{-}
Semilattice-:+: :
  (H B) ->
  {{H <: (F :+: G) }} ->
  {{Semilattice (F B)}} ->
  {{Semilattice (G B)}} ->
  Semilattice ((F :+: G) B)
Semilattice-:+: {B = B} {F} {G} neut = record { _<>_ = _<>'_ }
  where
    _<>'_ : (F :+: G) B -> (F :+: G) B -> (F :+: G) B
    (inl x) <>' (inl y) = inl (x <> y)
    (inr x) <>' (inr y) = inr (x <> y)
    _ <>' _ = inj neut
-}
Semilattice-:+: :
  (H B) ->
  (J B) ->
  {{scH : H <: M }} ->
  {{scJ : J <: M }} ->
  {{slF : Semilattice (F B)}} ->
  {{slG : Semilattice (G B)}} ->
  {{sc+ : (F :+: G) <: M}} ->
  Semilattice (M B)
Semilattice-:+: {B = B} {M = M} neut elim {{scH}} {{scJ}} {{sc+ = sc+}} = record { _<>_ = _<>'_ }
  where
    open _<:_ sc+ renaming (prj to prj+; inj to inj+)
    open _<:_ scH renaming (prj to prjneut; inj to injneut)
    open _<:_ scJ renaming (prj to prjelim; inj to injelim)

    _<>'_ : M B -> M B -> M B
    x <>' y with prj+ x | prj+ y
    ... | just (inl f1) | just (inl f2) = inj+ (inl (f1 <> f2))
    ... | just (inr g1) | just (inr g2) = inj+ (inr (g1 <> g2))
    ... | x' | y' with prjneut x | prjneut y
    ...               | just n | _      = y
    ...               | _      | just n = x
    ... | _ | _ with prjelim x | prjelim y
    ...               | just e | _      = injelim elim
    ...               | _      | just e = injelim elim
    ... | _ | _ = injelim elim

open Lattice {{...}}
{-}
Lattice-:+: : (top : H B) -> (bot : J B) ->
  {{H <: (F :+: G) }} ->
  {{J <: (F :+: G) }} ->
  {{Semilattice (F B)}} ->
  {{Semilattice (G B)}} ->
  Lattice ((F :+: G) B)
Lattice-:+: tp bt = record {
  meet-sl = Semilattice-:+: bt ;
  join-sl = Semilattice-:+: tp }
  -}



module Temp where

  module _ where
    instance
      _ = Functor-K
      _ = Functor-:*:
      _ = Functor-:+:
      _ = Semilattice-FTop
      _ = Semilattice-FBot
      _ = Semilattice-T
      _ = Semilattice-K
      _ = Semilattice-:*:

      {-}
      _ : {{K FTop <: (F :+: G) }} ->
          {{Semilattice (F B)}} ->
          {{Semilattice (G B)}} -> Semilattice ((F :+: G) B)
      _ = Semilattice-:+: (Kc ftt)

      _ : {{K FBot <: (F :+: G) }} ->
          {{Semilattice (F B)}} ->
          {{Semilattice (G B)}} -> Semilattice ((F :+: G) B)
      _ = Semilattice-:+: (Kc fbb)

      _ : {{K FTop <: (F :+: G) }} ->
          {{K FBot <: (F :+: G) }} ->
          {{Semilattice (F B)}} ->
          {{Semilattice (G B)}} -> Lattice ((F :+: G) B)
      _ = Lattice-:+: (Kc ftt) (Kc fbb)
      -}
      {-}
      SL+ : {{scH : K FTop <: M }} ->
          {{scJ : K FBot <: M }} ->
          {{slF : Semilattice (F B)}} ->
          {{slG : Semilattice (G B)}} ->
          {{sc+ : (F :+: G) <: M}} ->
          Semilattice (M B)
      SL+ {{slF = slF}} {{slG = slG}} = Semilattice-:+: (Kc ftt) (Kc fbb) {{slF = slF}} {{slG = slG}}
      -}
      _ = idSC
      _ = FSC
      _ = GSC

    ListF : Set -> Set -> Set
    ListF A = K A :+: C :+: K FTop :+: K FBot

    []c : ListF A B
    []c = inl (inl (inr (Kc tt)))

    _:: : A -> ListF A B
    _:: a = inl (inl (inl (Kc a)))

    lftop : ListF A B
    lftop = inl (inr (Kc ftt))

    lfbot : ListF A B
    lfbot = inr (Kc fbb)

    sl : {{Semilattice A}} -> Semilattice (ListF A B)
    sl {A} {B} = Semilattice-:+: {H = K FTop} {J = K FBot} {M = ListF A} (Kc ftt) (Kc fbb)
      {{scH = FSC {{GSC}}}}
      {{scJ = GSC}}
      {{sc+ = FSC {{FSC {{idSC}}}}}}

    --open Semilattice (sl {A = T} {B = T})
    instance _ = sl

    test : ListF T T
    test = []c <> (tt ::)
