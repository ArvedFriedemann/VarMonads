{-# OPTIONS --type-in-type #-}
module MTC.FunctorToolkit where
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

functor-:+: : {{Functor F}} -> {{Functor G}} -> Functor (F :+: G)
functor-:+: = {!!}

functor-K : Functor (K A)
functor-K = record { _<$>_ = \ {_ (Kc x) -> Kc x  } }


module Temp where
  ListF : Set -> Set -> Set
  ListF A = C :+: (K A :*: I)

  BinTreeF : Set -> Set -> Set
  BinTreeF A = C :+: (K A :*: I :*: I)

  module Liststuff where
    any' : Fix (ListF Bool) -> Bool
    any' = foldF \{
      [[_]] (inl c) -> false;
      [[_]] (inr (Kc x :c*: Kc xs)) -> x || [[ xs ]] }

    [] : Fix (ListF A)
    [] = In (inl (Kc tt))

    _::_ : A -> Fix (ListF A) -> Fix (ListF A)
    x :: xs = In (inr (Kc x :c*: Kc xs))

  {-
  record Unify (F : Set -> Set) : Set where
    field
      unifyAlg : Fix F -> Algebra F (Maybe $ Fix F)

  unifyK : {{Semilattice A}} -> Unify (K A)
  unifyK {A} {{sl}} = record {
      unifyAlg = \{f _ alg (Kc x) -> foldF (\{ _ [[_]] (Kc x') -> just $ In $ Kc $ x <> x' }) f }}
    where open Semilattice sl

  unify : {{Unify F}} -> Fix F -> Fix F -> Maybe (Fix F)
  unify {{uf}} f1 f2 = foldF (unifyAlg f1) f2
    where open Unify uf
    -}

  open Semilattice {{...}}

  FixSL : {{Functor F}} -> {{Semilattice (F (Fix F))}} -> Semilattice (Fix F)
  FixSL {F = F} = record {
      _<>_ = \f1 f2 -> In $ (Out f1) <> (Out f2) }

  KSL : {{Semilattice A}} -> Semilattice (K A B)
  KSL = record { _<>_ = \{
      (Kc a) (Kc a') -> Kc (a <> a')
    } }

  :*:SL : {{Semilattice (F B)}} -> {{Semilattice (G B)}} -> Semilattice ((F :*: G) B)
  :*:SL = record { _<>_ = \{
      (f1 :c*: g1) (f2 :c*: g2) -> (f1 <> f2) :c*: (g1 <> g2) } }

  :+:BSL : {{Semilattice (F B)}} -> {{Semilattice (G B)}} -> H B -> Semilattice ((F :+: G :+: H) B)
  :+:BSL {F} {B} {G} {H} def = record {
    _<>_ = _<>'_ }
    where
      _<>'_ : ((F :+: G :+: H) B) -> ((F :+: G :+: H) B) -> ((F :+: G :+: H) B)
      (inl x)       <>' (inl y)       = inl $ x <> y
      (inr (inl x)) <>' (inr (inl y)) = inr (inl $ x <> y)
      _             <>' _             = inr $ inr def

  open import Util.Monad
  open MonadFail {{...}}
  open import AgdaAsciiPrelude.Instances


  top : Fix (F :+: C :+: C)
  top = In (inr (inl (Kc tt)))

  bot : Fix (F :+: C :+: C)
  bot = In (inr (inr (Kc tt)))


  module _ {M : Set -> Set} {{mon : MonadFail M}} where

    toPartialFkt : Algebra F (M A) -> Fix (F :+: C :+: C) -> M A
    toPartialFkt alg = foldF \{
      [[_]] (inl f) -> alg [[_]] f;
      [[_]] (inr _) -> fail }

  record LatConstr (G : Set -> Set) : Set where
    field
      inj : forall {B} -> G B -> (G :+: C :+: C) B
      proj : forall {B} -> (G :+: C :+: C) B -> Maybe (G B)

  open LatConstr {{...}}

  LatAlgebra : (F G : Set -> Set) -> Set
  LatAlgebra F G = {{LatConstr G}} -> Algebra F (Maybe $ Fix (G :+: C :+: C))

  toPartialFkt' : (LatAlgebra F G) -> Fix (F :+: C :+: C) -> Fix (G :+: C :+: C)
  toPartialFkt' {G = G} alg = foldF \{
    [[_]] (inl f) -> fromMaybe top (alg {{latConstr}} (just o [[_]]) f);
    [[_]] (inr (inl _)) -> top;
    [[_]] (inr (inr _)) -> bot }
    where
      latConstr : LatConstr G
      latConstr = record {
        inj = inl ;
        proj = \{(inl g) -> just g; _ -> nothing} }
  module _ where
    instance
      _ = MaybeMonadFail
      _ = MonadMaybe

    [] : Fix (ListF A :+: C :+: C)
    [] = In (inl $ inl (Kc tt))

    infixr 5 _::_
    _::_ : A -> Fix (ListF A :+: C :+: C) -> Fix (ListF A :+: C :+: C)
    x :: xs = In (inl $ inr (Kc x :c*: Kc xs))

    any'' : Fix (ListF Bool :+: C :+: C) -> Maybe Bool
    any'' = toPartialFkt \{
        [[_]] (inl x) -> just false;
        [[_]] (inr (Kc true  :c*: Kc xs)) -> just true;
        [[_]] (inr (Kc false :c*: Kc xs)) -> [[ xs ]]
      }

    test : Maybe Bool
    test = any'' (false :: false :: top )--any'' (false :: true :: top )

    Tree = C :+: (I :*: I)

    leaf : Fix Tree
    leaf = In $ inl (Kc tt)

    node : Fix Tree -> Fix Tree -> Fix Tree
    node lft rgt = In (inr (Kc lft :c*: Kc rgt))

    nodeF : {{LatConstr Tree}} -> Fix (Tree :+: C :+: C) -> Fix (Tree :+: C :+: C) -> Fix (Tree :+: C :+: C)
    nodeF lft rgt = In (inj (inr (Kc lft :c*: Kc rgt)))

    leaf' : Fix (Tree :+: C :+: C)
    leaf' = In $ inl $ inl (Kc tt)

    node' : Fix (Tree :+: C :+: C) -> Fix (Tree :+: C :+: C) -> Fix (Tree :+: C :+: C)
    node' lft rgt = In (inl $ inr (Kc lft :c*: Kc rgt))

    swapAlg : {{Monad M}} -> Algebra Tree (M (Fix Tree))
    swapAlg [[_]] (inl x) = return leaf
    swapAlg [[_]] (inr ((Kc x) :c*: (Kc y))) = (| node [[ y ]] [[ x ]] |)

    swapAlg' : LatAlgebra Tree Tree
    swapAlg' [[_]] (inl x) = return leaf'
    swapAlg' [[_]] (inr (Kc x :c*: Kc y)) = (| node' [[ y ]] [[ x ]] |)

    swap : Fix (Tree :+: C :+: C) -> Maybe (Fix Tree)
    swap = toPartialFkt swapAlg

    swap' : Fix (Tree :+: C :+: C) -> (Fix (Tree :+: C :+: C))
    swap' = toPartialFkt' swapAlg'

    swapTest = swap (node' (node' top leaf') leaf')--swap (node' (node' leaf' leaf') leaf')
    swapTest2 : swap' (node' (node' top leaf') leaf') === (node' leaf' (node' leaf' top))
    swapTest2 = refl

    KFixSL : Semilattice A -> Semilattice (Fix (K A))
    KFixSL sla = FixSL {{{!!}}} {{KSL {{sla}} }}

  instance
    _ = functor-:+:
    _ = functor-K

  open Functor {{...}} renaming (_<$>_ to _<$>'_)

  typeof : Nat -> Set
  typeof n = {!!}

  Asm : Set -> Set
  Asm A = (n : Nat) -> A

  {-# TERMINATING #-}
  foldAsm : Algebra F A -> Asm (Fix (F :+: K Nat)) -> Fix (F :+: K Nat) -> A
  foldAsm alg asm = foldF \{
    [[_]] (inl f) -> alg [[_]] f;
    [[_]] (inr (Kc n)) -> foldAsm alg asm (asm n)
    }

  {-
  foldAsm : Algebra F A -> TAsm -> Fix (F o K Nat) -> A
  foldAsm alg asm = foldF \_ [[_]] -> alg _ \{(Kc n) -> [[ asm n _ ]]}
  -}
