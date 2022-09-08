{-# OPTIONS --type-in-type #-}
module Util.PointerEquality where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set
    V F G : Set -> Set

record PEq (V : Set -> Set) : Set where
  field
    _=p=_ : forall {A B} -> V A -> V B -> Bool

record PCmp (V : Set -> Set) : Set where
  field
    _<p_ : forall {A B} -> V A -> V B -> Bool

PEqToEq : {{peq : PEq V}} -> Eq (V A)
PEqToEq = record { _==_ = _=p=_ }
  where open PEq {{...}}

STO-PEqCmp : {{peq : PEq V}} -> {{pcmp : PCmp V}} -> {B : Set} -> Set
STO-PEqCmp {V = V} {{peq}} {{pcmp}} {B} = IsStrictTotalOrder {A = V B}
                                (\a b -> a =p= b === true)
                                (\a b -> a <p b === true)
  where
    open PEq peq
    open PCmp pcmp

FromSigmaISTO : {{isto : ISTO (Sigma Set V)}} -> ISTO (V A)
FromSigmaISTO {{sto}} = record {
    eq = \x y -> eq (_ , x) (_ , y) ;
    gr = \x y -> gr (_ , x) (_ , y) ;
    isto = record {
      isEquivalence = record {
        refl = \ {x} -> reflSTO ;
        sym = \ {x} {y} -> symSTO ;
        trans = \ {x} {y} {z} -> transSTO } ;
      trans = \ {x} {y} {z} -> transISTO ;
      compare = \ x y -> compareISTO (_ , x) (_ , y) }
  }
  where
    open ISTO sto
    open IsStrictTotalOrder isto renaming (trans to transISTO ; compare to compareISTO)
    open IsEquivalence isEquivalence renaming (refl to reflSTO ; sym to symSTO ; trans to transSTO)

ExtractSpecSTOFrom : {{isto : ISTO (Sigma Set V)}} -> (forall {A} -> F A -> V (G A)) -> ISTO (Sigma Set F)
ExtractSpecSTOFrom {{sto}} extract = record {
    eq = \{(_ , x) (_ , y) -> eq (_ , extract x) (_ , extract y) } ;
    gr = \{(_ , x) (_ , y) -> gr (_ , extract x) (_ , extract y) } ;
    isto = record {
      isEquivalence = record {
        refl = \ {(_ , x)} -> reflSTO ;
        sym = \ {(_ , x)} {(_ , y)} -> symSTO ;
        trans = \ {(_ , x)} {(_ , y)} {(_ , z)} -> transSTO } ;
      trans = \ {(_ , x)} {(_ , y)} {(_ , z)} -> transISTO ;
      compare = \ (_ , x) (_ , y) -> compareISTO (_ , extract x) (_ , extract y) }
  }
  where
    open ISTO sto
    open IsStrictTotalOrder isto renaming (trans to transISTO ; compare to compareISTO)
    open IsEquivalence isEquivalence renaming (refl to reflSTO ; sym to symSTO ; trans to transSTO)

ExtractISTOFrom : {{isto : ISTO (Sigma Set V)}} -> (forall {A} -> F A -> Sigma Set V) -> ISTO (Sigma Set F)
ExtractISTOFrom {{sto}} extract = record {
    eq = \{(_ , x) (_ , y) -> eq (extract x) (extract y) } ;
    gr = \{(_ , x) (_ , y) -> gr (extract x) (extract y) } ;
    isto = record {
      isEquivalence = record {
        refl = \ {(_ , x)} -> reflSTO ;
        sym = \ {(_ , x)} {(_ , y)} -> symSTO ;
        trans = \ {(_ , x)} {(_ , y)} {(_ , z)} -> transSTO } ;
      trans = \ {(_ , x)} {(_ , y)} {(_ , z)} -> transISTO ;
      compare = \ (_ , x) (_ , y) -> compareISTO (extract x) (extract y) }
  }
  where
    open ISTO sto
    open IsStrictTotalOrder isto renaming (trans to transISTO ; compare to compareISTO)
    open IsEquivalence isEquivalence renaming (refl to reflSTO ; sym to symSTO ; trans to transSTO)
