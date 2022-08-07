{-# OPTIONS --type-in-type #-}
module MTCDatatypes where

open import AgdaAsciiPrelude.AsciiPrelude
open import Fixpoints

open import Category.Functor using () renaming (RawFunctor to Functor)
open Functor {{...}}

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

data ListF (A : Set) (B : Set) : Set where
  nil : ListF A B
  lcons : A -> B -> ListF A B

instance
  listFFunctor : Functor (ListF A)
  listFFunctor = record { _<$>_ = \ {
    f nil -> nil; 
    f (lcons x xs) -> lcons x (f xs)} }