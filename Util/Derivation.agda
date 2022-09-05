{-# OPTIONS --type-in-type #-}
module Util.Derivation where

_derives_ : (Set -> Set) -> (Set -> Set) -> Set
K derives P = forall {A} -> {{k : K A}} -> P A

always : (Set -> Set) -> Set
always K = forall {A} -> K A

it : {A : Set} -> {{a : A}} -> A
it {{a}} = a
