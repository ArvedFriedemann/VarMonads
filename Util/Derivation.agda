{-# OPTIONS --type-in-type #-}
module Util.Derivation where

_derives_ : (Set -> Set) -> (Set -> Set) -> Set
K derives P = forall {A} -> {{K A}} -> P A
