{-# OPTIONS --type-in-type #-}
module BasicVarMonads.BaseVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

variable
  A B : Set
  a a' : A
  b : B
  M V : Set -> Set

record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    read : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

infixl 1 _>>>_
_>>>_ : {{mon : Monad M}} -> M A -> M B -> M A
ma >>> mb = ma >>= \ x -> mb >> return x

record BaseVarMonadProp
    (bvm : BaseVarMonad M V) (_~_ : {A : Set} -> M A -> M A -> Set) : Set where
  open BaseVarMonad bvm
  _/~_ : {A : Set} -> M A -> M A -> Set
  a /~ b = ¬(a ~ b)
  field
    row1 : (v : V A) -> (write v a >> read v) ~ (return a)
    row2 : (v v' : V A) -> (v =/= v') ->
      (write v' a' >> read v) ~ (read v)
    newpt1 : (a : A) (m : M B) -> (new a >>= read) ~ return a
    newpt2 : (a : A) (m : M B) -> (new a >> m) ~ m
    newpt3 : (f : V A -> M B) -> forall v v' -> v =/= v' -> f v /~ f v' -> forall (a a' : A) -> (new a >>> new a' >>= f) /~ (new a' >>> new a' >>= f)
