{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module Util.Monad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M : Set -> Set
    MT : (Set -> Set) -> Set -> Set

module _ {M : Set -> Set} {{mon : Monad M}} where

  void : M A -> M T
  void m = m >> return tt

  iterateM : Nat -> (A -> M A)-> A -> M A
  iterateM 0 _ x = return x
  iterateM (suc n) f x = f x >>= iterateM n f

  when : Bool -> M A -> M T
  when true m = void m
  when false m = return tt

  loop : List A -> B -> (A -> B -> M B) -> M B
  loop {A} {B} lst def f = loop' lst f def
    where
      loop' : List A -> (A -> B -> M B) -> B -> M B
      loop' [] f b0 = return b0
      loop' (x :: lst) f b0 = f x b0 >>= loop' lst f

record MonadTrans (MT : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{mon : Monad M}} -> M A -> MT M A

stateTMonadTrans : MonadTrans (StateT S)
stateTMonadTrans = record { liftT = \m s -> (_, s) <$> m }

open MonadTrans {{...}}
open MonadState {{...}} hiding (_<$>_; _>>_; _>>=_; return)

MonadReaderFromState :
  {{mon : Monad M}}
  {{mt : MonadState S M}} ->
  MonadReader S M
MonadReaderFromState = record {
  monad = it ;
  reader = _<$> get ;
  local = \f m -> get >>= \s -> put (f s) >> m >>= \r -> put s >> return r }
