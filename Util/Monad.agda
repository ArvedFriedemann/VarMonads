{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module Util.Monad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M : Set -> Set
    MT MT' : (Set -> Set) -> Set -> Set

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

record MonadRun (MT : (Set -> Set) -> Set -> Set) : Set where
  field
    run : {{mon : Monad M}} -> MT M A -> M A
    overlap {{mt}} : MonadTrans MT


MonadStateTFromTrans : {{monT : Monad (MT M)}} {{mon : Monad M}} {{mt : MonadTrans MT}} {{ms : MonadState S M}} -> MonadState S (MT M)
MonadStateTFromTrans {{monT}} {{mon}} {{mt}} {{ms}} = record {
  monad = it ;
  get = liftT get ;
  put = liftT o put }
  where
    open MonadState ms
    open MonadTrans mt

MonadTransTrans :
  {{mt : MonadTrans MT}}
  {{mt' : MonadTrans MT'}}
  {{mon : forall {M} -> {{mon' : Monad M}} -> Monad (MT' M)}}
  -> MonadTrans (MT o MT')
MonadTransTrans {{mt}} {{mt'}} = record { liftT = liftTMT o liftTMT' }
  where
    open MonadTrans mt renaming (liftT to liftTMT)
    open MonadTrans mt' renaming (liftT to liftTMT')

open MonadTrans {{...}}

MonadTransStateT : MonadTrans (StateT S)
MonadTransStateT = record { liftT = \m s -> (_, s) <$> m }

open MonadState {{...}} hiding (_<$>_; _>>_; _>>=_; return)


MonadReaderFromState :
  {{mon : Monad M}}
  {{mt : MonadState S M}} ->
  MonadReader S M
MonadReaderFromState = record {
  monad = it ;
  reader = _<$> get ;
  local = \f m -> get >>= \s -> put (f s) >> m >>= \r -> put s >> return r }

open MonadReader {{...}}
open MonadRun {{...}}

MonadReaderFromRun :
  {{mon : Monad M}}
  {{mont : Monad (MT M)}}
  {{mred : MonadReader S M}}
  {{mr : MonadRun MT}} ->
  MonadReader S (MT M)
MonadReaderFromRun = record {
  monad = it ;
  reader = liftT o reader ;
  local = \f -> liftT o local f o run }
