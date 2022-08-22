{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module MiscMonads.ConcurrentMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Monad
open import Category.Monad.State renaming (RawMonadState to MonadState)

private
  variable
    A S : Set
    M M' : Set -> Set
    S' : (Set -> Set) -> Set

record MonadFork (M : Set -> Set) : Set where
  field
    fork : M A -> M T
    overlap {{mon}} : Monad M

dfsFork : {{mon : Monad M}} -> MonadFork M
dfsFork = record { fork = \ m -> m >> return tt }

{-}
open MonadState {{...}} using (get; put; modify)

instance
  StateTMS : {{mon : Monad M}} ->  MonadState S (StateT S M)
  StateTMS {S = S} {{mon}} = StateTMonadState S mon

  StateTMon : {{mon : Monad M}} -> Monad (StateT S M)
  StateTMon {S = S} {{mon}} = StateTMonad S mon
-}

RecStateT : (S' : (Set -> Set) -> Set) (M : Set -> Set) (A : Set) -> Set
RecStateT S' M A = forall M' -> S' M' -> M (A -x- S' M')

ST : ((Set -> Set) -> Set) -> (Set -> Set) -> Set
ST S' M = S' (RecStateT S' M)

runRecStateT : RecStateT S' M A -> ST S' M -> M (A -x- ST S' M)
runRecStateT m s = m _ s

RecStateTMonadState : {{mon : Monad M}} -> MonadState (ST S' M) (RecStateT S' M)
RecStateTMonadState = record {
  monad = record {
    return = \x _ s -> return (x , s) ;
    _>>=_ = \m f _ s -> m _ s >>= \ {(a , s') -> f a _ s'} } ;
  get = \_ s -> return ({!   !} , s) ;
  put = \x _ s -> return (tt , {!!}) }

bfsFork : {{mon :  Monad M}} -> MonadFork (StateT (List (M' T)) M)
bfsFork = record {
    fork = \ m -> {!!};
    mon = {! !}
  }
