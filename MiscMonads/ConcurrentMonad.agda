{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module MiscMonads.ConcurrentMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Util.Monad
open import Category.Monad.State renaming (RawMonadState to MonadState)

private
  variable
    A B S : Set
    M M' : Set -> Set
    MT : (Set -> Set) -> Set -> Set
    S' : (Set -> Set) -> Set

record MonadFork (M : Set -> Set) : Set where
  field
    fork : M A -> M T
    overlap {{mon}} : Monad M

dfsFork : {{mon : Monad M}} -> MonadFork M
dfsFork = record { fork = \ m -> m >> return tt }


record MonadSTM (M' M : Set -> Set) : Set where
  field
    atomically : M' A -> M A
    overlap {{mon}} : Monad M
    overlap {{mon'}} : Monad M'

PlainMonadSTM : {{mon : Monad M}} -> MonadSTM M M
PlainMonadSTM = record { atomically = id }

open MonadState {{...}} using (get; put; modify)
{-}
instance
  StateTMS : {{mon : Monad M}} ->  MonadState S (StateT S M)
  StateTMS {S = S} {{mon}} = StateTMonadState S mon

  StateTMon : {{mon : Monad M}} -> Monad (StateT S M)
  StateTMon {S = S} {{mon}} = StateTMonad S mon
-}
ActList : (Set -> Set) -> Set
ActList M = List (M T)

{-}
naiveFork : {{Monad M}} -> MonadFork (StateT (ActList M) M)
naiveFork = record { fork = \m -> modify {!!} }
-}

--FreeMonadForkT
data FMFT (M : Set -> Set) : Set -> Set where
  liftF : M A -> FMFT M A
  forkF : FMFT M A -> FMFT M T
  returnF : A -> FMFT M A
  bindF : FMFT M A -> (A -> FMFT M B) -> FMFT M B

FMFTMonadFork : {{mon : Monad M}} -> MonadFork (FMFT M)
FMFTMonadFork = record {
    fork = forkF ;
    mon = record { return = returnF ; _>>=_ = bindF }
  }

open MonadTrans {{...}}
open MonadRun {{...}}
open MonadFork {{...}}

FMFTMonadForkFromRun : {{mon : Monad (MT M)}} {{mt : MonadRun MT}} {{mf : MonadFork M}} -> MonadFork (MT M)
FMFTMonadForkFromRun = record { fork = liftT o fork o run }

FMFTMonad : Monad (FMFT M)
FMFTMonad = record {
  return = returnF ;
  _>>=_ = bindF }

FMFTMonadTrans : MonadTrans FMFT
FMFTMonadTrans = record { liftT = liftF }

runFMFT : {{mon : Monad M}} -> FMFT M A -> M (A -x- ActList (FMFT M))
runFMFT (liftF m) = (_, []) <$> m
runFMFT (forkF m) = return ( tt , [ void {{mon = FMFTMonad}} $ m ])
runFMFT (returnF x) = return (x , [])
runFMFT (bindF m f) = do
  (a , lst) <- runFMFT m
  (b , lst') <- runFMFT (f a)
  return (b , lst ++ lst') --TODO: inefficient

module _ where
  -- module monadStateId {S : Set} where
  --   open Monad (MonadStateTId {S = S}) renaming (return to returnS; _>>_ to _>>S_; _>>=_ to _>>=S_; _<$>_ to _<$>S_) public
  --   open MonadState (MonadStateStateTId {S = S}) using (get; put) renaming (modify to modifyS) public
  -- open monadStateId
  instance
    _ = FMFTMonad

  runFMFTLift : {{mon' : Monad M'}} ->
    (forall {A} -> M' A -> M' T) ->
    (forall {A} -> M A -> M' A) ->
    FMFT M A -> M' A
  runFMFTLift runAtom liftT (liftF x) = liftT x
  runFMFTLift runAtom liftT (forkF m) = runAtom $ runFMFTLift runAtom liftT m
  runFMFTLift runAtom liftT (returnF x) = return x
  runFMFTLift runAtom liftT (bindF m f) = runFMFTLift runAtom liftT m >>= runFMFTLift runAtom liftT o f

flush : {{mon : Monad M}} -> ActList (FMFT M) -> M (ActList (FMFT M))
flush lst = concat <$> sequenceM (map ((snd <$>_) o runFMFT) lst)

boundedProp : {{mon : Monad M}} -> Nat -> FMFT M A -> M (ActList (FMFT M))
boundedProp n m = (snd <$> runFMFT m) >>= iterateM n flush

{-# TERMINATING #-}
propagate : {{mon : Monad M}} -> FMFT M A -> M A
propagate {M = M} m = do
    (a , lst) <- runFMFT m
    propagate' lst
    return a
  where
    propagate' : ActList (FMFT M) -> M (ActList (FMFT M))
    propagate' [] = return []
    propagate' m  = flush m >>= propagate'

-- flushLift : {{mon : Monad M'}} ->
--   (forall {A B} -> M A -> M' B) ->
--   ActList (FMFT M) ->
--   M' (ActList (FMFT M))
--   -- TODO : Problem is that we need to get the list of next actions somehow...in a guaranteed fashion...
--   -- SOLUTION : lift this whole thing into a state transformer.
--   -- Run the original and prolly not get a value, but make it still gather the forks somehow...
-- flushLift liftT lst = concat <$> sequenceM (map ((snd <$>_) o runFMFT) lst)

FMFTMonadRun : MonadRun FMFT
FMFTMonadRun = record { run = propagate }
  where
    instance
      _ = FMFTMonad
      _ = FMFTMonadTrans

{-}

instance
  StateTMS : {{mon : Monad M}} ->  MonadState S (StateT S M)
  StateTMS {S = S} {{mon}} = StateTMonadState S mon

  StateTMon : {{mon : Monad M}} -> Monad (StateT S M)
  StateTMon {S = S} {{mon}} = StateTMonad S mon
-}

open import AgdaAsciiPrelude.TrustMe


RecStateT : (S' : (Set -> Set) -> Set) (M : Set -> Set) (A : Set) -> Set
RecStateT S' M A = forall M' -> S' M' -> M (A -x- S' M')

ST : ((Set -> Set) -> Set) -> (Set -> Set) -> Set
ST S' M = S' (RecStateT S' M)

runRecStateT : ST S' M -> RecStateT S' M A -> M (A -x- ST S' M)
runRecStateT s m = m _ s

RecStateTMonad : {{mon : Monad M}} -> Monad (RecStateT S' M)
RecStateTMonad = record {
  return = \x _ s -> return (x , s) ;
  _>>=_ = \m f _ s -> m _ s >>= \ {(a , s') -> f a _ s'} }

--WARNING! This only works when RexStateT S' M is operated on ST S' M!
RecStateTMonadState : {{mon : Monad M}} -> MonadState (ST S' M) (RecStateT S' M)
RecStateTMonadState = record {
  monad = RecStateTMonad ;
  get = \_ s -> return (trustVal s , s) ;
  put = \x _ s -> return (tt , trustVal x) }

instance
  _ = RecStateTMonad
  _ = RecStateTMonadState
  _ = MonadMaybe

{-}
stateTest : Maybe Nat
stateTest = fst <$> runRecStateT {S' = \M -> (Nat -x- M T)} {M = Maybe} (3 , return tt)
  (put (4 , return tt) >> get >>= \{ (x , m) -> return x })
-}

bfsFork : {{mon :  Monad M}} -> MonadFork (RecStateT ActList M)
bfsFork = record {
    fork = \ m -> modify (void m ::_)
  }

flush' : {{mon : Monad M}} -> RecStateT ActList M T
flush' = do
  s <- get
  put []
  void $ sequenceM s

propagate' : {{mon : Monad M}} -> Nat -> RecStateT ActList M (ActList (RecStateT ActList M))
propagate' n = sequenceM (replicate n flush') >> get
