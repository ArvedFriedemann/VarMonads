{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module MiscMonads.ConcurrentMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Util.Monad
open import Category.Monad.State renaming (RawMonadState to MonadState)
--open import Debug.Trace

private
  variable
    A B S : Set
    M M' M'' : Set -> Set
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

FMFTMonadFork : MonadFork (FMFT M)
FMFTMonadFork = record {
    fork = forkF ;
    mon = record { return = returnF ; _>>=_ = bindF }
  }

module _ where
  open MonadFork {{...}}

  MonadForkFromStateT : {{mf : MonadFork M}} -> {{mon : Monad (StateT S M)}} -> MonadFork (StateT S M)
  MonadForkFromStateT = record { fork = \m s -> fork (m s) >> return (tt , s) }

module _ where
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

-- {{ms : MonadState (ActList (FMFT M')) M}}
module _
    {{mon : Monad M}}
    (liftM : forall {A B} -> M' A -> (A -> M B) -> M B)
    (run : M T -> M T) where
  open MonadState {{...}} using () renaming (put to putS; get to getS; modify to modifyS)

  {-# TERMINATING #-}
  runFMFT : (A -> M B) -> FMFT M' A -> M B
  runFMFT cont (liftF m) = liftM m cont
  runFMFT cont (forkF m) = run (runFMFT return (void {{mon = FMFTMonad}} m)) >>= cont
  runFMFT cont (returnF x) = cont x
  runFMFT cont (bindF m f) = runFMFT (runFMFT cont o f) m

  -- flush : M T
  -- flush = getS >>= \s -> putS [] >> (void $ sequenceM (map (run o runFMFT (trace "reached last return of fork continuation" return) o (trace "running fork")) s))

  propagate : FMFT M' A -> M A
  propagate = runFMFT return
  -- {-# TERMINATING #-}
  -- propagate : FMFT M' A -> M A
  -- propagate m = do
  --     a <- runFMFT return m
  --     propagate'
  --     return a
  --   where
  --     propagate' : M T
  --     propagate' = getS >>= \{
  --         [] -> return tt ;
  --         _  -> flush >> propagate'
  --       }

module _ {M' : Set -> Set} {{mon : Monad M}} where

  instance
    _ = MonadStateStateT
    _ = MonadStateT
    _ = MonadTransStateT

  open MonadTrans {{...}}

  propagateInterrupted : (forall {A B} -> M' A -> (A -> MaybeT M B) -> MaybeT M B) -> FMFT M' A -> MaybeT M A
  propagateInterrupted liftM fmft = propagate {{mon = MonadMaybeT}} liftM (\m -> m >>= maybe' (return o just) (return $ just tt)) fmft

  -- propagateInterrupted : (forall {A B} -> M' A -> (A -> MaybeT M B) -> MaybeT M B) -> FMFT M' A -> MaybeT M A
  -- propagateInterrupted liftM fmft = _<$>_ {M = M} fst $ propagate
  --   {M = MaybeT $ StateT (ActList (FMFT M')) M}
  --   {{mon = MonadMaybeT {{MonadStateT}}}}
  --   {{ms = MonadStateTFromTrans {{monT = MonadMaybeT }} {{mon = MonadStateT}} {{mt = MonadTransMaybeT }} {{ms = MonadStateStateT }} }}
  --   (\m cont s -> liftM m (\a -> return $ just $ cont a s) >>= maybe' id (return (nothing , s)))
  --   (\ m s -> m s >>= \{(_ , s') -> return (just tt , s')})
  --   fmft
  --   []


module _ {M' : Set -> Set} {{mon : Monad M}} where

  instance
    _ = MonadStateT
    _ = MonadStateStateT
    _ = MonadTransStateT

  open MonadTrans {{...}}

  open import AgdaAsciiPrelude.TrustMe

  propagateNormal : (forall {A} -> M' A -> M A) -> FMFT M' A -> M A
  propagateNormal liftM fmft = propagate (\m cont -> liftM m >>= cont) id fmft

  -- propagateNormal : (forall {A} -> M' A -> M A) -> FMFT M' A -> M A
  -- propagateNormal liftM fmft = fst <$> propagate (\m cont s -> liftM m >>= flip cont s) id fmft []
    --(maybe' id (trustVal tt) ) <$> propagateInterrupted (\m -> just <$> liftM m) fmft

-- FMFTMonadRun : MonadRun FMFT
-- FMFTMonadRun = record { run = propagate }
--   where
--     instance
--       _ = FMFTMonad
--       _ = FMFTMonadTrans


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
