{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module Assembly.VarMonadAssemblies where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Assembly.StdVarMonad
open import BasicVarMonads.Constructions
open import BasicVarMonads.ThresholdVarMonad
open import BasicVarMonads.ConstrainedVarMonad
open import BasicVarMonads.ModifyVarMonad
open import Util.Lattice
open import Util.Derivation
open import Util.PointerEquality
open import Util.Monad
open import SpecialVarMonads.BranchingVarMonad
open import MiscMonads.ConcurrentMonad

private
  variable
    A B S : Set
    K M V : Set -> Set

stdK = \A -> Eq A -x- BoundedMeetSemilattice A

instance
  stdKEq : stdK derives Eq
  stdKEq {{k}} = fst k

  stdKBoundedMeetSemilattice : stdK derives BoundedMeetSemilattice
  stdKBoundedMeetSemilattice {{k}} = snd k

  --stdKTup : {{eq : Eq A}} -> {{sl : BoundedMeetSemilattice A}} -> stdK A
  --stdKTup {{eq}} {{sl}} = eq , sl

  stdKSVarPType : {{peq : PEq V}} -> {{isto : ISTO (V S)}} -> stdK derives (stdK o SVarPType V S)
  stdKSVarPType {{peq = peq}} = (record { _==_ = \{(a1 , m1 , p1) (a2 , m2 , p2) -> a1 == a2 } }) , --WARNING : not correct Eq instance!
                  (record { bsl = record {
                    sl = record { _<>_ = \{(a1 , m1 , p1) (a2 , m2 , p2) ->
                      (a1 /\ a2) ,
                      union m1 m2 ,
                      (do
                        (SVarC T p1') <- p1
                        (SVarC _ p2') <- p2
                        whenMaybe (p1' =p= p2') (SVarC T p1')
                      )} } ;
                    neut = top , empty , nothing } })
    where
      open PEq {{...}}
      instance
        _ = PEqTVar
      open BoundedMeetSemilattice {{...}}
      instance
        _ = MonadMaybe

  -- stdKTup : {{ka : stdK A}} -> {{kb : stdK B}} -> stdK (A -x- B)
  -- stdKTup = {!!}
  --
  -- stdKMaybe : stdK derives (stdK o Maybe)
  -- stdKMaybe = {!!}
  --
  -- stdKMap : {{isto : ISTO A}} -> stdK (Map A B)
  -- stdKMap = {!!}

  --stdKTVar : stdK (TVar stdK V S)
  --stdKTVar = (record { _==_ = {!   !} }) , {!   !}

  stdKT : stdK T
  stdKT = (record { _==_ = const $ const true }) ,
          (record { bsl = record { sl = record { _<>_ = const $ const tt } ; neut = tt } })

  {-}
  stdKTup : {{ka : stdK A}} -> {{kb : stdK B}} -> stdK (A -x- B)
  stdKTup {{ka}} {{kb}} = {!!}

  stdKMaybe : stdK (Maybe A)
  stdKMaybe = {!!}

  stdKMap : {{isto : ISTO A}} -> stdK (Map A B)
  stdKMap = {!!}
  -}

stdLatMon = BaseVarMonad=>ConstrVarMonad {K = stdK} {{defaultVarMonad}}

record UniversalVarMonad (K M V : Set -> Set) (VS : Set) : Set where
  field
    bvm : BranchingVarMonad K M V VS
    mf : MonadFork M
  open BranchingVarMonad bvm public
  open MonadFork mf public

instance
  _ = ISTONatPtr
  _ = PEqNatPtr
  _ = MonadStateT
  _ = MonadStateStateT
  _ = MonadTransStateT
  _ : Monad id
  _ = record {
    return = id ;
    _>>=_ = \a f -> f a }
  -- _ : {{monFMFT : Monad (FMFT M) }}{{mon : Monad M}} {{ms : MonadState S M}} -> MonadState S (FMFT M)
  -- _ = MonadStateTFromTrans {{mt = FMFTMonadTrans}}
  -- _ = MonadTransTrans
  -- _ = MonadReaderFromState
  -- _ = MonadReaderFromRun

  -- _ = MonadStateTId

  _ = MonadFNCDVarMon
  _ = PlainMonadSTM
  _ = FMFTMonad
  _ = FMFTMonadFork
  _ = FMFTMonadTrans
  -- _ = FMFTMonadRun
  _ = ISTOTVar
  _ = ISTOSVar
  --_ = PEqToEq
  _ = PEqTVar
  cISTOTVar : {{ISTO (Sigma Set V)}} -> ISTO (TVar K V S)
  cISTOTVar = FromSigmaISTO {{isto = ISTOTVar}}

open MonadTrans {{...}}

readerTVM : {{mon : Monad M}} -> ThresholdVarMonad K M V -> ThresholdVarMonad K (StateT (List (V S)) M) V
readerTVM = liftThresholdVarMonad liftT

forkTVM : {{mon : Monad M}} -> ThresholdVarMonad K M V -> ThresholdVarMonad K (FMFT M) V
forkTVM = liftThresholdVarMonad liftF

open ConnectionOperations

stdSpecMonad : Set -> Set
stdSpecMonad = FMFT defaultVarMonadStateM

stdSpecModifyVarMonad : ModifyVarMonad stdSpecMonad NatPtr
stdSpecModifyVarMonad = liftModifyVarMonad liftF defaultModifyVarMonad

stdSpecK = SpecK stdK stdSpecMonad


stdBranchingVarMonadS : Set
stdBranchingVarMonadS = TVar (SpecK stdK stdSpecMonad) NatPtr T

stdSubM : Set -> Set
stdSubM = StateT (List stdBranchingVarMonadS)
              (FNCDVarMon stdK (TVar (SpecK stdK stdSpecMonad) NatPtr))

stdForkingPrepM : Set -> Set
stdForkingPrepM = StateT (List (stdSubM T)) stdSubM

stdBranchingVarMonadM : Set -> Set
stdBranchingVarMonadM = FMFT stdSubM --stdForkingPrepM

stdBranchingVarMonadV : Set -> Set
stdBranchingVarMonadV = TVar stdK (SVar (TVar (SpecK stdK stdSpecMonad) NatPtr) T)


instance
  _ = FMFTMonad

  --better instance than the "fromRun" instance as it does not rely on a run instance
  FMFTMonadRead : {{mr : MonadReader S M}} -> MonadReader S (FMFT M)
  FMFTMonadRead {S = S} {M = M} = record {
    monad = FMFTMonad ;
    reader = \f ->  liftF (reader f) ;
    local = local'}
    where
      open MonadReader {{...}}
      local' : (S -> S) -> FMFT M A -> FMFT M A
      local' f (liftF x) = liftF (local f x)
      local' f (forkF m) = forkF (local' f m)
      local' f (returnF x) = returnF x
      local' f (bindF m mf) = bindF (local' f m) (local' f o mf)

stdBranchingVarMonad : BranchingVarMonad stdK stdBranchingVarMonadM stdBranchingVarMonadV stdBranchingVarMonadS
stdBranchingVarMonad = let
    tvm = forkTVM $ readerTVM (SpecialFreeThresholdVarMonad {M = stdSpecMonad } {V = NatPtr})
    instance
      _ = PEqToEq
  in ThresholdVarMonad=>BranchingVarMonad
          {S = T}
          {{eq = PEqToEq {{ PEqTVar {K = stdSpecK} }} }}
          {{bvm = ThresholdVarMonad=>ConstrDefVarMonad {{ tvm }} }}
          {{tvm = tvm }}
          {{mr = FMFTMonadRead {{ MonadReaderFromState }} }}


stdMonadFork : MonadFork stdBranchingVarMonadM
stdMonadFork = it

open runFreeThresholdVarMonadPropagation

instance
  _ = stdSpecModifyVarMonad

-- runStdForkingVarMonad : stdBranchingVarMonadM B -> (B -> stdBranchingVarMonadM A) -> Maybe A
-- runStdForkingVarMonad m r = runDefVarMonad $ propagate $ propagateL m >>= propagateL o r
--   where
--     instance
--       _ : Monad (stdSpecMonad o Maybe)
--       _ = record { return = return o just ; _>>=_ = \m f -> _>>=_ {M = stdSpecMonad} m (\mab -> maybe' id (return nothing) (f <$> mab)) }
--
--     propagateL : stdBranchingVarMonadM A -> stdSpecMonad (Maybe A)
--     propagateL = runFMFTLift {M' = stdSpecMonad o Maybe} (\m -> _>>_ {M = stdSpecMonad} m (return $ just tt) ) (\m -> fst <$> runFNCD (m []))

runStdForkingVarMonad : stdBranchingVarMonadM B -> (B -> stdBranchingVarMonadM A) -> Maybe A
runStdForkingVarMonad m r = (fst <$>_) $ maybe' id (nothing , []) $ runDefVarMonad $
                              propagate
                                {M = StateT (List (FMFT defaultVarMonadStateM T)) (defaultVarMonadStateM o Maybe)}
                                {M' = defaultVarMonadStateM}
                                {{mon = mond }}
                                {{ms = MonadStateStateT {{ compMaybe {M = defaultVarMonadStateM} }} }}
                                (\m s -> _<$>_ {{r = defaultVarMonadStateMonad}} (just o (_, s)) m )
                                (\m s -> _>>=_ {{r = defaultVarMonadStateMonad}} (m s) \mab -> return {{r = defaultVarMonadStateMonad}} (maybe' (\r -> just r) (just (tt , s)) mab))--m s >>= return o maybe' id (tt , s))
                                ( (propagateL m) >>= (maybe' (propagateL o r) (return nothing)) )
                                []
                                 -- {M = StateT (List (FMFT defaultVarMonadStateM T)) (defaultVarMonadStateM o Maybe)}
                                 -- {M' = defaultVarMonadStateM o Maybe}
                                 -- {{mon = mond}}
                          -- runDefVarMonad $
                          --     propagate $
                          --     runFNCD {M = stdSpecMonad}
                          --       (fst <$> (propagateL m >>= propagateL o r) [])
    where
      _ : Monad (defaultVarMonadStateM)
      _ = it

      compMaybe : {{mon : Monad M}} -> Monad (M o Maybe)
      compMaybe {M = M} = record { return = return o just ; _>>=_ = \m f -> _>>=_ {M = M} m (\mab -> maybe' id (return nothing) (f <$> mab)) }
      instance
        _ = compMaybe {M = stdSpecMonad}
        _ = compMaybe {M = defaultVarMonadStateM}

      mond : Monad (StateT (List (FMFT defaultVarMonadStateM T)) (defaultVarMonadStateM o Maybe))
      mond = MonadStateT {{compMaybe {M = defaultVarMonadStateM}}}

      defaultVarMonadStateMonad : Monad (defaultVarMonadStateM)
      defaultVarMonadStateMonad = it

      propagateL : forall {A} -> stdBranchingVarMonadM A -> stdSpecMonad (Maybe A)
      propagateL m = (fst o fst) <$> propagate
                              {M = StateT (List (FMFT stdSubM T)) $ StateT (List stdBranchingVarMonadS) $ stdSpecMonad o Maybe}
                              {M' = stdSubM}
                              (\m sf sb -> (\{(a , sb') -> (a , sf) , sb'}) <$> runFNCD {M = stdSpecMonad} (m sb) )
                              (\ m sf sb -> m sf sb >>= return o maybe' id ((tt , sf) , sb) )
                              m
                              []
                              []



{-NOTES on problems:

this does not work as the propagation from the forking monad just puts the actions after each other.
When doing that with the continuation monad, that does not work because it might get stuck in a fork,
but then delays all subsequent computation as well, even though that should be independent...

runStdForkingVarMonad : stdBranchingVarMonadM B -> (B -> stdBranchingVarMonadM A) -> Maybe A
runStdForkingVarMonad m r = runDefVarMonad $
                              propagate $
                              runFNCD {M = stdSpecMonad}
                                (fst <$> (propagate m >>= propagate o r) [])
-}
