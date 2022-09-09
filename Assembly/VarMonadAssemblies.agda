{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
module Assembly.VarMonadAssemblies where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Assembly.StdVarMonad
open import BasicVarMonads.Constructions
open import BasicVarMonads.ThresholdVarMonad
open import BasicVarMonads.ConstrainedVarMonad
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
  _ = MonadReaderStateT
  _ = MonadStateTId
  _ = MonadFNCDVarMon
  _ = PlainMonadSTM
  _ = ISTOTVar
  _ = ISTOSVar
  _ = PEqToEq
  _ = PEqTVar
  cISTOTVar : {{ISTO (Sigma Set V)}} -> ISTO (TVar K V S)
  cISTOTVar = FromSigmaISTO {{isto = ISTOTVar}}

  ThresholdVarMonad=>ConstrDefVarMonad : {{tvm : ThresholdVarMonad K M V}} -> ConstrDefVarMonad K M V
  ThresholdVarMonad=>ConstrDefVarMonad {{tvm}} = record {
      new = new ;
      read = read ;
      write = write }
    where open ThresholdVarMonad tvm

readerTVM : {{mon : Monad M}} -> ThresholdVarMonad K M V -> ThresholdVarMonad K (StateT (List (V S)) M) V
readerTVM = liftThresholdVarMonad \m s -> (_, s) <$> m

open ConnectionOperations

stdSpecMonad : Set -> Set
stdSpecMonad = FMFT defaultVarMonadStateM

stdSpecK = SpecK stdK stdSpecMonad

stdBranchingVarMonadM : Set -> Set
stdBranchingVarMonadM = (StateT (List (TVar stdSpecK NatPtr T))
  (FNCDVarMon stdK (TVar stdSpecK NatPtr)))

stdBranchingVarMonadV : Set -> Set
stdBranchingVarMonadV = TVar stdK (SVar (TVar stdSpecK NatPtr) T)

stdBranchingVarMonadS : Set
stdBranchingVarMonadS = TVar stdSpecK NatPtr T

stdBranchingVarMonad : BranchingVarMonad stdK stdBranchingVarMonadM stdBranchingVarMonadV stdBranchingVarMonadS
stdBranchingVarMonad = let tvm = readerTVM (SpecialFreeThresholdVarMonad {M = stdSpecMonad } {V = NatPtr}) in
        ThresholdVarMonad=>BranchingVarMonad
          {S = T}
          {{eq = PEqToEq {{ PEqTVar {K = stdSpecK} }} }}
          {{bvm = ThresholdVarMonad=>ConstrDefVarMonad {{ tvm }} }}
          {{tvm = tvm }}

open import MiscMonads.ConcurrentMonad

instance
  _ = FMFTMonad

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

LiftedStdBranchingVarMonad : ((Set -> Set) -> Set -> Set) -> Set
LiftedStdBranchingVarMonad L = BranchingVarMonad stdK
                                  (L stdBranchingVarMonadM)
                                  stdBranchingVarMonadV
                                  stdBranchingVarMonadS

stdForkingVarMonadM : Set -> Set
stdForkingVarMonadM = FMFT stdBranchingVarMonadM

stdForkingVarMonad : LiftedStdBranchingVarMonad FMFT
stdForkingVarMonad = liftBranchingVarMonad liftF stdBranchingVarMonad

open runFreeThresholdVarMonadPropagation
{-}
runFNCDVarMon : FNCDVarMon stdK (TVar _ NatPtr) A -> FMFT defaultVarMonadStateM T
runFNCDVarMon = runFNCD {K = stdK}
                  {{mvm = defaultForkModifyVarMonad}}
                  {{mf = FMFTMonadFork}}
                  {{keq = stdKEq}}
-}

runStdForkingVarMonad : stdForkingVarMonadM B -> stdBranchingVarMonadM A -> T
runStdForkingVarMonad m r = {! runFNCD (void $ propagate m [])!}
