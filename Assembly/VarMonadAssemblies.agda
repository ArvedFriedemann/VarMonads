{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
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
  _ = MonadReaderFromState
  -- _ = MonadReaderFromRun
  _ = MonadStateTId
  _ = MonadFNCDVarMon
  _ = PlainMonadSTM
  _ = FMFTMonad
  _ = FMFTMonadFork
  _ = FMFTMonadTrans
  _ = FMFTMonadRun
  _ = ISTOTVar
  _ = ISTOSVar
  _ = PEqToEq
  _ = PEqTVar
  cISTOTVar : {{ISTO (Sigma Set V)}} -> ISTO (TVar K V S)
  cISTOTVar = FromSigmaISTO {{isto = ISTOTVar}}

open MonadTrans {{...}}

readerTVM : {{mon : Monad M}} -> ThresholdVarMonad K M V -> ThresholdVarMonad K (StateT (List (V S)) M) V
readerTVM = liftThresholdVarMonad liftT

forkTVM : ThresholdVarMonad K M V -> ThresholdVarMonad K (FMFT M) V
forkTVM = liftThresholdVarMonad liftF

open ConnectionOperations

stdSpecMonad : Set -> Set
stdSpecMonad = FMFT defaultVarMonadStateM

stdSpecModifyVarMonad : ModifyVarMonad stdSpecMonad NatPtr
stdSpecModifyVarMonad = liftModifyVarMonad liftF defaultModifyVarMonad

stdSpecK = SpecK stdK stdSpecMonad


stdBranchingVarMonadS : Set
stdBranchingVarMonadS = TVar (SpecK stdK stdSpecMonad) NatPtr T

stdBranchingVarMonadM : Set -> Set
stdBranchingVarMonadM = FMFT $ StateT
  (List stdBranchingVarMonadS)
  (FNCDVarMon stdK (TVar (SpecK stdK stdSpecMonad) NatPtr))

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
  in ThresholdVarMonad=>BranchingVarMonad
          {S = T}
          {{eq = PEqToEq {{ PEqTVar {K = stdSpecK} }} }}
          {{bvm = ThresholdVarMonad=>ConstrDefVarMonad {{ tvm }} }}
          {{tvm = tvm }}

stdMonadFork : MonadFork stdBranchingVarMonadM
stdMonadFork =

open runFreeThresholdVarMonadPropagation

instance
  _ = stdSpecModifyVarMonad

runStdForkingVarMonad : stdBranchingVarMonadM B -> (B -> stdBranchingVarMonadM A) -> Maybe A
runStdForkingVarMonad m r = runDefVarMonad $
                              propagate $
                              runFNCD {M = stdSpecMonad}
                                (fst <$> (propagate m >>= propagate o r) [])

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
