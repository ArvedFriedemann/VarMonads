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

record UniversalVarMonad (K M V : Set -> Set) : Set where
  field
    bvm : BranchingVarMonad K M V
    mf : MonadFork M
  open BranchingVarMonad bvm public
  open MonadFork mf public

instance
  _ = ISTONatPtr
  _ = PEqNatPtr
  _ = MonadStateT
  _ = MonadReaderStateT
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

--stdBranchingVarMonad : BranchingVarMonad K (StateT (List _) (FNCDVarMon K _) ) _
stdBranchingVarMonad = let tvm = readerTVM (FreeThresholdVarMonad {V = NatPtr}) in
        ThresholdVarMonad=>BranchingVarMonad
          {S = T}
          {{eq = PEqToEq {{PEqTVar {K = stdK} }} }}
          {{bvm = ThresholdVarMonad=>ConstrDefVarMonad {{ tvm }} }}
          {{tvm = tvm }}

--open import MiscMonads.ConcurrentMonad

--stdForkingVarMonad = liftThresholdVarMonad liftF stdBranchingVarMonad
