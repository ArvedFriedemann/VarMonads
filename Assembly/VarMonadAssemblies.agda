{-# OPTIONS --type-in-type #-}
module Assembly.VarMonadAssemblies where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Assembly.StdVarMonad
open import BasicVarMonads.Constructions
open import BasicVarMonads.ThresholdVarMonad
open import BasicVarMonads.ConstrainedVarMonad
open import Util.Lattice
open import Util.Derivation
open import SpecialVarMonads.BranchingVarMonad
open ConnectionOperations
open import MiscMonads.ConcurrentMonad

private
  variable
    A S : Set
    K M V : Set -> Set

stdK = \A -> Eq A -x- BoundedMeetSemilattice A

instance
  stdKEq : stdK derives Eq
  stdKEq {{k}} = fst k

  stdKBoundedMeetSemilattice : stdK derives BoundedMeetSemilattice
  stdKBoundedMeetSemilattice {{k}} = snd k

stdLatMon = BaseVarMonad=>ConstrVarMonad {K = stdK} {{defaultVarMonad}}

record UniversalVarMonad (K M V : Set -> Set) : Set where
  field
    bvm : BranchingVarMonad K M V
    mf : MonadFork M
  open BranchingVarMonad bvm public
  open MonadFork mf public

instance
  istoNP = ISTONatPtr
  _ = MonadStateT
  _ = MonadReaderStateT
  _ = MonadFNCDVarMon
  _ = PlainMonadSTM

  ThresholdVarMonad=>ConstrDefVarMonad : {{tvm : ThresholdVarMonad K M V}} -> ConstrDefVarMonad K M V
  ThresholdVarMonad=>ConstrDefVarMonad {{tvm}} = record {
      new = new ;
      read = read ;
      write = write }
    where open ThresholdVarMonad tvm

readerTVM : {{mon : Monad M}} -> ThresholdVarMonad K M V -> ThresholdVarMonad K (StateT (List (V S)) M) V
readerTVM = liftThresholdVarMonad \m s -> (_, s) <$> m

stdUniversalVarMonad : UniversalVarMonad stdK _ _
stdUniversalVarMonad = record {
  bvm = {! ThresholdVarMonad=>BranchingVarMonad {{tvm = readerTVM FreeThresholdVarMonad}}  !} ;
  mf = {!   !} }
