{-# OPTIONS --type-in-type #-}
module Assembly.VarMonadAssemblies where

open import AgdaAsciiPrelude.AsciiPrelude
open import Assembly.StdVarMonad
open import BasicVarMonads.Constructions
open import BasicVarMonads.ThresholdVarMonad
open import Util.Lattice
open import SpecialVarMonads.BranchingVarMonad
open ConnectionOperations
open import MiscMonads.ConcurrentMonad

private
  variable
    A : Set

stdK = \A -> Eq A -x- BoundedMeetSemilattice A

stdLatMon = BaseVarMonad=>ConstrVarMonad {K = stdK} {{defaultVarMonad}}

record UniversalVarMonad (K M V : Set -> Set) : Set where
  field
    bvm : BranchingVarMonad K M V
    mf : MonadFork M
  open BranchingVarMonad bvm public
  open MonadFork mf public

instance
  istoNP = ISTONatPtr

stdUniversalVarMonad : UniversalVarMonad stdK _ _
stdUniversalVarMonad = record {
  bvm = {! ThresholdVarMonad=>BranchingVarMonad {{tvm = FreeThresholdVarMonad}}  !} ;
  mf = {!   !} }
