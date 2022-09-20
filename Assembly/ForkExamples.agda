{-# OPTIONS --type-in-type #-}
module Assembly.ForkExamples where

open import AgdaAsciiPrelude.AsciiPrelude --hiding (return; _>>_; _>>=_)
open import AgdaAsciiPrelude.Instances
open import Assembly.VarMonadAssemblies
open import SpecialVarMonads.BranchingVarMonad
open import Util.Lattice
open import MiscMonads.ConcurrentMonad
open import BasicVarMonads.ThresholdVarMonad
--open import Debug.Trace

private
  variable
    A B : Set
    K K' : Set -> Set

open ThresholdVarMonad stdForkThresholdVarMonad
open MonadFork (FMFTMonadFork {M = stdForkThresholdSub}) hiding (mon)

open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators {{tvm = stdForkThresholdVarMonad}}

instance
  _ = mon
  _ = FMFTMonadFork

testFork : Maybe Nat
testFork = flip runStdForkingVarMonad read do
  v <- new {A = Nat}
  fork $ do
    read (eqThreshold 0 <bt$> v)
    write v 20
  fork $ do
    write v 10
  return v


testForkResult : testFork === just 20
testForkResult = refl
