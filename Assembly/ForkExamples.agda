{-# OPTIONS --type-in-type #-}
module Assembly.ForkExamples where

open import AgdaAsciiPrelude.AsciiPrelude --hiding (return; _>>_; _>>=_)
open import AgdaAsciiPrelude.Instances
open import Assembly.VarMonadAssemblies
open import SpecialVarMonads.BranchingVarMonad
open import Util.Lattice
open import MiscMonads.ConcurrentMonad
open import BasicVarMonads.ThresholdVarMonad
open import Debug.Trace

private
  variable
    A B : Set
    K K' : Set -> Set

open ThresholdVarMonad stdForkThresholdVarMonad
open MonadFork (FMFTMonadFork {M = stdForkThresholdSub}) hiding (mon)

open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators {{tvm = BranchingVarMonad.tvm stdBranchingVarMonad}}

instance
  _ = mon

  stdKNat : stdK Nat
  stdKNat = eqNat , record { bsl = record {
    sl = record { _<>_ = max } ;
    neut = 0 } }

testFork : Maybe Nat
testFork = flip runStdForkingVarMonad (trace "final read" read) do
  v <- new {A = Nat}
  fork $ do
  -- write v (trace "writing default 10" 10)
  -- fork $ do
    write v (trace "writing 10" 10)
  -- fork $ do
    --write v 5 --this is written, which means that the continuation mechanic on the FMFT side technically works
  -- x20 <- trace "evaluating read1" $ read (trace "evaluating variable of read1" $ ((\x -> whenMaybe (x == 10) 20) <,> const 10) <bt$> v) --TODO : trace the read to check where the other read comes from
    read v
    write v (trace "writing1 20" 20)
  -- fork $ do
  --   --write v 5 --this is written, which means that the continuation mechanic on the FMFT side technically works
  --   x20 <- trace "evaluating read2" $ read (trace "evaluating variable of read2" $ ((\x -> whenMaybe (x == 10) 20) <,> const 10) <bt$> v) --TODO : trace the read to check where the other read comes from
  --   write v (trace "writing2 20" x20)
  return v


-- testForkResult : testFork === just 20
-- testForkResult = refl
