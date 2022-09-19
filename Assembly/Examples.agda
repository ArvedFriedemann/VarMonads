{-# OPTIONS --type-in-type #-}
module Assembly.Examples where

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

open BranchingVarMonad stdBranchingVarMonad
open MonadReader _ (BranchingVarMonad.mr stdBranchingVarMonad) using (reader; local)
open MonadFork stdMonadFork hiding (mon)

instance
  _ = FMFTMonadFork

open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators {{tvm = BranchingVarMonad.tvm stdBranchingVarMonad}}

instance
  _ = mon


testWrite : Maybe Nat
testWrite = flip runStdBranchingVarMonad read do
  v <- new
  write v 10
  return v

testWriteResult : testWrite === just 10
testWriteResult = refl

testRead : Maybe Nat
testRead = flip runStdBranchingVarMonad read do
  v <- new
  write v 10
  read (eqThreshold 0 <bt$> v)
  write v 20
  return v

testReadResult : testRead === just 20
testReadResult = refl



testFork : Maybe Nat
testFork = flip runStdBranchingVarMonad read do
  v <- new {A = Nat}
  fork $ write v 10
  fork $ do
    read (eqThreshold 0 <bt$> v)
    write v 20
  return v

testForkResult : testFork === just 20
testForkResult = refl



testEqProp : Maybe Nat
testEqProp = flip runStdBranchingVarMonad read do
  v <- new
  v' <- new
  v'' <- new
  v' =p> v      --directional propagators are automatically forked
  v'' =p> v'    --directional propagators are automatically forked
  fork $ write v'' 10
  return v

testEqPropResult : testEqProp === just 10
testEqPropResult = refl



testBranch : Maybe Nat
testBranch = flip runStdBranchingVarMonad read do
  v <- new
  write v 10
  branched \push -> fork $ do
    write v 20
    read (eqThreshold 0 <bt$> v)
    push (write v 15)
  return v

testBranchResult : testBranch === just 15
testBranchResult = refl
