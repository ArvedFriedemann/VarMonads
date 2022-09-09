{-# OPTIONS --type-in-type #-}
module Assembly.Examples where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Assembly.VarMonadAssemblies
open import SpecialVarMonads.BranchingVarMonad
open import Util.Lattice
open import MiscMonads.ConcurrentMonad
open import BasicVarMonads.ThresholdVarMonad

private
  variable
    A B : Set
    K K' : Set -> Set

open BranchingVarMonad stdForkingVarMonad
open MonadFork (FMFTMonadFork {{BranchingVarMonad.mon stdBranchingVarMonad}}) hiding (mon)

instance
  _ = mon
  _ = FMFTMonadFork

  stdKNat : stdK Nat
  stdKNat = eqNat , record { bsl = record {
    sl = record { _<>_ = max } ;
    neut = 0 } }

testWrite : Maybe Nat
testWrite = flip runStdForkingVarMonad read do
  v <- new
  write v 10
  return v

testWriteResult : testWrite === just 10
testWriteResult = refl

testFork : Maybe Nat
testFork = flip runStdForkingVarMonad read do
  v <- new
  fork $ do
    read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
    write v 20
  write v 10
  return v

testForkResult : testFork === just 20
testForkResult = refl

testBranch : Maybe Nat
testBranch = flip runStdForkingVarMonad read do
  v <- new
  branched \push -> fork $ do
    read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
    write v 20
    push (write v 15)
  write v 10
  return v

testBranchResult : testBranch === just 15
testBranchResult = refl