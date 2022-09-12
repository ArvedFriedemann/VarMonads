{-# OPTIONS --type-in-type #-}
module Assembly.Examples where

open import AgdaAsciiPrelude.AsciiPrelude --hiding (return; _>>_; _>>=_)
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

open BranchingVarMonad stdBranchingVarMonad
open MonadReader _ (BranchingVarMonad.mr stdBranchingVarMonad) using (reader; local)
open MonadFork stdMonadFork hiding (mon)

open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators {{tvm = BranchingVarMonad.tvm stdBranchingVarMonad}}

instance
  _ = mon

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

testRead : Maybe Nat
testRead = flip runStdForkingVarMonad read do
  v <- new
  write v 10
  read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
  write v 20
  return v

testReadResult : testRead === just 20
testReadResult = refl

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

testEqProp : Maybe Nat
testEqProp = flip runStdForkingVarMonad read do
  v <- new
  v' <- new
  fork $ read (eqThreshold 0 <bt$> v') >>= write v >> read (eqThreshold 10 <bt$> v') --v' =p> v
  write v' 10
  return v

testEqPropResult : testEqProp === just 10
testEqPropResult = refl

testBranch : Maybe Nat
testBranch = flip runStdForkingVarMonad read do
  v <- new
  write v 10
  branched \push -> fork $ do
    -- l <- reader length
    -- write v (l + 100)
    read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
    push (write v 15)
  return v

-- testBranchResult : testBranch === just 15
-- testBranchResult = refl
