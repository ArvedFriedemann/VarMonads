{-# OPTIONS --type-in-type #-}
module Assembly.Examples where

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
testWrite = flip runStdBranchingVarMonad read do
  v <- new
  write v 10
  return v

-- testWriteResult : testWrite === just 10
-- testWriteResult = refl

testRead : Maybe Nat
testRead = flip runStdBranchingVarMonad read do
  v <- new
  write v 10
  read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
  write v 20
  return v

-- testReadResult : testRead === just 20
-- testReadResult = refl

open import Util.Monad
open MonadTrans {{...}}
open import BasicVarMonads.ConstrainedVarMonad
instance
  _ = MonadTransStateT
  _ = FMFTMonad
  _ = MonadFNCDVarMon

testFork : Maybe Nat
testFork = flip runStdBranchingVarMonad read do
  v <- new {A = Nat}
  fork $ write v (trace "writing 10" 10)
  fork $ do
    -- write v 15 --this is written, which means that the continuation mechanic on the FMFT side technically works
    x20 <- read (trace "evaluating variable of read" $ ((\x -> whenMaybe (x == 10) 20) <,> const 10) <bt$> v) --TODO : trace the read to check where the other read comes from
    write v (trace "writing 20" x20)
  return v


-- testForkResult : testFork === just 20
-- testForkResult = refl

testEqProp : Maybe Nat
testEqProp = flip runStdBranchingVarMonad read do
  v <- new
  v' <- new
  v'' <- new
  fork $ write v'' 10
  fork $ v' =p> v
  fork $ v'' =p> v'
  --write v'' 10
  return v''

-- testEqPropResult : testEqProp === just 20
-- testEqPropResult = refl

testBranch : Maybe Nat
testBranch = flip runStdBranchingVarMonad read do
  v <- new
  -- write v 10
  write v 10
  branched \push -> fork $ do
    -- l <- reader length
    -- write v (l + 100)
    -- fork $ write v 20 --stops working with fork!
    read (eqThreshold 0 <bt$> v)
    push (write v 15)
  --   v' <- new
  --   fork $ do
  --     read (eqThreshold 0 <bt$> v')
  --     push (write v 15)
  --   return v'
  -- write v' 10
  return v

-- testBranchResult : testBranch === just 15
-- testBranchResult = refl
