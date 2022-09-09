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

test : Maybe Nat
test = flip runStdForkingVarMonad read do
  v <- new
  fork $ do
    read (((\x -> whenMaybe (x == 10) tt) <,> const 10) <bt$> v)
    write v 20
  write v 10
  return v
