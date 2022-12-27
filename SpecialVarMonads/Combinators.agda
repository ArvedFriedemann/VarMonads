{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.Combinators where
open import AgdaAsciiPrelude.AsciiPrelude
open import SpecialVarMonads.BranchingVarMonad
open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators
open import MiscMonads.ConcurrentMonad
open import Util.Monad
open import Util.Lattice

private
  variable
    A B C VS : Set
    M M' V V' K : Set -> Set

module _ {{bvm : BranchingVarMonad K M V VS}} {{mf : MonadFork M}} {{kt : K (TrivLat T)}} where
  open BranchingVarMonad bvm
  open MonadFork mf
  instance _ = BranchingVarMonad.tvm bvm

  disjunctSuccFail : List (M T -x- M T -x- Sigma Set (\A -> M A -x- (A -> M T))) -> M T -> M T
  disjunctSuccFail psbs fail = do
    withFailVars <- forM psbs (\x -> (| (_, x) new |) )
    forMExcludeSelf withFailVars \{others (vf , m , mfail , _ , mresprep , mres) -> do
      branched $ \push -> do
        fork $ m
        fork $ mfail >> push (write vf trivbot)
        fork $ do
          forM (map fst others) (read o (eqThreshold trivbot <bt$>_))
          mresprep >>= push o mres
      }
    fork $ forM (map fst withFailVars) (read o (eqThreshold trivbot <bt$>_)) >> fail
