{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.Propagators.Unification where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ThresholdVarMonad
open import MTC.MTCMendler
open import Util.Monad
open import MiscMonads.ConcurrentMonad
open import SpecialVarMonads.Propagators.BasicPropagators
open EqTPropagators

open Functor {{...}} renaming (_<$>_ to _<$>f_)

private
  variable
    A : Set
    K M V F : Set -> Set

record UFunctor (F : Set -> Set) : Set where
  field
    getMatching : F A -> F A -> Maybe (List (A -x- A))

module _
  {{tvm : ThresholdVarMonad K M V}}
  {{mf : MonadFork M}}
  {{func : Functor F}}
  {{uf : UFunctor F}}
  {{kf : K (Fix (F o V))}}
  {{veq : Eq (Sigma Set V)}} where
  open ThresholdVarMonad tvm
  open MonadFork mf
  open UFunctor uf

  {-# TERMINATING #-}
  unifyNaive : Fix (F o V) -> Fix (F o V) -> M T
  unifyNaive f1 f2 = maybe'
      (void o sequenceM o map (\{(x , y) -> do
        x =p= y
        fork (| unifyNaive (read x) (read y) |)}))
      (return tt)
      mergeList
    where
      mergeList = getMatching (OutF f1) (OutF f2)

  {-# TERMINATING #-}
  unify' : List (Sigma Set V) -> Fix (F o V) -> Fix (F o V) -> M T
  unify' visited f1 f2 = maybe'
      (void o sequenceM o map (\{(x , y) ->
        if ((_ , x) elem visited withEq veq && (_ , y) elem visited withEq veq)
        then (return tt)
        else do
            x =p= y
            fork (| (unify' $ (_ , x) :: (_ , y) :: visited) (read x) (read y) |)
          }))
      (return tt)
      mergeList
    where
      mergeList = getMatching (OutF f1) (OutF f2)
