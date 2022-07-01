{-# OPTIONS --type-in-type #-}
module VarMonadConstructions where

open import AgdaAsciiPrelude.AsciiPrelude
open import SpecialVarMonads
open import Fixpoints
open import ConstraintProperties

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

RecTupPtr : (K : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> (A : Set) -> Set
RecTupPtr K V F A = V (A -x- KFix K (\ R -> F (\ B -> V (B -x- R) ) ) )

ConstrProdConstr :
  {F : (Set -> Set) -> Set} ->
  {{kp : ConservesProd K}} ->
  {{kf : K (KFix K (\ R -> F (\ B -> V (B -x- R) ) ))}} ->
  (femp : forall {V} -> F V) ->
  ConstrBaseVarMonad K M V ->
    ConstrBaseVarMonad K M (RecTupPtr K V F) -x-
    ConstrSpecVarMonad K M (RecTupPtr K V F) (F (RecTupPtr K V F))
ConstrProdConstr femp cbvm =
  (record {
    new = \ v -> new (v , {!!}) ;
    read = {!   !} ;
    write = {!   !} }) ,
  (record {
    read = {!   !} ;
    write = {!   !} })
  where open ConstrBaseVarMonad cbvm
