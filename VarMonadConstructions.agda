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

RecVarFuncCont : (K : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> Set
RecVarFuncCont K V F = KFix K (\ R -> F (\ B -> V (B -x- R) ) )

RecTupPtr : (K : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> (A : Set) -> Set
RecTupPtr K V F A = V (A -x- RecVarFuncCont K V F )

ConstrProdConstr :
  {F : (Set -> Set) -> Set} ->
  {{kp : ConservesProd K}} ->
  {{kf : K (KFix K (\ R -> F (\ B -> V (B -x- R) ) ))}} ->
  (femp : forall {V} -> F V) ->
  ConstrBaseVarMonad K M V ->
    ConstrBaseVarMonad K M (RecTupPtr K V F) -x-
    ConstrSpecVarMonad K M (RecTupPtr K V F) (RecVarFuncCont K V F)
ConstrProdConstr femp cbvm =
  (record {
    new = \ v -> new (v , KIn femp) ;
    read = \ p -> fst <$> read p ;
    write = \ p v -> read p >>= \ (_ , y) -> write p (v , y) }) ,
  (record {
    read = \ p -> snd <$> read p ;
    write = \ p x -> read p >>= \ (v , _) -> write p (v , x ) })
  where open ConstrBaseVarMonad cbvm
