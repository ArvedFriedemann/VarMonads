{-# OPTIONS --type-in-type #-}
module VarMonadMTC where

open import AgdaAsciiPrelude.AsciiPrelude
open import FixpointsVarMonads
open import MTCDatatypes

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

anyKBVM : {{cbvm : ConstrBaseVarMonad K M V}} ->
  {{kv : forall {R} -> {{kr : K R}} -> K (V R)}} ->
  KFix K (ListF Bool o V) -> M Bool
anyKBVM = foldKBVM \ {
  _ nil _ -> return false;
  _ (lcons true xs) _ -> return true;
  _ (lcons false xs) [[_]] -> [[ xs ]] }
