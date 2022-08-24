module SpecialVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A : Set
    B : Set -> Set
    M F V K C : Set -> Set


DepPtr : (Set -> Set) -> (Set -> Set) -> Set -> Set
DepPtr V B A = V (A -x- B A)

module DependentProductConstruction where
  open import BasicVarMonads.ConstrainedVarMonad
  open import BasicVarMonads.ModifyVarMonad
  open import SpecialVarMonads.FixedValueVarMonad renaming (ConstrDefDepModFixedValVarMonad to FixedVarMonad)
  open import Util.Derivation

  open ConstrDefModifyVarMonad {{...}}

  ConstrDefModifyVarMonad=>FixedVarMonad :
    {{vcm : ConstrDefModifyVarMonad K M V}} ->
    {{K derives (\A -> K (A -x- B A))}} ->
    ConstrDefVarMonad K M (DepPtr V B)
    -x- FixedVarMonad K M (DepPtr V B) B
  ConstrDefModifyVarMonad=>FixedVarMonad =
    record {
      new = new ;
      read = \v -> fst <$> read v ;
      write = \v x -> write' v \{ (a , b) -> x , b } } ,
    record {
      new = new ;
      read = \v -> snd <$> read v ;
      write = \v x -> write' v \{ (a , b) -> a , x } }

module DependentLatticeProductConstruction where
  open import BasicVarMonads.LatticeVarMonad
  open import SpecialVarMonads.FixedValueVarMonad renaming (ConstrDefDepModFixedValVarMonad to FixedVarMonad)
  open import Util.Derivation

  open ConstrLatVarMonad {{...}}

  ConstrDefModifyVarMonad=>FixedVarMonad :
    {{vcm : ConstrLatVarMonad K M V}} ->
    {{K derives (K o B)}} ->
    {{K derives (\A -> K (A -x- B A))}} ->
    ConstrLatVarMonad K M (DepPtr V B)
    -x- FixedVarMonad K M (DepPtr V B) B
  ConstrDefModifyVarMonad=>FixedVarMonad =
    record { cvm = record {
      new = \x -> new (x , top) ;
      read = \v -> fst <$> read v ;
      write = \v x -> write v (x , top) } } ,
    record {
      new = new' ;
      read = \v -> snd <$> read v ;
      write = \v x -> write v (top , x) }
