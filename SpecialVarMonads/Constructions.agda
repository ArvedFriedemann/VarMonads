module SpecialVarMonads.Constructions where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    M F V K C : Set -> Set

module ProductConstruction where
  open import BasicVarMonads.ConstrainedVarMonad
  open import SpecialVarMonads.FixedValueVarMonad

  open import MTC.MTCMendler

  TupPtr : (Set -> Set) -> Set -> Set -> Set
  TupPtr V B A = V (A -x- B)

  RecTupPtr : (Set -> Set) -> ((Set -> Set) -> Set) -> Set -> Set
  RecTupPtr V F A = V (A -x- Fix (F o TupPtr) )

  ConstrDefVarMonad=>FixedDefValVarMonad :
    {{vcm : ConstrDefVarMonad M V}} ->
    ConstrDefVarMonad M
open ProductConstruction public
