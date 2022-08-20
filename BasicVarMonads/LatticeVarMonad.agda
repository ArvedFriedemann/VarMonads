{-# OPTIONS --type-in-type #-}
module BasicVarMonads.LatticeVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import Util.Lattice
open import Util.Derivation
open import BasicVarMonads.ConstrainedVarMonad

private
  variable
    A : Set
    M V : Set -> Set

record ConstrLatVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  open Eq {{...}} public
  open BoundedMeetSemilattice {{...}} public

  field
    cvm : ConstrVarMonad K M V
    overlap {{KEq}} : K derives Eq
    overlap {{KBMSL}} : K derives BoundedMeetSemilattice
    overlap {{mon}} : Monad M
  open ConstrVarMonad cvm public


  new' : {{K A}} -> M (V A)
  new' = new top

module RunTrivLat where

  private
    variable
      K K' : Set -> Set

  open import Util.Lattice
  open import Util.Derivation
  open ConstrLatVarMonad {{...}}

  open BoundedLattice {{...}}
  instance
    tbl = trivialBoundedLattice

  TLP : (Set -> Set) -> Set -> Set
  TLP V A = V (TrivLat A)

  TLPCont : (Set -> Set) -> (Set -> Set) -> Set -> Set
  TLPCont K V A = Sigma Set \B -> (TLP V) B -x- (B -> FCDVarMon K (TLP V) A)

  -- TODO: This should be done properly with a lattice monad!

  runFDCVarMon : {{cdvm : ConstrLatVarMonad K M V}} ->
    {{K' derives (K o TrivLat)}} ->
    FCDVarMon K' (TLP V) A ->
    M (A or (TLPCont K' V A))
  runFDCVarMon newF = left <$> new'
  runFDCVarMon (readF v) = read v >>= \ {
    (trivcont x) -> left <$> return x ;
    _ -> right <$> return (_ , v , returnF) }
  runFDCVarMon (writeF v x) = left <$> write v (trivcont x)
  runFDCVarMon (returnF x) = left <$> return x
  runFDCVarMon (bindF m f) = runFDCVarMon m >>= \{
    (left x) -> runFDCVarMon (f x) ;
    (right (B , v , cont)) -> right <$> return (B , v , \b -> bindF (cont b) f) }
