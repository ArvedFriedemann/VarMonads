{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.PropagatorConstruction where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ModifyVarMonad
open import BasicVarMonads.ConstrainedVarMonad
open import BasicVarMonads.LatticeVarMonad
open import MiscMonads.ConcurrentMonad
open MonadFork {{...}}
open ConstrDefModifyVarMonad {{...}}

open RunTrivLat

open import Util.Derivation
open import Util.Lattice
open import Util.Monad
open BoundedMeetSemilattice {{...}}

private
  variable
    A : Set
    K M V C : Set -> Set

instance
  bm : {{Eq A}} -> BoundedMeetSemilattice (TrivLat A)
  bm = BoundedLattice.meet-bsl trivialBoundedLattice

DepTrivPtrCont : (Set -> Set) -> (Set -> Set) -> Set -> Set
DepTrivPtrCont V B A = TrivLat A -x- B A

DepTrivPtr : (Set -> Set) -> (Set -> Set) -> Set -> Set
DepTrivPtr V B A = V (DepTrivPtrCont V B A)

MCont : (Set -> Set) -> Set -> Set
MCont M A = A -> M T

DepTrivContPtrCont : (Set -> Set) -> (Set -> Set) -> (Set -> Set) -> Set -> Set
DepTrivContPtrCont M V C A = DepTrivPtrCont V (C o MCont M) A

ContTupPtr : (Set -> Set) -> (Set -> Set) -> (Set -> Set) -> Set -> Set
ContTupPtr M V C A = V (DepTrivContPtrCont M V C A)

FCDCont : (Set -> Set) -> (Set -> Set) -> Set -> Set
FCDCont K V A = Sigma Set \B -> V B -x- (B -> FCDVarMon K V A)

module runFDCVarMonProp
    {{lvm : ConstrDefModifyVarMonad K M V}}
    {{mfork : MonadFork M}}
    {{kinst : forall {A} -> K (DepTrivContPtrCont M V List A)}}
    {{keq : (K o DepTrivContPtrCont M V List) derives Eq}} where

  private
    propagatorModify : A -> DepTrivContPtrCont M V List A ->
      DepTrivContPtrCont M V List A -x- List (M T)
    propagatorModify x (x' , props) with (trivcont x) /\ x'
    ... | trivcont a = ((trivcont a) , []) , map (_$ x) props
    ... | r          = (r , props) , []

    runPropagators : List (M T) -> M T
    runPropagators props = void (sequenceM (map fork props))

    propagatorWrite : ContTupPtr M V List A -> A -> M T
    propagatorWrite v x =  modify v (propagatorModify x) >>= runPropagators


  --Agda here does not know that this always produces a smaller continuation
  --(or rather that if the continuation stays the same size, it is only ever operated when
  --its value actually changed)
  runFDCVarMonProp : FCDVarMon K (ContTupPtr M V List) A ->
                      M (A or (FCDCont K (ContTupPtr M V List) A))
  runFDCVarMonProp newF = left <$> new
  runFDCVarMonProp (readF v) = modify v \{
    (trivcont x , props) -> (trivcont x , props), (left x) ;
    (x , props) -> (x , props) , (right (_ , v , returnF)) }
  runFDCVarMonProp (writeF v x) = left <$> propagatorWrite v x
  runFDCVarMonProp (returnF x) = left <$> return x
  runFDCVarMonProp (bindF m f) = runFDCVarMonProp m >>= \{
    (left res) -> runFDCVarMonProp (f res) ;
    (right (_ , v , cont)) -> right <$> return (_ , v , \b -> bindF (cont b) f) }

  {-# TERMINATING #-}
  toVarProp : A or (FCDCont K (ContTupPtr M V List) A) -> M T
  toVarProp (left res) = return tt
  toVarProp (right (_ , v , cont)) = modify v (\{
        (trivcont x , props) -> propagatorModify x (trivcont x , newprop :: props) ;
        (r , props) -> (r , newprop ::  props) , [] }) >>= runPropagators
      where
        newprop = runFDCVarMonProp o cont >=> toVarProp


  {-
  open import AgdaAsciiPrelude.TrustMe

  runAll : FCDVarMon K (ContTupPtr M V List) A -> M A
  runAll m = runFDCVarMonProp m >>= \{
    (left x) -> return x ;
    (right (_ , _ , cont)) -> runAll (cont (trustVal tt)) }
  -}
