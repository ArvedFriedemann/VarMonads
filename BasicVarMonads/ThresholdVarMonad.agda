{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ThresholdVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances

open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation
open import Util.Lattice

private
  variable
    A B C : Set
    M M' V V' K : Set -> Set

record BijTFunc (A : Set) (B : Set) : Set where
  constructor _<,>_
  field
    Tfunc : A -> Maybe B
    Tfunc-1 : B -> A

record BijTFunctor (F : Set -> Set) : Set where
  field
    _<bt$>_ : BijTFunc A B -> F A -> F B

--ThresholdVar
record TVar (K : Set -> Set) (V : Set -> Set) (A : Set) : Set where
  constructor TVarC
  field
    OrigT : Set
    {{origK}} : K OrigT
    f : BijTFunc OrigT A
    OVar : V OrigT

instance
  monadMaybe = MonadMaybe

_<o>_ : BijTFunc B C -> BijTFunc A B -> BijTFunc A C
_<o>_ (BtoC <,> CtoB) (AtoB <,> BtoA) = (BtoC <=< AtoB) <,> (BtoA o CtoB)

_<$o$>_ : BijTFunc A B -> TVar K V A -> TVar K V B
_<$o$>_ t (TVarC T f v) = TVarC T (t <o> f) v


TVarBijTFunctor : BijTFunctor (TVar K V)
TVarBijTFunctor = record { _<bt$>_ = _<$o$>_ }

stdTransOf : TVar K V A -> TVar K (TVar K V) A
stdTransOf (TVarC T f v) = TVarC T f (TVarC T (just <,> id) v)

open import Util.PointerEquality

ISTOTVar :
  {{isto : ISTO (Sigma Set V)}} ->
  ISTO (Sigma Set (TVar K V))
ISTOTVar = ExtractISTOFrom \{(TVarC _ _ v) -> _ , v}

PEqTVar : {{peq : PEq V}} -> PEq (TVar K V)
PEqTVar {{peq}} = record { _=p=_ = \{(TVarC _ _ v1) (TVarC _ _ v2) -> v1 =p= v2 } }
  where open PEq peq

record ThresholdVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    cvm : NewConstrDefVarMonad K M V
    tvbf : BijTFunctor V
    transOf : V A -> TVar K V A
    overlap {{KEq}} : K derives Eq
    overlap {{KBMSL}} : K derives BoundedMeetSemilattice
  open NewConstrDefVarMonad cvm public
  open BijTFunctor tvbf public

  newLike : V A -> M (V A)
  newLike v = (f <bt$>_) <$> new {A = OrigT} {{k = origK}}
    where open TVar (transOf v)

  sameOrigT : V A -> V B -> Set
  sameOrigT v1 v2 = TVar.OrigT (transOf v1) === TVar.OrigT (transOf v2)

liftThresholdVarMonad : {{mon : Monad M'}} ->
  (forall {A} -> M A -> M' A) ->
  ThresholdVarMonad K M V ->
  ThresholdVarMonad K M' V
liftThresholdVarMonad liftT tvm = record {
    cvm = liftNewConstrDefVarMonad liftT cvm ;
    tvbf = tvbf ;
    transOf = transOf }
  where open ThresholdVarMonad tvm

FreeThresholdVarMonad : {{K derives Eq}} -> {{K derives BoundedMeetSemilattice}} ->
  ThresholdVarMonad K (FNCDVarMon K (TVar K V)) (TVar K V)
FreeThresholdVarMonad = record {
  cvm = FNCDVarMonNewConstrDefVarMonad ;
  tvbf = TVarBijTFunctor ;
  transOf = stdTransOf }

module _ {{tvm : ThresholdVarMonad K M V}}
          {{cvm : ConstrDefVarMonad K M V'}} where

  open ThresholdVarMonad tvm renaming (new to newT; read to readT; write to writeT; cvm to cvmT)
  open ConstrDefVarMonad cvm renaming (new to newC; read to readC; write to writeC)

  private
    variable
      PContT : Set -> Set

  ThresholdVarMonad=>ConstrDefVarMonad=>ThresholdVarMonad :
    (forall {A} -> (V' A) -> V (PContT A)) ->
    (forall {A B} -> BijTFunc A B -> BijTFunc (PContT A) B) ->
    ThresholdVarMonad K M (TVar K V')
  ThresholdVarMonad=>ConstrDefVarMonad=>ThresholdVarMonad
    retrieve bijTtrans = record {
      cvm = record {
        new = TVarC _ (just <,> id) <$> newC ;
        read = \{(TVarC _ f v) -> readT (bijTtrans f <bt$> retrieve v)} ;
        write = \{(TVarC _ f v) -> writeT (bijTtrans f <bt$> retrieve v)} } ;
      tvbf = TVarBijTFunctor ;
      transOf = stdTransOf }
