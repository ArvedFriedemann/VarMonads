{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ThresholdVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances

open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation
open import Util.Lattice
--open import Debug.Trace

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
    overlap {{KEq}} : K derives Eq
    overlap {{KBMSL}} : K derives BoundedMeetSemilattice
  open NewConstrDefVarMonad cvm public
  open BijTFunctor tvbf public

  -- newLike : V A -> M (V A)
  -- newLike v = (f <bt$>_) <$> new {A = OrigT} {{k = origK}}
  --   where open TVar (transOf v)
  --
  -- sameOrigT : V A -> V B -> Set
  -- sameOrigT v1 v2 = TVar.OrigT (transOf v1) === TVar.OrigT (transOf v2)

liftThresholdVarMonad : {{mon : Monad M'}} ->
  (forall {A} -> M A -> M' A) ->
  ThresholdVarMonad K M V ->
  ThresholdVarMonad K M' V
liftThresholdVarMonad liftT tvm = record {
    cvm = liftNewConstrDefVarMonad liftT cvm ;
    tvbf = tvbf }
  where open ThresholdVarMonad tvm

FreeThresholdVarMonad : {{K derives Eq}} -> {{K derives BoundedMeetSemilattice}} ->
  ThresholdVarMonad K (FNCDVarMon K (TVar K V)) (TVar K V)
FreeThresholdVarMonad = record {
  cvm = FNCDVarMonNewConstrDefVarMonad ;
  tvbf = TVarBijTFunctor }

open import Debug.Trace

ThresholdVarMonad=>ConstrDefVarMonad : {{tvm : ThresholdVarMonad K M V}} -> ConstrDefVarMonad K M V
ThresholdVarMonad=>ConstrDefVarMonad {{tvm}} = record {
    new = new ;
    read = read ;
    write = write }
  where open ThresholdVarMonad tvm

FNCDCont : (Set -> Set) -> (Set -> Set) -> Set -> Set
FNCDCont K V A = Sigma Set \B -> V B -x- (B -> FNCDVarMon K V A)

module _ where
  open ConstrDefVarMonad {{...}}

  runFreeThresholdVarMonad :
    {{cvm : ConstrDefVarMonad K M V}} ->
    FNCDVarMon K (TVar K V) A -> M (A or (FNCDCont K (TVar K V) A))
  runFreeThresholdVarMonad newF = (left o (TVarC _ (just <,> id))) <$> new
  runFreeThresholdVarMonad (readF (TVarC OrigT (to <,> from) OVar)) =
    (maybe' left (right (_ , (TVarC OrigT (to <,> from) OVar) , returnF))) o to
    <$> read OVar
  runFreeThresholdVarMonad (writeF (TVarC OrigT (to <,> from) OVar) x) =
    left <$> write OVar (from x)
  runFreeThresholdVarMonad (returnF x) = left <$> return x
  runFreeThresholdVarMonad (bindF m f) = runFreeThresholdVarMonad m >>= \{
      (left x) -> runFreeThresholdVarMonad (f x) ;
      (right (B , v , cont)) -> right <$> return (B , v , \b -> bindF (cont b) f)
    }

PropPtrCont : (Set -> Set) -> Set -> Set
PropPtrCont M A =  A -x- List (Sigma Set \B -> (A -> Maybe B) -x- (B -> M T))

SpecK : (Set -> Set) -> (Set -> Set) -> Set -> Set
SpecK K M B = Sigma Set \A -> (B === PropPtrCont M A) -x- K A

SpecialFreeThresholdVarMonad : {{K derives Eq}} -> {{K derives BoundedMeetSemilattice}} ->
  ThresholdVarMonad K (FNCDVarMon K (TVar (SpecK K M) V)) (TVar (SpecK K M) V)
SpecialFreeThresholdVarMonad = record {
  cvm = FNCDVarMonNewConstrDefVarMonad ;
  tvbf = TVarBijTFunctor}

open import BasicVarMonads.ModifyVarMonad
open import MiscMonads.ConcurrentMonad
open import Util.Monad

module runFreeThresholdVarMonadPropagation
  {{mvm : ModifyVarMonad M V}}
  {{mf : MonadFork M}}
  {{keq : K derives Eq}}
  {{kbmsl : K derives BoundedMeetSemilattice}}
  {{showv : forall {A} -> Show (V A)}}
  {{nk : K Nat}} where
  open BoundedMeetSemilattice {{...}}
  open MonadFork mf hiding (mon)
  open ModifyVarMonad mvm

  instance
    _ : forall {A V K} -> {{forall {B} -> Show (V B)}} -> Show (TVar K V A)
    _ = record { show = \{ (TVarC OrigT f OVar) -> "TVar#" ++s show OVar} }

  K' : Set -> Set
  K' = SpecK K M

  open import AgdaAsciiPrelude.TrustMe

  private

    propagatorModify : {{k : K A}} -> A -> PropPtrCont M A ->
      PropPtrCont M A -x- List (M T)
    propagatorModify x (x' , props) with
      xm <- x /\ x' | partitionSumsWith (\{(B , to , cont) ->
                        maybe' (left o cont)
                               (right (B , to , cont))
                               (to xm)}) props
    ... | (succd , failed) = (xm , failed) , succd

    runPropagators : List (M T) -> M T
    runPropagators = void o sequenceM o map fork

    propagatorWrite : TVar K' V A -> A -> M T
    propagatorWrite (TVarC _ {{(OrigT , refl , k)}} (to <,> from) v) x =
      modify v (propagatorModify {{k = k}} (fst $ from x)) >>= runPropagators

  runFNCDCont : FNCDVarMon K (TVar K' V) A -> M (A or (FNCDCont K (TVar K' V) A))
  --notice how we write an empty propagator list back. This is not a problem because we ignore that during the write!
  runFNCDCont newF = (left o (TVarC _ {{(_ , refl , it)}} ((just o fst) <,> (_, [])) )) <$> new (top , [])
  runFNCDCont (readF (TVarC OrigT (to <,> from) OVar)) =
    (maybe' left (right (_ , (TVarC OrigT (to <,> from) OVar) , returnF))) o to
    <$> read OVar
  runFNCDCont (writeF v x) = left <$> propagatorWrite v x
  runFNCDCont (returnF x) = left <$> return x
  runFNCDCont (bindF m f) = runFNCDCont m >>= \{
      (left x) -> runFNCDCont (f x) ;
      (right (B , v , cont)) -> right <$> return (B , v , \b -> bindF (cont b) f)
    }

  -- shallowInspectFNCD : FNCDVarMon K (TVar K' V) A -> (Maybe A -x- String)
  -- shallowInspectFNCD newF = nothing , "newF"
  -- shallowInspectFNCD (readF v) = nothing , "readF " ++s show v
  -- shallowInspectFNCD (writeF v x) = just tt , "writeF " ++s show v ++s " " ++s (showN $ trustVal x)
  -- shallowInspectFNCD (returnF x) = just x , "ret"
  -- shallowInspectFNCD (bindF m f) = let
  --     (rm , sm) = shallowInspectFNCD m
  --     (rm' , sm') = maybe' (shallowInspectFNCD o f) (nothing , " f") rm
  --   in rm' , (if (_==_ {{r = eqNat}} (lengthString sm) 3)
  --             then sm'
  --             else ("bindF (" ++s sm ++s ") (" ++s sm' ++s ")"))
  --
  -- inspectFNCD : FNCDVarMon K (TVar K' V) A -> String
  -- inspectFNCD = snd o shallowInspectFNCD

  {-# TERMINATING #-}
  runFNCDtoVarProp : (A -> MaybeT M B) -> A or (FNCDCont K (TVar K' V) A) -> MaybeT M B
  runFNCDtoVarProp cont' (left x) = cont' x
  runFNCDtoVarProp cont' (right (D , (TVarC _ {{(OrigT , refl , k)}} (to <,> from) v) , cont)) =
      modify v (\{(x , props) ->
        propagatorModify {{k = k}} x (x , (_ , to o (_, []) , newprop ) :: props) })
        >>= runPropagators >> return nothing
    where
      newprop : D -> M T
      newprop = runFNCDCont o cont >=> runFNCDtoVarProp cont' >=> const (return tt)

  runFNCD : FNCDVarMon K (TVar K' V) A -> (A -> MaybeT M B) -> MaybeT M B
  runFNCD m cont = runFNCDCont m) >>= runFNCDtoVarProp cont
