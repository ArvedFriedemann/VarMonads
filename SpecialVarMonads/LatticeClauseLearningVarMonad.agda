{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.LatticeClauseLearningVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ThresholdVarMonad
open import Util.Derivation

private
  variable
    A B : Set
    M F K : Set -> Set

LatAssignment : (Set -> Set) -> Set
LatAssignment V = Sigma Set \A -> A -x- V A

LatClause : (Set -> Set) -> Set
LatClause V = List (LatAssignment V)

LatAsmPtrCont : (Set -> Set) -> Set -> Set
LatAsmPtrCont V A = A -x- List (A -x- LatClause V)

LatAsmPtr : (Set -> Set) -> Set -> Set
LatAsmPtr V = V o LatAsmPtrCont V

{-# NO_POSITIVITY_CHECK #-}
record SpecKLPC (K : Set -> Set) (V : Set -> Set) (A : Set) : Set where
  constructor skC
  inductive
  field
    oT : Set
    eq : A === LatAsmPtrCont (TVar (SpecKLPC K V) (TVar K V)) oT
    overlap {{kb}} : K oT

module _ {V : Set -> Set} where
  --This assumes lattice property!
  liftBijTFunc : BijTFunc A B -> BijTFunc (LatAsmPtrCont V A) B
  liftBijTFunc (to <,> from) = (to o fst) <,> ((_, []) o from)

module _ {K : Set -> Set} {V' : Set -> Set} where
  K' = SpecKLPC K V'
  V = TVar K' (TVar K V')
  module ClauseLearningLattice
      {{tvm : ThresholdVarMonad K M (TVar K V')}}
      {{kas : K derives (K o LatAsmPtrCont V)}}
      {{ms : MonadState (LatClause V) M }} where

      open ThresholdVarMonad tvm
      open MonadState ms hiding (_>>=_;_>>_;return;_<$>_) renaming (modify to modifyS)

      ptrTrans : {{k : K A}} -> TVar K V' (LatAsmPtrCont V A) -> V A
      ptrTrans {A = A} (TVarC OrigT {{k}} f OVar) = TVarC
        (LatAsmPtrCont V A)
        {{ skC _ refl {{ it }} }}
        ((just o fst) <,> (_, [])) --assumes lattice property
        (f <bt$> (TVarC _ (just <,> id) OVar)) --has to be this way, because variable needs to be transformed

      CLTVM : ThresholdVarMonad K M V
      CLTVM = record {
        cvm = record {
          new = ptrTrans <$> new ;
          read = \{(TVarC OrigT f v) -> do
            x <- read (f <bt$> v)
            modifyS ((_ , x , (TVarC OrigT f v)) ::_)
            return x } ;
          write = \{(TVarC OrigT {{skC _ refl}} (_ <,> from) v) x -> do
            asm <- get
            write v (fst (from x) , [ (fst (from x)) , asm ]) } } ;
        tvbf = TVarBijTFunctor }

      open import Util.PointerEquality
      open import Util.Lists
      open import Util.Monad
      open PEq {{...}}

      module _ {{eq : PEq V}} where

        eqSig : {V : Set -> Set} -> {{PEq V}} -> Eq (Sigma Set V)
        eqSig = record { _==_ = \{(_ , v1) (_ , v2) -> v1 =p= v2 } }

        -- {-# TERMINATING #-}
        -- dfsFoldM :
        --   (forall {A} -> A -> AsmPtr K V C -> List B -> B) ->
        --   B ->
        --   AsmPtr K V A ->
        --   M B
        -- dfsFoldM f def (AsmPtrC v) = {!!}
