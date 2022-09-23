{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.LatticeClauseLearningVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ThresholdVarMonad
open import Util.Derivation
open import Util.Lattice

private
  variable
    A B : Set
    M F K : Set -> Set

LatAssignment : (Set -> Set) -> Set
LatAssignment V = Sigma Set V

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

  retrieveMinReason :
    {{eq : Eq A}} ->
    {{lat : BoundedMeetSemilattice A}} ->
    A -> List (A -x- LatClause V) -> Maybe (List (LatClause V))
  retrieveMinReason x lst = (map snd) <$> (head $
      boolFilter (lat-leq x o (foldr _/\_ top) o map fst) (inits lst))
    where
      open BoundedMeetSemilattice {{...}}
      open import AgdaAsciiPrelude.Instances
      instance
        _ = MonadMaybe

module _ {K : Set -> Set} {V' : Set -> Set} where
  K' = SpecKLPC K V'
  V = TVar K' (TVar K V')
  module ClauseLearningLattice
      {{tvm : ThresholdVarMonad K M (TVar K V')}}
      {{kas : K derives (K o LatAsmPtrCont V)}}
      {{ms : MonadState (LatClause V) M }} where

      open ThresholdVarMonad tvm
      open MonadState ms hiding (_>>=_;_>>_;return;_<$>_; join) renaming (modify to modifyS)

      ptrTrans : {{k : K A}} -> TVar K V' (LatAsmPtrCont V A) -> V A
      ptrTrans {A = A} (TVarC OrigT {{k}} f OVar) = TVarC
        (LatAsmPtrCont V A)
        {{ skC _ refl }}
        ((just o fst) <,> (_, [])) --assumes lattice property
        (f <bt$> (TVarC _ (just <,> id) OVar)) --has to be this way, because variable needs to be transformed


      CLTVM : ThresholdVarMonad K M V
      CLTVM = record {
        cvm = record {
          new = ptrTrans <$> new ;
          read = \{(TVarC OrigT {{skC oT refl}} (to <,> from) v) -> do
            x <- read ((to <,> from) <bt$> v)
            modifyS ((_ , (TVarC OrigT {{skC oT refl}}
              ((\orig -> join $ whenMaybe (lat-leq (from x) orig) (to orig)) <,> from) v)) ::_)
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

        {-# TERMINATING #-}
        dfsFoldM :
          (forall {A} -> A -> V A -> List B -> B) ->
          B ->
          V A ->
          M B
        dfsFoldM {B = B} f def (TVarC OrigT {{skC oT refl}} g v) = do --TODO: cleanup!
            x <- fst <$> read v
            fst <$> dfsFoldM' x (TVarC _ {{skC oT refl}} ((just o fst) <,> (_, [])) v) []
          where
            open ThresholdVarMonad CLTVM using () renaming (read to readC)

            dfsFoldM' : A -> V A -> StateT (List (Sigma Set V)) M B
            dfsFoldM' x (TVarC OrigT {{skC oT refl}} g v) visited
              with ((_ , (TVarC OrigT {{skC oT refl}} g v)) elem visited withEq eqSig)
            ...| true = return (def , visited)
            ...| false = do
              (x' , asm) <- read v
              let subres = retrieveMinReason x' asm
              maybe'
                (\cls -> do
                  (lst , visited') <- loop (concat cls) ([] , visited)
                    \{  (A , v) (lst , visited) -> do
                      x <- readC v
                      (map1 (_:: lst)) <$> dfsFoldM' x v visited}
                  return (f x' (TVarC _ {{skC oT refl}} ((just o fst) <,> (_, [])) v) lst , visited')
                )
                (return (def , visited)) --TODO : correct?
                subres


        deepestCut : V A -> M (LatClause V)
        deepestCut = dfsFoldM (\{
          x v [] -> [ _ , v ] ;
          _ _ subclauses -> concat subclauses}) []

        clauseProp : A -> V A -> LatClause V -> M T
        clauseProp x (TVarC OrigT {{skC _ refl}} (_ <,> from) v) clause = do
          mapM {B = T} (\{(_ , v' ) -> void $ readC v' }) clause --TODO : THis is fishy. x' should be used...this might be the difference that the threshold function makes
          write v (fst (from x) , [ fst (from x) , clause ])
          where
            open ThresholdVarMonad CLTVM using () renaming (read to readC; tvbf to tvbf')
            open BijTFunctor tvbf' renaming (_<bt$>_ to _<bt$>'_)
