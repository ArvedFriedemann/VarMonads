{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.ClauseLearningVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    M V F K : Set -> Set

Assignment : (K : Set -> Set) -> (V : Set -> Set) -> Set
Assignment K V = Sigma Set \A -> K A -x- A -x- V A

Clause : (K : Set -> Set) -> (V : Set -> Set) -> Set
Clause K V = List (Assignment K V)

--AsmPtr : (K : Set -> Set) -> (V : Set -> Set) -> (A : Set) -> Set
--AsmPtr K V A = V (A -x- List (Clause K V))

{-# NO_POSITIVITY_CHECK #-}
data AsmPtr (K : Set -> Set) (V : Set -> Set) (A : Set) : Set where
  AsmPtrC : V (A -x- List (Clause K (AsmPtr K V))) -> AsmPtr K V A


--open import BasicVarMonads.ThresholdVarMonad
open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation

module ClauseLearning
    {{tvm : ConstrDefVarMonad K M V}}
    {{kas : K derives (K o (_-x- List(Clause K (AsmPtr K V))))}}
    {{ms : MonadState (Clause K (AsmPtr K V)) M }} where

  open ConstrDefVarMonad tvm
  open MonadState ms hiding (_>>=_;_>>_;return;_<$>_) renaming (modify to modifyS)

  NCVM : ConstrDefVarMonad K M (AsmPtr K V)
  NCVM = record {
    new = AsmPtrC <$> new ;
    read = \{(AsmPtrC v) -> do
      (x , _) <- read v
      modifyS ((_ , it , x , AsmPtrC v) ::_)
      return x
      };
    write = \{(AsmPtrC v) x -> do
      asm <- get
      write v (x , [ asm ]) }}


  open import Util.PointerEquality
  open import Util.Lists
  open import Util.Monad
  open PEq {{...}}

  module _ {{eq : PEq V}} where

    eqSig : {V : Set -> Set} -> {{PEq V}} -> Eq (Sigma Set V)
    eqSig = record { _==_ = \{(_ , v1) (_ , v2) -> v1 =p= v2 } }

    -- TODO : the visited variables should be handed to the next branch as well, otherwise
    -- we will visit variables several times...problem: this cannot be done properly as it is not
    -- known in which order they will be accessed
    {-# TERMINATING #-}
    dfsFoldM : {{k : K A}} ->
      (forall {C} -> {{kc : K C}} -> C -> AsmPtr K V C -> List B -> B) ->
      B ->
      AsmPtr K V A ->
      M B
    dfsFoldM f def (AsmPtrC v) = (fst <$> read v)
                                  >>= dfsFoldM' [] f def (AsmPtrC v)
                                  >>= return o fst
      where
      dfsFoldM' : {{k : K A}} ->
        List (Sigma Set V) ->
        (forall {C} -> {{kc : K C}} ->  C -> AsmPtr K V C -> List B -> B) ->
        B ->
        AsmPtr K V A ->
        A ->
        M (B -x- List (Sigma Set V))
      dfsFoldM' visited f def (AsmPtrC v) x
        with (_ , v) elem visited withEq eqSig
      ...| true = return (def , visited)
      ...| false = do
        (_ , asms) <- read v
        mapHead asms (return (def , visited)) \cls -> do
          (lst , visited') <- loop cls ([] , visited)
            \{(_ , k , x' , v') (lst , visited) ->
              (map1 (_:: lst)) <$> dfsFoldM' {{k = k}} ((_ , v) :: visited) f def v' x'
            }
          return (f x (AsmPtrC v) lst , visited')

    deepestCut : {{k : K A}} -> AsmPtr K V A -> M (Clause K (AsmPtr K V))
    deepestCut = dfsFoldM (\{
      x v [] -> [ _ , it , x , v ] ;
      _ _ subclauses -> concat subclauses}) []

    clauseProp : {{k : K A}} -> {{K derives Eq}} -> A -> AsmPtr K V A -> Clause K (AsmPtr K V) -> M T
    clauseProp x (AsmPtrC v) clause = do
      match <- mapM (\{(_ , k , x' , (AsmPtrC v')) -> let instance _ = k in (x' ==_) o fst <$> read v'}) clause
      when (all id match) (write v (x , [ clause ]))

-- TODO : Monad with state to track variables and put clauses on assigning variables
-- eventually, real clause learning algorithm.
