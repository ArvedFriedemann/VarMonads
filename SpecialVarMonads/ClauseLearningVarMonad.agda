{-# OPTIONS --type-in-type #-}
module SpecialVarMonads.ClauseLearningVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    M V F K : Set -> Set

Assignment : (V : Set -> Set) -> Set
Assignment V = Sigma Set \A -> A -x- V A

Clause : (V : Set -> Set) -> Set
Clause V = List (Assignment V)

--AsmPtr : (V : Set -> Set) -> (A : Set) -> Set
--AsmPtr V A = V (A -x- List (Clause V))

{-# NO_POSITIVITY_CHECK #-}
record AsmPtr (V : Set -> Set) (A : Set) : Set where
  constructor AsmPtrC
  inductive
  field
    p : V (A -x- List (Clause (AsmPtr V)))


open import BasicVarMonads.ThresholdVarMonad
open import BasicVarMonads.ConstrainedVarMonad
open import Util.Derivation

module ClauseLearning
    {{tvm : ThresholdVarMonad K M V}}
    {{kas : K derives (K o (_-x- List(Clause (AsmPtr V))))}}
    {{ms : MonadState (Clause (AsmPtr V)) M }} where

  open ThresholdVarMonad tvm
  open MonadState ms hiding (_>>=_;_>>_;return;_<$>_) renaming (modify to modifyS)

  NCVM : NewConstrDefVarMonad K M (AsmPtr V)
  NCVM = record {
    new = AsmPtrC <$> new ;
    read = \{(AsmPtrC v) -> do
      (x , _) <- read v
      modifyS ((_ , x , AsmPtrC v) ::_)
      return x
      };
    write = \{(AsmPtrC v) x -> do
      asm <- get
      write v (x , [ asm ]) }}

  dfsFoldM' : (forall {A} -> List (M B) -> M B) -> B -> AsmPtr V A -> A -> M B
  dfsFoldM' f def (AsmPtrC v) x = do
    (_ , asms) <- read v
    foldr (\cls _ -> f $ map (\{(_ , x' , v') -> dfsFoldM' f def v'}) cls) (return def) asms



-- TODO : Monad with state to track variables and put clauses on assigning variables
-- eventually, real clause learning algorithm.
