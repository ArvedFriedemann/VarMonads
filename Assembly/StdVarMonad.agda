{-# OPTIONS --type-in-type #-}
module Assembly.StdVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import AgdaAsciiPrelude.Instances
open import Data.Nat.Properties renaming (<-strictTotalOrder to NatSTO)
open import BasicVarMonads.BaseVarMonad

open MonadState {{...}} using () renaming (get to getS; put to putS)

private
  variable
    A B S : Set
    M : Set -> Set

instance
  _ : ISTO Nat
  _ = STO-to-ISTO NatSTO


record NatPtr (A : Set) : Set where
  constructor ptr
  field
    idx : Nat

open NatPtr public

STONatPtr : StrictTotalOrder _ _ _
STONatPtr = record {
  Carrier = Sigma Set NatPtr ;
  _≈_ = \ {(_ , ptr x1) (_ , ptr x2) -> x1 === x2} ;
  _<_ = \ {(_ , ptr x1) (_ , ptr x2) -> x1 < x2} ;
  isStrictTotalOrder = record {
    isEquivalence = record { refl = refl ; sym = sym ; trans = trans } ;
    trans = <-trans ;
    compare = \ {(_ , ptr x1) (_ , ptr x2) -> <-cmp x1 x2 } } }

ISTONatPtr : ISTO (Sigma Set NatPtr)
ISTONatPtr = STO-to-ISTO (STONatPtr)

open import Util.PointerEquality

PEqNatPtr : PEq NatPtr
PEqNatPtr = record { _=p=_ = \{(ptr p1) (ptr p2) -> p1 == p2} }
  where
    instance
      _ = eqNat

defaultState : Set
defaultState = Nat -x- Map Nat (Sigma Set id)

defaultInit : defaultState
defaultInit = (0 , empty)

open import AgdaAsciiPrelude.TrustMe
postulate dummy : {A : Set} -> A

safeLookup : NatPtr A -> Map Nat (Sigma Set id) -> A
safeLookup (ptr p) mp with lookup p mp
safeLookup (ptr p) mp | just (B , b) = trustVal b
safeLookup (ptr p) mp | nothing = dummy

defaultVarMonadStateM : Set -> Set
defaultVarMonadStateM = StateT defaultState id

instance
  _ = MonadStateTId
  _ = MonadStateStateTId

defaultVarMonad : BaseVarMonad defaultVarMonadStateM NatPtr
defaultVarMonad = record {
    new = \ {A} x (n , mp) -> (ptr n) , (suc n , insert n (A , x) mp) ;
    read = \ { {A} p (n , mp) -> safeLookup p mp , (n , mp) } ;
    write = \ {A} p v (n , mp) -> tt , n , (insert (idx p) (A , v) mp)
  }

open import BasicVarMonads.Constructions

defaultModifyVarMonad = BaseVarMonad=>ModifyVarMonad {{defaultVarMonad}}

open import MiscMonads.ConcurrentMonad
open import BasicVarMonads.ModifyVarMonad

defaultForkModifyVarMonad = liftModifyVarMonad {{mon' = FMFTMonad}} liftF defaultModifyVarMonad

runDefVarMonad : defaultVarMonadStateM A -> A
runDefVarMonad m = fst $ m defaultInit
