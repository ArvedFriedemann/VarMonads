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

runDefVarMonad : defaultVarMonadStateM A -> A
runDefVarMonad m = fst $ m defaultInit
