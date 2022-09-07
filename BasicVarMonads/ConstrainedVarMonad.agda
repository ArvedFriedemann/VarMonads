{-# OPTIONS --type-in-type #-}
module BasicVarMonads.ConstrainedVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set
    K M V : Set -> Set

record ConstrVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    read : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M

record ConstrDefVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> M (V A)
    read : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M

  modify : {{k : K A}} -> V A -> (A -> A -x- B) -> M B
  modify v f = read v >>= \x -> write v (fst (f x)) >> return (snd (f x))

  modify' : {{k : K A}} -> V A -> (A -> A) -> M T
  modify' v f = modify v ((_, tt) o f)

record NewConstrDefVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> M (V A)
    read : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

  modify : V A -> (A -> A -x- B) -> M B
  modify v f = read v >>= \x -> write v (fst (f x)) >> return (snd (f x))

  modify' : V A -> (A -> A) -> M T
  modify' v f = modify v ((_, tt) o f)

--Free Constrained Default VarMonad
data FCDVarMon (K : Set -> Set) (V : Set -> Set) : Set -> Set where
  newF : {{k : K A}} -> FCDVarMon K V (V A)
  readF : {{k : K A}} -> V A -> FCDVarMon K V A
  writeF : {{k : K A}} -> V A -> A -> FCDVarMon K V T
  returnF : A -> FCDVarMon K V A
  bindF : FCDVarMon K V A -> (A -> FCDVarMon K V B) -> FCDVarMon K V B

data FNCDVarMon (K : Set -> Set) (V : Set -> Set) : Set -> Set where
  newF : {{k : K A}} -> FNCDVarMon K V (V A)
  readF : V A -> FNCDVarMon K V A
  writeF : V A -> A -> FNCDVarMon K V T
  returnF : A -> FNCDVarMon K V A
  bindF : FNCDVarMon K V A -> (A -> FNCDVarMon K V B) -> FNCDVarMon K V B

FNCDVarMonNewConstrDefVarMonad : NewConstrDefVarMonad K (FNCDVarMon K V) V
FNCDVarMonNewConstrDefVarMonad = record {
  new = newF ;
  read = readF ;
  write = writeF ;
  mon = record {
    return = returnF ;
    _>>=_ = bindF } }
