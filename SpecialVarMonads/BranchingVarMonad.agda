{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module SpecialVarMonads.BranchingVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ConstrainedVarMonad
open import Util.Monad

private
  variable
    A B S : Set
    M M' M'' V K : Set -> Set

record StateCpyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (S : Set) : Set where
  field
    cvm : ConstrDefVarMonad K M V
    newBranch : M (V S)
  open ConstrDefVarMonad cvm public

SVarPType : (V : Set -> Set) -> (S : Set) -> {{sto : ISTO (V S)}} -> Set -> Set

{-# NO_POSITIVITY_CHECK  #-}
record SVar (V : Set -> Set) (S : Set) {{sto : ISTO (V S)}} (A : Set) : Set where
  constructor SVarC
  field
    path : List (V S)
    --content, children, maybe parent
    var : V (SVarPType V S A)

SVarPType V S A = A -x- Map (V S) (SVar V S A) -x- Maybe (SVar V S A)

onSVarV : {{sto : ISTO (V S)}} -> (V (SVarPType V S A) -> B) -> SVar V S A -> B
onSVarV f (SVarC _ v) = f v

open import BasicVarMonads.ThresholdVarMonad

SVarBijTFunc : {{sto : ISTO (V S)}} -> BijTFunc A B -> BijTFunc (SVarPType V S A) B
SVarBijTFunc (to <,> from) = (to o fst) <,> \b -> from b , empty _ , nothing

record BranchingVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    tvm : ThresholdVarMonad K M V
    branched : ((forall {B} -> M B -> M B) -> M A) -> M A
  open ThresholdVarMonad tvm public


afterInitEqSegment : {{eq : Eq A}} -> List A -> List A -> (List A -x- List A)
afterInitEqSegment [] ys = ([] , ys)
afterInitEqSegment xs [] = (xs , [])
afterInitEqSegment (x :: xs) (y :: ys) with x == y
... | false = (x :: xs , y :: ys)
... | true  = afterInitEqSegment xs ys

--target path (where we are), origin path (where the variable is from),
  --(orig to target , orig to origin)
connectingPath : {{eq : Eq A}} -> List A -> List A -> (List A -x- List A)
connectingPath xs ys = afterInitEqSegment (reverse xs) (reverse ys)

headEq : {{eq : Eq A}} -> List A -> List A -> Bool
headEq (x :: _) (y :: _) = x == y
headEq _ _ = false

{-}
addIfNex : {{isto : ISTO A}} -> A -> B -> Map A B -> (B -x- Map A B)
addIfNex a b mp = fromMaybe b (lookup _ a mp') , mp'
  where mp' = insertWith _ a (fromMaybe b) mp
  -}

open import MiscMonads.ConcurrentMonad
open import BasicVarMonads.ConstrainedVarMonad
open import BasicVarMonads.ThresholdVarMonad
open import Util.Derivation


module ConnectionOperations
  {{isto : ISTO (V S)}}
  {{eq : Eq (V S)}}
  {{ks : K S}}
  {{kvs : K derives (K o SVarPType V S) }}
  {{bvm : ConstrDefVarMonad K M' V}}
  {{stm : MonadSTM M' M}}
  {{tvm : ThresholdVarMonad K M V}}
  {{mr : MonadReader (List (V S)) M}} where

  open MonadReader {{...}} using (reader; local)

  ask : {{mr : MonadReader A M''}} -> M'' A
  ask = reader id

  open MonadSTM stm
  open import AgdaAsciiPrelude.Instances
  instance
    _ = MonadMaybe

  module _ where
    open ConstrDefVarMonad bvm

    newSVar : {{k : K A}} -> List (V S) -> M' (SVar V S A)
    newSVar lst = SVarC lst <$> new

    getParentAndCreated? : {{k : K A}} -> SVar V S A -> M (Bool -x- SVar V S A)
    getParentAndCreated? (SVarC [] v) = return (false , SVarC [] v)
    getParentAndCreated? (SVarC (vs :: pathTail) v) = atomically do
      (x , mp , par) <- read v
      (SVarC pp vp) <- fromMaybe (newSVar pathTail) (return <$> par)
      write v (x , mp , just (SVarC pp vp))
      modify' vp \{(a , mp , par) -> (a , insert _ vs (SVarC pp vp) mp , par)}
      return (is-nothing par , (SVarC pp vp))

    getChildAndCreated? : {{k : K A}} ->
      V S -> SVar V S A -> M (Bool -x- SVar V S A)
    getChildAndCreated? vs (SVarC path v) = atomically do
      (x , mp , par) <- read v
      (SVarC pc vc) <- fromMaybe (newSVar (vs :: path)) (return <$> lookup _ vs mp)
      write v (x , insert _ vs (SVarC pc vc) mp , par)
      modify' vc \{(a , mp , par) -> (a , mp , just (SVarC path v))}
      return (is-nothing par , (SVarC pc vc))

  open ThresholdVarMonad tvm
  open import SpecialVarMonads.Propagators.BasicPropagators
  open EqTPropagators
  instance
    _ = tvbf

  getParent : {{k : K A}} -> SVar V S A -> M (SVar V S A)
  getParent (SVarC lst v) = do
    (c? , (SVarC lstpar vpar)) <- getParentAndCreated? (SVarC lst v)
    when c? (vpar =p> v)
    return (SVarC lstpar vpar)

  getChild : {{k : K A}} -> V S -> SVar V S A -> M (SVar V S A)
  getChild vs (SVarC lst v) = do
    (c? , (SVarC lstpar vc)) <- getChildAndCreated? vs (SVarC lst v)
    when c? (v =p> vc)
    return (SVarC lstpar vc)


  getLocalVar : {{k : K A}} -> SVar V S A -> M (SVar V S A)
  getLocalVar (SVarC origin v) = do
    target <- ask
    let (ancToTarget , ancToOrigin) =
          if headEq {{eq = eq}} target origin
          then ([] , [])
          else connectingPath {{eq = eq}} target origin
    par <- loop {M = M} ancToOrigin
                (SVarC origin v)
                (const getParent)
    res <- loop {M = M} ancToTarget
                par
                getChild
    return res

  newSVar' : {{k : K A}} -> List (V S) -> M (SVar V S A)
  newSVar' = atomically o newSVar

  open ConstrDefVarMonad bvm using () renaming (modify' to modifyAtom')

  CDVM : ConstrDefVarMonad K M (SVar V S)
  CDVM = record {
    new = ask >>= newSVar' ;
    read = getLocalVar >=> \{(SVarC _ v) -> fst <$> read v};
    write = \v x -> getLocalVar v >>= \{(SVarC _ v) ->
                    atomically (modifyAtom' v (map1 (const x) )) } }

  instance
    _ = CDVM

  ThresholdVarMonad=>BranchingVarMonad : BranchingVarMonad K M (TVar K (SVar V S))
  ThresholdVarMonad=>BranchingVarMonad = record {
    tvm = ThresholdVarMonad=>ConstrDefVarMonad=>ThresholdVarMonad
            SVar.var
            SVarBijTFunc ;
    branched = \m -> new >>= \vs -> local (vs ::_) (m (local $ drop 1)) }
