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

record BranchingVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (S : Set) : Set where
  field
    cvm : ConstrDefVarMonad K M V
    newBranch : M (V S)
  open ConstrDefVarMonad cvm public

{-# NO_POSITIVITY_CHECK  #-}
record SVar (V : Set -> Set) (S : Set) {{sto : ISTO (V S)}} (A : Set) : Set where
  constructor SVarC
  field
    path : List (V S)
    --content, children, maybe parent
    var : V (A -x- Map (V S) (SVar V S A) -x- Maybe (SVar V S A))

initEqSegment : {{eq : Eq A}} -> List A -> List A -> (List A -x- List A -x- List A)
initEqSegment [] ys = ([] , [] , ys)
initEqSegment xs [] = ([] , xs , [])
initEqSegment (x :: xs) (y :: ys) with x == y
... | false = ([] , x :: xs , y :: ys)
... | true  = let (i , xs' , ys') = initEqSegment xs ys in (x :: i , xs' , ys')

--target path (where we are), origin path (where the variable is from),
  --(orig to target , orig to origin)
connectingPath : {{eq : Eq A}} -> List A -> List A -> (List A -x- List A)
connectingPath xs ys = let (i , xs' , ys') = initEqSegment (reverse xs) (reverse ys)
                        in ((maybeToList $ last i) ++ xs') , ((maybeToList $ last i) ++ ys')

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
  {{stm : MonadSTM M' M}}
  {{isto : ISTO (V S)}}
  {{eq : Eq (V S)}}
  {{bvm : ConstrDefVarMonad K M' V}}
  {{ks : K derives (\A -> K (A -x- Map (V S) (SVar V S A) -x- Maybe (SVar V S A))) }}
  {{mr' : MonadReader (List (V S)) M'}}
  {{mr : MonadReader (List (V S)) M}}
  {{tvm : ThresholdVarMonad K M V}} where

  open MonadReader {{...}} using (reader)

  ask : {{mr : MonadReader A M''}} -> M'' A
  ask = reader id

  open MonadSTM stm
  open import AgdaAsciiPrelude.Instances
  instance
    _ = MonadMaybe

  open ConstrDefVarMonad bvm
  
  newSVar : {{k : K A}} -> M' (SVar V S A)
  newSVar = (| SVarC ask new |)


  -- TODO : Set propagator if created!
  getParentAndCreated? : {{k : K A}} -> SVar V S A -> M (Bool -x- SVar V S A)
  getParentAndCreated? (SVarC _ v) = atomically do
    (x , mp , par) <- read v
    p <- fromMaybe newSVar (return <$> par)
    write v (x , mp , just p)
    return (is-nothing par , p)

  -- TODO : Set propagator if created!
  getChildAndCreated? : {{k : K A}} ->
    SVar V S A -> V S -> M (Bool -x- SVar V S A)
  getChildAndCreated? (SVarC _ v) vs = atomically do
    (x , mp , par) <- read v
    c <- fromMaybe newSVar (return <$> lookup _ vs mp)
    write v (x , insert _ vs c mp , par)
    return (is-nothing par , c)

  open ThresholdVarMonad tvm

  getParent : {{k : K A}} -> SVar V S A -> M (SVar V S A)
  getParent (SVarC lst v) = do
    (c? , (SVarC lstpar vpar)) <- getParentAndCreated? (SVarC lst v)
    when c? (vpar =p> v)
    return (SVarC lstpar vpar)

  getChild : {{k : K A}} -> SVar V S A -> V S -> M (SVar V S A)
  getChild (SVarC lst v) vs = do
    (c? , (SVarC lstpar vc)) <- getChildAndCreated? (SVarC lst v) vs
    when c? (v =p> vc)
    return (SVarC lstpar vc)


  getLocalVar : {{k : K A}} -> SVar V S A -> M (SVar V S A)
  getLocalVar (SVarC origin v) = do
    target <- ask
    let (origToTarget , origToOrigin) = connectingPath {{eq = eq}} target origin
    par <- loop {M = M}
                (reverse origToOrigin)
                (const getParent)
                (return (SVarC origin v))
    loop {M = M} origToTarget
                (\s sv -> getChild sv s )
                (return par)
