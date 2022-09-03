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
                        in xs' , ys'

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
  {{stm : MonadSTM M' M}}
  {{isto : ISTO (V S)}}
  {{eq : Eq (V S)}}
  {{bvm : ConstrDefVarMonad K M' V}}
  {{ks : K derives (\A -> K (A -x- Map (V S) (SVar V S A) -x- Maybe (SVar V S A))) }}
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

  newSVar : {{k : K A}} -> List (V S) -> M' (SVar V S A)
  newSVar lst = SVarC lst <$> new


  -- TODO : Set propagator if created!
  getParentAndCreated? : {{k : K A}} -> SVar V S A -> M (Bool -x- SVar V S A)
  getParentAndCreated? (SVarC [] v) = return (false , SVarC [] v)
  getParentAndCreated? (SVarC (_ :: pathTail) v) = atomically do
    (x , mp , par) <- read v
    p <- fromMaybe (newSVar pathTail) (return <$> par)
    write v (x , mp , just p)
    return (is-nothing par , p)

  -- TODO : Set propagator if created!
  getChildAndCreated? : {{k : K A}} ->
    V S -> SVar V S A -> M (Bool -x- SVar V S A)
  getChildAndCreated? vs (SVarC path v) = atomically do
    (x , mp , par) <- read v
    c <- fromMaybe (newSVar (vs :: path)) (return <$> lookup _ vs mp)
    write v (x , insert _ vs c mp , par)
    return (is-nothing par , c)

  open ThresholdVarMonad tvm

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
    -- TODO : connecting path should check maybe whether the upperose variable is the same
    let (origToTarget , origToOrigin) =
          if headEq {{eq = eq}} target origin
          then ([] , [])
          else connectingPath {{eq = eq}} target origin
    par <- loop {M = M} origToOrigin (return (SVarC origin v))
                (const getParent)
    res <- loop {M = M} origToTarget (return par)
                getChild
    return res
