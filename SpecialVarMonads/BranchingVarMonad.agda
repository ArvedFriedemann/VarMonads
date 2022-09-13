{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
module SpecialVarMonads.BranchingVarMonad where

open import AgdaAsciiPrelude.AsciiPrelude
open import BasicVarMonads.ConstrainedVarMonad
open import Util.Monad
--open import Debug.Trace

private
  variable
    A B S VS : Set
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

mapVarSVar : {{sto : ISTO (V S)}} -> (V (SVarPType V S A) -> V (SVarPType V S B)) -> SVar V S A -> SVar V S B
mapVarSVar f (SVarC p v) = SVarC p (f v)

open import Util.PointerEquality

ISTOSVar :
  {{isto : ISTO (Sigma Set V)}} ->
  {{isto : ISTO (V S)}} -> ISTO (Sigma Set (SVar V S))
ISTOSVar = ExtractISTOFrom \{(SVarC _ v) -> _ , v}

open import BasicVarMonads.ThresholdVarMonad

halfSVarBijTFunc : {{sto : ISTO (V S)}} -> BijTFunc A B -> BijTFunc (SVarPType V S A) B
halfSVarBijTFunc (to <,> from) = (to o fst) <,> \b -> from b , empty , nothing

-- This doesn't work for so many reasons...the maps would need to adjust their type recursively,
-- there would need to be a reverse operation etc...
-- {-# TERMINATING #-}
-- SVarBijTFunc : {{sto : ISTO (V S)}} -> {{bf : BijTFunctor V}} -> BijTFunc A B -> BijTFunc (SVarPType V S A) (SVarPType V S B)
-- SVarBijTFunc (to <,> from) = (\{(x , mp , p) -> (_, mapMap recVTrans mp , (recVTrans <$> p)) <$> to x})
--                               <,> (\{(x , mp , p) -> (from x , {!   !} , {!!}) })
--     where
--       open BijTFunctor {{...}}
--       recVTrans = mapVarSVar (SVarBijTFunc (to <,> from) <bt$>_)
--       recBackTrans = mapVarSVar (SVarBijTFunc (to <,> from) <bt$>_)--this one doesnt even work...


record BranchingVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set)
    (VS : Set) : Set where
  inductive
  field
    tvm : ThresholdVarMonad K M V
    overlap {{mr}} : MonadReader (List VS) M
    branchedLift :
      {{mon : Monad M'}} ->
      {{mr : MonadReader (List VS) M' }} ->
      (forall {A} -> M A -> M' A) ->
      ((forall {B} -> M' B -> M' B) -> M' A) -> --Transformation has to preserve state!
      M' A
  open ThresholdVarMonad tvm public
  branched : ((forall {B} -> M B -> M B) -> M A) -> M A
  branched = branchedLift id

liftBranchingVarMonad :
  {{mon : Monad M'}} ->
  {{mr : MonadReader (List VS) M'}} ->
  (forall {A} -> M A -> M' A) ->
  BranchingVarMonad K M V VS -> BranchingVarMonad K M' V VS
liftBranchingVarMonad liftT bvm = record {
  tvm = liftThresholdVarMonad liftT tvm ;
  branchedLift = \liftT2 -> branchedLift (liftT2 o liftT) }
  where open BranchingVarMonad bvm

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
headEq [] [] = true
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
  {{mf : MonadFork M}}
  {{tvm : ThresholdVarMonad K M V}} where

  open MonadFork mf
  open import Util.Lattice
  open BoundedMeetSemilattice {{...}}

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
      modify' vp \{(a , mp , par) -> (a , insert vs (SVarC pp vp) mp , par)}
      return (is-nothing par , (SVarC pp vp))

    getChildAndCreated? : {{k : K A}} ->
      V S -> SVar V S A -> M (Bool -x- SVar V S A)
    getChildAndCreated? vs (SVarC path v) = atomically do
      (x , mp , par) <- read v
      (SVarC pc vc) <- fromMaybe (newSVar (vs :: path)) (return <$> lookup vs mp)
      write v (x , insert vs (SVarC pc vc) mp , par)
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
    when c? (fork $ vpar =p> v)
    -- when c? (fork $ v =p> vpar)
    return (SVarC lstpar vpar)

  getChild : {{k : K A}} -> V S -> SVar V S A -> M (SVar V S A)
  getChild vs (SVarC lst v) = do
    (c? , (SVarC lstpar vc)) <- getChildAndCreated? vs (SVarC lst v)
    when c? (fork $ v =p> vc)
    -- v =p> vc
    -- fork $ read (eqThreshold (top , empty , nothing) <bt$> v) >>= write vc --doesn't work with fork...
    -- fork $ read v >>= write vc --doesn't work with fork...
    -- read v >>= write vc
    -- when c? (fork $ vc =p> v)
    return (SVarC lstpar vc)


  getLocalVar : {{k : K A}} -> SVar V S A -> List (V S) -> M (SVar V S A)
  getLocalVar (SVarC origin v) target = do
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

  -- CDVM : ConstrDefVarMonad K M (SVar V S)
  -- CDVM = record {
  --   new = ask >>= newSVar' ;
  --   read = getLocalVar >=> \{(SVarC _ v) -> fst <$> read v};
  --   write = \v x -> getLocalVar v >>= \{(SVarC _ v) ->
  --                   atomically (modifyAtom' v (map1 (const x) )) } }

  open MonadReader {{...}} using (local; reader)
  open MonadTrans {{...}}

  ask : {{mr : MonadReader A M''}} -> M'' A
  ask = reader id

  instance
    _ = MonadReaderFromState
    _ = MonadTransStateT
    _ = MonadStateT
    _ = MonadStateStateT

  --we have to go the long way with new TVars here because SVars do not have a BijTFunctor instance, even when their original variable has one...
  ThresholdVarMonad=>BranchingVarMonad : BranchingVarMonad K (StateT (List (V S)) M) (TVar K (SVar V S)) (V S)
  ThresholdVarMonad=>BranchingVarMonad = record {
    tvm = record {
      cvm = record {
        new = (TVarC _ (just <,> id)) <$> (ask >>= liftT o newSVar') ;
        read = \{(TVarC OrigT f v) ->
          ask >>= liftT o (getLocalVar v >=> read o
            onSVarV (halfSVarBijTFunc f <bt$>_)) } ;
        write = \{(TVarC OrigT f v) x ->
          ask >>= liftT o ( getLocalVar v >=> flip write x o
            onSVarV (halfSVarBijTFunc f <bt$>_) )} } ;
      tvbf = TVarBijTFunctor } ;
    branchedLift = \{{_}} {{mr}} liftT' m -> do
        vs <- liftT' (liftT (new {A = S}))
        local {{r = mr}} (vs ::_) (m (local {{r = mr}} $ drop 1))
       }
