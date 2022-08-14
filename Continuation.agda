{-# OPTIONS --type-in-type #-}
module Continuation where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonads

variable
  A B : Set
  V M : Set -> Set

infixl 1 _>>=bvm_
data FreeBVM (V : Set -> Set) : Set -> Set where
  newF : A -> FreeBVM V (V A)
  readF : V A -> FreeBVM V A
  writeF : V A -> A -> FreeBVM V T
  returnFBVM : A -> FreeBVM V A
  _>>=bvm_ : FreeBVM V A -> (A -> FreeBVM V B) -> FreeBVM V B


toCont : FreeBVM V A -> (Sigma Set \ B -> V B -x- (B -> FreeBVM V A) ) or (FreeBVM V A)
toCont ((returnFBVM x) >>=bvm f) = toCont (f x)
toCont ((readF x) >>=bvm f) = left (_ , x , f)
toCont ((fbm >>=bvm f') >>=bvm f) with toCont (fbm >>=bvm f')
... | right fbm' = right (fbm' >>=bvm f)
... | left (A , va , fa) = left (A , va , (\ x -> (fa x) >>=bvm f))
toCont m = right m

open ConstrBaseVarMonad {{...}}

evalToCont : {{bvm : BaseVarMonad M V}} -> FreeBVM V A -> M $ (Sigma Set \ B -> V B -x- (B -> FreeBVM V A) ) or A
evalToCont (newF a) = right <$> new a
evalToCont (readF x) = right <$> read x --this is the case where evaluation might come to a halt!
evalToCont (writeF v a) = right <$> write v a
evalToCont (returnFBVM x) = right <$> return x
evalToCont (fbm >>=bvm f) = evalToCont fbm >>= \{
                                (left (B , vb , fb)) -> return $ left (B , vb , \a -> (fb a) >>=bvm f);
                                (right x) -> evalToCont (f x)
                              }

M-V : (Set -> Set) -> (Set -> Set) -> Set -> Set
M-V M V A = M $ (Sigma Set \ B -> V B -x- (B -> M (FreeBVM V A)) ) or A

monadMV : {{BaseVarMonad M V}} -> Monad (M-V M V)
monadMV {M = M} {V = V} = record {
  return = return o right ;
  _>>=_ = \ m fm -> m >>= \{
    (left (B , vb , fb)) -> return (left (B , vb , \b -> {!!} ));
    (right y) -> {!    !}}  }

test : FreeBVM V Nat
test = newF 3 >>=bvm readF >>=bvm returnFBVM
