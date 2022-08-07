{-# OPTIONS --type-in-type #-}

module VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B S : Set
    M V F C K : Set -> Set
    TF : (Set -> Set) -> Set

-------------------------------------------
--Constrained VarMonads
-------------------------------------------

record ConstrBaseVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    read : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M


--TODO modify gives extra read!!
-- NOTE : modify varmonads are just implementation detail.
--BaseVarMonad given to the user (and only that is constrained by lattices)
record ConstrModifyVarMonad
    (K : Set -> Set)
    (M : Set -> Set)
    (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    --write : {{k : K A}} -> V A -> A -> M T
    modify : {{k : K A}} -> V A -> (\ A -> A -x- B) -> M B
    overlap {{mon}} : Monad M

  read : {{k : K A}} -> V A -> M A
  read p = modify p \ x -> x , x

  modify' : {{k : K A}} -> V A -> (A -> A) -> M T
  modify' p f = modify p \ x -> f x , tt

  write : {{k : K A}} -> V A -> A -> M T
  write p v = modify' p (const v)

ma <|> mb

do {x <- isCons xs
comp on x}
<|>
do {x <- isNil xs
y <- get somewhereElse
comp on x and y}


2-variable SAT solver

initialise : (f : Bool -> Bool -> Bool) -> M (Bool ­-x- Bool)
initialise f = do
  xs <- new [ true, false ]
  ys <- new [ true, false ]

  --write xs [ true ] <|> write xs [ false ]
  --write ys [ true ] <|> write ys [ false ]

  x <- read xs
  y <- read ys

  if f x y then return (Just (x , y)) else empty

ContT : (R : Set) -> (M : Set -> Set) -> (A : Set) -> Set
ContT R M A = (A -> M R) -> M R

callCC : ((A -> ContT R M B) -> ContT R M A) -> ContT R M A
callCC f = \ c -> f (\ x -> \ _ -> c x) c

read : V A -> ContT () M A
read var = callCC \k ->
  watch var \x -> k x

-- -- hello
-- -- your number is 2
-- -- your number is 3
-- -- goodbye
-- program : ContT () IO ()
-- program = do
--   print "hello"
--
--   reset do
--     number <- shift \k -> k 2 >> k 3
--     print ("your number is " ++ show number)
--
--   print "goodbye"

gets :: (A -> B) -> V A -> M B

case lst of
  [] -> ...
  x :: xs -> ...

--------------------------------------------------
--Unconstrained VarMonads
--------------------------------------------------
--TODO do make those separate monads and make a construction from a T constrianed monad

data BVMUnit : Set where
  bvmunit : BVMUnit

instance
  bvmunitI = bvmunit

BaseVarMonad : (M : Set -> Set) -> (V : Set -> Set) -> Set
BaseVarMonad = ConstrBaseVarMonad (const BVMUnit)

ModifyVarMonad : (M : Set -> Set) -> (V : Set -> Set) -> Set
ModifyVarMonad = ConstrModifyVarMonad (const BVMUnit)
