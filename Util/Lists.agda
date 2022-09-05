{-# OPTIONS --type-in-type #-}
module Util.Lists where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B : Set

mapHead : List A -> B -> (A -> B) -> B
mapHead [] def _ = def
mapHead (x :: _) def f = f x
