{-# OPTIONS --type-in-type #-}
module Assembly.Main where

open import AgdaAsciiPrelude.AsciiPrelude hiding (_>>_; _>>=_; return)
open import Assembly.Examples

open import IO

main : Main
main = run $ putStrLn "I'm alive" >> return testBranch >>= \{
  (just x) -> putStrLn "Had value";
  nothing -> putStrLn "No value"}
