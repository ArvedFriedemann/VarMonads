{-# OPTIONS --type-in-type #-}
module Assembly.Main where

open import AgdaAsciiPrelude.AsciiPrelude hiding (_>>_; _>>=_; return)
open import Assembly.Examples
-- open import Assembly.ForkExamples

open import IO

showRes : Maybe Nat -> IO T
showRes (just x) = putStrLn $ "    Had value " ++s showN x
showRes nothing = putStrLn "    No value"

main : Main
main = run $ do
  -- putStrLn "testWrite"
  -- showRes testWrite
  -- putStrLn "testFork"
  -- showRes testFork
  putStrLn "testBranch"
  showRes testBranch
