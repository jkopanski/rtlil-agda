{-# OPTIONS --guardedness #-}

open import Prelude

module Main where

open import IO.Base
open import IO.Finite

main : Main
main = run $ do
  putStrLn "test"
