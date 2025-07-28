{-# OPTIONS --guardedness #-}

open import Prelude

module runtests where

open import IO.Base
open import Test.Golden

open List using (_∷_; [])
open String using (_++_)

prettyTests : TestPool
prettyTests = mkTestPool "Pretty printing"
  $ "code_verilog_tutorial_escape_id"
  ∷ "code_verilog_tutorial_good_code"
  ∷ "code_verilog_tutorial_addbit"
  ∷ []

main : Main
main = run $ ignore $ runner
  $ testPaths "pretty" prettyTests
  ∷ [] where

  testPaths : String.t → TestPool → TestPool
  testPaths dir pool =
    let testCases = List.map ((dir ++ "/") ++_) (pool .TestPool.testCases)
    in record pool { testCases = testCases }
