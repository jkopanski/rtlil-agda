{-# OPTIONS --guardedness #-}
module runtests where

open import Overture
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

semanticTests : TestPool
semanticTests = mkTestPool "Operational semantics"
  $ "unsigned_add"
  ∷ []

main : Main
main = run $ ignore $ runner
  $ testPaths "pretty" prettyTests
  ∷ testPaths "semantics" semanticTests
  ∷ [] where

  testPaths : String.t → TestPool → TestPool
  testPaths dir pool =
    let testCases = List.map ((dir ++ "/") ++_) (pool .TestPool.testCases)
    in record pool { testCases = testCases }
