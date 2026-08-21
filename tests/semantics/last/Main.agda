{-# OPTIONS --guardedness #-}
module Main where

import Overture
import IO.Base as IO
import Cheshire.Test as Test
import Cheshire.Instance.Combinational as Combinational
open Combinational using (module Syntax)

main : IO.Main
main = Test.Harness.combinational 4 Syntax.last?
