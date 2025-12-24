{-# OPTIONS --guardedness #-}
open import Prelude

module Main where

import Text.PrettyPrint.Annotated as Doc renaming (Doc to t)

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromString
open import IO.Base
open import IO.Finite

open List using (_∷_; [])
open import RTLIL.Syntax
open import RTLIL.Syntax.PrettyPrint using ()

instance
  _ = String.isString
  _ = ℕ.number

dut : Design.t
dut = Design.mk (Maybe.just 1) $
  record
  { name = "\\1dff"
  ; attributes = Attributes.mk
    $ ("\\blackbox" , 1)
    ∷ ("\\cells_not_processed" , 1)
    ∷ ("\\src" , "asicworld/verilog/code_verilog_tutorial_escape_id.v:3.1-14.10")
    ∷ []
  ; parameters = Parameters.empty
  ; connections = []
  ; wires = Wire.fromList
    $ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_escape_id.v:11.10-11.14"
        )
        (Wire.iowire "\\cl$k" (Wire.input 4))

    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_escape_id.v:11.7-11.8"
        )
        (Wire.iowire "\\d" (Wire.input 3))

    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_escape_id.v:12.8-12.9"
        )
        (Wire.iowire "\\q" (Wire.output 1))

    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_escape_id.v:12.11-12.14"
        )
        (Wire.iowire "\\q~" (Wire.output 2))

    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_escape_id.v:11.16-11.23"
        )
        (Wire.iowire "\\reset*" (Wire.input 5))
    ∷ []
  ; cells = Map.empty
  }
  ∷ []

main : Main
main = run $ do
  putStrLn $ Doc.render {ann = 𝟙*.t} $ Doc.pPrint dut
