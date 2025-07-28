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
  { name = "\\addbit"
  ; attributes = Attributes.mk
    $ ("\\cells_not_processed" , 1)
    ∷ ("\\src" , "asicworld/verilog/code_verilog_tutorial_good_code.v:1.7-18.16")
    ∷ []
  ; parameters = Parameters.empty
  ; connections = []
  ; wires = Map.fromList
    $ let n = "\\a"
       in ( n
          , Attributes.insert
            ( "\\src"
            , "asicworld/verilog/code_verilog_tutorial_good_code.v:7.23-7.24"
            )
            (Wire.iowire n (Wire.input 1))
          )
    ∷ let n = "\\b"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_good_code.v:8.23-8.24"
           )
           (Wire.iowire n (Wire.input 2))
         )
    ∷ let n = "\\ci"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_good_code.v:9.23-9.25"
           )
           (Wire.iowire n (Wire.input 3))
         )
    ∷ let n = "\\co"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_good_code.v:11.22-11.24"
           )
           (Wire.iowire n (Wire.output 5))
         )
    ∷ let n = "\\sum"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_good_code.v:10.22-10.25"
           )
           (Wire.iowire n (Wire.output 4))
         )
    ∷ []
  ; cells = Map.empty
  }
  ∷ []

main : Main
main = run $ do
  putStrLn $ Doc.render {ann = 𝟙.0ℓ.⊤} $ Doc.pPrint dut
