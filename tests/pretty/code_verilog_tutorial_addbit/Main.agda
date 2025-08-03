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
dut = Design.mk (Maybe.just 3) $
  record
  { name = "\\addbit"
  ; attributes = Attributes.mk
    $ ("\\cells_not_processed" , 1)
    ∷ ("\\src" , "asicworld/verilog/code_verilog_tutorial_addbit.v:1.1-24.10")
    ∷ []
  ; parameters = Parameters.empty
  ; connections = let open NonEmpty using (_∷_)
    in Signal.concat
        ("\\co" ∷ "\\sum" ∷ [])
        ⇐ "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y"
    ∷ []
  ; wires =
      Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
        )
        (Wire.bus "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y" 2)
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
        )
        (Wire.bus "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y" 2)
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:9.7-9.8"
        )
        (Wire.iowire "\\a" (Wire.input 1))
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:10.7-10.8"
        )
        (Wire.iowire "\\b" (Wire.input 2))
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:11.7-11.9"
        )
        (Wire.iowire "\\ci" (Wire.input 3))
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:14.8-14.10"
        )
        (Wire.iowire "\\co" (Wire.output 5))
    ∷ Attributes.insert
        ( "\\src"
        , "asicworld/verilog/code_verilog_tutorial_addbit.v:13.8-13.11"
        )
        (Wire.iowire "\\sum" (Wire.output 4))
    ∷ []
  ; cells =
      record
        { attributes = Attributes.mk $
          ( "\\src"
          , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
          ) ∷ []
        ; type = "$add"
        ; name = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1"
        ; parameters = Parameters.mk
          $ ("\\A_SIGNED" , 0)
          ∷ ("\\A_WIDTH"  , 1)
          ∷ ("\\B_SIGNED" , 0)
          ∷ ("\\B_WIDTH"  , 1)
          ∷ ("\\Y_WIDTH"  , 2)
          ∷ []
        ; connections =
            "\\A" ⇐ "\\a"
          ∷ "\\B" ⇐ "\\b"
          ∷ "\\Y" ⇐ "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y"
          ∷ []
        }
    ∷ record
        { attributes = Attributes.mk $
          ( "\\src"
          , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
          ) ∷ []
        ; type = "$add"
        ; name = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2"
        ; parameters = Parameters.mk
          $ ("\\A_SIGNED" , 0)
          ∷ ("\\A_WIDTH"  , 2)
          ∷ ("\\B_SIGNED" , 0)
          ∷ ("\\B_WIDTH"  , 1)
          ∷ ("\\Y_WIDTH"  , 2)
          ∷ []
        ; connections =
            "\\A" ⇐ "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y"
          ∷ "\\B" ⇐ "\\ci"
          ∷ "\\Y" ⇐ "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y"
          ∷ []
        }
    ∷ []
  }
  ∷ []

main : Main
main = run $ do
  putStrLn $ Doc.render {ann = 𝟙.0ℓ.⊤} $ Doc.pPrint dut
