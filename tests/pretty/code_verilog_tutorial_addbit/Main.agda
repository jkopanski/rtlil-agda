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
  ; wires = Map.fromList
    $ let n = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
           )
           (Wire.bus n 2)
         )
    ∷ let n = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y"
      in ( n
          , Attributes.insert
            ( "\\src"
            , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
            )
            (Wire.bus n 2)
          )
    ∷ let n = "\\a"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:9.7-9.8"
           )
           (Wire.iowire n (Wire.input 1))
         )
    ∷ let n = "\\b"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:10.7-10.8"
           )
           (Wire.iowire n (Wire.input 2))
         )
    ∷ let n = "\\ci"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:11.7-11.9"
           )
           (Wire.iowire n (Wire.input 3))
         )
    ∷ let n = "\\co"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:14.8-14.10"
           )
           (Wire.iowire n (Wire.output 5))
         )
    ∷ let n = "\\sum"
      in ( n
         , Attributes.insert
           ( "\\src"
           , "asicworld/verilog/code_verilog_tutorial_addbit.v:13.8-13.11"
           )
           (Wire.iowire n (Wire.output 4))
         )
    ∷ []
  ; cells = Map.fromList
    $ let n = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1"
      in ( n
         , record
           { attributes = Attributes.mk $
             ( "\\src"
             , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
             ) ∷ []
           ; type = "$add"
           ; name = n
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
         )
    ∷ let n = "$add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2"
      in ( n
         , record
           { attributes = Attributes.mk $
             ( "\\src"
             , "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
             ) ∷ []
           ; type = "$add"
           ; name = n
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
         )
    ∷ []
  }
  ∷ []

main : Main
main = run $ do
  putStrLn $ Doc.render {ann = 𝟙.0ℓ.⊤} $ Doc.pPrint dut
