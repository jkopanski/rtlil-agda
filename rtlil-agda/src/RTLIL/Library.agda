{-# OPTIONS --safe #-}
open import Prelude

module RTLIL.Library where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromString

open import RTLIL.Syntax

open List using (_∷_; [])

instance  _ = ℕ.number

module Unsigned (w′ : ℕ.t) .⦃ w≢0 : ℕ.NonZero w′ ⦄ where
  w : Constant
  w = signed (ℤ.+ w′)
  w+1 : Constant
  w+1 = signed (ℤ.+ (ℕ.suc w′))

  w-width : Width
  w-width = w′ , [ w≢0 ]

  w+1-width : Width
  w+1-width = ℕ.suc w′ , [ _ ]

------------------------------------------------------------------------
-- $add
-- https://yosyshq.readthedocs.io/projects/yosys/en/latest/cell/word_binary.html#binary.$add

  add : Module.t
  add = record
    { name = "$RTLIL$Library$Unsigned$add"
    ; attributes = Attributes.empty
    ; parameters = Parameters.empty
    ; connections = []
    ; wires =
        Wire.iobus "\\M" w-width (Wire.input 1)
      ∷ Wire.iobus "\\N" w-width (Wire.input 2)
      ∷ Wire.iobus "\\OUT" w+1-width (Wire.output 3)
      ∷ []
    ; cells =
        record
         { attributes = Attributes.empty
         ; type = "$add"
         ; name = "$internal$unsigned$add"
         ; parameters = Parameters.mk
           $ ("\\A_SIGNED" , 0)
           ∷ ("\\A_WIDTH"  , w)
           ∷ ("\\B_SIGNED" , 0)
           ∷ ("\\B_WIDTH"  , w)
           ∷ ("\\Y_WIDTH"  , w+1)
           ∷ []
         ; connections =
             "\\A" ⇐ "\\M"
           ∷ "\\B" ⇐ "\\N"
           ∷ "\\Y" ⇐ "\\OUT"
           ∷ []
         }
      ∷ []
    }
