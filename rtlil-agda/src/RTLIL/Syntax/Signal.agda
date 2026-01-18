{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Signal where

open import Overture
open import RTLIL.Syntax.Base
open import Agda.Builtin.FromString using (IsString)

import RTLIL.Syntax.Wire as Wire renaming (Wire to t)

data Selection : Set where
  All    :             Selection
  Single : ℕ.t       → Selection
  Range  : ℕ.t → ℕ.t → Selection

[_,_] : ℕ.t → ℕ.t → Selection
[_,_] = Range

-- | SigSpec in the spec
data Signal : Set where
  const  : Constant.t             → Signal
  refer  : Identifier → Selection → Signal
  concat : NonEmpty.t Signal      → Signal

prod : Signal → Signal → Signal
prod a b = concat (a ∷⁺ NonEmpty.[ b ])
  where open NonEmpty using (_∷⁺_)

simple : Identifier → Signal
simple id = refer id All

wire : Wire.t → Signal
wire wire = simple (wire .Wire.t.name)

instance
  IsStringSignal : IsString Signal
  IsStringSignal .IsString.Constraint _ = 𝟙*.t
  IsStringSignal .IsString.fromString s =
    refer (IsString.fromString IsStringIdentifier s) All
