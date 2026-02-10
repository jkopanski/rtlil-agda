{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Signal where

open import Overture
open import RTLIL.Syntax.Base
open import Agda.Builtin.FromString using (IsString)

import RTLIL.Syntax.Wire as Wire renaming (Wire to t)

data Selection : Set where
  All    :                           Selection
  Single : Constant.t              → Selection
  Range  : Constant.t → Constant.t → Selection

[_⋯_] : Constant.t → Constant.t → Selection
[_⋯_] = Range

-- | SigSpec in the spec
data Signal : Set where
  const  : Constant.t         → Signal
  simple : Identifier         → Signal
  refer  : Signal → Selection → Signal
  concat : NonEmpty.t Signal  → Signal

prod : Signal → Signal → Signal
prod a b = concat (a ∷⁺ NonEmpty.[ b ])
  where open NonEmpty using (_∷⁺_)

wire : Wire.t → Signal
wire wire = simple (wire .Wire.t.name)

identifier : Signal → Maybe.t Identifier
identifier (const _)   = Maybe.nothing
identifier (simple id) = Maybe.just id
identifier (refer s _) = identifier s
identifier (concat _)  = Maybe.nothing

instance
  IsStringSignal : IsString Signal
  IsStringSignal .IsString.Constraint _ = 𝟙*.t
  IsStringSignal .IsString.fromString s =
    simple (IsString.fromString IsStringIdentifier s)
