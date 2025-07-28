{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Signal where

open import RTLIL.Syntax.Base
open import Agda.Builtin.FromString using (IsString)

data Selection : Set where
  All    :             Selection
  Single : ℕ.t       → Selection
  Range  : ℕ.t → ℕ.t → Selection

-- | SigSpec in the spec
data Signal : Set where
  const  : Constant               → Signal
  refer  : Identifier → Selection → Signal
  concat : NonEmpty.t Signal      → Signal

instance
  IsStringSignal : IsString Signal
  IsStringSignal .IsString.Constraint _ = 𝟙.0ℓ.⊤
  IsStringSignal .IsString.fromString s =
    refer (IsString.fromString IsStringIdentifier s) All
