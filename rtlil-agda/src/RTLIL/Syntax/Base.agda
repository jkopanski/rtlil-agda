{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Base where

import Relation.Binary.Construct.On as On

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromString using (IsString)

open × using (_×_)
open String renaming (_<_ to _<ₛ_; _≈_ to _≈ₛ_) using ()
open Rel₀ using (yes; no)
open Char using (_≟_)
open IsString String.isString

data Identifier : Set where
  pub auto : String.t → Identifier

toString : Identifier → String.t
toString (pub  id) = "\\" String.++ id
toString (auto id) = "$"  String.++ id

instance
  IsStringIdentifier : IsString Identifier
  IsStringIdentifier .IsString.Constraint _ = 𝟙.0ℓ.⊤
    -- 0 ℕ.< String.length a
  IsStringIdentifier .IsString.fromString s with String.uncons s
  … | Maybe.just (head , rest) with head ≟ '$'
  …   | yes _ = auto rest
  …   | no  _ with head ≟ '\\'
  …              | yes _ = pub rest
  …              | no  _ = pub s
    -- error out?
  IsStringIdentifier .IsString.fromString s | Maybe.nothing = pub s

_≈_ : Rel Identifier 𝕃.0ℓ
_≈_ = _≈ₛ_ on toString

≈-isEquivalence : Rel₂.IsEquivalence (_≈ₛ_ on toString)
≈-isEquivalence = On.isEquivalence toString String.≈-isEquivalence

<-strictTotalOrder-≈ : Rel₂.StrictTotalOrder _ _ _
<-strictTotalOrder-≈ =
    On.strictTotalOrder String.<-strictTotalOrder-≈ toString

module Map where
  open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as Map renaming (Map to t) public

-- This can have all the verilog contsant expression, but I think in
-- practice it's a string or a number.
data Constant : Set where
  string : String.t → Constant
  signed : ℤ.t      → Constant
  -- real   : ?

instance
  IsStringConstant : IsString Constant
  IsStringConstant .IsString.Constraint _ = 𝟙.0ℓ.⊤
  IsStringConstant .IsString.fromString s = string s

  NumberConstant : Number Constant
  NumberConstant .Number.Constraint _ = 𝟙.0ℓ.⊤
  NumberConstant .Number.fromNat n = signed (ℤ.+ n)

record Width : Set where
  field
    width : ℕ.t
    .⦃ width≢0 ⦄ : ℕ.NonZero width

instance
  NumberWidth : Number Width
  NumberWidth .Number.Constraint w = ℕ.NonZero w
  NumberWidth .Number.fromNat w = record { width = w }

record Has {ℓ c} (C : Set c) (A : Set ℓ) : Set (ℓ 𝕃.⊔ c) where
  field
    get : A → C
    set : C → A → A

open Has ⦃ … ⦄ public
