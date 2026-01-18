{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Base where

open import Overture
open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromString using (IsString)

import Data.Refinement as Refinement renaming (Refinement to t)
import Data.Irrelevant as Irrelevant renaming (Irrelevant to t)
import Relation.Binary.Construct.On as On

open × using (_×_)
open Char using (_≟_)
open Function using (_∘_)
open IsString String.isString
open String renaming (_<_ to _<ₛ_; _≈_ to _≈ₛ_) using ()
open Rel₀ using (yes; no)
open Refinement using (Refinement-syntax; _,_)

data Identifier : Set where
  pub auto : String.t → Identifier

toString : Identifier → String.t
toString (pub  id) = "\\" String.++ id
toString (auto id) = "$"  String.++ id

getString : Identifier → String.t
getString (pub  id) = id
getString (auto id) = id

withString : Identifier → (String.t → String.t) → Identifier
withString (pub  id) f = pub  (f id)
withString (auto id) f = auto (f id)

instance
  IsStringIdentifier : IsString Identifier
  IsStringIdentifier .IsString.Constraint _ = 𝟙*.t
    -- 0 ℕ.< String.length a
  IsStringIdentifier .IsString.fromString s with String.uncons s
  … | Maybe.just (head , rest) with head ≟ '$'
  …   | yes _ = auto rest
  …   | no  _ with head ≟ '\\'
  …              | yes _ = pub rest
  …              | no  _ = pub s
    -- error out?
  IsStringIdentifier .IsString.fromString s | Maybe.nothing = pub s

identifier-setoid : Rel₂.Setoid 𝕃.0ℓ 𝕃.0ℓ
identifier-setoid = On.setoid String.≈-setoid toString

identifier-decSetoid : Rel₂.DecSetoid 𝕃.0ℓ 𝕃.0ℓ
identifier-decSetoid = On.decSetoid String.≈-decSetoid toString

<-strictTotalOrder-≈ : Rel₂.StrictTotalOrder _ _ _
<-strictTotalOrder-≈ =
    On.strictTotalOrder String.<-strictTotalOrder-≈ toString

module Map where
  open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as Map renaming (Map to t) public

  values : ∀ {v} {V : Set v} → Map.Map V → List.t V
  values = List.map proj₂ ∘ Map.toList

Width : Set
Width = [ value ∈ ℕ.t ∣ ℕ.NonZero value ]

open Refinement using (value; proof; _,_) public
open Irrelevant using ([_]) public

instance
  NumberWidth : Number Width
  NumberWidth .Number.Constraint w = ℕ.NonZero w
  NumberWidth .Number.fromNat w ⦃ w≢0 ⦄ = w , Irrelevant.[ w≢0 ]

module Constant where
  -- This can have all the verilog contsant expression, but I think in
  -- practice it's a string or a number.
  data t : Set where
    string : String.t → t
    signed : ℤ.t      → t
    -- real   : ?
    -- in rtlil spec this would be regular int, but I want to be more
    -- precise here
    width : Width     → t

  instance
    IsStringConstant : IsString t
    IsStringConstant .IsString.Constraint _ = 𝟙*.t
    IsStringConstant .IsString.fromString s = string s

    NumberConstant : Number t
    NumberConstant .Number.Constraint _ = 𝟙*.t
    NumberConstant .Number.fromNat n = signed (ℤ.+ n)

record Has {ℓ c} (C : Set c) (A : Set ℓ) : Set (ℓ 𝕃.⊔ c) where
  field
    get : A → C
    set : C → A → A

open Has ⦃ … ⦄ public
