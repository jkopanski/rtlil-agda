{-# OPTIONS --safe --cubical-compatible #-}
module Cheshire.Instance.Bits where

open import Overture
open import Cheshire.Core

-- stdlib
import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
open import Data.Vec.Recursive.Properties.Extra

-- cheshire
import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object
import Cheshire.Homomorphism as Homomorphism
import Cheshire.Construction.Sub.Object as Sub
import Cheshire.Instance.Sets 𝕃.0ℓ as Sets renaming (Sets to t)
import Cheshire.Morphism as Morphisms

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
import RTLIL.Word.Bits as Bits renaming (Bits to t)
import RTLIL.Word.Properties as Wordsₚ

open Pointwise using (≡×≡⇒≡; ≡⇒≡×≡)
open Object
open Homomorphism using (Morphism)
open Morphisms.Bundles Sets.category using (_≅_)

U : ℕ.t → Set 𝕃.0ℓ
U = Vec.Rec.t 𝟚.t

𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬 = Sub.𝒬 Sets.𝒬 U

instance
  terminal : Terminal (𝒬 .Ob)
  terminal .Terminal.⊤ = 0

  products : BinaryProducts (𝒬 .Ob)
  products .BinaryProducts._×_ = ℕ._+_

H : Morphism 𝒬 Sets.𝒬
H = Sub.H Sets.𝒬 U

tH : Homomorphism.Terminal H
tH .Homomorphism.Terminal.⊤-iso = record
  { from = λ where 𝟙.tt → 𝟙.tt
  ; to = λ where 𝟙.tt → 𝟙.tt
  }

pH : Homomorphism.BinaryProducts H
pH .Homomorphism.BinaryProducts.×-iso w u = record
  { from = ×.uncurry (Vec.Rec.append w u)
  ; to = Vec.Rec.splitAt w u
  }

⊤-iso : ⊤ ≅ U ⊤
⊤-iso = record
  { Homomorphism.Terminal.⊤-iso tH
  ; isIso = record
    { isoˡ = λ _ → ≡-refl
    ; isoʳ = λ _ → ≡-refl
    }
  }

×-iso : ∀ A B → U A × U B ≅ U (A × B)
×-iso w u = record
  { Homomorphism.BinaryProducts.×-iso pH
  ; isIso = record
    { isoˡ = ×.uncurry (Vec.Rec.splitAt-append-identity w u)
    ; isoʳ = Vec.Rec.append-splitAt-identity w u
    }
  }

-- We can project everything from this, but perhaps it is convenient to define everything?
Bits : Cartesian.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
Bits = Sub.Bundles.cartesian Sets.t U ⊤-iso ×-iso

module Signatures where

  category : Category.Signature 𝒬
  category = Cartesian.t.category Bits

  cartesian : Cartesian.Signature category
  cartesian = Cartesian.t.cartesian Bits

module Structures where

  instance
    eq : Equivalence 𝒬 𝕃.0ℓ
    eq = Cartesian.t.eq Bits

  is-category : Category.Structure eq Signatures.category
  is-category = Cartesian.t.isCategory Bits

  is-cartesian : Cartesian.Structure is-category Signatures.cartesian
  is-cartesian = Cartesian.t.isCartesian Bits

module Bundles where

  category : Category.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
  category = record { Cartesian.t Bits }

  cartesian : Cartesian.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
  cartesian = Bits
