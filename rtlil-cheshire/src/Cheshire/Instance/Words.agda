{-# OPTIONS --safe --cubical-compatible #-}
module Cheshire.Instance.Words where

open import Overture
open import Cheshire.Core

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
import RTLIL.Word.Properties as Wordsₚ

open Object
open Homomorphism using (Morphism)
open Morphisms.Bundles Sets.category using (_≅_)

U : ℕ.t → Set 𝕃.0ℓ
U = Word.t

𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬 = Sub.𝒬 Sets.𝒬 U

instance
  terminal : Terminal (𝒬 .Ob)
  terminal = record { ⊤ = 0 }

  products : BinaryProducts (𝒬 .Ob)
  products = record { _×_ = ℕ._+_ }

⊤-iso : ⊤ ≅ U ⊤
⊤-iso = record
  { from = const (Word.zero 0)
  ; to = λ _ → 𝟙.tt
  ; isIso = record
    { isoˡ = λ _ → Rel₂.refl
    ; isoʳ = 0↔⊤.strictlyInverseʳ
    }
  } where module 0↔⊤ = Function.Inverse {b = 𝕃.0ℓ} Wordsₚ.0↔⊤

×-iso : ∀ A B → U A × U B ≅ U (A × B)
×-iso w u = record
  { from = ×.uncurry Word.combine
  ; to = Word.remQuot u
  ; isIso = record
    { isoˡ = +↔×.strictlyInverseˡ
    ; isoʳ = +↔×.strictlyInverseʳ
    }
  } where module +↔× = Function.Inverse (Wordsₚ.+↔× {w} {u})

Words : Cartesian.t 𝕃.zero 𝕃.0ℓ 𝕃.0ℓ
Words = Sub.Bundles.cartesian Sets.t U ⊤-iso ×-iso

H : Homomorphism.Cartesian′ Sets.eq (Cartesian.t.cartesian Words) Sets.cartesian
-- for some reason agda barfs at isIso when I pass ⊤-iso as an argument
H = Sub.Structures.cartesianFunctor Sets.𝒬 U Sets.cartesian Sets.is-cartesian (record { _≅_ ⊤-iso }) ×-iso

module H = Homomorphism.Cartesian′ H

module Signatures where

  category : Category.Signature 𝒬
  category = Cartesian.t.category Words

  cartesian : Cartesian.Signature category
  cartesian = Cartesian.t.cartesian Words

module Structures where

  instance
    eq : Equivalence 𝒬 𝕃.0ℓ
    eq = Cartesian.t.eq Words

  is-category : Category.Structure eq Signatures.category
  is-category = Cartesian.t.isCategory Words

  is-cartesian : Cartesian.Structure is-category Signatures.cartesian
  is-cartesian = Cartesian.t.isCartesian Words

module Bundles where

  category : Category.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
  category = record { Cartesian.t Words }

  cartesian : Cartesian.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
  cartesian = Words
