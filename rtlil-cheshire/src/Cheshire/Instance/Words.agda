{-# OPTIONS --safe --cubical-compatible #-}
open import Cheshire.Core

module Cheshire.Instance.Words where

-- stdlib
import Data.Nat as ℕ renaming (ℕ to t)
import Data.Product as Product

-- cheshire
import Cheshire.Object.Signatures as Object
import Cheshire.Signatures as Signatures

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)

open Product using (proj₁; proj₂; uncurry)
open Function using (_⊙_; _∘₂_)
open Signatures

𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬 = mk⇒ {Ob = ℕ.t} λ u v → Word.t u → Word.t v
open Object (𝒬 .Ob)

instance
  eq : Equivalence 𝒬 𝕃.0ℓ
  eq = record
    { _≈_ = Rel₂._≗_
    ; equiv = record
      { refl = λ _ → Rel₂.refl
      ; trans = λ eq₁ eq₂ x → Rel₂.trans (eq₁ x) (eq₂ x)
      ; sym = λ eq x → Rel₂.sym (eq x)
      }
    }

terminal : Terminal
terminal = record { ⊤ = 0 }

products : BinaryProducts
products = record { _×_ = ℕ._+_ }

coproducts : BinaryCoproducts
coproducts = record { _⊎_ = ℕ.suc ∘₂ ℕ._⊔_ }

Words : Cartesian 𝒬
Words = record
  { id = Function.id
  ; _∘_ = Function._∘′_
  ; terminal = terminal
  ; ! = Function.const (0 Word.#b 0)
  ; products = products
  ; π₁ = λ {M} {N} → proj₁ ⊙ Word.remQuot N
  ; π₂ = λ {M} {N} → proj₂ ⊙ Word.remQuot N
  ; ⟨_,_⟩ = λ f g → uncurry Word.combine ⊙ Product.< f , g >
  }
