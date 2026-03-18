{-# OPTIONS --safe --cubical-compatible #-}
module Cheshire.Instance.Words where

open import Cheshire.Core

-- stdlib
import Data.Nat as ℕ renaming (ℕ to t)
import Data.Nat.Properties as ℕₚ
import Data.Product as Product
import Function.Properties.Inverse as Inverseₚ

-- cheshire
import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
import RTLIL.Word.Properties as Wordsₚ

open Product using (proj₁; proj₂; uncurry)
open Function using (_∘₂_) renaming (_∘_ to _⊙_)
open Inverseₚ using (↔⇒↣)
open Rel₂ using (_≗_)

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

  -- terminal : Terminal
  -- terminal = record { ⊤ = 0 }

  -- products : BinaryProducts
  -- products = record { _×_ = ℕ._+_ }

  -- coproducts : BinaryCoproducts
  -- coproducts = record { _⊎_ = ℕ.suc ∘₂ ℕ._⊔_ }

module Signatures where

  category : Category.Signature 𝒬
  category = record
    { id = Function.id
    ; _∘_ = Function._∘′_
    }

  cartesian : Cartesian.Signature category
  cartesian = record
    { terminal = record { ⊤ = 0 }
    ; ! = Function.const (Word.zero 0)
    ; products = record { _×_ = ℕ._+_ }
    ; π₁ = λ {M} {N} → proj₁ ⊙ Word.remQuot N
    ; π₂ = λ {M} {N} → proj₂ ⊙ Word.remQuot N
    ; ⟨_,_⟩ = λ f g → uncurry Word.combine ⊙ Product.< f , g >
    }

module Structures where
  category : Category.Structure eq Signatures.category
  category = record
    { assoc = λ _ → Rel₂.refl
    ; identityˡ = λ _ → Rel₂.refl
    ; identityʳ = λ _ → Rel₂.refl
    ; ∘-resp-≈ = λ {_ _ _ f h g i} f≗h g≗i x → Rel₂.trans (f≗h (g x)) (Rel₂.cong h (g≗i x))
    }

  cartesian : Cartesian.Structure category Signatures.cartesian
  cartesian = record
    { !-unique = λ _ _ → injective Rel₂.refl
    ; project₁ = λ { {h = h} {i} x → Rel₂.cong proj₁ (Wordsₚ.remQuot-combine (h x) (i x)) }
    ; project₂ = λ { {h = h} {i} x → Rel₂.cong proj₂ (Wordsₚ.remQuot-combine (h x) (i x)) }
    ; unique = uniq
    } where
      open Rel₂.≡-Reasoning -- ℕₚ.≤-Reasoning
      open Function.Inverse (Wordsₚ.0↔⊤ {𝕃.0ℓ})
      open Function.Injection (↔⇒↣ (Wordsₚ.0↔⊤ {𝕃.0ℓ}))
      uniq :
        ∀ {o m n} {h : Word.t o → Word.t (m ℕ.+ n)}
        {i : Word.t o → Word.t m} {j : Word.t o → Word.t n} →
        proj₁ ⊙ Word.remQuot n ⊙ h ≗ i →
        proj₂ ⊙ Word.remQuot n ⊙ h ≗ j →
        uncurry Word.combine ⊙ Product.< i , j > ≗ h
      uniq {_} {_} {n} {h} {i} {j} h≗i h≗j w =
        begin
          Word.combine (i w) (j w)
        ≡⟨ Rel₂.cong₂ Word.combine (h≗i w) (h≗j w) ⟨
          Word.combine (proj₁ (Word.remQuot n (h w))) (proj₂ (Word.remQuot n (h w)))
        ≡⟨ Wordsₚ.combine-remQuot n (h w) ⟩
          h w
        ∎

category : Category.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
category = record
  { 𝒬 = 𝒬
  ; category = Signatures.category
  ; isCategory = Structures.category
  }

cartesian : Cartesian.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
cartesian = record
  { Category.t category
  ; cartesian = Signatures.cartesian
  ; isCartesian = Structures.cartesian
  }
