{-# OPTIONS --safe --cubical-compatible #-}
module Cheshire.Instance.Words where

open import Cheshire.Core

-- stdlib
import Data.Nat as ℕ renaming (ℕ to t)
import Data.Nat.Properties as ℕₚ
import Data.Product as Product
import Function.Properties.Inverse as Inverseₚ

-- cheshire
import Cheshire.Object.Signatures as Object
import Cheshire.Signatures as Signatures
import Cheshire.Structures as Structures

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
import RTLIL.Word.Properties as Wordsₚ

open Product using (proj₁; proj₂; uncurry)
open Function using (_∘₂_) renaming (_∘_ to _⊙_)
open Inverseₚ using (↔⇒↣)
open Rel₂ using (_≗_)
open Signatures
open Structures

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

Words : Cartesian 𝒬
Words = record
  { id = Function.id
  ; _∘_ = Function._∘′_
  ; terminal = record { ⊤ = 0 }
  ; ! = Function.const (Word.zero 0)
  ; products = record { _×_ = ℕ._+_ }
  ; π₁ = λ {M} {N} → proj₁ ⊙ Word.remQuot N
  ; π₂ = λ {M} {N} → proj₂ ⊙ Word.remQuot N
  ; ⟨_,_⟩ = λ f g → uncurry Word.combine ⊙ Product.< f , g >
  }
open Cartesian Words public

isCartesian : IsCartesian 𝕃.0ℓ Words
isCartesian = record
  { eq = eq
  ; !-unique = λ _ _ → injective Rel₂.refl
  ; project₁ = λ { {h = h} {i} x → Rel₂.cong proj₁ (Wordsₚ.remQuot-combine (h x) (i x)) }
  ; project₂ = λ { {h = h} {i} x → Rel₂.cong proj₂ (Wordsₚ.remQuot-combine (h x) (i x)) }
  ; unique = uniq
  -- Category
  ; assoc = λ _ → Rel₂.refl
  ; identityˡ = λ _ → Rel₂.refl
  ; identityʳ = λ _ → Rel₂.refl
  ; ∘-resp-≈ = λ {_ _ _ f h g i} f≗h g≗i x → Rel₂.trans (f≗h (g x)) (Rel₂.cong h (g≗i x))
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
