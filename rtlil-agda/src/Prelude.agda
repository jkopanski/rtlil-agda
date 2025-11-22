{-# OPTIONS --safe --cubical-compatible #-}

module Prelude where

module 𝕃 where
  open import Level renaming (Level to t) public

module 𝟘 where open import Data.Empty renaming (⊥    to t)

module 𝟙 where
  open import Data.Unit.Polymorphic renaming (⊤ to t; tt to tt-lift) public
  open import Data.Unit renaming (tt to tt*)
  pattern tt = 𝕃.lift tt*
  open import Data.Unit.Polymorphic.Properties public

module 𝟙* where
  open import Data.Unit renaming (⊤ to t) public

module Rel₀ where
  open import Relation.Nullary public
  open import Relation.Nullary.Decidable public

module Rel₁ where
  open import Relation.Unary hiding (∅; U) public
  open import Relation.Unary.Polymorphic public

module Rel₂ where
  open import Relation.Binary public
  open import Relation.Binary.PropositionalEquality public

open Rel₀ using (¬_) public
open Rel₁ using (Universal; IUniversal) public
open Rel₂ using (_≡_; _≢_; Rel; cong; refl; trans; sym) public

module 𝟚 where open import Data.Bool renaming (Bool to t) public

module × where
  open import Data.Product            public
  open import Data.Product.Properties public

module ⊎ where
  open import Data.Sum            public
  open import Data.Sum.Properties public

module ℕ where
  open import Data.Nat renaming (ℕ to t) public
  open import Data.Nat.Properties        public
  open import Data.Nat.Divisibility      public
  open import Data.Nat.DivMod            public
  open import Data.Nat.Literals          public
  open import Data.Irrelevant
  open ≤-Reasoning
  open Rel₀ using (no; yes)

  -- TODO: Upstream to stdlib?
  m∸[n∸o]≡m∸n+o : ∀ {m n o} → n ≤ m → o ≤ n → m ∸ (n ∸ o) ≡ m ∸ n + o
  m∸[n∸o]≡m∸n+o {zero}    {zero}    {zero} m≥n n≥o = refl
  m∸[n∸o]≡m∸n+o {suc m}   {zero}    {zero} m≥n n≥o
    rewrite +-identityʳ m = refl
  m∸[n∸o]≡m∸n+o m@{suc _} n@{suc _} {zero} m≥n n≥o
    rewrite +-identityʳ (m ∸ n) = refl
  m∸[n∸o]≡m∸n+o {suc m} {suc n} {suc o} (s≤s m≥n) (s≤s n≥o)
    rewrite +-suc (m ∸ n) o
          | +-∸-assoc 1 (≤-trans (m∸n≤m n o) m≥n)
          = cong suc (m∸[n∸o]≡m∸n+o m≥n n≥o)

  m⊔n≡m∸n+n : ∀ m n → m ⊔ n ≡ m ∸ n + n
  m⊔n≡m∸n+n m n with m ≤? n
  … | yes m≤n = begin-equality
    m ⊔ n     ≡⟨ m≤n⇒m⊔n≡n m≤n ⟩
    n         ≡⟨ +-identityˡ n ⟨
    0 + n     ≡⟨ cong (_+ n) (m≤n⇒m∸n≡0 m≤n) ⟨
    m ∸ n + n ∎
  … | no  m≰n = begin-equality
    m ⊔ n     ≡⟨ m≥n⇒m⊔n≡m (≰⇒≥ m≰n) ⟩
    m         ≡⟨ m∸n+n≡m (≰⇒≥ m≰n) ⟨
    m ∸ n + n ∎

  m⊔n∸[m∸n]≡n : ∀ m n → m ⊔ n ∸ (m ∸ n) ≡ n
  m⊔n∸[m∸n]≡n m n with m ≤? n
  … | yes m≤n rewrite m≤n⇒m⊔n≡n m≤n | m≤n⇒m∸n≡0 m≤n = refl
  … | no  m≰n rewrite m≥n⇒m⊔n≡m (≰⇒≥ m≰n) = m∸[m∸n]≡n (≰⇒≥ m≰n)

  m⊔n∸∣m-n∣≡m⊓n : ∀ m n → m ⊔ n ∸ ∣ m - n ∣ ≡ m ⊓ n
  m⊔n∸∣m-n∣≡m⊓n m n with m ≤? n
  … | yes m≤n
    rewrite m≤n⇒m⊔n≡n m≤n
          | m≤n⇒m⊓n≡m m≤n
          | m≤n⇒∣m-n∣≡n∸m m≤n
          = m∸[m∸n]≡n m≤n
  … | no m≰n
    rewrite m≥n⇒m⊔n≡m (≰⇒≥ m≰n)
          | m≥n⇒m⊓n≡n (≰⇒≥ m≰n)
          | m≤n⇒∣n-m∣≡n∸m (≰⇒≥ m≰n)
          = m∸[m∸n]≡n (≰⇒≥ m≰n)

  m⊔n∸m⊓n≡∣m-n∣ : ∀ m n → m ⊔ n ∸ m ⊓ n ≡ ∣ m - n ∣
  m⊔n∸m⊓n≡∣m-n∣ m n with m ≤? n
  … | yes m≤n
    rewrite m≤n⇒m⊔n≡n m≤n
          | m≤n⇒m⊓n≡m m≤n
          | m≤n⇒∣m-n∣≡n∸m m≤n
          = refl
  … | no  m≰n
    rewrite m≥n⇒m⊔n≡m (≰⇒≥ m≰n)
          | m≥n⇒m⊓n≡n (≰⇒≥ m≰n)
          | m≤n⇒∣n-m∣≡n∸m (≰⇒≥ m≰n)
          = refl

  m⊔n≡n∸m+m : ∀ m n → m ⊔ n ≡ n ∸ m + m
  m⊔n≡n∸m+m m n = trans (⊔-comm m n) (m⊔n≡m∸n+n n m)

  n⊔m∸[m∸n]≡n : ∀ m n → n ⊔ m ∸ (m ∸ n) ≡ n
  n⊔m∸[m∸n]≡n m n = begin-equality
    n ⊔ m ∸ (m ∸ n) ≡⟨ cong (_∸ (m ∸ n)) (⊔-comm n m) ⟩
    m ⊔ n ∸ (m ∸ n) ≡⟨ m⊔n∸[m∸n]≡n m n ⟩
    n ∎

  ∣m-n∣+m⊓n≡m⊔n : ∀ m n → ∣ m - n ∣ + m ⊓ n ≡ m ⊔ n
  ∣m-n∣+m⊓n≡m⊔n m n with m ≤? n
  … | yes m≤n
    rewrite m≤n⇒m⊔n≡n m≤n
          | m≤n⇒m⊓n≡m m≤n
          | m≤n⇒∣m-n∣≡n∸m m≤n
          = m∸n+n≡m m≤n
  … | no  m≰n
    rewrite m≥n⇒m⊔n≡m (≰⇒≥ m≰n)
          | m≥n⇒m⊓n≡n (≰⇒≥ m≰n)
          | m≤n⇒∣n-m∣≡n∸m (≰⇒≥ m≰n)
          = m∸n+n≡m (≰⇒≥ m≰n)

module Fin where
  open import Data.Fin renaming (Fin to t) public
  open import Data.Fin.Properties          public

module ℤ where
  open import Data.Integer renaming (ℤ to t) public
  open import Data.Integer.Properties        public

module Char where
  open import Data.Char renaming (Char to t) public
  open import Data.Char.Properties           public

module String where
  open import Data.String renaming (String to t) public
  open import Data.String.Properties public
  open import Data.String.Literals public

module Maybe where
  open import Data.Maybe renaming (Maybe to t) public

module List where
  open import Data.List renaming (List to t) public
  open import Data.List.Properties           public

module NonEmpty where
  open import Data.List.NonEmpty renaming (List⁺ to t) public
  open import Data.List.NonEmpty.Properties            public

module Vec where
  open import Data.Vec renaming (Vec to t) public

module Function where
  open import Function public

open × using (Σ; ∃; ∃-syntax; _,_; proj₁; proj₂) public
open ⊎ using (_⊎_; inj₁; inj₂) public
open Function using (_∘_; _$_; _on_; case_of_; case_returning_of_) public

module Setoid where
  open import Relation.Binary.Bundles using () renaming (Setoid to t) public
  import Relation.Binary.Reasoning.Setoid as SetoidR
  module Reasoning {s₁ s₂} (S : t s₁ s₂) = SetoidR S

module Func where
  open import Function.Bundles renaming (Func to t) public
  open import Function.Relation.Binary.Setoid.Equality public

open Func using (_⟨$⟩_; _⟶ₛ_; _⇨_) public
