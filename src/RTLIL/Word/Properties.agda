{-# OPTIONS --safe #-}

-- A lot of this stuff came from James McKinna draft PR#2257 to add
-- Data.Nat.Bounded to agda-stdlib. See:
-- https://github.com/agda/agda-stdlib/pull/2257

open import Prelude

module RTLIL.Word.Properties where

import RTLIL.Word.Width as Width

open import RTLIL.Word.Base
open import Function.Consequences.Propositional
  using (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ; strictlyInverseʳ⇒inverseʳ)
open import Tactic.Cong using (cong!; ⌞_⌟)

open Func using (_↔_; _⤖_)
open ℕ hiding (zero; t; _+_; _≟_)
open Width
open Rel₀ using (no; yes)
open Rel₂ using (_≗_; _⇒_)

toℕ-cong : ∀ {w} → Function.Congruent _≡_ _≡_ (toℕ {w})
toℕ-cong = cong toℕ

toℕ-injective : ∀ {w} → Function.Injective _≡_ _≡_ (toℕ {w})
toℕ-injective refl = refl

infix 4 _≟_
_≟_ : ∀ {w} → Rel₂.DecidableEquality (Word w)
i ≟ j = Rel₀.map′ toℕ-injective toℕ-cong (toℕ i ℕ.≟ toℕ j)

------------------------------------------------------------------------
-- Bundles

toFin∘fromFin≐id : ∀ {w : ℕ.t} → toFin {w} ∘ fromFin ≗ Function.id
toFin∘fromFin≐id {w} i = Fin.fromℕ<-toℕ i (Fin.toℕ<n i)

fromFin∘toFin≐id : ∀ {w : ℕ.t} → fromFin ∘ toFin {w} ≗ Function.id
fromFin∘toFin≐id (⟦ value ⟧< value<⊤) = toℕ-injective (Fin.toℕ-fromℕ< (⊤⇒2ʷ ≤-isPreorder value<⊤))

Word⤖Fin : ∀ {w} → Word w ⤖ Fin.t (2 ^ w)
Word⤖Fin {w} = Func.mk⤖ $ inverseᵇ⇒bijective
  $ strictlyInverseˡ⇒inverseˡ {f⁻¹ = fromFin} toFin (toFin∘fromFin≐id {w})
  , strictlyInverseʳ⇒inverseʳ {f⁻¹ = fromFin} toFin fromFin∘toFin≐id

Word↔Fin : ∀ {w} → Word w ↔ Fin.t (2 ^ w)
Word↔Fin {w} = Func.mk↔ₛ′ toFin fromFin (toFin∘fromFin≐id {w}) fromFin∘toFin≐id

toℕ-#b :
  ∀ {w m} {witness : Rel₀.True (m <? 2 ^ w)} →
  toℕ (_#b_ w m {witness}) ≡ m
toℕ-#b {w} {m} {witness} rewrite sym (⊤-def w) = refl

toℕ-0-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (0-extend v word) ≡ toℕ word
toℕ-0-extend _ _ = refl

toℕ-1-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (1-extend v word) ≡ (⊤ v ∸ 1) * ⊤ w ℕ.+ toℕ word
toℕ-1-extend v {w} (⟦ value ⟧< value<⊤) = refl

toℕ-1-extend′ :
  ∀ {w} → (word : Word w) →
  toℕ (1-extend 1 word) ≡ ⊤ w ℕ.+ toℕ word
toℕ-1-extend′ {w} word = begin
  (⊤ 1 ∸ 1) * ⊤ w ℕ.+ toℕ word ≡⟨ cong! (⊤-def 1) ⟩
  (2 ∸ 1) * ⊤ w ℕ.+ toℕ word   ≡⟨ refl ⟩
  1 * ⊤ w ℕ.+ toℕ word         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  ⊤ w ℕ.+ toℕ word             ∎
  where open Rel₂.≡-Reasoning

split-0-extend :
  ∀ {w} → (word : Word w) →
  split (0-extend 1 word) ≡ inj₁ word
split-0-extend {w} word with (toℕ word) <? ⊤ w
… | yes v<⊤ = refl
… | no  v≮⊤ = Rel₀.contradiction (toℕ<⊤ word) v≮⊤

split-1-extend :
  ∀ {w} → (word : Word w) →
  split (1-extend 1 word) ≡ inj₂ word
split-1-extend {w} word
  with ex@(⟦ value ⟧< ex<⊤[1+w]) ← 1-extend 1 word
     | (⊤ 1 ∸ 1) * ⊤ w ℕ.+ toℕ word <? ⊤ w
… | yes v<⊤ = Rel₀.contradiction v<⊤ v≮⊤
  where v≮⊤ : (⊤ 1 ∸ 1) * ⊤ w ℕ.+ toℕ word ≮ ⊤ w
        v≮⊤ = ≤⇒≯ $ begin
          ⊤ w                   ≡⟨ +-identityʳ (⊤ w) ⟨
          ⊤ w ℕ.+ 0             ≤⟨ +-monoʳ-≤ (⊤ w) z≤n ⟩
          ⊤ w ℕ.+ toℕ word      ≡⟨ toℕ-1-extend′ word ⟨
          toℕ (1-extend 1 word) ∎
          where open ≤-Reasoning
… | no  v≮⊤ = cong inj₂ $ toℕ-injective $ begin
  toℕ (1-extend 1 word) ∸ ⊤ w ≡⟨ cong! (toℕ-1-extend′ word) ⟩
  ⊤ w ℕ.+ toℕ word ∸ ⊤ w      ≡⟨ m+n∸m≡n (⊤ w) (toℕ word) ⟩
  toℕ word                    ∎
  where open Rel₂.≡-Reasoning

split-join :
  ∀ {w} → (i : Word w ⊎ Word w) → split (join i) ≡ i
split-join (inj₁ i) = split-0-extend i
split-join (inj₂ i) = split-1-extend i

join-split : ∀ {w} → (i : Word (suc w)) → join (split i) ≡ i
join-split {w} i with toℕ i <? ⊤ w
… | yes _  = refl
… | no i≮⊤ = toℕ-injective $ begin
  (⊤ 1 ∸ 1) * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w) ≡⟨ cong! (⊤-def 1) ⟩
  (2 ∸ 1) * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)   ≡⟨ refl ⟩
  1 * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)             ≡⟨ m+[n∸m]≡n (≮⇒≥ i≮⊤) ⟩
  toℕ i ∎
  where open Rel₂.≡-Reasoning

opposite-involutive : ∀ {w} → (i : Word w) → opposite (opposite i) ≡ i
opposite-involutive {w} word@(⟦ i ⟧< _) = toℕ-injective $ begin
  ⊤ w ∸ suc (⊤ w ∸ suc i)   ≡⟨ cong (⊤ w ∸_) (+-∸-assoc 1 i<⊤) ⟨
  ⊤ w ∸ (suc (⊤ w) ∸ suc i) ≡⟨ refl ⟩
  ⊤ w ∸ (⊤ w ∸ i)           ≡⟨ m∸[m∸n]≡n (<⇒≤ i<⊤) ⟩
  i                         ∎
  where open Rel₂.≡-Reasoning
        i<⊤ = toℕ<⊤ word
