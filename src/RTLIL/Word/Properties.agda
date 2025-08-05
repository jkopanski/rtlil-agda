{-# OPTIONS --safe --cubical-compatible #-}

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
open × using (_×_)
open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- misc properties

w∸½<½ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) → toℕ word ≥ ⊤ (w ∸ 1) →
  toℕ word ∸ ⊤ (w ∸ 1) < ⊤ (w ∸ 1)
w∸½<½ w@{suc w-1} word v≥½ = begin-strict
  toℕ word ∸ ⊤ w-1 <⟨ ∸-monoˡ-< (toℕ<⊤ word) v≥½ ⟩
  ⊤ w ∸ ⊤ w-1      ≡⟨ ⊤∸⊤[w-1]≡⊤[w-1] w ⟩
  ⊤ w-1            ∎

------------------------------------------------------------------------
-- Properties of _#b_
------------------------------------------------------------------------

toℕ-#b :
  ∀ {w m} {witness : Rel₀.True (m <? 2 ^ w)} →
  toℕ (_#b_ w m {witness}) ≡ m
toℕ-#b {w} {m} {witness} rewrite sym (⊤-def w) = refl

------------------------------------------------------------------------
-- Properties of cast
------------------------------------------------------------------------

toℕ-cast :
  ∀ {w v} → .(eq : w ≡ v) → (word : Word w) →
  toℕ (cast eq word) ≡ toℕ word
toℕ-cast _ _ = refl

cast-irrelevant :
  ∀ {w v} → .(eq : w ≡ v) → (word : Word w) →
  cast eq word ≡ ⟦ toℕ word ⟧< <-≤-trans (toℕ<⊤ word) (≤-reflexive (cong ⊤ eq))
cast-irrelevant _ _ = refl

cast-is-id :
  ∀ {w} → .(eq : w ≡ w) → (word : Word w) →
  cast eq word ≡ word
cast-is-id _ _ = refl

subst-is-cast :
  ∀ {w v} → (eq : w ≡ v) (word : Word w) →
  Rel₂.subst Word eq word ≡ cast eq word
subst-is-cast refl _ = refl

------------------------------------------------------------------------
-- Properties of extend
------------------------------------------------------------------------

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
toℕ-1-extend′ {w} word = begin-equality
  (⊤ 1 ∸ 1) * ⊤ w ℕ.+ toℕ word ≡⟨ cong! (⊤-def 1) ⟩
  (2 ∸ 1) * ⊤ w ℕ.+ toℕ word   ≡⟨ refl ⟩
  1 * ⊤ w ℕ.+ toℕ word         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  ⊤ w ℕ.+ toℕ word             ∎

------------------------------------------------------------------------
-- Properties of split
------------------------------------------------------------------------

split-< :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) → (v<½ : toℕ word < ⊤ (w ∸ 1)) →
  split word ≡ inj₁ (⟦ toℕ word ⟧< v<½)
split-< {suc w-1} word v<½ with toℕ word <? ⊤ w-1
… | yes _   = refl
… | no  v≮½ = Rel₀.contradiction v<½ v≮½

split-≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) → (v≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
  split word ≡ inj₂ (⟦ toℕ word ∸ ⊤ (w ∸ 1) ⟧< w∸½<½ word v≥½)
split-≥ {suc w-1} word v≥½ with toℕ word <? ⊤ w-1
… | yes v<½ = Rel₀.contradiction v≥½ (<⇒≱ v<½)
… | no  v≮½ = refl

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
… | no  v≮⊤ = cong inj₂ $ toℕ-injective $ begin-equality
  toℕ (1-extend 1 word) ∸ ⊤ w ≡⟨ cong! (toℕ-1-extend′ word) ⟩
  ⊤ w ℕ.+ toℕ word ∸ ⊤ w      ≡⟨ m+n∸m≡n (⊤ w) (toℕ word) ⟩
  toℕ word                    ∎

split-join :
  ∀ {w} → (i : Word w ⊎ Word w) → split (join i) ≡ i
split-join (inj₁ i) = split-0-extend i
split-join (inj₂ i) = split-1-extend i

join-split : ∀ {w} → (i : Word (suc w)) → join (split i) ≡ i
join-split {w} i with toℕ i <? ⊤ w
… | yes _  = refl
… | no i≮⊤ = toℕ-injective $ begin-equality
  (⊤ 1 ∸ 1) * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w) ≡⟨ cong! (⊤-def 1) ⟩
  (2 ∸ 1) * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)   ≡⟨ refl ⟩
  1 * ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  ⊤ w ℕ.+ (toℕ i ∸ ⊤ w)             ≡⟨ m+[n∸m]≡n (≮⇒≥ i≮⊤) ⟩
  toℕ i ∎

------------------------------------------------------------------------
-- Properties of opposite
------------------------------------------------------------------------

opposite-involutive : ∀ {w} → (i : Word w) → opposite (opposite i) ≡ i
opposite-involutive {w} word@(⟦ i ⟧< _) = toℕ-injective $ begin-equality
  ⊤ w ∸ suc (⊤ w ∸ suc i)   ≡⟨ cong (⊤ w ∸_) (+-∸-assoc 1 i<⊤) ⟨
  ⊤ w ∸ (suc (⊤ w) ∸ suc i) ≡⟨ refl ⟩
  ⊤ w ∸ (⊤ w ∸ i)           ≡⟨ m∸[m∸n]≡n (<⇒≤ i<⊤) ⟩
  i                         ∎
  where i<⊤ = toℕ<⊤ word

------------------------------------------------------------------------
-- Properties of truncate
------------------------------------------------------------------------

truncate-< :
  ∀ {v w} → (word : Word w) →
  (w<⊤[w-v] : toℕ word < ⊤ (w ∸ v)) →
  truncate v word ≡ ⟦ toℕ word ⟧< w<⊤[w-v]
truncate-< {v} {w} word w<⊤[w-v] = toℕ-injective $ m<n⇒m%n≡m w<⊤[w-v]

truncate-0 :
  ∀ {w} → (word : Word w) →
  truncate 0 word ≡ word
truncate-0 word = toℕ-injective (m<n⇒m%n≡m (toℕ<⊤ word))

truncate-1-≥ :
  ∀ {w} → (word : Word w) → .⦃ _ : NonZero w ⦄ →
  (w≥⊤[w-1] : toℕ word ≥ ⊤ (w ∸ 1)) →
  truncate 1 word ≡ ⟦ toℕ word ∸ ⊤ (w ∸ 1) ⟧< w∸½<½ word w≥⊤[w-1]
truncate-1-≥ {w} word w≥⊤[w-1] = toℕ-injective $ begin-equality
  toℕ word % ⊤ (w ∸ 1)               ≡⟨ m≤n⇒[n∸m]%m≡n%m w≥⊤[w-1] ⟨
  (toℕ word ∸ ⊤ (w ∸ 1)) % ⊤ (w ∸ 1) ≡⟨ m<n⇒m%n≡m (w∸½<½ word w≥⊤[w-1]) ⟩
  toℕ word ∸ ⊤ (w ∸ 1)               ∎

truncate-cast-eq : ∀ w v → .⦃ NonZero v ⦄ → w ∸ 1 ∸ (v ∸ 1) ≡ w ∸ v
truncate-cast-eq w v = begin-equality
  w ∸ 1 ∸ (v ∸ 1)   ≡⟨ ∸-+-assoc w 1 (v ∸ 1) ⟩
  w ∸ (suc (v ∸ 1)) ≡⟨ cong (w ∸_) (suc-pred v) ⟩
  w ∸ v             ∎

truncate-suc :
  ∀ {v w} → (word : Word w) → ⦃ _ : NonZero v ⦄ →
  truncate v word ≡ cast (truncate-cast-eq w v) (truncate (v ∸ 1) (truncate 1 word))
truncate-suc {v} {w} word = toℕ-injective $ begin-equality
    toℕ word % ⊤ (w ∸ v)
  ≡⟨ m∣n⇒o%n%m≡o%m (⊤ (w ∸ v)) (⊤ (w ∸ 1)) (toℕ word) (v≤⊤⇒⊤v|⊤w (w ∸ v) (w ∸ 1) w-v≤w-1) ⟨
    (toℕ word % ⊤ (w ∸ 1)) % ⊤ (w ∸ v)
  ≡⟨ %-congʳ (cong ⊤ (truncate-cast-eq w v)) ⟨
    toℕ word % ⊤ (w ∸ 1) % ⊤ (w ∸ 1 ∸ (v ∸ 1))
  ∎ where w-v≤w-1 : w ∸ v ≤ w ∸ 1
          w-v≤w-1 = ∸-monoʳ-≤ w (>-nonZero⁻¹ v)

------------------------------------------------------------------------
-- remQuot
------------------------------------------------------------------------
-- Word (w * v) ↔ Word w × Word v

remQuot-combine :
  ∀ {w v} → .⦃ _ : NonZero v ⦄ →
  (x : Word w) (y : Word v) →
  remQuot v (combine x y) ≡ (x , y)
remQuot-combine {w} {v} x y = ×.×-≡,≡→≡
  ( toℕ-injective
      (begin-equality
        (toℕ x ℕ.* ⊤ v ℕ.+ toℕ y) / ⊤ v
      ≡⟨ +-distrib-/-∣ˡ {toℕ x ℕ.* ⊤ v} (toℕ y) {⊤ v} (n∣m*n (toℕ x)) ⟩
        toℕ x ℕ.* ⊤ v / ⊤ v ℕ.+ toℕ y / ⊤ v
      ≡⟨ Rel₂.cong₂ ℕ._+_ (m*n/n≡m (toℕ x) (⊤ v)) (m<n⇒m/n≡0 (toℕ<⊤ y)) ⟩
        toℕ x ℕ.+ 0
      ≡⟨ +-identityʳ (toℕ x) ⟩
        toℕ x
      ∎)
  , toℕ-injective (begin-equality
      (toℕ x * ⊤ v ℕ.+ toℕ y) % ⊤ v ≡⟨ %-remove-+ˡ (toℕ y) {⊤ v} (n∣m*n (toℕ x)) ⟩
      toℕ y % ⊤ v                   ≡⟨ m<n⇒m%n≡m (toℕ<⊤ y) ⟩
      toℕ y                         ∎)
  )

combine-remQuot : ∀ {w} v → .⦃ _ : NonZero v ⦄ →
  (x : Word (w ℕ.+ v)) →
  ×.uncurry combine (remQuot v x) ≡ x
combine-remQuot {w} v (⟦ x ⟧< _) = toℕ-injective $ begin-equality
  x / ⊤ v ℕ.* ⊤ v ℕ.+ x % ⊤ v ≡⟨ +-comm (x / ⊤ v ℕ.* ⊤ v) (x % ⊤ v) ⟩
  x % ⊤ v ℕ.+ x / ⊤ v ℕ.* ⊤ v ≡⟨ m≡m%n+[m/n]*n x (⊤ v) ⟨
  x                           ∎

------------------------------------------------------------------------
-- Bundles

+↔× : ∀ {w v} → .⦃ NonZero v ⦄ → Word (w ℕ.+ v) ↔ (Word w × Word v)
+↔× {w} {v} = Function.mk↔ₛ′ (remQuot {w} v) (×.uncurry combine)
  (×.uncurry remQuot-combine)
  (combine-remQuot {w} v)
