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
open import Function.Construct.Composition using (_↔-∘_)
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

0↔⊤ : ∀ {ℓ} → Word 0 ↔ 𝟙.t {ℓ}
0↔⊤ = Fin.1↔⊤ ↔-∘ Word↔Fin

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
-- toℕ-extend

toℕ-0-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (0-extend v word) ≡ toℕ word
toℕ-0-extend _ _ = refl

toℕ-1-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (1-extend v word) ≡ toℕ word ℕ.+ (⊤ v ∸ 1) * ⊤ w
toℕ-1-extend v {w} (⟦ value ⟧< value<⊤) = refl

toℕ-1-extend′ :
  ∀ {w} → (word : Word w) →
  toℕ (1-extend 1 word) ≡ toℕ word ℕ.+ ⊤ w
toℕ-1-extend′ {w} word = begin-equality
  toℕ word ℕ.+ (⊤ 1 ∸ 1) * ⊤ w ≡⟨ cong! ⊤1∸1≡1 ⟩
  toℕ word ℕ.+ 1 * ⊤ w         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  toℕ word ℕ.+ ⊤ w             ∎

0-extend-by-0 : ∀ {w} → (word : Word w) → 0-extend 0 word ≡ word
0-extend-by-0 {w} word = toℕ-injective refl

0-extend<⊤[w⊔v] : ∀ {w} v → (word : Word w) → toℕ (0-extend (suc (v ∸ w)) word) < ⊤ (w ⊔ v)
0-extend<⊤[w⊔v] {w} v word = m<⊤w⇒m<⊤[w⊔v] v (toℕ<⊤ word)

1-extend-by-0 : ∀ {w} → (word : Word w) → 1-extend 0 word ≡ word
1-extend-by-0 {w} word rewrite ⊤-zero = toℕ-injective (+-identityʳ (toℕ word))

1-extend≥⊤[w⊔v] : ∀ w v → (word : Word v) → ⊤ (w ⊔ v) ≤ toℕ (1-extend (suc (w ∸ v)) word)
1-extend≥⊤[w⊔v] w v word with w ≤? v
… | yes w≤v = begin
  ⊤ (w ⊔ v)                                ≡⟨ cong ⊤ (m≤n⇒m⊔n≡n w≤v) ⟩
  ⊤ v                                      ≡⟨ +-identityˡ (⊤ v) ⟩
  0 ℕ.+ ⊤ v                                ≤⟨ +-monoˡ-≤ (⊤ v) z≤n ⟩
  toℕ word ℕ.+ ⊤ v                         ≡⟨ cong! (*-identityˡ (⊤ v)) ⟨
  toℕ word ℕ.+ 1 * ⊤ v                     ≡⟨ cong! ⊤1∸1≡1 ⟨
  toℕ word ℕ.+ (⊤ (suc 0) ∸ 1) * ⊤ v       ≡⟨ cong! (m≤n⇒m∸n≡0 w≤v) ⟨
  toℕ word ℕ.+ (⊤ (suc (w ∸ v)) ∸ 1) * ⊤ v ∎
… | no  w≰v = begin
  ⊤ (w ⊔ v)                            ≡⟨ cong ⊤ (m≥n⇒m⊔n≡m (≰⇒≥ w≰v)) ⟩
  ⊤ w                                  ≡⟨ ⊤w≡⊤[w+1]∸⊤w w ⟩
  ⊤ (suc w) ∸ ⊤ w                      ≤⟨ ∸-monoʳ-≤ (⊤ (suc w)) (⊤-mono-≤ (≰⇒≥ w≰v)) ⟩
  ⊤ (suc w) ∸ ⊤ v                      ≡⟨ cong! (m∸n+n≡m (≰⇒≥ w≰v)) ⟨
  ⊤ (suc (w-v ℕ.+ v)) ∸ ⊤ v            ≡⟨ refl ⟩
  ⊤ (suc w-v ℕ.+ v) ∸ ⊤ v              ≡⟨ cong! (⊤[w+v]≡⊤[w]*⊤[v] (suc w-v) v) ⟩
  ⊤ (suc w-v) * ⊤ v ∸ ⊤ v              ≡⟨ cong! (*-identityˡ (⊤ v)) ⟨
  ⊤ (suc w-v) * ⊤ v ∸ 1 * ⊤ v          ≡⟨ *-distribʳ-∸ (⊤ v) (⊤ (suc w-v)) 1 ⟨
  (⊤ (suc w-v) ∸ 1) * ⊤ v              ≡⟨ +-identityˡ ((⊤ (suc w-v) ∸ 1) * ⊤ v) ⟨
  0 ℕ.+ (⊤ (suc w-v) ∸ 1) * ⊤ v        ≤⟨ +-monoˡ-≤ ((⊤ (suc w-v) ∸ 1) * ⊤ v) z≤n ⟩
  toℕ word ℕ.+ (⊤ (suc w-v) ∸ 1) * ⊤ v ∎
  where w-v = w ∸ v

------------------------------------------------------------------------
-- truncate-extend

truncate-zero :
  ∀ {w} → (word : Word w) →
  truncate 0 word ≡ word
truncate-zero word = toℕ-injective (m<n⇒m%n≡m (toℕ<⊤ word))

truncate-0-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  truncate v (0-extend v word) ≡ cast (sym $ m+n∸m≡n v w) word
truncate-0-extend v {w} word = toℕ-injective $ begin-equality
  toℕ word % ⊤ (v ℕ.+ w ∸ v) ≡⟨ %-congʳ (cong ⊤ (m+n∸m≡n v w)) ⟩
  toℕ word % ⊤ w             ≡⟨ m<n⇒m%n≡m (toℕ<⊤ word) ⟩
  toℕ word                   ∎

truncate-1-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  truncate v (1-extend v word) ≡ cast (sym $ m+n∸m≡n v w) word
truncate-1-extend v {w} word = toℕ-injective $
  begin-equality
    (toℕ word ℕ.+ (⊤ v ∸ 1) * ⊤ w) % ⊤ (v ℕ.+ w ∸ v)
  ≡⟨ %-congʳ (cong ⊤ (m+n∸m≡n v w)) ⟩
    (toℕ word ℕ.+ (⊤ v ∸ 1) * ⊤ w) % ⊤ w
  ≡⟨ [m+kn]%n≡m%n (toℕ word) (⊤ v ∸ 1) (⊤ w) ⟩
    toℕ word % ⊤ w
  ≡⟨ m<n⇒m%n≡m (toℕ<⊤ word) ⟩
    toℕ word
  ∎

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
     | toℕ word ℕ.+ (⊤ 1 ∸ 1) * ⊤ w <? ⊤ w
… | yes v<⊤ = Rel₀.contradiction v<⊤ v≮⊤
  where v≮⊤ : toℕ word ℕ.+ (⊤ 1 ∸ 1) * ⊤ w ≮ ⊤ w
        v≮⊤ = ≤⇒≯ $ begin
          ⊤ w                   ≡⟨ +-identityˡ (⊤ w) ⟨
          0 ℕ.+ ⊤ w             ≤⟨ +-monoˡ-≤ (⊤ w) z≤n ⟩
          toℕ word ℕ.+ ⊤ w      ≡⟨ toℕ-1-extend′ word ⟨
          toℕ (1-extend 1 word) ∎
          where open ≤-Reasoning
… | no  v≮⊤ = cong inj₂ $ toℕ-injective $ begin-equality
  toℕ (1-extend 1 word) ∸ ⊤ w ≡⟨ cong! (toℕ-1-extend′ word) ⟩
  toℕ word ℕ.+ ⊤ w ∸ ⊤ w      ≡⟨ m+n∸n≡m (toℕ word) (⊤ w) ⟩
  toℕ word                    ∎

split-join-1 :
  ∀ {w} → (i : Word w ⊎ Word w) → split (join-1 i) ≡ i
split-join-1 (inj₁ i) = split-0-extend i
split-join-1 (inj₂ i) = split-1-extend i

join-1-split : ∀ {w} → (i : Word (suc w)) → join-1 (split i) ≡ i
join-1-split {w} i with toℕ i <? ⊤ w
… | yes _  = refl
… | no i≮⊤ = toℕ-injective $ begin-equality
  toℕ i ∸ ⊤ w ℕ.+ (⊤ 1 ∸ 1) * ⊤ w ≡⟨ cong! (⊤-def 1) ⟩
  toℕ i ∸ ⊤ w ℕ.+ (2 ∸ 1) * ⊤ w   ≡⟨ refl ⟩
  toℕ i ∸ ⊤ w ℕ.+ 1 * ⊤ w         ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
  toℕ i ∸ ⊤ w ℕ.+ ⊤ w             ≡⟨ m∸n+n≡m (≮⇒≥ i≮⊤) ⟩
  toℕ i                           ∎

join-is-join-1 : ∀ {w} → (i : Word w ⊎ Word w) → join w w i ≡ cast (cong suc (sym $ ⊔-idem w)) (join-1 i)
join-is-join-1 {w} (inj₁ i) = toℕ-injective refl
join-is-join-1 {w} (inj₂ i) = toℕ-injective $ begin-equality
  toℕ i ℕ.+ (⊤ (suc (w ∸ w)) ∸ 1) * ⊤ w ≡⟨ cong! (n∸n≡0 w) ⟩
  toℕ i ℕ.+ (⊤ (suc 0) ∸ 1) * ⊤ w       ≡⟨⟩
  toℕ i ℕ.+ (⊤ 1 ∸ 1) * ⊤ w             ∎

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

truncate-nonZero :
  ∀ {v w} → (word : Word w) → ⦃ _ : NonZero v ⦄ →
  truncate v word ≡ cast (truncate-cast-eq w v) (truncate (v ∸ 1) (truncate 1 word))
truncate-nonZero {v} {w} word = toℕ-injective $ begin-equality
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
  ∀ {w v} → (x : Word w) (y : Word v) →
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

combine-remQuot :
  ∀ {w} v → (x : Word (w ℕ.+ v)) →
  ×.uncurry combine (remQuot v x) ≡ x
combine-remQuot {w} v (⟦ x ⟧< _) = toℕ-injective $ begin-equality
  x / ⊤ v ℕ.* ⊤ v ℕ.+ x % ⊤ v ≡⟨ +-comm (x / ⊤ v ℕ.* ⊤ v) (x % ⊤ v) ⟩
  x % ⊤ v ℕ.+ x / ⊤ v ℕ.* ⊤ v ≡⟨ m≡m%n+[m/n]*n x (⊤ v) ⟨
  x                           ∎

------------------------------------------------------------------------
-- Bundles

+↔× : ∀ {w v} → Word (w ℕ.+ v) ↔ (Word w × Word v)
+↔× {w} {v} = Function.mk↔ₛ′ (remQuot {w} v) (×.uncurry combine)
  (×.uncurry remQuot-combine)
  (combine-remQuot {w} v)
