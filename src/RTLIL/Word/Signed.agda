{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Signed where

open import RTLIL.Word.Base
open import RTLIL.Word.Width
open import RTLIL.Word.Properties

open import Tactic.Cong using (cong!; ⌞_⌟)

open ℕ hiding (t)
open Rel₀ using (no; yes)
open ℤ using (+_; -[1+_])
open ≤-Reasoning

fromNeg : ∀ {w n} → .⦃ _ : NonZero w ⦄ → n < ½ w → Word w
fromNeg {w} {n} n<½ = word< top-[1+n]<top
  where
    m = ⊤ w ∸ (1 + n)
    top-[1+n]<top : m < ⊤ w
    top-[1+n]<top = ∸-monoʳ-< z<s (≤-trans n<½ (<⇒≤ (½<⊤ w)))

fromPos : ∀ {w n} → .⦃ _ : ℕ.NonZero w ⦄ → n ℕ.< ½ w → Word w
fromPos {w} n<½ = word< (<-trans n<½ (½<⊤ w))

from :
  ∀ {w} {z} → .⦃ _ : NonZero w ⦄ →
  z ℤ.< + ½ w →
  z ℤ.> -[1+ ½ w ] →
  Word w
from {z = + _}      n<½ _   = fromPos (ℤ.drop‿+<+ n<½)
from {z = -[1+ _ ]} _   n<½ = fromNeg (ℤ.drop‿-<- n<½)

to : ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w → ℤ.t
to {w} word with split word
… | inj₁ n = + toℕ n
… | inj₂ n = -[1+ toℕ $ opposite n ]

opaque
  unfolding ⊤

  _ : to (3 #b 4) ≡ -[1+ 3 ]
  _ = refl

  _ : to (3 #b 3) ≡ + 3
  _ = refl

to-< :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) → (toℕ word < ⊤ (w ∸ 1)) →
  to word ≡ + toℕ word
to-< word v<½ rewrite split-< word v<½ = refl

-- 2+m+m≡2*[1+m] : ∀ m → 2+ (m + m) ≡ 2 * suc m
-- 2+m+m≡2*[1+m] m = begin-equality
--   2+ (m + m)            ≡⟨ cong! (+-suc m m) ⟨
--   suc (m + suc m)       ≡⟨⟩
--   suc m + suc m         ≡⟨ cong! (+-identityʳ (suc m)) ⟨
--   suc m + ⌞ suc m + 0 ⌟ ∎

m∸[n∸m]≡2m∸n : ∀ {m n} → m ≤ n → m ∸ (n ∸ m) ≡ 2 * m ∸ n
m∸[n∸m]≡2m∸n {m} {n} m≤n with k ← n ∸ m in n∸m≡k = begin-equality
    m ∸ k
  ≡⟨ [m+n]∸[m+o]≡n∸o m m k ⟨
    (m + m) ∸ (m + k)
  ≡⟨ Rel₂.cong₂ _∸_ (cong (m ℕ.+_) (+-identityʳ m)) (cong (m ℕ.+_) n∸m≡k) ⟨
    2 * m ∸ (m + (n ∸ m))
  ≡⟨ cong! (m+[n∸m]≡n m≤n) ⟩
    2 * m ∸ n
  ∎

to-≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) → (toℕ word ≥ ⊤ (w ∸ 1)) →
  to word ≡ -[1+ ⊤ w ∸ toℕ word ∸ 1 ]
to-≥ w@{suc w-1} word v≥½ rewrite split-≥ word v≥½ = cong -[1+_] $ begin-equality
  ⊤ w-1 ∸ suc (toℕ word ∸ ⊤ w-1)    ≡⟨ pred[m∸n]≡m∸[1+n] (⊤ w-1) _ ⟨
  pred (⊤ w-1 ∸ (toℕ word ∸ ⊤ w-1)) ≡⟨ cong pred (m∸[n∸m]≡2m∸n v≥½) ⟩
  pred (2 * ⊤ w-1 ∸ toℕ word)       ≡⟨ cong! (⊤-suc w-1) ⟨
  pred (⊤ w ∸ toℕ word)             ∎

instance
  extend-nonZero : ∀ {w v} → .⦃ _ : NonZero w ⦄ → NonZero (v + w)
  extend-nonZero {w} {v} = >-nonZero $ begin-strict
    0     <⟨ >-nonZero⁻¹ _ ⟩
    w     ≤⟨ m≤n+m w v ⟩
    v + w ∎

extend : ∀ {w} → .⦃ _ : NonZero w ⦄ → (v : ℕ.t) → Word w → Word (v ℕ.+ w)
extend w@{suc _} v word with toℕ word <? ⊤ (w ∸ 1)
… | yes _ = 0-extend v word
… | no  _ = 1-extend v word

extend-< :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (v : ℕ.t) → (word : Word w) → (w<½ : toℕ word < ⊤ (w ∸ 1)) →
  extend v word ≡ 0-extend v word
extend-< w@{suc w-1} ⦃ w≢0 ⦄ v word w<½ with toℕ word <? ⊤ w-1
… | yes _   = refl
… | no  w≮½ = Rel₀.contradiction w<½ w≮½

extend-<-⊤ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (v : ℕ.t) → (word : Word w) → (w<½ : toℕ word < ⊤ (w ∸ 1)) →
  toℕ (extend v word) < ⊤ (v + w ∸ 1)
extend-<-⊤ {w} v word w<½ rewrite extend-< v word w<½ = begin-strict
  toℕ word <⟨ w<½ ⟩
  ⊤ (w ∸ 1) ≤⟨ ⊤[w]≤⊤[v+w] (w ∸ 1) v ⟩
  ⊤ (v + (w ∸ 1)) ≡⟨ cong ⊤ (+-∸-assoc v (>-nonZero⁻¹ w)) ⟨
  ⊤ (v + w ∸ 1) ∎

extend-≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (v : ℕ.t) → (word : Word w) → (w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
  extend v word ≡ 1-extend v word
extend-≥ w@{suc w-1} ⦃ w≢0 ⦄ v word w≥½ with toℕ word <? ⊤ w-1
… | yes w<½ = Rel₀.contradiction w≥½ (<⇒≱ w<½)
… | no  w≮½ = refl

extend-≥-⊤ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (v : ℕ.t) → (word : Word w) → (w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
  toℕ (extend v word) ≥ ⊤ (v + w ∸ 1)
extend-≥-⊤ {w} ⦃ w≢0 ⦄ v word w≥½ rewrite extend-≥ v word w≥½ = begin
    ⊤ (v + w ∸ 1)
  ≡⟨ cong ⊤ (+-∸-assoc v (>-nonZero⁻¹ w)) ⟩
    ⊤ (v + (w ∸ 1))
  ≡⟨ ⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v (w ∸ 1) ⟩
    (⊤ v ∸ 1) * ⊤ (w ∸ 1) + ⊤ (w ∸ 1)
  ≤⟨ +-monoˡ-≤ (⊤ (w ∸ 1)) (*-monoʳ-≤ (⊤ v ∸ 1) (<⇒≤ $ ≤-<-trans (≤-reflexive (sym (½≡⊤[w-1] w))) (½<⊤ w)) )⟩
    (⊤ v ∸ 1) * ⊤ w + ⊤ (w ∸ 1)
  ≤⟨ +-monoʳ-≤ ((⊤ v ∸ 1) * ⊤ w) w≥½ ⟩
    (⊤ v ∸ 1) * ⊤ w + toℕ word
  ∎

to-extend :
  (v : ℕ.t) → ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) →
  to (extend v word) ≡ to word
to-extend v {w} ⦃ w≢0 ⦄ word
  with toℕ word <? ⊤ (w ∸ 1)
… | yes w<½
  rewrite to-< (extend v word) (extend-<-⊤ v word w<½)
        | extend-< v word w<½
        | to-< word w<½
        = refl

… | no  w≮½
  rewrite to-≥ (extend v word) (extend-≥-⊤ v word (≮⇒≥ w≮½))
        | extend-≥ v word (≮⇒≥ w≮½)
        | to-≥ word (≮⇒≥ w≮½)
        = cong (-[1+_] ∘ pred) $ begin-equality
          ⊤ (v + w) ∸ ((⊤ v ∸ 1) * ⊤ w + toℕ word) ≡⟨ cong! (*-distribʳ-∸ (⊤ w) (⊤ v) 1) ⟩
          ⊤ (v + w) ∸ (⊤ v * ⊤ w ∸ 1 * ⊤ w + toℕ word) ≡⟨ cong! (*-identityˡ (⊤ w)) ⟩
          ⊤ (v + w) ∸ (⊤ v * ⊤ w ∸ ⊤ w + toℕ word) ≡⟨ cong! (⊤[w+v]≡⊤[w]*⊤[v] v w) ⟨
          ⊤ (v + w) ∸ (⊤ (v + w) ∸ ⊤ w + toℕ word) ≡⟨ ∸-+-assoc (⊤ (v + w)) (⊤ (v + w) ∸ ⊤ w) (toℕ word) ⟨
          ⊤ (v + w) ∸ (⊤ (v + w) ∸ ⊤ w) ∸ toℕ word ≡⟨ cong! (m∸[m∸n]≡n (⊤[w]≤⊤[v+w] w v)) ⟩ 
          ⊤ w ∸ toℕ word ∎

opaque
  unfolding ⊤

  _ : to (3 #b 4) ≡ -[1+ 3 ]
  _ = refl

  _ : to (3 #b 3) ≡ + 3
  _ = refl

  _ : to (extend 2 $ (3 #b 3)) ≡ + 3
  _ = refl

  _ : toℕ (extend 0 $ (3 #b 4)) ≡ 4
  _ = refl

  _ : toℕ (extend 1 $ (3 #b 4)) ≡ 12
  _ = refl

  _ : to (extend 2 (3 #b 4)) ≡ -[1+ 3 ]
  _ = refl
