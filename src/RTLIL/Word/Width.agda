{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Width where

open ℕ hiding (t)

opaque
  ⊤ : ℕ.t → ℕ.t
  ⊤ = 2 ^_

  ⊤-def : ∀ w → ⊤ w ≡ 2 ^ w
  ⊤-def _ = refl

  ⊤-zero : ⊤ 0 ≡ 1
  ⊤-zero = refl

  ⊤-suc : (w : ℕ.t) → ⊤ (suc w) ≡ 2 * ⊤ w
  ⊤-suc w = refl

  ⊤-suc-comm : (w : ℕ.t) → ⊤ (suc w) ≡ ⊤ w * 2
  ⊤-suc-comm w rewrite *-comm (⊤ w) 2 = refl

⊤≢0 : (w : ℕ.t) → NonZero (⊤ w)
⊤≢0 zero rewrite ⊤-zero = nonZero
⊤≢0 (suc w-1) rewrite ⊤-suc w-1 = m*n≢0 2 (⊤ w-1) ⦃ _ ⦄ ⦃ ⊤≢0 w-1 ⦄

instance
  ⊤-nonZero : ∀ {w} → NonZero (⊤ w)
  ⊤-nonZero {w} = ⊤≢0 w

⊤>1 : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → NonTrivial (⊤ w)
⊤>1 w@(suc w-1) rewrite ⊤-suc w-1 = n>1⇒nonTrivial $ begin
  2 ≡⟨ *-identityʳ 2 ⟩
  2 * 1 ≤⟨ *-monoʳ-≤ 2 (>-nonZero⁻¹ (⊤ w-1)) ⟩
  2 * (⊤ w-1) ∎
  where open ≤-Reasoning

instance
  ⊤-nonTrivial : ∀ {w} → .⦃ _ : NonZero w ⦄ → NonTrivial (⊤ w)
  ⊤-nonTrivial {w} = ⊤>1 w

⊤-mono-< : ⊤ Rel₂.Preserves _<_ ⟶ _<_
⊤-mono-< {zero} {y} 1≤y rewrite ⊤-zero = nonTrivial⇒n>1 (⊤ y)
  where instance _ = >-nonZero 1≤y
⊤-mono-< {suc x} {suc y} x<y
  rewrite ⊤-suc x
        | ⊤-suc y = *-monoʳ-< 2 (⊤-mono-< (s<s⁻¹ x<y))

⊤-mono-≤ : ⊤ Rel₂.Preserves _≤_ ⟶ _≤_
⊤-mono-≤ {zero} {y} 0≤y rewrite ⊤-zero = >-nonZero⁻¹ (⊤ y)
⊤-mono-≤ {suc x} {suc y} x≤y
  rewrite ⊤-suc x
        | ⊤-suc y = *-monoʳ-≤ 2 (⊤-mono-≤ (s≤s⁻¹ x≤y))

2∣⊤ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  2 ∣ ⊤ w
2∣⊤ (suc w-1) = divides (⊤ w-1) (⊤-suc-comm w-1)

width<⊤ : (w : ℕ.t) → w < ⊤ w
width<⊤ zero rewrite ⊤-zero  = s≤s z≤n
width<⊤ (suc w-1)
  rewrite ⊤-suc w-1
        | +-identityʳ (⊤ w-1)
        = +-mono-≤-< (>-nonZero⁻¹ (⊤ w-1)) (width<⊤ w-1)

w≢0⇒⊤[w]≡⊤[w-1]*2 : ∀ w → .⦃ _ : NonZero w ⦄ → ⊤ w ≡ ⊤ (w ∸ 1) * 2
w≢0⇒⊤[w]≡⊤[w-1]*2 w@(suc w-1) = ⊤-suc-comm w-1

suc-pred-⊤ : (w : ℕ.t) → ⊤ w ≡ suc (pred (⊤ w))
suc-pred-⊤ w = sym (suc-pred (⊤ w))

½ : (w : ℕ.t) → .⦃ NonZero w ⦄ → ℕ.t
½ w = quotient (2∣⊤ w)

½≢0 : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → NonZero (½ w)
½≢0 w = quotient≢0 (2∣⊤ w)

instance
  ½-nonZero : ∀ {w} → .⦃ _ : NonZero w ⦄ → NonZero (½ w)
  ½-nonZero {w} = ½≢0 w

½w≡⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ½ w ≡ ⊤ (w ∸ 1)
½w≡⊤[w-1] (suc _) = refl

½<⊤ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ½ w < ⊤ w
½<⊤ w = quotient-< (2∣⊤ w)

½≡⌈⊤/2⌉ : ∀ w → .⦃ _ : NonZero w ⦄ → ½ w ≡ ⌈ ⊤ w /2⌉
½≡⌈⊤/2⌉ w@(suc w-1) = begin
  ⊤ w-1               ≡⟨ n≡⌈n+n/2⌉ (⊤ w-1) ⟩
  ⌈ ⊤ w-1 + ⊤ w-1 /2⌉ ≡⟨ cong (λ a → ⌈ ⊤ w-1 + a /2⌉) (+-identityʳ (⊤ w-1)) ⟨
  ⌈ 2 * ⊤ w-1 /2⌉     ≡⟨ cong ⌈_/2⌉ (⊤-suc w-1) ⟨
  ⌈ ⊤ w /2⌉           ∎
  where open Rel₂.≡-Reasoning

½≡⌊⊤/2⌋ : ∀ w → .⦃ _ : NonZero w ⦄ → ½ w ≡ ⌊ ⊤ w /2⌋
½≡⌊⊤/2⌋ w@(suc w-1) = begin
  ⊤ w-1               ≡⟨ n≡⌊n+n/2⌋ (⊤ w-1) ⟩
  ⌊ ⊤ w-1 + ⊤ w-1 /2⌋ ≡⟨ cong (λ a → ⌊ ⊤ w-1 + a /2⌋) (+-identityʳ (⊤ w-1)) ⟨
  ⌊ 2 * ⊤ w-1 /2⌋     ≡⟨ cong ⌊_/2⌋ (⊤-suc w-1) ⟨
  ⌊ ⊤ w /2⌋           ∎
  where open Rel₂.≡-Reasoning

⌈⊤/2⌉≡⌊⊤/2⌋ : ∀ w → .⦃ NonZero w ⦄ → ⌈ ⊤ w /2⌉ ≡ ⌊ ⊤ w /2⌋
⌈⊤/2⌉≡⌊⊤/2⌋ w = trans (sym (½≡⌈⊤/2⌉ w)) (½≡⌊⊤/2⌋ w)
