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
⊤-mono-< {x} {y} x<y rewrite ⊤-def x | ⊤-def y =
  ^-monoʳ-< 2 (s≤s (s≤s z≤n)) x<y

⊤-mono-≤ : ⊤ Rel₂.Preserves _≤_ ⟶ _≤_
⊤-mono-≤ {x} {y} x≤y rewrite ⊤-def x | ⊤-def y =
  ^-monoʳ-≤ 2 x≤y

⊤[w]≤⊤[v+w] : (w v : ℕ.t) → ⊤ w ≤ ⊤ (v ℕ.+ w)
⊤[w]≤⊤[v+w] w v = ⊤-mono-≤ $ begin
  w       ≡⟨ +-identityˡ w ⟨
  0 ℕ.+ w ≤⟨ +-monoˡ-≤ w z≤n ⟩
  v ℕ.+ w ∎
  where open ≤-Reasoning

⊤[w]≤⊤[w+v] : (w v : ℕ.t) → ⊤ w ≤ ⊤ (w ℕ.+ v)
⊤[w]≤⊤[w+v] w v = ⊤-mono-≤ $ begin
  w       ≡⟨ +-identityʳ w ⟨
  w ℕ.+ 0 ≤⟨ +-monoʳ-≤ w z≤n ⟩
  w ℕ.+ v ∎
  where open ≤-Reasoning

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

½ : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → ℕ.t
½ w@(suc _) = 2∣⊤ w .quotient

½≢0 : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → NonZero (½ w)
½≢0 (suc w-1) = ⊤≢0 w-1

instance
  ½-nonZero : ∀ {w} → .⦃ _ : NonZero w ⦄ → NonZero (½ w)
  ½-nonZero {w} = ½≢0 w

½≡⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ½ w ≡ ⊤ (w ∸ 1)
½≡⊤[w-1] (suc _) = refl

½<⊤ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ½ w < ⊤ w
½<⊤ w@(suc _) = quotient-< (2∣⊤ w)

⊤≡2*⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ 2 * ⊤ (w ∸ 1)
⊤≡2*⊤[w-1] w ⦃ w≢0 ⦄
  rewrite sym (⊤-suc (w ∸ 1))
        | suc-pred w ⦃ w≢0 ⦄ = refl

⊤≡2*½ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ 2 * ½ w
⊤≡2*½ w ⦃ w≢0 ⦄ rewrite ½≡⊤[w-1] w ⦃ w≢0 ⦄ = ⊤≡2*⊤[w-1] w

⊤≡⊤[w-1]+⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ ⊤ (w ∸ 1) + ⊤ (w ∸ 1)
⊤≡⊤[w-1]+⊤[w-1] w = begin
  ⊤ w             ≡⟨ ⊤≡2*⊤[w-1] w ⟩
  2 * ⊤[w-1]      ≡⟨ cong (⊤[w-1] +_) (+-identityʳ (⊤[w-1])) ⟩
  ⊤[w-1] + ⊤[w-1] ∎
  where ⊤[w-1] = ⊤ (w ∸ 1)
        open Rel₂.≡-Reasoning

⊤≡½+½ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ ½ w + ½ w
⊤≡½+½ w = begin
  ⊤ w             ≡⟨ ⊤≡2*½ w ⟩
  2 * ½ w         ≡⟨⟩
  ½ w + (½ w + 0) ≡⟨ cong (½ w +_) (+-identityʳ (½ w)) ⟩
  ½ w + ½ w       ∎
  where open Rel₂.≡-Reasoning

⊤[w+v]≡⊤[w]*⊤[v] : (w v : ℕ.t) → ⊤ (w + v) ≡ ⊤ w * ⊤ v
⊤[w+v]≡⊤[w]*⊤[v] w v
  rewrite ⊤-def (w + v)
        | ⊤-def w
        | ⊤-def v
        = ℕ.^-distribˡ-+-* 2 w v

⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] : (w v : ℕ.t) → ⊤ (w + v) ≡ ⊤ w + (⊤ v ∸ 1) * ⊤ w
⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w zero
  rewrite ℕ.+-identityʳ w
        | ⊤-def zero
        | ℕ.+-identityʳ (⊤ w)
        = refl
⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v@(suc v-1)
       -- lhs
  rewrite ℕ.+-suc w v-1
        | ⊤-suc (w + v-1)
        | ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v-1
        | ℕ.+-identityʳ (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w)
        -- rhs
        | ⊤-suc v-1
        | ℕ.+-identityʳ (⊤ v-1)
        | ℕ.+-∸-assoc (⊤ v-1) (>-nonZero⁻¹ (⊤ v-1))
        | ℕ.+-comm (⊤ v-1) (⊤ v-1 ∸ 1)
        | ℕ.*-distribʳ-+ (⊤ w) (⊤ v-1 ∸ 1) (⊤ v-1)
        | ℕ.*-comm (⊤ v-1) (⊤ w)
        | sym (⊤[w+v]≡⊤[w]*⊤[v] w v-1)
        | ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v-1
        | ℕ.+-assoc (⊤ w) ((⊤ v-1 ∸ 1) * ⊤ w) (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w)
        = refl

⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] : (v w : ℕ.t) → ⊤ (v + w) ≡ (⊤ v ∸ 1) * ⊤ w + ⊤ w
⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v w
  rewrite ℕ.+-comm v w
        | ℕ.+-comm ((⊤ v ∸ 1) * ⊤ w) (⊤ w)
        = ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v

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
