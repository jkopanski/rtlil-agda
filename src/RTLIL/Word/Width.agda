{-# OPTIONS --safe --cubical-compatible #-}

open import Prelude

module RTLIL.Word.Width where

open import Data.Nat.Tactic.RingSolver using (solve; solve-∀)
open import Tactic.Cong using (cong!; ⌞_⌟)

open ℕ hiding (t)
open List using ([]; _∷_; [_])

open ≤-Reasoning

opaque
  ⊤ : ℕ.t → ℕ.t
  ⊤ = 2 ^_

  ⊤-def : ∀ w → ⊤ w ≡ 2 ^ w
  ⊤-def _ = refl

  ⊤-zero : ⊤ 0 ≡ 1
  ⊤-zero = refl

  ⊤-suc : (w : ℕ.t) → ⊤ (suc w) ≡ 2 * ⊤ w
  ⊤-suc w = refl

  ⊤-one : ⊤ 1 ≡ 2
  ⊤-one rewrite ⊤-suc 0 = refl

⊤-suc-comm : (w : ℕ.t) → ⊤ (suc w) ≡ ⊤ w * 2
⊤-suc-comm w = trans (⊤-suc w) (*-comm 2 (⊤ w))

⊤≢0 : (w : ℕ.t) → NonZero (⊤ w)
⊤≢0 w rewrite ⊤-def w = m^n≢0 2 w

instance
  ⊤-nonZero : ∀ {w} → NonZero (⊤ w)
  ⊤-nonZero {w} = ⊤≢0 w

⊤⇒2ʷ :
  {P : Rel ℕ.t 𝕃.0ℓ} → (pre : Rel₂.IsPreorder _≡_ P) →
  ∀ {w x} → P x (⊤ w) → P x (2 ^ w)
⊤⇒2ʷ pre {w} x~⊤ = x~⊤ ⟫ (reflexive (⊤-def w))
  where open Rel₂.IsPreorder pre renaming (trans to _⟫_)

2ʷ⇒⊤ :
  {P : Rel ℕ.t 𝕃.0ℓ} → (pre : Rel₂.IsPreorder _≡_ P) →
  ∀ {w x} → P x (2 ^ w) → P x (⊤ w)
2ʷ⇒⊤ pre {w} x~2ʷ = x~2ʷ ⟫ (reflexive (sym (⊤-def w)))
  where open Rel₂.IsPreorder pre renaming (trans to _⟫_)

⊤-is-suc : (w : ℕ.t) → ⊤ w ≡ 1 + (⊤ w ∸ 1)
⊤-is-suc w = sym (m+[n∸m]≡n (>-nonZero⁻¹ (⊤ w)))

⊤>1 : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → NonTrivial (⊤ w)
⊤>1 w@(suc w-1) = n>1⇒nonTrivial $ begin
  2           ≡⟨ *-identityʳ 2 ⟩
  2 * 1       ≤⟨ *-monoʳ-≤ 2 (>-nonZero⁻¹ (⊤ w-1)) ⟩
  2 * (⊤ w-1) ≡⟨ ⊤-suc w-1 ⟨
  ⊤ w         ∎

instance
  ⊤-nonTrivial : ∀ {w} → .⦃ _ : NonZero w ⦄ → NonTrivial (⊤ w)
  ⊤-nonTrivial {w} = ⊤>1 w

⊤-mono-< : ⊤ Rel₂.Preserves _<_ ⟶ _<_
⊤-mono-< {x} {y} x<y = begin-strict --rewrite ⊤-def x | ⊤-def y =
  ⊤ x   ≡⟨ ⊤-def x ⟩
  2 ^ x <⟨ ^-monoʳ-< 2 (s≤s (s≤s z≤n)) x<y ⟩
  2 ^ y ≡⟨ ⊤-def y ⟨
  ⊤ y   ∎

⊤-mono-≤ : ⊤ Rel₂.Preserves _≤_ ⟶ _≤_
⊤-mono-≤ {x} {y} x≤y = begin -- rewrite ⊤-def x | ⊤-def y =
  ⊤ x   ≡⟨ ⊤-def x ⟩
  2 ^ x ≤⟨ ^-monoʳ-≤ 2 x≤y ⟩
  2 ^ y ≡⟨ ⊤-def y ⟨
  ⊤ y   ∎

⊤[w]≤⊤[v+w] : (w v : ℕ.t) → ⊤ w ≤ ⊤ (v ℕ.+ w)
⊤[w]≤⊤[v+w] w v = ⊤-mono-≤ $ begin
  w       ≡⟨ +-identityˡ w ⟨
  0 ℕ.+ w ≤⟨ +-monoˡ-≤ w z≤n ⟩
  v ℕ.+ w ∎

⊤[w]≤⊤[w+v] : (w v : ℕ.t) → ⊤ w ≤ ⊤ (w ℕ.+ v)
⊤[w]≤⊤[w+v] w v = ⊤-mono-≤ $ begin
  w       ≡⟨ +-identityʳ w ⟨
  w ℕ.+ 0 ≤⟨ +-monoʳ-≤ w z≤n ⟩
  w ℕ.+ v ∎

2∣⊤ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  2 ∣ ⊤ w
2∣⊤ (suc w-1) = divides (⊤ w-1) (⊤-suc-comm w-1)

⊤-pred : (w : ℕ.t) → .⦃ _ : NonZero w ⦄ → ⊤ (w ∸ 1) ≡ ⊤ w / 2
⊤-pred w@(suc w-1) = sym (n/m≡quotient (2∣⊤ w))

⊤[w-v]≡⊤[w]/⊤[v] :
  ∀ {w v} → .⦃ _ : NonZero w ⦄ → (v < w) →
  ⊤ (w ∸ v) ≡ ⊤ w / ⊤ v
⊤[w-v]≡⊤[w]/⊤[v] {w} {zero} _ = begin-equality
  ⊤ w       ≡⟨ n/1≡n (⊤ w) ⟨
  ⊤ w / 1   ≡⟨ /-congʳ ⦃ _ ⦄ (⊤-zero) ⟨
  ⊤ w / ⊤ 0 ∎
⊤[w-v]≡⊤[w]/⊤[v] {w} v@{suc v-1} (s<s v<w) = begin-equality
  ⊤ (w ∸ (1 + v-1)) ≡⟨ cong ⊤ (∸-+-assoc w 1 v-1) ⟨
  ⊤ (w ∸ 1 ∸ v-1)   ≡⟨ ⊤[w-v]≡⊤[w]/⊤[v] v<w ⟩
  ⊤ (w ∸ 1) / ⊤ v-1 ≡⟨ /-congˡ (⊤-pred w) ⟩
  ⊤ w / 2 / ⊤ v-1   ≡⟨ m/n/o≡m/[n*o] (⊤ w) 2 (⊤ v-1) ⟩
  ⊤ w / (2 * ⊤ v-1) ≡⟨ /-congʳ (⊤-suc v-1)  ⟨
  ⊤ w / ⊤ (suc v-1) ∎
  where instance
    w-1≢0 : NonZero (w ∸ 1)
    w-1≢0 = >-nonZero (<-≤-trans (s<s z≤n) v<w)
    ⊤*2≢0 : NonZero (2 * ⊤ v-1)
    ⊤*2≢0  = m*n≢0 2 (⊤ v-1) ⦃ _ ⦄ ⦃ ⊤≢0 v-1 ⦄

width<⊤ : (w : ℕ.t) → w < ⊤ w
width<⊤ zero = >-nonZero⁻¹ (⊤ 0)
width<⊤ w@(suc w-1) = begin-strict
  suc w-1       <⟨ +-mono-≤-< (>-nonZero⁻¹ (⊤ w-1)) (width<⊤ w-1) ⟩
  ⊤ w-1 + ⊤ w-1 ≡⟨ cong (⊤ w-1 +_) (+-identityʳ (⊤ w-1)) ⟨
  2 * ⊤ w-1     ≡⟨ ⊤-suc w-1 ⟨
  ⊤ (suc w-1)   ∎

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

⊤≡2*½ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ 2 * ½ w
⊤≡2*½ w@(suc w-1) ⦃ w≢0 ⦄ = begin-equality
  ⊤ w       ≡⟨ ⊤-suc w-1 ⟩
  2 * ⊤ w-1 ≡⟨ cong (2 *_) (½≡⊤[w-1] w) ⟨
  2 * ½ w   ∎

⊤≡⊤[w-1]+⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ ⊤ (w ∸ 1) + ⊤ (w ∸ 1)
⊤≡⊤[w-1]+⊤[w-1] w@(suc w-1) = trans
  (⊤-suc w-1)
  (cong (⊤ w-1 +_) (+-identityʳ (⊤ w-1)))

⊤∸⊤[w-1]≡⊤[w-1] :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ∸ ⊤ (w ∸ 1) ≡ ⊤ (w ∸ 1)
⊤∸⊤[w-1]≡⊤[w-1] w@(suc w-1) = begin-equality
  ⊤ w ∸ ⊤ w-1             ≡⟨ cong (_∸ ⊤ w-1) (⊤≡⊤[w-1]+⊤[w-1] w) ⟩
  ⊤ w-1 ℕ.+ ⊤ w-1 ∸ ⊤ w-1 ≡⟨ m+n∸n≡m (⊤ w-1) (⊤ w-1) ⟩
  ⊤ w-1                   ∎

⊤≡½+½ :
  (w : ℕ.t) → .⦃ _ : NonZero w ⦄ →
  ⊤ w ≡ ½ w + ½ w
⊤≡½+½ w = begin-equality
  ⊤ w             ≡⟨ ⊤≡2*½ w ⟩
  2 * ½ w         ≡⟨⟩
  ½ w + (½ w + 0) ≡⟨ cong (½ w +_) (+-identityʳ (½ w)) ⟩
  ½ w + ½ w       ∎

⊤[w+v]≡⊤[w]*⊤[v] : (w v : ℕ.t) → ⊤ (w + v) ≡ ⊤ w * ⊤ v
⊤[w+v]≡⊤[w]*⊤[v] w v = begin-equality
  ⊤ (w + v)     ≡⟨ ⊤-def (w + v) ⟩
  2 ^ (w + v)   ≡⟨ ^-distribˡ-+-* 2 w v ⟩
  2 ^ w * 2 ^ v ≡⟨ Rel₂.cong₂ _*_ (⊤-def w) (⊤-def v) ⟨
  ⊤ w * ⊤ v     ∎

⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] : (w v : ℕ.t) → ⊤ (w + v) ≡ ⊤ w + (⊤ v ∸ 1) * ⊤ w
⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w zero = begin-equality
  ⊤ (w + zero)                 ≡⟨ cong ⊤ (+-identityʳ w) ⟩
  ⊤ w                          ≡⟨ +-identityʳ (⊤ w) ⟨
  ⊤ w + 0 * ⊤ w                ≡⟨ refl ⟩
  ⊤ w + (1 ∸ 1) * ⊤ w          ≡⟨ cong! ⊤-zero ⟨
  ⊤ w + (⌞ ⊤ zero ⌟ ∸ 1) * ⊤ w ∎

⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v@(suc v-1) = begin-equality
  ⊤ (w + suc v-1)   ≡⟨ cong ⊤ (+-suc w v-1) ⟩
  ⊤ (suc (w + v-1)) ≡⟨ ⊤-suc (w + v-1) ⟩
  2 * ⊤ (w + v-1)   ≡⟨ cong (2 *_) (⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v-1) ⟩
  2 * (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w)                               ≡⟨ refl ⟩
  ⊤ w + (⊤ v-1 ∸ 1) * ⊤ w + ⌞ (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w) + 0 ⌟ ≡⟨ cong! (+-identityʳ (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w)) ⟩
  ⊤ w + (⊤ v-1 ∸ 1)  * ⊤ w + (⊤ w + (⊤ v-1 ∸ 1) * ⊤ w) ≡⟨ cong! (⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v-1) ⟨
  ⊤ w + (⊤ v-1 ∸ 1)  * ⊤ w + ⊤ (w + v-1)               ≡⟨ cong! (⊤[w+v]≡⊤[w]*⊤[v] w v-1) ⟩
  ⊤ w + (⊤ v-1 ∸ 1)  * ⊤ w + ⌞ ⊤ w * ⊤ v-1 ⌟ ≡⟨ cong! (*-comm (⊤ w) (⊤ v-1)) ⟩
  ⊤ w + (⊤ v-1 ∸ 1)  * ⊤ w + ⊤ v-1 * ⊤ w     ≡⟨ +-assoc (⊤ w) ((⊤ v-1 ∸ 1) * ⊤ w) (⊤ v-1 * ⊤ w) ⟩
  ⊤ w + ((⊤ v-1 ∸ 1) * ⊤ w + ⊤ v-1 * ⊤ w)    ≡⟨ cong! (*-distribʳ-+ (⊤ w) (⊤ v-1 ∸ 1) (⊤ v-1)) ⟨
  ⊤ w + (⊤ v-1 ∸ 1 + ⊤ v-1 )        * ⊤ w ≡⟨ cong! (+-comm (⊤ v-1 ∸ 1) (⊤ v-1)) ⟩
  ⊤ w + ⌞ ⊤ v-1 + (⊤ v-1     ∸ 1) ⌟ * ⊤ w ≡⟨ cong! (+-∸-assoc (⊤ v-1) (>-nonZero⁻¹ (⊤ v-1))) ⟨
  ⊤ w + (⊤ v-1 + ⌞ ⊤ v-1 ⌟   ∸ 1)   * ⊤ w ≡⟨ cong! (+-identityʳ (⊤ v-1)) ⟨
  ⊤ w + (⊤ v-1 + (⊤ v-1 + 0) ∸ 1)   * ⊤ w ≡⟨ cong! (⊤-suc v-1) ⟨
  ⊤ w + (⊤ (suc v-1) ∸ 1) * ⊤ w ∎

⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] : (v w : ℕ.t) → ⊤ (v + w) ≡ (⊤ v ∸ 1) * ⊤ w + ⊤ w
⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v w = begin-equality
  ⊤ (v + w)             ≡⟨ cong ⊤ (+-comm v w) ⟩
  ⊤ (w + v)             ≡⟨ ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v ⟩
  ⊤ w + (⊤ v ∸ 1) * ⊤ w ≡⟨ +-comm (⊤ w) ((⊤ v ∸ 1) * ⊤ w) ⟩
  (⊤ v ∸ 1) * ⊤ w + ⊤ w ∎

v≤⊤⇒⊤v|⊤w : ∀ v w → v ≤ w → ⊤ v ∣ ⊤ w
v≤⊤⇒⊤v|⊤w v w v≤w = divides (⊤ (w ∸ v)) $ begin-equality
  ⊤ w             ≡⟨ cong ⊤ (m∸n+n≡m v≤w) ⟨
  ⊤ (w ∸ v + v)   ≡⟨ ⊤[w+v]≡⊤[w]*⊤[v] (w ∸ v) v ⟩ 
  ⊤ (w ∸ v) * ⊤ v ∎

½≡⌈⊤/2⌉ : ∀ w → .⦃ _ : NonZero w ⦄ → ½ w ≡ ⌈ ⊤ w /2⌉
½≡⌈⊤/2⌉ w@(suc w-1) = begin-equality
  ⊤ w-1               ≡⟨ n≡⌈n+n/2⌉ (⊤ w-1) ⟩
  ⌈ ⊤ w-1 + ⊤ w-1 /2⌉ ≡⟨ cong (λ a → ⌈ ⊤ w-1 + a /2⌉) (+-identityʳ (⊤ w-1)) ⟨
  ⌈ 2 * ⊤ w-1 /2⌉     ≡⟨ cong ⌈_/2⌉ (⊤-suc w-1) ⟨
  ⌈ ⊤ w /2⌉           ∎

½≡⌊⊤/2⌋ : ∀ w → .⦃ _ : NonZero w ⦄ → ½ w ≡ ⌊ ⊤ w /2⌋
½≡⌊⊤/2⌋ w@(suc w-1) = begin-equality
  ⊤ w-1               ≡⟨ n≡⌊n+n/2⌋ (⊤ w-1) ⟩
  ⌊ ⊤ w-1 + ⊤ w-1 /2⌋ ≡⟨ cong (λ a → ⌊ ⊤ w-1 + a /2⌋) (+-identityʳ (⊤ w-1)) ⟨
  ⌊ 2 * ⊤ w-1 /2⌋     ≡⟨ cong ⌊_/2⌋ (⊤-suc w-1) ⟨
  ⌊ ⊤ w /2⌋           ∎

⌈⊤/2⌉≡⌊⊤/2⌋ : ∀ w → .⦃ NonZero w ⦄ → ⌈ ⊤ w /2⌉ ≡ ⌊ ⊤ w /2⌋
⌈⊤/2⌉≡⌊⊤/2⌋ w = trans (sym (½≡⌈⊤/2⌉ w)) (½≡⌊⊤/2⌋ w)
