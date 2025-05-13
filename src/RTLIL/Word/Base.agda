{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Base where

import RTLIL.Word.Width as Width

open ℕ hiding (zero; _+_; _*_; t)
open ℤ using (+_; -[1+_])
open Width

Word : ℕ.t → Set
Word = Fin.t ∘ ⊤

word< : ∀ {w v} → .(v < ⊤ w) → Word w
word< v<⊤ = Fin.fromℕ< v<⊤

infix 10 _#b_
-- kind of a similar to verilog 8'b4,
-- which means 4 encoded in 8 bits
_#b_ : ∀ w m {m<⊤ : Rel₀.True (m <? 2 ^ w)} → Word w
_#b_ w m {m<⊤} rewrite ⊤-def w = Fin.#_ m {2 ^ w} {m<⊤}
-- word< {w} {m} (Rel₀.toWitness m<w)

toℕ : ∀ {w} → Word w → ℕ.t
toℕ = Fin.toℕ

toℕ<⊤ : ∀ {w} → (word : Word w) → toℕ word < ⊤ w
toℕ<⊤ = Fin.toℕ<n

zero : (w : ℕ.t) → Word w
zero w = word< (>-nonZero⁻¹ (⊤ w))

last : (w : ℕ.t) → Word w
last w = word< (≤-reflexive (sym (suc-pred-⊤ w)))

-- | Unsigned interpretation
module Unsigned where
  from : ∀ {w n} → .(n < ⊤ w) → Word w
  from = word<

  from′ : ∀ {w} n → .(n <″ ⊤ w) → Word w
  from′ n = Fin.fromℕ<″ n

  to : ∀ {w} → Word w → ℕ.t
  to = toℕ

-- | Signed interpretation
module Signed where
  fromNeg : ∀ {w n} → .⦃ _ : NonZero w ⦄ → n < ½ w → Word w
  fromNeg {w} {n} n<½ = word< top-[1+n]<top
    where
      m = ⊤ w ∸ (1 ℕ.+ n)
      top-[1+n]<top : m < ⊤ w
      top-[1+n]<top = ∸-monoʳ-< z<s (≤-trans n<½ (<⇒≤ (½<⊤ w)))

  fromPos : ∀ {w n} → .⦃ _ : ℕ.NonZero w ⦄ → n ℕ.< ½ w → Word w
  fromPos {w} n<½ = word< (<-trans n<½ (½<⊤ w))

  from :
    ∀ {w} {z} → .⦃ _ : NonZero w ⦄ →
    z ℤ.< + ½ w →
    z ℤ.> -[1+ ½ w ] →
    Word w
  from {z = + _}     (n<½) _     = fromPos (ℤ.drop‿+<+ n<½)
  from {z = -[1+ _ ]} _    (n<½) = fromNeg (ℤ.drop‿-<- n<½)

  to : ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w → ℤ.t
  to {w} word
    rewrite Rel₂.sym (⌊n/2⌋+⌈n/2⌉≡n (⊤ w))
    with Fin.splitAt (⌊ ⊤ w /2⌋) word
  … | inj₁ n = + Fin.toℕ n
  … | inj₂ n = -[1+ Fin.toℕ $ Fin.opposite n ]

  opaque
    unfolding ⊤

    test : to (3 #b 4) ≡ -[1+ 3 ]
    test = refl

infixl 7 _/2 _*2 2*_
_/2 : ∀ {w} → Word w → Word (w ∸ 1)
_/2 {ℕ.zero} _ = zero 0
_/2 w@{suc w-1} word = Fin.quotient 2 (Fin.cast (⊤-suc-comm w-1) word)

2*_ : ∀ {w} → Word w → Word (suc w)
2*_ {w} word = word< (begin-strict
  2 ℕ.* toℕ word <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
  2 ℕ.* ⊤ w      ≡⟨ ⊤-suc w ⟨
  ⊤ (suc w)      ∎)
  where open ≤-Reasoning

_*2 : ∀ {w} → Word w → Word (suc w)
_*2 {w} word = Fin.fromℕ< (begin-strict
  2 ℕ.* (toℕ word) <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
  2 ℕ.* ⊤ w        ≡⟨ *-comm 2 (⊤ w) ⟩
  ⊤ w ℕ.* 2        ≡⟨ ⊤-suc-comm w ⟨
  ⊤ (suc w)        ∎)
  where open ≤-Reasoning

_+_ : ∀ {v w} → Word v → Word w → Word (suc (v ℕ.⊔ w))
_+_ {v} {w} a b = word< {_} {toℕ a ℕ.+ toℕ b} (begin-strict
  toℕ a ℕ.+ toℕ b   <⟨ +-mono-< (toℕ<⊤ a) (toℕ<⊤ b) ⟩
  ⊤ v ℕ.+ ⊤ w       ≤⟨ +-mono-≤ lemma₁ lemma₂ ⟩
  ⊤ v⊔w ℕ.+ (⊤ v⊔w) ≡⟨ cong (⊤ v⊔w ℕ.+_) (+-identityʳ (⊤ v⊔w)) ⟨
  2 ℕ.* ⊤ v⊔w       ≡⟨ ⊤-suc v⊔w ⟨
  ⊤ (suc v⊔w)       ∎)
  where open ≤-Reasoning
        v⊔w = v ℕ.⊔ w
        lemma₁ : ⊤ v ≤ ⊤ (v ℕ.⊔ w)
        lemma₁ = ⊤-mono-≤ (m≤m⊔n v w)
        lemma₂ : ⊤ w ≤ ⊤ (v ℕ.⊔ w)
        lemma₂ = ⊤-mono-≤ (m≤n⊔m v w)
