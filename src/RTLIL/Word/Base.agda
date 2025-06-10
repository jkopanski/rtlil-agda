{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Base where

import RTLIL.Word.Width as Width

open ℕ hiding (zero; _+_)
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

reduce≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) → .(⊤ (w ∸ 1) ≤ toℕ word) →
  Word (w ∸ 1)
reduce≥ w@{suc w-1} ⦃ w≢0 ⦄ word ⊤[w-1]≤word
  rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
    Fin.reduce≥ word ⊤[w-1]≤word

-- | Split the word at half.
-- split {w} "word" = inj₁ "word"       if word < ½ w
--                    inj₂ "word - ½ w" if word ≥ ½ w
-- See: Fin.splitAt (½ w) word
split :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w →
  Word (w ∸ 1) ⊎ Word (w ∸ 1)
split w@{suc w-1} ⦃ w≢0 ⦄ word
  rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
    Fin.splitAt (⊤ w-1) word

split-< :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) → .(w<½ : toℕ word < ⊤ (w ∸ 1)) →
  split word ≡ inj₁ (word< w<½)
split-< w@{suc w-1} ⦃ w≢0 ⦄ word w<½
  rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
    Fin.splitAt-< (⊤ w-1) word w<½

split-≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) →
  .(w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
  split word ≡ inj₂ (reduce≥ word w≥½)
split-≥ w@{suc w-1} ⦃ w≢0 ⦄ word w≥½
  rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
    Fin.splitAt-≥ (⊤ w-1) word w≥½

-- | Unsigned interpretation
module Unsigned where
  from : ∀ {w n} → .(n < ⊤ w) → Word w
  from = word<

  from′ : ∀ {w} n → .(n <″ ⊤ w) → Word w
  from′ n = Fin.fromℕ<″ n

  to : ∀ {w} → Word w → ℕ.t
  to = toℕ

  extend : ∀ {w} → (v : ℕ.t) → Word w → Word (v ℕ.+ w)
  extend {w} v word = Fin.inject≤ word (⊤[w]<⊤[v+w] w v)

  to-extend : ∀ v → ∀ {w} → (word : Word w) → to (extend v word) ≡ to word
  to-extend v {width} w = Fin.toℕ-inject≤ w (⊤[w]<⊤[v+w] width v)

  to-#b :
    ∀ {w m} {witness : Rel₀.True (m <? 2 ^ w)} →
    to (_#b_ w m {witness}) ≡ m
  to-#b {w} {m} {witness} rewrite ⊤-def w =
    Fin.toℕ-fromℕ< (Rel₀.toWitness witness)

  opaque
    unfolding ⊤
    test : to (3 #b 4) ≡ 4
    test = refl

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
  from {z = + _}     n<½ _   = fromPos (ℤ.drop‿+<+ n<½)
  from {z = -[1+ _ ]} _  n<½ = fromNeg (ℤ.drop‿-<- n<½)

  to : ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w → ℤ.t
  to {w} word with split word
  … | inj₁ n = + Fin.toℕ n
  … | inj₂ n = -[1+ Fin.toℕ $ Fin.opposite n ]

  to-< :
    ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) → (Unsigned.to word < ⊤ (w ∸ 1)) →
    to word ≡ + Unsigned.to word
  to-< {w} word w<½ rewrite split-< word w<½ = cong +_ (Fin.toℕ-fromℕ< w<½)
    
  lemma : (v w : ℕ.t) → .⦃ _ : NonZero w ⦄ → suc (v ℕ.+ (w ∸ 1)) ≡ v ℕ.+ w
  lemma v w = begin
    suc (v ℕ.+ (w ∸ 1)) ≡⟨ +-suc v (w ∸ 1) ⟨
    v ℕ.+ suc (w ∸ 1)   ≡⟨ cong (v ℕ.+_) (suc-pred w) ⟩
    v ℕ.+ w             ∎
    where open Rel₂.≡-Reasoning

  extend : ∀ {w} → .⦃ _ : NonZero w ⦄ → (v : ℕ.t) → Word w → Word (v ℕ.+ w)
  extend w@{suc _} v word with split word
  … | inj₁ _ = Unsigned.extend v word
  … | inj₂ _ = Fin.opposite $ Unsigned.extend v $ Fin.opposite word

  extend-< :
    ∀ {w} → .⦃ _ : NonZero w ⦄ →
    (v : ℕ.t) → (word : Word w) → .(w<½ : toℕ word < ⊤ (w ∸ 1)) →
    extend v word ≡  Unsigned.extend v word
  extend-< w@{suc _} v word w<½
    rewrite split-< word w<½ =
      refl

  extend-≥ :
    ∀ {w} → .⦃ _ : NonZero w ⦄ →
    (v : ℕ.t) → (word : Word w) →
    .(w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
    extend v word ≡ Fin.opposite (Unsigned.extend v $ Fin.opposite word)
  extend-≥ w@{suc _} v word w≥½
    rewrite split-≥ word w≥½ =
      refl

  instance
    extend-nonZero : ∀ {w v} → .⦃ _ : NonZero w ⦄ → NonZero (v ℕ.+ w)
    extend-nonZero {w} {v} = >-nonZero $ begin-strict
      0       <⟨ >-nonZero⁻¹ _ ⟩
      w       ≤⟨ m≤n+m w v ⟩
      v ℕ.+ w ∎
      where open ≤-Reasoning

  to-extend :
    ∀ v → ∀ {w} → .⦃ _ : NonZero w ⦄ →
    (word : Word w) →
    to (extend v word) ≡ to word
  to-extend v {w} ⦃ w≢0 ⦄ word
    with toℕ word <? ⊤ (w ∸ 1)
  … | Rel₀.yes w<½
    rewrite extend-< v word w<½ = {!!}
    -- rewrite extend-< v word w<½ | split-< word w<½ = {!!}
  … | Rel₀.no w≮½  = {!!}
  
    -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ = {!!}
  --   with toℕ (extend v word) <? ⊤ (v ℕ.+ w ∸ 1) | toℕ word <? ⊤ (w ∸ 1)
  -- … | Rel₀.yes ew<½ | Rel₀.yes w<½
  --   rewrite split-< (extend v word) ew<½
  --         | split-< word w<½ = {!!}
  -- … | Rel₀.yes ew<½ | Rel₀.no w≮½
  --   rewrite split-< (extend v word) ew<½
  --         | split-≥ word (≮⇒≥ w≮½) = {!!}
  -- … | Rel₀.no  ew<½ | y = {!!}

  --   rewrite split-< (extend v word) w<½ with Unsigned.to word <? ⊤ (w ∸ 1) = {!!}
  -- … | Rel₀.no  w≮½ = let w≥½ = ≮⇒≥ w≮½ in {!!}
  --   with split (extend v word) | split word
  -- ... | inj₁ ex | inj₁ x = {!!}
  -- ... | inj₁ ex | inj₂ x = {!!}
  -- ... | inj₂ ex | inj₁ x = {!!}
  -- ... | inj₂ ex | inj₂ x = {!!}

  -- … | Rel₀.yes w<½
  --   rewrite split-< (extend v word) w<½ = {!!}
  -- … | Rel₀.no  w≮½ = let w≥½ = ≮⇒≥ w≮½ in {!!}

  opaque
    unfolding ⊤

    test : to (3 #b 4) ≡ -[1+ 3 ]
    test = refl

    test′ : to (3 #b 3) ≡ + 3
    test′ = refl

    test″ : to (extend 2 $ (3 #b 3)) ≡ + 3
    test″ = refl

    t' : Unsigned.to (extend 0 $ (3 #b 4)) ≡ 4
    t' = refl

    t'' : Unsigned.to (extend 1 $ (3 #b 4)) ≡ 12
    t'' = refl

    test‴ : to (extend 2 (3 #b 4)) ≡ -[1+ 3 ]
    test‴ = refl

infixl 7 _/2 _*2 2*_
_/2 : ∀ {w} → Word w → Word (w ∸ 1)
_/2 {ℕ.zero} _ = zero 0
_/2 w@{suc w-1} word = Fin.quotient 2 (Fin.cast (⊤-suc-comm w-1) word)

2*_ : ∀ {w} → Word w → Word (suc w)
2*_ {w} word = word< (begin-strict
  2 * toℕ word <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
  2 * ⊤ w ≡⟨ ⊤-suc w ⟨
  ⊤ (suc w) ∎)
  where open ≤-Reasoning

_*2 : ∀ {w} → Word w → Word (suc w)
_*2 {w} word = Fin.fromℕ< (begin-strict
  2 * (toℕ word) <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
  2 * ⊤ w ≡⟨ *-comm 2 (⊤ w) ⟩
  ⊤ w * 2 ≡⟨ ⊤-suc-comm w ⟨
  ⊤ (suc w) ∎)
  where open ≤-Reasoning

_+_ : ∀ {v w} → Word v → Word w → Word (suc (v ℕ.⊔ w))
_+_ {v} {w} a b = word< {_} {toℕ a ℕ.+ toℕ b} (begin-strict
  toℕ a ℕ.+ toℕ b   <⟨ +-mono-< (toℕ<⊤ a) (toℕ<⊤ b) ⟩
  ⊤ v ℕ.+ ⊤ w       ≤⟨ +-mono-≤ lemma₁ lemma₂ ⟩
  ⊤ v⊔w ℕ.+ (⊤ v⊔w) ≡⟨ cong (⊤ v⊔w ℕ.+_) (+-identityʳ (⊤ v⊔w)) ⟨
  2 * ⊤ v⊔w         ≡⟨ ⊤-suc v⊔w ⟨
  ⊤ (suc v⊔w)       ∎)
  where open ≤-Reasoning
        v⊔w = v ℕ.⊔ w
        lemma₁ : ⊤ v ≤ ⊤ (v ℕ.⊔ w)
        lemma₁ = ⊤-mono-≤ (m≤m⊔n v w)
        lemma₂ : ⊤ w ≤ ⊤ (v ℕ.⊔ w)
        lemma₂ = ⊤-mono-≤ (m≤n⊔m v w)
