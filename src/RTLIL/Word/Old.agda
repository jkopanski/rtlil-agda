{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Base where

import RTLIL.Word.Width as Width

open ℕ hiding (zero; t)
open ℤ using (+_; -[1+_])
open Width

open import Data.Fin.Relation.Binary.Equality.Cast using (_≈[_]_; module CastReasoning)
open import Tactic.Cong using (cong!; ⌞_⌟)

Word : ℕ.t → Set
Word = Fin.t ∘ ⊤

word< : ∀ {w v} → .(v < ⊤ w) → Word w
word< v<⊤ = Fin.fromℕ< v<⊤

infix 10 _#b_
-- kind of a similar to verilog 8'b4,
-- which means 4 encoded in 8 bits
_#b_ : ∀ w m {m<⊤ : Rel₀.True (m <? 2 ^ w)} → Word w
_#b_ w m {m<⊤} rewrite ⊤-def w = Fin.#_ m {2 ^ w} {m<⊤}
-- word< {w} {m} (Rel₀.toWitness m<⊤)

toℕ : ∀ {w} → Word w → ℕ.t
toℕ = Fin.toℕ

toℕ<⊤ : ∀ {w} → (word : Word w) → toℕ word < ⊤ w
toℕ<⊤ = Fin.toℕ<n

toℕ-#b :
  ∀ {w m} {witness : Rel₀.True (m <? 2 ^ w)} →
  toℕ (_#b_ w m {witness}) ≡ m
toℕ-#b {w} {m} {witness} rewrite ⊤-def w =
  Fin.toℕ-fromℕ< (Rel₀.toWitness witness)

opaque
  unfolding ⊤
  test : toℕ (3 #b 4) ≡ 4
  test = refl

zero : (w : ℕ.t) → Word w
zero w = word< (>-nonZero⁻¹ (⊤ w))

last : (w : ℕ.t) → Word w
last w = word< (≤-reflexive (sym (suc-pred-⊤ w)))

cast : ∀ {w v} → .(eq : w ≡ v) → Word w → Word v
cast w≡v = Fin.cast (cong ⊤ w≡v)

toℕ-cast :
  ∀ {w v} → .(eq : w ≡ v) → (word : Word w) →
  toℕ (cast eq word) ≡ toℕ word
toℕ-cast w≡v = Fin.toℕ-cast (cong ⊤ w≡v)

cast-is-id :
  ∀ {w} → .(eq : w ≡ w) → (word : Word w) →
  cast eq word ≡ word
cast-is-id w≡w = Fin.cast-is-id (cong ⊤ w≡w)

subst-is-cast :
  ∀ {w v} → (eq : w ≡ v) → (word : Word w) →
  Rel₂.subst Word eq word ≡ cast eq word
subst-is-cast refl word = sym (cast-is-id refl word)

cast-trans :
  ∀ {w v u} → .(eq₁ : w ≡ v) .(eq₂ : v ≡ u) → (word : Word w) →
  cast eq₂ (cast eq₁ word) ≡ cast (trans eq₁ eq₂) word
cast-trans w≡v v≡u = Fin.cast-trans (cong ⊤ w≡v) (cong ⊤ v≡u)

t′ = Fin.suc $ Fin.suc $ Fin.zero {0}

t : Fin.t (2 + 3)
t = 2 Fin.↑ʳ t′

t″ : Fin.t 3
t″ = Fin.reduce≥ {2} t (s≤s (s≤s z≤n))

_ : t″ ≡ t′
_ = refl

-- | Append 'v' zeroes
0-extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v + w)
0-extend v {w} word =
  cast (ℕ.+-comm w v) $
    Fin.cast (sym (⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v)) $
      word Fin.↑ˡ ((⊤ v ∸ 1) * ⊤ w)
  -- rewrite ℕ.+-comm v w
  --       | ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v
  --       = word Fin.↑ˡ ((⊤ v ∸ 1) * ⊤ w)

toℕ-0-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (0-extend v word) ≡ toℕ word
toℕ-0-extend v {w} word = begin
  -- rewrite ℕ.+-comm v w
  --       | ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v
  --       = Fin.toℕ-↑ˡ word ((⊤ v ∸ 1) * ⊤ w)

  toℕ (0-extend v word)                 ≡⟨ toℕ-cast (ℕ.+-comm w v) _ ⟩
  Fin.toℕ (Fin.cast
    (sym (⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v))
      ↑ˡ-word)                          ≡⟨ Fin.toℕ-cast _ _ ⟩
  Fin.toℕ ↑ˡ-word                       ≡⟨ Fin.toℕ-↑ˡ _ _ ⟩
  toℕ word                              ∎
  where
    open Rel₂.≡-Reasoning
    ↑ˡ-word = word Fin.↑ˡ ((⊤ v ∸ 1) * ⊤ w)

-- | Append 'v' ones
1-extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v + w)
1-extend v {w} word = Fin.cast
  (sym (⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v w)) $
    (⊤ v ∸ 1) * ⊤ w Fin.↑ʳ word
  -- rewrite ⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v w
  --       = (⊤ v ∸ 1) * ⊤ w Fin.↑ʳ word

toℕ-1-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  toℕ (1-extend v word) ≡ (⊤ v ∸ 1) * ⊤ w + toℕ word
toℕ-1-extend v {w} word = begin
  toℕ (1-extend v word)          ≡⟨ Fin.toℕ-cast _ _ ⟩
  Fin.toℕ ↑ʳ-word                ≡⟨ Fin.toℕ-↑ʳ ((⊤ v ∸ 1) * ⊤ w) word ⟩
  (⊤ v ∸ 1) * ⊤ w + Fin.toℕ word ∎
  where
    open Rel₂.≡-Reasoning
    ↑ʳ-word = (⊤ v ∸ 1) * ⊤ w Fin.↑ʳ word
  -- rewrite ⊤[v+w]≡[⊤v∸1]*⊤[w]+⊤[w] v w
  --       = Fin.toℕ-↑ʳ ((⊤ v ∸ 1) * ⊤ w) word

reduce≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) → .(⊤ (w ∸ 1) ≤ toℕ word) →
  Word (w ∸ 1)
reduce≥ w@{suc w-1} ⦃ w≢0 ⦄ word ⊤[w-1]≤word
  rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
    Fin.reduce≥ word ⊤[w-1]≤word
  -- Fin.reduce≥ (Fin.cast (⊤≡⊤[w-1]+⊤[w-1] w) word) ⊤[w-1]≤word
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
  --   Fin.reduce≥ word ⊤[w-1]≤word

-- | Split the word at half.
-- split {w} "word" = inj₁ "word"       if word < ½ w
--                    inj₂ "word - ½ w" if word ≥ ½ w
-- See: Fin.splitAt (½ w) word
split :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w →
  Word (w ∸ 1) ⊎ Word (w ∸ 1)
split {w@(suc w-1)} ⦃ w≢0 ⦄ word
-- rewrite ⊤-is-suc w = case word of
--   λ { Fin.zero → {!!}
--     ; (Fin.suc word-1) → {!!}
--     }
  = Fin.splitAt (⊤ w-1) $
      Fin.cast (⊤≡⊤[w-1]+⊤[w-1] w) word
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
  --   Fin.splitAt (⊤ w-1) word

join :
  ∀ {w} → Word w ⊎ Word w →
  Word (1 + w)
join {w}
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] (suc w) ⦃ _ ⦄
  --       = Fin.join (⊤ w) (⊤ w)
  = ⊎.[ 0-extend 1 , 1-extend 1 ]

-- splitAt-cast-↑ˡ :
--   ∀ m {p} i n → (eq : p ≡ m) →
--   Fin.splitAt m (Fin.cast eq (i Fin.↑ˡ n)) ≡ inj₁ (Fin.cast eq i)
-- splitAt-cast-↑ˡ (suc m) Fin.zero    n eq = refl
-- splitAt-cast-↑ˡ (suc m) (Fin.suc i) n refl rewrite splitAt-cast-↑ˡ m i n refl = refl

splitAt-cast-↑ʳ :
  ∀ m n {p} i → (eq : p ≡ n) →
  Fin.splitAt m (m Fin.↑ʳ Fin.cast eq i) ≡ inj₂ (Fin.cast eq i)
splitAt-cast-↑ʳ ℕ.zero n i eq = refl
splitAt-cast-↑ʳ (suc m) n i eq rewrite splitAt-cast-↑ʳ m n i eq = refl

split-0-extend :
  ∀ {w} → (word : Word w) →
  split (0-extend 1 word) ≡ inj₁ word
split-0-extend {w} word = begin
  split (0-extend 1 word) ≡⟨⟩
  Fin.splitAt (⊤ w) (Fin.cast eq₀ (0-extend 1 word)) ≡⟨⟩
  Fin.splitAt (⊤ w) (Fin.cast eq₀ $ cast eq₁ $ Fin.cast eq₂ word↑)
    ≡⟨ cong! (Fin.cast-trans eq₂ (cong ⊤ eq₁) word↑) ⟩
  Fin.splitAt (⊤ w) (Fin.cast eq₀ $ Fin.cast eq₁∘eq₂ word↑)
    ≡⟨ cong (λ i → Fin.splitAt (⊤ w) i) (Fin.cast-trans eq₁∘eq₂ eq₀ word↑) ⟩
  Fin.splitAt (⊤ w) (Fin.cast eq₀∘eq₁∘eq₂ word↑)
    ≡⟨ {!Fin.splitAt-↑ˡ!} ⟩
  -- inj₁ (Fin.cast eq₀∘eq₁∘eq₂ word) ≡⟨ ? ⟩
  inj₁ word ∎
  -- rewrite trans (⊤-suc w) (cong (_+_ (⊤ w)) (+-identityʳ (⊤ w)))
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] (suc w) ⦃ _ ⦄
        -- = {!!}
        -- | ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] (suc w) 1 = {!!}
-- begin
--   Fin.splitAt (⊤ w) (Fin.cast _ (0-extend 1 word)) ≡⟨ {!Fin.splitAt-↑ˡ (⊤ w)!} ⟩
--   inj₁ (Fin.cast _ (0-extend 1 word)) ≡⟨ {!!} ⟩
--   inj₁ word ∎
  where open Rel₂.≡-Reasoning
        eq₀ = ⊤≡⊤[w-1]+⊤[w-1] (suc w) ⦃ _ ⦄
        eq₁ = ℕ.+-comm w 1
        eq₂ = sym (⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w 1)
        eq₃ = (⊤ 1 ∸ 1) * ⊤ w
        eq₁∘eq₂ = trans eq₂ (cong ⊤ eq₁)
        eq₀∘eq₁∘eq₂ = trans eq₁∘eq₂ eq₀
        word↑ = word Fin.↑ˡ eq₃
split-join :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → (words : Word w ⊎ Word w) →
  split (join words) ≡ words
split-join {w@(suc w-1)} ⦃ w≢0 ⦄ (inj₁ word) = {!!}
split-join {w@(suc w-1)} ⦃ w≢0 ⦄ (inj₂ word) = {!!}
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄

split-< :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) →
  .(w<½ : toℕ word < ⊤ (w ∸ 1)) →
  split word ≡ inj₁ (word< w<½)
split-< w@{suc w-1} ⦃ w≢0 ⦄ word w<½ =
  {!!}
  -- Fin.splitAt-< (⊤ w-1) (Fin.cast _ word) ? -- w<½
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
  --   Fin.splitAt-< (⊤ w-1) word w<½

split-≥ :
  ∀ {w} → .⦃ _ : NonZero w ⦄ →
  (word : Word w) →
  .(w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
  split word ≡ inj₂ (reduce≥ word w≥½)
split-≥ w@{suc w-1} ⦃ w≢0 ⦄ word w≥½ = {!!}
  -- Fin.splitAt-≥ (⊤ w-1) (Fin.cast _ word) w≥½
  -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ =
  --   Fin.splitAt-≥ (⊤ w-1) word w≥½

opposite-prop :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) →
  toℕ (Fin.opposite word) ≡ ⊤ w ∸ suc (toℕ word)
opposite-prop word = Fin.opposite-prop word

-- | Unsigned interpretation
-- module Unsigned where
--   from : ∀ {w n} → .(n < ⊤ w) → Word w
--   from = word<

--   from′ : ∀ {w} n → .(n <″ ⊤ w) → Word w
--   from′ n = Fin.fromℕ<″ n

--   to : ∀ {w} → Word w → ℕ.t
--   to = toℕ

--   extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v ℕ.+ w)
--   extend v {w} word = Fin.inject≤ word (⊤[w]≤⊤[v+w] w v)

--   to-extend : (v : ℕ.t) → ∀ {w} → (word : Word w) → to (extend v word) ≡ to word
--   to-extend v {width} w = Fin.toℕ-inject≤ w (⊤[w]≤⊤[v+w] width v)

--   extend-mono-≤ :
--     (v : ℕ.t) → ∀ {w} →
--     (extend v {w}) Rel₂.Preserves (_≤_ on toℕ) ⟶ (_≤_ on toℕ)
--   extend-mono-≤ v {w} {x} {y} x≤y = begin
--     toℕ (Fin.inject≤ x _) ≡⟨ Fin.toℕ-inject≤ x _ ⟩
--     toℕ x                 ≤⟨ x≤y ⟩
--     toℕ y                 ≡⟨ Fin.toℕ-inject≤ y _ ⟨
--     toℕ (Fin.inject≤ y _) ∎
--     where open ≤-Reasoning

--   extend-mono-< :
--     (v : ℕ.t) → ∀ {w} →
--     (extend v {w}) Rel₂.Preserves (_<_ on toℕ) ⟶ (_<_ on toℕ)
--   extend-mono-< v {w} {x} {y} x<y = begin-strict
--     Fin.toℕ (Fin.inject≤ x _) ≡⟨ Fin.toℕ-inject≤ x _ ⟩
--     Fin.toℕ x                 <⟨ x<y ⟩
--     Fin.toℕ y                 ≡⟨ Fin.toℕ-inject≤ y _ ⟨
--     Fin.toℕ (Fin.inject≤ y _) ∎
--     where open ≤-Reasoning

--   -- opposite-extend :
--   --   ∀ {w} → .⦃ _ : NonZero w ⦄ → (v : ℕ.t) → (word : Word w) →
--   --   toℕ (Fin.opposite (extend v word)) ≡ toℕ (extend v (Fin.opposite word))
--   -- opposite-extend w@{suc w-1} v word
--   --        -- lhs
--   --   rewrite Fin.opposite-prop (extend v word)
--   --         | Fin.toℕ-inject≤ word (⊤[w]≤⊤[v+w] w v)
--   --        -- rhs
--   --         | Fin.toℕ-inject≤ (Fin.opposite word) (⊤[w]≤⊤[v+w] w v)
--   --         | Fin.opposite-prop word = {!!}

--   to-#b :
--     ∀ {w m} {witness : Rel₀.True (m <? 2 ^ w)} →
--     to (_#b_ w m {witness}) ≡ m
--   to-#b {w} {m} {witness} rewrite ⊤-def w =
--     Fin.toℕ-fromℕ< (Rel₀.toWitness witness)

--   opaque
--     unfolding ⊤
--     test : to (3 #b 4) ≡ 4
--     test = refl

-- | Signed interpretation
-- module Signed where
--   fromNeg : ∀ {w n} → .⦃ _ : NonZero w ⦄ → n < ½ w → Word w
--   fromNeg {w} {n} n<½ = word< top-[1+n]<top
--     where
--       m = ⊤ w ∸ (1 ℕ.+ n)
--       top-[1+n]<top : m < ⊤ w
--       top-[1+n]<top = ∸-monoʳ-< z<s (≤-trans n<½ (<⇒≤ (½<⊤ w)))

--   fromPos : ∀ {w n} → .⦃ _ : ℕ.NonZero w ⦄ → n ℕ.< ½ w → Word w
--   fromPos {w} n<½ = word< (<-trans n<½ (½<⊤ w))

--   from :
--     ∀ {w} {z} → .⦃ _ : NonZero w ⦄ →
--     z ℤ.< + ½ w →
--     z ℤ.> -[1+ ½ w ] →
--     Word w
--   from {z = + _}     n<½ _   = fromPos (ℤ.drop‿+<+ n<½)
--   from {z = -[1+ _ ]} _  n<½ = fromNeg (ℤ.drop‿-<- n<½)

--   to : ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w → ℤ.t
--   to {w} word with split word
--   … | inj₁ n = + Fin.toℕ n
--   … | inj₂ n = -[1+ Fin.toℕ $ Fin.opposite n ]

--   to-< :
--     ∀ {w} → .⦃ _ : NonZero w ⦄ → (word : Word w) → (Unsigned.to word < ⊤ (w ∸ 1)) →
--     to word ≡ + Unsigned.to word
--   to-< {w} word w<½ rewrite split-< word w<½ = cong +_ (Fin.toℕ-fromℕ< w<½)

--   lemma : (v w : ℕ.t) → .⦃ _ : NonZero w ⦄ → suc (v ℕ.+ (w ∸ 1)) ≡ v ℕ.+ w
--   lemma v w = begin
--     suc (v ℕ.+ (w ∸ 1)) ≡⟨ +-suc v (w ∸ 1) ⟨
--     v ℕ.+ suc (w ∸ 1)   ≡⟨ cong (v ℕ.+_) (suc-pred w) ⟩
--     v ℕ.+ w             ∎
--     where open Rel₂.≡-Reasoning

--   extend : ∀ {w} → .⦃ _ : NonZero w ⦄ → (v : ℕ.t) → Word w → Word (v ℕ.+ w)
--   extend w@{suc _} v word with split word
--   … | inj₁ _ = Unsigned.extend v word
--   … | inj₂ _ = Fin.opposite $ Unsigned.extend v $ Fin.opposite word

--   extend-< :
--     ∀ {w} → .⦃ _ : NonZero w ⦄ →
--     (v : ℕ.t) → (word : Word w) → .(w<½ : toℕ word < ⊤ (w ∸ 1)) →
--     extend v word ≡  Unsigned.extend v word
--   extend-< w@{suc _} v word w<½
--     rewrite split-< word w<½ =
--       refl

--   extend-≥ :
--     ∀ {w} → .⦃ _ : NonZero w ⦄ →
--     (v : ℕ.t) → (word : Word w) →
--     .(w≥½ : toℕ word ≥ ⊤ (w ∸ 1)) →
--     extend v word ≡ Fin.opposite (Unsigned.extend v $ Fin.opposite word)
--   extend-≥ w@{suc _} v word w≥½
--     rewrite split-≥ word w≥½ =
--       refl

--   instance
--     extend-nonZero : ∀ {w v} → .⦃ _ : NonZero w ⦄ → NonZero (v ℕ.+ w)
--     extend-nonZero {w} {v} = >-nonZero $ begin-strict
--       0       <⟨ >-nonZero⁻¹ _ ⟩
--       w       ≤⟨ m≤n+m w v ⟩
--       v ℕ.+ w ∎
--       where open ≤-Reasoning

--   lemma₂ :
--     ∀ {n w} → .⦃ _ : NonZero w ⦄ →
--     n < ⊤ (w ∸ 1) →
--     ∀ v → n < ⊤ (v ℕ.+ w ∸ 1)
--   lemma₂ {n} {w} n<w v = begin-strict
--     n                 <⟨ n<w ⟩
--     ⊤ (w ∸ 1)         ≤⟨ ⊤[w]≤⊤[v+w] (w ∸ 1) v ⟩
--     ⊤ (v ℕ.+ (w ∸ 1)) ≡⟨ cong ⊤ (+-∸-assoc v (>-nonZero⁻¹ w)) ⟨
--     ⊤ (v ℕ.+ w ∸ 1)   ∎
--     where open ≤-Reasoning

--   lemma₃ :
--     ∀ {w} → .⦃ _ : NonZero w ⦄ → {word : Word w} →
--     toℕ word < ⊤ (w ∸ 1) →
--     ∀ v → toℕ (Unsigned.extend v word) < ⊤ (v ℕ.+ w ∸ 1)
--   lemma₃ {w} ⦃ w≢0 ⦄ {word} w<½ v = ≤-<-trans
--     (≤-reflexive (Unsigned.to-extend v word))
--     (lemma₂ w<½ v)
--     -- begin-strict
--     -- toℕ (Unsigned.extend v word) ≡⟨ Unsigned.to-extend v word ⟩
--     -- toℕ word <⟨ lemma₂ w<½ v ⟩
--     -- ⊤ (v ℕ.+ w ∸ 1) ∎
--     -- where open ≤-Reasoning

--   -- to-extend :
--   --   ∀ v → ∀ {w} → .⦃ _ : NonZero w ⦄ →
--   --   (word : Word w) →
--   --   to (extend v word) ≡ to word
--   -- to-extend v {w} ⦃ w≢0 ⦄ word
--   --   with toℕ word <? ⊤ (w ∸ 1)
--   -- … | Rel₀.yes w<½
--   --        -- lhs
--   --   rewrite extend-< v word w<½
--   --         | split-< (Unsigned.extend v word) (lemma₃ w<½ v)
--   --        -- rhs
--   --         | split-< word w<½
--   --         | Fin.toℕ-fromℕ< w<½ = cong +_ $ let open Rel₂.≡-Reasoning in begin
--   --           toℕ (Fin.fromℕ< (lemma₃ w<½ v)) ≡⟨ Fin.toℕ-fromℕ< (lemma₃ w<½ v) ⟩
--   --           toℕ (Unsigned.extend v word)    ≡⟨ Unsigned.to-extend v word ⟩
--   --           toℕ word                        ∎
--   -- … | Rel₀.no w≮½
--   --        -- lhs
--   --   rewrite extend-≥ v word (≮⇒≥ w≮½)
--   --         | split-≥ (Fin.opposite $ Unsigned.extend v $ Fin.opposite word) {!≮⇒≥ w≮½!} = {!!}
--   --        -- -- rhs
--   --        --  | split-≥ word (≮⇒≥ w≮½) = cong -[1+_] {!!}

--     -- rewrite ⊤≡⊤[w-1]+⊤[w-1] w ⦃ w≢0 ⦄ = {!!}
--   --   with toℕ (extend v word) <? ⊤ (v ℕ.+ w ∸ 1) | toℕ word <? ⊤ (w ∸ 1)
--   -- … | Rel₀.yes ew<½ | Rel₀.yes w<½
--   --   rewrite split-< (extend v word) ew<½
--   --         | split-< word w<½ = {!!}
--   -- … | Rel₀.yes ew<½ | Rel₀.no w≮½
--   --   rewrite split-< (extend v word) ew<½
--   --         | split-≥ word (≮⇒≥ w≮½) = {!!}
--   -- … | Rel₀.no  ew<½ | y = {!!}

--   --   rewrite split-< (extend v word) w<½ with Unsigned.to word <? ⊤ (w ∸ 1) = {!!}
--   -- … | Rel₀.no  w≮½ = let w≥½ = ≮⇒≥ w≮½ in {!!}
--   --   with split (extend v word) | split word
--   -- ... | inj₁ ex | inj₁ x = {!!}
--   -- ... | inj₁ ex | inj₂ x = {!!}
--   -- ... | inj₂ ex | inj₁ x = {!!}
--   -- ... | inj₂ ex | inj₂ x = {!!}

--   -- … | Rel₀.yes w<½
--   --   rewrite split-< (extend v word) w<½ = {!!}
--   -- … | Rel₀.no  w≮½ = let w≥½ = ≮⇒≥ w≮½ in {!!}

--   opaque
--     unfolding ⊤

--     test : to (3 #b 4) ≡ -[1+ 3 ]
--     test = refl

--     test′ : to (3 #b 3) ≡ + 3
--     test′ = refl

--     test″ : to (extend 2 $ (3 #b 3)) ≡ + 3
--     test″ = refl

--     t' : Unsigned.to (extend 0 $ (3 #b 4)) ≡ 4
--     t' = refl

--     t'' : Unsigned.to (extend 1 $ (3 #b 4)) ≡ 12
--     t'' = refl

--     test‴ : to (extend 2 (3 #b 4)) ≡ -[1+ 3 ]
--     test‴ = refl

-- infixl 7 _/2 _*2 2*_
-- _/2 : ∀ {w} → Word w → Word (w ∸ 1)
-- _/2 {ℕ.zero} _ = zero 0
-- _/2 w@{suc w-1} word = Fin.quotient 2 (Fin.cast (⊤-suc-comm w-1) word)

-- 2*_ : ∀ {w} → Word w → Word (suc w)
-- 2*_ {w} word = word< (begin-strict
--   2 ℕ.* toℕ word <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
--   2 ℕ.* ⊤ w      ≡⟨ ⊤-suc w ⟨
--   ⊤ (suc w)      ∎)
--   where open ≤-Reasoning

-- _*2 : ∀ {w} → Word w → Word (suc w)
-- _*2 {w} word = Fin.fromℕ< (begin-strict
--   2 ℕ.* (toℕ word) <⟨ *-monoʳ-< 2 (toℕ<⊤ word) ⟩
--   2 ℕ.* ⊤ w        ≡⟨ *-comm 2 (⊤ w) ⟩
--   ⊤ w ℕ.* 2        ≡⟨ ⊤-suc-comm w ⟨
--   ⊤ (suc w)        ∎)
--   where open ≤-Reasoning

-- _+_ : ∀ {v w} → Word v → Word w → Word (suc (v ℕ.⊔ w))
-- _+_ {v} {w} a b = word< {_} {toℕ a ℕ.+ toℕ b} (begin-strict
--   toℕ a ℕ.+ toℕ b   <⟨ +-mono-< (toℕ<⊤ a) (toℕ<⊤ b) ⟩
--   ⊤ v ℕ.+ ⊤ w       ≤⟨ +-mono-≤ lemma₁ lemma₂ ⟩
--   ⊤ v⊔w ℕ.+ (⊤ v⊔w) ≡⟨ cong (⊤ v⊔w ℕ.+_) (+-identityʳ (⊤ v⊔w)) ⟨
--   2 ℕ.* ⊤ v⊔w       ≡⟨ ⊤-suc v⊔w ⟨
--   ⊤ (suc v⊔w)       ∎)
--   where open ≤-Reasoning
--         v⊔w = v ℕ.⊔ w
--         lemma₁ : ⊤ v ≤ ⊤ (v ℕ.⊔ w)
--         lemma₁ = ⊤-mono-≤ (m≤m⊔n v w)
--         lemma₂ : ⊤ w ≤ ⊤ (v ℕ.⊔ w)
--         lemma₂ = ⊤-mono-≤ (m≤n⊔m v w)
