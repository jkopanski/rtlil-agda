{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Base where

import RTLIL.Word.Width as Width

open ℕ hiding (zero; _+_; _*_; t)
open Width

Word : ℕ.t → Set
Word = Fin.t ∘ ⊤

word< : ∀ {w v} → .(v < ⊤ w) → Word w
word< v<⊤ = Fin.fromℕ< v<⊤

toℕ : ∀ {w} → Word w → ℕ.t
toℕ = Fin.toℕ

toℕ<⊤ : ∀ {w} → (word : Word w) → toℕ word < ⊤ w
toℕ<⊤ = Fin.toℕ<n

zero : (w : ℕ.t) → Word w
zero w = word< (>-nonZero⁻¹ (⊤ w))

last : (w : ℕ.t) → Word w
last w = word< (≤-reflexive (sym (suc-pred-⊤ w)))

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
