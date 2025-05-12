{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Base where

import RTLIL.Word.Width as Width

open ℕ hiding (zero; _+_)
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
