{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Operations where

open import Overture

import RTLIL.Word.Width as Width
import RTLIL.Word.Base as Word
import RTLIL.Word.Properties as Wordₚ

open ℕ hiding (zero; t; _+_)
open Width
open Word
open Wordₚ
open Rel₀ using (yes; no)
open ≤-Reasoning

------------------------------------------------------------------------
-- Unary

opposite : ∀ {w} → Word w → Word w
opposite {w} (⟦ value ⟧< v<⊤) = ⟦ ⊤ w ∸ suc value ⟧< (begin-strict
  ⊤ w ∸ suc value    ≡⟨ pred[m∸n]≡m∸[1+n] (⊤ w) value ⟨
  pred (⊤ w ∸ value) ≤⟨ pred-mono-≤ (m∸n≤m (⊤ w) value) ⟩
  pred (⊤ w)         ≡⟨ refl ⟩
  ⊤ w ∸ 1            <⟨ ∸-monoʳ-< z<s (>-nonZero⁻¹ (⊤ w)) ⟩
  ⊤ w ∸ 0            ∎)

infixl 6 _+_
-- Addition is deliberately chosen to accept the same width
-- operands. It's up to the user to perform appropriate extension
-- (signed or not).  The same goes for the resulting type, there is no
-- information loss, it's user responsibility to truncate the result
-- if needed.
_+_ : ∀ {w} → Word w → Word w → Word (suc w)
_+_ {w} x y = ⟦ toℕ x ℕ.+ toℕ y ⟧< (begin-strict
  toℕ x ℕ.+ toℕ y <⟨ +-mono-< (toℕ<⊤ x) (toℕ<⊤ y) ⟩
  ⊤ w ℕ.+ ⊤ w     ≡⟨ ⊤≡⊤[w-1]+⊤[w-1] (suc w) ⟨
  ⊤ (suc w)       ∎)

infixl 6 _+′_
-- This one is more general but it will require casting of the word
-- width. I'm not sure if this is a good trade-off.
_+′_ : ∀ {w v} → Word w → Word v → Word (suc (w ℕ.⊔ v))
_+′_ {w} {v} x y = ⟦ toℕ x ℕ.+ toℕ y ⟧<
  (begin-strict
    toℕ x ℕ.+ toℕ y
  <⟨ +-mono-< (toℕ<⊤ x) (toℕ<⊤ y) ⟩
    ⊤ w ℕ.+ ⊤ v
  ≤⟨ +-mono-≤ (⊤-mono-≤ (m≤m⊔n w v)) (⊤-mono-≤ (m≤n⊔m w v)) ⟩
    ⊤ (w ℕ.⊔ v) ℕ.+ ⊤ (w ℕ.⊔ v)
  ≡⟨ ⊤≡⊤[w-1]+⊤[w-1] (suc (w ℕ.⊔ v)) ⟨
    ⊤ (suc (w ℕ.⊔ v))
  ∎)

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

