{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Bits where

open import Overture
open import RTLIL.Word.Base
open import RTLIL.Word.Width

open ℕ
open Rel₀ using (no; yes)

2^n≢0 : ∀ {n} {i : Fin.t n} → NonZero (2 ^ (Fin.toℕ i))
2^n≢0 {n} {i} = m^n≢0 2 (Fin.toℕ i) ⦃ ≢-nonZero λ () ⦄

divMod : ∀ {w} → (word : Word w) → (i : ℕ.t) → DivMod (toℕ word) (⊤ i)
divMod {w} word i rewrite ⊤-def i =
  (ℕ._divMod_) (toℕ word) (2 ^ i) ⦃ m^n≢0 2 i ⦄

testBit : ∀ {w} → Word w → Fin.t w → 𝟚.t
testBit {w} word i with 2 ∣? toℕ word ℕ.div (⊤ $ Fin.toℕ i)
… | yes 2|d = 𝟚.false
… | no  2∤d = 𝟚.true

-- from : ∀ {w} → Vec.t 𝟚.t w → Word w
-- from = {!!}

to : ∀ {w} → Word w → Vec.t 𝟚.t w
to word = Vec.tabulate (testBit word)
