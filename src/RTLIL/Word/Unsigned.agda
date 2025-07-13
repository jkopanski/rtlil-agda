{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Unsigned where

open import RTLIL.Word.Base
open import RTLIL.Word.Width
open import RTLIL.Word.Properties

open ℕ hiding (t; _+_)
open ≤-Reasoning

from : ∀ {w n} → .(n < ⊤ w) → Word w
from = word<

to : ∀ {w} → Word w → ℕ.t
to = toℕ

extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v ℕ.+ w)
extend v {w} = 0-extend v

to-extend :
  (v : ℕ.t) → ∀ {w} → (word : Word w) →
  to (extend v word) ≡ to word
to-extend v {width} word = toℕ-0-extend v word

extend-mono-≤ :
  (v : ℕ.t) → ∀ {w} →
  (extend v {w}) Rel₂.Preserves (_≤_ on to) ⟶ (_≤_ on to)
extend-mono-≤ v {_} {x} {y} x≤y = begin
  to (extend v x) ≡⟨ to-extend v x ⟩
  to x            ≤⟨ x≤y ⟩
  to y            ≡⟨ to-extend v y ⟨
  to (extend v y) ∎

extend-mono-< :
  (v : ℕ.t) → ∀ {w} →
  (extend v {w}) Rel₂.Preserves (_<_ on to) ⟶ (_<_ on to)
extend-mono-< v {_} {x} {y} x<y = begin-strict
  to (extend v x) ≡⟨ to-extend v x ⟩
  to x            <⟨ x<y ⟩
  to y            ≡⟨ to-extend v y ⟨
  to (extend v y) ∎

+-correct : ∀ {w} → (a b : Word w) → to (a + b) ≡ to a ℕ.+ to b
+-correct a b = refl
