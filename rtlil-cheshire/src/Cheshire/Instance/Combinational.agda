{-# OPTIONS --safe --cubical-compatible --guardedness #-}
open import Overture
open import Cheshire.Core

module Cheshire.Instance.Combinational where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Instance.Words as Words
import Cheshire.Instance.RTLIL as RTLIL

import RTLIL.Cells as Cells
import RTLIL.Word as Word

open Object

private
  variable
    w v : ℕ.t

module Syntax where

  infix 4 _↠_
  data _↠_ : ℕ.t → ℕ.t → Set where
    false : ⊤ ↠ w
    true  : .⦃ ℕ.NonZero w ⦄ → ⊤ ↠ w
    not : w ↠ w
    neg : .⦃ ℕ.NonZero w ⦄ → w ↠ w
    last?        : w ↠ 1
    zero? ¬zero? : w ↠ 1
    add : w × w ↠ ℕ.suc w
    -- and or xor xnor : {!!} ↠ {!!}

  𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
  𝒬 = mk⇒ _↠_

  open _↠_ public

open Syntax._↠_

module Meaning where

  𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
  𝒬 = Words.𝒬

  open Words.Signatures using (category)
  open Category.Signature category using (_∘_)

  F : ∀ {w v} → Syntax.𝒬 .Hom w v → Words.𝒬 .Hom w v
  F {_} {v} false = Function.const (Word.zero v)
  F {_} {v} true  = Function.const (Word.last v)
  F not = Cells.not-meaning
  F neg = Cells.neg-meaning
  F last?  = Cells.reduce_and-meaning
  F zero?  = Cells.logic_not-meaning
  F ¬zero? = Cells.reduce_or-meaning
  F add = Cells.add-meaning

  H : Morphism.t Syntax.𝒬 Words.𝒬
  H = record { F₀ = Function.id; F₁ = F }

  open Morphism.t H public

instance
  eq : Equivalence Syntax.𝒬 𝕃.0ℓ
  eq = Morphism.equivalence Words.eq Meaning.H

module Realization where

  𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
  𝒬 = RTLIL.𝒬

  open RTLIL.Signatures using (_∘_)

  F : ∀ {w v} → Syntax.𝒬 .Hom w v → RTLIL.𝒬 .Hom w v
  F false = Cells.pulldown
  F true  = Cells.pullup
  F not = Cells.not
  F neg = Cells.neg
  F last?  = Cells.reduce_and
  F zero?  = Cells.logic_not
  F ¬zero? = Cells.reduce_or
  F add = Cells.add

  H : Morphism.t Syntax.𝒬 RTLIL.𝒬
  H = record { F₀ = Function.id; F₁ = F }

  open Morphism.t H public
