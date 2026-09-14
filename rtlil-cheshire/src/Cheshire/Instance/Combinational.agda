{-# OPTIONS --safe --cubical-compatible --guardedness #-}
open import Overture hiding (¬_)
open import Cheshire.Core hiding (¬_)

module Cheshire.Instance.Combinational where

-- stdlib
import Algebra.Lattice as Algebra renaming (BooleanAlgebra to Boolean)

-- cheshire
import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Kan.Lift as Kan

-- rtlil-cheshire
import Cheshire.Instance.Words as Words
import Cheshire.Instance.RTLIL as RTLIL
import Cheshire.Instance.Words.Iso as Iso
import RTLIL.Cells as Cells

module Word where
  open import RTLIL.Word renaming (Word to t) public
  open import RTLIL.Word.Properties public

  private
    variable
      w v : ℕ.t

  module Bits where
    open import RTLIL.Word.Bits renaming (Bits to t) public
    module +↔× {w} v = Func.Inverse (RTLIL.Word.Bits.+↔× {w} {v})

    uncurry : ∀ {x} →
      (Vec.Rec.t 𝟚.t w → Vec.Rec.t 𝟚.t v → Vec.Rec.t 𝟚.t x) →
      Vec.Rec.t 𝟚.t (w ℕ.+ v) → Vec.Rec.t 𝟚.t x
    uncurry {_} {v} f = ×.uncurry f ⊙ (+↔×.to v)

  module ↔Bool = Func.Inverse 1↔Bool
  module +↔× {w} v = Func.Inverse (+↔× {w} {v})

  uncurry : ∀ {x} → (t w → t v → t x) → t (w ℕ.+ v) → t x
  uncurry {w} {v} {x} f = ×.uncurry f ⊙ (+↔×.to v)

open Function using (_∘₂_)
open Object

module Lift = Kan.Lift Iso.LiftBits

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
    -- bitwise
    and or xor xnor : w × w ↠ w
    -- bitwise folds
    reduce_and reduce_or reduce_xor reduce_xnor : w ↠ 1
    -- arithmetic
    add : w × w ↠ ℕ.suc w

  𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
  𝒬 = mk⇒ _↠_

  open _↠_ public

open Syntax._↠_

module Meaning where

  𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
  𝒬 = Words.𝒬

  open Words.Signatures using (category)
  open Category.Signature category using (_∘_)

  private module 𝟚-Alg = Algebra.Boolean 𝟚.∨-∧-booleanAlgebra

  F : ∀ {w v} → Syntax.𝒬 .Hom w v → Words.𝒬 .Hom w v
  F {_} {v} false = Function.const (Word.zero v)
  F {_} {v} true  = Function.const (Word.last v)
  F not = Word.opposite
  F neg = Word.truncate 1 ⊙ (Word._+ Word.one) ⊙ Word.opposite
  F last?  = Word.↔Bool.from ⊙ Rel₀.isYes ⊙ Word.last?
  F zero?  = Word.↔Bool.from ⊙ Rel₀.isYes ⊙ Word.zero?
  F ¬zero? = Word.↔Bool.from ⊙ Rel₀.isNo  ⊙ Word.zero?
  -- bitwise
  F {_} {v} and  = Lift.L.₁ (Word.Bits.uncurry _∧_)
    where open Algebra.Boolean (Word.Bits.t v)
  F {_} {v} or   = Lift.L.₁ (Word.Bits.uncurry _∨_)
     where open Algebra.Boolean (Word.Bits.t v)
  F {_} {v} xor  = Lift.L.₁ (Word.Bits.uncurry _⊕_)
     where open Word.Bits.Properties v
  F {_} {v} xnor = Lift.L.₁ (¬_ ⊙ Word.Bits.uncurry _⊕_)
    where open Word.Bits.Properties v
          open Algebra.Boolean (Word.Bits.t v)
  -- bitwise folds
  F {w} {_} reduce_and  = Lift.L.₁ $
    Vec.Rec.foldr {P = const 𝟚.t} 𝟚.false Function.id (const 𝟚-Alg._∧_) w
  F {w} {_} reduce_or   = Lift.L.₁ $
    Vec.Rec.foldr {P = const 𝟚.t} 𝟚.false Function.id (const 𝟚-Alg._∨_) w
  F {w} {_} reduce_xor  = Lift.L.₁ $
    Vec.Rec.foldr {P = const 𝟚.t} 𝟚.false Function.id (const 𝟚._xor_) w
  F {w} {_} reduce_xnor = Lift.L.₁ $
    Vec.Rec.foldr {P = const 𝟚.t} 𝟚.false Function.id (const (𝟚-Alg.¬_ ∘₂ 𝟚._xor_)) w
  -- arithmetic
  F add = ×.uncurry Word._+_ ⊙ Word.remQuot _

  H : Morphism.t Syntax.𝒬 Words.𝒬
  H = record { F₀ = Function.id; F₁ = F }

  open Morphism.t H public

instance
  eq : Equivalence Syntax.𝒬 𝕃.0ℓ
  eq = Morphism.equivalence Words.Structures.eq Meaning.H

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
  -- bitwise
  F and  = Cells.and
  F or   = Cells.or
  F xor  = Cells.xor
  F xnor = Cells.xnor
  -- bitwise folds
  F reduce_and  = Cells.reduce_and
  F reduce_or   = Cells.reduce_or
  F reduce_xor  = Cells.reduce_xor
  F reduce_xnor = Cells.reduce_xnor
  -- arithmetic
  F add = Cells.add

  H : Morphism.t Syntax.𝒬 RTLIL.𝒬
  H = record { F₀ = Function.id; F₁ = F }

  open Morphism.t H public
