{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Bits where

open import Overture hiding (¬_)

import Algebra.Lattice as Algebra renaming (BooleanAlgebra to Boolean)
import Data.Vec.Recursive.Relation.Binary.Pointwise as Pointwise

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Function.Construct.Composition using (_↔-∘_)

open import RTLIL.Word.Base
open import RTLIL.Word.Width using (⊤)
open import RTLIL.Word.Properties using (Word↔Vecᵣ)

open ℕ
open Function using (_∘_; _∘₂_; _-⟨_⟩-_; _on_; _↔_; mk↔ₛ′)
open Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)

from : ∀ {w} → Vec.Rec.t 𝟚.t w → Word w
from = Word↔Vecᵣ .Func.Inverse.from

to : ∀ {w} → Word w → Vec.Rec.t 𝟚.t w
to = Word↔Vecᵣ .Func.Inverse.to

Word↔MSB : ∀ {w} → Word w ↔ Vec.t 𝟚.t w
Word↔MSB = Vec.Rec.↔Vec _ ↔-∘ Word↔Vecᵣ

↔reverse : ∀ {a} {A : Set a} {n} → Vec.t A n ↔ Vec.t A n
↔reverse = mk↔ₛ′ Vec.reverse Vec.reverse Vec.reverse-involutive Vec.reverse-involutive

Word↔LSB : ∀ {w} → Word w ↔ Vec.t 𝟚.t w
Word↔LSB = ↔reverse ↔-∘ Word↔MSB

-- standard library provides this for Vector of BooleanAlgebra Carrier
-- in: Algebra.Lattice.Properties.BooleanAlgebra.Expression.lift.
-- I wanted to avoid forcing going through regular Vec.  This looks
-- quite mechanic, perhaps there is some opportunity to contribute to
-- std-lib here.
Bits : ℕ.t → Algebra.Boolean 𝕃.0ℓ 𝕃.0ℓ
Bits n = record
  { Carrier          = Vec.Rec.t 𝟚.t n
  -- Based on comment from Data.Vec.Recursive:
  --   two vectors of known length are definitionally equal
  --   whenever their elements are.  So no need for pointwise?
  ; _≈_              = _≡_
  ; _∨_              = Vec.Rec.zipWith _∨_ n
  ; _∧_              = Vec.Rec.zipWith _∧_ n
  ; ¬_               = Vec.Rec.map ¬_ n
  ; ⊤                = Vec.Rec.replicate n 𝟚-Alg.⊤ -- pure ⊤
  ; ⊥                = Vec.Rec.replicate n 𝟚-Alg.⊥ -- pure ⊥
  ; isBooleanAlgebra = Algebra.isBooleanAlgebraʳ record
    { isDistributiveLattice = Algebra.isDistributiveLatticeʳʲᵐ record
      { isLattice = record
        { isEquivalence = Rel₂.isEquivalence
        ; ∨-comm  = Pointwise-≡⇒≡ n ∘₂ Pointwise.zipWith-comm n 𝟚-Alg.∨-comm
        ; ∨-assoc = λ x → Pointwise-≡⇒≡ n ∘₂ Pointwise.zipWith-assoc n 𝟚-Alg.∨-assoc x
        ; ∨-cong  = Rel₂.cong₂ (Vec.Rec.zipWith _∨_ n)
          -- Pointwise-≡⇒≡ n ∘₂
          --   (≡⇒Pointwise-≡ n -⟨ Pointwise.zipWith-cong n 𝟚-Alg.∨-cong ⟩- ≡⇒Pointwise-≡ n)
        ; ∧-comm  = Pointwise-≡⇒≡ n ∘₂ Pointwise.zipWith-comm n 𝟚-Alg.∧-comm
        ; ∧-assoc = λ x → Pointwise-≡⇒≡ n ∘₂ Pointwise.zipWith-assoc n 𝟚-Alg.∧-assoc x
        ; ∧-cong  = Rel₂.cong₂ (Vec.Rec.zipWith _∧_ n)
        ; absorptive = or-absorbs-and n , and-absorbs-or n
        }
      ; ∨-distribʳ-∧ = or-distribʳ-and n
      }
    ; ∨-complementʳ = or-complement n
    ; ∧-complementʳ = and-complement n
    ; ¬-cong = cong (Vec.Rec.map ¬_ n)
    }
  } where
      module 𝟚-Alg = Algebra.Boolean 𝟚.∨-∧-booleanAlgebra
      open 𝟚-Alg
      or-absorbs-and : ∀ n xs ys → Vec.Rec.zipWith _∨_ n xs (Vec.Rec.zipWith _∧_ n xs ys) ≡ xs
      or-absorbs-and zero 𝟙.tt 𝟙.tt = Rel₂.refl
      or-absorbs-and (suc 0) x y    = ∨-absorbs-∧ x y
      or-absorbs-and (2+ _) (x , xs) (y , ys) = ≡×≡⇒≡ (∨-absorbs-∧ x y , or-absorbs-and _ xs ys)
      and-absorbs-or : ∀ n xs ys → Vec.Rec.zipWith _∧_ n xs (Vec.Rec.zipWith _∨_ n xs ys) ≡ xs
      and-absorbs-or zero 𝟙.tt 𝟙.tt = Rel₂.refl
      and-absorbs-or (suc 0) x y    = ∧-absorbs-∨ x y
      and-absorbs-or (2+ _) (x , xs) (y , ys) = ≡×≡⇒≡ (∧-absorbs-∨ x y , and-absorbs-or _ xs ys)
      and-complement : ∀ n xs → Vec.Rec.zipWith _∧_ n xs (Vec.Rec.map ¬_ n xs) ≡ Vec.Rec.replicate n 𝟚-Alg.⊥
      and-complement zero    𝟙.tt = Rel₂.refl
      and-complement (suc 0) x    = ∧-complementʳ x
      and-complement (2+ _)  (x , xs) = ≡×≡⇒≡ (∧-complementʳ x , and-complement _ xs)
      or-complement : ∀ n xs → Vec.Rec.zipWith 𝟚._∨_ n xs (Vec.Rec.map ¬_ n xs) ≡ Vec.Rec.replicate n 𝟚-Alg.⊤
      or-complement zero    𝟙.tt = Rel₂.refl
      or-complement (suc 0) x    = ∨-complementʳ x
      or-complement (2+ _) (x , xs) = ≡×≡⇒≡
        ( ∨-complementʳ x
        , or-complement _ xs
        )
      or-distribʳ-and :
        ∀ n x y z → Vec.Rec.zipWith _∨_ n (Vec.Rec.zipWith _∧_ n y z) x ≡
          Vec.Rec.zipWith _∧_ n (Vec.Rec.zipWith _∨_ n y x) (Vec.Rec.zipWith _∨_ n z x)
      or-distribʳ-and zero 𝟙.tt 𝟙.tt 𝟙.tt = Rel₂.refl
      or-distribʳ-and (suc 0) x y z = ∨-distribʳ-∧ x y z
      or-distribʳ-and (2+ _) (x , xs) (y , ys) (z , zs) = ≡×≡⇒≡ (∨-distribʳ-∧ x y z , or-distribʳ-and _ xs ys zs)

module _ (w : ℕ.t) where
  open import Algebra.Lattice.Properties.BooleanAlgebra (Bits w) public
