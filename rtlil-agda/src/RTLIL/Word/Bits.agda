{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Bits where

open import Overture hiding (¬_)

import Algebra.Lattice as Algebra renaming (BooleanAlgebra to Boolean)
import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise

open import Function.Construct.Composition using (_↔-∘_)

open import RTLIL.Word.Base
open import RTLIL.Word.Width using (⊤)
open import RTLIL.Word.Properties using (Word↔Vecᵣ)

open ℕ
open Function using (_↔_; mk↔ₛ′)

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
        ; ∨-comm  = or-comm n
        ; ∨-assoc = or-assoc n
        ; ∨-cong  = Rel₂.cong₂ (Vec.Rec.zipWith _∨_ n)
        ; ∧-comm  = and-comm n
        ; ∧-assoc = and-assoc n
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
      or-comm : ∀ n x y → Vec.Rec.zipWith _∨_ n x y ≡ Vec.Rec.zipWith _∨_ n y x
      or-comm zero    𝟙.tt 𝟙.tt = Rel₂.refl
      or-comm (suc 0) x    y    = ∨-comm x y
      or-comm (2+ _) (x , xs) (y , ys) = Pointwise.≡×≡⇒≡ (∨-comm x y , or-comm _ xs ys)
      or-assoc :
        ∀ n x y z → Vec.Rec.zipWith _∨_ n (Vec.Rec.zipWith _∨_ n x y) z ≡
          Vec.Rec.zipWith _∨_ n x (Vec.Rec.zipWith _∨_ n y z)
      or-assoc zero 𝟙.tt 𝟙.tt 𝟙.tt = Rel₂.refl
      or-assoc (suc 0) x y z = ∨-assoc x y z
      or-assoc (2+ _) (x , xs) (y , ys) (z , zs) = Pointwise.≡×≡⇒≡ (∨-assoc x y z , or-assoc _ xs ys zs)
      and-comm : ∀ n x y → Vec.Rec.zipWith _∧_ n x y ≡ Vec.Rec.zipWith _∧_ n y x
      and-comm zero    𝟙.tt 𝟙.tt = Rel₂.refl
      and-comm (suc 0) x    y    = ∧-comm x y
      and-comm (2+ _) (x , xs) (y , ys) = Pointwise.≡×≡⇒≡ (∧-comm x y , and-comm _ xs ys)
      and-assoc :
        ∀ n x y z → Vec.Rec.zipWith _∧_ n (Vec.Rec.zipWith _∧_ n x y) z ≡
          Vec.Rec.zipWith _∧_ n x (Vec.Rec.zipWith _∧_ n y z)
      and-assoc zero 𝟙.tt 𝟙.tt 𝟙.tt = Rel₂.refl
      and-assoc (suc 0) x y z = ∧-assoc x y z
      and-assoc (2+ _) (x , xs) (y , ys) (z , zs) = Pointwise.≡×≡⇒≡ (∧-assoc x y z , and-assoc _ xs ys zs)
      or-absorbs-and : ∀ n xs ys → Vec.Rec.zipWith _∨_ n xs (Vec.Rec.zipWith _∧_ n xs ys) ≡ xs
      or-absorbs-and zero 𝟙.tt 𝟙.tt = Rel₂.refl
      or-absorbs-and (suc 0) x y    = ∨-absorbs-∧ x y
      or-absorbs-and (2+ _) (x , xs) (y , ys) = Pointwise.≡×≡⇒≡ (∨-absorbs-∧ x y , or-absorbs-and _ xs ys)
      and-absorbs-or : ∀ n xs ys → Vec.Rec.zipWith _∧_ n xs (Vec.Rec.zipWith _∨_ n xs ys) ≡ xs
      and-absorbs-or zero 𝟙.tt 𝟙.tt = Rel₂.refl
      and-absorbs-or (suc 0) x y    = ∧-absorbs-∨ x y
      and-absorbs-or (2+ _) (x , xs) (y , ys) = Pointwise.≡×≡⇒≡ (∧-absorbs-∨ x y , and-absorbs-or _ xs ys)
      and-complement : ∀ n xs → Vec.Rec.zipWith _∧_ n xs (Vec.Rec.map ¬_ n xs) ≡ Vec.Rec.replicate n 𝟚-Alg.⊥
      and-complement zero    𝟙.tt = Rel₂.refl
      and-complement (suc 0) x    = ∧-complementʳ x
      and-complement (2+ _)  (x , xs) = Pointwise.≡×≡⇒≡ (∧-complementʳ x , and-complement _ xs)
      or-complement : ∀ n xs → Vec.Rec.zipWith 𝟚._∨_ n xs (Vec.Rec.map ¬_ n xs) ≡ Vec.Rec.replicate n 𝟚-Alg.⊤
      or-complement zero    𝟙.tt = Rel₂.refl
      or-complement (suc 0) x    = ∨-complementʳ x
      or-complement (2+ _) (x , xs) = Pointwise.≡×≡⇒≡
        ( ∨-complementʳ x
        , or-complement _ xs
        )
      or-distribʳ-and :
        ∀ n x y z → Vec.Rec.zipWith _∨_ n (Vec.Rec.zipWith _∧_ n y z) x ≡
          Vec.Rec.zipWith _∧_ n (Vec.Rec.zipWith _∨_ n y x) (Vec.Rec.zipWith _∨_ n z x)
      or-distribʳ-and zero 𝟙.tt 𝟙.tt 𝟙.tt = Rel₂.refl
      or-distribʳ-and (suc 0) x y z = ∨-distribʳ-∧ x y z
      or-distribʳ-and (2+ _) (x , xs) (y , ys) (z , zs) = Pointwise.≡×≡⇒≡ (∨-distribʳ-∧ x y z , or-distribʳ-and _ xs ys zs)

module _ (w : ℕ.t) where
  open import Algebra.Lattice.Properties.BooleanAlgebra (Bits w) public
