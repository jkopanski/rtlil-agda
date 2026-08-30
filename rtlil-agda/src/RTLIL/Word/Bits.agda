{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Bits where

open import Overture hiding (¬_)

import Algebra.Lattice as Algebra renaming (BooleanAlgebra to Boolean)
import Data.Vec.Recursive.Relation.Binary.Pointwise as Pointwise

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡; ≡⇒≡×≡)
open import Function.Construct.Composition using (_↔-∘_)
open import Tactic.Cong using (cong!; ⌞_⌟)

open import RTLIL.Word.Base as Word
open import RTLIL.Word.Width
open import RTLIL.Word.Properties as Wordₚ
  using (1↔Bool; Word↔Vecᵣ)

open ℕ
open × using (_×_)
open Function using (_∘_; _∘₂_; _-⟨_⟩-_; _on_; _↔_; mk↔ₛ′)
open Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open Rel₂ using (_≗_; module ≡-Reasoning)

open ≡-Reasoning
open Function.Inverse 1↔Bool renaming (to to toBool; from to fromBool)

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

+↔× : ∀ {w v} → Vec.Rec.t 𝟚.t (w ℕ.+ v) ↔ (Vec.Rec.t 𝟚.t w × Vec.Rec.t 𝟚.t v)
+↔× {w} {v} = mk↔ₛ′
  (Vec.Rec.splitAt w v)
  (×.uncurry $ Vec.Rec.append w v)
  (×.uncurry $ Vec.Rec.splitAt-append-identity w v)
  (Vec.Rec.append-splitAt-identity w v)

cons-homo :
  ∀ w (a : 𝟚.t) (as : Vec.Rec.t 𝟚.t w) →
  from (Vec.Rec.cons w a as) ≡ ×.uncurry combine (×.map (1↔Bool .Func.Inverse.from) from (a , as))
cons-homo zero a [] = Wordₚ.toℕ-injective $ begin
  toℕ (from a)           ≡⟨ *-identityʳ (toℕ (from a)) ⟨
  toℕ (from a) * 1       ≡⟨ cong (toℕ (from a) *_) ⊤-zero ⟨
  toℕ (from a) * ⊤ 0     ≡⟨ +-identityʳ (toℕ (from a) * ⊤ 0) ⟨
  toℕ (from a) * ⊤ 0 + 0 ∎
cons-homo (suc 0) 𝟚.false 𝟚.false = refl
cons-homo (suc 0) 𝟚.false 𝟚.true  = refl
cons-homo (suc 0) 𝟚.true  𝟚.false = Wordₚ.toℕ-injective $ begin
  (⊤ 1 ∸ 1) * ⊤ 1 ≡⟨ Rel₂.cong₂ _*_ ⊤1∸1≡1 ⊤-one ⟩
  1 * 2           ≡⟨ ⊤-one                       ⟨
  ⊤ 1             ≡⟨ +-identityʳ (⊤ 1)           ⟨
  ⊤ 1 + 0         ≡⟨ +-identityʳ (⊤ 1 + 0)       ⟨
  ⊤ 1 + 0 + 0     ∎
cons-homo (suc 0) 𝟚.true  𝟚.true  = Wordₚ.toℕ-injective $ begin
  1 + (⊤ 1 ∸ 1) * ⊤ 1 ≡⟨ cong! (Rel₂.cong₂ _*_ ⊤1∸1≡1 ⊤-one) ⟩
  1 + ⌞ 1 * 2 ⌟       ≡⟨ Rel₂.cong (1 +_) ⊤-one              ⟨
  1 + ⊤ 1             ≡⟨ +-comm 1 (⊤ 1)                      ⟩
  ⊤ 1 + 1             ≡⟨ cong (_+ 1) (+-identityʳ (⊤ 1))     ⟨
  ⊤ 1 + 0 + 1         ∎
cons-homo (2+ w) 𝟚.false (𝟚.false , as) = refl
cons-homo (2+ w) 𝟚.false (𝟚.true  , as) = refl
cons-homo (2+ w) 𝟚.true (𝟚.false  , as) =
  let as′ = Function.Inverse.from Word↔Vecᵣ as
  in Wordₚ.toℕ-injective $ begin
    toℕ as′ + (⊤ 1 ∸ 1) * ⊤ (2+ w) ≡⟨ cong! ⊤1∸1≡1                    ⟩
    toℕ as′ + 1 * ⊤ (2+ w)         ≡⟨ +-comm (toℕ as′) (1 * ⊤ (2+ w)) ⟩
    ⊤ (2+ w) + 0 + toℕ as′         ∎
cons-homo (2+ w) 𝟚.true (𝟚.true   , as) =
  let as′ = Function.Inverse.from Word↔Vecᵣ as
  in Wordₚ.toℕ-injective $ begin
    toℕ as′ + (⊤ 1 ∸ 1) * ⊤ (suc w) + (⊤ 1 ∸ 1) * ⊤ (2+ w)
  ≡⟨ cong! ⊤1∸1≡1 ⟩
    toℕ as′ + (⊤ 1 ∸ 1) * ⊤ (suc w) + 1 * ⊤ (2+ w)
  ≡⟨ +-comm (toℕ as′ + (⊤ 1 ∸ 1) * ⊤ (suc w)) (1 * ⊤ (2+ w)) ⟩
    ⊤ (2+ w) + 0 + (toℕ as′ + (⊤ 1 ∸ 1) * ⊤ (suc w))
  ∎

-- meaning of the `Vec.Rec.append` is the `combine` of meanings
append-homo :
  ∀ w v →
  from ∘ ×.uncurry (Vec.Rec.append w v) ≗ ×.uncurry combine ∘ ×.map from from
append-homo 0       _ _               = refl
append-homo (suc 0) v (x , ys)        = cons-homo v x ys
append-homo (2+ w)  v ((x , xs) , ys) = begin
  from (×.uncurry (Vec.Rec.append (2+ w) v) ((x , xs) , ys))
    ≡⟨⟩
  from (Vec.Rec.append (2+ w) v (x , xs) ys)
    ≡⟨ b.from-cong {w = 2+ w + v} (Vec.Rec.append-cons (suc w) v x xs ys) ⟩
  from (Vec.Rec.cons (suc w + v) x (Vec.Rec.append (suc w) v xs ys))
    ≡⟨ cons-homo (suc (w + v)) x (Vec.Rec.append (suc w) v xs ys) ⟩
  ×.uncurry combine (×.map fromBool from (x , _))
    ≡⟨ cong (combine (fromBool x)) (append-homo (suc w) v (xs , ys)) ⟩
  combine (fromBool x) (combine (from xs) (from ys))
    ≡⟨ Wordₚ.assocˡ-combine (fromBool x) (from xs) (from ys) ⟩
  combine (combine (fromBool x) (from xs)) (from ys)
    ≡⟨ cong (λ u → combine u (from ys)) (cons-homo (suc w) x xs) ⟨
  ×.uncurry combine (×.map from from ((x , xs) , ys))
    ∎
  where module b {w} = Func.Inverse (Word↔Vecᵣ {w})

-- meaning of the `Vec.Rec.splitAt` is the `remQuot` of meaning
splitAt-homo :
  ∀ w v →
  ×.map from from ∘ Vec.Rec.splitAt w v ≗ remQuot v ∘ from
splitAt-homo w v vec =
  let (x , y) = Vec.Rec.splitAt w v vec
  in begin
    ×.map from from (Vec.Rec.splitAt w v vec)
  ≡⟨⟩
    from x , from y
  ≡⟨ Wordₚ.remQuot-combine (from x) (from y) ⟨
    remQuot v (combine (from x) (from y))
  ≡⟨ cong! (append-homo w v (x , y)) ⟨
    remQuot v (from (Vec.Rec.append w v x y))
  ≡⟨ cong! (Vec.Rec.append-splitAt-identity w v vec) ⟩
    remQuot v (from vec)
  ∎

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

module Properties (w : ℕ.t) where
  open import Algebra.Lattice.Properties.BooleanAlgebra (Bits w) public
