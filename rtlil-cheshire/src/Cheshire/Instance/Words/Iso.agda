{-# OPTIONS --safe --cubical-compatible #-}
module Cheshire.Instance.Words.Iso where

open import Overture
open import Cheshire.Core

-- cheshire
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Homomorphism to t)

-- rtlil-agda
module Word where
  open import RTLIL.Word public
  open import RTLIL.Word.Properties public
  import RTLIL.Word.Bits as B
  module Bits = B

import Cheshire.Instance.Sets as Sets renaming (Sets to t)
import Cheshire.Instance.Bits as Bits renaming (Bits to t)
import Cheshire.Instance.Words as Words renaming (Words to t)

module Word↔Bits {w} = Function.Inverse (Word.Word↔Vecᵣ {w})
open Word↔Bits

open Function using (_∘₂_)
open Rel₂.≡-Reasoning

toBits : Homomorphism.Cartesian
  Words.Structures.eq Bits.Structures.eq
  Words.Signatures.cartesian Bits.Signatures.cartesian
toBits = record
  { morphism = record
    { F₀ = Function.id
    ; F₁ = λ f → to ⊙ f ⊙ from
    }
  ; isHomomorphism = record
    { F-resp-≈ = λ f≈g vec → to-cong (f≈g (from vec)) }
  ; isFunctor = record
    { F-resp-id = strictlyInverseˡ
    ; F-resp-∘ = λ {f = f} {g} vec → ≡-sym $
        to-cong (≡-cong g (strictlyInverseʳ (f (from vec))))
    }
  ; isCartesian = record
    { ⊤-iso = record
      { from = Function.id ; to = Function.id
      ; isIso = record { isoˡ = λ _ → ≡-refl ; isoʳ = λ _ → ≡-refl }
      }
    ; ×-iso = λ w v → record
      { from = Function.id ; to = Function.id
      ; isIso = record { isoˡ = λ _ → ≡-refl ; isoʳ = λ _ → ≡-refl }
      }
    ; F-resp-! = λ _ → ≡-refl
    ; F-resp-π₁ = λ {w} {v} vec → ≡-trans
        (≡-sym (cong (to ⊙ proj₁) (Word.Bits.splitAt-homo w v vec)))
        (strictlyInverseˡ _)
      -- let (X , Y) = Vec.Rec.splitAt w v vec
      -- in begin
      --   to (W.π₁ (from vec)) ≡⟨⟩
      --   to (proj₁ (Word.remQuot v (from vec)))
      -- ≡⟨ cong (to ⊙ proj₁) (Word.Bits.splitAt-homo w v vec) ⟨
      --   to (proj₁ (from X , from Y)) ≡⟨⟩
      --   to (from X)
      -- ≡⟨ strictlyInverseˡ X ⟩
      --   X ≡⟨⟩
      --   proj₁ (X , Y) ≡⟨⟩
      --   proj₁ (Vec.Rec.splitAt w v vec) ≡⟨⟩
      --   B.π₁ vec
      -- ∎
    ; F-resp-π₂ = λ {w} {v} vec → ≡-trans
        (≡-sym (cong (to ⊙ proj₂) (Word.Bits.splitAt-homo w v vec)))
        (strictlyInverseˡ _)
    ; F-resp-⟨⟩ = λ {w} {v} {x} f g vec → begin
        -- to (W.⟨ f , g ⟩ $ from vec) ≡⟨⟩
        -- to (×.uncurry Word.combine (×.< f , g > $ from vec)) ≡⟨⟩
        to (Word.combine (f (from vec)) (g (from vec)))
      ≡⟨ Rel₂.cong₂ (to ∘₂ Word.combine)
          (strictlyInverseʳ (f (from vec)))
          (strictlyInverseʳ (g (from vec))) ⟨
        to (Word.combine (from (to (f (from vec)))) (from (to (g (from vec)))))
      ≡⟨ ≡-cong to (Word.Bits.append-homo w v _) ⟨
        to (from (Vec.Rec.append w v (to (f (from vec))) (to (g (from vec)))))
      ≡⟨ strictlyInverseˡ _ ⟩
        -- Vec.Rec.append w v (to (f (from vec))) (to (g (from vec))) ≡⟨⟩
        -- (×.uncurry (Vec.Rec.append w v)) (to (f (from vec)) , to (g (from vec))) ≡⟨⟩
        (×.uncurry (Vec.Rec.append w v)) (×.< to ⊙ f ⊙ from , to ⊙ g ⊙ from > vec)
        -- B.⟨ to ⊙ f ⊙ from , to ⊙ g ⊙ from ⟩ vec
      ∎
    }
  }

fromBits : Homomorphism.Cartesian
  Bits.Structures.eq Words.Structures.eq
  Bits.Signatures.cartesian Words.Signatures.cartesian
fromBits = record
  { morphism = record
    { F₀ = Function.id
    ; F₁ = λ f → from ⊙ f ⊙ to
    }
  ; isHomomorphism = record
    { F-resp-≈ = λ f≈g word → from-cong (f≈g (to word)) }
  ; isFunctor = record
    { F-resp-id = strictlyInverseʳ
    ; F-resp-∘ = λ {f = f} {g} word → ≡-sym $
        from-cong (≡-cong g (strictlyInverseˡ (f (to word))))
    }
  ; isCartesian = record
    { ⊤-iso = record
      { from = Function.id ; to = Function.id
      ; isIso = record { isoˡ = λ _ → ≡-refl ; isoʳ = λ _ → ≡-refl }
      }
    ; ×-iso = λ w v → record
      { from = Function.id ; to = Function.id
      ; isIso = record { isoˡ = λ _ → ≡-refl ; isoʳ = λ _ → ≡-refl }
      }
    ; F-resp-! = λ _ → ≡-refl
    ; F-resp-π₁ = λ {w} {v} word → ≡-cong proj₁ $ ≡-trans
        (Word.Bits.splitAt-homo w v (to word))
        (≡-cong (Word.remQuot v) (strictlyInverseʳ word))
      -- let (X , Y) = Word.remQuot v word
      -- in begin
      --   from (B.π₁ (to word)) ≡⟨⟩
      --   from (proj₁ (Vec.Rec.splitAt w v (to word))) ≡⟨⟩
      --   proj₁ (×.map from from (Vec.Rec.splitAt w v (to word)))
      -- ≡⟨ ≡-cong proj₁ (Word.Bits.splitAt-homo w v (to word)) ⟩
      --   proj₁ (Word.remQuot v (from (to word)))
      -- ≡⟨ ≡-cong (proj₁ ⊙ Word.remQuot v) (strictlyInverseʳ word) ⟩
      --   proj₁ (Word.remQuot v word) ≡⟨⟩
      --   W.π₁ word ∎
    ; F-resp-π₂ = λ {w} {v} word → ≡-cong proj₂ $ ≡-trans
        (Word.Bits.splitAt-homo w v (to word))
        (≡-cong (Word.remQuot v) (strictlyInverseʳ word))
    ; F-resp-⟨⟩ = λ {w} {v} f g word → Word.Bits.append-homo w v (f (to word) , g (to word))
    }
  }
