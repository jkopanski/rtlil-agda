{-# OPTIONS --allow-unsolved-metas #-}
-- Collection of stuff that I thought would be working but is somehow
-- flawed.
open import Prelude

module RTLIL.Word.Wrong where

open import RTLIL.Word.Base
open import RTLIL.Word.Properties

import RTLIL.Word.Width as Width

open ℕ hiding (zero; t; _+_)
open Width
open Rel₀ using (no; yes)
open ≤-Reasoning

-- Those 2 joins are technically correct, I'm not sure about their
-- usefulness given that generic splitAt isn't
join-⊔-⊓ : ∀ w v → Word (w ⊔ v) ⊎ Word (w ⊓ v) → Word (suc (w ⊔ v))
join-⊔-⊓ w v =
  ⊎.[ 0-extend 1
    , cast (cong suc $ ∣m-n∣+m⊓n≡m⊔n w v) ∘ 1-extend (suc ∣ w - v ∣)
    ]

join-⊓-⊔ : ∀ w v → Word (w ⊓ v) ⊎ Word (w ⊔ v) → Word (suc (w ⊔ v))
join-⊓-⊔ w v =
  ⊎.[ cast (cong suc $ ∣m-n∣+m⊓n≡m⊔n w v) ∘ 0-extend (suc ∣ w - v ∣)
    , 1-extend 1
    ]

-- While those definitions seems ok, the truncation of the lower width
-- will loose information that we won't be able to recreate later
splitAt :
  ∀ w {v} → Word (suc (w ⊔ v)) →
  Word w ⊎ Word v
splitAt w {v} word with toℕ word <? ⊤ (w ⊔ v)
… | yes x<w⊔v = inj₁ $ cast (n⊔m∸[m∸n]≡n v w) $ [ word ]ₜ suc (v ∸ w)
… | no  x≮w⊔v = inj₂ $ cast (m⊔n∸[m∸n]≡n w v) $ [ word ]ₜ suc (w ∸ v)

splitAt-⊔-⊓ :
  ∀ w {v} → Word (suc (w ⊔ v)) →
  Word (w ⊔ v) ⊎ Word (w ⊓ v)
splitAt-⊔-⊓ w {v} word with toℕ word <? ⊤ (w ℕ.⊔ v)
… | yes x<w⊔v = inj₁ $ ⟦ toℕ word ⟧< x<w⊔v
… | no  x≮w⊔v = inj₂ $ cast (m⊔n∸∣m-n∣≡m⊓n w v) $ [ word ]ₜ suc ∣ w - v ∣

splitAt-⊓-⊔ :
  ∀ w {v} → Word (suc (w ⊔ v)) →
  Word (w ⊓ v) ⊎ Word (w ⊔ v)
splitAt-⊓-⊔ w {v} word with toℕ word <? ⊤ (w ℕ.⊔ v)
… | yes x<w⊔v = inj₁ $ {!!}
… | no  x≮w⊔v = inj₂ $ ⟦ toℕ word ∸ ⊤ (w ⊔ v) ⟧< {!!}

splitAt-0-extend :
  ∀ w v → (word : Word w) →
  splitAt w (cast (cong suc $ sym (m⊔n≡n∸m+m w v)) $ 0-extend (suc (v ∸ w)) word) ≡ inj₁ word
splitAt-0-extend w v word
  with toℕ (cast (cong suc $ sym (m⊔n≡n∸m+m w v)) $ 0-extend (suc (v ∸ w)) word) <? ⊤ (w ⊔ v)
… | yes word<⊤ rewrite truncate-0-extend (suc (v ∸ w)) word = cong inj₁ $ toℕ-injective $ begin-equality
  toℕ word % ⊤ (w ⊔ v ∸ (v ∸ w)) ≡⟨ %-congʳ (cong ⊤ (n⊔m∸[m∸n]≡n v w)) ⟩
  toℕ word % ⊤ w                 ≡⟨ m<n⇒m%n≡m (toℕ<⊤ word) ⟩
  toℕ word                       ∎
… | no  word≮⊤ = Rel₀.contradiction (0-extend<⊤[w⊔v] v word) word≮⊤
  where module ≡ = Rel₂.≡-Reasoning

splitAt-1-extend :
  ∀ w v → (word : Word v) →
  splitAt w (cast (cong suc $ sym (m⊔n≡m∸n+n w v)) $ 1-extend (suc (w ∸ v)) word) ≡ inj₂ word
splitAt-1-extend w v word
  with toℕ (cast (cong suc $ sym (m⊔n≡m∸n+n w v)) $ 1-extend (suc (w ∸ v)) word) <? ⊤ (w ⊔ v)
… | yes word<⊤ = Rel₀.contradiction word<⊤ (≤⇒≯ (1-extend≥⊤[w⊔v] w v word))
… | no  word≮⊤ rewrite truncate-1-extend (suc (w ∸ v)) word = cong inj₂ $ toℕ-injective $ begin-equality
    (toℕ word ℕ.+ (⊤ (suc w-v) ∸ 1) * ⊤ v) % ⊤ (w ⊔ v ∸ w-v)
  ≡⟨ %-congʳ (cong ⊤ (m⊔n∸[m∸n]≡n w v)) ⟩
    (toℕ word ℕ.+ (⊤ (suc w-v) ∸ 1) * ⊤ v) % ⊤ v
  ≡⟨ [m+kn]%n≡m%n (toℕ word) (⊤ (suc w-v) ∸ 1) (⊤ v) ⟩
    toℕ word % ⊤ v
  ≡⟨ m<n⇒m%n≡m (toℕ<⊤ word) ⟩
    toℕ word
  ∎ where w-v = w ∸ v

splitAt-join : ∀ w v i → splitAt w (join w v i) ≡ i
splitAt-join w v (inj₁ i) = splitAt-0-extend w v i
splitAt-join w v (inj₂ i) = splitAt-1-extend w v i

