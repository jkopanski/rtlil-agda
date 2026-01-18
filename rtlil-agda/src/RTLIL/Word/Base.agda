{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Base where

open import Overture
open import Tactic.Cong using (cong!; ⌞_⌟)

import Data.Refinement as Refinement renaming (Refinement to t)
import Data.Irrelevant as Irrelevant renaming (Irrelevant to t)
import RTLIL.Word.Width as Width

open × using (_×_)
open Irrelevant using ([_])
open ℕ hiding (zero; t; _+_)
open ℤ using (+_; -[1+_])
open Function using (_∘_)
open Width
open Refinement using (Refinement-syntax; _,_)
open Rel₀ using (no; yes)
open ≤-Reasoning

Word : ℕ.t → Set
Word w = [ value ∈ ℕ.t ∣ value < ⊤ w ]
-- Refinement.t ℕ.t (_< ⊤ w)

pattern ⟦_⟧<_ v v<⊤ = v , [ v<⊤ ]

{-# DISPLAY Irrelevant.[_] t = t #-}
{-# DISPLAY Refinement._,_ v v<⊤ = ⟦ v ⟧< v<⊤ #-}

word< : ∀ {w value} → .(value < ⊤ w) → Word w
word< {_} {value} <⊤ = ⟦ value ⟧< <⊤

infix 10 _#b_
-- kind of a similar to verilog 8'b4,
-- which means 4 encoded in 8 bits
_#b_ : ∀ w m {m<⊤ : Rel₀.True (m <? 2 ^ w)} → Word w
_#b_ w m {m<⊤} rewrite sym (⊤-def w) =
  word< {w} {m} (Rel₀.toWitness m<⊤)

toℕ : ∀ {w} → Word w → ℕ.t
toℕ = Refinement.value

toFin : ∀ {w} → Word w → Fin.t (2 ^ w)
toFin {w} (⟦ _ ⟧< value<⊤) = Fin.fromℕ< (⊤⇒2ʷ ≤-isPreorder value<⊤)

fromFin : ∀ {w} → Fin.t (2 ^ w) → Word w
fromFin {w} i = Fin.toℕ i , [ 2ʷ⇒⊤ ≤-isPreorder (Fin.toℕ<n i) ]

toℕ<⊤ : ∀ {w} → (word : Word w) → toℕ word < ⊤ w
toℕ<⊤ {w} (⟦ value ⟧< v<⊤) = Rel₀.recompute (value <? ⊤ w) v<⊤

zero : (w : ℕ.t) → Word w
zero w = word< (>-nonZero⁻¹ (⊤ w))

last : (w : ℕ.t) → Word w
last w = word< (≤-reflexive (sym (suc-pred-⊤ w)))

cast : ∀ {w v} → .(w ≡ v) → Word w → Word v
cast {w} {v} w≡v (⟦ value ⟧< v<⊤) =
  ⟦ value ⟧< <-≤-trans v<⊤ (≤-reflexive (cong ⊤ w≡v))

0-extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v ℕ.+ w)
0-extend v {w} (⟦ word ⟧< word<⊤ ) =
  ⟦ word ⟧< ≤-trans word<⊤ (⊤[w]≤⊤[v+w] w v)

1-extend : (v : ℕ.t) → ∀ {w} → Word w → Word (v ℕ.+ w)
1-extend v {w} (⟦ value ⟧< value<⊤ ) = ⟦ value ℕ.+ (⊤ v ∸ 1) * ⊤ w ⟧<
  (begin-strict
    value ℕ.+ (⊤ v ∸ 1) * ⊤ w <⟨ +-monoˡ-< _ value<⊤ ⟩
    ⊤ w ℕ.+ (⊤ v ∸ 1) * ⊤ w   ≡⟨ ⊤[w+v]≡⊤[w]+[⊤v∸1]*⊤[w] w v ⟨
    ⊤ (w ℕ.+ v)               ≡⟨ cong ⊤ (+-comm w v) ⟩
    ⊤ (v ℕ.+ w)               ∎)

truncate : (v : ℕ.t) → ∀ {w} → Word w → Word (w ∸ v)
truncate v {w} word =
  ⟦ toℕ word % ⊤ (w ∸ v) ⟧< m%n<n (toℕ word) (⊤ (w ∸ v))

[_]ₜ_ : ∀ {w} → Word w → (v : ℕ.t) → Word (w ∸ v)
[ w ]ₜ v = truncate v w

-- | Split the word at half.
-- split {w} "word" = inj₁ "word"       if word < ½ w
--                    inj₂ "word - ½ w" if word ≥ ½ w
-- See: Fin.splitAt (½ w) word
split :
  ∀ {w} → .⦃ _ : NonZero w ⦄ → Word w →
  Word (w ∸ 1) ⊎ Word (w ∸ 1)
split w@{suc w-1} (⟦ value ⟧< v<⊤ ) with value <? ⊤ (w ∸ 1)
… | yes v<½ = inj₁ $ ⟦ value ⟧< v<½
… | no  v≮½ = inj₂ $ ⟦ value ∸ ⊤ (w ∸ 1) ⟧< (begin-strict
  value ∸ ⊤ w-1             <⟨ ∸-monoˡ-< v<⊤ (≮⇒≥ v≮½) ⟩
  ⊤ w ∸ ⊤ w-1               ≡⟨ cong (_∸ ⊤ w-1) (⊤≡⊤[w-1]+⊤[w-1] w) ⟩
  ⊤ w-1 ℕ.+ ⊤ w-1 ∸ ⊤ w-1   ≡⟨ +-∸-assoc (⊤ w-1) {n = ⊤ w-1} (≤-reflexive refl) ⟩
  ⊤ w-1 ℕ.+ (⊤ w-1 ∸ ⊤ w-1) ≡⟨ cong (⊤ w-1 ℕ.+_) (n∸n≡0 (⊤ w-1)) ⟩
  ⊤ w-1 ℕ.+ 0               ≡⟨ +-identityʳ (⊤ w-1) ⟩
  ⊤ w-1                     ∎)

join-1 : ∀ {w} → Word w ⊎ Word w → Word (suc w)
join-1 {w} = ⊎.[ 0-extend 1 , 1-extend 1 ]

join-1′ :
  ∀ {w} → ⦃ _ : NonZero w ⦄ →
  Word (w ∸ 1) ⊎ Word (w ∸ 1) → Word w
join-1′ {w} word rewrite sym (suc-pred w) = join-1 word

join : ∀ w v → Word w ⊎ Word v → Word (suc (w ℕ.⊔ v))
join w v =
  ⊎.[ cast (cong suc $ sym (m⊔n≡n∸m+m w v)) ∘ 0-extend (suc (v ∸ w))
    , cast (cong suc $ sym (m⊔n≡m∸n+n w v)) ∘ 1-extend (suc (w ∸ v))
    ]

opposite : ∀ {w} → Word w → Word w
opposite {w} (⟦ value ⟧< v<⊤) = ⟦ ⊤ w ∸ suc value ⟧< (begin-strict
  ⊤ w ∸ suc value    ≡⟨ pred[m∸n]≡m∸[1+n] (⊤ w) value ⟨
  pred (⊤ w ∸ value) ≤⟨ pred-mono-≤ (m∸n≤m (⊤ w) value) ⟩
  pred (⊤ w)         ≡⟨ refl ⟩
  ⊤ w ∸ 1            <⟨ ∸-monoʳ-< z<s (>-nonZero⁻¹ (⊤ w)) ⟩
  ⊤ w ∸ 0            ∎)

combine : ∀ {w v} → Word w → Word v → Word (w ℕ.+ v)
combine {w} {v} x y = ⟦ toℕ x ℕ.* ⊤ v ℕ.+ toℕ y ⟧< (begin-strict
  toℕ x ℕ.* ⊤ v ℕ.+ toℕ y       <⟨ +-monoʳ-< (toℕ x * ⊤ v) (toℕ<⊤ y) ⟩
  toℕ x ℕ.* ⊤ v ℕ.+ ⊤ v         ≡⟨ cong! (+-identityʳ (⊤ v)) ⟨
  toℕ x ℕ.* ⊤ v ℕ.+ (⊤ v ℕ.+ 0) ≡⟨ *-distribʳ-+ (⊤ v) (toℕ x) 1 ⟨
  ⌞ toℕ x ℕ.+ 1 ⌟ ℕ.* ⊤ v       ≡⟨ cong! (+-comm (toℕ x) 1) ⟩
  (1 ℕ.+ toℕ x) ℕ.* ⊤ v         ≤⟨ *-monoˡ-≤ (⊤ v) (toℕ<⊤ x) ⟩
  ⊤ w ℕ.* ⊤ v                   ≡⟨ ⊤[w+v]≡⊤[w]*⊤[v] w v ⟨
  ⊤ (w ℕ.+ v)                   ∎)

remQuot : ∀ {w} v → Word (w ℕ.+ v) → Word w × Word v
remQuot {w} v x .proj₁ = ⟦ toℕ x ℕ./ ⊤ v ⟧<
  m<n*o⇒m/o<n (<-≤-trans (toℕ<⊤ x) (≤-reflexive (⊤[w+v]≡⊤[w]*⊤[v] w v)))
remQuot {w} v x .proj₂ = ⟦ toℕ x ℕ.% ⊤ v ⟧<
  m%n<n (toℕ x) (⊤ v)

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
