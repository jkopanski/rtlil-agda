{-# OPTIONS --safe #-}

open import Prelude

module RTLIL.Word.Properties where

import RTLIL.Word.Width as Width

open import RTLIL.Word.Base
open Width

2*w≡w*2 : ∀ {w} → (word : Word w) → 2* word ≡ word *2
2*w≡w*2 {w} word = refl
