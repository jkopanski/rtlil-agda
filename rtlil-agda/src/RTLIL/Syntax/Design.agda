{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Design where

open import Overture
open import RTLIL.Syntax.Base

import RTLIL.Syntax.Module as Module renaming (Module to t)

record Design : Set where
  constructor mk
  field
    autoidx : Maybe.t ℕ.t
    modules : List.t Module.t

open Design public
