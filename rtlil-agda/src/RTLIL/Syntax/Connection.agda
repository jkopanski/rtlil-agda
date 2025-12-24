{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude
open import RTLIL.Syntax.Base

module RTLIL.Syntax.Connection where

import RTLIL.Syntax.Signal as Signal renaming (Signal to t)

open × using (_×_)

record Connection : Set where
  constructor _⇐_
  field
    sink   : Signal.t
    source : Signal.t

simple : Identifier → Identifier → Connection
simple sink source = Signal.simple sink ⇐ Signal.simple source
