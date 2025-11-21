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

sigSpec : Identifier × Signal.t → Connection
sigSpec (id , sig) = Signal.simple id ⇐ sig

simple : Identifier → Identifier → Connection
simple sink source = sigSpec (sink , Signal.simple source)
