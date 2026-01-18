{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Connection where

open import Overture
open import RTLIL.Syntax.Base

import RTLIL.Syntax.Signal as Signal renaming (Signal to t)

open × using (_×_)

record Connection : Set where
  constructor _⇐_
  field
    sink   : Signal.t
    source : Signal.t

simple : Identifier → Identifier → Connection
simple sink source = Signal.simple sink ⇐ Signal.simple source
