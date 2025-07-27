{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Cell where

open import RTLIL.Syntax.Base

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)
import RTLIL.Syntax.Parameters as Parameters renaming (Parameters to t)
import RTLIL.Syntax.Signal     as Signal     renaming (Signal     to t)

record Cell : Set where
  field
    attributes  : Attributes.t
    type        : Identifier
    name        : Identifier
    connections : Map.t Signal.t
    parameters  : Parameters.t

instance
  CellHasAttributes : Attributes.Has Cell
  CellHasAttributes .Attributes.Has.get = Cell.attributes
  CellHasAttributes .Attributes.Has.set a m = record m { attributes = a }

  CellHasParameters : Parameters.Has Cell
  CellHasParameters .Parameters.Has.get = Cell.parameters
  CellHasParameters .Parameters.Has.set a m = record m { parameters = a }
