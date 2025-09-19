{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude
open import RTLIL.Syntax.Base

module RTLIL.Syntax.Cell where

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)
import RTLIL.Syntax.Connection as Connection renaming (Connection to t)
import RTLIL.Syntax.Parameters as Parameters renaming (Parameters to t)
import RTLIL.Syntax.Signal     as Signal     renaming (Signal     to t)

record Cell : Set where
  field
    attributes  : Attributes.t
    type        : Identifier
    name        : Identifier
    parameters  : Parameters.t
    connections : List.t Connection.t

instance
  CellHasAttributes : Has Attributes.t Cell
  CellHasAttributes .Has.get = Cell.attributes
  CellHasAttributes .Has.set a m = record m { attributes = a }

  CellHasParameters : Has Parameters.t Cell
  CellHasParameters .Has.get = Cell.parameters
  CellHasParameters .Has.set a m = record m { parameters = a }
