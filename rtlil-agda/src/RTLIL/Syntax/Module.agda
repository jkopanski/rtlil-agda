{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude
open import RTLIL.Syntax.Base

module RTLIL.Syntax.Module where

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)
import RTLIL.Syntax.Cell       as Cell       renaming (Cell       to t)
import RTLIL.Syntax.Connection as Connection renaming (Connection to t)
import RTLIL.Syntax.Parameters as Parameters renaming (Parameters to t)
import RTLIL.Syntax.Signal     as Signal     renaming (Signal     to t)
import RTLIL.Syntax.Wire       as Wire       renaming (Wire       to t)

record Module : Set where
  field
    name : Identifier
    attributes : Attributes.t
    parameters : Parameters.t
    connections : List.t Connection.t

    wires : List.t Wire.t
    cells : List.t Cell.t

    -- TODO:
    -- memories : Map.t Memory
    -- processes : Map.t Process

instance
  ModuleHasAttributes : Attributes.Has Module
  ModuleHasAttributes .Attributes.Has.get = Module.attributes
  ModuleHasAttributes .Attributes.Has.set a m = record m { attributes = a }

  ModuleHasParameters : Parameters.Has Module
  ModuleHasParameters .Parameters.Has.get = Module.parameters
  ModuleHasParameters .Parameters.Has.set a m = record m { parameters = a }
