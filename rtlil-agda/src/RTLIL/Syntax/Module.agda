{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Module where

open import Overture
open import RTLIL.Syntax.Base

import Relation.Binary.Construct.On as On

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

    wires : Map.t Wire.t
    cells : Map.t Cell.t

    -- TODO:
    -- memories : Map.t Memory
    -- processes : Map.t Process

open Module

empty : Identifier → Module
empty id = record
  { attributes = Attributes.empty
  ; parameters = Parameters.empty
  ; name = id
  ; connections = List.[]
  ; wires = Map.empty
  ; cells = Map.empty
  }

instance
  ModuleHasAttributes : Has Attributes.t Module
  ModuleHasAttributes .Has.get = Module.attributes
  ModuleHasAttributes .Has.set a m = record m { attributes = a }

  ModuleHasParameters : Has Parameters.t Module
  ModuleHasParameters .Has.get = Module.parameters
  ModuleHasParameters .Has.set a m = record m { parameters = a }

-- name needs to be unique for each module
setoid : Rel₂.Setoid 𝕃.0ℓ 𝕃.0ℓ
setoid = On.setoid identifier-setoid name

decSetoid : Rel₂.DecSetoid 𝕃.0ℓ 𝕃.0ℓ
decSetoid = On.decSetoid identifier-decSetoid name
