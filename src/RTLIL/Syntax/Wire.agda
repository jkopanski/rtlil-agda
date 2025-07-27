{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Wire where

open import Agda.Builtin.FromNat
open import RTLIL.Syntax.Base using (Constant; Identifier; module Map; Width)

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)

data BitNumbering : Set where
  MSB LSB : BitNumbering

-- TODO: I have no idea what the nat is here for
data Direction : Set where
  input  : ℕ.t → Direction
  output : ℕ.t → Direction
  inout  : ℕ.t → Direction

  -- "offset": <the lowest bit index in use, if non-0>
  -- "upto": <1 if the port bit indexing is MSB-first>
  -- "signed": <1 if the port is signed>
data Signedness : Set where
  Signed Unsigned : Signedness

record Wire : Set where
  constructor mk
  field
    attributes : Attributes.t
    name       : Identifier
    direction  : Direction
    width      : Width
    offset     : ℕ.t
    upto       : BitNumbering
    signed     : Signedness

open Wire

instance
  _ = ℕ.number

  WireHasAttributes : Attributes.Has Wire
  WireHasAttributes .Attributes.Has.get = Wire.attributes
  WireHasAttributes .Attributes.Has.set a m = record m { attributes = a }

module msb where
  wire : Identifier → Direction → Wire
  wire i d = record
    { attributes = Attributes.empty
    ; name       = i
    ; direction  = d
    ; width      = 1
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

  bus : Identifier → Direction → Width → Wire
  bus i d w = record
    { attributes = Attributes.empty
    ; name       = i
    ; direction  = d
    ; width      = w
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

wire : Identifier → Direction → Wire
wire i d = record
  { attributes = Attributes.empty
  ; name       = i
  ; direction  = d
  ; width      = 1
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

bus : Identifier → Direction → Width → Wire
bus i d w = record
  { attributes = Attributes.empty
  ; name       = i
  ; direction  = d
  ; width      = w
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

