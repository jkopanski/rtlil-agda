{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Wire where

open import Agda.Builtin.FromNat
open import RTLIL.Syntax.Base using (Constant; Has; Identifier; module Map; Width)

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)

data BitNumbering : Set where
  MSB LSB : BitNumbering

-- The natural number is the index of the input/output port that this
-- wire corresponds to
data InOut : Set where
  input  : ℕ.t → InOut
  output : ℕ.t → InOut
  inout  : ℕ.t → InOut

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
    io         : Maybe.t InOut
    width      : Width
    offset     : ℕ.t
    upto       : BitNumbering
    signed     : Signedness

open Wire

instance
  _ = ℕ.number

  WireHasAttributes : Has Attributes.t Wire
  WireHasAttributes .Has.get = Wire.attributes
  WireHasAttributes .Has.set a m = record m { attributes = a }

module msb where
  wire : Identifier → Wire
  wire i = record
    { attributes = Attributes.empty
    ; name       = i
    ; io         = Maybe.nothing
    ; width      = 1
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

  iowire : Identifier → InOut → Wire
  iowire i io = record
    { attributes = Attributes.empty
    ; name       = i
    ; io         = Maybe.just io
    ; width      = 1
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }


  bus : Identifier → Width → Wire
  bus i w = record
    { attributes = Attributes.empty
    ; name       = i
    ; io         = Maybe.nothing
    ; width      = w
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

  iobus : Identifier → Width → InOut → Wire
  iobus i w io = record
    { attributes = Attributes.empty
    ; name       = i
    ; io         = Maybe.just io
    ; width      = w
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

wire : Identifier → Wire
wire i = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.nothing
  ; width      = 1
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

iowire : Identifier → InOut → Wire
iowire i io = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.just io
  ; width      = 1
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

bus : Identifier → Width → Wire
bus i w = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.nothing
  ; width      = w
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

iobus : Identifier → Width → InOut → Wire
iobus i w io = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.just io
  ; width      = w
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }
