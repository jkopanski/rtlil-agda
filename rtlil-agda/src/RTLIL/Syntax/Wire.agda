{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Wire where

open import Overture
open import Agda.Builtin.FromNat
open import RTLIL.Syntax.Base

import RTLIL.Syntax.Attributes as Attributes renaming (Attributes to t)

open Function using (_∘_)

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

data Size : Set where
  direct    : Width → Size
  reference : Identifier → Size

instance
  NumberSize : Number Size
  NumberSize .Number.Constraint w = ℕ.NonZero w
  NumberSize .Number.fromNat w ⦃ w≢0 ⦄ = direct (fromNat w)

record Wire : Set where
  constructor mk
  field
    attributes : Attributes.t
    name       : Identifier
    io         : Maybe.t InOut
    width      : Size
    offset     : ℕ.t
    upto       : BitNumbering
    signed     : Signedness

open Wire

instance
  _ = ℕ.number

  WireHasAttributes : Has Attributes.t Wire
  WireHasAttributes .Has.get = Wire.attributes
  WireHasAttributes .Has.set a m = record m { attributes = a }

-- TODO: use Fresh?
fromList : List.t Wire → Map.t Wire
fromList = Map.fromList ∘ List.map (λ w → (w .name) , w)

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


  bus : Identifier → Size → Wire
  bus i w = record
    { attributes = Attributes.empty
    ; name       = i
    ; io         = Maybe.nothing
    ; width      = w
    ; offset     = 0
    ; upto       = MSB
    ; signed     = Unsigned
    }

  iobus : Identifier → Size → InOut → Wire
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

bus : Identifier → Size → Wire
bus i w = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.nothing
  ; width      = w
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }

iobus : Identifier → Size → InOut → Wire
iobus i w io = record
  { attributes = Attributes.empty
  ; name       = i
  ; io         = Maybe.just io
  ; width      = w
  ; offset     = 0
  ; upto       = LSB
  ; signed     = Unsigned
  }
