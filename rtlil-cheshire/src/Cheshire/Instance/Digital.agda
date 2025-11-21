{-# OPTIONS --safe --cubical-compatible #-}
open import Cheshire.Core
open import Prelude

module Cheshire.Instance.Digital where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromString

-- cheshire
import Cheshire.Object.Signatures as Object
import Cheshire.Signatures as Signatures

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
open import RTLIL.Syntax

open List using ([]; _∷_)
open Signatures

instance
  _ = ℕ.number
  _ = String.isString

-- record `Ob (width : Width) : Set where
--   constructor ob
--   field
--     name : Identifier
--     signal : Signal.t

-- open `Ob

data `Ob : ℕ.t → Set where
  `⊤ : `Ob 0
  `bus : ∀ {w} → ⦃ _ : ℕ.NonZero w ⦄ → `Ob w
  `concat : ∀ {w v} → `Ob w → `Ob v → `Ob (w ℕ.+ v)
  -- This won't provide generic coproducts for this categor, but
  -- should be enough to get us coproducts at higher level one, that
  -- can compile to this.
  `mux : ∀ {w} → `Ob w ⊎ `Ob w → `Ob (ℕ.suc w)

instance
  binaryProducts : ∀ {w} → Object.BinaryProducts (`Ob w)
  binaryProducts .Object.BinaryProducts._×_ = λ x y → {!`concat x y!}

record Component (i : ℕ.t) (o : ℕ.t) : Set where
  field
    name : Identifier
    input : `Ob i
    output : `Ob o
    -- module : Module.t

-- signal : ∀ {w} → `Ob w → Signal.t
-- signal o = Signal.simple (o .name)

-- data _⇒_ : Ob u → Ob w → Set where
--   _`∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
--   `id : ∀ {A} → A ⇒ A

-- open Quiver 𝒬

𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬 = mk⇒ {Ob = ℕ.t} λ u v → `Ob u → Circuit (`Ob v)

-- record Interface : Set where
--   constructor iface
--   field
--     wires : List.t Wire.t
--     parameters : Parameters.t

-- -- common wires, interface to the module
-- inputId outputId : Identifier
-- inputId  = "\\INPUT"
-- outputId = "\\OUTPUT"

-- inputParam outputParam : Identifier
-- inputParam  = "\\IN_WIDTH"
-- outputParam = "\\OUT_WIDTH"

-- common : Interface
-- common = record
--   { wires = Wire.iobus inputId  (Wire.reference  inputParam) (Wire.input  1)
--           ∷ Wire.iobus outputId (Wire.reference outputParam) (Wire.output 2)
--           ∷ []

--   ; parameters =  Parameters.mk
--                $ (inputParam  , width 1)
--                ∷ (outputParam , width 1)
--                ∷ []
--   }

-- -- id : ∀ {w} → w ⇒ w
-- -- id {w} input output = record
-- --   { Interface common
-- --   ; name = "$Digital$id"
-- --   ; attributes = Attributes.empty
-- --   ; connections = Connection.simple outputId inputId ∷ []
-- --   ; cells = []
-- --   }

-- -- compose : ∀ {u v w} → v ⇒ w → u ⇒ v → u ⇒ w
-- -- compose {u} {v} {w} g f input output =
-- --   let
-- --     intermediate : `Ob v
-- --     intermediate = ? -- λ where
-- --       -- .name → "intermediate"
-- --     f′ = f input intermediate
-- --     g′ = g intermediate output
-- --     input′  = input .name
-- --     output′ = output .name
-- --     inter′  = intermediate .name
-- --   in record
-- --   { Interface common
-- --   ; name = auto $ "Digital$compose$"
-- --         String.++ getString (g′ .Module.name)
-- --         String.++ getString (f′ .Module.name)
-- --   ; attributes = Attributes.empty
-- --   ; connections = []
-- --   ; cells =
-- --       record
-- --         { attributes = Attributes.empty
-- --         ; type = f′ .Module.name
-- --         ; name = "$f"
-- --         ; parameters = Parameters.empty
-- --         ; connections = Connection.simple inter′ input′ ∷ []
-- --         }
-- --     ∷ record
-- --         { attributes = Attributes.empty
-- --         ; type = g′ .Module.name
-- --         ; name = "$g"
-- --         ; parameters = Parameters.empty
-- --         ; connections = Connection.simple output′ inter′ ∷ []
-- --         }
-- --     ∷ []
-- --   } 

-- -- Digital : Category 𝒬
-- -- Digital = record
-- --   { id = id
-- --   ; _∘_ = compose
-- --   }
