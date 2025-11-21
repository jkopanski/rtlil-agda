{-# OPTIONS --safe --cubical-compatible --guardedness #-}
module Cheshire.Instance.RTLIL where

open import Cheshire.Core

-- stdlib
import Codata.Guarded.Stream as Stream renaming (Stream to t)
import Data.Product as Prod
import Data.List.Fresh.Membership.Setoid as Membership
import Effect.Monad as Monad
import Effect.Monad.State as State renaming (State to t)
import Effect.Monad.State.Instances
import Effect.Monad.Identity.Instances

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromString
open import Data.List.Fresh.Relation.Unary.Any using (any?)
open import Data.List.Fresh.Relation.Unary.Any.Properties using (¬Any⇒All; Any⇒¬All)
open import Data.List.Fresh.Relation.Unary.All.Properties using (fromAll)

-- cheshire
import Cheshire.Object.Signatures as Object
import Cheshire.Signatures as Signatures

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
open import RTLIL.Syntax

-- rtlil-cheshire
import Cheshire.Instance.Words as Words renaming (Words to t)

open Function renaming (_∘_ to _⊙_)
open Membership Module.setoid using (_∈_)
open Signatures
open Signal using ([_⋯_])

instance
  _ = ℕ.number
  _ = String.isString

Modules : Set
Modules = List.Fresh.t Module.t _≉_
  where open Rel₂.DecSetoid Module.decSetoid

Identifiers : Set
Identifiers = Stream.t ℕ.t

record S : Set where
  field
    -- | Circuit being constructed
    circuit : Module.t
    -- | Modules that are instantiated as cells
    dependencies : Modules
    -- | Supply of fresh names for auto identifiers
    idSupply     : Identifiers

open S

empty : Identifier → S
empty id = record
  { circuit = Module.empty id
  ; dependencies = List.Fresh.[]
  ; idSupply = Stream.nats
  }

CircuitM : Set → Set
CircuitM = State.t S

open Monad.RawMonad ⦃ … ⦄ public
open State.RawMonadState ⦃ … ⦄ public

withDeps : (Modules → Modules) → CircuitM 𝟙.t
withDeps f = modify (λ s → record s { dependencies = f (s .dependencies) })

withCircuit : (Module.t → Module.t) → CircuitM 𝟙.t
withCircuit f = modify
  λ s → record s { circuit = f (s .circuit) }

connect : Connection.t → CircuitM 𝟙.t
connect conn = withCircuit
  λ c → record c { connections = conn List.∷ (c .Module.t.connections) }

instantiate : Cell.t → CircuitM 𝟙.t
instantiate cell = withCircuit
  λ c → record c { cells = Cell.insert cell (c .Module.t.cells) }

fresh : Identifier → CircuitM Identifier
fresh ident = do
  ns <- gets S.idSupply
  let ident′ = withString ident (λ s → s String.++ "$" String.++ ℕ.show (Stream.head ns))
  modify (λ s → record s { idSupply = Stream.tail ns })
  pure ident′

freshWire : Wire.t → CircuitM Identifier
freshWire wire = do
  freshId ← fresh (wire .Wire.t.name)
  let wire′ = record wire { name = freshId }
  withCircuit
    λ c → record c { wires = Wire.insert wire′ (c .Module.t.wires) }
  pure freshId

freshBus : Identifier → Width → CircuitM Identifier
freshBus ident size = freshWire (Wire.bus ident (Wire.direct size))

-- TODO: missing in stdlib:
-- Data.List.Fresh.Membership.DecSetoid
infix 4 _∈?_
_∈?_ : (a : Module.t) → (as : Modules) → Rel₀.Dec (a ∈ as)
x ∈? xs = any? (x ≟_) xs
  where open Rel₂.DecSetoid Module.decSetoid

insert′ : Module.t → Modules → Modules
insert′ m modules with m ∈? modules
… | Rel₀.yes _ = modules
… | Rel₀.no m∉ =
    -- the Q param of the ¬Any⇒All seems to be unused?
    let is-fresh = fromAll (¬Any⇒All {Q = λ _ → 𝟙*.t} (m ≟_) m∉)
    in List.Fresh.cons m modules is-fresh
  where open Rel₂.DecSetoid Module.decSetoid

insert : Module.t → CircuitM 𝟙.t
insert = withDeps ⊙ insert′

data `Ob : ℕ.t → Set where
  `⊤ : `Ob 0 -- const 0
  `wire : ∀ {w} → .⦃ _ : ℕ.NonZero w ⦄ → Signal.t → `Ob w

  -- `concat : ∀ {w v} → `Ob w → `Ob w → `Ob (w ℕ.+ v)

signal : ∀ {w} → `Ob w → Signal.t
signal `⊤ = Signal.const 0
signal (`wire x) = x

-- signal (`concat a b) = Signal.prod (signal a) (signal b)

width : ∀ {w} → `Ob w → Width
width `⊤ = 1
width {w} (`wire ⦃ w≢0 ⦄ _) = w , [ w≢0 ]

-- width (`concat a b) with width a | width b
-- … | x , [ x≢0 ] | y , [ y≢0 ] = x ℕ.+ y ,
--   [ ℕ.>-nonZero (ℕ.≤-trans (ℕ.>-nonZero⁻¹ x ⦃ x≢0 ⦄) (ℕ.m≤m+n x y)) ]

freshOb : Identifier → (w : ℕ.t) → CircuitM (`Ob w)
freshOb _ ℕ.zero = pure `⊤
freshOb ident w@(ℕ.suc _) =
  let wid = w , [ ℕ.nonZero ]
  in do
    wire ← freshBus ident wid
    pure (`wire {w} (Signal.simple wire))

-- It won't make the name fresh,
-- as I need predictable identifiers for test scripts
IObus : Identifier → (w : ℕ.t) → Wire.InOut → CircuitM (`Ob w)
IObus id ℕ.zero _ = pure `⊤
IObus id w@(ℕ.suc _) io = do
  let wire′ = Wire.iobus id (Wire.direct (w , [ ℕ.nonZero ])) io
  withCircuit
    λ c → record c { wires = Wire.insert wire′ (c .Module.t.wires) }
  pure (`wire {w} (Signal.simple (wire′ .Wire.t.name)))

`proj₁ : ∀ {w v} → `Ob (w ℕ.+ v) → `Ob w
`proj₁ {ℕ.zero} {v} _ = `⊤
-- This case isn't really necessary,
-- but it'll lead to simpler rtlil code
`proj₁ {ℕ.suc w-1} {ℕ.zero }
  rewrite ℕ.+-identityʳ w-1 = Function.id
`proj₁ w@{ℕ.suc w-1} v@{ℕ.suc _} (`wire i) =
  `wire {w} (Signal.refer i [ Constant.unsigned (w-1 ℕ.+ v) ⋯ Constant.unsigned v ])

`proj₂ : ∀ {w v} → `Ob (w ℕ.+ v) → `Ob v
`proj₂ {w} {ℕ.zero} _ = `⊤
-- This case isn't really necessary,
-- but it'll lead to simpler rtlil code
`proj₂ {ℕ.zero } {ℕ.suc _} = Function.id
`proj₂ {ℕ.suc _} v@{ℕ.suc v-1} (`wire i) =
  `wire {v} (Signal.refer i [ Constant.unsigned v-1 ⋯ 0 ])

_`×_ : ∀ {w v} → `Ob w → `Ob v → `Ob (w ℕ.+ v)
`⊤ `× a = a
a@(`wire {w} _) `× `⊤ rewrite ℕ.+-identityʳ w = a
`wire {w} ⦃ w≢0 ⦄ a `× `wire {v} ⦃ v≢0 ⦄ b = `wire ⦃ w+v≢0 ⦄ (Signal.prod a b)
  where w+v≢0 : ℕ.NonZero (w ℕ.+ v)
        w+v≢0 = ℕ.>-nonZero (ℕ.<-≤-trans (ℕ.>-nonZero⁻¹ w) (ℕ.m≤m+n w v))

-- Morphism type for RTLIL category.  The objects are natural numbers
-- representing bit width of the binary words.  The meaning of this
-- morphism is RTLIL implementation of a function between binary words.
𝒬 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬 = mk⇒ {Ob = ℕ.t} λ i o → `Ob i → CircuitM (`Ob o)
open Object (𝒬 .Ob)
open Quiver 𝒬

RTLIL : Cartesian 𝒬
RTLIL = record
  { id = pure ⊙ id
  ; _∘_ = λ g f i → g =<< f i
  ; terminal = record { ⊤ = 0 }
  ; ! = const $ pure `⊤
  ; products = record { _×_ = ℕ._+_ }
  ; π₁ = pure ⊙ `proj₁
  ; π₂ = pure ⊙ `proj₂
  ; ⟨_,_⟩ = λ f g c → do
      a ← f c
      b ← g c
      pure (a `× b)
  }
open Cartesian RTLIL public

instance
  _ = terminal; _ = products

design : ∀ {w v} → Identifier → w ⇒ v → Design.t
design {w} {v} id f =
  let s = State.execState top (empty id)
      mods = insert′ (s .circuit) (s .dependencies)
  in Design.mk (Maybe.just (Stream.head (s .idSupply))) (proj₁ (List.Fresh.toList mods))
  where
    top : CircuitM 𝟙.t
    top = do
      i ← IObus "\\INPUT" w (Wire.input 1)
      o ← IObus "\\OUTPUT" v (Wire.output 2)
      o′ ← f i
      connect (signal o ⇐ signal o′)
      pure 𝟙.tt
