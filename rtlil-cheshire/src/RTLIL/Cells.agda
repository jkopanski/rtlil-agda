{-# OPTIONS --safe --cubical-compatible --guardedness #-}
module RTLIL.Cells where

open import Cheshire.Core

-- stdlib
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromString
import Data.Product as Prod
import Effect.Monad.State.Instances
import Effect.Monad.Identity.Instances

-- cheshire
import Cheshire.Object.Signatures as Object
import Cheshire.Signatures as Signatures

-- rtlil-agda
import RTLIL.Word as Word renaming (Word to t)
import RTLIL.Word.Properties as Wordₚ
open import RTLIL.Syntax

-- rtlil-cheshire
import Cheshire.Instance.RTLIL as RTLIL renaming (RTLIL to t)
import Cheshire.Instance.Words as Words renaming (Words to t)

open List using ([]; _∷_)
open RTLIL
open Object (𝒬 .Ob)
open Quiver 𝒬

private
  -- Convention used through yosys internal rtliil library cells
  a b s y : Identifier
  a = "\\A"
  b = "\\B"
  s = "\\S"
  y = "\\Y"
  width′ a-width b-width s-width y-width : Identifier
  width′   = "\\WIDTH"
  a-width = "\\A_WIDTH"
  b-width = "\\B_WIDTH"
  s-width = "\\S_WIDTH"
  y-width = "\\Y_WIDTH"
  a-signed b-signed y-signed : Identifier
  a-signed = "\\A_SIGNED"
  b-signed = "\\B_SIGNED"
  y-signed = "\\Y_SIGNED"

instance
  _ = ℕ.number; _ = String.isString
  _ = terminal; _ = products

private
  variable
    w v : ℕ.t

-- WARNING:
-- YOU HAVE TO SPECIFY ALL THE INTERNAL CELLS PARAMETERS

-- update parameter on internal yosys cell
updateInternalParameter : Identifier → Constant.t → w ⇒ v → w ⇒ v
updateInternalParameter ident const comp i = do
  out ← comp i
  withCircuit $ λ m → record m
    { cells = Map.map (Parameters.insert (ident , const)) (m .Module.t.cells) }
  pure out

unary : Identifier → (u : ℕ.t) → (w : ℕ.t) → u ⇒ w
unary ident u w i = do
  name ← fresh (withString ident ("$RTLIL$internal" String.++_))
  out ← freshOb (withString name (String._++ "$output")) w
  instantiate record
        { attributes = Attributes.empty
        ; type = ident
        ; name = name
        ; parameters = Parameters.mk
          $ (a-width , Constant.unsigned u)
          ∷ (y-width , Constant.unsigned w)
          ∷ (a-signed , 0)
          ∷ []
        ; connections =
            Signal.simple a ⇐ signal i
          ∷ Signal.simple y ⇐ signal out
          ∷ []
        }
  pure out

binary : Identifier → (u : ℕ.t) → (w : ℕ.t) → (v : ℕ.t) → u × w ⇒ v
binary ident u w v i = do
  name ← fresh (withString ident ("$RTLIL$internal" String.++_))
  out ← freshOb (withString name (String._++ "$output")) v
  instantiate record
        { attributes = Attributes.empty
        ; type = ident
        ; name = name
        ; parameters = Parameters.mk
          $ (a-width , Constant.unsigned u)
          ∷ (b-width , Constant.unsigned w)
          ∷ (y-width , Constant.unsigned v)
          ∷ (a-signed , 0)
          ∷ (b-signed , 0)
          ∷ []
        ; connections =
            Signal.simple a ⇐ signal (`proj₁ {v = w} i)
          ∷ Signal.simple b ⇐ signal (`proj₂ {w = u} i)
          ∷ Signal.simple y ⇐ signal out
          ∷ []
        }
  pure out

-- yosys unary cells:
-- https://yosyshq.readthedocs.io/projects/yosys/en/stable/cell/word_unary.html#unary-operators
not : w ⇒ w
not {w} = unary "$not" w w

not-meaning : Words.𝒬 .Hom w w
not-meaning = Word.opposite

neg : w ⇒ w
neg {w} = updateInternalParameter a-signed 1 $ unary "$neg" w w

neg-meaning : ⦃ _ : ℕ.NonZero w ⦄ → Words.𝒬 .Hom w w
neg-meaning {w} = Word.truncate 1 ⊙ (Word._+ Word.one) ⊙ Word.opposite

reduce_and : w ⇒ 1
reduce_and {w} = unary "$reduce_and" w 1

reduce_and-meaning : Words.𝒬 .Hom w 1
reduce_and-meaning = Func.Inverse.from Wordₚ.1↔Bool ⊙ Rel₀.isYes ⊙ Wordₚ.last?

reduce_or : w ⇒ 1
reduce_or {w} = unary "$reduce_or" w 1

reduce_or-meaning : Words.𝒬 .Hom w 1
reduce_or-meaning = Func.Inverse.from Wordₚ.1↔Bool ⊙ Rel₀.isNo ⊙ Wordₚ.zero?
reduce_bool : w ⇒ 1
reduce_bool {w} = updateInternalParameter a-signed 1 $ unary "$reduce_bool" w 1

reduce_bool-meaning : Words.𝒬 .Hom w 1
reduce_bool-meaning = Func.Inverse.from Wordₚ.1↔Bool ⊙ Rel₀.isNo ⊙ Wordₚ.zero?

logic_not : w ⇒ 1
logic_not {w} = unary "$logic_not" w 1

logic_not-meaning : Words.𝒬 .Hom w 1
logic_not-meaning = not-meaning ⊙ reduce_bool-meaning

-- yosys binary cells:
-- https://yosyshq.readthedocs.io/projects/yosys/en/stable/cell/word_binary.html#binary-operators
and : w × w ⇒ w
and {w} = binary "$and" w w w

add : w × w ⇒ ℕ.suc w
add {w} = binary "$add" w w (ℕ.suc w)

add-meaning : Words.𝒬 .Hom (w × w) (ℕ.suc w)
add-meaning {w} = Prod.uncurry Word._+_ ⊙ Word.remQuot w

contrived : (w × w) × (w × w) ⇒ ℕ.2+ w
contrived = add ∘ (add ⁂ add)

contrived-meaning : Words.𝒬 .Hom ((w × w) × (w × w)) (ℕ.2+ w)
contrived-meaning = wadd Words.∘ (wadd Words.⁂ wadd)
  where wadd : ∀ {u} → Words.𝒬 .Hom (u ℕ.+ u) (ℕ.suc u)
        wadd {u} = Prod.uncurry Word._+_ ⊙ Word.remQuot u
