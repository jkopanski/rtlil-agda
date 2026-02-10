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
open import RTLIL.Syntax

-- rtlil-cheshire
import Cheshire.Instance.RTLIL as RTLIL renaming (RTLIL to t)
import Cheshire.Instance.Words as Words renaming (Words to t)

open List using ([]; _∷_)
open RTLIL
open Signatures
open Object (𝒬 .Ob)
open Quiver 𝒬

private
  -- Convention used through yosys internal rtliil library cells
  a b y : Identifier
  a = "\\A"
  b = "\\B"
  y = "\\Y"
  a-width b-width y-width : Identifier
  a-width = "\\A_WIDTH"
  b-width = "\\B_WIDTH"
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

and : w × w ⇒ w
and {w} = binary "$and" w w w

add : w × w ⇒ ℕ.suc w
add {w} = binary "$add" w w (ℕ.suc w)

contrived : (w × w) × (w × w) ⇒ ℕ.2+ w
contrived = add ∘ (add ⁂ add)

contrived-meaning : Words.𝒬 .Hom ((w × w) × (w × w)) (ℕ.2+ w)
contrived-meaning = wadd Words.∘ (wadd Words.⁂ wadd)
  where wadd : ∀ {u} → Words.𝒬 .Hom (u ℕ.+ u) (ℕ.suc u)
        wadd {u} = Prod.uncurry Word._+_ ⊙ Word.remQuot u
