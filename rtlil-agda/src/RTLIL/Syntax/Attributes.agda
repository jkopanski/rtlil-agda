{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Attributes where

open import RTLIL.Syntax.Base

open × using (_×_)

private
  variable
    a : 𝕃.t
    A : Set a

record Attributes : Set where
  field
    map : Map.t Constant

open Attributes

record Has {ℓ} (A : Set ℓ) : Set ℓ where
  field
    get : A → Attributes
    set : Attributes → A → A

open Has ⦃ … ⦄ public

mk : List.t (Identifier × Constant) → Attributes
mk cs .map = Map.fromList cs

empty : Attributes
empty .map = Map.empty

insert : ⦃ Has A ⦄ → Identifier × Constant → A → A
insert (i , c) r =
  let old = get r .map
  in set (record { map = Map.insert i c old }) r
