{-# OPTIONS --safe --cubical-compatible #-}
open import Prelude

module RTLIL.Syntax.Parameters where

open import RTLIL.Syntax.Base

open × using (_×_)

private
  variable
    a : 𝕃.t
    A : Set a

record Parameters : Set where
  field
    map : Map.t Constant

open Parameters

record Has {ℓ} (A : Set ℓ) : Set ℓ where
  field
    get : A → Parameters
    set : Parameters → A → A

open Has ⦃ … ⦄ public

mk : List.t (Identifier × Constant) → Parameters
mk cs .Parameters.map = Map.fromList cs

empty : Parameters
empty .Parameters.map = Map.empty

insert : ⦃ Has A ⦄ → Identifier × Constant → A → A
insert (i , c) r =
  let old = get r .map
  in set (record { map = Map.insert i c old }) r
