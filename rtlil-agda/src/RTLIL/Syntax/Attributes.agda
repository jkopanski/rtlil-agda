{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Attributes where

open import Overture
open import RTLIL.Syntax.Base

open × using (_×_)

private
  variable
    a : 𝕃.t
    A : Set a

record Attributes : Set where
  field
    map : Map.t Constant.t

open Attributes

mk : List.t (Identifier × Constant.t) → Attributes
mk cs .map = Map.fromList cs

empty : Attributes
empty .map = Map.empty

insert : ⦃ Has Attributes A ⦄ → Identifier × Constant.t → A → A
insert (i , c) r =
  let old = get r .map
  in set (record { map = Map.insert i c old }) r
