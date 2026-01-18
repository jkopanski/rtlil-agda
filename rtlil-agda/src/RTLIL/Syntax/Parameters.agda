{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax.Parameters where

open import Overture
open import RTLIL.Syntax.Base

open × using (_×_)

private
  variable
    a : 𝕃.t
    A : Set a

record Parameters : Set where
  field
    map : Map.t Constant.t

open Parameters

mk : List.t (Identifier × Constant.t) → Parameters
mk cs .Parameters.map = Map.fromList cs

empty : Parameters
empty .Parameters.map = Map.empty

insert : ⦃ Has Parameters A ⦄ → Identifier × Constant.t → A → A
insert (i , c) r =
  let old = get r .map
  in set (record { map = Map.insert i c old }) r
