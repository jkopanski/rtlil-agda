{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Word.Test where

open import Overture
open import RTLIL.Word.Base

open ℕ using (_^_)

all : ∀ w → List.t (Word w)
all w = List.tabulate fromFin
