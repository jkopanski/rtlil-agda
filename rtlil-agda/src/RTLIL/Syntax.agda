{-# OPTIONS --safe --cubical-compatible #-}
module RTLIL.Syntax where

open import RTLIL.Syntax.Base public

module Attributes where
  open import RTLIL.Syntax.Attributes renaming (Attributes to t) public

module Cell where
  open import RTLIL.Syntax.Cell renaming (Cell to t) public

module Connection where
  open import RTLIL.Syntax.Connection renaming (Connection to t) public

open Connection using (_⇐_) public

module Design where
  open import RTLIL.Syntax.Design renaming (Design to t) public

module Module where
  open import RTLIL.Syntax.Module renaming (Module to t) public

module Parameters where
  open import RTLIL.Syntax.Parameters renaming (Parameters to t) public

module Signal where
  open import RTLIL.Syntax.Signal renaming (Signal to t) public

module Wire where
  open import RTLIL.Syntax.Wire renaming (Wire to t) public
