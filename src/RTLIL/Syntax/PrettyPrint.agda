open import Prelude
open import Agda.Builtin.FromString

module RTLIL.Syntax.PrettyPrint where

import Text.PrettyPrint.Annotated as Doc renaming (Doc to t)

open import RTLIL.Syntax.Attributes
open import RTLIL.Syntax.Base
open import RTLIL.Syntax.Cell
open import RTLIL.Syntax.Connection
open import RTLIL.Syntax.Design
open import RTLIL.Syntax.Module
open import RTLIL.Syntax.Parameters
open import RTLIL.Syntax.Signal
open import RTLIL.Syntax.Wire

open × using (_×_; _,_)
open Doc using (Pretty; _<>_; _<+>_; _</>_; _$+$_; pPrintPrec)

private
  variable
    ann : Set

------------------------------------------------------------------------
-- RTLIL.Syntax.Base

instance
  PrettyIdent : Pretty ann Identifier
  PrettyIdent .pPrintPrec _ _ id = Doc.text $ toString id

  PrettyConst : Pretty ann Constant
  PrettyConst .pPrintPrec _ _ (string c) = Doc.doubleQuotes (Doc.text c)
  PrettyConst .pPrintPrec _ _ (signed c) = Doc.int c

  PrettyConstId : Pretty ann (Identifier × Constant)
  PrettyConstId .pPrintPrec l p (id , c) = pPrintPrec l p id <+> pPrintPrec l p c
  {-# OVERLAPPING PrettyConstId #-}

pMap : ∀ {ℓ} {A : Set ℓ} → ⦃ Pretty ann A ⦄ → (Identifier × A → Doc.t ann) → Map.t A → Doc.t ann
pMap f m = List.foldr
  (λ id×a acc → f id×a $+$ acc)
  Doc.Empty
  (Map.toList m)

instance
  PrettyAttrs : Pretty ann Attributes
  PrettyAttrs .pPrintPrec l p a = pMap
    (λ (id , attr) → "attribute" <+> pPrintPrec l p id <+> pPrintPrec l p attr)
    (a .Attributes.map)

  PrettyParams : Pretty ann Parameters
  PrettyParams .pPrintPrec l p a = pMap
    (λ (id , param) → "parameter" <+> pPrintPrec l p id <+> pPrintPrec l p param)
    (a .Parameters.map)

------------------------------------------------------------------------
-- RTLIL.Syntax.Signal

spaceOut : Doc.t ann → Doc.t ann
spaceOut p = Doc.space <> p <> Doc.space

instance
  PrettySelection : Pretty ann Selection
  PrettySelection .pPrintPrec _ _ All         = Doc.empty
  PrettySelection .pPrintPrec _ _ (Single s)  = Doc.brackets $ Doc.nat s
  PrettySelection .pPrintPrec _ _ (Range m n) = Doc.brackets $ Doc.nat m <+> Doc.colon <+> Doc.nat n

  {-# TERMINATING #-}
  PrettySignal : Pretty ann Signal
  PrettySignal .pPrintPrec l p (const c)    = pPrintPrec l p c
  PrettySignal .pPrintPrec l p (refer id s) = pPrintPrec l p id <+> pPrintPrec l p s
  PrettySignal .pPrintPrec l p (concat s)   =
    Doc.braces $ spaceOut
               $ Doc.hsep
               $ List.map (pPrintPrec l p)
               $ NonEmpty.toList s

------------------------------------------------------------------------
-- RTLIL.Syntax.Connection

instance
  PrettyConnection : Pretty ann Connection
  PrettyConnection .pPrintPrec l p (sink ⇐ source) = "connect" <+> pPrintPrec l p sink <+> pPrintPrec l p source

------------------------------------------------------------------------
-- RTLIL.Syntax.Wire

instance
  PrettyBitNumbering : Pretty ann BitNumbering
  PrettyBitNumbering .pPrintPrec _ _ MSB = "upto"
  PrettyBitNumbering .pPrintPrec _ _ LSB = Doc.Empty

  PrettyInOut : Pretty ann InOut
  PrettyInOut .pPrintPrec _ _ (input  d) = "input"  <+> Doc.nat d
  PrettyInOut .pPrintPrec _ _ (output d) = "output" <+> Doc.nat d
  PrettyInOut .pPrintPrec _ _ (inout  d) = "inout"  <+> Doc.nat d

  PrettyMaybeInOut : Pretty ann (Maybe.t InOut)
  PrettyMaybeInOut .pPrintPrec l p (Maybe.just io) = pPrintPrec l p io
  PrettyMaybeInOut .pPrintPrec _ _ (Maybe.nothing) = Doc.empty
  {-# OVERLAPS PrettyMaybeInOut #-}
  -- overlaps Pretty ann (Maybe A) from agda-pretty

  PrettySignedness : Pretty ann Signedness
  PrettySignedness .pPrintPrec _ _ Signed = "signed"
  PrettySignedness .pPrintPrec _ _ Unsigned = Doc.Empty

  PrettyWidth : Pretty ann Width
  PrettyWidth .pPrintPrec _ _ record { width = ℕ.suc ℕ.zero } = Doc.empty
  PrettyWidth .pPrintPrec _ _ record { width = width@(ℕ.suc (ℕ.suc _)) } =
    "width" <+> Doc.nat width

pOffset : ℕ.t → Doc.t ann
pOffset ℕ.zero = Doc.Empty
pOffset n@(ℕ.suc _) = Doc.nat n

instance
  PrettyWire : Pretty ann Wire
  PrettyWire .pPrintPrec l p wire = pPrintPrec l p attributes $+$
    "wire" <+> pPrintPrec l p width
           <+> pPrintPrec l p io
           <+> pOffset offset
           <+> pPrintPrec l p upto
           <+> pPrintPrec l p (wire .Wire.signed)
           <+> pPrintPrec l p name
    where open Wire wire

------------------------------------------------------------------------
-- RTLIL.Syntax.Cell

instance
  PrettyCell : Pretty ann Cell
  PrettyCell .pPrintPrec l p c = pPrint attributes
    $+$ "cell" <+> pPrint type <+> pPrint name
    </> (pPrint parameters
      $+$ Doc.vcat (List.map pPrint connections))
    $+$ "end"
    where open Cell c
          pPrint : ∀ {ℓ} {A : Set ℓ} → ⦃ Pretty ann A ⦄ → A → Doc.t ann
          pPrint = pPrintPrec l p

------------------------------------------------------------------------
-- RTLIL.Syntax.Module

instance
  PrettyModule : Pretty ann Module
  PrettyModule .pPrintPrec l p m = pPrint attributes
    $+$ "module" <+> pPrint name
    </> (pPrint parameters
      $+$ Doc.vcat (List.map pPrint wires)
      $+$ Doc.vcat (List.map pPrint cells)
      $+$ Doc.hsep (List.map pPrint connections))
    $+$ "end"
    where open Module m
          pPrint : ∀ {ℓ} {A : Set ℓ} → ⦃ Pretty ann A ⦄ → A → Doc.t ann
          pPrint = pPrintPrec l p

------------------------------------------------------------------------
-- RTLIL.Syntax.Design

instance
  PrettyDesign : Pretty ann Design
  PrettyDesign .pPrintPrec l p d =
    Maybe.maybe′ (("autoidx" <+>_) ∘ Doc.nat) Doc.empty (d .autoidx)
    $+$ Doc.hsep (List.map (pPrintPrec l p) (d .modules))
