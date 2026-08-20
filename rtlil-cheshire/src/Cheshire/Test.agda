{-# OPTIONS --guardedness #-}

open import Cheshire.Core

module Cheshire.Test where

open import Cheshire.Core using (Quiver)
open import Agda.Builtin.FromString
open import RTLIL.Syntax
open import RTLIL.Syntax.PrettyPrint using (PrettyWord)
open import RTLIL.Word.Test

module IO where
  open import IO.Base   public
  open import IO.Finite public
  open import IO.Handle public

module Table where
  open import Text.Tabular.Base public
  open import Text.Tabular.List public

  open TabularConfig public
  open TabularLine   public

import Cheshire.Instance.RTLIL as Rtl
import Cheshire.Instance.Combinational as Combinational

import Text.PrettyPrint.Annotated as Doc renaming (Doc to t)

open Quiver using (Hom)
open IO using (_>>_)
open Function using (_∘_)
open List using (_∷_; []; [_])
open Combinational using (module Syntax)

module R = Combinational.Realization
module M = Combinational.Meaning

instance _ = PrettyWord

pretty : ∀ {A : Set} → ⦃ _ : Doc.Pretty 𝟙*.t A ⦄ → A → String.t
pretty = Doc.render ∘ Doc.pPrint

module Harness where
  combinational : (w : ℕ.t) → ∀ {v} → Syntax.𝒬 .Hom w v → IO.Main
  combinational w logic =
    let dut = Rtl.design "dut" (R.₁ logic)
    in IO.run $ do
      IO.writeFile "dut.il" $ pretty dut
      -- TODO: should this be in the pretty print somewhere?
      IO.appendFile "dut.il" "\n"

      let words = all w
          tt = Function.flip List.map words $ λ where
              i →   pretty i
                  ∷ (pretty $ M.₁ logic i)
                  ∷ []
          header = "\\INPUT" ∷ "\\OUTPUT" ∷ []
          table = header ∷ tt

      IO.putStrLn ∘ String.unlines $
        Table.display Table.whitespace (List.replicate 3 Table.Right) table
