{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Builtin.FromString
open import Overture
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

module Word where
  open import RTLIL.Word.Base public

import Text.PrettyPrint.Annotated as Doc renaming (Doc to t)

import Cheshire.Instance.RTLIL as Rtl
import RTLIL.Cells as Cells

open IO using (_>>_)
open Function using (_∘_)
open List using (_∷_; []; [_])

instance _ = PrettyWord

pretty : ∀ {A : Set} → ⦃ _ : Doc.Pretty 𝟙*.t A ⦄ → A → String.t
pretty = Doc.render ∘ Doc.pPrint

main : IO.Main
main =
  let w = 4
      dut = Rtl.design {w} {w} "dut" Cells.not
  in IO.run $ do
    IO.writeFile "dut.il" $ pretty dut
    -- TODO: should this be in the pretty print somewhere?
    IO.appendFile "dut.il" "\n"

    let words = all w
        tt = Function.flip List.map words $ λ where
            i →   pretty i
                ∷ (pretty $ Cells.not-meaning {w} i)
                ∷ []
        header = "\\INPUT" ∷ "\\OUTPUT" ∷ []
        table = header ∷ tt

    IO.putStrLn ∘ String.unlines $ Table.display Table.whitespace (List.replicate 3 Table.Right) table
