{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.306] the consumer's line, unchanged.  `LowerAgree`'s import
-- shape (`src/L/Condensation/LowerAgree.lagda.md:33-35`) against the
-- re-exporting replacement.  The `using` list resolves or the file
-- does not check.

open import Base.Prelude
open import Base.Truth

module LJ-1-306.ReexportUse {ℓ : Level} where

open import LJ-1-306.ReexportTest {ℓ}
  using ( envHypB2; module Mem; module Eq; module And; module Or
        ; module Imp; module Neg; module MemAgree; module EqAgree
        ; module AndAgree; module OrAgree; module ImpAgree
        ; module NegAgree; succU; keyU; module TopAgree; module BotAgree
        ; envSetB; module EnvSet; tagBS )

-- One nominal use per kind, so the names are not only imported.
reached-tagBS : ∀ {n : ℕ} → Fin n → Fin n → Fin n → Fin n → _
reached-tagBS = tagBS
