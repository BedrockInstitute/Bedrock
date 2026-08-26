{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.682] PROBE.  convert-generic spent at matrix₃ by restating
-- Convert at pin₃ (embed φ).  Does not substitute into the matrix.
-- Lands nothing in src/.
--
--   W3              whether pin₃ (embed φ) elaborates at matrix₃
--                   (agents/tasks/LJ-1-680/lj-1.680-report.md:285-291).
--   THE OBLIGATION  convert-at-matrix.  The restated Convert,
--                   inhabited by convert-generic {φ = matrix₃}
--                   Δ₀-matrix₃.  The leftover equation
--                   mapFo val (mapFo slide matrix₃) ≡ embed matrix₃
--                   is never formed.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-682.Probe682 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Relabelling using ( embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import Cubical.Data.Vec using ( _∷_; [] )
import LJ-1-680.Probe680 {ℓ} as P680
import LJ-1-667.Probe667 {ℓ} lem as P667

open hPropStructure 𝒮ᵥ
open P680 using ( pin₃; _⊨ₚ_ )
open P667 using ( matrix₃; Δ₀-matrix₃ )

-- Restated Convert at pin₃ (embed φ), spent at the delivered
-- matrix₃.  W2: convert-generic is the generic unpack; this is
-- the instance.  convert-at-true (Probe680.agda:141) is the same
-- term at ⊤̇.

module Spend (U : S) (Utr : isTrans U) where
  open P680.Unpack U Utr

  convert-at-matrix :
      (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ (embed matrix₃) ca cp) ⟩
    → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ matrix₃ ⟩
  convert-at-matrix = convert-generic {φ = matrix₃} Δ₀-matrix₃

-- THE OBLIGATION.  Lifted off the carrier module so the witness
-- meter reads Target.convert-at-matrix (scripts/pod/witness.py:278).
convert-at-matrix = Spend.convert-at-matrix
