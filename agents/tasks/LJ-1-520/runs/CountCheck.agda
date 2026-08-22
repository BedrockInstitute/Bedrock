{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.520] A SEPARATE RUN, so a normalisation blow-up cannot cost the
-- probe.  Does the graded formula carry a constant?  The tree's own
-- bounded clause is constant-free and proves it by refl
-- (src/L/Condensation.lagda.md:365).  This asks the same question of the
-- formula this task delivers.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-520.runs.CountCheck {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Manipulation.Parameters using ( countFo )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )

no-constant : {n : ℕ} (w b : Fin n) → countFo (fst (levelFo-Σ₁ w b)) ≡ 0
no-constant w b = refl
