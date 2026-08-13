{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.32] Finding: the DELIVERED clause forms (existClauseAt,
-- exInClauseAt, ...) are not Delta-0 formulas.  Their frames use the
-- unbounded quantifiers `∀̇` and `∃̇`, and `Δ₀` has no constructor for
-- them ("absence is the classification").  The two functions below are
-- machine-checked witnesses that `Δ₀ (∀̇ ⊥̇)` and `Δ₀ (∃̇ ⊥̇)` are empty.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ132NotD0 {ℓ : Level} where

open import FOL.Syntax using ( Formula; ⊥̇; ∀̇_; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
import Cubical.Data.Empty as Empty

notD0-∀ : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K (suc n)) → Δ₀ (∀̇ φ) → Empty.⊥* {ℓc}
notD0-∀ φ ()

notD0-∃ : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K (suc n)) → Δ₀ (∃̇ φ) → Empty.⊥* {ℓc}
notD0-∃ φ ()
