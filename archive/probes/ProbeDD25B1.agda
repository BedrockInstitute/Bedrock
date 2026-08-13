{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.32] Separate the ARITY axis from the SIZE axis.
-- `src/ProbeLJ132Small0.agda` places the small count-0 reader `consAtL` at
-- the CONCRETE arity 1 and is green.  `src/ProbeLJ132C0.agda` places the big
-- count-0 matrix at a VARIABLE arity `n` and walls.  The two controls differ
-- in size AND in arity, so neither isolates a cause.
-- This probe holds the SIZE small and moves the ARITY to a variable.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeDD25B1 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters
  using ( countFo; absFo; placeFo; padLeft )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt )
open import L.Coding.Model {ℓ} using ( consAtL )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Nat using ( _+_ )

open hPropStructure 𝒮ʟ

placeΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n k} {φ : Formula K n}
        → Δ₀ φ → (θ : Fin (countFo φ) → Fin (n + k))
        → Δ₀ (placeFo {ℓz = ℓz} φ θ)
placeΔ₀ δ-∈ θ = δ-∈
placeΔ₀ δ-≐ θ = δ-≐
placeΔ₀ (δ-∧ c d) θ = δ-∧ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-∨ c d) θ = δ-∨ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-⇒ c d) θ = δ-⇒ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-¬ c)   θ = δ-¬ (placeΔ₀ c θ)
placeΔ₀ δ-⊤ θ = δ-⊤
placeΔ₀ δ-⊥ θ = δ-⊥
placeΔ₀ (δ-∀∈ c) θ = δ-∀∈ (placeΔ₀ c _)
placeΔ₀ (δ-∃∈ c) θ = δ-∃∈ (placeΔ₀ c _)

absΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n} {φ : Formula K n}
      → Δ₀ φ → Δ₀ (absFo {ℓz = ℓz} φ)
absΔ₀ {n = n} d = placeΔ₀ d (padLeft n)

Δ₀-consAtL : ∀ {n} (e' m e : Fin n) → Δ₀ (consAtL e' m e)
Δ₀-consAtL e' m e = Δ₀-liftFo _ (Δ₀-consAt e' m e)

-- The count at a VARIABLE arity, asserted before the placement witness.
_ : ∀ {n} (e' m e : Fin n) → countFo (consAtL e' m e) ≡ 0
_ = λ e' m e → refl

-- The placement witness for the SMALL count-0 reader, at a VARIABLE arity.
module VarArity {n : ℕ} (e' m e : Fin n) where
  σL : Formula S (n + countFo (consAtL e' m e))
  σL = embed (absFo {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} (consAtL e' m e))

  Δ₀-σL : Δ₀ σL
  Δ₀-σL = mapΔ₀ Empty.rec* (absΔ₀ {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S}
                             (Δ₀-consAtL e' m e))
