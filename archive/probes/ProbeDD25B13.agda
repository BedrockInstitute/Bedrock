{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.32] Width ladder point k=16: 16 right-nested copies
-- of the small count-0 reader consAtL, PLACED, at a VARIABLE arity n.
-- This locates where the placement certificate turns over with the tree,
-- with the arity axis held at the setting that walls.
-- `src/ProbeLJ132Small0.agda` places the small count-0 reader `consAtL` at
-- the CONCRETE arity 1 and is green.  `src/ProbeLJ132C0.agda` places the big
-- count-0 matrix at a VARIABLE arity `n` and walls.  The two controls differ
-- in size AND in arity, so neither isolates a cause.
-- This probe holds the SIZE small and moves the ARITY to a variable.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeDD25B13 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
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

module Ladder {n : ℕ} (e' m e : Fin n) where
  phi : Formula S n
  phi = consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e ∧̇ (consAtL e' m e)))))))))))))))

  Delta0-phi : Δ₀ phi
  Delta0-phi = δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (δ-∧ (Δ₀-consAtL e' m e) (Δ₀-consAtL e' m e)))))))))))))))

  sigmaL : Formula S (n + countFo phi)
  sigmaL = embed (absFo {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} phi)

  Delta0-sigmaL : Δ₀ sigmaL
  Delta0-sigmaL = mapΔ₀ Empty.rec* (absΔ₀ {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} Delta0-phi)
