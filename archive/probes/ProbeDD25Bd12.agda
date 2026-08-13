{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.32] DEPTH ladder point d=12.  The formula is ONE
-- atom under 12 nested BOUNDED quantifiers, at a VARIABLE arity.  Its node
-- count is 13, far below the 244 of consAtL and the 651 of the walling
-- matrix.  If depth alone walls, the placement cost follows the BINDER
-- DEPTH and not the node count.
-- `src/ProbeLJ132Small0.agda` places the small count-0 reader `consAtL` at
-- the CONCRETE arity 1 and is green.  `src/ProbeLJ132C0.agda` places the big
-- count-0 matrix at a VARIABLE arity `n` and walls.  The two controls differ
-- in size AND in arity, so neither isolates a cause.
-- This probe holds the SIZE small and moves the ARITY to a variable.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeDD25Bd12 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ∀̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters
  using ( countFo; absFo; placeFo; padLeft )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ )




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

-- One atom under d nested bounded quantifiers.  Count 0, node count d+1.
deep : (d : ℕ) {m : ℕ} → Formula S (suc m)
deep zero = var zero ∈̇ var zero
deep (suc d) {m} = ∀̇∈ (var zero) (deep d {suc m})

Delta0-deep : (d : ℕ) {m : ℕ} → Δ₀ (deep d {m})
Delta0-deep zero = δ-∈
Delta0-deep (suc d) {m} = δ-∀∈ (Delta0-deep d {suc m})

module Depth {n : ℕ} where
  phi : Formula S (suc n)
  phi = deep 12 {n}

  sigmaL : Formula S (suc n + countFo phi)
  sigmaL = embed (absFo {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} phi)

  Delta0-sigmaL : Δ₀ sigmaL
  Delta0-sigmaL = mapΔ₀ Empty.rec* (absΔ₀ {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S}
                                     (Delta0-deep 12 {n}))
