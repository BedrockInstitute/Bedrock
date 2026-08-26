{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.674] PROBE.  Does a stage describe the definable powerset of
-- the member the tower applies 𝒟ₒ to.
-- It runs in agents/tasks/LJ-1-674/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is describes-status: Describes at
-- the pair (sucV δ, Lset δ).  That is the pair Lset-suc names
-- (src/L/Axioms/Basic.lagda.md:196).  The formula is ⊤̇.  The
-- generic fact is defSet⊤≡A (src/L/Definability.lagda.md:178).
--
-- WHAT IS SETTLED.
--   1. Describes, copied from
--      agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82.
--   2. carve-self: the tautology carves any carrier (W2).
--   3. describes-status: instantiate at Lset (sucV δ) and rewrite
--      by Lset-suc.
--
-- WHAT IS NOT SETTLED.
--   Describes σ y at an arbitrary member y of Lset σ.  The tautology
--   carves the WHOLE stage, so it pays the pair where 𝒟ₒ y IS the
--   stage, and nothing else.  A Formula Code 1 for 𝒟ₒ stays a
--   second debt.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth

module LJ-1-674.Probe674 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

open import Cubical.Data.Sigma using ( Σ-syntax; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE PAIR THE TOWER REACHES.
--
-- Describes is [LJ-1.169]'s type.  Lset-suc says the next stage IS
-- 𝒟ₒ of the current stage.  defSet⊤≡A says the tautology carves
-- the carrier.  Those two identities inhabit Describes at that pair.
-- =====================================================================

Describes : S → S → Type (ℓ-suc ℓ)
Describes σ y =
  ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) ψ ≡ 𝒟ₒ y) ∥₁

-- W2: the tautology carves an arbitrary carrier.  One fact, then
-- instantiate.
carve-self : (A : S)
           → ∥ Σ[ ψ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A ψ ≡ A) ∥₁
carve-self A = ∣ ⊤̇ , DefOf.defSet⊤≡A A ∣₁

-- THE OBLIGATION.  The stage is sucV δ.  The member is Lset δ, the
-- set the tower itself feeds to 𝒟ₒ.
describes-status : (δ : S) → Describes (sucV δ) (Lset δ)
describes-status δ = PT.map (λ { (ψ , q) → ψ , q ∙ Lset-suc δ })
  (carve-self (Lset (sucV δ)))
