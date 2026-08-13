{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.88] probe A: the decisive step of the closure route, GREEN.
--
-- Question 2 of the brief: "A definable subset of a set that has a stage
-- appears one level up.  Does that route reach w?"  The route's decisive
-- step is exactly this pair of delivered facts:
--
--   1. finSet∈𝒟ₒ : a finite family of members of a stage spans a
--      DEFINABLE subset of that stage.
--      (L.Axioms.Basic.lagda.md:352-354, inside module FinOf)
--   2. Lset-suc   : Lset (sucV σ) ≡ 𝒟ₒ (Lset σ), i.e. the successor
--      stage IS the definable power set.
--      (L.Axioms.Basic.lagda.md:196)
--
-- Composing them: a finite family of members of Lset σ is a member of
-- Lset (sucV σ).  The consumer's witness w is the subformula closure
-- (L.Coding.CodeSet.lagda.md:369), which is by construction a finite
-- union of singletons of keys (L.Coding.InL.lagda.md:258-270), and every
-- member of w lies in Lset δ for a δ below the stage of AllCodes A
-- (w ⊆ AllCodes A, ProbeLJ185B.agda:58-68; AllCodes A ∈ Lset δ₀,
-- ProbeLJ186A.agda:43-45; Lset-out plus 𝒟ₒ∋⊆).  So the closure lands in
-- Lset (sucV δ) — one level up, by finiteness, NOT by condensation.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ188A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Axioms.Basic {ℓ}
  using ( finSet; module FinOf; Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Foundations.Prelude using ( sym )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- THE DECISIVE STEP.  A finite family of members of a stage is a
-- definable subset of that stage (finSet∈𝒟ₒ), and the successor stage is
-- exactly the definable power set (Lset-suc).  Hence the family appears
-- one level up.  This is the "definable subset of a set that has a stage
-- appears one level up" step, in the exact form the closure route
-- consumes.
finSet-stage : (σ : V ℓ) (oσ : IsOrd σ) (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
             → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ Lset (sucV σ) ⟩
finSet-stage σ oσ n g =
  subst (λ w → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ w ⟩)
    (sym (Lset-suc σ))
    (FinOf.finSet∈𝒟ₒ σ oσ n g)
