{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.697] W3.  Does an adequate K sit inside Lset lam?
-- Three membership facts, none a second formula.  Lands nothing in src/.
--
--   LSET           Lset β is a member of Lset (sucV β).  W2:
--                  𝒟ₒ-intro at ⊤̇ and Lset-suc, as [LJ-1.536]
--                  (Probe536.agda:159-161), not a second proof.
--   ORDINAL        an ordinal in Lset lam is a member of lam.
--                  W2: ord∈Lset→∈ (src/L/Ordinal/Stages.lagda.md:265-268).
--   CLIMB          succλ iterated.  The limit hypotheses pay the
--                  successor tower that [LJ-1.494] did not have.
--   LSET-IN-STAGE  Lset δ is a member of Lset lam.  That is a K
--                  inside the stage.  It is not hierL.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-697.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono; 𝒟ₒ-intro )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- A STAGE IS A MEMBER OF THE NEXT STAGE.  W2: Probe536.agda:159-161.
Lset∈suc : (β : S) → ⟨ Lset β ∈ˢ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ˢ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

step : ℕ → S → S
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

module At (lam : S) (ordλ : IsOrd lam)
          (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) where

  -- THE LIMIT HYPOTHESIS, ITERATED.  [LJ-1.494] had no succλ
  -- (Probe494.agda:35).  This frame does (Probe679.agda:64).
  climb : (n : ℕ) (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ step n d ∈ˢ lam ⟩
  climb zero    d d∈ = d∈
  climb (suc n) d d∈ = succλ (step n d) (climb n d d∈)

  -- AN ORDINAL IN THE STAGE IS A MEMBER OF THE INDEX.
  ordinal-in : (δ : S) (oδ : IsOrd δ)
             → ⟨ δ ∈ˢ Lset lam ⟩ → ⟨ δ ∈ˢ lam ⟩
  ordinal-in δ oδ = ord∈Lset→∈ lam ordλ δ oδ

  -- THE ADEQUATE K THAT IS A MEMBER OF THE STAGE: Lset δ, not Lset lam.
  -- kvalue-escapes forbids K = Lset lam
  -- (agents/tasks/LJ-1-679/runs/W3.agda:36-37).
  lset-in-stage : (δ : S) (oδ : IsOrd δ)
                → ⟨ δ ∈ˢ Lset lam ⟩
                → ⟨ Lset δ ∈ˢ Lset lam ⟩
  lset-in-stage δ oδ δ∈Lλ =
    Lset-mono {α = lam} {β = sucV δ}
      (succλ δ (ordinal-in δ oδ δ∈Lλ))
      (Lset∈suc δ)
