{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.87] probe A: what the two premises actually give.
--
-- The repaired witK adds two premises:
--     (1) w ⊆ AllCodes A              (LJ-1.85)
--     (2) fst (AllCodes A) ∈ Lset lam (the frame hypothesis, LJ-1.86)
-- and concludes fst w ∈ Lset lam.
--
-- This probe machine-checks the honest content of those two premises:
--   a. The frame hypothesis decomposes: AllCodes A is a definable subset
--      of Lset δ for some δ ∈ lam (Lset-out), hence a subset of Lset δ
--      (𝒟ₒ∋⊆).
--   b. With w ⊆ AllCodes A, every member of w lies in Lset lam
--      (w ⊆ Lset lam), by transitivity of the stage.
--   c. The frame hypothesis is the "stage of AllCodes A is below lam"
--      class: from stage (AllCodes A) ∈ lam we get AllCodes A ∈ Lset lam
--      by Lset-mono and stage-mem.
--
-- The step the two premises do NOT give is fst w ∈ Lset lam: the
-- premises bound the MEMBERS of w, not w itself.  The hierarchy is the
-- definable power set (L.Axioms.Power.lagda.md:18-20: "Condensation is
-- not part of this"), so a subset of a stage element need not appear one
-- level up.  Probe B is the red control for the missing step.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ187A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-out; Lset-mono
        ; 𝒟ₒ; 𝒟ₒ∋⊆; layer-trans; Lset-layer )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Stage {ℓ} lem using ( stage; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- a. The frame hypothesis decomposes: AllCodes A is a definable subset
--    of Lset δ for some δ ∈ lam (Lset-out), hence a subset of Lset δ
--    (𝒟ₒ∋⊆).
-- =====================================================================
Allcodes-in-stage : (A : Sʟ) (lam : V ℓ)
  → ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
  → ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩
       × ((z : V ℓ) → ⟨ z ∈ˢ fst (AllCodes A) ⟩ → ⟨ z ∈ˢ Lset δ ⟩)) ∥₁
Allcodes-in-stage A lam All∈Lλ =
  PT.map go (Lset-out lam (fst (AllCodes A)) All∈Lλ)
  where
  go : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩ × ⟨ fst (AllCodes A) ∈ˢ 𝒟ₒ (Lset δ) ⟩)
     → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩
          × ((z : V ℓ) → ⟨ z ∈ˢ fst (AllCodes A) ⟩ → ⟨ z ∈ˢ Lset δ ⟩))
  go (δ , δ∈lam , AC∈𝒟ₒδ) =
    δ , δ∈lam , 𝒟ₒ∋⊆ (Lset δ) (fst (AllCodes A)) AC∈𝒟ₒδ

-- =====================================================================
-- b. With w ⊆ AllCodes A, every member of w lies in Lset lam: the stage
--    is transitive, so AllCodes A ⊆ Lset lam, and w ⊆ AllCodes A.
-- =====================================================================
w⊆Lλ : (A : Sʟ) (lam : V ℓ) (w : Sʟ)
  → ((z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ fst (AllCodes A) ⟩)
  → ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
  → (z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ Lset lam ⟩
w⊆Lλ A lam w w⊆All All∈Lλ z z∈w =
  layer-trans (Lset-layer lam) (w⊆All z z∈w) All∈Lλ

-- =====================================================================
-- c. One direction of the frame hypothesis's equivalence: the stage of
--    AllCodes A below lam gives AllCodes A ∈ Lset lam (Lset-mono with
--    stage-mem).  The other direction (stage ∈ lam) needs the
--    ordinals-in-stages machinery and is not needed here.
-- =====================================================================
stage→mem : (x : V ℓ) (c : ⟨ isL x ⟩) (lam : V ℓ)
  → ⟨ stage x c ∈ˢ lam ⟩ → ⟨ x ∈ˢ Lset lam ⟩
stage→mem x c lam s∈lam = Lset-mono {α = lam} {β = stage x c} s∈lam
  (stage-mem x c)
