{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.600]  THE FLOOR.  The obligation STATED WITH A HOLE, and the
-- stage row stated with a hole, in Probe600's full import frame, so the
-- frame's own price is measured BEFORE the real bodies are written.
-- The brief orders it: "State the obligation with a hole and typecheck
-- it under an explicit wall-clock cap you set yourself."  This task's
-- cap for the floor is 300 s (runs/floor-*.out).  EXPECTED RESULT: exit
-- 42 at the two holes and nowhere else.  THIS FILE IS NOT THE
-- OBLIGATION'S DELIVERY; Probe600.agda is.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-600.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; AllCodes )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

key-at-stage : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
key-at-stage δ oδ = {! keyS (LsetS δ oδ) !}

allcodes-stage : (δ : V ℓ) (oδ : IsOrd δ)
               → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ AllCodes (LsetS δ oδ) .fst SV.∈ˢ Lset σ ⟩)
allcodes-stage δ oδ = {! stage , stage-ord , stage-mem !}
