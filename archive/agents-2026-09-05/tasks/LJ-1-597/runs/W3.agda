{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.597]  W3.  `step`, RE-ASCRIBED ALONE.  TYPE ONLY.
--
-- The brief: "Write it FIRST and typecheck it ALONE.  ESTIMATE: about
-- 12 lines, under 90 seconds."
--
-- THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.  ONE AGDA
-- PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-597.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import L.StageCardinal

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- W3.1  `step`, RE-ASCRIBED ALONE.  src/L/StageCardinal.lagda.md:561-562.
-- It takes a stage and the induction hypothesis at every member stage,
-- and it returns the stage's own injection.
step : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) → SC.Upper.P α
step = SC.Upper.step
