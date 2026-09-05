{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.584]  W3.  `step`, RE-ASCRIBED ALONE.  TYPE ONLY, AND THE ONE
-- DEPENDENCE THE FORMULA WOULD HAVE TO DESCRIBE.
--
-- The brief: "If `step` cannot be described by a formula, neither can
-- the injection, and you will know in the first hour."

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-584.runs.W3b {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( sucV; ω )
import L.StageCardinal

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- W3.1  `step`, RE-ASCRIBED ALONE.  src/L/StageCardinal.lagda.md:561-562.
step : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) → SC.Upper.P α
step = SC.Upper.step

-- W3.2  AND `step` IS `limit-step` AT `branch`.  The elaborator's word,
--       by `refl`.  src/L/StageCardinal.lagda.md:562.
step-is-limit-step :
    (α : S) (IH : (δ : S) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
    (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → step α IH oα α∈suc infα
    ≡ SC.limit-step α α∈suc oα infα (SC.Upper.branch α oα α∈suc infα IH)
step-is-limit-step _ _ _ _ _ = refl

