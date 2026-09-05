{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.365 solo control run.  EXPECTED RED.  It lands nothing.
-- One control active, so Agda prints its refusal alone.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-365.SoloC3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import LJ-1-365.ProbeLJ1365A {ℓ} lem using ( LimitBandT )
open import LJ-1-337.ProbeLJ1337D {ℓ} lem using ( stage-card-from-band )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- CONTROL 3, SOLO.  The delivered consumer, fed the truncated band.
band-refusal : (α : S) (oα : IsOrd α) → LimitBandT
             → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
band-refusal α oα t = stage-card-from-band α oα t
