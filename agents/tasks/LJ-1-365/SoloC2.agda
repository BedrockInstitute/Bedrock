{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.365 solo control run.  EXPECTED RED.  It lands nothing.
-- One control active, so Agda prints its refusal alone.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-365.SoloC2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( S )

-- CONTROL 2, SOLO.  The wrap at the body's first data goal.
wrap-at-injection : (α : S) → (body : sq α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫)
                  → ∥ sq α ∥₁ → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
wrap-at-injection α body =
  PT.rec {P = ⟪ Lset α ⟫ ↪ ⟪ α ⟫} squash₁ body
