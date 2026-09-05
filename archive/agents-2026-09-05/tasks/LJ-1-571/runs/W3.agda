{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.571]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it "`SqLaw`'s own carrier", written as
--
--     -- SqLaw (fst κ), unfolded one step, TYPE ONLY
--
-- and says it decides the whole shape of the task.  This file is TYPE
-- ONLY: no inhabitant, no hole, no postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-571.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- THE ANSWER IS IN THE FIRST LINE: the binder is `SV.S` and the
-- carriers are `⟪ δ ⟫`.  Both are AMBIENT.  `SL.S` occurs ONLY at the
-- outer `κ`, and it is spent at once by `fst κ` to reach the ambient
-- side.  Nothing under the arrow mentions `isL`, `Lset` or `𝒮ʟ`.
w3-sqlaw-at : SL.S → Type (ℓ-suc ℓ)
w3-sqlaw-at κ =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV (fst κ) ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- And the row itself, one step further out.  TYPE ONLY.
w3-sqat : Type (ℓ-suc ℓ)
w3-sqat = (κ : SL.S) → IsOrd (fst κ) → w3-sqlaw-at κ
