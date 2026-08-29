{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb4a {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the graph reading at the empty instance, named once
GraphAt : Type (ℓ-suc ℓ)
GraphAt = ⟨ γ15 P652.⊨ₚ CntS.erase Mx.G.graphBndAt countGB ⟩
