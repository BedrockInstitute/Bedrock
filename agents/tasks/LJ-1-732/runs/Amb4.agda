{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb4 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Condensation {ℓ} lem using ( domB )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-520.Probe520 {ℓ} lem as P520
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open import LJ-1-732.runs.Amb6 {ℓ} lem
open import LJ-1-732.runs.Amb7 {ℓ} lem

-- the graph at the empty table: the table member is ∅, and every
-- branch inside dies at a membership in it or in the empty parameter
graph-part :
    ⟨ γ15 P652.⊨ₚ CntS.erase Mx.G.graphBndAt countGB ⟩
graph-part = ∣ n 0 , (mem0 , approx-part , step-part) ∣₁
