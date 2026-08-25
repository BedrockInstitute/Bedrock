{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  FLOOR ARM.  Probe603.agda WITHOUT section 1's value
-- equation rows: the frame the rows sit in, priced before the rows
-- land (owner's ruling of 2026-08-23).  Kept as the floor record.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-603.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- (section 1 removed: the value equation rows)

-- THE FINITE BASE BESIDE IT, IMPORTED.
import LJ-1-601.runs.W3 {ℓ} lem α₀ oα₀ sq as W601
import LJ-1-601.Probe601 {ℓ} lem α₀ oα₀ sq as P601

the-finite-base-has-a-formula : (n : ℕ) → W601.TallyGraph n
the-finite-base-has-a-formula = P601.finite-base-measured

-- THE BRANCH'S LIMIT CASE, TYPE ONLY.
branch-type :
  (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((ε : V ℓ) → ⟨ ε ∈ˢ α ⟩ → SC.Upper.P ε)
  → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
branch-type = SC.Upper.branch

P-is-the-injection :
  (ε : V ℓ) → SC.Upper.P ε
            ≡ ( IsOrd ε → ⟨ ε ∈ˢ sucV α₀ ⟩ → (⟨ ε ∈ˢ ω ⟩ → Empty.⊥)
              → (⟪ Lset ε ⟫ ↪ ⟪ ε ⟫) )
P-is-the-injection _ = refl
