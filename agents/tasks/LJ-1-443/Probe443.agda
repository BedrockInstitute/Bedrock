{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.443] W3 PROBE.  Do the two landed spellings of the truncation
-- family meet as the identity?  It runs in agents/tasks/LJ-1-443/
-- and lands nothing in src/.  The stated NO-GO is Probe443NoGo.agda.
--
--   TERM      `domains-meet`.  Identity from the supply spelling
--             (δ : V ℓ, ∈) to the consumer spelling (δ : S, ∈ˢ).
--             Obligation omitted.  The named chapter
--             src/L/StageBound.lagda.md is not in this tree, so this
--             miniature uses V.Hierarchy and L.Ordinal.SquareLaw,
--             which are.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-443.Probe443 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open hPropStructure 𝒮ᵥ

domains-meet :
    ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
  → ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
domains-meet f = f
