{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.337 probe D.  It lands nothing.  It runs in agents/tasks/LJ-1-337/.
--
-- THE CONSUMER CHECK (C-40).  `[LJ-1.335]` section 4.1 promised that
-- `sq-below` lets a caller supply ONE BAND where the delivered chapter
-- asks for a whole FAMILY.  This file MEASURES the promise: it
-- instantiates `L.StageCardinal` with `sq-below α oα lb` and reads
-- `stage-card-upper` out of it.  The only open hypothesis left in the
-- statement is `LimitBand`.
--
-- IT LIVES ALONE because the instantiation is expensive, the same reason
-- `[LJ-1.332]` gave at ProbeLJ1332B.agda:11-12.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-337.ProbeLJ1337D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand; sq-below )
import L.StageCardinal

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- THE NARROWING, MEASURED.  One band in, the delivered conclusion out.
-- No signature under src/ changes, and the diff to
-- src/L/StageCardinal.lagda.md and src/L/BoundedSubset.lagda.md is EMPTY.
stage-card-from-band : (α : S) (oα : IsOrd α) → LimitBand
                     → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
stage-card-from-band α oα lb =
  SC.Upper.stage-card-upper α oα (self∈sucV α)
  where
  module SC = L.StageCardinal {ℓ} lem α oα (sq-below α oα lb)
