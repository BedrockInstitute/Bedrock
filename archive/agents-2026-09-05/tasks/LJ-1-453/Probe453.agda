{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.453] PROBE.  Do the two landed telescopes meet as the identity?
-- It runs in agents/tasks/LJ-1-453/ and lands nothing in src/.
--
--   W3 FIRST  `domains-meet`.  Typechecked ALONE, obligation omitted
--             from the chapter.  Body is the identity.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

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

module LJ-1-453.Probe453 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open hPropStructure 𝒮ᵥ

-- Supply spelling: V ℓ and ∈, as sq-trunc-closed
-- (src/L/SquareLawClosed.lagda.md:325-327).
-- Consumer spelling: S and ∈ˢ, as SqCollect's hypothesis
-- (the brief's type; SqFam is src/L/StageBound.lagda.md:33-37).
-- Body is the identity.  If this fails, the elaborator's error is
-- the finding.

domains-meet :
    ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
  → ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
domains-meet z = z
