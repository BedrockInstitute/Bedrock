{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.623]  W3, THE WIDEST UNMEASURED TERM: [LJ-1.618]'s `Inj-extract`,
-- re-ascribed at SiteFiber's frame, TYPE ONLY.
--
-- THE FRAME is the one [LJ-1.621] states `SiteFiber` at
-- (agents/tasks/LJ-1-621/Probe621.agda:40-42): the site telescope
-- (lem, alpha, o-alpha, alpha-not-in-omega).  The type is
-- [LJ-1.618]'s residue VERBATIM
-- (agents/tasks/LJ-1-618/Probe618.agda:151-154), the untruncation of
-- the least-cardinal injection: one honest ambient injection read out
-- of the truncated statement the tree's own search returns
-- (`κ-injL`, src/L/SquareLawClosed.lagda.md:82-84, sealed from
-- `κ-inj`, src/L/Cardinal.lagda.md:133-134).
--
-- TYPE ONLY.  No term of this file proves anything.  No term of this
-- file inhabits the type: that is the residue this task must clear,
-- and the clearing is measured in the probe, not assumed here.  The
-- site parameters (alpha, o-alpha, alpha-not-in-omega) do not occur
-- in the type; the frame is carried because the brief re-ascribes the
-- residue AT SiteFiber's frame, so that the probe can tie this row to
-- [LJ-1.618]'s spelling by one refl and the two cannot drift.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Cap: TWO MINUTES, set and reported by
-- this task (runs/w3-1.out).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-623.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) (oα : IsOrd α)
  (α∉ω : ⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥) where

open InfinitySet using ( ω )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.SquareLawClosed {ℓ} lem ω ω-ord
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE RESIDUE, TYPE ONLY, at the site frame.  [LJ-1.618]'s
-- `Inj-extract` (agents/tasks/LJ-1-618/Probe618.agda:151-154), word
-- for word, inside [LJ-1.621]'s telescope.  NOT INHABITED here.
-- =====================================================================

Inj-extract-at-site : Type (ℓ-suc ℓ)
Inj-extract-at-site = (a : S) (oa : IsOrd (fst a))
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
            → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫
