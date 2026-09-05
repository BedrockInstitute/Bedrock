{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.613]  W3.  THE WIDEST UNMEASURED TERM: ingredient (i) of the
-- `class-pred` table, RE-ASCRIBED AT THIS CARRIER, TYPE ONLY.
--
-- The brief names it ("It is ingredient (i) at this carrier") and
-- orders this file written FIRST and typechecked ALONE under a cap this
-- task sets at TWO MINUTES (runs/w3-*.out).
--
-- WHAT INGREDIENT (i) IS, at file:line.  [LJ-1.594]'s table row
-- (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40): "`D`, the
-- definable power set | INTERNAL. `D-at-the-site`,
-- `Probe594.agda:227-234`: at the real site `limit-step` supplies
-- `DefOf.defSet (Lset ·)` and `𝒟ₒ-inv`".  So (i) is TWO terms, and
-- both were measured only THROUGH the site's own call
-- (src/L/StageCardinal.lagda.md:399-403):
--   * the operator, `DefOf.defSet` at the stage
--     (src/L/Definability.lagda.md:111-112), in the parameter shape
--     `LimitStep` declares for `D` (src/L/StageCardinal.lagda.md:278);
--   * the inversion, `𝒟ₒ-inv` (src/L/Constructible.lagda.md:306-308),
--     in the parameter shape `LimitStep` declares for `inv` (:279-280).
-- NOBODY has written either one STANDALONE at the carrier.  This file
-- is that, and nothing else.
--
-- "THIS CARRIER" is [LJ-1.600]'s: the stage's members `⟪ Lset δ ⟫`,
-- the alphabet of `Formula ⟪ Lset δ ⟫ 1`
-- (agents/tasks/LJ-1-600/runs/W3.agda:52-53).  ONE spelling
-- throughout, R-41's cure (dev/LESSONS.md:4762): the site's own
-- (`Formula ⟪ Lset δ ⟫ 1`, src/L/StageCardinal.lagda.md:278).  No
-- bridge anywhere: `Lset` at `V ℓ` is the chapter's own application.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-613.runs.W3 {ℓ : Level} where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- W3.1  INGREDIENT (i), FIRST HALF, AT THIS CARRIER.  The site's own
--       supply (src/L/StageCardinal.lagda.md:400), standalone at every
--       stage, in `LimitStep`'s own shape for `D` (:278).  TYPE ONLY:
--       no row here proves anything about the term.
D-at-carrier : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ
D-at-carrier δ φ = DefOf.defSet (Lset δ) φ

-- W3.2  INGREDIENT (i), SECOND HALF, AT THIS CARRIER.  The inversion
--       the site supplies at :401, standalone, in `LimitStep`'s own
--       shape for `inv` (:279-280).  TYPE ONLY.
inv-at-carrier : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
               → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D-at-carrier δ φ₀ ≡ y) ∥₁
inv-at-carrier δ y h = 𝒟ₒ-inv (Lset δ) y h
