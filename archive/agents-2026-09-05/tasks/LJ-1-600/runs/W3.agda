{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.600]  W3.  THE WIDEST UNMEASURED TERM: `keyS` INSTANTIATED AT
-- `A := LsetS δ oδ`, RE-ASCRIBED, TYPE ONLY.
--
-- The brief names it and orders this file written FIRST and typechecked
-- ALONE, under a wall-clock cap this task sets at TWO MINUTES
-- (runs/w3-*.out).  Nothing else is in this file.
--
-- `keyS` is the live chapter's own function
-- (src/L/Coding/CodeSet.lagda.md:300-301); this file instantiates its
-- carrier module parameter at `A := LsetS δ oδ`
-- (src/L/Axioms/Basic.lagda.md:160-161), so the alphabet the keys range
-- over is `⟪ Lset δ ⟫`, the site's own spelling of ingredient (v)
-- (src/L/StageCardinal.lagda.md:286, :321; the site's D takes
-- `Formula ⟪ Lset δ ⟫ 1` at :278).  ONE spelling throughout: R-41's cure
-- (dev/LESSONS.md:4762), and the only bridge is `fst (Lset δ , p)`
-- reducing to `Lset δ`, one definitional projection, depth one.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-600.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

-- W3.1  THE TERM, AT THE CONCRETE CARRIER.  src/L/Coding/CodeSet.
--       lagda.md:300-301 applied at `A := LsetS δ oδ`.  The application
--       elaborates only if `LsetS δ oδ : S`, and the written type only
--       checks if `⟪ LsetS δ oδ .fst ⟫` is `⟪ Lset δ ⟫`: both are the
--       one projection named in W3.2.  TYPE ONLY: no row here proves
--       anything about the term.
key-at-stage : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
key-at-stage δ oδ = keyS (LsetS δ oδ)

-- W3.2  THE CARRIER'S FIRST COMPONENT IS THE STAGE ITSELF, BY REFL.
--       `LsetS β oβ = Lset β , isL-Lset β oβ` is literal
--       (src/L/Axioms/Basic.lagda.md:160-161), so the alphabet is the
--       stage's members and no bridge is forced on any consumer.
stage-carrier : (δ : V ℓ) (oδ : IsOrd δ) → LsetS δ oδ .fst ≡ Lset δ
stage-carrier δ oδ = refl
