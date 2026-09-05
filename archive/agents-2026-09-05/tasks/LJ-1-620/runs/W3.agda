{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.620]  W3.  THE IMPORT CLOSURE OF INGREDIENT (v), TYPE ONLY.
--
-- The brief names the widest unmeasured term of this task: the import
-- closure of ingredient (v), `keyS`, the smallest of the four.  This
-- file is written FIRST and typechecked ALONE under the two-minute cap
-- the brief sets (runs/w3-1.out).  It is imported by Probe620.agda,
-- not restated.
--
-- The file's import block IS the measurement: the lines below are the
-- smallest set under which the two rows of (v) elaborate, one per
-- direction of the paid ingredient.  The host question of the brief
-- asks, of the masters under src/, which one already contains every
-- line here; the answer is read off that graph and cited in the
-- report at file:line.
--
-- W3.1  `keyS` at `A := LsetS δ oδ`, the row [LJ-1.600] paid
--       (agents/tasks/LJ-1-600/Probe600.agda:129-130): every meta
--       formula at this carrier has a code, an element of L.
-- W3.2  THE COLLECTION, the row [LJ-1.600] paid in Probe600 section 0
--       (agents/tasks/LJ-1-600/Probe600.agda:108-115): AllCodes at
--       this carrier is an element of L that lives in its EARLIEST
--       stage, the stage named by L.Stage's three projections.  This
--       row is the half of the closure [LJ-1.600]'s W3 did not carry:
--       it is what imports L.Stage.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-620.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; AllCodes )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

-- W3.1  THE KEY, AT THE CONCRETE CARRIER.  TYPE ONLY.
key-at-stage : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
key-at-stage δ oδ = keyS (LsetS δ oδ)

-- W3.2  THE CARRIER'S FIRST COMPONENT IS THE STAGE ITSELF, BY REFL.
--       The alphabet the keys range over is the stage's members and
--       no bridge is forced on any consumer.
stage-carrier : (δ : V ℓ) (oδ : IsOrd δ) → LsetS δ oδ .fst ≡ Lset δ
stage-carrier δ oδ = refl

-- W3.3  THE CODES, COLLECTED, AND THE STAGE THAT HOLDS THEM.  The
--       two lines [LJ-1.600] paid in section 0, at this carrier:
--       AllCodes at `LsetS δ oδ` is an element of L that sits in its
--       earliest stage, with ordinality and membership from the three
--       projections of src/L/Stage.lagda.md.  This is the half of the
--       (v) closure that imports L.Stage, and the half a host must
--       already contain if the landing adds no new import line.
codes-stage : (δ : V ℓ) (oδ : IsOrd δ)
  → Σ[ σ ∈ V ℓ ]
      ( IsOrd σ × ⟨ AllCodes (LsetS δ oδ) .fst SV.∈ˢ Lset σ ⟩ )
codes-stage δ oδ =
  stage (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)
    , stage-ord (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)
    , stage-mem (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)
