{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.418] PROBE.  The stage injects into an ordinal, at EVERY
-- ordinal, with no pairing.
--
--   W3 FIRST  `carry-at-generic`.  One application of carry to
--             orderAt, at a generic ordinal.  Stated alone and run
--             before the Sigma.
--
--   TERM      `stage-into-bound`.  Feed that order to swo-into-ord
--             at [LJ-1.417]'s type.  Some β, no bound relating β
--             and α.
--
--   ONE MODULE HYPOTHESIS, not imported, not rebuilt:
--             `swo-into-ord` at [LJ-1.417]'s type.  The rank is
--             not rebuilt.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands
-- in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-418.Probe418 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( orderAt; carry )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The tree's embedding type, as Cardinal writes it
-- (src/L/Cardinal.lagda.md:47-48).
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- W3.  carry and orderAt at a generic ordinal.  No Init, no band, no
-- infiniteness, no SiteBound.  orderAt stays sealed: this term names
-- it and does not unfold it (P-l, P-y).  Carrier at ℓ (ℓc = ℓ).  Order
-- at ℓ-suc ℓ (the instantiation of WellOrder.Base above).
-- =====================================================================

carry-at-generic : (α : S) → IsOrd α → SWO {ℓc = ℓ} ⟪ Lset α ⟫
carry-at-generic α oα = carry (Lset α) (orderAt α oα)

-- =====================================================================
-- THE OBLIGATION.  swo-into-ord at [LJ-1.417]'s type: generic small
-- carrier, generic SWO at order level ℓ-suc ℓ, no truncation, no rank.
-- The rank stays inside 417.  This task does not rebuild it.
-- =====================================================================

module _
  (swo-into-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A)
                → Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫)))
  where

  stage-into-bound : (α : S) → IsOrd α
                   → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))
  stage-into-bound α oα = swo-into-ord (carry-at-generic α oα)
