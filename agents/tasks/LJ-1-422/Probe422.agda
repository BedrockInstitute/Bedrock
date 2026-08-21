{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.422] PROBE.  The untruncated least-cardinal arrow, or the
-- device the tree lacks.
--
--   W3        `device-covers-carrier`.  Apply swo-into-ord, at
--             [LJ-1.417]'s type, to THIS carrier: the type of
--             injections.  The only nearby delivered SWO is ordSWO
--             on the domain (SquareLaw:176).  One device, one
--             fragment, one run.
--
--   TERM      `kappa-arrow-data`.  Same application, at the
--             named target.  Not inhabited: the device returns an
--             injection into SOME ordinal, from a carrier that
--             still needs an SWO this tree does not deliver.
--
--   FOUR MODULE HYPOTHESES, not imported, not rebuilt:
--             `κL`, `κoL` at [LJ-1.406]'s types (Probe406.agda:82, :85),
--             `swo-into-ord` at [LJ-1.417]'s type (Probe417.agda:80),
--             `ordSWO` at src/L/Ordinal/SquareLaw.lagda.md:176.
--
-- ONE Agda process per run.  GHCRTS is the wide caliber the program
-- set on this pane.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-422.Probe422 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- The tree's embedding type, as Cardinal writes it
-- (src/L/Cardinal.lagda.md:47-48).
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- MODULE HYPOTHESES.  Not imported.  Not rebuilt.
-- =====================================================================

module _
  (κL : (a : S) (oa : IsOrd (fst a)) → S)
  (κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa)))
  (swo-into-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A)
                → Σ[ β ∈ V ℓ ] (IsOrd β × (A ↪ ⟪ β ⟫)))
  (ordSWO : (α : V ℓ) (oα : IsOrd α) → SWO {ℓc = ℓ} ⟪ α ⟫)
  where

  -- W3.  The truncation sits over ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫.
  -- swo-into-ord ranks a carrier that already carries an SWO.  Feed
  -- it the delivered domain order and ask for a ranking of THIS
  -- carrier.  The elaborator must reject the SWO argument.
  device-covers-carrier :
      (a : S) (oa : IsOrd (fst a))
    → Σ[ β ∈ V ℓ ] (IsOrd β × ((⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫) ↪ ⟪ β ⟫))
  device-covers-carrier a oa =
    swo-into-ord {A = ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫} (ordSWO (fst a) oa)

  -- THE OBLIGATION.  Same fragment, at the named target.  Even a
  -- well-typed ranking would inject the injection-type into SOME
  -- ordinal, not produce one injection into the named κL.
  kappa-arrow-data :
      (a : S) (oa : IsOrd (fst a))
    → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫
  kappa-arrow-data a oa =
    snd (snd (swo-into-ord {A = ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫} (ordSWO (fst a) oa)))
