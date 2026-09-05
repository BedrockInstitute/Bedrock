{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.644]  SECTION 6 UNDER ISOLATION.  `Probe644.agda` walled at
-- 600 s when this material sat inside it (runs/final-2.out).  The wall
-- is restructured here, one variant per run, so the obligation file
-- stays green while the shape is measured.
--
-- THE MEASUREMENT, IN THREE VARIANTS AND FOUR RUNS.
--
--   A  `ordL` on the raw package, no equality       runs/s6-a.out  2.66 s  EXIT=0
--   B  A plus the `ChosenSite` conjunct (`refl`)    runs/s6-b.out  2.64 s  EXIT=0
--   C  B, but the ambient cardinality read back
--      through `subst IsCardinal e` instead of
--      from `cardAboveAt` directly                  runs/s6-c.out  240 s   EXIT=142
--
--   and C is what `runs/final-2.out` paid 600 s for.
--
-- THE LAW THE THREE RUNS MEASURE.  Neither `ordL` nor the equality is
-- the cost.  **`subst IsCardinal e` AT A CONCRETE SEPARATION SITE is.**
-- `IsCardinal θ` unfolds to a Π-type over `⟪ θ ⟫`, and under `--cubical`
-- `subst` is a `transp` over that family, so supplying a CONCRETE `θ`
-- makes the elaborator transport across the whole separation set rather
-- than across a variable.  The cure is not to transport at all: the
-- producer already hands the fact over at its own site, so take it
-- there and let the equality carry only what has no other source.
--
-- 2.66 s against more than 240 s, at one `subst`.  The file below is
-- the surviving shape, A and B fused; C stands in this comment only.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-644.runs.S6 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.CardinalAbove {ℓ} lem using ( cardAboveAt; noInjOrd; ordL )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

NoInjAt : SV.S → Type (ℓ-suc ℓ)
NoInjAt a = Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))

ChosenSite : SL.S → Type (ℓ-suc ℓ)
ChosenSite κ =
  Σ[ a ∈ SV.S ] Σ[ oa ∈ IsOrd a ] Σ[ h ∈ NoInjAt a ]
    (fst (cardAboveAt a oa h) ≡ fst κ)

free-chosen-above :
    (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SL.S ]
       (ChosenSite θ × IsCardinal (fst θ) × ⟨ a ∈ˢ fst θ ⟩) ∥₁
free-chosen-above a oa = PT.map build (noInjOrd a oa)
  where
  build : NoInjAt a
        → Σ[ θ ∈ SL.S ]
            (ChosenSite θ × IsCardinal (fst θ) × ⟨ a ∈ˢ fst θ ⟩)
  build h =
      ordL (fst (cardAboveAt a oa h)) (cardAboveAt a oa h .snd .fst)
    , (a , oa , h , refl)
    , cardAboveAt a oa h .snd .snd .fst
    , cardAboveAt a oa h .snd .snd .snd
