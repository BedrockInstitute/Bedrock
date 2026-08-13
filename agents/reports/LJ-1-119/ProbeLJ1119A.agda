{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.119] probe A: the restricted absorbs-subset at the site, and
-- the entry into Devlin55 and BoundedSubsetAt.
--
-- LJ-1.117 restricted sq by moving it from Devlin55's telescope into
-- BoundedSubsetAt, where the consumer names its arguments.  LJ-1.119
-- does the same for absorbs-subset: the master now takes
--   absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
-- in BoundedSubsetAt's telescope (src/L/BoundedSubset.lagda.md:1397),
-- and Devlin55 has no parameter.  The [LJ-1.118] site value supplies
-- absorbs at α = ω, x = ∅ (P118.Site.site-inj), so this probe enters
-- Devlin55, enters BoundedSubsetAt with the fifteen site values, and
-- reports the first hypothesis nothing supplies.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1119A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import L.BoundedSubset {ℓ} lem as BS
open BS using ( _↪_ )
import ProbeLJ194A {ℓ} lem as P194
import ProbeLJ1117A {ℓ} lem as P117
import ProbeLJ1118A {ℓ} lem as P118
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE RESTRICTED MODULE AT THE SITE: Devlin55 has no parameters now.
-- absorbs is supplied by the [LJ-1.118] site value at α = ω, x = ∅.
-- =====================================================================
module D55 = BS.Devlin55

module BA = D55.BoundedSubsetAt
  P194.SiteAt.κ
  P194.SiteAt.ordκ
  P194.SiteAt.cardκ
  P194.SiteAt.κ∉ω
  P194.SiteAt.α
  P194.SiteAt.ordα
  P194.SiteAt.α∈κ
  P194.SiteAt.α∉ω
  P117.sqω
  P194.SiteAt.x
  P194.SiteAt.x⊆Lα
  P118.Site.site-inj
  P194.SiteAt.lam
  P194.SiteAt.ordλ
  P194.SiteAt.α∈λ
  P194.SiteAt.succλ
  P194.SiteAt.x∈Lλ

-- =====================================================================
-- THE NEXT BOUNDARY: Co's telescope.  The first hypotheses the site
-- does not supply are levelIn and cover; they are the abort criterion's
-- good stop.  Entering Co with them as parameters forces the body to
-- elaborate with them abstract, which checks code-inj against the
-- restricted absorbs (BA.absorbs, the [LJ-1.118] site value).
-- =====================================================================
module C0 (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BA.HS.C.πX ⟩)
          (cover : (y : S) → ⟨ y ∈ˢ BA.HS.M ⟩ → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BA.HS.C.πX ⟩ × ⟨ BA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁) where

  module C0' = BA.Co levelIn cover

  code-inj : _↪_ ⟪ BA.UK.X ⟫ ⟪ P194.SiteAt.α ⟫
  code-inj = C0'.code-inj
