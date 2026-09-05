# The LJ-1.292 second bisect: what separates the free site from the costly conversion

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-292.Bisect2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- LJ-1.292 BISECT 2.  `s0` (the site verbatim) is free while `s3` (the
-- full chain against the iterate, same member, base and depth) costs
-- 9,330 ms.  The one visible difference: every conversion at the site
-- compares `sucV (sucIter (n-1) σ)` against `sucIter n σ`, ONE `sucV`
-- directly over an iterate, never a full explicit chain.  These three
-- definitions price that one-deep spelling in isolation.
-- =====================================================================

-- d2: one-deep at depth 2.
d2 : (σ : V ℓ) → ⟨ σ ∈ sucV (sucIter 1 σ) ⟩ → ⟨ σ ∈ sucIter 2 σ ⟩
d2 σ p = p

-- d3: one-deep at depth 3, the SITE's member, base and depth.
d3 : (σ : V ℓ) → ⟨ σ ∈ sucV (sucIter 2 σ) ⟩ → ⟨ σ ∈ sucIter 3 σ ⟩
d3 σ p = p

-- d4: one-deep at depth 4, the DECISIVE arm.  `w4`, the full chain at
-- depth 4, costs 419,218 ms.  If this is free, the costly shape is
-- precisely a full explicit chain against a numeral iterate.
d4 : (δ a : V ℓ)
   → ⟨ sucV a ∈ sucV (sucIter 3 δ) ⟩ → ⟨ sucV a ∈ sucIter 4 δ ⟩
d4 δ a p = p
```
