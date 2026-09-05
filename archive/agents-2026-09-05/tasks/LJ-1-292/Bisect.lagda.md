# The LJ-1.292 bisect: price the mixed spelling at `Key.lagda.md:424-429`

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-292.Bisect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- LJ-1.292 BISECT.  Each definition isolates ONE conversion at the site
-- src/L/Coding/Key.lagda.md:424-429.  `--profile=definitions` charges
-- each of them separately, so one run prices every step.
--
-- The site sits under the BARE membership `⟨ _ ∈ _ ⟩` at V.  The first
-- site, [LJ-1.287]'s `sucV∈`, sat under `⟨ _ ∈ Lset _ ⟩` with `Lset`
-- opaque.  `l4` below is [LJ-1.287]'s `v4` VERBATIM, so the same run
-- anchors this harness to its measured 438,043 ms and prices the
-- wrapper's share by contrast.
-- =====================================================================

-- s0: the SITE VERBATIM, the two applications at `Key.lagda.md:428-429`
-- with `α` inlined as its definition spells it at `:424`.
s0 : (σ : V ℓ) → ⟨ σ ∈ sucIter 3 σ ⟩
s0 σ = ∈sucV-inl {A = sucIter 2 σ} {x = σ}
         (∈sucV-inl {A = sucIter 1 σ} {x = σ} (self∈sucV σ))

-- s3: the site's own conversion in isolation.  `p = p` at the site's
-- member, base and depth, under the bare head.
s3 : (σ : V ℓ) → ⟨ σ ∈ sucV (sucV (sucV σ)) ⟩ → ⟨ σ ∈ sucIter 3 σ ⟩
s3 σ p = p

-- w1 to w4: the pure mixed conversion under the BARE head, the ladder.
-- [LJ-1.287]'s `v4` shape minus the `Lset` wrapper, member `sucV a`.
w1 : (δ a : V ℓ) → ⟨ sucV a ∈ sucV δ ⟩ → ⟨ sucV a ∈ sucIter 1 δ ⟩
w1 δ a p = p

w2 : (δ a : V ℓ)
   → ⟨ sucV a ∈ sucV (sucV δ) ⟩ → ⟨ sucV a ∈ sucIter 2 δ ⟩
w2 δ a p = p

w3 : (δ a : V ℓ)
   → ⟨ sucV a ∈ sucV (sucV (sucV δ)) ⟩ → ⟨ sucV a ∈ sucIter 3 δ ⟩
w3 δ a p = p

w4 : (δ a : V ℓ)
   → ⟨ sucV a ∈ sucV (sucV (sucV (sucV δ))) ⟩
   → ⟨ sucV a ∈ sucIter 4 δ ⟩
w4 δ a p = p

-- m3: the MATCHED-spelling control at depth 3, the `v5` shape.  Both
-- sides carry one spelling, so the checker never reduces either side.
m3 : (δ a : V ℓ)
   → ⟨ sucV a ∈ sucV (sucV (sucV δ)) ⟩
   → ⟨ sucV a ∈ sucV (sucV (sucV δ)) ⟩
m3 δ a p = p

-- l4: [LJ-1.287]'s `v4` VERBATIM, the ANCHOR.  Identical to `w4` except
-- the `Lset` wrapper, with `Lset` opaque upstream.
l4 : (δ a : V ℓ)
   → ⟨ sucV a ∈ Lset (sucV (sucV (sucV (sucV δ)))) ⟩
   → ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
l4 δ a p = p
```
