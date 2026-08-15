# The LJ-1.311 `#`-bridge probe: does the R-41 disease fire through the
# library's numeral iterate `#_`, which `[LJ-1.309]`'s `sucIter` filter cannot
# see?

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-311.Bridge {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Constructible {ℓ} using ( Lset )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- INSTRUMENT ANCHOR.  [LJ-1.292]'s `w2` / [LJ-1.309]'s `b2`: a depth-2
-- explicit `sucV` chain against the `sucIter` numeral iterate.  Expected
-- about 219 ms.  If this arm is not charged, the run is instrument-blind
-- and every negative below is void.
-- =====================================================================

b2 : (σ x : V ℓ) → ⟨ x ∈ sucV (sucV σ) ⟩ → ⟨ x ∈ sucIter 2 σ ⟩
b2 σ x p = p

-- =====================================================================
-- THE `#` FAMILY.  `#_` is a numeral iterate: `# suc n = sucV (# n)`
-- (library Constructions:164-166).  The candidate site the census missed
-- is Name.lagda.md:129-135, where `pr∈Lset-suc (# (k + j))` produces
-- `Lset (sucV (sucV (# (k + j))))` against `Lset-mono`'s beta, which the
-- membership argument spells `# (suc (suc (k + j)))`.
-- =====================================================================

-- h1: depth 1, one `sucV` directly over the iterate.  The free family in
-- the sucIter ladder.  Prediction: not charged.
h1 : (m : ℕ) (x : V ℓ) → ⟨ x ∈ sucV (# m) ⟩ → ⟨ x ∈ # (suc m) ⟩
h1 m x p = p

-- h2: THE NAME SITE'S TERMS, depth 2, bare membership.
h2 : (m : ℕ) (x : V ℓ)
   → ⟨ x ∈ sucV (sucV (# m)) ⟩ → ⟨ x ∈ # (suc (suc m)) ⟩
h2 m x p = p

-- hL2: the NAME SITE ITSELF, the conversion in `Lset`'s level argument,
-- as the elaborator forces it at Name.lagda.md:130-135.
hL2 : (m : ℕ) (x : V ℓ)
    → ⟨ x ∈ˢ Lset (sucV (sucV (# m))) ⟩ → ⟨ x ∈ˢ Lset (# (suc (suc m))) ⟩
hL2 m x p = p

-- hsub2: the SUBJECT flavor, if the elaborator instead compares the
-- membership subjects under `ω`.
hsub2 : (m : ℕ) → ⟨ (# (suc (suc m))) ∈ˢ ω ⟩ → ⟨ (sucV (sucV (# m))) ∈ˢ ω ⟩
hsub2 m p = p

-- hm2: matched-spelling control, one spelling on both sides.
hm2 : (m : ℕ) (x : V ℓ)
   → ⟨ x ∈ # (suc (suc m)) ⟩ → ⟨ x ∈ # (suc (suc m)) ⟩
hm2 m x p = p

-- h3: depth 3, the next rung of the `#` ladder, if depth 2 charges.
h3 : (m : ℕ) (x : V ℓ)
   → ⟨ x ∈ sucV (sucV (sucV (# m))) ⟩ → ⟨ x ∈ # (suc (suc (suc m))) ⟩
h3 m x p = p

-- h4: depth 4, the rung where the `sucIter` ladder reaches 419,218 ms.
-- If the `#` ladder hides a 400-second prize anywhere, it is here.
h4 : (m : ℕ) (x : V ℓ)
   → ⟨ x ∈ sucV (sucV (sucV (sucV (# m)))) ⟩
   → ⟨ x ∈ # (suc (suc (suc (suc m)))) ⟩
h4 m x p = p

-- x2: the CROSS arm, a `sucIter` iterate at a `#` base against a chain.
-- Diagnostic for the b2-against-h2 asymmetry: does the iterate FUNCTION
-- decide the cost, or the base?  Also the shape a consumer of Key's
-- `KeyOver` sites would force if it instantiated sigma at a numeral.
x2 : (m : ℕ) (x : V ℓ)
   → ⟨ x ∈ sucV (sucV (# m)) ⟩ → ⟨ x ∈ sucIter 2 (# m) ⟩
x2 m x p = p
```
