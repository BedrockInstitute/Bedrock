# The LJ-1.311 ladder re-measurement: do the depth-3 and depth-4 rungs of
# `[LJ-1.292]`'s bisect survive in the delivered sites' own setting (an
# abstract stage function `T`)?  P-l: the ladder was priced on a bare
# membership; only its depth-2 rung was re-measured in setting (`[LJ-1.309]`,
# t2 219 ms against b2 221 ms).  This file prices depth 3 and depth 4 the
# same way, plus a repeat of `[LJ-1.309]`'s t7 for run-to-run spread.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-311.Ladder3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- t7r: a REPEAT of [LJ-1.309]'s t7, the splitKey∈ conversion isolated, for
-- run-to-run spread against its 261 ms.
t7r : (T : V ℓ → V ℓ) (σ x : V ℓ)
    → ⟨ x ∈ T (sucV (sucV (sucIter 5 σ))) ⟩ → ⟨ x ∈ T (sucIter 7 σ) ⟩
t7r T σ x p = p

-- b3: the BARE anchor at depth 3, [LJ-1.292]'s w3 re-measured.
b3 : (σ x : V ℓ) → ⟨ x ∈ sucV (sucV (sucV σ)) ⟩ → ⟨ x ∈ sucIter 3 σ ⟩
b3 σ x p = p

-- t3: depth 3 under an abstract stage function, the delivered setting.
t3 : (T : V ℓ → V ℓ) (σ x : V ℓ)
   → ⟨ x ∈ T (sucV (sucV (sucV σ))) ⟩ → ⟨ x ∈ T (sucIter 3 σ) ⟩
t3 T σ x p = p

-- t4: depth 4 under an abstract stage function.  [LJ-1.292]'s bare w4
-- measured 419,218 ms here.  If the abstract setting transfers, this arm
-- costs about seven minutes and the file's wall stays under the 30-minute
-- abort line.
t4 : (T : V ℓ → V ℓ) (σ x : V ℓ)
   → ⟨ x ∈ T (sucV (sucV (sucV (sucV σ)))) ⟩ → ⟨ x ∈ T (sucIter 4 σ) ⟩
t4 T σ x p = p
```
