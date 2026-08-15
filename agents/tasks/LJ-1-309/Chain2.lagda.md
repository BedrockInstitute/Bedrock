# The LJ-1.309 chain-2 bisect: what a depth-2 full chain costs under an ABSTRACT stage function

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-309.Chain2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- LJ-1.309 CENSUS ARM.  The census found THREE full-chain sites in
-- `src/`, all at depth 2, all inside `module KeyOver (T : S → S)` at
-- `src/L/Coding/Key.lagda.md:82-91`.  [LJ-1.292] priced a depth-2 full
-- chain against a numeral iterate at 219 ms, but it priced it on a
-- BARE membership with a variable base.  The delivered sites run under
-- an ABSTRACT stage function.  P-l: that is a hypothesis until it is
-- measured here.  These five definitions measure it.
-- =====================================================================

-- b2: the BARE membership, full chain depth 2 against numeral iterate 2.
-- This is [LJ-1.292]'s `w2` re-measured, the anchor of this run.
b2 : (σ x : V ℓ) → ⟨ x ∈ sucV (sucV σ) ⟩ → ⟨ x ∈ sucIter 2 σ ⟩
b2 σ x p = p

-- t2: THE SITE'S OWN SETTING, rank 1 of the census.  An abstract stage
-- function, exactly as `KeyOver`'s parameter at `Key.lagda.md:83`, and
-- the conversion `pair∈` runs at `Key.lagda.md:118-120`.
t2 : (T : V ℓ → V ℓ) (σ x : V ℓ)
   → ⟨ x ∈ T (sucV (sucV σ)) ⟩ → ⟨ x ∈ T (sucIter 2 σ) ⟩
t2 T σ x p = p

-- t7: ranks 2 and 3 of the census, `splitKey∈` at `Key.lagda.md:129-133`.
-- A depth-2 chain over an ITERATE base, against a deeper numeral iterate.
t7 : (T : V ℓ → V ℓ) (σ x : V ℓ)
   → ⟨ x ∈ T (sucV (sucV (sucIter 5 σ))) ⟩ → ⟨ x ∈ T (sucIter 7 σ) ⟩
t7 T σ x p = p

-- m2: the matched-spelling control.  One spelling on both sides.
m2 : (T : V ℓ → V ℓ) (σ x : V ℓ)
   → ⟨ x ∈ T (sucV (sucV σ)) ⟩ → ⟨ x ∈ T (sucV (sucV σ)) ⟩
m2 T σ x p = p

-- d2: the FREE spelling, one `sucV` over the iterate.  [LJ-1.292]'s `d2`
-- was not charged; this repeats it under the same run as the arms above.
d2 : (σ x : V ℓ) → ⟨ x ∈ sucV (sucIter 1 σ) ⟩ → ⟨ x ∈ sucIter 2 σ ⟩
d2 σ x p = p
```
