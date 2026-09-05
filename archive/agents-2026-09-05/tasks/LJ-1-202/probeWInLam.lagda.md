# LJ-1.202 probe: is `ω ∈ lam` derivable at the sole `HullStage` site?

The lead (INFERRED) claims an ordinal not in `ω` satisfies `ω ∈ α` or
`ω ≡ α`, so `α∈λ` carries `ω ∈ lam`. The derivation below uses exactly the
facts in scope at `src/L/BoundedSubset.lagda.md:1380-1405`:
`ord-tri` (`:879`), `ω` (`:886`), `ω-ord` (`:1040`), and the module
parameters `ordα`, `ordλ`, `α∈λ`, `α∉ω`.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module probeWInLam {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )

import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The one derivation, at the instantiation site's own hypotheses.
module Derive
  (α lam : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  ω∈λ : ⟨ ω ∈ˢ lam ⟩
  ω∈λ = Sum.rec
    (λ α∈ω → Empty.rec (α∉ω α∈ω))
    (Sum.rec (λ α≡ω → subst (λ w → ⟨ w ∈ˢ lam ⟩) α≡ω α∈λ)
             (λ ω∈α → ordλ .fst ω∈α α∈λ))
    (ord-tri α ordα ω ω-ord)
```
