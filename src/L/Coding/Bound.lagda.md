# The bound at a limit

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Bound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

A stage function and the two facts the numeral argument uses.  Nothing in
this module names a tower: the argument climbs by one successor, and every
tower supplies that shape.

```agda
module BoundOver
  (T : S → S)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-ord : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ T (sucV δ) ⟩)
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
```

Every numeral is an ordinal of the limit, by the two parameters alone.

```agda
  #∈λ : (k : ℕ) → ⟨ (# k) ∈ˢ lam ⟩
  #∈λ zero    = ∅∈λ
  #∈λ (suc k) = succλ (# k) (#∈λ k)
```

The formula set: Devlin's `𝓕 ∪ {vᵢ}`, here the numerals.

```agda
  #∈Tλ : (k : ℕ) → ⟨ (# k) ∈ˢ T lam ⟩
  #∈Tλ k = T-mono {α = lam} {β = sucV (# k)} (#∈λ (suc k))
    {x = # k} (T-ord (# k) (numeral-ord k))
```

The L tower supplies the two facts outright: `Lset-mono` and
`ord∈Lset-suc`, one call each.

```agda
module Bound (lam : S) (ordλ : IsOrd lam)
             (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  open BoundOver Lset Lset-mono ord∈Lset-suc lam ordλ succλ ∅∈λ public
```

The numerals as elements of L, and the model's own pair. Both are the L
presentation of a fact `BoundOver` already has.

```agda
  num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  num∈λ k = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (numeralL-fst k)) (#∈Tλ k)
```
