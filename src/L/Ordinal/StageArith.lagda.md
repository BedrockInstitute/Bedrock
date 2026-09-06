# The stage-arithmetic kit

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.StageArith {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

Pointwise inclusion at the big membership, as the ordinal chapters read it.

```agda
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩
```

The finite successor chain above a stage.

```agda
sucIter : ℕ → S → S
sucIter zero u = u
sucIter (suc n) u = sucV (sucIter n u)
```

The ω-block above a stage: the union of the finitely iterated successors.
The union representation is sealed at birth (R-38). Consumers see an atom.

```agda
opaque
  +ω : S → S
  +ω u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u))

opaque
  unfolding +ω

  -- One direction: a member of a finite iterate is a member of the block.

  -- The base and every finite iterate lie in the block.

  -- Ordinality: each iterate is an ordinal, and the block is an ordinal.
  sucIter-ord : {u : S} → (n : ℕ) → IsOrd u → IsOrd (sucIter n u)
  sucIter-ord zero ou = ou
  sucIter-ord (suc n) ou = suc-ord (sucIter-ord n ou)

```

Closure under +ω: the ω-block above every member stays inside α.

```agda
```

The code set over the carrier at δ sits at stage δ+ω. Under closure, the
stage δ+ω stays below α for every δ below α, so the bound lands in Lset α.

```agda
```

The environment at δ+3 lifts by the finite-iterate law, then by closure.

```agda
```
