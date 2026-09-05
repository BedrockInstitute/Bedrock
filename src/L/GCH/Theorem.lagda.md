# The constructible universe satisfies GCH

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Theorem {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.GCH.Assembly {ℓ} lem using ( gch-from-internal-bill )
open import L.GCH.StageCount {ℓ} lem using ( stage-counted )
open import L.GCH.SuccIntoPower {ℓ} lem using ( succ-into-power )
open import L.GCH.BoundedSubset {ℓ} lem using ( internal-bounded-subset )
```

The trophy: the internal bill of L.GCH.Assembly, paid in full.
StageCountedCoded by L.GCH.StageCount,
InternalBoundedSubset by L.GCH.BoundedSubset (the hull in L, its
collapse, condensation through the level formula, and the count),
SuccIntoPower by L.GCH.SuccIntoPower.

```agda
L⊨GCH : GCHStatement L⊨ZF
L⊨GCH = gch-from-internal-bill L⊨ZF stage-counted internal-bounded-subset
          (succ-into-power L⊨ZF)
```
