<!--en-->
# The constructible universe satisfies GCH

The preceding counting, condensation, and power-set arguments now meet. This chapter supplies the four internal hypotheses of the assembly theorem and records the final result that `L` satisfies GCH.
<!--zh-->
# 可构造宇宙满足 GCH

此前关于计数、凝聚与幂集的论证在此汇合。本章给出定理所需的四条内部假设，并陈述最终结果：`L` 满足 GCH。
<!--ja-->
# 構成可能宇宙は GCH を満たす

ここで、これまでの計数、凝縮、冪集合の議論が合流する。本章では組み立て定理の四つの内部仮定を与え、最終結果として `L` が GCH を満たすことを記録する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Theorem {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.GCH.Assembly {ℓ} lem using ( gch-from-internal-bill )
open import L.GCH.StageInjection {ℓ} lem using ( stage-counted )
open import L.GCH.SuccessorIntoPowerSet {ℓ} lem using ( succ-into-power )
open import L.GCH.BoundedSubset {ℓ} lem using ( internal-bounded-subset )
```

The trophy: the internal bill of `L.GCH.Assembly`, paid in full.
`StageCountedCoded` by `L.GCH.StageInjection`, `InternalBoundedSubset` by
`L.GCH.BoundedSubset` (the hull in L, its collapse, condensation through the
level formula, and the count), `SuccIntoPower` by `L.GCH.SuccessorIntoPowerSet`.

```agda
L⊨GCH : GCHStatement L⊨ZF
L⊨GCH = gch-from-internal-bill L⊨ZF stage-counted internal-bounded-subset
          (succ-into-power L⊨ZF)
```
