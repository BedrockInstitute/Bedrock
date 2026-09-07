<!--en-->
# Numerals in a successor-closed ordinal stage

Finite ordinals supply the numerals used in formula codes. This chapter shows that every numeral belongs to a stage indexed by an ordinal that contains zero and is closed under successors. The argument first treats any monotone stage family containing each ordinal at its successor stage, then applies it to the constructible hierarchy.
<!--zh-->
# 对后继封闭的序数阶段中的数码

有限序数提供公式码所用的数码。本章证明，当阶段的序数指标包含零且对后继封闭时，每个数码都属于该阶段。我们先处理任意单调且在后继阶段包含原序数的阶段族，再将结论应用于可构造层级。
<!--ja-->
# 後者演算について閉じた順序数段階の数項

有限順序数は論理式コードに用いる数項を与えます。本章では、段階の順序数添字が零を含み、後者演算について閉じていれば、すべての数項がその段階に属することを示します。まず各順序数をその後者の段階に含む単調な段階族を扱い、その結果を構成可能階層に適用します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.NumeralBound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

<!--en-->
## A bound for monotone stage families

Let λ contain zero and be closed under successors. Induction puts each finite ordinal in λ. To put it in the stage T λ, first place it in T at its successor and then use monotonicity.
<!--zh-->
## 单调阶段族的界

设 λ 包含零且对后继封闭。归纳法将每个有限序数放入 λ。为了进一步将它放入阶段 T λ，先把它放入后继所对应的阶段，再使用单调性。
<!--ja-->
## 単調な段階族に対する上界

λ が零を含み後者演算について閉じているとします。帰納法により各有限順序数は λ に属します。さらにその後者に対応する段階への所属と単調性を用いると、T λ への所属が得られます。
<!--/-->

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

<!--en-->
## Numerals in the constructible hierarchy

Constructible stages are monotone, and each ordinal belongs to the stage indexed by its successor. The general bound therefore applies to L. We also express this membership using the numerals already regarded as elements of the model.
<!--zh-->
## 可构造层级中的数码

可构造阶段具有单调性，每个序数也属于以后继为指标的阶段，因此一般的界适用于 L。我们还用模型内部的数码来表述这一隶属关系。
<!--ja-->
## 構成可能階層における数項

構成可能な段階は単調であり、各順序数はその後者を添字とする段階に属します。したがって一般の上界の議論を L に適用できます。この所属関係を、モデルの要素として与えた数項についても述べます。
<!--/-->

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
