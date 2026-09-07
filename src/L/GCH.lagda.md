<!--en-->
# Stating the generalized continuum hypothesis inside a model

The generalized continuum hypothesis compares each infinite cardinal with its power set. This chapter packages that statement for an arbitrary model of set theory, so later chapters can concentrate on proving it for `L`.
<!--zh-->
# 在模型内部陈述广义连续统假设

广义连续统假设比较每个无穷基数及其幂集。本章先为任意集合论模型封装这一陈述，使后续章节可以专注于证明 `L` 满足它。
<!--ja-->
# モデルの内部で一般連続体仮説を述べる

一般連続体仮説は、各無限基数とその冪集合を比較する。本章ではこの主張を任意の集合論モデルについて整え、後の章で `L` に対する証明へ集中できるようにする。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )
```

The L-internal injection: the model's own truth value of the internal statement
that some `F` in L is an injection of `a` into `b`. The model's `∃` is the
truncated `Σ` over the carrier, and `InjCode`'s conjuncts are satisfaction facts
(src/L/Cardinal.lagda.md:223-228). This is the refutand of `IsCardinalL`, reused
positively.

```agda
InjL : S → S → Type (ℓ-suc ℓ)
InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
```

`δ` is THE successor cardinal of `κ` in the sense of L: an ordinal L-cardinal
above `κ`, below or equal to every ordinal L-cardinal above `κ`. Leastness is
the ordinal order: for ordinals, `δ ⊆ c` is `δ ≤ c`, and `_⊆ˢ_` is the model's
own subset relation (src/FOL/ZFModel.lagda.md:141-142). Every component is an
hProp, so the witness `δ` is unique and the truncation below is the classical
`∃`.

```agda
SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsOrd (fst δ)
  × IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩
             → ⟨ δ ⊆ˢ c ⟩)
```

The statement. L satisfies the generalized continuum hypothesis: for every
infinite cardinal `κ` of L, `2^κ = κ⁺` in the sense of L. The equality is the
pair of internal injections at the successor cardinal; the power set is the
model's own. No hypothesis remains beyond `κ` itself, and no ambient function
type crosses the `⊨` boundary.

```agda
GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHStatement zf =
  (κ : S)
  → IsOrd (fst κ)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ]
       ( SuccCardL δ κ
       × InjL (𝒫 κ) δ
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )
```
