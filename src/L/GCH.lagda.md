<!--en-->
# The generalized continuum hypothesis inside L

Inside `L`, the generalized continuum hypothesis says that the power set of every infinite internal cardinal has the size of its internal successor cardinal. This chapter states that comparison as coded injections in both directions; later chapters construct those injections.
<!--zh-->
# L 内部的广义连续统假设

在 `L` 内部，广义连续统假设断言每个无穷内部基数的幂集与其内部后继基数等势。本章用两个方向的编码单射陈述这一比较，后续章节将构造这些单射。
<!--ja-->
# L の内部における一般連続体仮説

`L` の内部における一般連続体仮説は、各無限な内部基数の冪集合が、その内部の後続基数と同じ濃度をもつことを述べます。本章ではこの比較を双方向の符号化された単射として定式化し、後の章でそれらを構成します。
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
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjL; SuccCardL )
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
