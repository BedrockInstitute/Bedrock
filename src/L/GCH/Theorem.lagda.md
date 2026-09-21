<!--en-->
# The constructible universe satisfies GCH

The preceding chapters established the three estimates needed to compare an infinite internal cardinal's power set with its successor. Together with the ZF model structure on `L`, they prove that the constructible universe satisfies the generalized continuum hypothesis. The only classical assumption is the same instance of excluded middle used throughout the construction of the model and its internal cardinal theory.
<!--zh-->
# 可构造宇宙满足 GCH

前几章已经建立了比较无穷内部基数的幂集与其后继基数所需的三项估计。它们与 `L` 上的 ZF 模型结构合在一起，证明可构造宇宙满足广义连续统假设。唯一的经典假设，仍是构造该模型及其内部基数理论时始终采用的同一个排中律实例。
<!--ja-->
# 構成可能宇宙は GCH を満たす

前章までに、無限な内部基数の冪集合をその後続基数と比較するための三つの評価を確立した。それらを `L` 上の ZF モデル構造と合わせると、構成可能宇宙が一般連続体仮説を満たすことが従う。古典的仮定は、モデルとその内部基数論の構成を通して用いてきた同じ排中律の実例だけである。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.GCH.Theorem {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Model {ℓ} lem using ( L⊨ZF )
```

<!--en-->
The target is `GCHStatement L⊨ZF`. It quantifies over `κ` in `L` whose underlying set is an ordinal, which is an internal cardinal, and which does not belong to `ω`. It asks merely for a successor cardinal `δ` and for internal coded injections in both directions between `𝒫 κ` and `δ`; the power set here is the one determined by `L⊨ZF`.
<!--zh-->
目标是 `GCHStatement L⊨ZF`。它量化 `L` 中这样的 `κ`：其底层集合是序数，`κ` 是内部基数，并且 `κ ∉ ω`。结论仅仅要求存在后继基数 `δ`，以及 `𝒫 κ` 与 `δ` 之间两个方向的内部编码单射；这里的幂集由 `L⊨ZF` 确定。
<!--ja-->
目標は `GCHStatement L⊨ZF` である。これは、基礎となる集合が順序数であり、内部基数であり、かつ `ω` に属さない `L` の要素 `κ` にわたって量化する。結論は、後続基数 `δ` と、`𝒫 κ` と `δ` の間の両方向の内部的に符号化された単射が単に存在することを求める。ここで冪集合を定めるのは `L⊨ZF` である。
<!--/-->

```agda
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.GCH.Assembly {ℓ} lem using ( gch-from-internal-bill )
open import L.GCH.StageInjection {ℓ} lem using ( stage-counted )
open import L.GCH.SuccessorIntoPowerSet {ℓ} lem using ( succ-into-power )
open import L.GCH.BoundedSubset {ℓ} lem using ( internal-bounded-subset )
```

<!--en-->
Fix such a `κ`. The general implication first obtains its internal successor cardinal `δ`. For every `y ∈ 𝒫 κ`, the bounded-subset theorem supplies an ordinal `β` such that `y ∈ Lset β` and `β` injects into `κ`. The fact that `δ` is an internal cardinal and that `κ ∈ δ`, together with ordinal trichotomy, forces `β ∈ δ`; hence `y ∈ Lset δ`. Thus the whole power set injects into `Lset δ`, and the stage-counting theorem injects that stage into `δ`, yielding `InjL (𝒫 κ) δ`. Finally, `succ-into-power`, using the infinitude of `κ` and the successor-cardinal facts for `δ`, turns this comparison into `InjL δ (𝒫 κ)`. These two injections establish the required instance of GCH, recorded as `L⊨GCH`.
<!--zh-->
固定这样的 `κ`。一般蕴涵先取得它的内部后继基数 `δ`。对每个 `y ∈ 𝒫 κ`，有界子集定理给出序数 `β`，使 `y ∈ Lset β` 且 `β` 单射入 `κ`。`δ` 是内部基数且 `κ ∈ δ`，这些事实与序数三分法合起来迫使 `β ∈ δ`，因而 `y ∈ Lset δ`。于是整个幂集先单射入 `Lset δ`，层计数定理再把这一层单射入 `δ`，得到 `InjL (𝒫 κ) δ`。最后，`succ-into-power` 利用 `κ` 的无穷性和 `δ` 的后继基数性质，把这一比较转化为 `InjL δ (𝒫 κ)`。两个方向的单射给出所需的 GCH 实例，并记作 `L⊨GCH`。
<!--ja-->
このような `κ` を固定する。一般の含意は、まずその内部の後続基数 `δ` を得る。各 `y ∈ 𝒫 κ` に対して、有界部分集合定理は、`y ∈ Lset β` かつ `β` が `κ` へ単射するような順序数 `β` を与える。`δ` が内部基数であることと `κ ∈ δ` を順序数の三分法と合わせると `β ∈ δ` が従い、したがって `y ∈ Lset δ` である。これにより冪集合全体が `Lset δ` へ単射し、段階計数定理がこの段階を `δ` へ単射するので、`InjL (𝒫 κ) δ` を得る。最後に `succ-into-power` は、`κ` の無限性と `δ` の後続基数としての性質を用いて、この比較を `InjL δ (𝒫 κ)` へ移す。両方向の単射が必要な GCH の実例を与え、これを `L⊨GCH` と記する。
<!--/-->

```agda
L⊨GCH : GCHStatement L⊨ZF
L⊨GCH = gch-from-internal-bill L⊨ZF stage-counted internal-bounded-subset
          (succ-into-power L⊨ZF)
```
