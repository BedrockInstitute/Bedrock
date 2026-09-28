```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The generalized continuum hypothesis inside L
<!--zh-->
# L 内部的广义连续统假设
<!--ja-->
# L の内部における一般連続体仮説
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ`{.Agda} and assume `lem : LEM (ℓ-suc ℓ)`{.Agda}. This hypothesis supplies a decision for each proposition at that level; it remains an explicit parameter of the constructions below.
<!--zh-->
固定宇宙层级 `ℓ`{.Agda}，并假设 `lem : LEM (ℓ-suc ℓ)`{.Agda}。这个假设为相应层级的每个命题提供判定，并始终作为下文构造的显式参数。
<!--ja-->
宇宙レベル `ℓ`{.Agda} を固定し、`lem : LEM (ℓ-suc ℓ)`{.Agda} を仮定する。この仮定は該当するレベルの各命題に判定を与え、以下の構成の明示的なパラメータとして保たれる。
<!--/-->

```agda
module L.GCH {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjL; SuccCardL )
```

<!--en-->

Inside `L`, the generalized continuum hypothesis compares two sets attached to every infinite internal cardinal `κ`: its power set and its internal successor cardinal. In this development, having the same size is expressed by internal coded injections in both directions. The statement below formulates this comparison using the power set supplied by the model itself.
<!--zh-->

在 `L` 内部，广义连续统假设比较与每个无穷内部基数 `κ` 相联系的两个集合：它的幂集与内部后继基数。本书用两个方向的内部编码单射表示二者大小相同。下面的陈述采用模型自身给出的幂集来表述这一比较。
<!--ja-->

`L` の内部における一般連続体仮説は、各無限な内部基数 `κ` に付随する二つの集合、すなわちその冪集合と内部の後続基数を比較する。本書では、大きさが等しいことを両方向の内部的に符号化された単射で表す。以下では、モデル自身が与える冪集合を用いてこの比較を定式化する。
<!--/-->

<!--en-->
The notions of internal cardinal, successor cardinal, and coded injection are all formed relative to the chosen instance of excluded middle. Thus the statement belongs to the same classical context as the cardinal theory developed earlier, with no additional classical assumption.
<!--zh-->
内部基数、后继基数和编码单射都相对于这里选定的排中律实例而定义。因此，这一陈述沿用此前基数理论的经典背景，不再加入其他经典假设。
<!--ja-->
内部基数、後続基数、符号化された単射はいずれも、ここで選んだ排中律の実例に相対して定義される。したがって、この主張は先に展開した基数論と同じ古典的な前提のもとにあり、それ以外の古典的仮定を加えない。
<!--/-->

<!--en-->
The quantifier ranges over the carrier of the constructible structure. Such an element consists of an ambient set together with a proof of constructibility. Membership in `ω` is read through the ambient membership relation; its negation supplies the condition that the cardinal is infinite.
<!--zh-->
量词遍历可构造结构的论域。论域中的元素由一个外围集合及其可构造性证明组成。是否属于 `ω` 通过外围成员关系来解释；其否定给出基数为无穷的条件。
<!--ja-->
量化は構成可能構造の領域にわたる。その要素は、周囲の集合と構成可能性の証明からなる。`ω` への所属は周囲の所属関係によって解釈され、その否定が基数の無限性を表す。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
```

<!--en-->
A ZF model supplies its own power-set operation. For a model proof `zf`, the notation `𝒫 κ` denotes the set that the power-set axiom of that model assigns to `κ`. Consequently, every set and every membership assertion in the comparison remains internal to the constructible structure.
<!--zh-->
ZF 模型带有自身的幂集运算。给定模型证明 `zf`，记号 `𝒫 κ` 表示该模型的幂集公理为 `κ` 给出的集合。因此，这一比较中的集合与成员陈述都留在可构造结构内部。
<!--ja-->
ZF モデルはそれ自身の冪集合演算を備える。モデルの証明 `zf` に対して、`𝒫 κ` はそのモデルの冪集合公理が `κ` に与える集合を表す。したがって、この比較に現れる集合と所属の主張は、すべて構成可能構造の内部にとどまる。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
```

<!--en-->
The hypotheses on `κ` can be read in order. Its underlying set is an ordinal. It is an internal cardinal, meaning that for every `δ ∈ κ` there is no internal coded injection from `κ` into `δ`. Finally, `κ ∉ ω`. Together these conditions say that `κ` is an infinite internal cardinal.
<!--zh-->
关于 `κ` 的假设可以依次读出。它的底层集合是序数。它是内部基数，也就是说，对每个 `δ ∈ κ`，都不存在从 `κ` 到 `δ` 的内部编码单射。最后，`κ ∉ ω`。这些条件合在一起说明 `κ` 是无穷内部基数。
<!--ja-->
`κ` に対する仮定は順に読める。その基礎となる集合は順序数である。また `κ` は内部基数であり、各 `δ ∈ κ` に対して `κ` から `δ` への内部的に符号化された単射は存在しない。最後に `κ ∉ ω` である。これらを合わせると、`κ` が無限な内部基数であることを表す。
<!--/-->

```agda
GCHStatement zf =
  (κ : S)
  → IsOrd (fst κ)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
```

<!--en-->
The conclusion says, merely, that an internal successor cardinal `δ` of `κ` exists together with internal coded injections from `𝒫 κ` to `δ` and from `δ` to `𝒫 κ`. This pair of comparisons is the form in which this development states that the two sets have the same size. The outer truncation does not choose a particular `δ`, while each occurrence of `InjL` in turn retains only the existence of a suitable constructible injection code.
<!--zh-->
结论仅仅断言：存在 `κ` 的内部后继基数 `δ`，并且存在从 `𝒫 κ` 到 `δ` 以及从 `δ` 到 `𝒫 κ` 的内部编码单射。本书用这两个方向的比较表达两集合大小相同。最外层截断不选定某个特定的 `δ`；其中每个 `InjL` 又只保留合适的可构造单射码的存在性。
<!--ja-->
結論は、`κ` の内部の後続基数 `δ` が単に存在し、さらに `𝒫 κ` から `δ` へ、また `δ` から `𝒫 κ` への内部的に符号化された単射が存在することを述べる。本書では、この両方向の比較によって二つの集合の大きさが等しいことを表す。外側の切り詰めは特定の `δ` を選ばず、各 `InjL` も適切な構成可能な単射の符号の存在だけを保つ。
<!--/-->

```agda
  → ∥ Σ[ δ ∶ S ]
       ( SuccCardL δ κ
       × InjL (𝒫 κ) δ
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )
```
