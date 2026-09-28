```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Assembling GCH from four internal bounds
<!--zh-->
# 从四条内部界装配 GCH
<!--ja-->
# 四つの内部上界から GCH を組み立てる
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
We fix this hypothesis at the single universe level required by the proof. Thus every construction below, including the least-candidate argument, depends on the same explicit instance `LEM (ℓ-suc ℓ)`.
<!--zh-->
我们把这一假设固定在证明所需的唯一宇宙层级上。因此下文所有构造，包括最小候选者论证，都只依赖同一个显式实例 `LEM (ℓ-suc ℓ)`。
<!--ja-->
この仮定を、証明に必要なただ一つの宇宙レベルで固定する。したがって、最小候補の議論を含む以下の構成は、すべて同じ明示的な実例 `LEM (ℓ-suc ℓ)` だけに依存する。
<!--/-->

```agda
module L.GCH.Assembly {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_ )
import FOL.Semantics
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOfFormula; module SWO )
open import L.Axioms.Basic {ℓ} using ( isL-Lset )
open import L.Cardinal {ℓ} lem
  using ( InjL; SuccCardL; IsCardinalL; module LeastCardInjL )
open import L.CardinalAbove {ℓ} lem using ( CardAboveL )
open import L.DefinableInjection {ℓ} lem using ( cardinalAt; module CardinalAt )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
```

<!--en-->
This chapter completes the stated form of GCH inside `L`. For each infinite internal ordinal cardinal `κ`, it proves, under an outer propositional truncation, that there is a successor cardinal `δ` together with the two coded injections `𝒫κ ↪ δ` and `δ ↪ 𝒫κ`. The proof may work with witnesses inside a truncated branch, but it exports neither a chosen `δ` nor either injection graph.
<!--zh-->
本章完成 `L` 内部所采用的 GCH 陈述。对每个无穷内部序数基数 `κ`，它在最外层的命题截断下证明：存在一个后继基数 `δ`，并有两条编码单射 `𝒫κ ↪ δ` 与 `δ ↪ 𝒫κ`。证明可以在截断的局部分支内使用见证，但最终既不选定一个 `δ`，也不交出任何一张单射图。
<!--ja-->
本章では、`L` の内部で採用する形の GCH を完成させる。無限な内部順序数基数 `κ` ごとに、外側の命題的切り詰めのもとで、後続基数 `δ` と二つの符号化された単射 `𝒫κ ↪ δ` および `δ ↪ 𝒫κ` が存在することを示す。証明では切り詰められた枝の内部で証人を使えるが、特定の `δ` も、どちらの単射のグラフも外へ取り出さない。
<!--/-->

<!--en-->
The only classical principle used in the assembly is excluded middle. It will turn a merely inhabited family of candidates into its unique least member, once the candidates have been placed in a small well-order.
<!--zh-->
装配过程使用的唯一经典原则是排中律。一旦把候选者放进一个小良序中，排中律便可把仅仅非空的候选族化为其唯一最小元。
<!--ja-->
組み立てで用いる古典的原理は排中律だけである。候補を小さな整列順序の中に置いた後、単に要素をもつ候補族から一意な最小元を得るために使う。
<!--/-->



<!--en-->
Two set-theoretic viewpoints meet here. The ambient cumulative hierarchy supplies membership and small presentations, while the constructible subuniverse supplies the predicate `isL` and the stages `Lset α`; the ZF model structure later interprets the internal power set.
<!--zh-->
这里汇合了两个集合论视角。外围累积层级提供隶属与小呈现，可构造子宇宙提供谓词 `isL` 和各层 `Lset α`；随后由 ZF 模型结构解释内部幂集。
<!--ja-->
ここでは、集合論に関する二つの見方を結び付ける。周囲の累積階層は所属と小さな提示を与え、構成可能な部分宇宙は述語 `isL` と各段階 `Lset α` を与える。内部の冪集合は、後で ZF モデルの構造によって解釈される。
<!--/-->

<!--en-->
The minimization argument uses three facts about ordinals: membership in an ordinal is transitive, any two ordinals satisfy trichotomy, and the membership order on the small presentation of an ordinal is a well-order. These facts let a least candidate found in a bounded search control every competing cardinal.
<!--zh-->
极小化论证使用序数的三项事实：序数中的隶属具有传递性，任意两个序数满足三分律，并且序数的小呈现上的隶属次序是良序。这些事实使有界搜索所得的最小候选者能够控制任意竞争基数。
<!--ja-->
最小化の議論では、順序数について三つの事実を使う。順序数の所属は推移的であり、任意の二つの順序数には三岐性が成り立ち、順序数の小さな提示上の所属順序は整列順序である。これにより、有界な探索で得た最小候補が、任意の競合する基数を制御できる。
<!--/-->

<!--en-->
Internal size comparisons are expressed by `InjL`, the propositional truncation of a constructible graph coding an injection. From these comparisons, `IsCardinalL` defines internal cardinals and `SuccCardL` specifies the least internal ordinal cardinal strictly above a given one; `CardAboveL` supplies only some larger cardinal, still under truncation.
<!--zh-->
内部大小比较由 `InjL` 表达，即「存在一个编码单射的可构造图」的命题截断。`IsCardinalL` 据此定义内部基数，`SuccCardL` 刻画严格大于给定基数的最小内部序数基数；`CardAboveL` 只在命题截断下提供某个更大的基数。
<!--ja-->
内部の大きさの比較は `InjL` で表す。これは、単射を符号化する構成可能なグラフが存在するという命題的切り詰めである。`IsCardinalL` はこの比較から内部の基数を定義し、`SuccCardL` は与えられた基数より真に大きい最小の内部順序数基数を指定する。一方、`CardAboveL` が与えるのは、切り詰めの内側にある何らかのより大きい基数だけである。
<!--/-->

<!--en-->
The final GCH statement asks for a successor cardinal together with coded injections in both directions between it and the model's power set. To construct the forward comparison, inclusions will first be coded as injections and then composed with the injection that counts a constructible stage.
<!--zh-->
最终的 GCH 陈述要求：仅仅存在一个后继基数，并有它与模型幂集之间两个方向的编码单射。为构造从幂集出发的比较，证明先把包含关系编码成单射，再与计数可构造层的单射复合。
<!--ja-->
最終的な GCH の主張は、後続基数が単に存在し、それとモデルの冪集合との間に両方向の符号化された単射があることを要求する。冪集合から出る向きの比較を構成するため、まず包含を単射として符号化し、次に構成可能な段階を数える単射と合成する。
<!--/-->

<!--en-->
The bounded search is made small by using the presentation of the ordinal `sucV (fst θ)`. Its indices represent the members of `sucV (fst θ)`, hence ordinals no larger than `θ`; `ω` is used separately to express that the cardinal under study is not finite. When two constructible pairs have equal underlying sets, propositionhood of constructibility lifts that equality to the pairs themselves.
<!--zh-->
有界搜索通过序数 `sucV (fst θ)` 的小呈现变成一个小类型。其索引表示 `sucV (fst θ)` 的成员，也就是不大于 `θ` 的序数；`ω` 则另用于表达所研究的基数不是有限序数。若两个可构造对的底层集合相等，可构造性的命题性会把这一相等提升为这两个配对的相等。
<!--ja-->
有界探索には、順序数 `sucV (fst θ)` の小さな提示を使う。その添字は `sucV (fst θ)` の要素、すなわち `θ` 以下の順序数を表す。一方、`ω` は考察する基数が有限順序数でないことを表すために使う。二つの構成可能な対の底の集合が等しいとき、構成可能性が命題であることにより、その等しさを対そのものの等しさへ持ち上げられる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
```

<!--en-->
Trichotomy will be analyzed through three coproduct branches. Impossible branches end in the empty type, while propositional truncation records existence without exposing a chosen witness; its eliminations below therefore always target propositions such as membership or another truncated existence statement.
<!--zh-->
三分律将通过余积的三个分支来分析。不可能的分支落入空类型，而命题截断只记录存在而不暴露选定见证；因此下文对它的消去总是以隶属或另一个截断存在陈述等命题为目标。
<!--ja-->
三岐性は、直和の三つの分岐に分けて調べる。不可能な分岐は空型に帰着し、命題的切り詰めは選ばれた証人を外へ出さずに存在だけを記録する。したがって、以下での消去先は、所属や別の切り詰められた存在命題のような命題に限られる。
<!--/-->

<!--en-->
Membership written `_∈ˢ_` is ambient membership in the cumulative hierarchy. This is the relation needed for pointwise containments, including the claim that every ambient member of a constructible subset of `κ` also belongs to `κ`.
<!--zh-->
记作 `_∈ˢ_` 的隶属是累积层级中的外围隶属。逐点包含使用这一关系，特别是「`κ` 的一个可构造子集的每个外围成员也属于 `κ`」这一陈述。
<!--ja-->
`_∈ˢ_` と書く所属は、累積階層における周囲の所属である。点ごとの包含、特に「`κ` の構成可能な部分集合の各周囲要素が `κ` にも属する」という主張には、この関係を使う。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
We write `SV` for the ambient proposition-valued set-theoretic structure. Its carrier includes every set over which the pointwise subset hypotheses range.
<!--zh-->
记外围的命题值集合论结构为 `SV`。它的载体包含逐点子集前提所量化的全部集合。
<!--ja-->
周囲の命題値の集合論的構造を `SV` と書く。その台は、点ごとの部分集合の仮定が量化するすべての集合を含む。
<!--/-->

```agda
module SV = hPropStructure 𝒮ᵥ
```

<!--en-->
We write `SL` for the corresponding structure restricted to constructible sets. Its elements pair an underlying ambient set with a proof that the set lies in `L`.
<!--zh-->
记限制在可构造集合上的相应结构为 `SL`。它的元素把一个外围底层集合与该集合属于 `L` 的证明配成一对。
<!--ja-->
構成可能な集合に制限した対応する構造を `SL` と書く。その要素は、周囲の底の集合と、その集合が `L` に属することの証明との対である。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ
```

<!--en-->
The ZF model structure on `SL` supplies the specified internal power set `𝒫κ`. Hence every later reference to a power set concerns the power set of the constructible model, rather than the ambient power set in the whole cumulative hierarchy.
<!--zh-->
`SL` 上的 ZF 模型结构提供指定的内部幂集 `𝒫κ`。因此后文提到的幂集都指可构造模型的幂集，而不是整个累积层级中的外围幂集。
<!--ja-->
`SL` 上の ZF モデルの構造は、指定された内部の冪集合 `𝒫κ` を与える。したがって、以下でいう冪集合はすべて構成可能モデルの冪集合であり、累積階層全体における周囲の冪集合ではない。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
```

<!--en-->
## Four internal estimates
<!--zh-->
## 四条内部估计
<!--ja-->
## 四つの内部評価
<!--/-->

<!--en-->
The first interface says what it means for a stage to be counted: for every pair of a constructible ordinal `δ` and a set `Lδ` whose underlying set is the stage `Lset δ`, if `δ` is not finite, then the stage injects into the ordinal. The type excludes finite ordinals and produces only the truncated existence of a coded injection.
<!--zh-->
第一个接口陈述「层被计数」的含义：对每对「可构造序数 `δ` 与底层集合恰为层 `Lset δ` 的集合 `Lδ`」，若 `δ` 非有限，则该层单射入该序数。该类型排除有限序数，且只产出编码单射的截断存在。
<!--ja-->
最初のインターフェースは、段階が数え上げられるとは何を意味するかを述べる。構成可能な順序数 `δ` と、底の集合が段階 `Lset δ` と等しい集合 `Lδ` の対に対して、`δ` が有限でなければ、段階から順序数への単射が存在する、というものである。この型は有限の順序数を排除し、符号化された単射の切り詰められた存在だけを産み出す。
<!--/-->

```agda
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (⟨ fst δ ∈ˢ ω ⟩ → ⊥₀)
  → fst Lδ ≡ Lset (fst δ) → InjL Lδ δ
```

<!--en-->
The second interface states the bounded-subset theorem. For an ordinal internal cardinal `κ` that is not finite, and any constructible set `y` whose ambient members all belong to `κ`, there is, merely, an ordinal `β` such that `y` lies in the stage `Lset β` and `β` injects into `κ`. The subset hypothesis quantifies over ambient sets, which covers members that carry no constructibility proof of their own.
<!--zh-->
第二个接口陈述有界子集定理。对非有限、序数、内部基数的 `κ`，以及任一「其外围成员都属于 `κ`」的可构造集合 `y`，都仅仅地存在序数 `β`，使 `y` 落在层 `Lset β` 中且 `β` 单射入 `κ`。子集前提量化外围集合，从而覆盖那些自身不带可构造性证明的成员。
<!--ja-->
第二のインターフェースは、有界部分集合の定理を述べる。有限ではなく順序数であり内部の基数である `κ` と、その周囲の要素がすべて `κ` に属する構成可能な集合 `y` に対して、単に、順序数 `β` が存在し、`y` が段階 `Lset β` の中にあり、`β` が `κ` へ単射する。部分集合の仮定は周囲の集合の上で量化するので、自分自身の構成可能性の証明をもたない要素も覆う。
<!--/-->

```agda
InternalBoundedSubset : Type (ℓ-suc ℓ)
InternalBoundedSubset =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  → (y : SL.S) → ((z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩)
  → ∥ Σ[ β ∶ SL.S ]
```

<!--en-->
The produced record contains the ordinality of `β`, the landing of `y` in the stage, and the coded injection of `β` into `κ`.
<!--zh-->
产出的记录包含 `β` 的序数性、`y` 在层中的落位，以及 `β` 到 `κ` 的编码单射。
<!--ja-->
産み出される記録には、`β` の順序数性、`y` の段階への着地、そして `β` から `κ` への符号化された単射が含まれる。
<!--/-->

```agda
       (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ) ∥₁
```

<!--en-->
The third interface is a conditional reverse comparison: given that the internal power set of `κ` injects into a successor cardinal `δ` of `κ`, it returns the reverse injection of `δ` into the power set. The hypothesis is genuinely conditional; the interface cannot be invoked from the successor-cardinal record alone.
<!--zh-->
第三个接口是条件性的反向比较：给定 `κ` 的内部幂集单射入 `κ` 的后继基数 `δ`，它返回 `δ` 到幂集的反向单射。该假设是真正条件性的；仅凭后继基数记录无法调用此接口。
<!--ja-->
第三のインターフェースは条件つきの逆向きの比較である。`κ` の内部の冪集合が `κ` の後続基数 `δ` へ単射することが与えられたとき、`δ` から冪集合への単射を返す。仮定は本当に条件つきであり、後続基数の記録だけから呼び出すことはできない。
<!--/-->

```agda
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀) → SuccCardL δ κ
  → InjL (𝒫 κ) δ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )
```

<!--en-->
The fourth interface states the mere existence of a successor cardinal: for every infinite internal ordinal cardinal, some successor cardinal exists. The conclusion is truncated, so a caller cannot select a global representative from it.
<!--zh-->
第四个接口陈述后继基数的仅仅存在：对每个无穷内部序数基数，存在某个后继基数。结论是截断的，调用者不能从中选定全局代表。
<!--ja-->
第四のインターフェースは、後続基数の単なる存在を述べる。無限の内部順序数基数ごとに、ある後続基数が存在する。結論は切り詰められており、呼び出し側がそこから大域的な代表を選ぶことはできない。
<!--/-->

```agda
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  → ∥ Σ[ δ ∶ SL.S ] SuccCardL δ κ ∥₁
```

<!--en-->
## Larger internal cardinals exist
<!--zh-->
## 更大的内部基数存在
<!--ja-->
## より大きな内部基数の存在
<!--/-->

<!--en-->
The reduction module fixes an ordinal internal cardinal `θ` strictly above `κ` and proves that, within the small search space determined by the successor of `θ`, a least cardinal above `κ` exists. This is the heart of the chapter: first fix an explicit upper bound, then minimize inside it.
<!--zh-->
约简模块固定严格大于 `κ` 的序数内部基数 `θ`，并证明：在 `θ` 的后继所决定的小搜索空间内，存在 `κ` 之上的最小基数。这是本章的核心：先固定显式上界，再在其内最小化。
<!--ja-->
約簡のモジュールは、`κ` より真に大きい順序数の内部基数 `θ` を固定し、`θ` の後続が決める小さな探索空間の中で、`κ` より上の最小の基数が存在することを示す。これがこの章の中心である。まず明示的な上界を固定し、その中で最小化するのである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Reduce (κ : SL.S) (oκ : IsOrd (fst κ))
              (θ : SL.S) (oθ : IsOrd (fst θ))
              (cθ : IsCardinalL θ) (κ∈θ : ⟨ fst κ ∈ˢ fst θ ⟩) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The earlier cardinal machinery supplies a map `up` from indices in the small presentation of the ordinal `sucV (fst θ)` to constructible sets. It also supplies an index `self` that presents `θ` itself and an equation `self-eq` identifying the underlying set of `up self` with `θ`. Thus the known cardinal `θ` occurs among the candidates of the bounded search.
<!--zh-->
此前的基数机制提供映射 `up`，把序数 `sucV (fst θ)` 的小呈现中的索引送到可构造集合。它还提供呈现 `θ` 自身的索引 `self`，以及把 `up self` 的底层集合与 `θ` 认同起来的等式 `self-eq`。因此，已知的基数 `θ` 确实出现在有界搜索的候选者中。
<!--ja-->
先の基数の仕組みは、順序数 `sucV (fst θ)` の小さな提示の添字から構成可能な集合への写像 `up` を与える。さらに、`θ` 自身を提示する添字 `self` と、`up self` の底の集合を `θ` と同一視する等式 `self-eq` も与える。したがって、既知の基数 `θ` は有界探索の候補に実際に含まれる。
<!--/-->

```agda
  open LeastCardInjL θ oθ using ( up; self; self-eq )
```

<!--en-->
The search space is the small presentation of the ordinal successor `sucV (fst θ)`. It is a presentation of an ordinal, not a constructible stage `Lset (fst θ)`.
<!--zh-->
搜索空间是序数后继 `sucV (fst θ)` 的小呈现。这里呈现的是一个序数，而不是可构造层 `Lset (fst θ)`。
<!--ja-->
探索空間は、順序数としての後続 `sucV (fst θ)` の小さな提示である。ここで提示しているのは順序数であって、構成可能な段階 `Lset (fst θ)` ではない。
<!--/-->

```agda
  A : Type ℓ
  A = ⟪ sucV (fst θ) ⟫
```

<!--en-->
Membership on the ordinal `sucV (fst θ)` induces a strict well-order on this presentation. That well-order makes it possible to search the small candidate family for a least member.
<!--zh-->
序数 `sucV (fst θ)` 上的隶属关系在这一呈现上诱导出严格良序。借助该良序，证明可以在这个小候选族中寻找最小元。
<!--ja-->
順序数 `sucV (fst θ)` 上の所属関係は、この提示に厳密な整列順序を誘導する。この整列順序により、小さな候補族の中で最小要素を探索できる。
<!--/-->

```agda
  opaque
    w : SWO A
    w = ordSWO (sucV (fst θ)) (suc-ord oθ)
```

<!--en-->
For presentation indices `m` and `n`, the induced relation `m < n` holds exactly when the ordinal represented by `m` belongs to the ordinal represented by `n`. Consequently, being earlier in the search order has the intended mathematical meaning of being a smaller ordinal.
<!--zh-->
对呈现索引 `m` 与 `n`，诱导关系 `m < n` 恰在 `m` 所表示的序数属于 `n` 所表示的序数时成立。因此，在搜索序中更靠前正对应于序数意义下更小。
<!--ja-->
提示の添字 `m` と `n` について、誘導された関係 `m < n` が成り立つのは、`m` が表す順序数が `n` の表す順序数に属するとき、かつそのときに限る。したがって、探索順序で先にあることは、順序数としてより小さいことを正確に表す。
<!--/-->

```agda
  opaque
    unfolding w
    w-lt : (m n : A) → SWO._<∙_ w m n
         ≡ ⟨ ⟪ sucV (fst θ) ⟫↪ m ∈ˢ ⟪ sucV (fst θ) ⟫↪ n ⟩
    w-lt m n = refl
```

<!--en-->
Internal cardinality is a proposition. Indeed, `IsCardinalL x` says, for every constructible member `δ` of `x`, that any coded injection from `x` into `δ` leads to the empty type; dependent function types with proposition-valued conclusions remain propositions. This allows cardinality to form one component of the proposition-valued candidate predicate below.
<!--zh-->
内部基数性是命题。具体说，`IsCardinalL x` 对 `x` 的每个可构造成员 `δ` 断言：任何从 `x` 到 `δ` 的编码单射都会导出空类型；而结论为命题的依值函数类型仍是命题。因此，基数性可作为下文命题值候选谓词的一个分量。
<!--ja-->
内部の基数性は命題である。実際、`IsCardinalL x` は、`x` の構成可能な各要素 `δ` について、`x` から `δ` への符号化された単射があれば空型が導かれると述べる。命題値の結論をもつ依存関数型は、やはり命題である。したがって、基数性を以下の命題値の候補述語の一成分にできる。
<!--/-->

```agda
  isPropIsCardinalL : (x : SL.S) → isProp (IsCardinalL x)
  isPropIsCardinalL x =
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isProp⊥)))
```

<!--en-->
The candidate predicate asks two things of an index: the constructible set it presents is an internal cardinal, and `κ` belongs to it. Ordinality need not be stored in the predicate, because every presented set is a member of the ordinal `sucV (fst θ)` and is therefore itself an ordinal. The package `definedGood` presents the conjunction by `cardinalAt zero ∧̇ (var one ∈̇ var zero)`. Its environment places the candidate before `κ`, and the two directions of `CardinalAt` give the checked reading of the non-atomic conjunct.
<!--zh-->
候选谓词向索引要求两件事：其呈现的可构造集合是内部基数，并且 `κ` 属于它。谓词无需另存序数性，因为每个被呈现的集合都是序数 `sucV (fst θ)` 的成员，因而自身就是序数。包 `definedGood` 用 `cardinalAt zero ∧̇ (var one ∈̇ var zero)` 呈现这个合取；其环境把候选者放在 `κ` 之前，而 `CardinalAt` 的两个方向为非原子合取支给出经过检查的读取。
<!--ja-->
候補述語は、添字に二つの条件を課す。その添字が提示する構成可能な集合が内部基数であることと、`κ` がその集合に属することである。順序数性を述語に別途保存する必要はない。提示される各集合は順序数 `sucV (fst θ)` の要素なので、それ自身も順序数だからである。パッケージ `definedGood` はこの連言を `cardinalAt zero ∧̇ (var one ∈̇ var zero)` で表す。その環境では候補が `κ` より前に置かれ、`CardinalAt` の二方向が非原子的な連言肢の検査済みの読みを与える。
<!--/-->

```agda
  Good : A → hProp (ℓ-suc ℓ)
  Good b = (IsCardinalL (up b) × ⟨ fst κ ∈ˢ fst (up b) ⟩)
         , isProp× (isPropIsCardinalL (up b)) (snd (fst κ ∈ˢ fst (up b)))

  definedGood : FOL.Semantics.FormulaPredicate 𝒮ʟ A SL.S id Good
  definedGood = FOL.Semantics.presented 2
    (cardinalAt zero ∧̇ (var (suc zero) ∈̇ var zero)) (λ b → up b ∷ κ ∷ [])
    (λ b → ⇔toPath
      (λ { (card , mem) → CardinalAt.fill zero (up b ∷ κ ∷ []) card , mem })
      (λ { (sat , mem) → CardinalAt.read zero (up b ∷ κ ∷ []) sat , mem }))
```

<!--en-->
The index presenting `θ` itself presents a constructible set whose underlying set is `θ`, by the propositionhood of constructibility.
<!--zh-->
呈现 `θ` 自身的索引所呈现的可构造集合，其底层集合就是 `θ`，依据是可构造性的命题性。
<!--ja-->
`θ` 自身を提示する索引が提示する構成可能な集合の底の集合は、構成可能性の命題性によって、`θ` になる。
<!--/-->

```agda
  upSelf : up self ≡ θ
  upSelf = Σ≡Prop (λ x → snd (isL x)) self-eq
```

<!--en-->
The candidate class is nonempty: the index presenting `θ` is a candidate, carrying the cardinality and the membership transported along that identification.
<!--zh-->
候选类非空：呈现 `θ` 的索引就是候选，它携带沿该同一视搬运的基数性与隶属。
<!--ja-->
候補の類は空ではない。`θ` を提示する索引が候補であり、その同一視に沿って運ばれた基数性と所属を運ぶ。
<!--/-->

```agda
  nonempty : ∥ Σ[ b ∶ A ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ self
            , subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upSelf) (cθ , κ∈θ) ∣₁
```

<!--en-->
The formula-facing search on the well order now produces an actual least candidate with its leastness proof. The least-witness type is a proposition, so the truncation of nonemptiness can be eliminated here; the classical descent decides satisfaction of `definedGood`, not an unrestricted host callback.
<!--zh-->
搜索空间上的面向公式搜索随即产出实际的最小候选及其最小性证明。最小见证的类型是命题，因此非空性的截断可在此消去；经典下降判定的是 `definedGood` 的满足关系，而不是不受限制的宿主回调。
<!--ja-->
探索空間の整列順序に対する論理式に面する探索は、実際の最小候補とその最小性の証明を産み出す。最小証人の型は命題なので、非空性の切り詰めをここで消去できる。古典的な降下が判定するのは `definedGood` の充足であり、制限のないホスト側のコールバックではない。
<!--/-->

```agda
  least : Σ[ b ∶ A ] IsLeast w Good b
  least = leastOfFormula w definedGood lem nonempty
```

<!--en-->
Name the constructible set presented by the least candidate `δ`. The following argument verifies that its local leastness in the bounded search gives all four clauses of `SuccCardL δ κ`, including leastness against every competing internal ordinal cardinal above `κ`.
<!--zh-->
把最小候选所呈现的可构造集合命名为 `δ`。下面将验证：它在有界搜索中的局部最小性足以给出 `SuccCardL δ κ` 的四个条款，包括相对于每个严格大于 `κ` 的竞争内部序数基数的全局最小性。
<!--ja-->
最小候補が提示する構成可能な集合を `δ` と名付ける。以下では、有界探索における局所的な最小性から `SuccCardL δ κ` の四つの条件がすべて従うことを確かめる。その中には、`κ` より大きい任意の競合する内部順序数基数に対する大域的な最小性も含まれる。
<!--/-->

```agda
  δ : SL.S
  δ = up (fst least)
```

<!--en-->
By the presentation's membership record, the underlying set of `δ` belongs to the ordinal `sucV (fst θ)`. Thus the construction proves only `fst δ ∈ sucV (fst θ)`, which places `δ` at or below `θ`; it does not assert `fst δ ∈ fst θ`.
<!--zh-->
由呈现所附的隶属记录，`δ` 的底层集合属于序数 `sucV (fst θ)`。因此这里证明的只是 `fst δ ∈ sucV (fst θ)`，即 `δ` 不大于 `θ`；并没有断言 `fst δ ∈ fst θ`。
<!--ja-->
提示に付随する所属の記録により、`δ` の底の集合は順序数 `sucV (fst θ)` に属する。したがって、ここで示されるのは `fst δ ∈ sucV (fst θ)`、すなわち `δ` が `θ` 以下であることだけであり、`fst δ ∈ fst θ` を主張してはいない。
<!--/-->

```agda
  δ∈sθ : ⟨ fst δ ∈ˢ sucV (fst θ) ⟩
  δ∈sθ = member (sucV (fst θ)) (fst least)
```

<!--en-->
The underlying set of `δ` is an ordinal, because it is a member of the ordinal successor of an ordinal.
<!--zh-->
`δ` 的底层集是序数，因为它是某序数的序数后继的成员。
<!--ja-->
`δ` の底の集合は順序数である。順序数の順序数としての後続の要素だからである。
<!--/-->

```agda
  oδ : IsOrd (fst δ)
  oδ = mem-ord {A = sucV (fst θ)} (suc-ord oθ) (fst δ) δ∈sθ
```

<!--en-->
The least candidate is an internal cardinal, read off the candidate record.
<!--zh-->
最小候选是内部基数，由候选记录读出。
<!--ja-->
最小の候補は内部の基数である。候補の記録から読み取られる。
<!--/-->

```agda
  cδ : IsCardinalL δ
  cδ = fst (fst (snd least))
```

<!--en-->
The given cardinal lies below the least candidate, also read off the candidate record.
<!--zh-->
给定基数位于最小候选之下，这同样由候选记录读出。
<!--ja-->
与えられた基数は、最小の候補の下にある。これも候補の記録から読み取られる。
<!--/-->

```agda
  κ∈δ : ⟨ fst κ ∈ˢ fst δ ⟩
  κ∈δ = snd (fst (snd least))
```

<!--en-->
Leastness says that no earlier index of the search space is a candidate.
<!--zh-->
最小性说：搜索空间中没有任何更早的索引是候选。
<!--ja-->
最小性は、探索空間のそれより早い索引が候補ではないことを言う。
<!--/-->

```agda
  δ-min : (b : A) → ⟨ Good b ⟩ → (SWO._<∙_ w b (fst least) → ⊥₀)
  δ-min = snd (snd least)
```

<!--en-->
Global leastness is stated as a containment: for every ordinal internal cardinal `c` above `κ`, every member of `δ` belongs to `c`. This is exactly the last clause of the successor-cardinal record, and the proof compares the ordinals `δ` and `c`.
<!--zh-->
全局最小性被陈述为包含：对每个位于 `κ` 之上的序数内部基数 `c`，`δ` 的每个成员都属于 `c`。这正是后继基数记录的最后一个条款；证明比较序数 `δ` 与 `c`。
<!--ja-->
大域的な最小性は、包含として述べられる。`κ` より上にある順序数の内部基数 `c` ごとに、`δ` のすべての要素は `c` に属する。これは、後続基数の記録の最後の条項そのものであり、証明は順序数 `δ` と `c` を比較する。
<!--/-->

```agda
  leastness : (c : SL.S) → IsOrd (fst c) → IsCardinalL c
            → ⟨ fst κ ∈ˢ fst c ⟩
            → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
  leastness c oc cc κ∈c = go (ord-tri (fst δ) oδ (fst c) oc)
    where
```

<!--en-->
The three trichotomy cases are handled directly: if `δ` lies below `c`, the transitivity of `c` gives the containment; if they are equal, the equation transports the containment; if `c` lies below `δ`, a contradiction is derived from the leastness.
<!--zh-->
三分法的三种情形被直接处理：若 `δ` 低于 `c`，由 `c` 的传递性给出包含；若二者相等，沿等式搬运包含；若 `c` 低于 `δ`，则由最小性导出矛盾。
<!--ja-->
三岐性の三つの場合は直接扱われる。`δ` が `c` より下なら、`c` の推移性が包含を与える。等しいなら、等式に沿って包含を運ぶ。`c` が `δ` より下なら、最小性から矛盾を導く。
<!--/-->

```agda
    go : Tri (fst δ) (fst c)
       → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
    go (inl δ∈c)       x x∈δ = oc .fst x∈δ δ∈c
    go (inr (inl e))   x x∈δ = subst (λ v → ⟨ fst x ∈ˢ v ⟩) e x∈δ
    go (inr (inr c∈δ)) x x∈δ = ⊥₀-rec (δ-min b bGood b<δ)
```

<!--en-->
In the remaining case, `c ∈ δ`. Since `fst δ ∈ sucV (fst θ)` and the ordinal `sucV (fst θ)` is transitive, it follows that `fst c ∈ sucV (fst θ)`. Only this contradictory branch needs to pull the competing cardinal back into the bounded search space; no prior bound on an arbitrary competitor was assumed.
<!--zh-->
在余下的情形中有 `c ∈ δ`。由 `fst δ ∈ sucV (fst θ)` 及序数 `sucV (fst θ)` 的传递性，可得 `fst c ∈ sucV (fst θ)`。只有这个反证分支才需要把竞争基数拉回有界搜索空间；证明并未预先假设任意竞争者都受 `θ` 限制。
<!--ja-->
残る場合には `c ∈ δ` である。`fst δ ∈ sucV (fst θ)` であり、順序数 `sucV (fst θ)` は推移的なので、`fst c ∈ sucV (fst θ)` が従う。競合する基数を有界探索へ引き戻す必要があるのは、この矛盾を導く枝だけである。任意の競合者があらかじめ `θ` で抑えられているとは仮定していない。
<!--/-->

```agda
      where
      c∈sθ : ⟨ fst c ∈ˢ sucV (fst θ) ⟩
      c∈sθ = suc-ord oθ .fst c∈δ δ∈sθ
      b : A
      b = fiber (sucV (fst θ)) c∈sθ .fst
```

<!--en-->
The recovered index presents exactly `c`, and the constructible set it presents is therefore `c` itself; the candidate predicate for this index is obtained by transporting the cardinality and the membership of `c` along that identification.
<!--zh-->
恢复出的索引恰呈现 `c`，其呈现的可构造集合即 `c` 自身；该索引的候选谓词由沿此同一视搬运 `c` 的基数性与隶属得到。
<!--ja-->
復元された索引はちょうど `c` を提示し、その索引が提示する構成可能な集合は `c` 自身である。この索引のための候補の述語は、`c` の基数性と所属をその同一視に沿って運ぶことで得られる。
<!--/-->

```agda
      be : ⟪ sucV (fst θ) ⟫↪ b ≡ fst c
      be = fiber (sucV (fst θ)) c∈sθ .snd
      upb : up b ≡ c
      upb = Σ≡Prop (λ v → snd (isL v)) be
      bGood : ⟨ Good b ⟩
```

<!--en-->
The membership of `c` below `δ` is then converted into the strict order of the search space, contradicting the leastness of the selected index.
<!--zh-->
于是「`c` 位于 `δ` 之下」的隶属被转换为搜索空间的严格序，与所选索引的最小性矛盾。
<!--ja-->
そして、`c` が `δ` より下にあるという所属は、探索空間の厳格な順序に変換され、選ばれた索引の最小性と矛盾する。
<!--/-->

```agda
      bGood = subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upb) (cc , κ∈c)
      b<δ : SWO._<∙_ w b (fst least)
      b<δ = transport (λ i → sym (w-lt b (fst least)) i)
              (subst (λ v → ⟨ v ∈ˢ fst δ ⟩) (sym be) c∈δ)
```
</div>
</details>

<!--en-->
`CardAboveL` supplies only the propositionally truncated existence of some ordinal internal cardinal `θ` with `κ ∈ θ`; it supplies no leastness and does not select `θ`. The proof maps each local witness through `Reduce`, where minimization occurs inside the presentation of `sucV (fst θ)`. The resulting successor cardinal therefore remains under propositional truncation.
<!--zh-->
`CardAboveL` 只在命题截断下给出某个序数内部基数 `θ`，满足 `κ ∈ θ`；它既不提供最小性，也不选定 `θ`。证明把每个局部见证送入 `Reduce`，并在那里于 `sucV (fst θ)` 的呈现中完成极小化。因此，所得后继基数仍处在命题截断之下。
<!--ja-->
`CardAboveL` が与えるのは、`κ ∈ θ` を満たす何らかの内部順序数基数 `θ` の命題的に切り詰められた存在だけである。最小性は与えず、`θ` も選ばない。証明は各局所的な証人を `Reduce` へ写し、そこで `sucV (fst θ)` の提示の内部における最小化を行う。したがって、得られる後続基数も命題的切り詰めの内側に留まる。
<!--/-->

```agda
succCardExists : SuccCardExists
succCardExists κ oκ cκ κ∉ω = map₁ build (CardAboveL κ oκ cκ κ∉ω)
  where
  build : Σ[ θ ∶ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
```

<!--en-->
Within one local branch, `build` packages the chosen `δ` with the four clauses of `SuccCardL δ κ`: `δ` is an ordinal, it is an internal cardinal, `κ ∈ δ`, and `δ` is contained in every ordinal internal cardinal lying above `κ`.
<!--zh-->
在一个局部分支内，`build` 把选出的 `δ` 与 `SuccCardL δ κ` 的四个条款打包：`δ` 是序数，是内部基数，满足 `κ ∈ δ`，并且包含于每个严格大于 `κ` 的序数内部基数。
<!--ja-->
一つの局所的な枝の内部で、`build` は選ばれた `δ` を `SuccCardL δ κ` の四条件と組にする。すなわち、`δ` は順序数であり、内部基数であり、`κ ∈ δ` を満たし、さらに `κ` より大きい任意の内部順序数基数に包含される。
<!--/-->

```agda
        → Σ[ δ ∶ SL.S ] SuccCardL δ κ
  build (θ , oθ , cθ , κ∈θ) = R.δ , R.oδ , R.cδ , R.κ∈δ , R.leastness
    where module R = Reduce κ oκ θ oθ cθ κ∈θ
```

<!--en-->
## Discharging the structural estimates
<!--zh-->
## 兑现结构性估计
<!--ja-->
## 構造に関する評価を満たす
<!--/-->

<!--en-->
A stage whose index is an ordinal is constructible, by the axiom relating stages and constructibility.
<!--zh-->
指数为序数的层是可构造的，依据联系层与可构造性的公理。
<!--ja-->
指数が順序数である段階は、構成可能である。段階と構成可能性を結ぶ公理によるものである。
<!--/-->

```agda
stage-is-L : (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩
stage-is-L δ ordδ = isL-Lset (fst δ) ordδ
```

<!--en-->
The bridging predicate for the power set states its content: for two constructible sets `κ` and `y`, with `κ` an ordinal and `y` a member of the model's power set of `κ`, every ambient member `z` of `y` is constructible, belongs to `κ`, and is an ordinal.
<!--zh-->
幂集的桥接谓词陈述其内容：对可构造集合 `κ` 与 `y`，其中 `κ` 是序数且 `y` 属于模型幂集 `𝒫κ`，`y` 的每个外围成员 `z` 都可构造、属于 `κ`，且是序数。
<!--ja-->
冪集合のための橋渡しの述語は、その内容を述べる。構成可能な集合 `κ` と `y`、すなわち `κ` が順序数であり `y` がモデルの冪集合 `𝒫κ` の要素であるとき、`y` の周囲のすべての要素 `z` は構成可能であり、`κ` に属し、順序数でもあるのである。
<!--/-->

```agda
zStrongest : ModelL.isZFModel → Type (ℓ-suc ℓ)
zStrongest zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩
  → (⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z)
```

<!--en-->
The bridge depends on the chosen ZF model because its premise refers to that model's specified power set. Thus `𝒫κ` here remains the internal power set of `L` throughout the argument.
<!--zh-->
这座桥依赖所给的 ZF 模型，因为其前提涉及该模型指定的幂集。因此，在整个论证中，`𝒫κ` 始终是 `L` 的内部幂集。
<!--ja-->
この橋渡しは、与えられた ZF モデルに依存する。その前提が、そのモデルによって指定された冪集合を参照するからである。したがって、議論を通じて `𝒫κ` は常に `L` の内部冪集合である。
<!--/-->

```agda
  where open ModelL.isZFModel zf using ( 𝒫 )
```

<!--en-->
The subtle point is a change of domains. Power-set membership yields a subset statement quantified over constructible sets, whereas `z` initially ranges over the ambient hierarchy. Transitivity of `L` first makes `z` available as a constructible set; only then can the internal subset statement be applied, after which ordinality follows from `z ∈ κ` and the ordinality of `κ`.
<!--zh-->
这里的细节在于量化域发生了转换。幂集隶属给出的子集陈述量化可构造集合，而 `z` 起初量化整个外围层级。先用 `L` 的传递性证明 `z` 可构造，才能把内部子集陈述施用于它；随后由 `z ∈ κ` 与 `κ` 的序数性得到 `z` 的序数性。
<!--ja-->
ここで注意すべき点は、量化領域が変わることである。冪集合への所属から得る部分集合の主張は構成可能な集合にわたって量化するが、`z` は最初、周囲の階層全体を動く。まず `L` の推移性によって `z` が構成可能であることを示して初めて、内部の部分集合の主張を適用できる。その後、`z ∈ κ` と `κ` の順序数性から `z` の順序数性が従う。
<!--/-->

```agda
z-strongest : (zf : ModelL.isZFModel) → zStrongest zf
z-strongest zf κ y ordκ y∈𝒫κ z z∈y = isLz , z∈κ , mem-ord {A = fst κ} ordκ z z∈κ
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )
```

<!--en-->
The constructibility of `z` follows by transitivity: `z` belongs to the constructible set `y`, which is itself constructible.
<!--zh-->
`z` 的可构造性由传递性得出：`z` 属于可构造集合 `y`，而 `y` 自身可构造。
<!--ja-->
`z` の構成可能性は、推移性によって従う。`z` は構成可能な集合 `y` に属し、`y` 自身が構成可能だからである。
<!--/-->

```agda
  isLz : ⟨ isL z ⟩
  isLz = isL-trans z∈y (snd y)
```

<!--en-->
The defining specification of the model's power set identifies `y ∈ 𝒫κ` with the internal subset relation `y ⊆ κ`. This relation quantifies over elements of `SL`, so the constructibility established in the preceding step is essential.
<!--zh-->
模型幂集的定义规格把 `y ∈ 𝒫κ` 认同为内部子集关系 `y ⊆ κ`。这一关系量化 `SL` 的元素，因此上一步所得的可构造性不可缺少。
<!--ja-->
モデルの冪集合の定義仕様は、`y ∈ 𝒫κ` を内部の部分集合関係 `y ⊆ κ` と同一視する。この関係は `SL` の要素にわたって量化するので、前の段階で示した構成可能性が不可欠である。
<!--/-->

```agda
  y⊆κ : ⟨ y ModelL.⊆ˢ κ ⟩
  y⊆κ = subst ⟨_⟩ (ModelL.℩-spec (hasPower κ) y) y∈𝒫κ
```

<!--en-->
The internal subset relation is then applied to the pair of `z` and its constructibility, yielding membership of `z` in `κ`.
<!--zh-->
内部子集关系随即施加于「`z` 连同其可构造性」的配对，得到 `z` 属于 `κ`。
<!--ja-->
内部の部分集合の関係は、`z` とその構成可能性の対に適用され、`z` の `κ` への所属を与える。
<!--/-->

```agda
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = y⊆κ (z , isLz) z∈y
```

<!--en-->
## Every subset lands before the successor
<!--zh-->
## 每个子集都在后继之前落定
<!--ja-->
## 各部分集合は後続基数までに現れる
<!--/-->

<!--en-->
The landing lemma is stated for the model, the bounded-subset interface, and a fixed successor cardinal `δ` of `κ`: every member of the model's power set of `κ` lies in the stage `Lset δ`.
<!--zh-->
落位引理就模型、有界子集接口与 `κ` 的固定后继基数 `δ` 陈述：模型幂集 `𝒫κ` 的每个成员都落在层 `Lset δ` 中。
<!--ja-->
着地の補題は、モデル・有界部分集合のインターフェース・そして `κ` の固定された後続基数 `δ` に対して述べられる。モデルの冪集合 `𝒫κ` のすべての要素は、段階 `Lset δ` の中にある。
<!--/-->

```agda
stage-landing :
    (zf : ModelL.isZFModel) → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  → (δ : SL.S) → SuccCardL δ κ
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
```

<!--en-->
For each fixed `y`, the bounded-subset theorem returns a suitable stage index `β` only under propositional truncation. The desired conclusion `y ∈ Lset δ` is itself a proposition, so the proof may reason with a local `β` without choosing such indices uniformly. The ambient pointwise subset hypothesis required by that theorem is exactly the bridge just established.
<!--zh-->
对每个固定的 `y`，有界子集定理只在命题截断下返回一个合适的层索引 `β`。目标结论 `y ∈ Lset δ` 本身是命题，所以证明可以使用局部的 `β` 推理，而无需为所有 `y` 一致地选择层索引。该定理所需的外围逐点子集前提，正是刚才建立的桥。
<!--ja-->
固定した各 `y` に対して、有界部分集合定理が適切な段階の添字 `β` を返すのは命題的切り詰めの内側だけである。目標である `y ∈ Lset δ` 自体が命題なので、すべての `y` に対して添字を一様に選ぶことなく、局所的な `β` を用いて議論できる。この定理が要求する周囲の点ごとの部分集合の仮定は、直前に確立した橋渡しそのものである。
<!--/-->

```agda
  → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
stage-landing zf ibs κ ordκ cardκ κ∉ω δ (ordδ , cardδ , κ∈δ , _) y y∈𝒫κ =
  rec₁ (snd (fst y ∈ˢ Lset (fst δ))) place (ibs κ ordκ cardκ κ∉ω y y⊆κ)
  where
  y⊆κ : (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩
```

<!--en-->
From `y ∈ 𝒫κ` and `z ∈ y`, the strongest-member lemma yields `z ∈ κ`. Its proof first uses the transitivity of `L` to recognize the ambient member `z` as constructible, so that the internal subset relation expressed by power-set membership can be applied to it.
<!--zh-->
由 `y ∈ 𝒫κ` 与 `z ∈ y`，最强成员引理得到 `z ∈ κ`。其证明先利用 `L` 的传递性认出外围成员 `z` 是可构造的，从而能把幂集隶属所表达的内部子集关系施用于 `z`。
<!--ja-->
`y ∈ 𝒫κ` と `z ∈ y` から、最強要素補題は `z ∈ κ` を与える。その証明では、まず `L` の推移性によって外側の要素 `z` が構成可能であると分かるので、冪集合への所属が表す内部の部分集合関係を `z` に適用できる。
<!--/-->

```agda
  y⊆κ z z∈y = z-strongest zf κ y ordκ y∈𝒫κ z z∈y .snd .fst
```

<!--en-->
No injection from `δ` into `κ` can exist, because `δ` is an internal cardinal and `κ` is a member of `δ`. This refutation is the tool used to eliminate the impossible trichotomy branches below.
<!--zh-->
从 `δ` 到 `κ` 的单射不可能存在，因为 `δ` 是内部基数且 `κ` 是 `δ` 的成员。这条反驳是下文排除不可能三歧分支的工具。
<!--ja-->
`δ` から `κ` への単射は存在し得ない。`δ` は内部の基数であり、`κ` は `δ` の要素だからである。この反駁が、下で不可能な三択の分岐を排除する道具である。
<!--/-->

```agda
  no-δ↪κ : InjL δ κ → ⊥₀
  no-δ↪κ = cardδ κ κ∈δ
```

<!--en-->
For the fixed subset `y`, the bounded-subset estimate supplies, under propositional truncation, an ordinal `β` such that `y ∈ Lset β` and there is an internal coded injection `β ↪ κ`. Once such a witness is exposed locally, `place` compares `β` with `δ` by ordinal trichotomy and proves that `y` already belongs to `Lset δ`.
<!--zh-->
对固定的子集 `y`，有界子集估计在命题截断下给出一个序数 `β`，使得 `y ∈ Lset β`，并且存在内部编码单射 `β ↪ κ`。在局部展开这样一个见证后，`place` 用序数三歧性比较 `β` 与 `δ`，并证明 `y` 已属于 `Lset δ`。
<!--ja-->
固定した部分集合 `y` に対し、有界部分集合の評価は命題的切り詰めのもとで、`y ∈ Lset β` を満たし、内部の符号化された単射 `β ↪ κ` をもつ順序数 `β` を与える。その証人を局所的に取り出すと、`place` は順序数の三分法によって `β` と `δ` を比較し、`y` がすでに `Lset δ` に属することを示す。
<!--/-->

```agda
  place : Σ[ β ∶ SL.S ]
            (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ)
        → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  place (β , ordβ , y∈Lβ , β↪κ) = go (ord-tri (fst β) ordβ (fst δ) ordδ)
    where
```

<!--en-->
If `β` lies below `δ`, monotonicity of the tower directly places the member at the lower stage inside the higher stage. If `β` equals `δ`, the injection `β ↪ κ` would become an injection `δ ↪ κ`, contradicting the cardinality of `δ`.
<!--zh-->
若 `β` 低于 `δ`，塔的单调性直接把较低层中的成员放进较高层。若 `β` 等于 `δ`，则注入 `β ↪ κ` 会变成注入 `δ ↪ κ`，与 `δ` 的基数性矛盾。
<!--ja-->
`β` が `δ` より下なら、塔の単調性が、低い段階の要素を高い段階の中に直接置く。`β` が `δ` に等しいなら、注入 `β ↪ κ` は `δ ↪ κ` になり、`δ` の基数性と矛盾する。
<!--/-->

```agda
    go : Tri (fst β) (fst δ) → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
    go (inl β∈δ)       = Lset-mono β∈δ y∈Lβ
    go (inr (inl e))   = ⊥₀-rec (no-δ↪κ (subst (λ b → InjL b κ) β≡δ β↪κ))
      where
      β≡δ : β ≡ δ
```

<!--en-->
In the equality branch, equality of the underlying sets lifts to equality of the corresponding elements of `L` because constructibility is proposition-valued. In the remaining branch, where `δ ∈ β`, the inclusion `δ ↪ β` followed by the given coded injection `β ↪ κ` would produce the forbidden coded injection `δ ↪ κ`.
<!--zh-->
在相等分支中，因为可构造性取命题值，底层集合的相等可提升为相应 `L` 元素的相等。在余下的 `δ ∈ β` 分支中，先取包含给出的 `δ ↪ β`，再接上已有的编码单射 `β ↪ κ`，便会产生被排除的编码单射 `δ ↪ κ`。
<!--ja-->
等しい場合には、構成可能性が命題値なので、基礎となる集合の等しさを対応する `L` の要素の等しさへ持ち上げられる。残る `δ ∈ β` の場合には、包含から得る `δ ↪ β` に、与えられた符号化された単射 `β ↪ κ` を続けると、存在し得ない符号化された単射 `δ ↪ κ` が生じる。
<!--/-->

```agda
      β≡δ = Σ≡Prop (λ x → snd (isL x)) e
    go (inr (inr δ∈β)) = ⊥₀-rec (no-δ↪κ
      (injl-trans δ β κ (inclusion-coded δ β δ⊆β) β↪κ))
      where
      δ⊆β : (z : SV.S) → ⟨ z ∈ˢ fst δ ⟩ → ⟨ z ∈ˢ fst β ⟩
```

<!--en-->
The inclusion is the transitivity of the ordinal `β` applied to the two memberships.
<!--zh-->
包含是序数 `β` 的传递性施于两条隶属的结果。
<!--ja-->
包含は、順序数 `β` の推移性を、二つの所属に適用したものである。
<!--/-->

```agda
      δ⊆β z z∈δ = ordβ .fst z∈δ δ∈β
```

<!--en-->
## Coding the power set below the successor
<!--zh-->
## 把幂集编码到后继以下
<!--ja-->
## 冪集合を後続基数の下へコード化する
<!--/-->

<!--en-->
The power-set comparison now follows from the chain `𝒫κ ↪ Lset δ ↪ δ`. The first arrow comes from the fact that every member of the internal power set lies in `Lset δ`, and the second counts that constructible stage by `δ`. No stage index is chosen uniformly for the members of `𝒫κ`.
<!--zh-->
幂集比较现在来自复合链 `𝒫κ ↪ Lset δ ↪ δ`。第一条箭头来自「内部幂集的每个成员都属于 `Lset δ`」，第二条则用 `δ` 计数这一可构造层。证明没有为 `𝒫κ` 的各个成员一致地选择层索引。
<!--ja-->
冪集合の比較は、鎖 `𝒫κ ↪ Lset δ ↪ δ` から従う。第一の矢印は、内部冪集合のすべての要素が `Lset δ` に属することから得られ、第二の矢印は、その構成可能な段階を `δ` で数える。`𝒫κ` の各要素に対して段階の添字を一様に選ぶことはない。
<!--/-->

```agda
power-into-succ :
    (zf : ModelL.isZFModel) → StageCountedCoded → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  → (δ : SL.S) → SuccCardL δ κ
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
```

<!--en-->
Pointwise containment is first converted by `inclusion-coded` into the coded injection `𝒫κ ↪ Lset δ`. The stage-counting hypothesis supplies `Lset δ ↪ δ`, and `injl-trans` composes the two. Since both comparisons are expressed by `InjL`, their witnessing graphs remain propositionally truncated.
<!--zh-->
逐点包含先由 `inclusion-coded` 转换为编码单射 `𝒫κ ↪ Lset δ`。层计数假设给出 `Lset δ ↪ δ`，再由 `injl-trans` 复合两者。由于两项比较都用 `InjL` 表达，见证它们的图仍处于命题截断之下。
<!--ja-->
点ごとの包含は、まず `inclusion-coded` によって符号化された単射 `𝒫κ ↪ Lset δ` に変換される。段階計数の仮定が `Lset δ ↪ δ` を与え、`injl-trans` が両者を合成する。どちらの比較も `InjL` で表されるため、それらを証すグラフは命題的切り詰めの内側に留まる。
<!--/-->

```agda
power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc@(ordδ , _ , κ∈δ , _) =
  injl-trans (𝒫 κ) Lδ δ (inclusion-coded (𝒫 κ) Lδ into)
    (scc δ Lδ ordδ δ∉ω refl)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
```

<!--en-->
The stage at `δ` is presented as an element of `L` by pairing the stage set with its constructibility certificate, obtained from the ordinality of `δ`.
<!--zh-->
`δ` 处的层通过把层集合与其可构造性证书配对而呈现为 `L` 的元素，证书由 `δ` 的序数性得来。
<!--ja-->
`δ` での段階は、段階の集合とその構成可能性の証明を対にすることで、`L` の要素として提示される。証明は、`δ` の順序数性から得られる。
<!--/-->

```agda
  Lδ : SL.S
  Lδ = Lset (fst δ) , stage-is-L δ ordδ
```

<!--en-->
The successor cardinal `δ` lies outside `ω`: if it were inside, the membership `κ ∈ δ` would force `κ ∈ ω` by transitivity of `ω`, contradicting the hypothesis.
<!--zh-->
后继基数 `δ` 落在 `ω` 之外：若它在 `ω` 内，则隶属 `κ ∈ δ` 经 `ω` 的传递性将迫使 `κ ∈ ω`，与假设矛盾。
<!--ja-->
後続基数 `δ` は `ω` の外にある。もし `ω` の中にあるなら、所属 `κ ∈ δ` が `ω` の推移性によって `κ ∈ ω` を強制し、仮定と矛盾する。
<!--/-->

```agda
  δ∉ω : ⟨ fst δ ∈ˢ ω ⟩ → ⊥₀
  δ∉ω δ∈ω = κ∉ω (ω-ord .fst {x = fst δ} {y = fst κ} κ∈δ δ∈ω)
```

<!--en-->
Every member of the power set is landed inside `Lset δ` by the landing lemma, with its constructibility supplied through the transitivity of `L` from the power-set membership.
<!--zh-->
幂集的每个成员由安放引理落入 `Lset δ` 之内，其可构造性经 `L` 的传递性从幂集隶属供给。
<!--ja-->
冪集合のすべての要素は、着地の補題によって `Lset δ` の中に落ちる。その構成可能性は、冪集合への所属から、`L` の推移性を通して供給される。
<!--/-->

```agda
  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ =
    stage-landing zf ibs κ ordκ cardκ κ∉ω δ sc (z , isL-trans z∈ (snd (𝒫 κ))) z∈
```

<!--en-->
## The generalized continuum hypothesis
<!--zh-->
## 广义连续统假设
<!--ja-->
## 一般連続体仮説
<!--/-->

<!--en-->
The final theorem keeps the two directions logically separate. Stage counting and the bounded-subset theorem establish `𝒫κ ↪ δ`. Only after that injection has been obtained does the independent conditional theorem `SuccIntoPower` apply, using it together with the successor-cardinal facts to establish `δ ↪ 𝒫κ`.
<!--zh-->
最终定理把两个方向的职责明确分开。层计数与有界子集定理建立 `𝒫κ ↪ δ`。只有取得这条单射之后，独立的条件定理 `SuccIntoPower` 才能把它与后继基数事实一同使用，建立 `δ ↪ 𝒫κ`。
<!--ja-->
最後の定理では、二つの向きの役割を明確に分ける。段階計数と有界部分集合定理が `𝒫κ ↪ δ` を確立する。この単射を得た後で初めて、独立した条件付き定理 `SuccIntoPower` を適用し、それと後続基数の事実を用いて `δ ↪ 𝒫κ` を確立する。
<!--/-->

```agda
gch-from-internal-bill :
    (zf : ModelL.isZFModel)
  → StageCountedCoded → InternalBoundedSubset → SuccIntoPower zf
  → GCHStatement zf
gch-from-internal-bill zf scc ibs sip κ ordκ cardκ κ∉ω =
```

<!--en-->
The theorem `succCardExists` gives only the propositionally truncated existence of a successor cardinal `δ`. The map therefore works inside each local witness: `step` keeps the successor-cardinal proof, constructs the truncated coded injection `𝒫κ ↪ δ` by the landing argument, and passes that result to the independent conditional interface to obtain the truncated coded injection `δ ↪ 𝒫κ`.
<!--zh-->
定理 `succCardExists` 只给出后继基数 `δ` 的命题截断存在。因此映射在每个局部见证内工作：`step` 保留后继基数证明，用落层论证构造命题截断下的编码单射 `𝒫κ ↪ δ`，再把该结果交给独立的条件接口，得到命题截断下的编码单射 `δ ↪ 𝒫κ`。
<!--ja-->
定理 `succCardExists` が与えるのは、後続基数 `δ` の命題的切り詰めのもとでの存在だけである。そこで写像は各局所的な証人の内部で働く。`step` は後続基数の証明を保ち、着地の議論から命題的切り詰めのもとで符号化された単射 `𝒫κ ↪ δ` を構成し、その結果を独立した条件付きインターフェースに渡して、同じく切り詰められた符号化された単射 `δ ↪ 𝒫κ` を得る。
<!--/-->

```agda
  map₁ step (succCardExists κ ordκ cardκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∶ SL.S ] SuccCardL δ κ
       → Σ[ δ ∶ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
```

<!--en-->
The landing argument supplies `pis : InjL (𝒫 κ) δ`, and the independent conditional interface uses `pis` to supply `InjL δ (𝒫 κ)`. Each `InjL` is the propositional truncation of the existence of a constructible injection code, so the result records exactly two opposite coded-injection existences; it does not select either graph or construct a bijection, a set equality, or a cardinal-arithmetic equality.
<!--zh-->
落层论证给出 `pis : InjL (𝒫 κ) δ`，独立的条件接口再以 `pis` 为前提给出 `InjL δ (𝒫 κ)`。每个 `InjL` 都是「存在可构造单射码」的命题截断，所以结果恰好记录两个相反方向的编码单射存在性；它没有选定任何一张图，也没有构造双射、集合相等或基数算术等式。
<!--ja-->
着地の議論は `pis : InjL (𝒫 κ) δ` を与え、独立した条件付きインターフェースは `pis` を前提として `InjL δ (𝒫 κ)` を与える。各 `InjL` は、構成可能な単射の符号が存在することの命題的切り詰めである。したがって結果が記録するのは、ちょうど反対向きの二つの符号化された単射の存在であり、どちらのグラフも選択せず、全単射、集合の等しさ、基数算術上の等式も構成しない。
<!--/-->

```agda
  step (δ , sc) = δ , sc , pis , sip κ δ κ∉ω sc pis
    where
    pis : InjL (𝒫 κ) δ
    pis = power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc
```
