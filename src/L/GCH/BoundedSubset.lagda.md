<!--en-->
# Bounded subsets appear at controlled stages

The bounded-subset theorem starts with an internal cardinal `κ` whose underlying set is an ordinal and does not belong to `ω`, together with an arbitrary constructible set `y` whose ambient members all lie in `κ`. Under propositional truncation, it gives a constructible ordinal `β` such that `y ∈ Lset β` and a coded injection `β ↪ κ` exists. It assumes no formula defining `y`, selects no least stage, and makes no uniform choice of `β` as `y` varies.
<!--zh-->
# 有界子集落在受控层

有界子集定理从如下数据出发：内部基数 `κ` 的底层集合是序数且不属于 `ω`，任意可构造集合 `y` 的每个外围成员都属于 `κ`。定理在命题截断下给出可构造序数 `β`，使 `y ∈ Lset β`，并存在编码单射 `β ↪ κ`。这里不假设 `y` 由某个公式定义，不选取最小层，也不随 `y` 统一选取 `β`。
<!--ja-->
# 有界部分集合が制御された段階に現れる

有界部分集合定理では、台となる集合が順序数であり `ω` に属さない内部基数 `κ` と、周囲の各要素が `κ` に属する任意の構成可能集合 `y` を考えます。命題的切り詰めのもとで、`y ∈ Lset β` を満たし、符号化された単射 `β ↪ κ` が存在するような構成可能順序数 `β` が得られます。`y` を定義する論理式は仮定せず、最小の段階も選ばず、`y` ごとに `β` を一様に選ぶこともありません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The proof is classical only through the displayed instance of excluded middle. This hypothesis supports the earlier constructions of stages, hulls, and coded maps used here; it does not turn the final truncated existence into a chosen family of witnesses.
<!--zh-->
本证明的经典性只来自这里显式给出的排中律实例。该假设支撑本章所用的层、壳与编码映射等先前构造；它不会把最终的截断存在变成一族已选定的见证。
<!--ja-->
この証明で用いる古典性は、ここで明示された排中律の実例だけです。この仮定は、本章で利用する段階、包、符号化された写像の先行する構成を支えますが、最後の切り詰められた存在を、選択された証人の族へ変えるものではありません。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and excluded middle at level `ℓ-suc ℓ`. Every construction below, including the final bounded-subset theorem, depends on this single classical hypothesis and on no choice principle.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上的排中律。下文全部构造，包括最终的有界子集定理，都只依赖这一项经典假设，而不依赖任何选择原理。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` における排中律を固定します。以下のすべての構成は、最後の有界部分集合定理も含め、この一つの古典的仮定だけに依存し、選択原理には依存しません。
<!--/-->

```agda
module L.GCH.BoundedSubset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Two levels of objects must be kept separate throughout the argument. Symbols such as `κ`, `α₀`, `lam`, and later `β` denote sets in the ambient cumulative hierarchy, some proved to be ordinals; `Lset κ`, `Lset α₀`, `Lset lam`, and `Lset β` denote the corresponding constructible stages. Membership in a stage index and membership in its indexed stage are different assertions.
<!--zh-->
整个论证必须始终区分两类对象。`κ`、`α₀`、`lam` 以及后文的 `β` 等符号表示外围累积层级中的集合，其中一些会被证明为序数；`Lset κ`、`Lset α₀`、`Lset lam` 与 `Lset β` 则表示相应的可构造层。属于层索引与属于该索引所确定的层是两个不同的断言。
<!--ja-->
議論を通して、二つの種類の対象を区別しなければなりません。`κ`、`α₀`、`lam`、そして後の `β` は周囲の累積階層の集合を表し、そのうちいくつかは順序数であることが示されます。一方、`Lset κ`、`Lset α₀`、`Lset lam`、`Lset β` は、それぞれに対応する構成可能段階です。段階の添字に属することと、その添字が定める段階に属することは別の主張です。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( #∈ω )
```

<!--en-->
The first task is to place both `κ` and `y` in one sufficiently high constructible stage. Since `y` is already supplied as a constructible set, an occurrence stage can be obtained directly; no formula defining `y`, and no finite list of defining parameters, enters this construction.
<!--zh-->
第一项任务是把 `κ` 与 `y` 一同放进某个足够高的可构造层。由于 `y` 已作为可构造集合给出，可以直接取得它的某个出现层；这一构造不使用定义 `y` 的公式，也不使用任何有限的定义参数表。
<!--ja-->
最初の課題は、`κ` と `y` を一つの十分高い構成可能段階へ入れることです。`y` はすでに構成可能な集合として与えられているので、それが現れる段階を直接得られます。`y` を定義する論理式も、有限個の定義パラメータの列も、この構成には入りません。
<!--/-->

```agda
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( pairʟ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL )
```

<!--en-->
The central strategy is to enlarge `Lset κ` by the single point `y`, generate an elementary Skolem hull from that transitive starting set, and apply condensation. Counting the starting set by `κ` will count the whole hull by `κ`; condensation will then convert the collapsed hull into a stage `Lset β`.
<!--zh-->
核心策略是把单点 `y` 添入 `Lset κ`，从这个传递起始集生成初等 Skolem 壳，再应用凝聚。先用 `κ` 计数起始集，便可进一步用 `κ` 计数整个壳；凝聚随后把塌缩后的壳识别为某个层 `Lset β`。
<!--ja-->
中心となる方針は、`Lset κ` に一点 `y` を加え、この推移的な出発集合から初等 Skolem 包を生成し、凝縮を適用することです。出発集合を `κ` で数えれば、包全体も `κ` で数えられます。その後、凝縮によって崩壊した包がある段階 `Lset β` と同一視されます。
<!--/-->

```agda
open import L.GCH.Assembly {ℓ} lem using ( InternalBoundedSubset )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.GCH.SkolemHull {ℓ} lem
  using ( module UnionKit; module HullStage; module HullElemDown )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prodL; ω⊆; Goal; module Step )
```

<!--en-->
This plan needs two different kinds of control. A sufficiently closed ordinal `lam` provides the ambient stage in which the hull and condensation argument can be carried out. Coded injections control size: first `X ↪ κ`, then `M ↪ κ`, and finally `β ↪ κ`.
<!--zh-->
这条路线需要两种不同的控制。一个具有充分闭包性质的序数 `lam` 提供环境层，使壳与凝聚论证能在其中进行。编码单射则控制大小：先得到 `X ↪ κ`，再得到 `M ↪ κ`，最终得到 `β ↪ κ`。
<!--ja-->
この方針には、二種類の制御が必要です。十分な閉性をもつ順序数 `lam` は、包と凝縮の議論を行う周囲の段階を与えます。符号化された単射は大きさを制御し、まず `X ↪ κ`、次に `M ↪ κ`、最後に `β ↪ κ` を与えます。
<!--/-->

```agda
open import L.GCH.AdequateStages {ℓ} lem using ( superadequate-above; Superadequate )
open import L.GCH.StageCountingTools {ℓ} lem using ( move )
open import L.GCH.StageInjection {ℓ} lem using ( stage-counted; module Site )
open import L.GCH.OmegaRecursion {ℓ} lem using ( pairʟ-in )
open import L.GCH.HullCounting {ℓ} lem
```

<!--en-->
The size estimate begins with two elementary pieces. The stage `Lset κ` can be coded into `κ`, and a singleton can also be coded into `κ`. Finite tags keep their images disjoint, while the square law for the infinite internal cardinal `κ` absorbs the resulting product back into `κ`.
<!--zh-->
大小估计从两个简单部分开始。层 `Lset κ` 可以编码单射入 `κ`，单点集也可以编码单射入 `κ`。有限标签使两部分的像保持分离，而无穷内部基数 `κ` 的平方律把所得乘积重新吸收到 `κ` 中。
<!--ja-->
大きさの評価は、二つの基本的な部分から始まります。段階 `Lset κ` は `κ` へ符号化でき、単元集合も `κ` へ符号化できます。有限のタグが二つの像を区別し、無限の内部基数 `κ` に対する平方法則が、得られた積を再び `κ` へ収めます。
<!--/-->

```agda
  using ( ord⊆Lset; module Union2; tag-union; module Point; module Count )

```

<!--en-->
Several equalities below are proved by comparing membership in both directions. The alternatives arising from union membership are propositionally truncated, but each target membership statement is a proposition, so those alternatives may be used locally without selecting a lasting branch.
<!--zh-->
下文若干相等通过双向比较成员关系来证明。并集隶属给出的分支带有命题截断，但每个目标隶属陈述本身都是命题，因此可以局部使用这些分支，而不必选定并保留某个分支。
<!--ja-->
以下では、いくつかの等しさを、所属を両方向に比較して証明します。合併への所属から得られる場合分けは命題的に切り詰められていますが、行き先となる所属の主張はいずれも命題です。したがって、どちらかの分岐を選んで保持することなく、その場合分けを局所的に利用できます。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
```

<!--en-->
Finite von Neumann numerals provide the tags used in the union coding, while ordinal successor closure is part of the environment needed for the hull. Well-foundedness supports the square law. Propositional truncation records the existence of coded injections without exposing a chosen graph.
<!--zh-->
有限 von Neumann 数码提供并集编码所需的标签，序数后继闭包则是壳所需环境的一部分。良基性支撑平方律。命题截断记录编码单射的存在，却不暴露一张选定的图。
<!--ja-->
有限 von Neumann 数項は合併の符号化に使うタグを与え、順序数の後続に関する閉性は包に必要な環境の一部をなします。整礎性は平方法則を支えます。命題的切り詰めは、特定のグラフを公開せずに、符号化された単射の存在を記録します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet; ⁅_⁆s )
open InfinitySet {ℓ} using ( #_; ω; sucV )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
Whenever an injection is asserted through `InjL`, its graph exists only under propositional truncation. The proof may compose such existences inside propositions, but it never obtains a distinguished injection that can be used as computational data outside the truncation.
<!--zh-->
凡是通过 `InjL` 断言单射时，其图都只在命题截断下存在。证明可以在命题内部复合这些存在性，却不会得到一条能在截断之外作为计算数据使用的指定单射。
<!--ja-->
`InjL` によって単射を主張する場合、そのグラフが存在するのは命題的切り詰めの内側だけです。証明は命題の内部でそのような存在を合成できますが、切り詰めの外で計算データとして使える特定の単射を得ることはありません。
<!--/-->

```agda
open PT using ( ∣_∣₁ )

```

<!--en-->
The subset premise is deliberately stated with ambient membership. Thus an arbitrary ambient set `z` may be tested for membership in `y` and then in `κ`; `z` is not required to arrive together with its own proof of constructibility.
<!--zh-->
子集前提刻意用外围隶属来陈述。因此可以对任意外围集合 `z` 检验它属于 `y`，继而推出它属于 `κ`；并不要求 `z` 一开始就附带自身的可构造性证明。
<!--ja-->
部分集合の仮定は、意図的に周囲の所属を用いて述べられます。したがって、任意の周囲の集合 `z` について、`y` への所属から `κ` への所属を導けます。`z` 自身の構成可能性の証明が、初めから添えられている必要はありません。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

```

<!--en-->
By contrast, `κ` and `y` are elements of the constructible carrier `S`: each packages an ambient set with evidence that it belongs to `L`. The eventual witness is packaged in the same way, so the theorem produces a constructible ordinal rather than an arbitrary ambient ordinal.
<!--zh-->
与之相对，`κ` 与 `y` 是可构造载体 `S` 的元素：二者都把外围集合与其属于 `L` 的证据打包在一起。最终见证也以同样方式打包，因此定理给出的是可构造序数，而不是任意外围序数。
<!--ja-->
これに対して、`κ` と `y` は構成可能な台 `S` の要素であり、周囲の集合と、それが `L` に属する証拠とを組にしています。最後の証人も同じ形でまとめられるので、定理が与えるのは任意の周囲の順序数ではなく、構成可能な順序数です。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Bounding a constructible subset of a cardinal
<!--zh-->
## 为基数的可构造子集取界
<!--ja-->
## 基数の構成可能な部分集合を有界化する
<!--/-->

<!--en-->
Fix a constructible set `κ` whose underlying set is an ordinal, an internal cardinal, and not a member of `ω`. Also fix an arbitrary constructible set `y` and assume pointwise that every ambient member of `y` belongs to `κ`. These are the complete hypotheses: in particular, no definition of `y` by a formula or by finitely many parameters is assumed.
<!--zh-->
固定可构造集合 `κ`，假设其底层集合是序数、是内部基数且不属于 `ω`。再固定任意可构造集合 `y`，并逐点假设 `y` 的每个外围成员都属于 `κ`。这些就是全部前提；特别地，不假设 `y` 由公式或有限多个参数定义。
<!--ja-->
台となる集合が順序数であり、内部の基数であり、`ω` の要素ではない構成可能集合 `κ` を固定します。さらに任意の構成可能集合 `y` を固定し、`y` の周囲の各要素が `κ` に属すると点ごとに仮定します。仮定はこれですべてです。とくに、`y` が論理式や有限個のパラメータで定義されるとは仮定しません。
<!--/-->

```agda
module At (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
          (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
          (y : S) (y⊆κ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩) where

```

<!--en-->
The assumptions that `κ` is an ordinal and `κ ∉ ω` imply `ω ⊆ κ`. Since every finite von Neumann numeral `# k` belongs to `ω`, it follows that `# k ∈ κ` for every `k`. These elements will serve as the finite tags in the union coding.
<!--zh-->
由 `κ` 的序数性与 `κ ∉ ω` 可得 `ω ⊆ κ`。每个有限 von Neumann 数码 `# k` 都属于 `ω`，所以对每个 `k` 都有 `# k ∈ κ`。这些元素将充当并集编码中的有限标签。
<!--ja-->
`κ` が順序数であることと `κ ∉ ω` から、`ω ⊆ κ` が従います。有限 von Neumann 数項 `# k` はどれも `ω` に属するので、すべての `k` について `# k ∈ κ` です。これらの要素を、合併の符号化における有限のタグとして使います。
<!--/-->

```agda
  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)

```

<!--en-->
The ordinal `κ` and the constructible stage indexed by it are different sets. We therefore package `Lset κ` as the internal set `Lκ`; this stage will form the large part of the starting set, while `κ` itself remains the cardinal into which that starting set is coded.
<!--zh-->
序数 `κ` 与以它为指标的可构造层是两个不同的集合。因此把 `Lset κ` 打包为内部集合 `Lκ`；该层将构成起始集的主要部分，而 `κ` 自身仍是起始集所要编码单射入的基数。
<!--ja-->
順序数 `κ` と、それを添字とする構成可能段階は別の集合です。そこで `Lset κ` を内部集合 `Lκ` としてまとめます。この段階が出発集合の主要部分となり、`κ` 自身は、その出発集合を符号化して入れる基数として残ります。
<!--/-->

```agda
  Lκ : S
  Lκ = LsetS (fst κ) oκ
```

<!--en-->
To place `κ` and `y` in one common stage, first form their unordered pair inside `L`. A stage containing this pair will contain both entries by transitivity, so one occurrence-stage construction suffices for the two objects.
<!--zh-->
为了把 `κ` 与 `y` 放进同一个层，先在 `L` 内形成二者的无序对。任何包含该对的传递层都会包含它的两个成员，因此只需一次出现层构造便能同时处理这两个对象。
<!--ja-->
`κ` と `y` を一つの共通の段階へ入れるため、まず `L` の内部で両者の無順序対を作ります。この対を含む推移的な段階は、その二つの要素も含むので、一度の出現段階の構成で両方を扱えます。
<!--/-->

```agda
  private
    P₀ : S
    P₀ = pairʟ κ y

```

<!--en-->
Choose an ordinal stage index `α₀` at whose stage the pair occurs. This is a convenient occurrence index supplied by constructibility; nothing here says that `α₀` is the least stage at which the pair appears.
<!--zh-->
选取序数层索引 `α₀`，使该无序对出现在其所索引的层中。这只是由可构造性给出的一个方便的出现索引；这里没有断言 `α₀` 是该对最早出现的层。
<!--ja-->
この無順序対が現れる、順序数である段階の添字 `α₀` を取ります。これは構成可能性から得られる扱いやすい添字にすぎず、`α₀` がこの対の現れる最小の段階だとは主張していません。
<!--/-->

```agda
    α₀ : V ℓ
    α₀ = stage (fst P₀) (snd P₀)

```

<!--en-->
The chosen stage index `α₀` is an ordinal. This matters because the next construction asks for a superadequate ordinal strictly above it and because ordinal transitivity will later carry `κ` from below `α₀` into `lam`.
<!--zh-->
所选层索引 `α₀` 是序数。这一点很关键：下一步要取得严格高于它的超充分序数，稍后还要用序数的传递性把 `κ` 从 `α₀` 以下继续送入 `lam`。
<!--ja-->
選んだ段階の添字 `α₀` は順序数です。次にこれより真に上にある、十分性を強めた順序数を取るため、また後で順序数の推移性によって `κ` を `α₀` の下から `lam` へ運ぶために、この事実が必要です。
<!--/-->

```agda
    oα₀ : IsOrd α₀
    oα₀ = stage-ord (fst P₀) (snd P₀)

```

<!--en-->
The cardinal `κ` belongs to `Lset α₀`. Indeed, `κ` is a member of the unordered pair, the pair belongs to `Lset α₀`, and this stage is transitive. This is stage membership, not yet the ordinal membership `κ ∈ α₀` used later.
<!--zh-->
基数 `κ` 属于 `Lset α₀`。这是因为 `κ` 是无序对的成员，该无序对属于 `Lset α₀`，而这一层是传递集。这里得到的是层隶属，尚不是后文所用的序数隶属 `κ ∈ α₀`。
<!--ja-->
基数 `κ` は `Lset α₀` に属します。`κ` は無順序対の要素であり、その対は `Lset α₀` に属し、この段階は推移的だからです。ここで得たのは段階への所属であって、後で使う順序数への所属 `κ ∈ α₀` ではありません。
<!--/-->

```agda
    κ∈Lα₀ : ⟨ fst κ ∈ˢ Lset α₀ ⟩
    κ∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst κ}
      (pairʟ-in κ y κ (inl refl)) (stage-mem (fst P₀) (snd P₀))

```

<!--en-->
The same transitivity argument places `y` in `Lset α₀` through the other member of the pair. Unlike `κ`, the set `y` is not assumed to be an ordinal, so this fact will be transported to `Lset lam` by stage monotonicity rather than converted into membership in `α₀`.
<!--zh-->
同一个传递性论证经无序对的另一成员把 `y` 放进 `Lset α₀`。与 `κ` 不同，并未假设 `y` 是序数，所以后文会用层的单调性把这一事实搬到 `Lset lam`，而不会把它转换成 `y ∈ α₀`。
<!--ja-->
同じ推移性の議論により、無順序対のもう一つの要素を通して `y` も `Lset α₀` に入ります。`κ` と違い、`y` は順序数とは仮定されていません。したがって後では、この事実を段階の単調性によって `Lset lam` へ運び、`y ∈ α₀` へ変換することはしません。
<!--/-->

```agda
    y∈Lα₀ : ⟨ fst y ∈ˢ Lset α₀ ⟩
    y∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst y}
      (pairʟ-in κ y y (inr refl)) (stage-mem (fst P₀) (snd P₀))

```

<!--en-->
Now choose explicitly a superadequate ordinal `lam` with `α₀ ∈ lam`. This strict extension provides enough closure for the later hull and condensation arguments. Although `lam` itself is explicit, the adequate subindices promised by its superadequacy remain under propositional truncation.
<!--zh-->
现在显式选取超充分序数 `lam`，满足 `α₀ ∈ lam`。这个严格扩张提供后续壳与凝聚论证所需的闭包性质。`lam` 自身虽是显式数据，但其超充分性所保证的局部充分指标仍处于命题截断下。
<!--ja-->
ここで `α₀ ∈ lam` を満たす、十分性を強めた順序数 `lam` を明示的に取ります。この真の拡張が、後の包と凝縮の議論に必要な閉性を与えます。`lam` 自身は明示的なデータですが、その強められた十分性が保証する局所的な十分な添字は、命題的切り詰めの内側にとどまります。
<!--/-->

```agda
    sa = superadequate-above α₀ oα₀

```

<!--en-->
Write this high ordinal as `lam`, corresponding to `λ` in the exposition. Its particular construction will play no further role; the proof uses its ordinality, successor closure, superadequacy, and its position above `α₀`.
<!--zh-->
把这个高序数在代码中记作 `lam`，正文中记作 `λ`。它的具体构造后文不再起作用；证明只使用其序数性、后继闭包、超充分性以及它高于 `α₀` 这一事实。
<!--ja-->
この高い順序数を、コードでは `lam`、本文では `λ` と書きます。その具体的な構成は以後使わず、順序数性、後続に関する閉性、強められた十分性、および `α₀` より上にあるという事実だけを使います。
<!--/-->

```agda
  opaque
    lam : V ℓ
    lam = sa .fst

```

<!--en-->
The first retained fact is that `lam` is an ordinal. Consequently it is transitive, which will allow ordinal memberships below `lam` to be carried farther upward.
<!--zh-->
首先保留的事实是 `lam` 为序数。因此它是传递集，这使得 `lam` 以下的序数隶属可以继续向上传递。
<!--ja-->
最初に保つ事実は、`lam` が順序数であることです。したがって `lam` は推移的であり、`lam` より下の順序数の所属をさらに上へ運べます。
<!--/-->

```agda
    ordλ : IsOrd lam
    ordλ = sa .snd .fst

```

<!--en-->
The second retained fact is closure under ordinal successor: whenever `d ∈ lam`, also `sucV d ∈ lam`. This closure is one of the structural hypotheses under which the finite Skolem construction remains inside the stage indexed by `lam`.
<!--zh-->
其次保留对序数后继的闭包：只要 `d ∈ lam`，便有 `sucV d ∈ lam`。这项闭包是保证有限 Skolem 构造留在 `lam` 所索引层内的结构前提之一。
<!--ja-->
次に保つのは、順序数の後続に関する閉性です。`d ∈ lam` ならば `sucV d ∈ lam` でもあります。この閉性は、有限 Skolem 構成が `lam` を添字とする段階の内部にとどまるための構造的仮定の一つです。
<!--/-->

```agda
    succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
    succλ = sa .snd .snd .snd .fst .snd .fst

```

<!--en-->
Superadequacy says that for each `d ∈ lam` there merely exists an adequate ordinal `γ` with `d ∈ γ ∈ lam`. It supplies local adequate room below `lam` without choosing a least `γ` or a family of such choices.
<!--zh-->
超充分性表示：对每个 `d ∈ lam`，都仅仅存在充分序数 `γ`，满足 `d ∈ γ ∈ lam`。它在 `lam` 以下提供局部的充分空间，却不选取最小的 `γ`，也不选取这样一族 `γ`。
<!--ja-->
強められた十分性とは、各 `d ∈ lam` に対して、`d ∈ γ ∈ lam` を満たす十分な順序数 `γ` が単に存在することです。これは `lam` より下に局所的な十分な余地を与えますが、最小の `γ` も、そのような `γ` の族も選びません。
<!--/-->

```agda
    sup : Superadequate lam
    sup = sa .snd .snd .snd .snd

```

<!--en-->
The cardinal `κ` belongs to the ordinal index `lam`. Because both `κ` and `α₀` are ordinals, `κ ∈ Lset α₀` first yields `κ ∈ α₀`. The relation `α₀ ∈ lam` and the transitivity of the ordinal `lam` then give `κ ∈ lam`. This conclusion concerns the index `lam`, rather than the stage `Lset lam`.
<!--zh-->
基数 `κ` 属于序数索引 `lam`。由于 `κ` 与 `α₀` 都是序数，先由 `κ ∈ Lset α₀` 得到 `κ ∈ α₀`；再结合 `α₀ ∈ lam` 与序数 `lam` 的传递性，得到 `κ ∈ lam`。这个结论说的是属于索引 `lam`，而不是属于层 `Lset lam`。
<!--ja-->
基数 `κ` は順序数の添字 `lam` に属します。`κ` と `α₀` はともに順序数なので、まず `κ ∈ Lset α₀` から `κ ∈ α₀` が得られます。さらに `α₀ ∈ lam` と順序数 `lam` の推移性から、`κ ∈ lam` が従います。この結論は添字 `lam` への所属であり、段階 `Lset lam` への所属ではありません。
<!--/-->

```agda
    κ∈λ : ⟨ fst κ ∈ˢ lam ⟩
    κ∈λ = ordλ .fst (ord∈Lset→∈ α₀ oα₀ (fst κ) oκ κ∈Lα₀) (sa .snd .snd .fst)

```

<!--en-->
For `y`, the required conclusion is instead membership in the stage `Lset lam`. Since `α₀ ∈ lam`, monotonicity gives `Lset α₀ ⊆ Lset lam`; applying it to the earlier fact `y ∈ Lset α₀` yields `y ∈ Lset lam`. No ordinality of `y` is needed.
<!--zh-->
对 `y`，所需结论则是它属于层 `Lset lam`。由 `α₀ ∈ lam`，层的单调性给出 `Lset α₀ ⊆ Lset lam`；把它用于先前的 `y ∈ Lset α₀`，便得到 `y ∈ Lset lam`。这里不需要假设 `y` 是序数。
<!--ja-->
一方、`y` について必要なのは、段階 `Lset lam` への所属です。`α₀ ∈ lam` から、段階の単調性により `Lset α₀ ⊆ Lset lam` が得られます。これを先の `y ∈ Lset α₀` に適用すると、`y ∈ Lset lam` となります。`y` が順序数であるという仮定は必要ありません。
<!--/-->

```agda
    y∈Lλ : ⟨ fst y ∈ˢ Lset lam ⟩
    y∈Lλ = Lset-mono {α = lam} {β = α₀} (sa .snd .snd .fst) y∈Lα₀
```

<!--en-->
Every ambient member of `y` lies in `Lset κ`. Indeed, the subset hypothesis sends `z ∈ y` to `z ∈ κ`; since `κ` is an ordinal, such a `z` is itself an ordinal, lies in its successor stage, and hence lies in `Lset κ` by cumulativity. Thus `y ⊆ κ` supplies the stage inclusion needed to make the starting set transitive.
<!--zh-->
`y` 的每个外围成员都属于 `Lset κ`。子集前提先把 `z ∈ y` 送到 `z ∈ κ`；由于 `κ` 是序数，这样的 `z` 本身也是序数，属于自己的后继层，再由累积性得到 `z ∈ Lset κ`。因此，`y ⊆ κ` 给出了使起始集成为传递集所需的层包含关系。
<!--ja-->
`y` の周囲の各要素は `Lset κ` に属します。部分集合の仮定により `z ∈ y` から `z ∈ κ` が得られます。`κ` は順序数なので、このような `z` も順序数であり、自身の後続段階に属し、累積性によって `z ∈ Lset κ` となります。したがって `y ⊆ κ` から、出発集合を推移的にするために必要な段階への包含が得られます。
<!--/-->

```agda
  y⊆Lκ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  y⊆Lκ z hz = ord⊆Lset (fst κ) oκ z (y⊆κ z hz)

```

<!--en-->
Form the starting set `X = Lset κ ∪ {y}` inside `Lset lam`. It contains `y` and is transitive: elements inherited from `Lset κ` stay in that transitive stage, while an element of `y` lies in `κ` by hypothesis and hence in `Lset κ`. This transitivity is precisely what will make the collapse fix `y` later.
<!--zh-->
在 `Lset lam` 内形成起始集 `X = Lset κ ∪ {y}`。它包含 `y`，并且是传递集：来自 `Lset κ` 的元素仍留在这个传递层中；来自 `y` 的元素则由假设属于 `κ`，因而属于 `Lset κ`。这项传递性正是后文使塌缩固定 `y` 的原因。
<!--ja-->
`Lset lam` の内部で、出発集合 `X = Lset κ ∪ {y}` を作ります。これは `y` を含み、しかも推移的です。`Lset κ` に由来する要素は、その推移的な段階にとどまります。また `y` の要素は、仮定により `κ` に属し、したがって `Lset κ` に属します。この推移性こそが、後で崩壊に `y` を固定させます。
<!--/-->

```agda
  module UK = UnionKit (fst κ) lam (fst y) oκ ordλ κ∈λ y⊆Lκ y∈Lλ κ∉ω
    using ( X; X⊆Lλ; ∅∈λ; Lα∈X; x∈X; X-mem; sgl≡; Xtr )

```

<!--en-->
From now on, `X` denotes this transitive enlargement of `Lset κ`. The two features to retain are complementary: `y ∈ X` ensures that the hull contains the set we want to locate, and transitivity ensures that the collapse does not alter it.
<!--zh-->
下文用 `X` 表示这个由 `Lset κ` 扩张而成的传递集。需要保留的两项性质彼此配合：`y ∈ X` 保证壳包含待定位的集合，传递性则保证塌缩不会改变它。
<!--ja-->
以下では、この `Lset κ` の推移的な拡張を `X` と書きます。覚えておくべき二つの性質は互いに補い合います。`y ∈ X` によって、位置を定めたい集合が包に入り、推移性によって、崩壊がその集合を変えません。
<!--/-->

```agda
  X : V ℓ
  X = UK.X
```

<!--en-->
For counting, construct the singleton `{y}` internally together with its injection into `κ`, using the tag `0 ∈ κ`, and take its internal union with `Lκ`. This produces a coded presentation of the same set `Lset κ ∪ {y}` whose two pieces already carry the injections needed for the tagged-union argument.
<!--zh-->
为了计数，在内部构造单点集 `{y}` 及其到 `κ` 的编码单射，其中使用标签 `0 ∈ κ`，再把它与 `Lκ` 作内部并。这样得到同一集合 `Lset κ ∪ {y}` 的编码呈现，其两个部分已经分别带有带标签并集论证所需的单射。
<!--ja-->
数え上げのため、タグ `0 ∈ κ` を用いて、単元集合 `{y}` とその `κ` への符号化された単射を内部で構成し、それを `Lκ` と内部で合併します。こうして同じ集合 `Lset κ ∪ {y}` の符号化された提示が得られ、その二つの部分には、タグ付き合併の議論に必要な単射がすでに備わっています。
<!--/-->

```agda
  module Pt = Point κ (num∈κ 0) y using ( Y; Y-out; Y-in; injL )
  module U = Union2 Lκ Pt.Y using ( D; out; in₁; in₂ )

```

<!--en-->
Call this internally constructed union `Xʟ`. It represents the same mathematical union as `X`, but its construction carries the internal coding data needed to prove an injection into `κ`.
<!--zh-->
把这个内部构造的并记作 `Xʟ`。它与 `X` 表示同一个数学并集，但其构造附带了证明它编码单射入 `κ` 所需的内部数据。
<!--ja-->
この内部で構成した合併を `Xʟ` と書きます。これは `X` と同じ数学的な合併を表しますが、その構成には、`κ` への符号化された単射を示すために必要な内部データが伴っています。
<!--/-->

```agda
  Xʟ : S
  Xʟ = U.D

```

<!--en-->
To identify `Xʟ` with `X`, compare their members in both directions. In the forward direction, membership in the internally coded union yields, under propositional truncation, either a member of `Lset κ` or a member of the coded singleton; both cases imply membership in `X`. The elimination is valid because membership in `X` is a proposition.
<!--zh-->
为了把 `Xʟ` 与 `X` 识别起来，双向比较二者的成员。正向中，属于内部编码并意味着在命题截断下分成两种情形：属于 `Lset κ`，或属于编码单点集；两种情形都推出属于 `X`。由于属于 `X` 是命题，这次消去是合法的。
<!--ja-->
`Xʟ` と `X` を同一視するため、両者の要素を二方向に比較します。順方向では、内部で符号化された合併への所属から、命題的切り詰めのもとで、`Lset κ` の要素である場合と、符号化された単元集合の要素である場合に分かれます。どちらからも `X` への所属が従います。`X` への所属は命題なので、この除去は正当です。
<!--/-->

```agda
  Xʟ-eq : fst Xʟ ≡ X
  Xʟ-eq = extensionalV {a = fst Xʟ} {b = X} (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : V ℓ) → ⟨ z ∈ˢ fst Xʟ ⟩ → ⟨ z ∈ˢ X ⟩
    fwd z h = PT.rec (snd (z ∈ˢ X)) go (U.out zS h)
```

<!--en-->
In the stage case, the left inclusion places the member in `X`. The temporary packaging of `z` as constructible is justified by transitivity of `L`: since `z` belongs to the constructible set `Xʟ`, it is constructible as well.
<!--zh-->
在层这一分支中，左侧包含把该成员放入 `X`。把 `z` 暂时打包为可构造集合是由 `L` 的传递性保证的：既然 `z` 属于可构造集合 `Xʟ`，它自身也可构造。
<!--ja-->
段階の側の場合、左の包含によって、その要素は `X` に入ります。`z` を一時的に構成可能集合としてまとめられるのは、`L` の推移性によります。`z` は構成可能集合 `Xʟ` の要素なので、`z` 自身も構成可能です。
<!--/-->

```agda
      where
      zS : S
      zS = z , isL-trans {x = fst Xʟ} {y = z} h (snd Xʟ)
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ fst Pt.Y ⟩ → ⟨ z ∈ˢ X ⟩
      go (inl hz) = UK.Lα∈X z hz
```

<!--en-->
In the singleton case, the coded member is equal to `y`, already known to belong to `X`. Conversely, membership in `X` splits, again only under propositional truncation, into the `Lset κ` side and the singleton side; the target membership in `Xʟ` is a proposition, so this second elimination is equally legitimate.
<!--zh-->
在单点分支中，编码成员等于已知属于 `X` 的 `y`。反向中，属于 `X` 同样只在命题截断下拆分为 `Lset κ` 一侧与单点一侧；目标「属于 `Xʟ`」是命题，因此第二次消去同样合法。
<!--ja-->
単元集合の側では、符号化された要素は、すでに `X` に属すると分かっている `y` に等しくなります。逆方向では、`X` への所属が、やはり命題的切り詰めのもとで `Lset κ` の側と単元集合の側に分かれます。行き先である `Xʟ` への所属は命題なので、この二度目の除去も正当です。
<!--/-->

```agda
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ X ⟩) (sym (Pt.Y-out zS hz)) UK.x∈X
    bwd : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
    bwd z h = PT.rec (snd (z ∈ˢ fst Xʟ)) go (UK.X-mem z h)
      where
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ ⁅ fst y ⁆s ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
```

<!--en-->
The reverse cases enter the two summands of `Xʟ`. A member of `Lset κ` enters on the left, with constructibility inherited from that stage; a member of `{y}` is first identified with `y` and then enters through the coded singleton. Thus extensionality proves `fst Xʟ ≡ X` without retaining either truncated case split.
<!--zh-->
反向的两个分支分别进入 `Xʟ` 的两个并项。`Lset κ` 的成员从左侧进入，其可构造性由该层继承；`{y}` 的成员先与 `y` 识别，再从编码单点集一侧进入。因此外延性给出 `fst Xʟ ≡ X`，而不保留任何一次截断的分支选择。
<!--ja-->
逆方向の二つの場合は、`Xʟ` の二つの成分へそれぞれ入ります。`Lset κ` の要素は、その段階から構成可能性を受け継いで左側に入り、`{y}` の要素は、まず `y` と同一視されてから、符号化された単元集合の側に入ります。こうして外延性により `fst Xʟ ≡ X` が得られ、切り詰められた場合分けはどちらも保持されません。
<!--/-->

```agda
      go (inl hz) = U.in₁ (z , isL-trans {x = Lset (fst κ)} {y = z} hz (snd Lκ)) hz
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ fst Xʟ ⟩) (sym (UK.sgl≡ z hz)) (U.in₂ y Pt.Y-in)

```

<!--en-->
The starting set is constructible, since the internal copy is constructible and the two copies have equal underlying sets.
<!--zh-->
起始集合可构造，因为内部副本可构造且两副本底层集合相等。
<!--ja-->
始集合は構成可能です。内部の写しが構成可能で、二つの写しの底の集合が等しいからです。
<!--/-->

```agda
  X-isL : ⟨ isL X ⟩
  X-isL = subst (λ w → ⟨ isL w ⟩) Xʟ-eq (snd Xʟ)

```

<!--en-->
Package `X` together with this constructibility proof as `XS : S`. Its underlying ambient set is still exactly `X`; the packaging merely supplies the internal domain required by `InjL`.
<!--zh-->
把 `X` 连同这份可构造性证明打包为 `XS : S`。它的底层外围集合仍恰好是 `X`；这项打包只提供 `InjL` 所要求的内部定义域。
<!--ja-->
`X` とこの構成可能性の証明を組にして、`XS : S` とします。台となる周囲の集合は依然としてちょうど `X` であり、この包装は `InjL` が要求する内部の定義域を与えるだけです。
<!--/-->

```agda
  XS : S
  XS = X , X-isL
```

<!--en-->
The infinite-cardinal square law gives the propositionally truncated existence of a coded injection `κ × κ ↪ κ`. Its hypotheses are exactly the facts fixed at the start: `κ` is an ordinal internal cardinal and is not a member of `ω`. No bijection or chosen injection graph is produced.
<!--zh-->
无穷基数平方律给出编码单射 `κ × κ ↪ κ` 的命题截断存在。它所需的前提正是开头固定的事实：`κ` 是序数、内部基数且不属于 `ω`。这里既不产生双射，也不产生一张选定的单射图。
<!--ja-->
無限基数の平方法則により、符号化された単射 `κ × κ ↪ κ` の存在が命題的切り詰めのもとで得られます。その仮定は冒頭で固定した事実、すなわち `κ` が順序数であり内部の基数であり、`ω` の要素ではないことに一致します。全単射も、特定の単射のグラフも得られません。
<!--/-->

```agda
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

```

<!--en-->
The two component injections feed the tagged-union construction, giving a coded injection `Xʟ ↪ κ × κ`: tags `#0` and `#1` distinguish the stage part from the singleton part. Composing with the square-law injection gives `Xʟ ↪ κ`, and transport along `fst Xʟ ≡ X` changes the domain to the constructible package `XS`. The result is the required coded injection `X ↪ κ`, still under propositional truncation.
<!--zh-->
两条分量单射输入带标签并的构造，得到编码单射 `Xʟ ↪ κ × κ`：标签 `#0` 与 `#1` 区分层部分和单点集部分。再与平方律给出的单射复合，得到 `Xʟ ↪ κ`；最后沿 `fst Xʟ ≡ X` 搬运定义域，把它换成可构造包装 `XS`。所得正是需要的编码单射 `X ↪ κ`，并且仍处于命题截断下。
<!--ja-->
二つの成分の単射をタグ付き合併の構成に入れると、符号化された単射 `Xʟ ↪ κ × κ` が得られます。タグ `#0` と `#1` が、段階の側と単元集合の側を区別します。これを平方法則の単射と合成して `Xʟ ↪ κ` を得た後、`fst Xʟ ≡ X` に沿って定義域を構成可能な包装 `XS` へ移します。こうして必要な符号化された単射 `X ↪ κ` が、引き続き命題的切り詰めのもとで得られます。
<!--/-->

```agda
  base : InjL XS κ
  base = move Xʟ XS κ κ Xʟ-eq refl
    (injl-trans Xʟ (prodL κ) κ
      (tag-union κ (num∈κ 0) (num∈κ 1) Lκ Pt.Y (stage-counted κ Lκ oκ κ∉ω refl) Pt.injL)
      pairκ)
```

<!--en-->
Let `M` be the Skolem hull generated by `X` inside `Lset lam`. The Tarski-Vaught theorem for this hull shows that `M` is elementary in the sense required by condensation. The whole transitive set `X` is the starting set, so this is the same hull that contains `y` and whose collapse will later fix `y`.
<!--zh-->
令 `M` 为 `X` 在 `Lset lam` 内生成的 Skolem 壳。适用于这个壳的 Tarski-Vaught 定理表明，`M` 具有凝聚所需的初等性。整个传递集 `X` 就是起始集，因此这正是包含 `y`、且其塌缩稍后将固定 `y` 的同一个壳。
<!--ja-->
`M` を、`Lset lam` の内部で `X` が生成する Skolem 包とします。この包に対する Tarski-Vaught の定理により、`M` は凝縮に必要な意味で初等的です。推移的集合 `X` 全体が出発集合なので、これは `y` を含み、後でその崩壊が `y` を固定する、同じ一つの包です。
<!--/-->

```agda
  elem = HullElemDown.elem lam ordλ X UK.X⊆Lλ UK.∅∈λ
```

<!--en-->
The hull-counting theorem propagates `X ↪ κ` through the finite stages of Skolem closure and then through their union. It yields the existence, under propositional truncation, of a coded injection `M ↪ κ`. The hull is therefore both elementary enough for condensation and small enough to remain controlled by `κ`.
<!--zh-->
壳计数定理把 `X ↪ κ` 依次传过 Skolem 闭包的有限阶段及这些阶段的并，得到编码单射 `M ↪ κ` 在命题截断下的存在性。于是，这个壳既具有应用凝聚所需的初等性，其大小又仍受 `κ` 控制。
<!--ja-->
包の数え上げ定理は、`X ↪ κ` を Skolem 閉包の有限段階へ順に伝え、さらにそれらの合併へ伝えます。その結果、符号化された単射 `M ↪ κ` の存在が命題的切り詰めのもとで得られます。したがって、この包は凝縮を適用するのに必要な初等性をもち、その大きさも引き続き `κ` によって制御されます。
<!--/-->

```agda
  hull↪κ = Count.hull↪κ lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL κ oκ cκ κ∉ω base
```

<!--en-->
Condensation supplies an explicit ordinal `β` and identifies the collapse image of `M` with `Lset β`. It also packages `Lset β` and `M` as constructible sets and gives the propositionally truncated coded injection `Lset β ↪ M` induced by the inverse collapse. Here `β` is the stage index, while `Lset β` is the stage it indexes.
<!--zh-->
凝聚给出显式序数 `β`，并把 `M` 的塌缩像识别为 `Lset β`。它还把 `Lset β` 与 `M` 打包为可构造集合，并通过逆塌缩给出编码单射 `Lset β ↪ M` 的命题截断存在。这里 `β` 是层索引，`Lset β` 才是它所索引的层。
<!--ja-->
凝縮は明示的な順序数 `β` を与え、`M` の崩壊像を `Lset β` と同一視します。さらに `Lset β` と `M` を構成可能集合としてまとめ、逆崩壊から得られる符号化された単射 `Lset β ↪ M` の存在を命題的切り詰めのもとで与えます。ここで `β` は段階の添字であり、`Lset β` がそれによって添字づけられる段階です。
<!--/-->

```agda
  module St = Site lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL
    using ( β; oβ; ext; Lβ; βL; hullL; Lβ↪M )
```

<!--en-->
We now use three aspects of this single hull construction: the hull `M`, the inclusion `X ⊆ M`, and the collapse map `π` with image `πX`. The associated fixed-point theorem applies to transitive subsets of `M`. These facts will first show that `y` is unchanged by the collapse and then place that same `y` in the stage identified by condensation.
<!--zh-->
下面使用同一个壳构造的三个方面：壳 `M`、包含关系 `X ⊆ M`，以及像为 `πX` 的塌缩映射 `π`。相应的不动点定理适用于 `M` 的传递子集。这些事实将先证明塌缩不改变 `y`，再把同一个 `y` 放入凝聚所识别出的层中。
<!--ja-->
ここからは、一つの包の構成について三つの側面を使います。包 `M`、包含 `X ⊆ M`、そして像を `πX` とする崩壊写像 `π` です。対応する不動点定理は、`M` の推移的部分集合に適用できます。これらの事実から、まず崩壊が `y` を変えないことを示し、次に同じ `y` を凝縮によって同一視された段階へ入れます。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ
    using ( πX; π; fixes; πX-intro )
```

<!--en-->
The set `y` belongs to the Skolem hull `M`: it was placed in the starting set `X`, and every member of `X` lies in the hull generated from `X`.
<!--zh-->
集合 `y` 属于 Skolem 壳 `M`：它已被放入起点集 `X`，而 `X` 的每个成员都属于由 `X` 生成的壳。
<!--ja-->
集合 `y` は Skolem 包 `M` に属します。`y` は始点集合 `X` に入っており、`X` の各要素は `X` から生成された包に属するからです。
<!--/-->

```agda
  y∈M : ⟨ fst y ∈ˢ HS.M ⟩
  y∈M = HSH.X⊆M (fst y) UK.x∈X

```

<!--en-->
The collapse fixes `y`: because the starting set `X` is transitive and contained in the hull, the collapse map acts as the identity on every member of `X`, and `y` is one of them.
<!--zh-->
塌缩固定 `y`：因为起点集 `X` 传递且包含于壳中，塌缩映射在 `X` 的每个成员上恒等，而 `y` 即为其中之一。
<!--ja-->
崩壊は `y` を固定します。始点の集合 `X` が推移的で包の中にあるため、崩壊の写像は `X` のすべての要素の上で恒等であり、`y` もその一つです。
<!--/-->

```agda
  πy : HSC.π (fst y) ≡ fst y
  πy = HSC.fixes X
    (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst (HSH.X⊆M a (∈∈ₛ {a = a} {b = X} .snd a∈ₛX)))
    UK.Xtr (fst y) UK.x∈X

```

<!--en-->
The collapse image contains `π(y)`, since `y` belongs to the hull. Condensation identifies that image with the constructible stage `Lset β`, and the fixed-point equation `π(y) = y` then gives `y ∈ Lset β`. The point is that the collapse has not replaced `y` by another set: it has located the original `y` inside a controlled constructible stage.
<!--zh-->
由于 `y` 属于壳，塌缩像包含 `π(y)`。凝聚把这个像认同为可构造层 `Lset β`，再由不动点等式 `π(y) = y` 得到 `y ∈ Lset β`。关键在于，塌缩没有用另一个集合替换 `y`，而是把原来的 `y` 定位在一个受控的可构造层中。
<!--ja-->
`y` は包に属するので、崩壊像は `π(y)` を含みます。凝縮によってこの像は構成可能段階 `Lset β` と同一視され、不動点の等式 `π(y) = y` から `y ∈ Lset β` が従います。ここで崩壊は `y` を別の集合に置き換えたのではなく、もとの `y` を制御された構成可能段階の中に位置づけています。
<!--/-->

```agda
  y∈Lβ : ⟨ fst y ∈ˢ Lset St.β ⟩
  y∈Lβ = subst (λ w → ⟨ w ∈ˢ Lset St.β ⟩) πy
    (subst (λ w → ⟨ HSC.π (fst y) ∈ˢ w ⟩) St.ext (HSC.πX-intro (fst y) y∈M))
```

<!--en-->
The ordinal `β` injects into `κ` by a chain of three coded injections: the inclusion from `β` into the level `Lset β` by ordinal membership, the restricted inverse collapse from `Lset β` into the hull `M`, and the hull counting from `M` into `κ`. The chain gives a coded injection, not a bare ordinal comparison.
<!--zh-->
序数 `β` 经三条编码单射的链注入 `κ`：由序数隶属从 `β` 到层 `Lset β` 的包含、由受限逆塌缩从 `Lset β` 到壳 `M` 的单射、以及由壳计数从 `M` 到 `κ` 的单射。这条链给出的是编码单射，而非裸序数比较。
<!--ja-->
順序数 `β` は、三つの符号化された単射の鎖によって `κ` へ単射します。順序数の所属による `β` から `Lset β` への包含、制限された逆崩壊による `Lset β` から包 `M` への単射、そして包の計数による `M` から `κ` への単射です。この鎖が与えるのは符号化された単射であり、裸の順序数の比較ではありません。
<!--/-->

```agda
  β↪κ : InjL St.βL κ
  β↪κ = injl-trans St.βL St.Lβ κ
    (inclusion-coded St.βL St.Lβ (λ z hz → ord⊆Lset St.β St.oβ z hz))
    (injl-trans St.Lβ St.hullL κ St.Lβ↪M hull↪κ)

```

<!--en-->
The local witness now packages the constructible ordinal `β`, its ordinality, the fact that `y` belongs to the stage `Lset β`, and the coded injection `β ↪ κ`. Here `β` is the stage index being returned, whereas `Lset β` is the constructible stage in which `y` has been located.
<!--zh-->
局部见证现把可构造序数 `β`、它的序数性、`y` 属于层 `Lset β` 的事实，以及编码单射 `β ↪ κ` 打包在一起。这里返回的是层指标 `β`，而 `Lset β` 是已经容纳 `y` 的可构造层；二者不可混同。
<!--ja-->
局所的な証人は、構成可能順序数 `β`、その順序数性、`y` が段階 `Lset β` に属するという事実、そして符号化された単射 `β ↪ κ` をまとめます。ここで返されるのは段階の添字 `β` であり、`Lset β` は `y` が位置づけられた構成可能段階です。この二つは区別されます。
<!--/-->

```agda
  result : Σ[ b ∈ S ] (IsOrd (fst b) × ⟨ fst y ∈ˢ Lset (fst b) ⟩ × InjL b κ)
  result = St.βL , St.oβ , y∈Lβ , β↪κ
```

<!--en-->
Finally, `∣_∣₁` places the entire local witness under propositional truncation. The final theorem therefore retains only that some constructible ordinal `β` satisfies `y ∈ Lset β` and admits a coded injection `β ↪ κ`. It provides neither a least nor a canonical `β`, and it makes no uniform choice of witnesses as `y` varies.
<!--zh-->
最后，`∣_∣₁` 把整个局部见证置于命题截断下。因此，最终定理只保留如下存在性：某个可构造序数 `β` 满足 `y ∈ Lset β`，并存在编码单射 `β ↪ κ`。它既不提供最小或规范的 `β`，也不随 `y` 统一选取见证。
<!--ja-->
最後に、`∣_∣₁` は局所的な証人全体を命題的切り詰めのもとに置きます。したがって、最後の定理が保つのは、ある構成可能順序数 `β` が `y ∈ Lset β` を満たし、符号化された単射 `β ↪ κ` が存在するということだけです。最小または標準的な `β` も、`y` ごとの証人の一様な選択も与えません。
<!--/-->

```agda
internal-bounded-subset : InternalBoundedSubset
internal-bounded-subset κ oκ cκ κ∉ω y y⊆κ =
  ∣ At.result κ oκ cκ κ∉ω y y⊆κ ∣₁
```
