<!--en-->
# Injecting an infinite constructible stage into its index

This chapter proves the stage estimate used in GCH: if `δ` is a non-finite constructible ordinal, then `Lset δ` admits an internal coded injection into `δ`. The conclusion `InjL` is the propositional truncation of the type of constructible graphs satisfying the injection conditions. Thus it asserts that such a graph exists, without retaining a chosen graph; it asserts neither a host-level function nor a bijection, and it does not assume that `δ` is itself an internal cardinal.
<!--zh-->
# 把无穷可构造层单射到其指标

本章证明 GCH 所用的层估计：若 `δ` 是非有限的可构造序数，则 `Lset δ` 有一条到 `δ` 的内部编码单射。结论 `InjL` 是「满足单射条件的可构造图」这一类型的命题截断。因此，它只断言这样的图存在，而不保留某个选定的图；它既不声称给出宿主层函数，也不声称双射，并且不假设 `δ` 本身是内部基数。
<!--ja-->
# 無限構成可能段階をその添字へ単射する

この章では GCH に用いる段階評価を証明する。`δ` が有限でない構成可能順序数なら、`Lset δ` から `δ` への内部的に符号化された単射が存在する。結論 `InjL` は、単射の条件を満たす構成可能なグラフの型を命題的切り詰めにかけたものである。したがって、そのようなグラフの存在だけを主張し、特定のグラフは保持しない。ホスト側の関数も全単射も主張せず、`δ` 自身が内部基数であることも仮定しない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
The proof repeatedly separates existence from choice. Classical reasoning supplies suitable stages and cardinal representatives, while every exported injection remains under propositional truncation. Local witnesses may therefore be used inside propositional arguments without turning them into canonical global data.
<!--zh-->
本章反复区分存在与选择。经典推理提供合适的层和基数代表，而每条对外给出的单射始终处于命题截断之下。因此，局部见证可以在命题性论证内部使用，却不会变成典范的全局数据。
<!--ja-->
この証明では、存在と選択を一貫して区別する。古典的推論は適切な段階と基数代表を与えるが、外部に示される単射はすべて命題的切り詰めの内側にとどまる。したがって、局所的な証人を命題の証明の中で使っても、それが標準的な大域データになることはない。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The argument is uniform in the universe level and uses only the displayed instance `lem : LEM (ℓ-suc ℓ)` of excluded middle. In particular, the later passage to an internal cardinal representative does not add a hidden assumption that the original ordinal `δ` is a cardinal.
<!--zh-->
论证对宇宙层级一致，只使用明示的排中律实例 `lem : LEM (ℓ-suc ℓ)`。特别地，后文转到内部基数代表时，并未暗中增加「原序数 `δ` 是基数」这一假设。
<!--ja-->
議論は宇宙レベルについて一様であり、明示された排中律の実例 `lem : LEM (ℓ-suc ℓ)` だけを使う。とくに、後で内部の基数代表へ移ることによって、もとの順序数 `δ` が基数であるという仮定が暗黙に加わることはない。
<!--/-->

```agda
module L.GCH.StageInjection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
To turn the inverse collapse into an injection inside `L`, its graph must be expressed in the first-order language of the constructible structure. Only variables, constants, membership, and conjunction are needed. Formula renaming will exchange the two argument positions while preserving satisfaction, and the ambient cumulative hierarchy supplies the sets on which the collapse is computed.
<!--zh-->
要把逆塌缩变成 `L` 内部的单射，必须用可构造结构的一阶语言表达它的图。这里只需变元、常元、隶属与合取。公式改名会交换两个实参位置而保持满足关系，外围累积层级则提供计算塌缩所用的集合。
<!--ja-->
逆崩壊を `L` の内部の単射にするには、そのグラフを構成可能構造の一階言語で表さなければならない。必要なのは変数、定数、所属、連言だけである。論理式の名前替えによって二つの引数位置を交換しても充足関係が保たれ、周囲の累積階層が崩壊を計算する集合を与える。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The collapse will be injective because the hull carries the required extensionality. Later, `self∈sucV` places `δ` in its set-theoretic successor `δ+1`, while the constructible-stage lemmas provide transitivity, monotonicity, and the passage between a stage and its layers. Ordinal successors are kept distinct from successor stages throughout this argument.
<!--zh-->
壳具备所需的外延性，因此塌缩在壳上单射。后文中，`self∈sucV` 把 `δ` 放入其集合论后继 `δ+1`；可构造层引理则提供传递性、单调性以及层与其分层之间的联系。这个论证始终区分序数后继与可构造后继层。
<!--ja-->
包が必要な外延性を備えるため、崩壊は包の上で単射になる。後で `self∈sucV` は `δ` を集合論的な後続 `δ+1` に入れ、構成可能段階の補題は推移性、単調性、段階とその層の間の移行を与える。この議論では、順序数の後続と構成可能な後続段階を区別する。
<!--/-->

```agda
open import V.Collapse {ℓ} using ( isExt )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( #∈ω; suc-ord )
```

<!--en-->
Two complementary stage facts will be used. A constructible stage can be packaged as an element of `L`, and if an ordinal `x` belongs to the stage `Lset α`, then rank comparison yields `x ∈ α`. The target `InjL` records the mere existence of an internal coded injection, while `IsCardinalL` will apply only to the cardinal representative introduced later.
<!--zh-->
后文会使用两条互补的层事实。一个可构造层可以打包为 `L` 的元素；若序数 `x` 属于层 `Lset α`，则秩比较给出 `x ∈ α`。目标 `InjL` 记录内部编码单射仅仅存在，而 `IsCardinalL` 只会用于稍后引入的基数代表。
<!--ja-->
後では、段階に関する二つの相補的な事実を用いる。構成可能段階は `L` の要素としてまとめられ、順序数 `x` が段階 `Lset α` に属するなら、階数の比較から `x ∈ α` が従う。目標 `InjL` は内部的に符号化された単射の単なる存在を記録し、`IsCardinalL` は後で導入する基数代表にだけ適用される。
<!--/-->

```agda
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL )
```

<!--en-->
The desired estimate has the interface `StageCountedCoded`. Its proof first replaces the arbitrary infinite ordinal `δ` by an internal cardinal representative `μ`, counts a suitable Skolem hull into `μ`, and then composes coded injections. To make the inverse collapse participate in this chain, it will be presented as a definable map whose graph is a set of `L`.
<!--zh-->
所需估计由接口 `StageCountedCoded` 表述。证明先以内部基数代表 `μ` 表示任意无穷序数 `δ` 的基数，再把合适的 Skolem 壳计数到 `μ` 中，最后复合编码单射。为使逆塌缩能够加入这条链，证明会把它表示为可定义映射，其图是 `L` 的元素。
<!--ja-->
求める評価は `StageCountedCoded` という型で表される。証明では、まず任意の無限順序数 `δ` を内部の基数代表 `μ` で表し、適切な Skolem 包を `μ` へ数え上げ、最後に符号化された単射を合成する。逆崩壊もこの鎖に組み込めるよう、そのグラフが `L` の要素である定義可能写像として表す。
<!--/-->

```agda
open import L.GCH.Assembly {ℓ} lem using ( StageCountedCoded )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.GCH.CardinalRepresentative {ℓ} lem using ( cardOf )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.SkolemHull {ℓ} lem
```

<!--en-->
The global comparison will combine three ingredients. Condensation turns a hull into a stage `Lset β`; the shift for non-finite ordinals and the cardinal representative `μ` make the starting set injectable into `μ`; and composition transports these local comparisons back to the desired endpoints. None of these steps changes an internal coded injection into a host-level function.
<!--zh-->
整体比较由三项材料组成。凝聚把壳变成层 `Lset β`；非有限序数的移位与基数代表 `μ` 使起点可单射到 `μ`；最后，复合把这些局部比较接回所需的两个端点。这些步骤都不会把内部编码单射变成宿主层函数。
<!--ja-->
全体の比較は三つの材料を組み合わせる。凝縮は包を段階 `Lset β` に変え、有限でない順序数に対するシフトと基数代表 `μ` は始点を `μ` へ単射できるようにし、最後に合成がこれらの局所的な比較を求める端点へつなぎ戻す。どの段階でも、内部的に符号化された単射がホスト側の関数に変わることはない。
<!--/-->

```agda
  using ( module Frame; module HullStage; module HullElemDown )
open import L.GCH.ConstructibleHull {ℓ} lem using ( module PiIn; module Condense′ )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( ordL; ω⊆; no-fin; module Shift )
open import L.GCH.AdequateStages {ℓ} lem using ( superadequate-above; Superadequate )
open import L.GCH.StageCountingTools {ℓ} lem using ( move )
```

<!--en-->
The hull-count theorem is the quantitative input: once its starting set injects into a non-finite internal cardinal, the generated hull does too. We will also use that every ordinal is contained in its own constructible stage, and that equality of the underlying sets determines equality of elements of the constructible carrier because their constructibility proofs are propositions.
<!--zh-->
壳计数定理是这里的定量输入：只要起始集合单射入一个非有限内部基数，由它生成的壳也单射入该基数。后文还会使用「每个序数包含于其自身可构造层」，以及「可构造性证明是命题，因此底层集合相等就决定可构造载体元素相等」。
<!--ja-->
包の計数定理が、ここでの量的な入力である。出発集合が有限でない内部基数へ単射するなら、そこから生成される包も同じ基数へ単射する。また、各順序数が自分自身の構成可能段階に含まれることと、構成可能性の証明が命題なので基礎集合の等しさから構成可能な台の要素の等しさが決まることも用いる。
<!--/-->

```agda
open import L.GCH.HullCounting {ℓ} lem using ( ord⊆Lset; module Count; S≡ )
```

<!--en-->
The inverse collapse will be compared as a map between elements of the constructible carrier `S`. Such an element includes both an underlying set and a constructibility proof, but the proof component is propositional. Consequently, equality of underlying sets determines equality in `S`, so the coded graph does not depend on which constructibility evidence presents its values.
<!--zh-->
逆塌缩将作为可构造载体 `S` 的元素之间的映射来比较。这样的元素同时包含底层集合与可构造性证明，但证明分量是命题。因此，底层集合相等便决定 `S` 中的相等，编码图不会依赖用哪份可构造性证据呈现其值。
<!--ja-->
逆崩壊は、構成可能な台 `S` の要素の間の写像として比較される。その要素は基礎集合と構成可能性の証明を含むが、証明の成分は命題である。したがって、基礎集合の等しさから `S` での等しさが決まり、符号化されたグラフは値を表示する構成可能性の証拠に依存しない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
```

<!--en-->
Non-finiteness enters the later counting argument in two concrete ways. It provides the shift injection `δ+1 ↪ δ`, and it implies that every finite ordinal, in particular the empty set, lies below `δ`. The length-two environments used for the inverse-collapse formula are independent of this infinitude argument.
<!--zh-->
非有限性在后面的计数论证中有两项具体作用：它给出移位单射 `δ+1 ↪ δ`，并保证每个有限序数，特别是空集，都位于 `δ` 之下。逆塌缩公式所用的二元环境与这项无穷性论证彼此独立。
<!--ja-->
有限でないことは、後の計数の議論で二つの具体的な役割を果たす。シフト単射 `δ+1 ↪ δ` を与え、また空集合を含むすべての有限順序数が `δ` より下にあることを保証する。逆崩壊の論理式に用いる長さ二の環境は、この無限性の議論とは独立である。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( ω; sucV )
```

<!--en-->
Propositional truncation appears at two decisive points. It lets the proof use the mere constructibility of the hull when establishing a propositional satisfaction statement, and it is also the outer form of every conclusion `InjL`. Elimination is therefore always into a proposition.
<!--zh-->
命题截断出现在两个关键位置。证明壳满足某个公式时，它允许从壳仅仅可构造这一事实消去到命题性的满足陈述；同时，每个 `InjL` 结论的最外层也正是命题截断。因此，这里的截断消去总是以命题为目标。
<!--ja-->
命題的切り詰めは、二つの決定的な箇所に現れる。包がある論理式を満たすことを示す際には、包が単に構成可能であるという事実を命題である充足の主張へ消去できる。また、すべての `InjL` の結論も、その最外層が命題的切り詰めである。したがって、ここでの切り詰めの消去先は常に命題である。
<!--/-->



<!--en-->
Membership written `_∈ˢ_` is membership in the ambient hierarchy structure `𝒮ᵥ`. It is used for statements about the hull, its collapse image, and ordinal indices before those sets are packaged as elements of the constructible structure.
<!--zh-->
记作 `_∈ˢ_` 的隶属是外围层级结构 `𝒮ᵥ` 中的隶属。壳、其塌缩像与序数指标尚未打包为可构造结构的元素时，关于它们的陈述都使用这种隶属。
<!--ja-->
`_∈ˢ_` と書く所属は、周囲の階層構造 `𝒮ᵥ` における所属である。包、その崩壊像、順序数の添字が構成可能構造の要素としてまとめられる前には、それらについての主張をこの所属で表す。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
The type `S` is the carrier of the constructible structure: an element consists of an ambient set together with a proof that it belongs to `L`. Domains, codomains, and graph parameters of the internal coded maps below all live in this carrier.
<!--zh-->
类型 `S` 是可构造结构的载体：它的一个元素由外围集合及其属于 `L` 的证明组成。下文内部编码映射的定义域、陪域与图参数都属于这个载体。
<!--ja-->
型 `S` は構成可能構造の台である。その要素は、周囲の集合と、その集合が `L` に属することの証明からなる。以下の内部的に符号化された写像では、定義域、終域、グラフのパラメータがすべてこの台に属する。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Satisfaction of an object-language formula in `𝒮ʟ` is read through absoluteness as the corresponding proposition about ambient sets. This bridge lets the proof establish the inverse-collapse graph externally and then package the same relation as a definable graph inside `L`.
<!--zh-->
对象语言公式在 `𝒮ʟ` 中的满足关系经绝对性读作关于外围集合的相应命题。这座桥梁使证明可以先在外围建立逆塌缩图，再把同一个关系打包为 `L` 内部的可定义图。
<!--ja-->
対象言語の論理式が `𝒮ʟ` で満たされることは、絶対性を通して、周囲の集合についての対応する命題として読まれる。この橋渡しにより、逆崩壊のグラフを外側で証明し、同じ関係を `L` の内部の定義可能なグラフとしてまとめられる。
<!--/-->

```agda
open FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using () renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
There is one small mismatch of conventions to resolve. The collapse formula `piFo` is read with its value and preimage in the order `(v,x)`, whereas the definable-map graph is evaluated in the order `(x,v)`. Swapping the two free variables and using invariance of satisfaction under renaming expresses the same relation in the required order; no model or formula meaning is changed.
<!--zh-->
这里需要协调一处约定差异。塌缩公式 `piFo` 按 `(v,x)` 的顺序读取像值与原像，而可定义映射的图按 `(x,v)` 的顺序求值。交换两个自由变元，再利用满足关系在改名下的不变性，就能以所需顺序表达同一关系；模型与公式含义都没有改变。
<!--ja-->
ここでは、約束の小さな違いを調整する必要がある。崩壊の論理式 `piFo` は値と逆像を `(v,x)` の順で読むが、定義可能写像のグラフは `(x,v)` の順で評価される。二つの自由変数を入れ替え、名前替えのもとでの充足の不変性を使えば、同じ関係を必要な順序で表せる。モデルも論理式の意味も変わらない。
<!--/-->

```agda
module Ren = Sat 𝒮ʟ id using ( Agrees; ⊨-rename )
```

<!--en-->
## Counting the hull at a strengthened adequate stage
<!--zh-->
## 在超充分层计数 Skolem 壳
<!--ja-->
## 強化された十分な段階で Skolem 包を数える
<!--/-->

<!--en-->
We first isolate the geometric part of the argument from its later cardinal estimate. Fix an ordinal `lam` closed under successors and a starting set `X` contained in `Lset lam`; assume also that the index contains the empty set and that the Skolem hull generated from `X` is elementary in the required sense. No target cardinal is involved at this point.
<!--zh-->
先把论证的几何部分与后面的基数估计分开。固定一个对后继封闭的序数 `lam`，以及包含于 `Lset lam` 的起始集合 `X`；还假设该指标包含空集，并且由 `X` 生成的 Skolem 壳具有所需的初等性。此时尚未涉及任何目标基数。
<!--ja-->
まず、議論の幾何的な部分を、後で行う基数評価から切り離する。後続について閉じた順序数 `lam` と、`Lset lam` に含まれる出発集合 `X` を固定する。さらに、この添字が空集合を含み、`X` から生成される Skolem 包が必要な意味で初等的であると仮定する。この時点では、目標となる基数はまだ現れない。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Site (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : V ℓ) (X⊆Lλ : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
Superadequacy of `lam` supplies the closure and correctness conditions required by condensation. Constructibility of `X` ensures that the successive finite closure stages used to generate the hull, and hence their union, remain in `L`. The hull and its collapse image can therefore both be represented inside the constructible structure.
<!--zh-->
`lam` 的超充分性提供凝聚所需的闭包与正确性条件。`X` 的可构造性保证生成壳时逐次得到的有限闭包层，以及这些闭包层的并，仍留在 `L` 中。因此，壳及其塌缩像都能在可构造结构内部表示。
<!--ja-->
`lam` の強化された十分性は、凝縮に必要な閉性と正しさの条件を与える。`X` の構成可能性により、包を生成する有限な閉包段階の列とその合併は `L` の中にとどまる。したがって、包とその崩壊像の双方を構成可能構造の内部で表せる。
<!--/-->



<!--en-->
Condensation now identifies the collapse image with `Lset β` for some ordinal `β`. Independently, the hull construction proves that the hull `M` is constructible. These are exactly the two facts needed to regard the inverse collapse as a map from a constructible stage to a constructible hull.
<!--zh-->
凝聚由此把塌缩像认同为某个序数 `β` 所索引的 `Lset β`。另一方面，壳构造证明壳 `M` 可构造。这两条事实恰好使逆塌缩能够被视为从一个可构造层到一个可构造壳的映射。
<!--ja-->
凝縮により、崩壊像はある順序数 `β` による `Lset β` と同一視される。一方、包の構成から包 `M` が構成可能であることも分かる。この二つの事実によって、逆崩壊を構成可能段階から構成可能な包への写像として扱える。
<!--/-->

```agda
  condenses′ = Condense′.condenses′ lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
  M-isL = Condense′.M-isL lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
```

<!--en-->
Write `π : M → πX` for the collapse and `πX` for its image. The collapse machinery supplies preimages of points in `πX`, injectivity on the extensional hull, and the fact that transitive parts of the hull are fixed. The formula `piFo` represents the graph of `π`; its adequacy lemmas will connect satisfaction of that formula with the actual collapse value.
<!--zh-->
把塌缩记作 `π : M → πX`，并以 `πX` 表示其像。塌缩机制提供 `πX` 中各点的原像、塌缩在外延壳上的单射性，以及它固定壳中传递部分这一事实。公式 `piFo` 表示 `π` 的图；其充分性引理会把该公式的满足关系与实际塌缩值联系起来。
<!--ja-->
崩壊を `π : M → πX` と書き、その像を `πX` と書く。崩壊の仕組みから、`πX` の点の逆像、外延的な包の上での単射性、包の推移的な部分を固定することが得られる。論理式 `piFo` は `π` のグラフを表し、その妥当性補題が、この論理式の充足と実際の崩壊値を結ぶ。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆Lλ ∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X X⊆Lλ ∅∈λ
    using ( πX; π; fixes; πX-intro; πX-member )
  module P = PiIn (HS.M , M-isL) using ( piFo; up; good-at; piFo-val )
```

<!--en-->
The ordinal `β` measures the height of the collapse image. At this general site there is no ordinal `δ` to be counted and no target cardinal, so no comparison between `β` and either of them is available yet.
<!--zh-->
序数 `β` 衡量塌缩像所处的高度。在这个一般场址中，尚无待计数的序数 `δ`，也无目标基数，因此此时不能把 `β` 与二者中的任何一个比较。
<!--ja-->
順序数 `β` は、崩壊像が位置する高さを表す。この一般的な場では、まだ数えるべき順序数 `δ` も目標の基数もないため、`β` をそれらと比較することはできない。
<!--/-->

```agda

  β : V ℓ
  β = condenses′ .fst
```

<!--en-->
The accompanying proof that `β` is an ordinal makes `Lset β` a genuine ordinal-indexed stage. It will also be essential later when membership of an ordinal in `Lset β` is converted into an ordinal comparison with `β`.
<!--zh-->
随附的序数性证明使 `Lset β` 成为真正由序数索引的层。稍后把某个序数属于 `Lset β` 转换为它与 `β` 的序数比较时，也必须使用这份证明。
<!--ja-->
付随する順序数性の証明により、`Lset β` は順序数で添字づけられた段階になる。後で、ある順序数が `Lset β` に属することを `β` との順序数比較へ変換する際にも、この証明が必要である。
<!--/-->

```agda
  oβ : IsOrd β
  oβ = condenses′ .snd .fst
```

<!--en-->
The equality `ext : πX = Lset β` is the hinge between collapse theory and the constructible hierarchy. It converts membership in the collapse image into membership in the stage at `β`; later, once the collapse is shown to fix `δ`, this is exactly how `δ ∈ Lset β` will be obtained.
<!--zh-->
等式 `ext : πX = Lset β` 是塌缩理论与可构造层级之间的枢纽。它把塌缩像中的隶属转换为 `β` 处层中的隶属；稍后证明塌缩固定 `δ` 后，正是沿这条等式得到 `δ ∈ Lset β`。
<!--ja-->
等式 `ext : πX = Lset β` は、崩壊の理論と構成可能階層を結ぶ要である。これは崩壊像への所属を `β` の段階への所属に変換する。後で崩壊が `δ` を固定すると示した後、まさにこの等式によって `δ ∈ Lset β` が得られる。
<!--/-->

```agda
  ext : HSC.πX ≡ Lset β
  ext = condenses′ .snd .snd
```

<!--en-->
Because `β` is an ordinal, `Lset β` is constructible and can be packaged as an element `Lβ` of the carrier `S`. This packaged stage will be the domain of the inverse-collapse map.
<!--zh-->
由于 `β` 是序数，`Lset β` 可构造，因而可以打包为载体 `S` 的元素 `Lβ`。这个打包后的层将成为逆塌缩映射的定义域。
<!--ja-->
`β` は順序数なので `Lset β` は構成可能であり、台 `S` の要素 `Lβ` としてまとめられる。このまとめられた段階が逆崩壊写像の定義域になる。
<!--/-->

```agda
  Lβ : S
  Lβ = LsetS β oβ
```

<!--en-->
The ordinal `β` itself is also constructible and is packaged as `βL`. Although the inverse-collapse map uses `Lβ`, the packaged index will later let the bounded-subset argument compare `β` with a target cardinal by an internal coded injection.
<!--zh-->
序数 `β` 本身也可构造，并被打包为 `βL`。逆塌缩映射使用的是 `Lβ`，而打包后的指标会在后面的有界子集论证中用于通过内部编码单射比较 `β` 与目标基数。
<!--ja-->
順序数 `β` 自身も構成可能であり、`βL` としてまとめられる。逆崩壊写像が使うのは `Lβ` であるが、まとめられた添字は、後の有界部分集合の議論で `β` と目標の基数を内部的に符号化された単射によって比較するために使われる。
<!--/-->

```agda
  βL : S
  βL = ordL β oβ
```

<!--en-->
An internal coded map must have a codomain in the carrier `S`, not merely an externally described class of hull members. The element `hullL` supplies that internal presentation of the hull together with its constructibility evidence.
<!--zh-->
内部编码映射的陪域必须是载体 `S` 的元素，不能只是外围描述的壳成员类。元素 `hullL` 给出壳在内部的这种呈现，并携带其可构造性证据。
<!--ja-->
内部的に符号化された写像の終域は、外側で記述された包の要素の集まりではなく、台 `S` の要素でなければならない。`hullL` は、構成可能性の証拠とともに包の内部的な表示を与える。
<!--/-->

```agda
  hullL : S
  hullL = Condense′.hullL lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
```

<!--en-->
The equality `M≡` connects the two presentations of the hull. Collapse theorems speak about the ambient set `M`, whereas the internal graph speaks about the carrier element `hullL`; transporting along this equality lets the same membership evidence serve on both sides.
<!--zh-->
等式 `M≡` 连接壳的两种呈现。塌缩定理谈论外围集合 `M`，内部图则谈论载体元素 `hullL`；沿这条等式搬运后，同一份隶属证据即可用于两边。
<!--ja-->
等式 `M≡` は、包の二つの表示を結ぶ。崩壊の定理は周囲の集合 `M` を扱い、内部のグラフは台の要素 `hullL` を扱う。この等式に沿って輸送することで、同じ所属の証拠を両方で使える。
<!--/-->

```agda
  M≡ : fst hullL ≡ HS.M
  M≡ = Condense′.hullL-spec lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
```

<!--en-->
The hull frame proves that membership on `M` is extensional. This is the precise hypothesis needed to deduce that two members of the hull with the same collapse value are equal.
<!--zh-->
壳框架证明 `M` 上的隶属关系具有外延性。这正是从「壳的两个成员具有相同塌缩值」推出它们相等所需的假设。
<!--ja-->
包の枠組みから、`M` 上の所属関係が外延的であることが分かる。これは、包の二つの要素が同じ崩壊値をもつなら等しいと結論するために必要な仮定である。
<!--/-->

```agda
  Mext : isExt HS.M
  Mext = Frame.Mext lam ordλ succλ X X⊆Lλ ∅∈λ
```

<!--en-->
Applying the collapse injectivity theorem to this extensional hull yields `π-inj`. It will prove both uniqueness of each preimage and injectivity of the inverse-collapse map constructed from those preimages.
<!--zh-->
把塌缩单射性定理施于这个外延壳，便得到 `π-inj`。它既用于证明每个原像唯一，也用于证明由这些原像构造的逆塌缩映射单射。
<!--ja-->
この外延的な包に崩壊の単射性定理を適用すると `π-inj` が得られる。これは、各逆像の一意性と、それらの逆像から作る逆崩壊写像の単射性の両方を証明するために使われる。
<!--/-->

```agda
  module CI = HullStage.C.InjExt lam ordλ succλ X X⊆Lλ ∅∈λ Mext using ( π-inj )
```

<!--en-->
A preimage of a collapse value `v` is an element `x` of the hull whose collapse equals the underlying set of `v`. The record is an untruncated dependent pair: both the preimage and its membership and its identification are carried explicitly.
<!--zh-->
塌缩值 `v` 的原像，是其塌缩等于 `v` 底层集的壳元素 `x`。该记录是未截断的依赖对：原像、其隶属及其同一视都被显式携带。
<!--ja-->
崩壊の値 `v` の逆像とは、崩壊させたものが `v` の底の集合と等しくなるような、包の要素 `x` のことである。この記録は切り詰められていない依存対であり、逆像とその所属とその同一視を明示的に運ぶ。
<!--/-->

```agda
  Pre : S → Type (ℓ-suc ℓ)
  Pre v = Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ HS.M ⟩ × (HSC.π x ≡ fst v))
```

<!--en-->
Preimages are unique, because the collapse is injective on the hull: two records with the same value identify their preimages through `π-inj`, and the remaining components are propositions. This is why the preimage can be recovered without choosing it.
<!--zh-->
原像唯一，因为塌缩在壳上单射：值相同的两条记录经 `π-inj` 认同其原像，其余分量都是命题。正因如此，无需选择即可恢复原像。
<!--ja-->
逆像は一意である。崩壊が包の上で単射だからである。同じ値をもつ二つの記録は `π-inj` を通して逆像を同一視し、残りの成分は命題になる。だからこそ、証人を選ばずに逆像を復元できるのである。
<!--/-->

```agda
  isPropPre : (v : S) → isProp (Pre v)
  isPropPre v (x , mx , e) (x' , mx' , e') =
    Σ≡Prop (λ x → isProp× (snd (x ∈ˢ HS.M)) (setIsSet _ _)) (CI.π-inj x x' mx mx' (e ∙ sym e'))
```

<!--en-->
The inverse collapse is required only for points of its image, which condensation identifies with `Lset β`. Accordingly, `Mem v` is the proposition that the underlying set of `v` belongs to this stage; this domain evidence is what produces an inhabited preimage type.
<!--zh-->
逆塌缩只需定义在其像中的点上，而凝聚已把该像认同为 `Lset β`。因此，`Mem v` 是「`v` 的底层集合属于这个层」这一命题；正是这份定义域证据保证原像类型有元素。
<!--ja-->
逆崩壊を定義する必要があるのは、その像の点だけであり、凝縮によってこの像は `Lset β` と同一視されている。そこで `Mem v` は、`v` の基礎集合がこの段階に属するという命題である。この定義域の証拠から、逆像の型に要素があることが分かる。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem v = ⟨ fst v ∈ˢ fst Lβ ⟩
```

<!--en-->
Membership in `Lset β` gives only the propositionally truncated type of preimages under the collapse. Since `Pre v` has already been proved to be a proposition, truncation elimination recovers its unique inhabitant. Thus `pre` uses uniqueness to obtain the inverse value; it makes no arbitrary choice among competing preimages.
<!--zh-->
属于 `Lset β` 起初只给出塌缩原像类型的命题截断。由于 `Pre v` 已经证明为命题，截断消去可以恢复其中唯一的元素。因此，`pre` 依靠唯一性取得逆像值，并未在多个竞争原像之间作任意选择。
<!--ja-->
`Lset β` への所属から最初に得られるのは、崩壊の逆像の型を命題的に切り詰めたものだけである。`Pre v` はすでに命題であると示されているため、切り詰めの消去によってその一意な要素を取り出せる。したがって `pre` は一意性によって逆像の値を得ており、複数の逆像から恣意的に選んではいない。
<!--/-->

```agda
  pre : (v : S) → Mem v → Pre v
  pre v m = rec₁ (isPropPre v) (λ w → w)
    (HSC.πX-member (fst v) (subst (λ w → ⟨ fst v ∈ˢ w ⟩) (sym ext) m))
```

<!--en-->
The preimage is packaged as a constructible set: its constructibility is transported from the hull through the identification of the packaged hull with the hull itself. The function is defined only on members of the stage at `β`, with the hull as its codomain; it is the inverse of the collapse on its image, not a global inverse.
<!--zh-->
原像被打包为可构造集合：其可构造性经「打包壳等于壳」的同一视从壳搬运而来。该函数只定义在 `β` 处层的成员上，以壳为陪域；它是塌缩在其像上的逆，而非全局逆函数。
<!--ja-->
逆像は構成可能な集合としてまとめられる。その構成可能性は、まとめられた包と包を同一視することを通して、包から運ばれる。この関数が定義されるのは `β` の段階の要素の上だけで、終域は包である。崩壊の像の上での逆であり、大域的な逆ではない。
<!--/-->

```agda
  fn : (v : S) → Mem v → S
  fn v m = pre v m .fst
         , isL-trans {x = fst hullL} {y = pre v m .fst}
             (subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)) (snd hullL)
```

<!--en-->
The renaming swaps the two variable slots: slot zero becomes slot one and conversely.
<!--zh-->
改名交换两个变元槽：零槽变为一槽，反之亦然。
<!--ja-->
改名は、二つの変数の枠を入れ替える。枠ゼロが枠一になり、逆もまた同様である。
<!--/-->

```agda
  ρ : Fin 2 → Fin 2
  ρ zero = suc zero
  ρ (suc zero) = zero
```

<!--en-->
The two environments list the same carrier elements in opposite orders. The proof `ag` checks at each of the two variable indices that looking up a variable after applying `ρ` agrees with looking it up in the swapped environment. This pointwise agreement is the hypothesis needed by satisfaction under renaming.
<!--zh-->
两个环境以相反顺序列出同样的载体元素。证明 `ag` 对两个变元指标逐一核对：先应用 `ρ` 再查找变元，与在交换后的环境中查找该变元相同。这种逐点一致正是改名保持满足关系所需的假设。
<!--ja-->
二つの環境には、同じ台の要素が逆の順序で並んでいる。証明 `ag` は二つの変数添字のそれぞれについて、`ρ` を適用してから変数を参照することと、入れ替えた環境でその変数を参照することが一致すると確かめる。この各点での一致が、名前替えのもとで充足関係を保つための仮定である。
<!--/-->

```agda
  private
    ag : (x v : S) → Ren.Agrees ρ (x ∷ v ∷ []) (v ∷ x ∷ [])
    ag x v zero = refl
    ag x v (suc zero) = refl
```

<!--en-->
Satisfaction of the renamed formula at the ordered environment equals satisfaction of the original formula at the swapped environment; this is the transport used to arrange the collapse graph's slots.
<!--zh-->
改名公式在有序环境处的满足等于原公式在交换环境处的满足；这正是安排塌缩图槽位所用的搬运。
<!--ja-->
名前を替えた論理式の、順序どおりの環境での充足は、入れ替えた環境のもとでのもとの論理式の充足と等しくなる。これが、崩壊のグラフの枠を整えるために使う輸送である。
<!--/-->

```agda
    rn : (x v : S) → ⟨ (x ∷ v ∷ []) ⊨ renameFo ρ P.piFo ⟩ ≡ ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
    rn x v = cong ⟨_⟩ (Ren.⊨-rename ρ P.piFo (x ∷ v ∷ []) (v ∷ x ∷ []) (ag x v))
```

<!--en-->
The inverse-collapse graph is the conjunction: the preimage belongs to the hull, and the renamed pairing graph holds of the preimage and the value.
<!--zh-->
逆塌缩图即该合取：原像属于壳，且改名后的配对图对原像与值成立。
<!--ja-->
逆崩壊のグラフはこの連言である。逆像が包に属し、名前を替えた対のグラフが逆像と値について成り立つ、というものである。
<!--/-->

```agda
  invFo : Formula S 2
  invFo = (var zero ∈̇ con hullL) ∧̇ renameFo ρ P.piFo
```

<!--en-->
For a hull member `x` whose collapse is `v`, the actual pair `(v,x)` satisfies `piFo`. Constructibility of the hull is itself given through a propositional truncation, so the proof eliminates that truncation into the satisfaction statement, which is a proposition, and works at any constructible stage containing the hull.
<!--zh-->
若壳成员 `x` 的塌缩为 `v`，则实际的有序对 `(v,x)` 满足 `piFo`。壳的可构造性本身经命题截断给出，因此证明把该截断消去到命题性的满足陈述，并在任意包含该壳的可构造层中完成构造。
<!--ja-->
包の要素 `x` の崩壊が `v` なら、実際の対 `(v,x)` は `piFo` を満たす。包の構成可能性そのものが命題的切り詰めを通して与えられるため、その切り詰めを命題である充足の主張へ消去し、包を含む任意の構成可能段階で証明する。
<!--/-->

```agda
  π-graph : (x : S) (mx : ⟨ fst x ∈ˢ HS.M ⟩) (v : S) → HSC.π (fst x) ≡ fst v
          → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
  π-graph x mx v e = rec₁ (snd ((v ∷ x ∷ []) ⊨ P.piFo)) read M-isL
    where
    read : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ HS.M ∈ˢ Lset α ⟩) → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
```

<!--en-->
The read statement transports both slots: the collapse value is identified with the underlying set of `v`, and the hull member is identified with the underlying set of `x`.
<!--zh-->
读取陈述搬运两个槽：塌缩值与 `v` 的底层集同一视，壳成员与 `x` 的底层集同一视。
<!--ja-->
読みの主張は、二つの枠を運ぶ。崩壊の値は `v` の底の集合と同一視され、包の要素は `x` の底の集合と同一視される。
<!--/-->

```agda
    read (α , oα , M∈Lα) =
      subst2 (λ a b → ⟨ (a ∷ b ∷ []) ⊨ P.piFo ⟩)
        (S≡ {x = HSC.π (fst x) , G .fst} {y = v} e) (S≡ {x = P.up (fst x) mx} {y = x} refl)
        (G .snd mx)
      where
```

<!--en-->
Given a constructible stage `Lset α` containing the hull, transitivity of the layer places each hull member `x` in that same stage. The lemma `good-at` then supplies a constructibility proof for `π x` together with a proof that the packaged collapse value and the packaged member satisfy `piFo`.
<!--zh-->
给定一个包含该壳的可构造层 `Lset α`，分层的传递性把每个壳成员 `x` 放入同一层。引理 `good-at` 随后给出 `π x` 的可构造性证明，并证明打包后的塌缩值与打包后的成员满足 `piFo`。
<!--ja-->
包を含む構成可能段階 `Lset α` が与えられると、層の推移性によって各包の要素 `x` も同じ段階に入る。補題 `good-at` は、`π x` の構成可能性の証明と、まとめられた崩壊値と要素が `piFo` を満たすことの証明を与える。
<!--/-->

```agda
      G = P.good-at α oα (fst x) mx (layer-trans (Lset-layer α) {x = HS.M} {y = fst x} mx M∈Lα)
```

<!--en-->
The proof `defines` is the bridge from the actual inverse value to the internal formula. Its first component places that value in the packaged hull, and its second component uses the collapse equation together with renaming to show that `invFo` relates the value to its image point.
<!--zh-->
证明 `defines` 把实际逆像值连接到内部公式。其第一分量把该值放入打包后的壳，第二分量则结合塌缩等式与公式改名，证明 `invFo` 把这个值关联到相应的像点。
<!--ja-->
証明 `defines` は、実際の逆像の値と内部の論理式を結ぶ橋である。第一成分はその値をまとめられた包に入れ、第二成分は崩壊の等式と名前替えを用いて、`invFo` がその値を対応する像の点に関係づけることを示す。
<!--/-->

```agda
  defines : (v : S) (m : Mem v) → ⟨ (fn v m ∷ v ∷ []) ⊨ invFo ⟩
  defines v m =
      subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
    , transport (sym (rn (fn v m) v)) (π-graph (fn v m) (pre v m .snd .fst) v (pre v m .snd .snd))
```

<!--en-->
Only the preimage is left to identify: any preimage satisfying the inverse graph has the same collapse value as the packaged preimage, and the injectivity of the collapse returns the equality of the two preimages.
<!--zh-->
只剩下原像需要识别：任何满足逆图的原像与打包后的原像有相同的塌缩值，而塌缩的单射性返回两个原像的相等。
<!--ja-->
残るのは逆像の特定だけである。逆のグラフを満たすどんな逆像も、まとめられた逆像と同じ崩壊の値をもち、崩壊の単射性が、二つの逆像の等しさを返す。
<!--/-->

```agda
  only : (v : S) (m : Mem v) (x' : S) → ⟨ (x' ∷ v ∷ []) ⊨ invFo ⟩ → x' ≡ fn v m
  only v m x' (hx , hp) = S≡ (CI.π-inj (fst x') (pre v m .fst) mx' (pre v m .snd .fst)
    (sym (P.piFo-val x' mx' v (transport (rn x' v) hp)) ∙ sym (pre v m .snd .snd)))
    where
    mx' : ⟨ fst x' ∈ˢ HS.M ⟩
```

<!--en-->
For an alternative output `x'` satisfying the graph, the first conjunct says that its underlying set belongs to the packaged hull. Transport along `M≡` turns this into membership in the ambient hull `M`, which is the premise needed to compare `x'` with the recovered preimage by collapse injectivity.
<!--zh-->
若另一个输出 `x'` 满足该图，第一合取支说明其底层集属于打包后的壳。沿 `M≡` 搬运后，便得到它属于外围壳 `M`，这正是利用塌缩单射性把 `x'` 与已恢复原像比较所需的前提。
<!--ja-->
グラフを満たす別の出力 `x'` について、第一の連言はその基礎集合がまとめられた包に属することを述べる。`M≡` に沿って輸送すると周囲の包 `M` への所属が得られ、崩壊の単射性によって `x'` と復元した逆像を比較するための前提になる。
<!--/-->

```agda
    mx' = subst (λ w → ⟨ fst x' ∈ˢ w ⟩) M≡ hx
```

<!--en-->
These results internalize the restricted inverse as a single-valued definable map. Every `v ∈ Lβ` is sent into the hull and satisfies `invFo`, while `only` shows that any other output satisfying the same graph is equal to this value. Injectivity is a further property and is proved separately next.
<!--zh-->
这些结果把受限逆内化为单值的可定义映射。每个 `v ∈ Lβ` 都被送入壳并满足 `invFo`，而 `only` 说明任何满足同一图的其他输出都等于这个值。单射性是进一步的性质，将在下一步另行证明。
<!--ja-->
以上の結果により、制限された逆写像は一価な定義可能写像として内部化される。各 `v ∈ Lβ` は包へ送られて `invFo` を満たし、`only` は同じグラフを満たすほかの出力がこの値に等しいことを示す。単射性はさらに必要な性質であり、次に別途証明する。
<!--/-->

```agda
  Dmap : DefinableMap
  Dmap = record
    { dom = Lβ ; cod = hullL ; fn = fn
    ; into = λ v m → subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
    ; graph = invFo ; defines = defines ; only = only }
```

<!--en-->
Each uniquely determined preimage satisfies `π(pre(v)) = v`. Hence, if the two values of the inverse-collapse map are equal, applying `π` to that equality and composing with the two preimage equations gives `v = v'`. Thus the inverse on the collapse image is injective; this step uses the right-inverse equations rather than injectivity of the collapse.
<!--zh-->
每个由唯一性确定的原像都满足 `π(pre(v)) = v`。因此，若逆塌缩映射的两个值相等，对该等式施加 `π`，再与两端的原像等式复合，便得到 `v = v'`。所以塌缩像上的逆映射是单射；这一步使用的是右逆等式，而不是塌缩本身的单射性。
<!--ja-->
一意性によって定まる各逆像は `π(pre(v)) = v` を満たす。したがって、逆崩壊写像の二つの値が等しければ、その等式に `π` を作用させ、両端の逆像の等式と合成することで `v = v'` が得られる。よって崩壊像上の逆写像は単射である。この段階で使うのは右逆の等式であり、崩壊そのものの単射性ではない。
<!--/-->

```agda

  inj : (v : S) (m : Mem v) (v' : S) (m' : Mem v') → fst (fn v m) ≡ fst (fn v' m') → fst v ≡ fst v'
  inj v m v' m' q = sym (pre v m .snd .snd) ∙ cong HSC.π q ∙ pre v' m' .snd .snd
```

<!--en-->
The restricted inverse is packaged as a coded injection from `Lβ` into the hull, completing the first section's construction. The packaging preserves the truncated form, so only the existence of a coded graph is exposed.
<!--zh-->
受限逆被打包为从 `Lβ` 到壳的编码单射，完成第一节的构造。打包保持截断形式，只暴露编码图的存在性。
<!--ja-->
制限された逆は、`Lβ` から包への符号化された単射としてまとめられ、最初の節の構成が完成する。まとめは切り詰められた形を保つので、公開されるのは符号化されたグラフの存在だけである。
<!--/-->

```agda
  Lβ↪M : InjL Lβ hullL
  Lβ↪M = Inj.injL Dmap inj
```
</div>
</details>


<!--en-->
## Collapsing the hull back to the original stage
<!--zh-->
## 把 Skolem 壳塌缩回原层
<!--ja-->
## Skolem 包を元の段階へ崩壊して戻す
<!--/-->

<!--en-->
The counting module `At` fixes a non-finite constructible ordinal `δL`, its ordinality, and its exclusion from `ω`; an internal cardinal representative `μ` with the same non-finiteness; and two coded injections between `δL` and `μ` in both directions. These are exactly the data needed to count a non-finite stage by a cardinal representative.
<!--zh-->
计数模块 `At` 固定非有限可构造序数 `δL`、其序数性与对 `ω` 的排除；具有相同非有限性的内部基数代表 `μ`；以及 `δL` 与 `μ` 之间双向的编码单射。这些恰是以基数代表计数非有限层所需的数据。
<!--ja-->
計数のモジュール `At` は、非有限の構成可能な順序数 `δL`、その順序数性、`ω` への所属の排除、同じく非有限な内部の基数代表 `μ`、そして `δL` と `μ` の間の双方向の符号化された単射を固定する。これらが、基数代表で非有限の段階を数えるために必要なデータそのものである。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module At (δL : S) (oδ : IsOrd (fst δL)) (δ∉ω : ⟨ fst δL ∈ˢ ω ⟩ → ⊥₀)
          (μ : S) (oμ : IsOrd (fst μ)) (cμ : IsCardinalL μ)
          (μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → ⊥₀)
          (δ↪μ : InjL δL μ) (μ↪δ : InjL μ δL) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
It is useful to separate the carrier element `δL` from its underlying ambient ordinal `δ = fst δL`. Set-theoretic successor, stage membership, and the collapse act on `δ`, while internal coded injections retain the packaged endpoint `δL`.
<!--zh-->
这里需要区分载体元素 `δL` 与其底层外围序数 `δ = fst δL`。集合论后继、层隶属与塌缩作用于 `δ`，内部编码单射的端点则仍使用打包后的 `δL`。
<!--ja-->
台の要素 `δL` と、その基礎となる周囲の順序数 `δ = fst δL` を区別すると見通しがよくなる。集合論的後続、段階への所属、崩壊は `δ` に作用し、内部的に符号化された単射の端点にはまとめられた `δL` を使う。
<!--/-->

```agda
  δ : V ℓ
  δ = fst δL
```

<!--en-->
The stage of the ordinal `δ` is the earliest constructible level containing it; here it provides the starting index for finding a sufficiently high superadequate level.
<!--zh-->
序数 `δ` 的层是包含它的最早可构造层；此处它提供寻找足够高的超充分层的起始索引。
<!--ja-->
順序数 `δ` の段階は、それを含む最初の構成可能な層であり、ここでは、十分に高い超適切な層を見つけるための出発点の添字を供給する。
<!--/-->

```agda
  private
    α₀ : V ℓ
    α₀ = stage δ (snd δL)
```

<!--en-->
The least-stage construction always returns an ordinal index. Applied to the constructible set `δ`, this gives the ordinality of `α₀`; the argument does not derive it from the separate hypothesis that `δ` is an ordinal.
<!--zh-->
最小层构造总会返回一个序数索引。把它用于可构造集合 `δ`，便得到 `α₀` 的序数性；这一步并非从另一项「`δ` 是序数」的假设推出。
<!--ja-->
最小段階の構成は常に順序数の添字を返す。これを構成可能集合 `δ` に適用すると `α₀` の順序数性が得られる。この事実は、`δ` 自身が順序数であるという別の仮定から導かれるのではない。
<!--/-->

```agda
    oα₀ : IsOrd α₀
    oα₀ = stage-ord δ (snd δL)
```

<!--en-->
The ordinal `δ` belongs to its own stage, which is the membership fact that anchors `δ` inside the constructible hierarchy.
<!--zh-->
序数 `δ` 属于自身所在的层，这正是把 `δ` 锚定在可构造层级内的隶属事实。
<!--ja-->
順序数 `δ` はそれ自身の段階に属する。これが、`δ` を構成可能階層の中に位置づける所属の事実である。
<!--/-->

```agda
    δ∈Lα₀ : ⟨ δ ∈ˢ Lset α₀ ⟩
    δ∈Lα₀ = stage-mem δ (snd δL)
```

<!--en-->
A superadequate level above the stage index is obtained; it carries all the closure conditions needed for the Skolem hull construction and for the condensation transfer.
<!--zh-->
在层索引之上取得一个超充分层；它携带着 Skolem 壳构造与凝聚搬运所需的全部闭包条件。
<!--ja-->
段階の添字より上に、超適切な層が得られる。そこは、Skolem 包の構成と凝縮の移送に必要なすべての閉じの条件を携えている。
<!--/-->

```agda
    sa = superadequate-above α₀ oα₀
```

<!--en-->
Choose the strengthened adequate stage supplied above and denote its ordinal index by `λ`. All subsequent hull and condensation arguments take place at this one sufficiently high stage.
<!--zh-->
取上面给出的超充分层，并把它的序数指标记作 `λ`。后续的壳与凝聚论证都在这个足够高的固定层中进行。
<!--ja-->
上で得た強化された十分な段階を取り、その順序数添字を `λ` と書く。以後の包と凝縮の議論は、すべてこの十分に高い一つの段階で行う。
<!--/-->

```agda
  opaque
    lam : V ℓ
    lam = sa .fst
```

<!--en-->
The chosen high index `λ` is an ordinal. Its transitivity will first carry `δ` through the comparison `δ ∈ α₀ ∈ λ`, and will then place every member of `δ+1` below `λ`.
<!--zh-->
所选高指标 `λ` 是序数。它的传递性先沿比较 `δ ∈ α₀ ∈ λ` 把 `δ` 放入 `λ`，随后又把 `δ+1` 的每个成员放到 `λ` 之下。
<!--ja-->
選ばれた高い添字 `λ` は順序数である。その推移性により、まず比較 `δ ∈ α₀ ∈ λ` から `δ ∈ λ` を得て、さらに `δ+1` の各要素を `λ` より下に置く。
<!--/-->

```agda
    ordλ : IsOrd lam
    ordλ = sa .snd .fst
```

<!--en-->
Successor closure is the second property of the index used immediately below: from `δ ∈ λ` it yields `δ+1 ∈ λ`. This is a statement about the ordinal index `λ`; it should not be confused with taking a successor constructible stage.
<!--zh-->
对后继封闭是下文立即使用的第二项指标性质：由 `δ ∈ λ` 可得 `δ+1 ∈ λ`。这是关于序数指标 `λ` 的陈述，不能与取可构造后继层混淆。
<!--ja-->
後続についての閉性は、直後に使う添字の第二の性質である。`δ ∈ λ` から `δ+1 ∈ λ` が従う。これは順序数添字 `λ` についての主張であり、構成可能段階の後続を取ることとは異なる。
<!--/-->

```agda
    succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
    succλ = sa .snd .snd .snd .fst .snd .fst
```

<!--en-->
Superadequacy says that above every member `d` of `λ` there merely exists an adequate stage `γ` that still belongs to `λ`. This supply of intermediate adequate stages provides the local reflection and closure used in counting and condensing the hull.
<!--zh-->
超充分性断言：对 `λ` 的每个成员 `d`，仅仅存在一个仍属于 `λ` 且位于 `d` 之上的充分层 `γ`。这些中间充分层提供计数并凝聚该壳时所需的局部反映与闭包。
<!--ja-->
強化された十分性は、`λ` の各要素 `d` の上に、なお `λ` に属する十分な段階 `γ` が単に存在することを述べる。このような中間の十分な段階が、包の計数と凝縮に必要な局所的な反映と閉性を与える。
<!--/-->

```agda
    sup : Superadequate lam
    sup = sa .snd .snd .snd .snd
```

<!--en-->
First, `δ ∈ Lset α₀` and the fact that both `δ` and `α₀` are ordinals imply `δ ∈ α₀`. Since `α₀ ∈ λ`, transitivity of the ordinal `λ` then yields `δ ∈ λ`.
<!--zh-->
首先，由 `δ ∈ Lset α₀` 以及 `δ`、`α₀` 都是序数，可得 `δ ∈ α₀`。再由 `α₀ ∈ λ` 和序数 `λ` 的传递性，得到 `δ ∈ λ`。
<!--ja-->
まず、`δ ∈ Lset α₀` と、`δ` と `α₀` がともに順序数であることから `δ ∈ α₀` が従う。さらに `α₀ ∈ λ` なので、順序数 `λ` の推移性により `δ ∈ λ` を得る。
<!--/-->

```agda
    δ∈λ : ⟨ δ ∈ˢ lam ⟩
    δ∈λ = ordλ .fst (ord∈Lset→∈ α₀ oα₀ δ oδ δ∈Lα₀) (sa .snd .snd .fst)
```

<!--en-->
Take the starting set to be the von Neumann successor `X = δ+1`. It contains `δ` together with every smaller ordinal, and, because `δ` is an ordinal, `X` is transitive; these are exactly the features needed when the collapse is later shown to fix `δ`.
<!--zh-->
取冯·诺伊曼后继 `X = δ+1` 为起点集。它包含 `δ` 以及每个更小的序数；又因 `δ` 是序数，`X` 是传递集。这些性质正用于稍后证明塌缩固定 `δ`。
<!--ja-->
始点集合をフォン・ノイマン後続 `X = δ+1` とする。これは `δ` と、それより小さいすべての順序数を含み、`δ` が順序数なので推移的である。これらの性質を用いて、後で崩壊が `δ` を固定することを示す。
<!--/-->

```agda
  X : V ℓ
  X = sucV δ
```

<!--en-->
Successor closure of the ordinal index now gives `X = δ+1 ∈ λ`. This is an ordinal comparison. The stronger-looking statement needed by the hull construction, that every member of `X` lies in `Lset λ`, is derived separately in the next step.
<!--zh-->
序数指标的后继封闭性现给出 `X = δ+1 ∈ λ`。这是一项序数比较。壳构造所需的另一项陈述，即 `X` 的每个成员都属于 `Lset λ`，将在下一步另行推出。
<!--ja-->
順序数添字の後続についての閉性から、`X = δ+1 ∈ λ` が得られる。これは順序数の比較である。包の構成に必要な、`X` の各要素が `Lset λ` に属するという別の主張は、次の段階で導く。
<!--/-->

```agda
  sucδ∈λ : ⟨ X ∈ˢ lam ⟩
  sucδ∈λ = succλ δ δ∈λ
```

<!--en-->
If `z ∈ X`, transitivity of the ordinal `λ` and `X ∈ λ` give `z ∈ λ`. The general inclusion of an ordinal in its own constructible stage then yields `z ∈ Lset λ`. Hence the required premise is precisely `X ⊆ Lset λ`.
<!--zh-->
若 `z ∈ X`，则由序数 `λ` 的传递性与 `X ∈ λ` 得到 `z ∈ λ`。再用序数包含于自身可构造层的一般事实，可得 `z ∈ Lset λ`。因此，所需前提正是 `X ⊆ Lset λ`。
<!--ja-->
`z ∈ X` なら、順序数 `λ` の推移性と `X ∈ λ` から `z ∈ λ` が従う。さらに、順序数はそれ自身の構成可能段階に含まれるという一般的な事実により、`z ∈ Lset λ` を得る。したがって、必要な前提はちょうど `X ⊆ Lset λ` である。
<!--/-->

```agda
  X⊆Lλ : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  X⊆Lλ z hz = ord⊆Lset lam ordλ z (ordλ .fst hz sucδ∈λ)
```

<!--en-->
Because `δ` is non-finite, every finite ordinal lies below `δ`; in particular `∅ ∈ δ`. Combining this with `δ ∈ λ` and transitivity of the ordinal `λ` gives the separate hull premise `∅ ∈ λ`.
<!--zh-->
由于 `δ` 非有限，每个有限序数都位于 `δ` 之下，特别有 `∅ ∈ δ`。再结合 `δ ∈ λ` 与序数 `λ` 的传递性，便得到壳构造的另一前提 `∅ ∈ λ`。
<!--ja-->
`δ` は有限でないため、すべての有限順序数は `δ` より下にあり、とくに `∅ ∈ δ` である。これを `δ ∈ λ` と順序数 `λ` の推移性に合わせると、包の構成に必要な別の前提 `∅ ∈ λ` が得られる。
<!--/-->

```agda
  ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩
  ∅∈λ = ordλ .fst (ω⊆ δ oδ δ∉ω ∅ (#∈ω zero)) δ∈λ
```

<!--en-->
The starting set is constructible, because the coded successor of a constructible set is constructible, transported along the equation identifying the coded successor with the set-theoretic successor.
<!--zh-->
起点集可构造，因为可构造集合的编码后继也可构造，沿认同编码后继与集合论后继的等式运输而来。
<!--ja-->
始点の集合は構成可能である。構成可能な集合の符号化された後続も構成可能であり、符号化された後続と集合論の後続を同一視する等式に沿って運ばれるからである。
<!--/-->

```agda
  X-isL : ⟨ isL X ⟩
  X-isL = subst (λ w → ⟨ isL w ⟩) (sucʟ-fst δL) (snd (sucʟ δL))
```

<!--en-->
The constructibility proof turns the ambient set `X = δ+1` into the carrier element `XS`. This changes only its presentation: the counting problem remains the problem of injecting the successor of `δ` into the cardinal representative `μ`.
<!--zh-->
可构造性证明把外围集合 `X = δ+1` 变成载体元素 `XS`。这只改变其呈现；计数问题仍是把 `δ` 的后继单射到基数代表 `μ`。
<!--ja-->
構成可能性の証明により、周囲の集合 `X = δ+1` は台の要素 `XS` になる。変わるのは表示だけであり、計数の問題は依然として `δ` の後続を基数代表 `μ` へ単射することである。
<!--/-->

```agda
  XS : S
  XS = X , X-isL
```

<!--en-->
The start is counted by the chain `δ+1 ↪ δ ↪ μ`. The first coded injection is the shift available for every non-finite ordinal `δ`, and the second is the assumed internal injection from `δ` to its cardinal representative `μ`. Their composition gives `InjL XS μ` without assuming that `δ` itself is a cardinal.
<!--zh-->
起点由链 `δ+1 ↪ δ ↪ μ` 计数。第一条编码单射是每个非有限序数 `δ` 都具有的移位单射，第二条是从 `δ` 到其基数代表 `μ` 的已知内部单射。复合后得到 `InjL XS μ`，全程无须假设 `δ` 本身是基数。
<!--ja-->
始点は鎖 `δ+1 ↪ δ ↪ μ` によって数えられる。最初の符号化された単射は、任意の非有限順序数 `δ` に対するシフトであり、二番目は `δ` からその基数代表 `μ` への仮定された内部単射である。これらを合成して `InjL XS μ` を得るが、`δ` 自身が基数であるとは仮定しない。
<!--/-->

```agda
  base : InjL XS μ
  base = injl-trans XS δL μ
    (move (sucʟ δL) XS δL δL (sucʟ-fst δL) refl (Shift.injL δL oδ δ∉ω))
    δ↪μ
```

<!--en-->
The Skolem hull generated from `X` is elementary in the surrounding stage `Lset λ`. This elementarity is what lets the counting theorem and the condensation argument transfer the relevant formulas and witnesses between the hull and the stage.
<!--zh-->
由 `X` 生成的 Skolem 壳在外围层 `Lset λ` 中是初等的。这项初等性使计数定理与凝聚论证能够在壳和该层之间转移相关公式及其见证。
<!--ja-->
`X` から生成される Skolem 包は、周囲の段階 `Lset λ` の初等部分構造である。この初等性により、計数定理と凝縮の議論は、包と段階の間で必要な論理式と証人を移すことができる。
<!--/-->

```agda
  elem = HullElemDown.elem lam ordλ X X⊆Lλ ∅∈λ
```

<!--en-->
The Skolem hull is counted by the cardinal representative `μ`, because the starting set already injects into `μ` and the hull chapter shows that closure preserves the counting.
<!--zh-->
Skolem 壳由基数代表 `μ` 计数，因为起点已经单射入 `μ`，而壳章证明封闭保持计数。
<!--ja-->
Skolem 包は、基数の代表 `μ` によって数えられる。始点がすでに `μ` へ単射し、包の章が、閉じても計数が保たれることを示しているからである。
<!--/-->

```agda
  hull↪μ = Count.hull↪κ lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL μ oμ cμ μ∉ω base
```

<!--en-->
Apply the general condensation construction to this hull. It supplies an ordinal `β` whose stage `Lβ` is the collapse image, presents the hull as a constructible set, and gives the propositionally truncated coded injection `Lβ ↪ M` obtained from the inverse collapse.
<!--zh-->
把一般凝聚构造用于这个壳。它给出序数 `β`，使其层 `Lβ` 正是塌缩像；同时把壳呈现为可构造集合，并由逆塌缩给出命题截断下的编码单射 `Lβ ↪ M`。
<!--ja-->
一般の凝縮構成をこの包に適用する。すると、その段階 `Lβ` が崩壊像となる順序数 `β`、構成可能集合としての包、そして逆崩壊から得られる、命題的に切り詰められた符号化単射 `Lβ ↪ M` が与えられる。
<!--/-->

```agda
  module St = Site lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
    using ( β; oβ; ext; Lβ; hullL; Lβ↪M )
```

<!--en-->
For the remaining comparison, use three facts about this hull: its underlying set is `M`, every member of the start lies in `M`, and the collapse `π` maps `M` onto `Lβ` while fixing members of any transitive subset of `M`. Applied to the transitive start `δ+1`, these facts will place `δ` in `Lβ`.
<!--zh-->
余下的比较使用该壳的三项性质：其底层集合是 `M`，起点的每个成员都属于 `M`，而塌缩 `π` 把 `M` 映到 `Lβ`，并固定 `M` 的任一传递子集中的成员。把这些性质用于传递起点 `δ+1`，稍后便可把 `δ` 放入 `Lβ`。
<!--ja-->
残る比較では、この包について三つの事実を使う。その基礎集合は `M` であり、始点の各要素は `M` に属し、崩壊 `π` は `M` を `Lβ` へ写すとともに、`M` の推移的部分集合の要素を固定する。これらを推移的な始点 `δ+1` に適用すると、`δ` を `Lβ` に置くことができる。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆Lλ ∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X X⊆Lλ ∅∈λ
    using ( π; fixes; πX-intro )
```

<!--en-->
The ordinal `δ` belongs to its own successor, which is the starting set for the hull construction.
<!--zh-->
序数 `δ` 属于自身的后继，后者是壳构造的起点集。
<!--ja-->
順序数 `δ` はそれ自身の後続に属する。それが、包の構成の始点の集合である。
<!--/-->

```agda
  δ∈X : ⟨ δ ∈ˢ X ⟩
  δ∈X = self∈sucV δ
```

<!--en-->
The ordinal `δ` therefore belongs to the hull, because the hull contains every member of the starting set.
<!--zh-->
因此序数 `δ` 属于壳，因为壳包含起点集的每个成员。
<!--ja-->
したがって、順序数 `δ` は包に属する。包が、始点の集合のすべての要素を含むからである。
<!--/-->

```agda
  δ∈M : ⟨ δ ∈ˢ HS.M ⟩
  δ∈M = HSH.X⊆M δ δ∈X
```

<!--en-->
The successor `X = δ+1` is transitive and is contained in the hull `M`. The collapse therefore fixes every member of `X`; since `δ ∈ X`, it follows in particular that `π(δ) = δ`.
<!--zh-->
后继 `X = δ+1` 是传递集，并且包含于壳 `M`。因此塌缩固定 `X` 的每个成员；特别地，由 `δ ∈ X` 可得 `π(δ) = δ`。
<!--ja-->
後続 `X = δ+1` は推移的で、包 `M` に含まれる。したがって崩壊は `X` の各要素を固定し、とくに `δ ∈ X` から `π(δ) = δ` が従う。
<!--/-->

```agda
  πδ : HSC.π δ ≡ δ
  πδ = HSC.fixes X
    (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst (HSH.X⊆M a (∈∈ₛ {a = a} {b = X} .snd a∈ₛX)))
    (suc-ord oδ .fst) δ δ∈X
```

<!--en-->
The ordinal `δ` lies inside the collapse level `Lβ`, because its collapse (which is itself) belongs to the collapse image, and the collapse image equals `Lset β`.
<!--zh-->
序数 `δ` 落在塌缩层 `Lset β` 之内，因为其塌缩 (即自身) 属于塌缩像，而塌缩像等于 `Lset β`。
<!--ja-->
順序数 `δ` は、崩壊の層 `Lset β` の中にある。その崩壊 (すなわちそれ自身) が崩壊の像の中にあり、崩壊の像が `Lset β` に等しいからである。
<!--/-->

```agda
  δ∈Lβ : ⟨ δ ∈ˢ Lset St.β ⟩
  δ∈Lβ = subst (λ w → ⟨ w ∈ˢ Lset St.β ⟩) πδ
    (subst (λ w → ⟨ HSC.π δ ∈ˢ w ⟩) St.ext (HSC.πX-intro δ δ∈M))
```

<!--en-->
The ordinal-stage bound now applies: when an ordinal `δ` belongs to `Lset β`, it must belong to the ordinal index `β`. Thus `δ ∈ β`. This is the strict comparison needed for monotonicity, and its direction places `Lset δ` inside `Lset β`.
<!--zh-->
现在可应用序数的层界：若序数 `δ` 属于 `Lset β`，则它必属于序数指标 `β`。因此 `δ ∈ β`。这正是层单调性所需的严格比较，其方向给出 `Lset δ ⊆ Lset β`。
<!--ja-->
ここで順序数の段階境界を適用する。順序数 `δ` が `Lset β` に属するなら、`δ` は順序数添字 `β` に属する。したがって `δ ∈ β` である。これは段階の単調性に必要な狭義比較であり、その向きから `Lset δ ⊆ Lset β` が得られる。
<!--/-->

```agda
  δ∈β : ⟨ δ ∈ˢ St.β ⟩
  δ∈β = ord∈Lset→∈ St.β St.oβ δ oδ δ∈Lβ
```

<!--en-->
The canonical carrier presentation `Lδ` has underlying set `Lset δ`. It is the source used by `At.result`; the final theorem will later transport this source to any other carrier element whose underlying set is equal to the same stage.
<!--zh-->
典范载体呈现 `Lδ` 的底层集是 `Lset δ`。`At.result` 以它为始域；最终定理随后会把这个始域搬到任意另一个底层集等于同一层的载体元素上。
<!--ja-->
標準的な台の表示 `Lδ` の基礎集合は `Lset δ` である。`At.result` はこれを始域とし、最後の定理は、基礎集合が同じ段階に等しい任意の台の要素へこの始域を輸送する。
<!--/-->

```agda
  Lδ : S
  Lδ = LsetS δ oδ
```

<!--en-->
The final comparison follows the chain `Lset δ ↪ Lset β ↪ M ↪ μ ↪ δ`. Its arrows come respectively from stage monotonicity using `δ ∈ β`, the inverse collapse, hull counting, and the assumed injection `μ ↪ δ`. Composing them proves `InjL Lδ δL`, the propositionally truncated existence of an internally coded injection from the stage at `δ` into `δ`.
<!--zh-->
最终比较沿链 `Lset δ ↪ Lset β ↪ M ↪ μ ↪ δ` 进行。四条箭头依次来自：利用 `δ ∈ β` 的层单调性、逆塌缩、壳计数，以及已知单射 `μ ↪ δ`。复合它们便证明 `InjL Lδ δL`，即从 `δ` 处的层到 `δ` 的内部编码单射在命题截断下存在。
<!--ja-->
最終の比較は鎖 `Lset δ ↪ Lset β ↪ M ↪ μ ↪ δ` に沿う。四つの矢印は順に、`δ ∈ β` を用いた段階の単調性、逆崩壊、包の計数、そして仮定された単射 `μ ↪ δ` から得られる。これらを合成すると `InjL Lδ δL`、すなわち `δ` の段階から `δ` への内部的に符号化された単射が命題的切り詰めのもとで存在することが示される。
<!--/-->

```agda
  result : InjL Lδ δL
  result = injl-trans Lδ St.Lβ δL
    (inclusion-coded Lδ St.Lβ (λ z hz → Lset-mono {α = St.β} {β = δ} δ∈β hz))
    (injl-trans St.Lβ St.hullL δL St.Lβ↪M
      (injl-trans St.hullL μ δL hull↪μ μ↪δ))
```
</div>
</details>


<!--en-->
For a general non-finite constructible ordinal `δ`, `cardOf` provides a cardinal representative only under propositional truncation. The proof works with a local representative `μ` inside the eliminator and applies `At.result`. This is legitimate because the target `InjL Lδ δ` is itself a propositionally truncated existence and hence a proposition. The resulting theorem is the stage-counting interface used later by both the GCH assembly and the bounded-subset argument; it proves only `Lset δ ↪ δ`, not GCH by itself.
<!--zh-->
对一般的非有限可构造序数 `δ`，`cardOf` 只在命题截断下给出基数代表。证明在消去器内部使用局部代表 `μ`，并应用 `At.result`。由于目标 `InjL Lδ δ` 本身是命题截断下的存在，因而是命题，这项消去合法。所得定理随后既作为 GCH 装配的层计数接口，也用于有界子集论证；它本身只证明 `Lset δ ↪ δ`，并不单独证明 GCH。
<!--ja-->
一般の有限でない構成可能順序数 `δ` に対し、`cardOf` は基数代表を命題的切り詰めのもとでのみ与える。証明は消去子の内部で局所的な代表 `μ` を用い、`At.result` を適用する。目標 `InjL Lδ δ` 自身が命題的に切り詰められた存在であり、したがって命題なので、この消去は正当である。得られる定理は、後で GCH の組み立てと有界部分集合の議論の双方に段階計数のインターフェースとして使われる。この定理だけが示すのは `Lset δ ↪ δ` であり、それ自体で GCH を証明するものではない。
<!--/-->

```agda
stage-counted : StageCountedCoded
stage-counted δ Lδ oδ δ∉ω q = rec₁ squash₁ build (cardOf δ oδ)
  where
  build : Σ[ μ ∈ S ]
            ( IsOrd (fst μ) × IsCardinalL μ
```

<!--en-->
A local `cardOf` witness records that `μ` is an ordinal and an internal cardinal, that its underlying set is contained in `δ`, and that coded injections exist in both directions. The containment proof is part of the representative package but is not needed by `At.result`; the construction uses the two injections together with ordinality, cardinality, and non-finiteness. Finally, `move` transports the source from the canonical `LsetS (fst δ) oδ` along `q : fst Lδ = Lset (fst δ)` to the presentation required by `StageCountedCoded`.
<!--zh-->
`cardOf` 的一个局部见证记录：`μ` 是序数和内部基数，其底层集包含于 `δ`，并且两个方向的编码单射都存在。包含性证明属于基数代表的数据包，但 `At.result` 并不使用它；该构造使用两条单射以及序数性、基数性和非有限性。最后，`move` 沿等式 `q : fst Lδ = Lset (fst δ)`，把始域从典范呈现 `LsetS (fst δ) oδ` 搬到 `StageCountedCoded` 所要求的呈现。
<!--ja-->
`cardOf` の局所的な証人は、`μ` が順序数かつ内部の基数であること、その基礎集合が `δ` に含まれること、そして両方向の符号化された単射が存在することを記録する。包含の証明は基数代表の組に含まれるが、`At.result` では使われない。この構成が使うのは、二つの単射と、順序数性、基数性、有限でないことである。最後に `move` は、等式 `q : fst Lδ = Lset (fst δ)` に沿って、始域を標準的な表示 `LsetS (fst δ) oδ` から `StageCountedCoded` が要求する表示へ移す。
<!--/-->

```agda
            × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst δ ⟩)
            × InjL δ μ × InjL μ δ )
        → InjL Lδ δ
  build (μ , oμ , cμ , μ⊆δ , δ↪μ , μ↪δ) =
    move (LsetS (fst δ) oδ) Lδ δ δ (sym q) refl
```

<!--en-->
It remains to justify the non-finiteness required by the hull-count theorem. If `μ ∈ ω`, the coded injection `δ ↪ μ` would inject the non-finite ordinal `δ` into a finite ordinal, contradicting `δ ∉ ω`; hence `μ ∉ ω`. With this last premise, `At.result` supplies exactly the propositionally truncated coded injection from the chosen presentation of `Lset δ` into `δ`.
<!--zh-->
最后还须证明壳计数定理要求的非有限性。若 `μ ∈ ω`，编码单射 `δ ↪ μ` 就会把非有限序数 `δ` 单射入有限序数，与 `δ ∉ ω` 矛盾；故 `μ ∉ ω`。有了这项最后前提，`At.result` 恰好给出从所选 `Lset δ` 呈现到 `δ` 的命题截断下的编码单射。
<!--ja-->
最後に、包の計数定理が要求する有限でないことを確認する。もし `μ ∈ ω` なら、符号化された単射 `δ ↪ μ` によって有限でない順序数 `δ` が有限順序数へ単射し、`δ ∉ ω` に反する。したがって `μ ∉ ω` である。この最後の前提により、`At.result` は選ばれた `Lset δ` の表示から `δ` への、命題的に切り詰められた符号化単射をちょうど与える。
<!--/-->

```agda
      (At.result δ oδ δ∉ω μ oμ cμ μ∉ω δ↪μ μ↪δ)
    where
    μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → ⊥₀
    μ∉ω h = no-fin δ μ oδ δ∉ω oμ h δ↪μ
```
