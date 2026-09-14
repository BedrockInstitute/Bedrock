<!--en-->
# Composition and inclusion of coded injections

This chapter develops two constructions of coded injections inside `L` and proves one exclusion. First, two coded injections compose: the composite is the graph relating `x` to `z` when some intermediate `y` has `(x, y)` in the first graph and `(y, z)` in the second. Second, an inclusion of sets is coded by the identity map on the smaller set, whose graph is the set of ordered pairs defined by equality: the pairs `(x, y)` with `y = x`. Finally, no injection exists from `ω` into the square of a finite ordinal.
<!--zh-->
# 编码单射的复合与包含

本章在 `L` 内部发展两种编码单射的构造，并证明一个排除。其一，两个编码单射的复合：当某个中间值 `y` 使 `(x, y)` 落在第一个图、`(y, z)` 落在第二个图时，复合图把 `x` 关联到 `z`。其二，集合的包含由较小集合上的恒等映射编码，其图是由相等定义的有序对集合：即满足 `y = x` 的那些对 `(x, y)`。最后，从 `ω` 到有限序数平方的单射不存在。
<!--ja-->
# 符号化された単射の合成と包含

本章は、`L` の内部で符号化された単射の構成を二つ発展させ、一つの排除を証明します。第一に、二つの符号化された単射の合成です。ある中間の `y` が `(x, y)` を最初のグラフに、`(y, z)` を第二のグラフに持つとき、合成のグラフは `x` を `z` に関係付けます。第二に、集合の包含は、小さい方の集合上の恒等写像によって符号化されます。そのグラフは、等号で定義される順序対の集合、すなわち `y = x` を満たす対 `(x, y)` の全体です。最後に、`ω` から有限順序数の平方への単射は存在しません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.InjectionComposition {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Properties and applications of graphs are expressed by formulas of the model language. Each variable slot is read against a list of elements, and satisfaction is the semantics of the structures. Two structures are in play. The ambient hierarchy supplies the sets; the constructible structure supplies the carrier inside which the graphs live and are read.
<!--zh-->
图的性质与应用由模型语言的公式表达。每个变元空位对照一列元素读取，满足关系即结构的语义。这里有两个结构。外围层级提供集合本身；可构造结构提供图所居、被读取的载体。
<!--ja-->
グラフの性質と適用は、モデル言語の論理式によって表されます。各変数の枠は要素の列に対して読まれ、充足が構造の意味論となります。二つの構造が現れます。周囲の階層が集合を供給し、構成可能構造がグラフの住み、読まれる台を供給します。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
Ordered pairs of ambient sets are coded by a pairing operation whose two components are recoverable: equal codes have equal components. Small sets come with presentations, an index type embedded into the hierarchy, so that facts about presented elements transfer to facts about indices. Constructibility is a predicate with downward closure along membership: a member of a constructible set is constructible.
<!--zh-->
外围集合的有序对由一个配对运算编码，其两个分量皆可恢复：相等的码有相等的分量。小集合带有呈现，即嵌入层级的索引类型，因此关于被呈现元素的事实可转移为关于索引的事实。可构造性是沿隶属向下封闭的谓词：可构造集合的成员是可构造的。
<!--ja-->
周囲の集合の順序対は、二つの成分が復元できる対の演算で符号化されます。等しい符号は等しい成分をもちます。小さな集合には提示が伴い、階層へ埋め込まれた索引型によって、提示された要素についての事実が索引についての事実へ移ります。構成可能性は、所属に沿って下方閉な述語です。構成可能な集合の要素は構成可能です。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
```

<!--en-->
Four materials carry the chapter. The ordinal `ω` with the fact that its members are exactly the numerals. The finite dictionary between numerals and finite sets, with its abstract chase argument. The small-domain principle, which bounds any small family of constructible sets by a single stage. And separation inside `L`, available for formulas of arbitrary complexity, which carves every relation below out of a shared bound.
<!--zh-->
四项材料支撑全章。序数 `ω`，连同「其成员恰为数码」的事实。数码与有限集之间的有限词典，及其抽象追逐论证。小域原理：把由可构造集合组成的任何小族界于单一层。以及 `L` 内部的分离，对任意复杂度的公式可用，下文的每个关系都由此从公共界中刻出。
<!--ja-->
四つの材料が本章を支えます。序数 `ω` と、その要素がちょうど数項であるという事実。数項と有限集合の間の有限の対応辞と、その抽象的な追跡論法。小さな定義域の原理、すなわち構成可能集合の小さな族を一つの段階で抑えるもの。そして `L` 内部の分出であり、任意の複雑さの論理式に使えるので、以下のどの関係も共有の上界から刻み出されます。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
```

<!--en-->
Inside `L`, the application atoms of the language are read at constants: a graph applied to arguments is again a formula, and this reading is faithful. The three formula conditions of an injection each have an introduction and an elimination form under these atoms. A coded injection can also be read back as a genuine function between the presentations of its domain and codomain.
<!--zh-->
在 `L` 内部，语言的应用原子在常元处读取：图施于参数后仍是公式，且该读取是忠实的。单射的三条公式条件在这些原子下各有引入与消去两种形式。编码单射还可读回为其定义域与陪域的呈现之间的真正函数。
<!--ja-->
`L` の内部では、言語の適用のアトムは定数のもとで読まれます。グラフに引数を適用したものは再び論理式であり、この読みは忠実です。単射の三つの論理条件は、これらのアトムのもとでそれぞれ導入と除去の形をもちます。符号化された単射は、定義域と終域の提示の間の本物の関数として読み戻すこともできます。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Model {ℓ} using ( appC; appC-adequate ) public
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-out; injAt-in; module Small )
```

<!--en-->
The code of an injection is the graph together with all four conditions: single-valuedness, domain totality, and injectivity as formulas read over the domain, plus the range clause stated in the meta-language. The internal injection relation `InjL`{.Agda} asserts, merely, that such a graph with its four conditions exists. The definable-injection construction converts a map given with a defining formula into such a code.
<!--zh-->
单射的码是图连同全部四项条件：单值性、定义域上的全域性、单射性作为在定义域上读取的公式，外加以元语言陈述的值域条款。内部单射关系 `InjL`{.Agda} 仅仅地断言：这样的图连同其四项条件存在。可定义单射构造把连同定义公式一起给出的映射变成这样的码。
<!--ja-->
単射の符号とは、グラフに四条件のすべてを合わせたものです。すなわち、定義域の上で読まれる論理式としての一価性・定義域の全域性・単射性と、メタ言語で述べられる値域の条項です。内部単射の関係 `InjL`{.Agda} は、そのようなグラフと四条件が、単に、存在すると主張します。定義可能な単射の構成は、定義の論理式とともに与えられた写像をそのような符号へ変えます。
<!--/-->

```agda
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.DefinableInjection {ℓ} lem
  using ( DefinableMap ) renaming ( module Inj to DefinableInj )

```

<!--en-->
Internal existence is asserted through propositional truncation: a statement holds without a selected witness, and truncated statements eliminate only into propositions. The empty type and the natural numbers bound the finite argument below from both sides.
<!--zh-->
内部存在经命题截断来断言：陈述成立而无需选定见证，截断后的陈述只能消去到命题。空类型与自然数从两端抑住下文的有限论证。
<!--ja-->
内部の存在は命題的切り詰めによって主張されます。主張は証人を選ばずに成り立ち、切り詰められた主張は命題へしか消去できません。空の型と自然数が、後の有限の議論を両側から抑えます。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
```

<!--en-->
Some proofs move both components of a pair at once, and a two-place transport serves them. Between the presentation types of two sets, an equivalence carries functions and injections across; a path between sets yields such an equivalence. The ambient hierarchy is the carrier on which every membership statement of the chapter is read.
<!--zh-->
有的证明让一对的两个分量同时变动，二元的搬运正为此服务。在两个集合的呈现类型之间，等价把函数与单射搬运过去；集合之间的路径给出这样的等价。外围层级是本章一切成员陈述所读取的载体。
<!--ja-->
一つの証明が対の両成分を同時に動かすことがあり、二項の輸送がこれに仕えます。二つの集合の提示型の間では、同値が関数と単射を運び、集合の間のパスがそのような同値を与えます。周囲の階層は、本章のすべての所属の主張が読まれる台です。
<!--/-->

```agda
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Foundations.Equiv as Equiv
open Equiv using ( equivFun; invEq; retEq; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
The hierarchy builds successors and limits alike: the successor operation adds one element to a set, and the infinity set `ω` collects the numerals, one per finite ordinal.
<!--zh-->
层级同样地构造后继与极限：后继运算向集合添入一个元素，无穷集合 `ω` 收集诸数码，每个有限序数一个。
<!--ja-->
階層は後続も極限も同じように構成します。後続の演算は集合に一つの要素を加え、無限集合 `ω` は数項、有限順序数ごとに一つを集めます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
```

<!--en-->
Presentations pair index types with embeddings into the hierarchy, and their fibers move facts between elements and indices. A proposition-valued existential quantifier states the domain condition used by the composite.
<!--zh-->
呈现把索引类型与到层级的嵌入配成一对，其纤维在元素与索引之间搬运事实。取值于命题的存在量词陈述复合所用的定义域条件。
<!--ja-->
提示は索引型と階層への埋め込みを対にし、その繊維が要素と索引の間で事実を運びます。命題値の存在量化子が、合成が使う定義域の条件を述べます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )

```

<!--en-->
The constructible carrier is opened under the name on which every set of the chapter lives. From the absoluteness development come two readings: satisfaction at the constructible structure, renamed for local use, and its raised form, in which an atom is evaluated at a list of constants. Every application of a graph to arguments below goes through the raised reading.
<!--zh-->
可构造载体以本章一切集合所居之名打开。绝对性一章带来两种读法：在可构造结构处的满足 (为本地使用而改名)，及其抬升形式，即原子在常元列表处求值。下文图的一切应用都经过这一抬升读法。
<!--ja-->
構成可能な台は、本章のすべての集合の住む名前で開かれます。絶対性の展開からは二つの読みが来ます。構成可能構造での充足、これを局所の使用のために改名したもの、そしてその持ち上げられた形、すなわちアトムを定数の列のもとで評価する形です。以下のグラフの適用はすべて、この持ち上げられた読みを通します。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )


```

<!--en-->
The finite side opens its numeral dictionary and its abstract chase, both stated in a form that this chapter only instantiates.
<!--zh-->
有限一侧打开其数码词典与抽象追逐，二者都以本章只需例示的形式陈述。
<!--ja-->
有限の側は、数項の対応辞と抽象的な追跡を開きます。どちらも、本章が具体化するだけの形で述べられています。
<!--/-->

```agda
open FiniteBase using ( ω-mem→numeral; toFin; toFin-inj; fromFin; fromFin-inj )
open FiniteBase using ( module AbstractChase )
```

<!--en-->
## A common constructible bound

Carving a relation by separation needs its candidates to lie in one constructible set. The shared device accepts any small indexed family `g : I → S` and returns a constructible set containing every `g i`. The later `PairBound` specializes it to the ordered pairs arising from a chosen domain and codomain.
<!--zh-->
## 共同的可构造界

用分离刻出关系，需要候选元素落在同一个可构造集合中。共享装置接收任意小索引族 `g : I → S`，返回包含每个 `g i` 的可构造集合；稍后的 `PairBound` 才把它例示于由选定定义域与陪域产生的有序对。
<!--ja-->
## 共通の構成可能な上界

分出で関係を刻むには、候補となる要素が一つの構成可能集合の中になければなりません。共有の装置は任意の小さな添字族 `g : I → S` を受け取り、各 `g i` を含む構成可能集合を返します。後の `PairBound` で初めて、選んだ定義域と終域から生じる順序対に具体化します。
<!--/-->

```agda
module StageBound (I : Type ℓ) (g : I → S) where

  opaque
    bnd : S
    bnd = smallDom I g .fst

```

<!--en-->
The reader states the bound's purpose directly: each member of the family, read as an ambient element, belongs to the bound. Every pair later admitted to a `Relation` reaches the bound through this reader.
<!--zh-->
读取器直接陈述界的用途：族的每个成员按外围元素读取时都属于该界。此后每个被纳入 `Relation` 的对都经此读取器进入该界。
<!--ja-->
読み手は上界の目的をそのまま述べます。族の各構成員は、周囲の要素として読めば上界に属します。後で `Relation` に入れられる各対は、この読み手を通して上界に入ります。
<!--/-->

```agda
    below : (i : I) → ⟨ fst (g i) ∈ fst bnd ⟩
    below = smallDom I g .snd
```

<!--en-->
## Excluding finite targets

The exclusion reads: no injection exists from `ω` into the square of a finite ordinal. The route avoids the internal membership of `ω` almost entirely. What is used is that every member of `ω` is, merely, a numeral; that each numeral presents a finite set with an injective dictionary in both directions; and an abstract chase which, given injections from each finite presentation into a fixed type and an injection from that fixed type into the square of one finite presentation, derives an injection from a larger finite set into a smaller one.
<!--zh-->
## 排除有限目标

后文所需的有限排除取如下形式：从 `ω` 到有限序数平方的单射不存在。这条路线几乎完全避开 `ω` 的内部隶属。所用到的只是：`ω` 的每个成员仅仅地是某个数码；每个数码呈现一个有限集，且词典在两个方向上都单射；以及一条抽象追逐。给定从每个有限呈现到某个固定类型的单射、再给定从该固定类型到某个有限呈现之平方的单射，便导出从较大有限集到较小有限集的单射。
<!--ja-->
## 有限な終域の排除

後に使う有限の排除は次の形を取ります。`ω` から有限順序数の平方への単射は存在しません。道は `ω` の内部の所属をほとんど避けます。使うのは、`ω` の各要素が単にある数項であること、各数項が有限集合を提示し対応辞が両方向で単射であること、そして抽象的な追跡です。各有限の提示から固定された型への単射と、その固定型からある有限の提示の平方への単射が与えられれば、大きい有限集合から小さい有限集合への単射が導かれます。
<!--/-->

<!--en-->
A fact about `ω` itself, at the strength the membership predicate supports: a member of `ω` is, merely, a numeral, and the successor of the numeral `n` is again a numeral, hence again a member. The identification of `γ` with its numeral is transported along the successor.
<!--zh-->
关于 `ω` 自身的一条事实，取其隶属谓词所能支撑的强度：`ω` 的成员仅仅地是某个数码，而数码 `n` 的后继仍是数码，因而仍是成员。`γ` 与其数码的同一视沿后继搬运。
<!--ja-->
`ω` 自身についての事実であり、所属の述語が支える強さでのものです。`ω` の要素は、単に、ある数項であり、数項 `n` の後続は再び数項、したがって再び要素です。`γ` とその数項の同一視は後続に沿って輸送されます。
<!--/-->

```agda
ω-limit : (γ : V ℓ) → ⟨ γ ∈ ω ⟩ → ⟨ sucV γ ∈ ω ⟩
ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ ω)) go (ω-mem→numeral γ γ∈ω)
  where
  go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ ω ⟩
  go (n , p) = subst (λ w → ⟨ sucV w ∈ ω ⟩) (sym p) (#∈ω (suc n))
```

<!--en-->
The numerals embed into the presentation of `ω`, and the route is direct. An index of the presentation of the numeral `m` names an element of that numeral; the numeral belongs to `ω`, and by transitivity of `ω` the named element belongs to `ω` as well; the fiber of the presentation of `ω` at that element returns the index of the presentation of `ω` that presents it.
<!--zh-->
诸数码嵌入 `ω` 的呈现，路线是直接的。数码 `m` 的呈现的一个索引指名该数码的一个元素；该数码属于 `ω`，而由 `ω` 的传递性，被指名的元素也属于 `ω`；取 `ω` 的呈现在该元素处的纤维，即得呈现它的那个 `ω` 呈现索引。
<!--ja-->
数項は `ω` の提示へ埋め込まれます。道すじは直接です。数項 `m` の提示の索引は、その数項の要素を名指します。その数項は `ω` に属し、`ω` の推移性により、名指された要素も `ω` に属します。`ω` の提示のその要素での繊維を取れば、それを提示する `ω` の提示の索引が得られます。
<!--/-->

```agda
numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

```

<!--en-->
The embedding is injective. If two indices of the same numeral have equal images in the presentation of `ω`, the two fiber identifications convert the equality of images into an equality of the presented elements inside that numeral; and since the numeral's own presentation is injective, the indices coincide.
<!--zh-->
嵌入是单射的。若同一数码的两个索引在 `ω` 的呈现中取值相等，两条纤维的同一视就把像的相等换成该数码内部被呈现元素的相等；而数码自身的呈现是单射的，故两个索引重合。
<!--ja-->
埋め込みは単射です。同じ数項の二つの索引が `ω` の提示の中で等しい値をもつなら、二つの繊維の同一視が、像の等しさをその数項の内部の提示された要素の等しさへ変えます。そして数項自身の提示は単射なので、二つの索引は一致します。
<!--/-->

```agda
numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                   → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
  (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
    ∙ cong (⟪ ω ⟫↪) e
```

<!--en-->
The only injectivity fact used on the `ω` side is that of the numeral's presentation.
<!--zh-->
`ω` 一侧用到的单射事实只有数码呈现的单射性。
<!--ja-->
`ω` の側で使われる単射の事実は、数項の提示の単射性だけです。
<!--/-->

```agda
    ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)
```

<!--en-->
The chase is a statement of the metatheory about presentation index types; it is not the internal injection relation. Its assumptions are, first, that for each numeral `n` the presentation type `⟪ # n ⟫` and the finite set `Fin n` admit injections in each direction, each injective on its own; second, that every `⟪ # m ⟫` admits an injection into the fixed type `⟪ ω ⟫`. Its conclusion: an injection from `⟪ ω ⟫` into `⟪ # n ⟫ × ⟪ # n ⟫` is impossible.
<!--zh-->
追逐是元理论层面关于呈现索引类型的陈述，并非内部单射关系。其假设有二：其一，对每个数码 `n`，呈现类型 `⟪ # n ⟫` 与有限集 `Fin n` 之间在两个方向各有一个单射，各自单射；其二，每个 `⟪ # m ⟫` 都有到固定类型 `⟪ ω ⟫` 的单射。其结论：从 `⟪ ω ⟫` 到 `⟪ # n ⟫ × ⟪ # n ⟫` 的单射不可能存在。
<!--ja-->
追跡は、提示の索引型についてのメタ理論の主張であり、内部の単射の関係ではありません。仮定は二つです。第一に、各数項 `n` について、提示の型 `⟪ # n ⟫` と有限集合 `Fin n` の間に両方向の単射があり、それぞれの向きがそれ自身として単射であること。第二に、すべての `⟪ # m ⟫` から固定された型 `⟪ ω ⟫` への単射があること。結論は、`⟪ ω ⟫` から `⟪ # n ⟫ × ⟪ # n ⟫` への単射は不可能だ、ということです。
<!--/-->

```agda
no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
no-inj-finite-ω n f finj =
```

<!--en-->
The abstract argument consumes exactly the dictionaries and the family of injections into the fixed type. Its core is the pigeonhole count: an injection from `Fin (suc (n · n))` into `Fin (n · n)` cannot exist, and the chase reduces the assumed injection to precisely that shape.
<!--zh-->
抽象论证恰好消耗那两本词典与到固定类型的单射族。其核心是鸽笼计数：从 `Fin (suc (n · n))` 到 `Fin (n · n)` 的单射不存在，而追逐把所设单射化归为恰是这一形状。
<!--ja-->
抽象的な議論が消費するのは、対応辞と、固定型への単射の族です。その中心は鳩の巣の数え上げです。`Fin (suc (n · n))` から `Fin (n · n)` への単射は存在せず、追跡は仮定された単射をまさにその形へ帰着させます。
<!--/-->

```agda
  AbstractChase.NoInj.no-inj
    (λ n → ⟪ # n ⟫)
    toFin toFin-inj
    fromFin fromFin-inj
    (⟪ ω ⟫)
```

<!--en-->
The chapter only has to hand over the numerals' dictionary and the embedding into the presentation of `ω`.
<!--zh-->
本章只需交出数码的词典与到 `ω` 呈现的嵌入。
<!--ja-->
本章が渡すべきは、数項の対応辞と `ω` の提示への埋め込みだけです。
<!--/-->

```agda
    (numeral-into-ω)
    (numeral-into-ω-inj)
    n f finj
```

<!--en-->
The clause lifts the exclusion to an arbitrary finite ordinal, and it stays at the level of presentation index types, in the shape of the chase: here the fixed type is `⟪ ω ⟫` and the finite presentations are the `⟪ # n ⟫`.
<!--zh-->
该条款把排除提升到任意有限序数，且始终停留在呈现索引类型层面，保持追逐的形状：此处固定类型是 `⟪ ω ⟫`，有限呈现是诸 `⟪ # n ⟫`。
<!--ja-->
この条項は排除を任意の有限順序数へ持ち上げます。しかも追跡の形のまま、提示の索引型の水準にとどまります。ここで固定された型は `⟪ ω ⟫`、有限の提示は诸 `⟪ # n ⟫` です。
<!--/-->

```agda
finite-excl-ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩
              → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
finite-excl-ω β oβ β∈ω f finj =
  PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
```

<!--en-->
Let `β` be an ordinal member of `ω`, and let a function from the presentation of `ω` to the square of the presentation of `β` be injective; the claim is a contradiction.
<!--zh-->
设 `β` 是 `ω` 的序数成员，并设从 `ω` 的呈现到 `β` 之呈现的平方的函数为单射；要证的是矛盾。
<!--ja-->
`β` を `ω` の順序数の要素とし、`ω` の提示から `β` の提示の平方への関数が単射だとします。主張は矛盾であり、
<!--/-->

```agda
  where
```

<!--en-->
Membership of `β` in `ω` yields, merely, a numeral with which `β` is identified, so it is enough to refute the numeral case; the truncation is eliminated into the empty type, which is a proposition.
<!--zh-->
`β` 属于 `ω` 仅仅地给出一个与 `β` 同一视的数码，故只需对数码情形导出反驳；截断消去到空类型，而空类型是命题。
<!--ja-->
`β` の `ω` への所属は、`β` と同一視される数項を単に与えます。したがって数項の場合を反証すれば十分で、切り詰めは空の型へ消去されます。空の型は命題です。
<!--/-->

```agda
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = no-inj-finite-ω n f' finj'
    where
```

<!--en-->
The identification is a path between sets, and squaring the path gives an equivalence between the two squared presentations. The assumed function is composed with this equivalence, and its injectivity transfers along the equivalence's unit laws: if the transported function identified two inputs, the original would identify them too.
<!--zh-->
该同一视是集合之间的路径，对路径取平方便得两个平方呈现之间的等价。所设函数与该等价复合，其单射性沿等价的单位律转移：若被搬运的函数等同了两个输入，原来的函数也会等同它们。
<!--ja-->
この同一視は集合の間のパスであり、パスを平方すると二つの平方の提示の間の同値が得られます。仮定された関数はこの同値と合成され、その単射性は同値の単位則に沿って移ります。輸送された関数が二つの入力を同一視するなら、元の関数も同一視します。
<!--/-->

```agda
    e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
    e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
    f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
    f' x = equivFun e (f x)
    finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
```

<!--en-->
The chase then applies at the numeral, and its contradiction is of the stated pigeonhole shape, an injection from `Fin (suc (n · n))` into `Fin (n · n)`.
<!--zh-->
于是追逐施于该数码，其矛盾正是所述鸽笼形状：从 `Fin (suc (n · n))` 到 `Fin (n · n)` 的单射。
<!--ja-->
こうして追跡は数項に適用され、その矛盾は述べた鳩の巣の形、すなわち `Fin (suc (n · n))` から `Fin (n · n)` への単射です。
<!--/-->

```agda
    finj' x y e' = finj x y
      (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))
```

<!--en-->
## Relations as bounded pair graphs

A relation between two sets of `L` will be a set of coded ordered pairs. The bound enumerates its pairs before any formula appears: the index type is the product of one presentation index from the domain and one from the codomain.
<!--zh-->
## 有界有序对图所呈现的关系

`L` 中两个集合之间的关系将成为编码有序对组成的集合。界在任何公式出现之前就枚举了这些对：索引类型是定义域的一个呈现索引与陪域的一个呈现索引之积。
<!--ja-->
## 有界な順序対グラフとしての関係

`L` の二つの集合の間の関係は、符号化された順序対の集合になります。上界はどの論理式が現れるより先に、対を数え上げます。索引型は、定義域からの提示の索引と終域からの索引の積です。
<!--/-->

```agda
module PairBound (D C : S) where

  Ix : Type ℓ
  Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫

```

<!--en-->
Each presentation index is realized as an element of the carrier: the presented set, which is constructible because it is a member of the constructible set `D` or `C`, the constructibility being transported down along membership.
<!--zh-->
每个呈现索引被实现为载体的元素：即那个被呈现的集合；它是可构造集合 `D` 或 `C` 的成员，可构造性沿隶属向下搬运。
<!--ja-->
各提示の索引は台の要素として実現されます。それは提示された集合であり、構成可能な集合 `D` または `C` の要素なので、所属に沿って構成可能性が降ろされます。
<!--/-->

```agda
  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
```

<!--en-->
One L-element per index, on each side.
<!--zh-->
每一侧各为每个索引产生一个 L 元素。
<!--ja-->
それぞれの側で、索引ごとに一つの L 要素です。
<!--/-->

```agda
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

```

<!--en-->
The family sends each pair of indices to the coded ordered pair of the two realized elements, and the shared bound device is applied once to this family: one constructible set contains every coded pair that can arise from `D` and `C`.
<!--zh-->
该族把每对索引送到两个实现元素的编码有序对，共享界装置对这个族一次施用：一个可构造集合包含由 `D` 与 `C` 可能产生的一切编码对。
<!--ja-->
この族は、索引の各対を、実現された二要素の符号化された順序対へ送ります。共有の上界の装置がこの族に一度だけ施され、一つの構成可能集合が `D` と `C` から生じうるすべての符号化された対を含みます。
<!--/-->

```agda
    pw : Ix → S
    pw (m , k) = prʟ (toD m) (toC k)

    module SB = StageBound Ix pw
```

<!--en-->
The bound is read off the device and used from here on only through membership; nothing below needs its construction.
<!--zh-->
界从该装置读出，此后只通过隶属使用；下文无需其构造。
<!--ja-->
上界は装置から読み出され、以降は所属を通してのみ使われます。以下でその構成は必要とされません。
<!--/-->

```agda
  bnd : S
  bnd = SB.bnd

```

<!--en-->
The reader extends the bound beyond presentations: for arbitrary elements `x` of `D` and `z` of `C`, not given by indices, their coded pair still lies in the bound. This is the form in which every later construction touches the bound.
<!--zh-->
读取器把界扩展到呈现之外：对 `D` 的任意元素 `x` 与 `C` 的任意元素 `z`，即便不由索引给出，其编码对仍在界内。此后每个构造触及界用的都是这个形式。
<!--ja-->
読み手は上界を提示の外へ広げます。`D` の任意の要素 `x` と `C` の任意の要素 `z` は、索引で与えられなくても、その符号化された対が上界の中にあります。以降のどの構成も、この形で上界に触れます。
<!--/-->

```agda
  below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
        → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩
  below x z mx mz = subst (λ w → ⟨ w ∈ fst bnd ⟩) pa (SB.below i)
    where
```

<!--en-->
Since `D` and `C` are presented, each of the two elements has a fiber: an index whose presented set is identified with the element. The two fibers are taken independently.
<!--zh-->
由于 `D` 与 `C` 是被呈现的，两个元素各有纤维：一个索引，其被呈现集合与该元素被等同。两条纤维各自独立取得。
<!--ja-->
`D` と `C` は提示されているので、二つの要素はそれぞれ繊維をもちます。提示された集合がその要素と同一視される索引です。二つの繊維は独立に取られます。
<!--/-->

```agda
    fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
    fD = fiber (fst D) mx
    fC : Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst z)
    fC = fiber (fst C) mz
```

<!--en-->
The two indices form one index of the bound's family, whose value is the coded pair of the presented elements; along the two fiber paths this equals the coded pair of `x` and `z`. Transporting membership along that equality finishes the reader.
<!--zh-->
两个索引构成界的族的一个索引，族在该索引处的取值是被呈现元素们的编码对，沿两条纤维路径它等于 `x` 与 `z` 的编码对。沿该相等搬运隶属，读取器即告完成。
<!--ja-->
二つの索引は上界の族の一つの索引となり、その索引での族の値は提示された要素たちの符号化された対で、二つの繊維のパスに沿って `x` と `z` の符号化された対と等しくなります。その等しさに沿って所属を輸送すれば、読み手は完了します。
<!--/-->

```agda
    i : Ix
    i = fD .fst , fC .fst
    pa : fst (pw i) ≡ pr (fst x) (fst z)
    pa = prʟ-fst (toD (fD .fst)) (toC (fC .fst))
       ∙ cong₂ pr (fD .snd) (fC .snd)
```

<!--en-->
A relation is carved from the bound given three data: a formula in three slots and a host predicate `P` on pairs, with adequacy in both directions. The reading order of the formula is value, index, pair: at the environment `y ∷ x ∷ e`, the formula is read as `P x y`.
<!--zh-->
从界中刻出关系需要三份数据：一个三空位公式，以及定义在有序对上的宿主谓词 `P`，连同两个方向的充分性。公式的读取次序是值、索引、对：在环境 `y ∷ x ∷ e` 下，该公式被读作 `P x y`。
<!--ja-->
上界から関係を刻むのに三つのデータが要ります。三つの枠をもつ論理式と、対の上の述語 `P`、そして両方向の妥当性です。論理式の読みの順は値、添字、対です。環境 `y ∷ x ∷ e` のもとで、論理式は `P x y` として読まれます。
<!--/-->

```agda
module Relation (D C : S) (φ : Formula S 3) (P : S → S → hProp (ℓ-suc ℓ))
                (read : (x y e : S) → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩ → ⟨ P x y ⟩)
                (fill : (x y e : S) → ⟨ P x y ⟩ → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩) where

```

<!--en-->
The carving formula quantifies the two slots existentially, and besides the given formula it asserts, in the object language, that the third slot codes the ordered pair of the first two. Separation at the shared bound, applied to this one-slot formula, returns the relation as an element of `L`.
<!--zh-->
刻画公式对两个空位作存在量化，并且除给定公式外，还在对象语言中断言第三空位编码前两者的有序对。共享界上的分离施于这个单空位公式，返回作为 `L` 元素的关系。
<!--ja-->
刻むための論理式は、二つの枠を存在量化し、さらに与えられた論理式に加えて、第三の枠が最初の二つの順序対を符号化することを対象言語の中で主張します。共有の上界での分出をこの一枠の論理式に施すと、関係が `L` の要素として返ります。
<!--/-->

```agda
  opaque
    fo : Formula S 1
    fo = ∃̇ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ φ))

    rel : S
    rel = hasSeparationL (PairBound.bnd D C) fo .fst .fst

```

<!--en-->
The backward reading turns membership into truncated data about a pair. A member `e` of the relation satisfies the carving formula by the separation specification; the two existentials unwrap to components `x` and `y` with a proof that `e` codes their pair, restored to the coding operation's own form by adequacy, and the formula part is read into `P x y`.
<!--zh-->
反向读取把隶属换成关于某一对的截断数据。关系的成员 `e` 由分离规格满足刻画公式；两层存在量化解开得到分量 `x`、`y`，以及「`e` 编码其对子」的证明，经充分性恢复为编码运算自身的形式，而公式部分被读成 `P x y`。
<!--ja-->
逆の読みは、所属を一つの対についての切り詰められたデータへ変えます。関係の要素 `e` は分出の仕様により刻むための論理式を満たします。二つの存在量化が解けて成分 `x` と `y` が現れ、`e` がその対を符号化することの証明が、妥当性によって符号化の演算自身の形に戻され、論理式の部分は `P x y` へ読み替えられます。
<!--/-->

```agda
    out : (e : S) → ⟨ fst e ∈ fst rel ⟩
        → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] ((fst e ≡ pr (fst x) (fst y)) × ⟨ P x y ⟩) ∥₁
    out e h = PT.rec squash₁ (λ { (x , hx) → PT.map
      (λ { (y , q , hy) → x , y
         , subst ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ e ∷ [])) q
```

<!--en-->
Everything is truncated, matching the form in which the relation will be consumed.
<!--zh-->
一切都是截断的，与该关系日后被消耗的形式一致。
<!--ja-->
すべて切り詰められており、この関係が後に消費される形と一致します。
<!--/-->

```agda
         , read x y e hy }) hx })
      (subst ⟨_⟩ (hasSeparationL (PairBound.bnd D C) fo .fst .snd e) h .snd)

```

<!--en-->
The forward direction builds membership from the predicate.
<!--zh-->
正向由谓词构造隶属。
<!--ja-->
順方向は述語から所属を作ります。
<!--/-->

```agda
    into : (x y : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst y ∈ fst C ⟩ → ⟨ P x y ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩
    into x y mx my h = subst (λ w → ⟨ w ∈ fst rel ⟩) (prʟ-fst x y)
      (subst ⟨_⟩ (sym (hasSeparationL (PairBound.bnd D C) fo .fst .snd (prʟ x y)))
        ( subst (λ w → ⟨ w ∈ fst (PairBound.bnd D C) ⟩) (sym (prʟ-fst x y))
```

<!--en-->
The coded pair of `x` and `y` lies in the shared bound by the bound's reader; the coding clause of the formula holds by the coding operation's computation, and the given formula holds by adequacy; separation certifies membership, transported along the coding's definitional equality.
<!--zh-->
`x` 与 `y` 的编码对由界的读取器进入共享界；公式的编码条款由编码运算的计算成立，给定公式由充分性成立；分离给出隶属，并沿编码的定义性相等搬运。
<!--ja-->
`x` と `y` の符号化された対は、上界の読み手によって共有の上界に入ります。論理式の符号化の条項は符号化の演算の計算で成り立ち、与えられた論理式は妥当性で成り立ちます。分出が所属を証明し、符号化の定義的な等しさに沿って輸送されます。
<!--/-->

```agda
            (PairBound.below D C x y mx my)
        , ∣ x , ∣ y
          , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ prʟ x y ∷ [])))
              (prʟ-fst x y)
          , fill x y (prʟ x y) h ∣₁ ∣₁ ))

```

<!--en-->
For the genuine coded pair of `x` and `y`, the backward reading sharpens to an untruncated conclusion.
<!--zh-->
对 `x` 与 `y` 的真实编码对，反向读取可锐化为非截断的结论。
<!--ja-->
`x` と `y` の本来の符号化された対に対しては、逆の読みは切り詰めのない結論へ鋭くなります。
<!--/-->

```agda
  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩ → ⟨ P x y ⟩
  pair-out x y h = PT.rec (snd (P x y))
    (λ { (x' , y' , q , h') →
      subst2 (λ a b → ⟨ P a b ⟩)
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .fst)))
```

<!--en-->
Its witness presents `e` as the coded pair of some `x'` and `y'`; injectivity of the coding identifies the underlying elements of `x'` with those of `x` and of `y'` with those of `y`; and since constructibility is a proposition, these underlying equalities lift to equalities of carrier elements. The predicate is then transported exactly to `P x y`.
<!--zh-->
其见证把 `e` 呈现为某对 `x'`、`y'` 的编码对；编码的单射性把 `x'` 的底层元素等同于 `x` 的底层元素、`y'` 的等同于 `y` 的；又因可构造性是命题，这些底层等式提升为载体元素的等式。谓词随即被恰好搬到 `P x y`。
<!--ja-->
その証人は `e` をある `x'` と `y'` の符号化された対として提示します。符号化の単射性により、`x'` の底の要素は `x` のそれと、`y'` の底の要素は `y` のそれと同一視されます。さらに構成可能性は命題なので、これらの底の等しさは台の要素の等しさへ持ち上がります。述語は、ちょうど `P x y` の場所へ輸送されます。
<!--/-->

```agda
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .snd))) h' })
    (out (prʟ x y) (subst (λ w → ⟨ w ∈ fst rel ⟩) (sym (prʟ-fst x y)) h))
```

<!--en-->
## Composing coded injections

Two coded injections compose when the codomain of the first is the domain of the second. The composite is again a graph, and its verification never re-runs replacement: both input graphs already exist as sets, and the composite is a relation separated inside a shared bound. The module receives the two graphs with three reading conditions each.
<!--zh-->
## 复合编码单射

第一个的陪域是第二个的定义域时，两个编码单射可以复合。复合物仍是图，其验证从不重跑替换：两个输入图已作为集合存在，复合物只是从共享界内分离出的一个关系。模块收取两个图，以及各自的三条读取条件。
<!--ja-->
## 符号化された単射の合成

最初の終域が第二の定義域であるとき、二つの符号化された単射は合成できます。合成物もまたグラフであり、その検証は置換をやり直しません。二つの入力グラフはすでに集合として存在し、合成物は共有の上界の中で分出された一つの関係です。モジュールは二つのグラフと、それぞれ三つの読みの条件を受け取ります。
<!--/-->

```agda
module Comp (D E C F H : S)
            (svF : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
            (dmF : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijF : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
```

<!--en-->
Besides the three reading conditions, each graph carries its range clause as a separate assumption of the module: every coded pair of the first graph has its value in the middle set, and every coded pair of the second has its value in the final codomain.
<!--zh-->
除三条读取条件外，每个图还以模块的独立假设携带值域条款：第一个图的每个编码对的取值落在中间集合，第二个图的每个编码对的取值落在最终陪域。
<!--ja-->
三つの読みの条件に加えて、各グラフは値域の条項をモジュールの独立な仮定として運びます。最初のグラフの各符号化された対の値は中間の集合にあり、第二のグラフの各対の値は最終の終域にあります。
<!--/-->

```agda
            (ranF : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst E ⟩)
            (svH : ⟨ (H ∷ E ∷ []) ⊨ svAt zero ⟩)
            (dmH : ⟨ (H ∷ E ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijH : ⟨ (H ∷ E ∷ []) ⊨ injAt zero ⟩)
```

<!--en-->
These two clauses are stated in the meta-language, not as formulas.
<!--zh-->
这两条条款以元语言陈述，而非公式。
<!--ja-->
この二つの条項は、論理式としてではなくメタ言語で述べられます。
<!--/-->

```agda
            (ranH : (y z : S) → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
                  → ⟨ fst z ∈ fst C ⟩) where

```

<!--en-->
Each pair of a code and its domain is just the two-slot environment that the three formula conditions require: slot zero holds the graph, slot one holds the domain. One environment per graph.
<!--zh-->
每个「码与定义域」的对，正是三条公式条件所需的两槽环境：槽 0 放图，槽 1 放定义域。每个图一个环境。
<!--ja-->
「符号と定義域」の各対は、三つの論理条件が要求する二枠の環境にすぎません。枠 0 にグラフ、枠 1 に定義域です。環境はグラフごとに一つです。
<!--/-->

```agda
  private
    γF : S ^ 2
    γF = F ∷ D ∷ []

    γH : S ^ 2
    γH = H ∷ E ∷ []
```

<!--en-->
The linking relation says: `x` and `z` are related when the object language can produce an intermediate `y` with `(x, y)` in the first graph and `(y, z)` in the second. Its truncation is inherited from the semantics of the existential quantifier, which is proposition-valued: a satisfaction of the formula carries a witness only up to the truncation built into the quantifier.
<!--zh-->
连接关系说：当对象语言能产生中间值 `y`，使 `(x, y)` 在第一个图中、`(y, z)` 在第二个图中时，`x` 与 `z` 相关。它的截断继承自存在量词的语义：量词取值于命题，公式的满足只带有量化器内建截断意义上的见证。
<!--ja-->
結びの関係は次を言います。対象言語が中間の `y` で、`(x, y)` が最初のグラフに、`(y, z)` が第二のグラフにあるものを生み出せるなら、`x` と `z` は関係します。その切り詰めは存在量化子の意味論から受け継がれます。量化子は命題値であり、論理式の充足が運ぶ証人は、量化子に組み込まれた切り詰めの分だけです。
<!--/-->

```agda
  private
    Chain : S → S → Type (ℓ-suc ℓ)
    Chain x z = ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                             × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁

```

<!--en-->
The carving formula has a single existential, over the intermediate value. Inside it, two application atoms are conjoined: the first graph read with the intermediate in the value slot and `x` in the index slot, the second read with `z` in the value slot and the intermediate in the index slot. This is the object-language shape of `(x, y) ∈ F` and `(y, z) ∈ H`.
<!--zh-->
刻画公式只有一个存在量化，遍历中间值。其内合取两个应用原子：第一个图以中间值居取值空位、`x` 居索引空位读取，第二个图以 `z` 居取值空位、中间值居索引空位读取。这正是 `(x, y) ∈ F` 与 `(y, z) ∈ H` 的对象语言形状。
<!--ja-->
刻むための論理式には、中間の値の上の一つの存在量化だけがあります。その内側で二つの適用のアトムが連言されます。最初のグラフは、値の枠に中間値、添字の枠に `x` を置いて読まれ、第二のグラフは、値の枠に `z`、添字の枠に中間値を置いて読まれます。これが `(x, y) ∈ F` と `(y, z) ∈ H` の対象言語としての形です。
<!--/-->

```agda
    opaque
      body : Formula S 3
      body = ∃̇ (appC F (suc (suc zero)) zero ∧̇ appC H zero (suc zero))

```

<!--en-->
Adequacy of the application atoms moves each conjunct to its intended membership: the first into the first graph at the pair `(x, y)`, the second into the second graph at `(y, z)`. What remains is exactly a linking witness, in truncated form.
<!--zh-->
应用原子的充分性把每个合取项搬到其本意的隶属：第一个搬到第一个图在 `(x, y)` 处的隶属，第二个搬到第二个图在 `(y, z)` 处的隶属。剩下的恰是截断形式的连接见证。
<!--ja-->
適用アトムの妥当性が、各連言を本来の所属へ運びます。第一は `(x, y)` における最初のグラフへの所属へ、第二は `(y, z)` における第二のグラフへの所属へ。残るのは、切り詰められた形の結びの証人です。
<!--/-->

```agda
      read : (x z p : S) → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩ → Chain x z
      read x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ [])) hf
        , subst ⟨_⟩ (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ [])) hh })

```

<!--en-->
The converse moves a linking witness back into the object language along the same adequacy, reversed. The two directions say that the formula and the linking relation express one another.
<!--zh-->
逆向把连接见证沿同一条充分性的反向搬回对象语言。两个方向合起来说：公式与连接关系互相表达。
<!--ja-->
逆方向は、結びの証人を同じ妥当性を逆にたどって対象言語へ戻します。二つの向きは、論理式と結びの関係が互いを表現することを言います。
<!--/-->

```agda
      fill : (x z p : S) → Chain x z → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩
      fill x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (sym (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ []))) hf
        , subst ⟨_⟩ (sym (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ []))) hh })

```

<!--en-->
The bounded-relation device is instantiated once, with the linking relation as its host predicate; everything below is read off that single instance.
<!--zh-->
有界关系装置被例示一次，宿主谓词取为连接关系；下文一切都从这个唯一实例读出。
<!--ja-->
有界関係の装置は一度だけ具体化され、その述語として結びの関係が与えられます。以下のすべてはこの一つの実例から読み出されます。
<!--/-->

```agda
    module Composite = Relation D C body (λ x z → Chain x z , squash₁) read fill

```

<!--en-->
The composite graph is the separated relation itself.
<!--zh-->
复合图就是那个分离出的关系。
<!--ja-->
合成のグラフは、分出された関係そのものです。
<!--/-->

```agda
  K : S
  K = Composite.rel

  K-out : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
        → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
```

<!--en-->
Its backward reading is inherited unchanged: a coded pair in the composite yields, merely, an intermediate `y` with `(x, y)` in the first graph and `(y, z)` in the second. This one reader drives all four verifications.
<!--zh-->
其反向读取原样继承：复合物中的一个编码对仅仅地给出中间值 `y`，使 `(x, y)` 在第一个图、`(y, z)` 在第二个图。下文四项验证都由这一条读取驱动。
<!--ja-->
逆の読みはそのまま引き継がれます。合成の中の符号化された対は、単に、`(x, y)` が最初のグラフに、`(y, z)` が第二のグラフにあるような中間の `y` を与えます。以下の四つの検証はすべて、この一つの読み手が駆動します。
<!--/-->

```agda
  K-out = Composite.pair-out

```

<!--en-->
The forward reading is the composition law: given an intermediate `y` with the two pairs in the two graphs, the truncated witness is handed to the device, which places the coded pair of `x` and `z` inside the composite.
<!--zh-->
正向读取即复合律：给定中间值 `y`，使两对分别落在两个图中，把截断的见证交给装置，装置便把 `x` 与 `z` 的编码对放进复合物。
<!--ja-->
順方向の読みは合成の法則です。二つの対がそれぞれ二つのグラフにある中間の `y` が与えられれば、切り詰められた証人が装置に渡され、装置は `x` と `z` の符号化された対を合成の中に置きます。
<!--/-->

```agda
  K-in : (x y z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
       → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
  K-in x y z mx mz hf hh = Composite.into x z mx mz ∣ y , hf , hh ∣₁
```

<!--en-->
The composite must now satisfy the four conditions on its own, under the environment pairing the composite graph with the first domain. Single-valuedness is first.
<!--zh-->
复合物现在必须以其自身资格满足四项条件，环境把复合图与第一个定义域配对。先证单值性。
<!--ja-->
合成は次に、四条件を自分の力で満たさねばなりません。環境は合成のグラフと最初の定義域を対にします。まず一価性です。
<!--/-->

```agda
  γK : S ^ 2
  γK = K ∷ D ∷ []

  svK : ⟨ γK ⊨ svAt zero ⟩
```

<!--en-->
Suppose the composite pairs `x` with two values `y` and `y'`. Unwrapping both truncated linkings gives intermediates `w` and `w'`, with `(x, w)` and `(x, w')` in the first graph.
<!--zh-->
设复合把 `x` 与两个值 `y`、`y'` 配对。拆开两个截断的连接得中间值 `w` 与 `w'`，`(x, w)` 与 `(x, w')` 在第一个图中。
<!--ja-->
合成が `x` を二つの値 `y` と `y'` に対にするとします。切り詰められた二つの結びを解くと中間の `w` と `w'` が現れ、`(x, w)` と `(x, w')` が最初のグラフにあります。
<!--/-->

```agda
  svK = svAt-in zero γK (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (w' , (hf' , hh')) →
          svAt-out zero γH svH w y y' hh
```

<!--en-->
Single-valuedness of the first graph identifies `w` and `w'`; the identification is transported into the second graph's pair, whose single-valuedness then identifies `y` and `y'`. The goal is a path in an h-set, hence a proposition, so both eliminations of truncations are legitimate.
<!--zh-->
第一个图的单值性等同 `w` 与 `w'`；该同一视被搬入第二个图的对子，其单值性随即等同 `y` 与 `y'`。目标是 h-集合中的路径，因而是命题，故两次截断消去都合法。
<!--ja-->
最初のグラフの一価性が `w` と `w'` を同一視し、その同一視は第二のグラフの対へ輸送され、第二の一価性が `y` と `y'` を同一視します。目標は h-集合の中のパス、すなわち命題なので、二度の切り詰めの消去は正当です。
<!--/-->

```agda
            (subst (λ t → ⟨ pr t (fst y') ∈ fst H ⟩)
              (sym (svAt-out zero γF svF x w w' hf hf')) hh') })
        (K-out x y' q) })
      (K-out x y p))

```

<!--en-->
Injectivity is verified next, and the order of the two graphs matters: the second graph's injectivity is used first, the first graph's second.
<!--zh-->
接着验证单射性，且两个图的使用次序重要：先用第二个图的单射性，再用第一个图的。
<!--ja-->
次に単射性を検証します。ここで二つのグラフの使う順序が重要です。第二のグラフの単射性を先に使い、最初のグラフの単射性を後に使います。
<!--/-->

```agda
  ijK : ⟨ γK ⊨ injAt zero ⟩
```

<!--en-->
Suppose `y` receives both `x` and `x'` under the composite. The two truncated linkings yield intermediates `w` and `w'`, with `(x, w)` and `(x', w')` in the first graph and both `(w, y)` and `(w', y)` in the second.
<!--zh-->
设复合把 `x` 与 `x'` 都映到 `y`。两个截断的连接给出中间值 `w` 与 `w'`：`(x, w)` 与 `(x', w')` 在第一个图中，而 `(w, y)` 与 `(w', y)` 都在第二个图中。
<!--ja-->
合成が `y` に `x` と `x'` の両方を送るとします。切り詰められた二つの結びが中間の `w` と `w'` を与えます。`(x, w)` と `(x', w')` は最初のグラフにあり、`(w, y)` と `(w', y)` は第二のグラフにあります。
<!--/-->

```agda
  ijK = injAt-in zero γK (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (w' , (hf' , hh')) →
          injAt-out zero γF ijF w x x' hf
```

<!--en-->
Injectivity of the second graph at the common value `y` identifies `w` and `w'`; injectivity of the first graph at the now-common intermediate identifies `x` and `x'`.
<!--zh-->
第二个图在公共值 `y` 处的单射性等同 `w` 与 `w'`；第一个图在此时公共的中间值处的单射性等同 `x` 与 `x'`。
<!--ja-->
共通の値 `y` における第二のグラフの単射性が `w` と `w'` を同一視し、今や共通の中間における最初のグラフの単射性が `x` と `x'` を同一視します。
<!--/-->

```agda
            (subst (λ t → ⟨ pr (fst x') t ∈ fst F ⟩)
              (sym (injAt-out zero γH ijH y w w' hh hh')) hf') })
        (K-out x' y q) })
      (K-out x y p))

```

<!--en-->
Domain totality for the composite is an equivalence: `x` belongs to the first domain precisely when it has a composite value. Both directions are supplied to the introduction form.
<!--zh-->
复合在定义域上的全域性是一条等价：`x` 属于第一个定义域，当且仅当它有复合取值。两个方向一并交给引入形式。
<!--ja-->
合成の定義域における全域性は同値です。`x` が最初の定義域に属するのは、合成の値をもつとき、そのときに限ります。二つの向きが導入の形に渡されます。
<!--/-->

```agda
  dmK : ⟨ γK ⊨ domAt zero (suc zero) ⟩
  dmK = domAt-intro zero (suc zero) γK (λ x → fwd x , bwd x)
```

<!--en-->
One direction eliminates the first graph's domain condition directly.
<!--zh-->
一个方向直接消去第一个图的定义域条件。
<!--ja-->
一つの向きは、最初のグラフの定義域の条件をそのまま消去します。
<!--/-->

```agda
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
```

<!--en-->
If `x` has a composite value, the linking witness exhibits an intermediate `w` with `(x, w)` in the first graph; the domain atom's own elimination, applied to that pair, places `x` in `D`. The second graph plays no role in this direction.
<!--zh-->
若 `x` 有复合取值，连接见证给出中间值 `w`，使 `(x, w)` 在第一个图中；把定义域原子自身的消去施于该对，即将 `x` 放入 `D`。这个方向用不到第二个图。
<!--ja-->
`x` が合成の値をもつなら、結びの証人が中間の `w` を示し、`(x, w)` が最初のグラフにあります。定義域のアトム自身の消去をその対に施せば、`x` が `D` の中に置かれます。この向きで第二のグラフは役に立ちません。
<!--/-->

```agda
        (λ { (w , (hf , _)) → domAt-out zero (suc zero) γF dmF x w hf })
        (K-out x y p) })

```

<!--en-->
The other direction chains the two introductions. Given `x` in `D`, the first graph's domain introduction yields an intermediate `w` with `(x, w)` in the first graph, and its range clause puts `w` in the middle set.
<!--zh-->
另一方向串起两条引入。给定 `D` 中的 `x`，第一个图的定义域引入给出中间值 `w`，使 `(x, w)` 在第一个图中，其值域条款把 `w` 放入中间集。
<!--ja-->
もう一つの向きは、二つの導入をつなぎます。`D` の `x` が与えられると、最初のグラフの定義域の導入が中間の `w` を与え、`(x, w)` が最初のグラフにあり、その値域の条項が `w` を中間の集合に置きます。
<!--/-->

```agda
    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (w , hf) → PT.rec squash₁
        (λ { (z , hh) → ∣ z , K-in x w z mx (ranH w z hh) hf hh ∣₁ })
```

<!--en-->
The second graph's domain introduction, applied at `w`, produces `z` with `(w, z)` in the second graph; the range clause of the second graph places `z` in `C`; and the composition law pairs `x` with `z` inside the composite. Both steps are truncated, and so is the conclusion.
<!--zh-->
第二个图的定义域引入在 `w` 处产出 `z`，使 `(w, z)` 在第二个图中；第二个图的值域条款把 `z` 放入 `C`；复合律把 `x` 与 `z` 的对放进复合物。两步都是截断的，结论亦然。
<!--ja-->
第二のグラフの定義域の導入は `w` で `(w, z)` をもつ `z` を産み、第二のグラフの値域の条項が `z` を `C` に置きます。そして合成の法則が `x` と `z` の対を合成の中に置きます。どちらの段階も切り詰められ、結論もそうです。
<!--/-->

```agda
        (domAt-in zero (suc zero) γH dmH w (ranF x w hf)) })
      (domAt-in zero (suc zero) γF dmF x mx)

```

<!--en-->
The range condition is the second graph's range clause applied at the intermediate. Unwrapping the composite pair yields the linking witness; its second component pairs the intermediate with `z` inside the second graph, and the clause places `z` in `C`.
<!--zh-->
值域条件是第二个图的值域条款在中间值处的应用。拆开复合对得到连接见证；其第二分量在第二个图内把中间值与 `z` 配对，条款随即将 `z` 放入 `C`。
<!--ja-->
値域の条件は、第二のグラフの値域の条項を中間の値に適用したものです。合成の対を解けば結びの証人が現れ、その第二成分が第二のグラフの中で中間と `z` を対にするので、条項が `z` を `C` の中に置きます。
<!--/-->

```agda
  ranK : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩ → ⟨ fst z ∈ fst C ⟩
  ranK x z h = PT.rec (snd (fst z ∈ fst C))
    (λ { (w , (_ , hh)) → ranH w z hh }) (K-out x z h)
```

<!--en-->
The three reading conditions together with the range clause are exactly what lets a coded injection be read back as a function between presentations. The composite therefore admits that reading, and this module carries it privately: what is passed on publicly are the graph and its four conditions, so the reading needs nothing beyond them.
<!--zh-->
三条读取条件连同值域条款，恰是「编码单射可读回为呈现之间的函数」所需。因此复合物也承认这一读取；该模块私下承载它：公开传递出去的只是图与其四项条件，这一读取所需不外乎此。
<!--ja-->
三つの読みの条件と値域の条項が揃うのは、符号化された単射を提示の間の関数として読み戻すための条件にちょうど合います。したがって合成もこの読みを認めます。このモジュールがそれを非公開で担います。公開されて渡るのはグラフと四条件だけなので、この読みにそれ以外は要りません。
<!--/-->

```agda
  private
    module Sm = Small K D C svK dmK ijK ranK
```

<!--en-->
## Coding inclusions

An inclusion needs no new construction: when `D` is contained in `C`, the identity map on `D` already maps into `C`. What is coded is that map's graph, written in the object language as equality between the value slot and the index slot. The module receives the two sets and the pointwise inclusion.
<!--zh-->
## 符号化包含

包含不需要新的构造：当 `D` 包含于 `C` 时，`D` 上的恒等映射本来就是到 `C` 的映射。被编码的是这个映射的图，它在对象语言中写作取值空位与索引空位之间的相等。模块收取两个集合与逐点的包含。
<!--ja-->
## 包含の符号化

包含には新しい構成は要りません。`D` が `C` に含まれるなら、`D` 上の恒等写像はもともと `C` への写像です。符号化されるのはその写像のグラフであり、対象言語では値の枠と添字の枠の間の等号として書かれます。モジュールは二つの集合と点ごとの包含を受け取ります。
<!--/-->

```agda
module InclGraph (D C : S)
                 (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩) where

```

<!--en-->
The definable-map record is filled with the identity on the domain: the function sends each
<!--zh-->
可定义映射记录由定义域上的恒等填成：函数把每个元素送到自身，逐点包含证明每个取值落入
<!--ja-->
定義可能な写像のレコードは、定義域上の恒等で満たされます。
<!--/-->

```agda
  private
    M : DefinableMap
    M = record
      { dom = D ; cod = C
      ; fn = λ x _ → x
```

<!--en-->
element to itself, and the pointwise inclusion certifies that every value lands in `C`.
<!--zh-->
`C`。
<!--ja-->
関数は各要素を自分自身へ送り、点ごとの包含がすべての値が `C` に着地することを証明します。
<!--/-->

```agda
      ; into = λ x mx → sub (fst x) mx
```

<!--en-->
The graph formula is equality between the two slots, and that it holds of the function's own value is definitional. Uniqueness of solutions uses the equation's underlying equality: any solution satisfies the equation, which is an equality of underlying elements, and since constructibility is a proposition, this underlying equality lifts to an equality of carrier elements. This is how unrelatedness to the function's value is excluded.
<!--zh-->
图公式是两个空位之间的相等，它对函数自身取值成立是定义性的。解的唯一性用的是等式的底层等式：任何解都满足该等式，而那是底层元素之间的相等；又因可构造性是命题，这个底层等式提升为载体元素的等式。排除「与函数取值无关的解」靠的正是这一点。
<!--ja-->
グラフの論理式は二つの枠の間の等号であり、それが関数自身の値について成り立つことは定義的です。解の一意性には、等号の底の等しさを使います。どんな解も等式を満たしますが、それは底の要素の間の等しさであり、構成可能性が命題なので、この底の等しさは台の要素の等しさへ持ち上がります。関数の値と無関係な解が除かれるのは、このためです。
<!--/-->

```agda
      ; graph = var zero ≐ var (suc zero)
      ; defines = λ _ _ → refl
      ; only = λ _ _ _ h → Σ≡Prop (λ w → snd (isL w)) h }

```

<!--en-->
The shared construction turns the map into a graph with its three reading conditions, but it demands from outside a proof that the underlying function is injective. For the identity map this is immediate: the hypothesis equates the images of two inputs, and under the identity map equality of images is equality of inputs, so the supplied continuation, which returns the equation itself, is exactly the required proof.
<!--zh-->
共享构造把该映射变成带三条读取条件的图，但它要从外部收取底层函数为单射的证明。对恒等映射而言这是直接的：该假设等同两个输入的像，而在恒等映射下像的相等就是输入的相等，故所提供的、把等式原样返回的延续恰是所需的证明。
<!--ja-->
共有の構成はこの写像を三つの読みの条件をもつグラフへ変えますが、底の関数が単射であることの証明を外部から要求します。恒等写像の場合これは直接です。仮定は二つの入力の像を等しくしますが、恒等写像のもとで像の等しさは入力の等しさです。したがって、等式をそのまま返す渡された継続が、求める証明にちょうどなります。
<!--/-->

```agda
    module I = DefinableInj M (λ _ _ _ _ e → e)
      using ( F; code )

  opaque
    G : S
    G = I.F

```

<!--en-->
The graph with all four conditions is delivered together as the code of an injection from `D` to `C`; consumers receive the package as a unit and never need to open it.
<!--zh-->
图连同全部四项条件一并作为从 `D` 到 `C` 的单射之码交付；使用者把整个包当作一个单元接收，无需打开。
<!--ja-->
グラフと四条件のすべてが、`D` から `C` への単射の符号として一緒に渡されます。利用者は包みを一つの単位として受け取り、開く必要はありません。
<!--/-->

```agda
  opaque
    unfolding G
    code : InjCode G D C
    code = I.code
```

<!--en-->
The same graph is read back through the shared reading as a function between the presentations of `D` and `C`. This reading is carried in a private module, because the results that pass on publicly are the graph and its four conditions, and those are all the reading needs.
<!--zh-->
同一个图经共享读取被读回为 `D` 与 `C` 的呈现之间的函数。这一读取由一个私有的模块承载：公开传递出去的结果只是图与其四项条件，而这正是该读取所需的全部。
<!--ja-->
同じグラフが、共有の読みを通して、`D` と `C` の提示の間の関数として読み戻されます。この読みは非公開のモジュールが担います。公開されて渡る結果はグラフとその四条件であり、この読みに必要なのはそれだけです。
<!--/-->

```agda
  private
    module Sm = Small G D C (code .fst) (code .snd .fst)
      (code .snd .snd .fst) (code .snd .snd .snd)

```

<!--en-->
The induced function is named `incl`, and its route matters. An index of `D`'s presentation names an underlying element, which belongs to `D` and therefore, by the inclusion, to `C`. The function then takes the fiber of `C`'s own presentation at that element: the index of `C` presenting it. The index is not transported directly; it is recovered through the element and the fiber.
<!--zh-->
导出的函数名为 `incl`，其路线值得注意。`D` 呈现的一个索引指名一个底层元素，该元素属于 `D`，因而由包含属于 `C`。函数随后取 `C` 自身呈现在该元素处的纤维：即呈现它的那个 `C` 索引。索引不是被直接搬运的，而是经由元素与纤维找回。
<!--ja-->
導かれた関数は `incl` と名付けられ、その道すじが重要です。`D` の提示の索引は底の要素を名指し、その要素は `D` に属し、したがって包含によって `C` に属します。関数は次に、`C` 自身の提示のその要素での繊維を取ります。すなわち、その要素を提示する `C` の索引です。索引を直接輸送するのではなく、要素と繊維を通して取り戻します。
<!--/-->

```agda
  opaque
    incl : ⟪ fst D ⟫ → ⟪ fst C ⟫
    incl = Sm.small
```

<!--en-->
## Inclusion and composition at the internal-existence level

The constructions so far produce graphs; the internal injection relation asks only that a graph exist. The lift is immediate: an inclusion yields the identity graph as witness, and the assertion is truncated around it. This is the form in which inclusions reach the cardinal arguments.
<!--zh-->
## 内部存在层面的包含与复合

至此的构造产出图；而内部单射关系只要求某个图存在。提升是直接的：包含给出恒等图作为见证，断言在其外围截断。包含进入基数论证所用的正是这一形式。
<!--ja-->
## 内部存在の水準における包含と合成

これまでの構成はグラフを産みます。内部の単射関係が要求するのは、グラフが存在することだけです。持ち上げは直接です。包含は恒等グラフを証人として与え、主張はその周りで切り詰められます。基数の議論が包含を受け取るのは、この形です。
<!--/-->

```agda
inclusion-coded : (a b : S)
                → ((z : V ℓ) → ⟨ z ∈ fst a ⟩ → ⟨ z ∈ fst b ⟩)
                → InjL a b
inclusion-coded a b sub = ∣ I.G , I.code ∣₁
  where module I = InclGraph a b sub

```

<!--en-->
Composition lifts in the same way: `PT.rec2` exposes both witnesses locally, builds their composite, and truncates the result again, without making a global choice of representatives.
<!--zh-->
复合同样提升：`PT.rec2` 在局部分支中展开两个见证，构造其复合，再次截断结果，而不作代表的全局选择。
<!--ja-->
合成も同様に持ち上がります。`PT.rec2` は二つの証人を局所的に取り出して合成を作り、結果を再び切り詰めるので、代表を大域的に選ぶ必要はありません。
<!--/-->

```agda
injl-trans : (a b c : S) → InjL a b → InjL b c → InjL a c
injl-trans a b c = PT.rec2 PT.squash₁ step
  where
```

<!--en-->
The two-fold elimination locally unwraps the two witnesses, assembles the composite by the verified construction, and truncates the result again. It performs no global choice of representatives: the witnesses exist only as hypotheses of the construction and are never retained.
<!--zh-->
双重消去局部地拆开两个见证，用已验证的构造组装复合物，再把结果重新截断。它不作任何全局的代表选择：两个见证只作为构造的假设存在，从不被保留。
<!--ja-->
二重の消去は、二つの証人を局所的に解きほぐし、検証済みの構成で合成を組み立て、結果を改めて切り詰めます。代表の大域的な選択は行いません。二つの証人は、構成の仮定として存在するだけで、保持されることはありません。
<!--/-->

```agda
  step : Σ[ F ∈ S ] InjCode F a b
       → Σ[ H ∈ S ] InjCode H b c
       → InjL a c
  step (F , svF , dmF , ijF , ranF) (H , svH , dmH , ijH , ranH) =
    ∣ K.K , (K.svK , K.dmK , K.ijK , K.ranK) ∣₁
```

<!--en-->
The composite module carries the whole verification, so at this level the composition law is a single line.
<!--zh-->
复合模块承载全部验证，因此在这个层面，复合律只有一行。
<!--ja-->
合成のモジュールが検証のすべてを担うので、この水準では合成の法則は一行です。
<!--/-->

```agda
    where
    module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH
```

<!--en-->
The principal instance starts from a member `D` of an ordinal `C`. The only assumption is that `D` belongs to the ordinal `C`; transitivity of `C` then says that every member of `D` is a member of `C`, which is exactly the pointwise inclusion the coding requires. The module opens the inclusion construction for this pair, so its graph, code, and induced map are all available under one name.
<!--zh-->
主要实例从序数 `C` 的成员 `D` 出发。唯一的假设是 `D` 属于序数 `C`；`C` 的传递性随即断言 `D` 的每个成员都是 `C` 的成员，而这正是编码所需的逐点包含。模块对这一对打开包含构造，于是其图、码与导出映射都在同一个名字下可用。
<!--ja-->
主要な実例は、順序数 `C` の要素 `D` から始まります。仮定は `D` が順序数 `C` に属することだけです。`C` の推移性により、`D` の各要素が `C` の要素であることが従い、これが符号化の必要とする点ごとの包含にほかなりません。モジュールはこの対に対して包含の構成を開くので、そのグラフ・符号・導かれた写像が一つの名のもとで使えます。
<!--/-->

```agda
module OrdIncl (C : S) (oC : IsOrd (fst C))
               (D : S) (D∈C : ⟨ fst D ∈ fst C ⟩) where

  open InclGraph D C (λ _ z∈D → oC .fst z∈D D∈C) public
```

<!--en-->
## Recap

Three results serve the internal cardinal arguments. The finite exclusion shows that no injection exists from `ω` into the square of a finite ordinal: a member of `ω` is, merely, a numeral, the presentation types `⟪ # n ⟫` and the finite sets `Fin n` admit injections in each direction, and the abstract chase derives, from any assumed injection into a finite square, an injection from a larger finite set into a smaller one. The composition turns two coded injections into one, verifying single-valuedness, domain totality, injectivity, and the range clause through the linking relation. The inclusion codes pointwise containment by the identity graph. At the existence level, both operations lift to the truncated internal relation, so cardinal bounds can be built and compared entirely through graphs living inside `L`.
<!--zh-->
## 小结

三项结果服务于内部基数论证。有限排除表明从 `ω` 到任何有限序数平方的单射不存在：`ω` 的成员仅仅地是数码，呈现类型 `⟪ # n ⟫` 与有限集 `Fin n` 在两个方向上各有一个单射，若假设存在到某个有限平方的单射，抽象追逐便导出从较大有限集到较小有限集的单射。复合把两个编码单射变成一个，经连接关系核验单值性、定义域上的全域性、单射性与值域条款。包含由恒等图把逐点包含编码为单射。在存在层面，两种操作都提升到截断的内部关系，因此基数界限的构造与比较完全可以经由居于 `L` 内部的图进行。
<!--ja-->
## まとめ

三つの結果が内部の基数の議論に仕えます。有限の排除は、`ω` から任意の有限順序数の平方への単射が存在しないことを示します。`ω` の要素は単に数項であり、提示の型 `⟪ # n ⟫` と有限集合 `Fin n` の間には両方向それぞれに単射があり、抽象的な追跡は、有限の平方への単射の存在を仮定すると、大きい有限集合から小さい有限集合への単射を導きます。合成は二つの符号化された単射を一つにし、結びの関係を通して一価性・定義域における全域性・単射性・値域の条項を検証します。包含は恒等グラフによって点ごとの包含を符号化された単射へ変えます。存在の水準では、どちらの操作も切り詰められた内部の関係へ持ち上がるので、基数の上界の構成と比較を、`L` の中に住むグラフだけを通して行えます。
<!--/-->
