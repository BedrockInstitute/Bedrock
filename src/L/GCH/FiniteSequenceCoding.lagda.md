```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Coding finite sequences below an infinite ordinal
<!--zh-->
# 在无穷序数以下编码有限序列
<!--ja-->
# 無限順序数の下で有限列をコード化する
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and excluded middle at level `ℓ-suc ℓ`. Every construction below, from separation to the cardinal square law used at the end, is relative to this one named hypothesis, so the final sequence bound carries exactly the same assumption.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上的排中律。下文从分离到末尾所用平方律的每项构造都相对于这一条具名假设，因此最终的序列界恰好承载同一假设。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` における排中律を固定する。以下の分出から最後に用いる平方律まで、すべての構成はこの一つの名づけられた仮定に相対的であり、最終的な列の上界もまったく同じ仮定をもつ。
<!--/-->

```agda
module L.GCH.FiniteSequenceCoding {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( #∈ω; ∈#-elim )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-out; domAt; domAt-in; domAt-out; domAt-intro; appAt; appAt-adequate; envOverAt; envOver-sv; envOver-dom; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( numL; sucAtL; sucAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt; module Extract )
open import L.Coding.Environment {ℓ} using ( lookup-spec )
open import L.Coding.EnvironmentSet {ℓ} lem
  using ( Ix; envS; envOver; envSet; envSet-in; envSet-out; module Recover )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct; smallDom )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL )
open import L.InjectionComposition {ℓ} lem using ( injl-trans )
open import L.GCH.CardinalRepresentative {ℓ} lem using ( cardOf )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.CardinalSquareLaw {ℓ} lem
  using ( prodL; prodL-in; Goal; module Step; prod-inj; no-fin; ω⊆ )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )
```

<!--en-->

Finite parameter lists must be counted by sets that exist inside `L`. This chapter first collects all finite sequences over a constructible set as one constructible set. For an infinite ordinal `α`, it then folds each sequence through an internal injection from `α × α` to `α`, attaches the length as a final tag, and proves an internal injection from the sequence set into `α`. The result is an upper bound only: it neither covers every element of `α` nor defines a decoder on all of `α`.
<!--zh-->

有限参数表必须由 `L` 内部存在的集合来计数。本章先把一个可构造集合上的全部有限序列收集成一个可构造集合。随后对无穷序数 `α`，借助从 `α × α` 到 `α` 的内部编码单射逐项折叠序列，再以长度作最终标签，并证明从序列集到 `α` 的内部单射。这个结论只给出上界：它既不覆盖 `α` 的每个元素，也不定义 `α` 全域上的解码器。
<!--ja-->

有限なパラメータ列を数えるには、その列を集める集合が `L` の内部に存在しなければならない。本章ではまず、構成可能集合上のすべての有限列を一つの構成可能集合に集める。次に無限順序数 `α` に対し、`α × α` から `α` への内部の符号化された単射を用いて列を項ごとに畳み込み、最後に長さをタグとして付け、列の集合から `α` への内部単射を示す。この結論は上界だけを与える。`α` のすべての要素を覆うことも、`α` 全体で定義された復号写像を与えることもない。
<!--/-->

<!--en-->
The construction is classical only through an explicit excluded-middle hypothesis. In particular, propositionally truncated witnesses remain truncated unless uniqueness makes their witness type a proposition; no choice principle is used to select arbitrary sequence representations or injection graphs.
<!--zh-->
这项构造的经典性只来自一条显式的排中律假设。尤其是，命题截断的见证始终保持截断，除非唯一性使见证类型本身成为命题；证明不借助选择公理来任意选取序列表示或单射图。
<!--ja-->
この構成で用いる古典性は、明示された排中律の仮定だけから来る。とくに、命題的に切り詰められた証人は、一意性によって証人型そのものが命題になる場合を除いて、切り詰められたままである。列の表現や単射のグラフを任意に選ぶための選択原理は用いない。
<!--/-->

```agda
open import Cubical.HITs.PropositionalTruncation using ( rec2 )
```



<!--en-->
Two descriptions of the same objects will be used throughout. At the object-language level, equality, conjunction, and bounded or unbounded quantification describe sequence graphs and recursive traces inside `L`. At the host level, presentations turn membership in a set into small indices, while regularity later supports the well-founded argument behind the square law.
<!--zh-->
下文始终交替使用同一对象的两种描述。在对象语言层面，相等、合取以及有界或无界量化描述 `L` 内部的序列图与递归轨迹。在宿主层面，呈现把集合成员化为小索引，而正则公理稍后支撑平方律背后的良基论证。
<!--ja-->
以下では、同じ対象について二つの記述を行き来する。対象言語の水準では、等号、連言、有界および非有界の量化によって、`L` の内部の列のグラフと再帰の軌跡を記述する。ホストの水準では、提示によって集合の要素を小さな添字として扱い、正則性は後で平方律を支える整礎的な議論に用いられる。
<!--/-->

<!--en-->
The coding relies on two rigid families of set codes. Ordered-pair injectivity recovers both coordinates from an equality of pair codes, and von Neumann numerals faithfully record natural numbers and their order inside `ω`. Transitivity of constructibility keeps every member of a constructible ordinal inside `L`, so these ambient codes can be used as elements of the constructible model.
<!--zh-->
编码依赖两类具有刚性的集合码。有序对码的单射性可从对码相等恢复两个坐标，冯·诺伊曼数码则在 `ω` 内忠实记录自然数及其顺序。可构造性的传递性保证可构造序数的每个成员仍在 `L` 中，因而这些外围码可作为可构造模型的元素使用。
<!--ja-->
符号化は、二つの剛直な集合符号の族に依存する。順序対の符号の単射性により、対の符号の等しさから二つの座標を復元でき、フォン・ノイマン数項は自然数とその順序を `ω` の内部で忠実に記録する。構成可能性の推移性により、構成可能な順序数の各要素も `L` にとどまるので、これらの周囲の符号を構成可能モデルの要素として使える。
<!--/-->

<!--en-->
The set-theoretic graphs used here must be visible to first-order reasoning in `L`. Separation forms the exact subcollections, while adequacy for pairs, graph application, domains, and environments identifies each object-language clause with its intended relation between underlying sets. This bridge will later turn a host recursive fold into an internal definable graph.
<!--zh-->
这里使用的集合论图必须能由 `L` 内部的一阶推理识别。分离构成准确的子集合，而配对、图应用、定义域与环境的充分性把每条对象语言子句同底层集合之间的预期关系认同起来。这座桥梁稍后会把宿主层的递归折叠转化为内部可定义图。
<!--ja-->
ここで用いる集合論的グラフは、`L` の内部の一階推論から読めなければならない。分出によって正確な部分集合を作り、対、グラフの適用、定義域、環境についての妥当性が、各対象言語の節を底集合間の意図された関係と同一視する。この橋によって、後でホスト側の再帰的な畳み込みを内部の定義可能なグラフへ移せる。
<!--/-->

<!--en-->
A finite sequence is represented by an environment graph with a numeral as its exact domain. For each fixed length, the environment-set construction collects precisely those graphs and reads a member back only under propositional truncation. The recursion machinery will nevertheless produce an actual value once the graph formula has a unique output, and coded-injection composition will carry the resulting bounds between constructible sets.
<!--zh-->
有限序列表示为以数码为准确规定义域的环境图。对每个固定长度，环境集构造恰好收集这些图，而从成员反向读取表示时只得到命题截断的结果。尽管如此，一旦图公式的输出唯一，递归机制仍可产出实际取值；编码单射的复合则把所得的界在可构造集合之间传递。
<!--ja-->
有限列は、数項をちょうど定義域とする環境のグラフとして表す。各固定長について、環境集合の構成はそのようなグラフだけを集め、要素から表現を読み戻す向きは命題的に切り詰められている。それでも、グラフの論理式の出力が一意なら、再帰の仕組みは実際の値を与える。さらに、符号化された単射の合成によって、得られた上界を構成可能集合の間で移せる。
<!--/-->

<!--en-->
The final counting argument need not assume that the given infinite ordinal is already a cardinal. It first passes to a cardinal representative, uses the square law there to compress pairs, and composes back into the original ordinal. The present chapter then turns that pair compression into a definable injection for finite sequences.
<!--zh-->
最终的计数论证无需假设给定的无穷序数本身已是基数。证明先转到一个基数代表，在那里用平方律压缩有序对，再复合回原序数。本章随后把这项对压缩构造成有限序列的可定义单射。
<!--ja-->
最後の数え上げでは、与えられた無限順序数がすでに基数であると仮定する必要はない。まず基数代表へ移り、そこで平方律を用いて対を圧縮し、もとの順序数へ合成して戻す。本章は、その対の圧縮から有限列の定義可能な単射を構成する。
<!--/-->

<!--en-->
Lengths live as natural numbers, positions as elements of `Fin n`, and internal domain markers as numerals. Moving between these three views requires order facts such as `toℕ i < n` and the inverse conversion from a number below `n` to a finite index. Equality of dependent pairs is controlled by their data component because the accompanying membership proofs are propositions.
<!--zh-->
长度以自然数表示，位置以 `Fin n` 的元素表示，内部定义域标记则以数码表示。在这三种视角之间转换，需要 `toℕ i < n` 之类的顺序事实，以及从小于 `n` 的自然数反向构造有穷索引。由于随附的隶属证明是命题，依值对的相等由其数据分量控制。
<!--ja-->
長さは自然数、位置は `Fin n` の要素、内部の定義域の標識は数項として表す。この三つの見方の間を移るには、`toℕ i < n` のような順序の事実と、`n` 未満の自然数から有限添字を作り直す逆変換が必要である。付随する所属の証明は命題なので、依存対の等しさはデータの成分によって決まる。
<!--/-->

```agda
open import Cubical.Data.Nat.Order
  using ( _<_; ≤-refl; ≤-suc; suc-≤-suc; pred-≤-pred; ¬-<-zero; <-split; zero-≤ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
```

<!--en-->
The injectivity proof repeatedly separates two possibilities for an index below a successor: it lies below the predecessor, or it is the last index. Propositional extensionality then converts two membership implications into equality of sets, and the cumulative hierarchy supplies the sets and their canonical presentations on which these arguments run.
<!--zh-->
单射性证明反复区分后继以下索引的两种情形：它小于前驱，或者正是末索引。命题外延性随后把两个隶属蕴含化为集合相等，累积层级则提供承载这些论证的集合及其典范呈现。
<!--ja-->
単射性の証明では、後続数未満の添字について、前の数未満である場合と最後の添字である場合を繰り返し分ける。命題外延性は二つの所属の含意を集合の等しさへ変え、累積階層はこの議論を行う集合とその標準的な提示を与える。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
```

<!--en-->
Von Neumann numerals and their successor operation connect finite lengths with the internal set `ω`. An impossible finite bound is expressed by the empty type, while well-founded induction enters only in the later construction of pair compression from the cardinal square law, not in the elementary recursion that folds a given finite sequence.
<!--zh-->
冯·诺伊曼数码及其后继运算把有限长度同内部集合 `ω` 联系起来。不可能的有限界由空类型表示；良基归纳只在稍后借平方律构造对压缩时出现，并不参与折叠一条给定有限序列的初等递归。
<!--ja-->
フォン・ノイマン数項とその後続演算は、有限な長さを内部集合 `ω` と結び付ける。不可能な有限上界は空型で表す。整礎帰納法が現れるのは、後で平方律から対の圧縮を構成するときだけであり、与えられた有限列を畳み込む初等的な再帰には用いない。
<!--/-->

```agda
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Induction.WellFounded as WF
```

<!--en-->
Propositional truncation records that a representation exists while deliberately forgetting which representation was supplied. Its eliminator is used only when the target is itself a proposition, such as membership or equality of sets. This restriction is the reason the chapter can prove existence and injectivity without silently choosing a length, an assignment, or an internal graph.
<!--zh-->
命题截断记录某个表示存在，同时刻意忘却所给的是哪一个表示。只有当目标本身是命题时，例如集合的隶属或相等，才使用它的消去原则。这项限制保证本章能够证明存在性与单射性，而不会暗中选取长度、赋值或内部图。
<!--ja-->
命題的切り詰めは、ある表現が存在することを記録しつつ、どの表現が与えられたかを意図的に忘れる。その除去則を使うのは、集合の所属や等しさのように、目標自身が命題である場合だけである。この制限により、長さ、割り当て、内部グラフを暗黙に選ぶことなく、存在と単射性を証明できる。
<!--/-->

<!--en-->
At the ambient level, membership is proposition-valued. This matters whenever a truncated witness is eliminated into a membership claim: no data are selected, and only the truth of membership survives.
<!--zh-->
在外围层面，隶属是命题值的。每当把截断见证消去到隶属断言中，这一点都至关重要：没有数据被选出，留下的只有隶属为真。
<!--ja-->
周囲の水準では、所属は命題値である。切り詰められた証人を所属の主張へ除去するとき、この点が効く。データは何も選ばれず、所属が成り立つという事実だけが残る。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
Write `SV` for the proposition-valued structure on the ambient cumulative hierarchy. It provides the outer notion of membership used to compare pair codes, numerals, and set-theoretic graphs before they are regarded as constructible objects.
<!--zh-->
以 `SV` 表示外围累积层级上的命题值结构。它提供外围隶属概念，用来比较有序对码、数码与集合论图，随后再把这些对象视为可构造对象。
<!--ja-->
周囲の累積階層上の命題値構造を `SV` と書く。これは、順序対の符号、数項、集合論的グラフを構成可能な対象として見る前に比較するための、外側の所属概念を与える。
<!--/-->

```agda
module SV = hPropStructure 𝒮ᵥ using ()
```

<!--en-->
Write `S` for the carrier of the constructible structure `SL`. An element of `S` is an ambient set together with evidence that it lies in `L`; consequently every sequence set, graph, and ordinal used by the internal injection has an actual constructible representative.
<!--zh-->
以 `S` 表示可构造结构 `SL` 的载体。`S` 的元素由外围集合及其属于 `L` 的证据组成；因此内部单射所用的每个序列集、图与序数都有实际的可构造代表。
<!--ja-->
構成可能構造 `SL` の台を `S` と書く。`S` の要素は、周囲の集合と、それが `L` に属すことの証拠からなる。したがって、内部単射で用いる列の集合、グラフ、順序数には、いずれも実際の構成可能な代表がある。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open SL using ( S )
```

<!--en-->
Formulas with constants from `S` are evaluated in the constructible structure, while their atomic content can also be read after projection to ambient sets. Transitivity of `L` makes these readings agree, allowing an object-language graph condition to justify the ambient membership equations used in the fold.
<!--zh-->
带有 `S` 中常元的公式在可构造结构中求值，其原子内容也可投影到底层外围集合后读取。`L` 的传递性使两种读法一致，从而对象语言中的图条件能够证成折叠所用的外围隶属等式。
<!--ja-->
`S` の定数を含む論理式は構成可能構造で評価され、その原子的な内容は周囲の集合へ射影して読むこともできる。`L` の推移性により二つの読み方が一致するので、対象言語のグラフ条件から、畳み込みで用いる周囲の所属の等式を得られる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
The numeral `nn k` packages the ambient von Neumann numeral together with its constructibility proof. Numerals mark the exact domains of finite environments; zero also supplies the initial accumulator and the harmless out-of-range value of `ext`; and the length numeral tags the completed fold. These roles keep finite indices visible inside the constructible model.
<!--zh-->
数码 `nn k` 把外围的冯·诺伊曼数码与其可构造性证明打包在一起。数码标记有限环境的准确定义域；数码零还充当折叠的初始累积值与 `ext` 在界外的无关紧要默认值；长度数码则为完成的折叠加上标签。借助这些用途，有限索引在可构造模型内部仍可被识别。
<!--ja-->
数項 `nn k` は、周囲のフォン・ノイマン数項とその構成可能性の証明をまとめたものである。数項は有限環境の正確な定義域を示し、零の数項は畳み込みの初期累積値と `ext` の範囲外での無意味な既定値にもなり、長さの数項は完了した畳み込みにタグを付ける。これらの役割によって、有限添字を構成可能モデルの内部で扱える。
<!--/-->

```agda
nn : ℕ → S
nn k = # k , numL k
```

<!--en-->
## Collecting all finite sequences over a set
<!--zh-->
## 收集一个集合上的全部有限序列
<!--ja-->
## 集合上のすべての有限列を集める
<!--/-->

<!--en-->
A sequence over `A` is, at the host level, a function from a finite ordinal into the presentation of `A`; the small index type collects a length and such a function. This is the host-level notion; its set-coded counterpart is defined below.
<!--zh-->
`A` 上的序列在宿主层面是从有限序数到 `A` 的呈现的函数；小索引类型收集一个长度与这样一个函数。这是宿主层面的概念；其集合编码的对应物在下文定义。
<!--ja-->
`A` の上の列とは、ホストの水準では、有限順序数から `A` の提示への関数である。小さな索引型は、長さとそのような関数の対を集める。これはホストの水準の概念であり、集合で符号化された対応物は、この後で定義される。
<!--/-->

```agda
SeqIx : S → Type ℓ
SeqIx A = Σ[ n ∈ ℕ ] Ix A n
```

<!--en-->
The small-domain principle gives one constructible set that contains every environment graph over `A`, of every finite length. This is only a common container: the exact collection is carved out by separation below, and nothing is claimed about the container being precisely the image.
<!--zh-->
小定义域原理给出一个可构造集合，它包含 `A` 上一切有限长度的环境图。这只是公共容器：精确的集合由下文的分离刻出，且不主张该容器恰为这些图的像。
<!--ja-->
小さな定義域の原理は、`A` の上のすべての有限長の環境グラフを含む、一つの構成可能な集合を与える。これは共通の容器にすぎない。正確な集合は後の分出で刻まれ、この容器がちょうどその像であるとは主張しない。
<!--/-->

```agda
private
  amb : (A : S) → S
  amb A = smallDom (SeqIx A) (λ p → envS A (snd p)) .fst
```

<!--en-->
For a particular length `n` and assignment `g`, the graph `envS A g` lies in the common container. This inclusion supplies the ambient half of separation membership; the defining formula will supply the exact finite-environment condition.
<!--zh-->
对特定长度 `n` 与赋值 `g`，图 `envS A g` 属于这个公共容器。这条包含提供分离隶属的外围一半；定义公式则提供准确的有限环境条件。
<!--ja-->
特定の長さ `n` と割り当て `g` に対し、グラフ `envS A g` は共通の容器に属する。この包含が分出による所属の外側の半分を与え、定義論理式が有限環境であるという正確な条件を与える。
<!--/-->

```agda
  amb-in : (A : S) (p : SeqIx A) → ⟨ fst (envS A (snd p)) ∈ˢ fst (amb A) ⟩
  amb-in A = smallDom (SeqIx A) (λ p → envS A (snd p)) .snd
```

<!--en-->
The one-variable formula says that the candidate `x` is an environment graph over `A` whose domain is some member of the internal `ω`. The bounded witness is therefore only known at first to be an element of `ω`; recovering an actual natural length from it is a later, propositionally truncated step.
<!--zh-->
这个一元公式断言：候选对象 `x` 是 `A` 上的环境图，其定义域是内部 `ω` 的某个成员。因此起初只知道这个有界见证属于 `ω`；从中恢复实际的自然数长度要到稍后进行，而且结果仍在命题截断之内。
<!--ja-->
この一変数論理式は、候補 `x` が `A` 上の環境のグラフであり、その定義域が内部の `ω` のある要素であることを述べる。したがって、有界な証人について最初に分かるのは `ω` に属すことだけである。そこから実際の自然数の長さを復元するのは後の段階であり、その結果も命題的に切り詰められている。
<!--/-->

```agda
seqFo : S → Formula S 1
seqFo A = ∃̇∈ (con ωʟ) (∃̇ ( (var zero ≐ con A)
                        ∧̇ envOverAt (suc (suc zero)) (suc zero) zero ))
```

<!--en-->
Separation now removes the surplus elements of the common container. The resulting set `seqL A` contains exactly those container elements satisfying the finite-environment description. Keeping the definition opaque affects normalization only; the mathematical content is fixed by the membership equation that follows.
<!--zh-->
现在用分离去除公共容器中的多余元素。所得集合 `seqL A` 恰好包含容器中满足有限环境描述的元素。保持定义不透明只影响归一化；其数学内容由随后给出的隶属等式完全确定。
<!--ja-->
ここで分出を用いて、共通の容器に含まれる余分な要素を除く。得られる集合 `seqL A` は、容器の要素のうち有限環境の記述を満たすものをちょうど含む。定義を不透明に保つことは正規化にだけ影響し、数学的内容は続く所属の等式によって完全に定まる。
<!--/-->

```agda
opaque
  seqL : S → S
  seqL A = hasSeparationL (amb A) (seqFo A) .fst .fst
```

<!--en-->
An element belongs to `seqL A` precisely when it both lies in the common container and satisfies `seqFo A`. Thus the container establishes set-sizedness, while the formula establishes exactness; neither part alone characterizes the set of all finite sequences.
<!--zh-->
一个元素属于 `seqL A`，当且仅当它既属于公共容器，又满足 `seqFo A`。因此容器保证这批对象组成集合，公式保证其准确性；任何一部分都不能单独刻画全部有限序列之集。
<!--ja-->
ある要素が `seqL A` に属すのは、それが共通の容器に属し、かつ `seqFo A` を満たすとき、そしてそのときに限る。容器は集合としての大きさを保証し、論理式は正確さを保証する。どちらか一方だけでは、すべての有限列の集合を特徴づけられない。
<!--/-->

```agda
  seqL-spec : (A x : S) → (x SL.∈ˢ seqL A)
            ≡ ((x SL.∈ˢ amb A) ⊓ ((x ∷ []) ⊨ seqFo A))
  seqL-spec A = hasSeparationL (amb A) (seqFo A) .fst .snd
```

<!--en-->
Every member of an environment set of length `n` belongs to `seqL A`. The proof reads the truncated presentation of the member and then introduces it into the separated set.
<!--zh-->
长度为 `n` 的环境集的每个成员都属于 `seqL A`。证明先读取该成员的截断呈现，再把它引入分离所得的集合。
<!--ja-->
長さ `n` の環境集合のすべての要素は `seqL A` に属する。証明は、その要素の切り詰められた提示を読み、その後に分出された集合の中へ導入する。
<!--/-->

```agda
seqL-in : (A : S) (n : ℕ) (x : S)
        → ⟨ fst x ∈ˢ fst (envSet A n) ⟩ → ⟨ fst x ∈ˢ fst (seqL A) ⟩
seqL-in A n x hx = rec₁ (snd (fst x ∈ˢ fst (seqL A))) from (envSet-out A n x hx)
  where
  from : Σ[ g ∈ Ix A n ] (fst x ≡ fst (envS A g)) → ⟨ fst x ∈ˢ fst (seqL A) ⟩
```

<!--en-->
The member is transported to its graph form, which is a member of the container by the bounding record; the description is then satisfied by the canonical entry.
<!--zh-->
该成员先被搬运到图形式。界定记录表明这个图属于容器，随后典范条目便满足相应描述。
<!--ja-->
その要素はグラフの形へ運ばれ、界定の記録によって容器の中にある。そして、正準な項目によって記述が充足される。
<!--/-->

```agda
  from (g , e) = subst (λ w → ⟨ w ∈ˢ fst (seqL A) ⟩) (sym e) canonical
    where
    canonical : ⟨ fst (envS A g) ∈ˢ fst (seqL A) ⟩
    canonical = subst ⟨_⟩ (sym (seqL-spec A (envS A g)))
      ( amb-in A (n , g)
```

<!--en-->
The description's witness consists of the numeral of the length, its membership in the internal `ω`, and the graph relation of the environment over `A`, all packaged in the truncated existential.
<!--zh-->
描述的见证由长度的数码、其在内部 `ω` 中的隶属，以及该环境在 `A` 上的图关系组成，全部打包进截断存在。
<!--ja-->
記述の証人は、長さの数項、内部の `ω` への所属、そして `A` の上の環境のグラフの関係からなり、すべて切り詰められた存在の中にまとめられる。
<!--/-->

```agda
      , ∣ nn n , (#∈ω n , ∣ A , (refl , envOver A g) ∣₁) ∣₁ )
```

<!--en-->
Conversely, membership in `seqL A` yields only the propositionally truncated assertion that some natural length `n` makes the member an element of `envSet A n`. The argument discards the container component of the separation equation and reads the existential information from the defining formula; it does not choose a length uniformly for all members.
<!--zh-->
反过来，属于 `seqL A` 只给出经过命题截断的断言：存在某个自然数长度 `n`，使该成员属于 `envSet A n`。论证舍去分离等式中的容器分量，从定义公式读取存在信息；它并未为所有成员一致地选取长度。
<!--ja-->
逆に、`seqL A` への所属から得られるのは、ある自然数の長さ `n` が存在し、その要素が `envSet A n` に属すという命題的に切り詰められた主張だけである。分出の等式のうち容器の成分を捨て、定義論理式から存在情報を読み取るが、すべての要素に対して長さを一様に選ぶわけではない。
<!--/-->

```agda
seqL-out : (A x : S) → ⟨ fst x ∈ˢ fst (seqL A) ⟩
         → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
seqL-out A x hx = rec₁ squash₁ step1 (subst ⟨_⟩ (seqL-spec A x) hx .snd)
  where
  step2 : (d : S) (k : ℕ) → # k ≡ fst d
```

<!--en-->
Inside one branch of the truncated witnesses, suppose the domain object `d` has been identified with the numeral `# k`, the base object `b` with `A`, and `x` satisfies the environment condition. For these fixed witnesses, recovery produces an assignment of length `k` and identifies `x` with its graph. The outer result is truncated again, so this local construction does not define a global decoder.
<!--zh-->
在截断见证的一个分支内，设定义域对象 `d` 已与数码 `# k` 等同，底对象 `b` 已与 `A` 等同，且 `x` 满足环境条件。对这些固定见证，恢复过程构造长度为 `k` 的赋值，并把 `x` 与其图等同。外层结果随即再次截断，所以这项局部构造并不定义全局解码器。
<!--ja-->
切り詰められた証人の一つの分岐の中で、定義域の対象 `d` が数項 `# k` と、基礎の対象 `b` が `A` と同一視され、`x` が環境条件を満たすとする。これらの固定された証人に対して、復元過程は長さ `k` の割り当てを構成し、`x` をそのグラフと同一視する。外側の結果は再び切り詰められるので、この局所的な構成は大域的な復号写像を定めない。
<!--/-->

```agda
        → Σ[ b ∈ S ] ((fst b ≡ fst A)
             × ⟨ (b ∷ d ∷ x ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩)
        → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
  step2 d k q (b , eb , hov) =
    ∣ k , subst (λ w → ⟨ w ∈ˢ fst (envSet A k) ⟩) (sym R.recovers) (envSet-in A R.g) ∣₁
```

<!--en-->
For the fixed length `k`, the environment clauses determine each entry uniquely: exactness of the domain gives mere existence, single-valuedness makes the entry fiber a proposition, and the value restriction places the recovered value in the presentation of `A`. Extensionality, using also the clause that every graph member has pair shape, then identifies the whole set `x` with the canonical environment graph.
<!--zh-->
在固定长度 `k` 下，环境的各项条件唯一确定每个条目：准确的定义域给出仅有的存在性，单值性使条目纤维成为命题，取值限制则把恢复出的值放入 `A` 的呈现。随后外延性还使用「图的每个成员都具有对形」这一条，把整个集合 `x` 与典范环境图等同。
<!--ja-->
長さ `k` を固定すると、環境の各条件がそれぞれの項目を一意に定める。正確な定義域が切り詰められた存在を与え、一価性が項目のファイバーを命題にし、値の制限が復元された値を `A` の提示に置く。さらに、グラフのすべての要素が対の形をもつという条件も用い、外延性によって集合 `x` 全体を標準的な環境のグラフと同一視する。
<!--/-->

```agda
    where
    module R = Recover A k (b ∷ d ∷ x ∷ []) (suc (suc zero)) (suc zero) zero
                 (sym q) eb hov using ( g; recovers )
```

<!--en-->
The remaining step eliminates the membership of the domain in `ω`: a member of `ω` is, merely, a numeral.
<!--zh-->
剩余步骤消去定义域在 `ω` 中的隶属：`ω` 的成员仅仅是某个数码。
<!--ja-->
残りの段階は、定義域の `ω` への所属を消去する。`ω` の要素は、単に、ある数項である。
<!--/-->

```agda
  step1 : Σ[ d ∈ S ] (⟨ fst d ∈ˢ ω ⟩
            × ∥ Σ[ b ∈ S ] ((fst b ≡ fst A)
                 × ⟨ (b ∷ d ∷ x ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩) ∥₁)
        → ∥ Σ[ n ∈ ℕ ] ⟨ fst x ∈ˢ fst (envSet A n) ⟩ ∥₁
  step1 (d , d∈ω , h) = rec₁ squash₁
```

<!--en-->
The numeral is fed into the conversion step, completing the reading direction. Note the strength: the length and the environment are recovered only within the truncation, and no global decoder from `seqL A` to assignments is produced.
<!--zh-->
数码被喂入转换步骤，读取方向完成。注意其强度：长度与环境只在截断之内被恢复，并未产出从 `seqL A` 到赋值的全局解码器。
<!--ja-->
数項が変換の一歩に渡され、読みの方向が完成する。強さに注意してほしい。長さと環境は切り詰めの中でだけ復元され、`seqL A` から割り当てへの大域的な復号器が作られるわけではない。
<!--/-->

```agda
    (λ { (k , q) → rec₁ squash₁ (step2 d (lower k) q) h }) d∈ω
```

<!--en-->
## Folding a finite sequence into one ordinal code
<!--zh-->
## 把有限序列折叠成一个序数码
<!--ja-->
## 有限列を一つの順序数コードへ畳み込む
<!--/-->

<!--en-->
The coding module fixes the data of the pairing function. Its parameters are an ordinal `α`, a proof that `α` is not a member of `ω` (the form of infinitude used here), and a constructible graph `F` together with three clauses: single-valuedness, totality on the product, and injectivity.
<!--zh-->
编码模块固定配对函数的数据。其参数包括序数 `α`、`α` 不属于 `ω` 的证明，以及可构造图 `F` 连同三条子句：单值性、在乘积上的全域性和单射性。这里以 `α ∉ ω` 表述所需的无穷性。
<!--ja-->
符号化のモジュールは、対の関数のデータを固定する。引数は、順序数 `α`、`α` が `ω` に属さないこと、すなわちこの章が使う形での無限性の仮定、そして構成可能なグラフ `F` と、一価性・積の上の全域性・単射性という三つの節である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Code (α : S) (oα : IsOrd (fst α)) (α∉ω : ⟨ fst α ∈ˢ ω ⟩ → ⊥₀)
            (F : S)
            (sv : ⟨ (F ∷ prodL α ∷ []) ⊨ svAt zero ⟩)
            (dm : ⟨ (F ∷ prodL α ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ij : ⟨ (F ∷ prodL α ∷ []) ⊨ injAt zero ⟩)
            (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                 → ⟨ fst y ∈ fst α ⟩) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The last hypothesis is the range condition in meta-level form: every value recorded by the graph belongs to `α`. Together the four clauses say that `F` is an internal coded injection from the product `α × α` into `α`.
<!--zh-->
最后一条假设是元层形式的值域条件：图记录的每个值都属于 `α`。四条条款合起来说：`F` 是从乘积 `α × α` 到 `α` 的内部编码单射。
<!--ja-->
最後の仮定は、メタレベルの形での値域の条件である。グラフに記録されたすべての値は `α` に属する。四つの節合わせて、`F` が積 `α × α` から `α` への内部の符号化された単射であることを言う。
<!--/-->

<!--en-->
The carrier of inputs and values is the type of constructible sets together with membership in `α`: an entry of the product must lie in `α`, and so must every value.
<!--zh-->
输入与值的载体是「可构造集合连同属于 `α` 的证明」这一类型：乘积的条目必须落在 `α` 中，每个值也一样。
<!--ja-->
入力と値の台は、構成可能な集合と `α` への所属の対の型である。積の項目も、すべての値も、`α` の中になければならない。
<!--/-->

```agda
  M : Type (ℓ-suc ℓ)
  M = Σ[ v ∈ S ] ⟨ fst v ∈ˢ fst α ⟩
```

<!--en-->
Numerals become elements of the carrier: since `α` is not in `ω`, the infinitude of `α` places every numeral inside `α`. This is the only use of the infinitude hypothesis in the fold.
<!--zh-->
数码成为载体的元素：由于 `α` 不属于 `ω`，`α` 的无穷性把每个数码放入 `α` 之内。这是无穷性假设在折叠中的唯一用场。
<!--ja-->
数項は台の要素になる。`α` が `ω` に属さないため、`α` の無限性がすべての数項を `α` の中に置くからである。これが、畳み込みにおける無限性の仮定の唯一の用途である。
<!--/-->

```agda
  num : ℕ → M
  num k = nn k , ω⊆ (fst α) oα α∉ω (# k) (#∈ω k)
```

<!--en-->
Presentation indices of `α` also become elements of the carrier, with constructibility transported along the membership of `α` and membership witnessed by the presentation.
<!--zh-->
`α` 的呈现索引也成为载体元素：可构造性沿 `α` 的隶属搬运，而隶属由呈现见证。
<!--ja-->
`α` の提示の索引も台の要素になる。構成可能性は `α` の所属に沿って運ばれ、所属は提示によって証明される。
<!--/-->

```agda
  up : ⟪ fst α ⟫ → M
  up m = (⟪ fst α ⟫↪ m , isL-trans (member (fst α) m) (snd α)) , member (fst α) m
```

<!--en-->
Single-valuedness together with the exact-domain clause turns the graph `F` into an actual host function on members of `prodL α`. Domain membership initially gives only a truncated output, but the fiber of possible outputs is a proposition, so its unique value can be extracted. The separate hypothesis `ij` is still needed to conclude that equal outputs have equal inputs.
<!--zh-->
单值性与准确的定义域子句共同把图 `F` 读成 `prodL α` 成员上的实际宿主函数。定义域隶属起初只给出截断的输出，但可能输出所成的纤维是命题，故可提取其中的唯一取值。要从输出相等推出输入相等，仍须另用假设 `ij`。
<!--ja-->
一価性と正確な定義域の条件を合わせると、グラフ `F` を `prodL α` の要素上の実際のホスト関数として読める。定義域への所属から最初に得られる出力は切り詰められているが、可能な出力のファイバーは命題なので、その一意な値を取り出せる。等しい出力から入力の等しさを結論するには、別の仮定 `ij` がなお必要である。
<!--/-->

```agda
  module E = Extract F (prodL α) sv dm using ( toFun; toFun-graph; toFun-inj )
```

<!--en-->
The coded pair of two carrier elements belongs to the product: both coordinates are in `α`, and the pair operation transports this into membership in `prodL α`.
<!--zh-->
两个载体元素的编码对属于乘积：两个坐标都在 `α` 中，配对运算把这一点转化为对 `prodL α` 的隶属。
<!--ja-->
台の二つの要素の符号化された対は積の中にある。両方の座標が `α` の中にあり、対の演算がそれを `prodL α` への所属に変えるからである。
<!--/-->

```agda
  opaque
    pairMem : (a u : M) → ⟨ fst (prʟ (fst a) (fst u)) ∈ˢ fst (prodL α) ⟩
    pairMem a u = subst (λ w → ⟨ w ∈ˢ fst (prodL α) ⟩) (sym (prʟ-fst (fst a) (fst u)))
                    (prodL-in α (fst a) (fst u) (snd a) (snd u))
```

<!--en-->
For an input `x` already known to belong to `prodL α`, define `val x` to be the unique output recorded by `F` at `x`. The membership proof is part of the input because the graph is required to be total exactly on the product, not on every constructible set.
<!--zh-->
对已经知道属于 `prodL α` 的输入 `x`，定义 `val x` 为 `F` 在 `x` 处记录的唯一输出。隶属证明是输入数据的一部分，因为图只被要求恰好在该乘积上全域，而非在每个可构造集合上全域。
<!--ja-->
`prodL α` に属すことが分かっている入力 `x` に対し、`val x` を `F` が `x` に記録する一意な出力と定める。所属の証明も入力データに含めるのは、グラフが全域的であると要求されるのがちょうどこの積の上だけであり、すべての構成可能集合の上ではないからである。
<!--/-->

```agda
  opaque
    val : (x : S) → ⟨ fst x ∈ˢ fst (prodL α) ⟩ → S
    val x mx = E.toFun (x , mx)
```

<!--en-->
The graph record states that the pair of the input and the value belongs to `F`, which is the data the later identification lemmas consume.
<!--zh-->
图记录陈述：输入与值构成的有序对属于 `F`；这正是后文同一视引理所消耗的数据。
<!--ja-->
グラフの記録は、入力と値の順序対が `F` に属することを述べる。これが、後の同一視の補題が消費するデータである。
<!--/-->

```agda
    val-graph : (x : S) (mx : ⟨ fst x ∈ˢ fst (prodL α) ⟩)
              → ⟨ pr (fst x) (fst (val x mx)) ∈ fst F ⟩
    val-graph x mx = E.toFun-graph (x , mx)
```

<!--en-->
The graph is injective on the product: two points with equal values have equal underlying sets. Together with the extraction, this is the injectivity half of the pairing function.
<!--zh-->
图在乘积上单射：值相等的两点底层集合相等。与提取合在一起，这是配对函数的单射一半。
<!--ja-->
グラフは積の上で単射である。同じ値をもつ二つの点は、底の集合が等しくなる。抽出と合わせて、これが対の関数の単射の半分である。
<!--/-->

```agda
    val-inj : (x : S) (mx : ⟨ fst x ∈ˢ fst (prodL α) ⟩)
              (x' : S) (mx' : ⟨ fst x' ∈ˢ fst (prodL α) ⟩)
            → fst (val x mx) ≡ fst (val x' mx') → fst x ≡ fst x'
    val-inj x mx x' mx' = E.toFun-inj ij (x , mx) (x' , mx')
```

<!--en-->
The binary operation `app a u` evaluates `F` at the internal ordered pair of `a` and `u`. Its value is already a constructible set because it comes from the graph fiber, and the range clause supplies the additional proof that this value lies in `α`. Hence `app` is closed on the carrier `M`.
<!--zh-->
二元运算 `app a u` 在 `a` 与 `u` 的内部有序对处求图 `F` 的值。这个取值来自图纤维，因而已经是可构造集合；值域子句再提供它属于 `α` 的证明。因此 `app` 在载体 `M` 上封闭。
<!--ja-->
二項演算 `app a u` は、`a` と `u` の内部順序対におけるグラフ `F` の値を取る。その値はグラフのファイバーから得られるので、すでに構成可能集合である。さらに値域の条件が、その値が `α` に属すことを証明する。したがって `app` は台 `M` 上で閉じている。
<!--/-->

```agda
  opaque
    app : M → M → M
    app a u = val (prʟ (fst a) (fst u)) (pairMem a u)
            , ran (prʟ (fst a) (fst u)) (val (prʟ (fst a) (fst u)) (pairMem a u))
                (val-graph (prʟ (fst a) (fst u)) (pairMem a u))
```

<!--en-->
Evaluation does not lose contact with the internal graph. The theorem `app-graph` records that the pair whose input is the ambient code of `(a,u)` and whose output is `app a u` belongs to `F`. The projection equation for the constructible pair supplies the needed identification of the two input codes.
<!--zh-->
求值并未失去与内部图的联系。定理 `app-graph` 记录：以 `(a,u)` 的外围对码为输入、以 `app a u` 为输出的有序对属于 `F`。可构造有序对的投影等式提供两种输入码之间所需的等同。
<!--ja-->
値を取り出しても、内部グラフとのつながりは失われない。定理 `app-graph` は、`(a,u)` の周囲の対符号を入力とし、`app a u` を出力とする順序対が `F` に属すことを記録する。構成可能な対の射影等式が、二つの入力符号の間に必要な同一視を与える。
<!--/-->

```agda
    app-graph : (a u : M)
              → ⟨ pr (pr (fst (fst a)) (fst (fst u))) (fst (fst (app a u))) ∈ fst F ⟩
    app-graph a u = subst (λ w → ⟨ pr w (fst (fst (app a u))) ∈ fst F ⟩)
                      (prʟ-fst (fst a) (fst u))
                      (val-graph (prʟ (fst a) (fst u)) (pairMem a u))
```

<!--en-->
If two applications have equal outputs, injectivity of `F` first identifies their encoded pair inputs. Injectivity of the ordered-pair code then separates this equality into equality of the two first coordinates and equality of the two second coordinates. Thus one application layer can be peeled off without constructing an inverse to `F`.
<!--zh-->
若两次应用的输出相等，`F` 的单射性先认同它们的编码对输入。有序对码的单射性再把这条相等拆成两个第一坐标相等与两个第二坐标相等。因此可以剥去一层应用，而无需构造 `F` 的逆函数。
<!--ja-->
二つの適用の出力が等しければ、まず `F` の単射性によって、それらの符号化された対入力が同一視される。次に順序対符号の単射性が、この等しさを二つの第一座標の等しさと二つの第二座標の等しさへ分ける。したがって、`F` の逆関数を構成せずに、適用を一層ずつ剥がせる。
<!--/-->

```agda
    app-inj : (a u a' u' : M) → fst (fst (app a u)) ≡ fst (fst (app a' u'))
            → (fst (fst a) ≡ fst (fst a')) × (fst (fst u) ≡ fst (fst u'))
    app-inj a u a' u' e = pr-inj
      (sym (prʟ-fst (fst a) (fst u))
       ∙ val-inj (prʟ (fst a) (fst u)) (pairMem a u) (prʟ (fst a') (fst u')) (pairMem a' u') e
```

<!--en-->
The comparison of pair inputs passes from constructible pair codes to their ambient Kuratowski codes and back. After these transports, pair injectivity yields exactly the two component equalities required by `app-inj`; no equality of the accompanying membership proofs is needed.
<!--zh-->
对输入对的比较先从可构造对码转到外围 Kuratowski 对码，再转回去。完成这些搬运后，有序对的单射性恰好给出 `app-inj` 所需的两条分量相等；无需比较随附的隶属证明。
<!--ja-->
対入力の比較では、構成可能な対符号から周囲のクラトフスキー対符号へ移り、さらに戻る。これらの輸送の後、対の単射性が `app-inj` に必要な二つの成分の等しさをちょうど与える。付随する所属の証明を比較する必要はない。
<!--/-->

```agda
       ∙ prʟ-fst (fst a') (fst u'))
```

<!--en-->
The companion uniqueness fact runs in the forward direction. If `F` records some value `w` at the pair `(a,u)`, then `w` must equal the already extracted value `app a u`. This is functionality of the graph, independent of its injectivity across different inputs.
<!--zh-->
配套的唯一性事实沿正向使用图。若 `F` 在输入对 `(a,u)` 处记录某个取值 `w`，则 `w` 必须等于已经提取的取值 `app a u`。这是图的单值性，与不同输入之间的单射性无关。
<!--ja-->
対になる一意性の事実は、グラフを順方向に用いる。`F` が入力対 `(a,u)` にある値 `w` を記録しているなら、`w` はすでに取り出した値 `app a u` と等しくなければならない。これはグラフの一価性であり、異なる入力の間の単射性とは独立である。
<!--/-->

```agda
    app-uniq : (a u : M) (w : S)
             → ⟨ pr (pr (fst (fst a)) (fst (fst u))) (fst w) ∈ fst F ⟩
             → fst w ≡ fst (fst (app a u))
    app-uniq a u w h =
      svAt-out zero (F ∷ prodL α ∷ []) sv (prʟ (fst a) (fst u)) w (fst (app a u))
```

<!--en-->
To apply single-valuedness, the supplied membership is first transported from the ambient pair code to the constructible pair used by `val`. It is then compared with `val-graph`, the canonical membership for the extracted value. Since both entries now have the same input, the single-valuedness clause identifies their outputs.
<!--zh-->
为应用单值性，先把给定的隶属从外围对码搬运到 `val` 所用的可构造对。随后将它与 `val-graph` 给出的典范图隶属比较。此时两条记录具有相同输入，单值性子句便认同它们的输出。
<!--ja-->
一価性を適用するため、まず与えられた所属を周囲の対符号から `val` が用いる構成可能な対へ輸送する。次に、それを抽出された値についての標準的な所属 `val-graph` と比較する。二つの項目は同じ入力をもつので、一価性の条件がそれらの出力を同一視する。
<!--/-->

```agda
        (subst (λ z → ⟨ pr z (fst w) ∈ fst F ⟩) (sym (prʟ-fst (fst a) (fst u))) h)
        (val-graph (prʟ (fst a) (fst u)) (pairMem a u))
```

<!--en-->
The environment reader is extended to a total function on the numerals: outside the range of the sequence it returns the numeral zero. This junk value carries no mathematical meaning; every later use reads the extension only at indices below the length.
<!--zh-->
环境读取被延拓为数码上的全函数：在序列范围之外它返回数码零。这个垃圾值不携带数学含义；后文的一切使用都只在长度以下的索引处读取该延拓。
<!--ja-->
環境の読みは、数項の上の全域的な関数へ延長される。列の範囲の外では数項のゼロを返す。この既定の値に数学的な意味はなく、後の使用はすべて、長さより下の索引でだけこの延長を読む。
<!--/-->

```agda
  ext : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → ℕ → M
  ext zero    g k       = num zero
  ext (suc n) g zero    = up (g zero)
  ext (suc n) g (suc k) = ext n (λ i → g (suc i)) k
```

<!--en-->
At every index below the length, the extension reads back exactly the entry of the sequence, by a recursion on the index.
<!--zh-->
由对索引的递归，在长度以下的每个索引处，延拓读回的恰是序列的该条目。
<!--ja-->
索引についての再帰により、長さより下のどの索引でも、延長は列のその項目をちょうど読み戻す。
<!--/-->

```agda
  ext-at : (n : ℕ) (g : Fin n → ⟪ fst α ⟫) (i : Fin n) → ext n g (toℕ i) ≡ up (g i)
  ext-at (suc n) g zero    = refl
  ext-at (suc n) g (suc i) = ext-at n (λ j → g (suc j)) i
```

<!--en-->
With the length `n` and sequence `g` fixed, `chain n g k` is defined by recursion on the step counter `k`. It starts at the numeral zero, and each step with `k<n` applies the pairing function to the next entry `g(k)` and the value accumulated so far. Thus `chain n g n` has consumed exactly the `n` entries of the sequence; behavior after that bound depends only on the meaningless default supplied by `ext` and is not part of the sequence code.
<!--zh-->
固定长度 `n` 与序列 `g` 后，`chain n g k` 按步数参数 `k` 递归定义。初值为数码零；在每个满足 `k<n` 的步骤中，配对函数作用于下一条目 `g(k)` 与此前的累积值。因此 `chain n g n` 恰好消耗序列的 `n` 个条目；超过此界后的行为只依赖 `ext` 给出的无意义默认值，不属于序列码的数学内容。
<!--ja-->
長さ `n` と列 `g` を固定すると、`chain n g k` は段階数 `k` についての再帰で定義される。初期値は零の数項であり、`k<n` を満たす各段階では、対の関数を次の項 `g(k)` とそれまでの累積値に適用する。したがって `chain n g n` は列の `n` 個の項をちょうどすべて消費する。この範囲を越えた後の振る舞いは `ext` の無意味な既定値だけに依存し、列の符号の数学的内容には含まれない。
<!--/-->

```agda
  chain : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → ℕ → M
  chain n g zero    = num zero
  chain n g (suc k) = app (ext n g k) (chain n g k)
```

<!--en-->
For a sequence of length `n`, the fold ends at `vₙ = chain n g n`. Its code is then `F(n,vₙ)`: the length numeral is the first coordinate of the final pairing, and the folded value is the second. This gives an actual value once `n` and `g` are given. It neither says that every element of `α` is a code nor defines a decoder on all of `α`.
<!--zh-->
对长度为 `n` 的序列，折叠终止于 `vₙ = chain n g n`。其码定义为 `F(n,vₙ)`：最终配对的第一坐标是长度数码，第二坐标是折叠值。给定 `n` 与 `g` 后，这一定义产出实际取值；它既不声称 `α` 的每个元素都是码，也不定义 `α` 全域上的解码器。
<!--ja-->
長さ `n` の列では、畳み込みは `vₙ = chain n g n` で終わる。その符号を `F(n,vₙ)` と定める。最後の対の第一座標が長さの数項、第二座標が畳み込み値である。`n` と `g` が与えられれば、これは実際の値を与える。`α` のすべての要素が符号であるとも、`α` 全体上の復号写像があるとも述べていない。
<!--/-->

```agda
  code : (n : ℕ) → (Fin n → ⟪ fst α ⟫) → M
  code n g = app (num n) (chain n g n)
```

<!--en-->
Suppose two fold chains agree after `k` steps. Then their entries agree at every position `j<k`. The induction runs backward through the chain: equality at stage `k+1` is split by injectivity of `F` into equality of the entries used at stage `k` and equality of the preceding chain values.
<!--zh-->
设两条折叠链在 `k` 步后相等，则它们在每个位置 `j<k` 的条目都相等。归纳沿链反向进行：第 `k+1` 阶段的相等经 `F` 的单射性分解为第 `k` 阶段所用条目的相等，以及此前链值的相等。
<!--ja-->
二つの畳み込みの鎖が `k` 段後に一致すると仮定すると、各位置 `j<k` の項も一致する。帰納は鎖を後ろ向きにたどる。段階 `k+1` での等しさを `F` の単射性で分けると、段階 `k` で用いた項の等しさと、一つ前の鎖の値の等しさが得られる。
<!--/-->

```agda
  chain-inj : (n : ℕ) (g g' : Fin n → ⟪ fst α ⟫) (k : ℕ)
            → fst (fst (chain n g k)) ≡ fst (fst (chain n g' k))
            → (j : ℕ) → j < k → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))
  chain-inj n g g' zero    e j j<0  = ⊥₀-rec (¬-<-zero j<0)
  chain-inj n g g' (suc k) e j j<sk = go (<-split j<sk)
```

<!--en-->
At a successor stage, `app-inj` supplies those two equalities. If `j=k`, the first one is the desired entry equality; if `j<k`, the second one lets the induction hypothesis continue with the shorter chain. This is a cancellation argument between two known valid folds, not a procedure that turns an arbitrary element of `α` into a sequence.
<!--zh-->
在后继阶段，`app-inj` 给出这两条相等。若 `j=k`，第一条正是所需的条目相等；若 `j<k`，第二条使归纳假设可用于更短的链。这是在两条已知合法折叠之间作消去，并不是把 `α` 的任意元素变成序列的过程。
<!--ja-->
後者段階では、`app-inj` がこの二つの等しさを与える。`j=k` なら第一の等しさが求める項の等しさであり、`j<k` なら第二の等しさによって短い鎖へ帰納仮定を適用できる。これは既知の正しい二つの畳み込みの間の消去論法であり、`α` の任意の要素を列へ変える手続きではない。
<!--/-->

```agda
    where
    q = app-inj (ext n g k) (chain n g k) (ext n g' k) (chain n g' k) e
    go : (j < k) ⊎ (j ≡ k) → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))
    go (inl j<k) = chain-inj n g g' k (snd q) j j<k
    go (inr j≡k) = subst (λ j → fst (fst (ext n g j)) ≡ fst (fst (ext n g' j))) (sym j≡k) (fst q)
```

<!--en-->
The length tag now proves its purpose. If two codes are equal, injectivity of the outer application first recovers equality of their length numerals and hence equality of their natural-number lengths. After transporting to one common length, backward cancellation of the fold gives entrywise equality, so the two environment graphs have equal underlying sets. Only this implication is asserted.
<!--zh-->
长度标签在此发挥作用。若两个码相等，外层应用的单射性先恢复长度数码的相等，继而得到自然数长度相等。把两条序列传输到同一长度后，沿折叠反向消去便得到逐项相等，因而两个环境图的底层集合相等。这里仅断言这一方向。
<!--ja-->
ここで長さのタグが役割を果たす。二つの符号が等しければ、外側の適用の単射性からまず長さの数項が等しく、したがって自然数としての長さも等しいことが分かる。共通の長さへ輸送した後、畳み込みを後ろ向きに消去すると各項が一致し、二つの環境グラフの底集合も等しくなる。ここで述べるのはこの向きだけである。
<!--/-->

```agda
  code-inj : (n : ℕ) (g : Fin n → ⟪ fst α ⟫) (n' : ℕ) (g' : Fin n' → ⟪ fst α ⟫)
           → fst (fst (code n g)) ≡ fst (fst (code n' g'))
           → fst (envS α g) ≡ fst (envS α g')
  code-inj n g n' g' e = subst P (#-inj′ (fst q)) same g' (snd q)
    where
```

<!--en-->
The pair `q` separates the code equation into equality of the numeral coordinates and equality of the terminal fold values. The family `P m` records exactly what remains to prove for a sequence of length `m`, allowing numeral injectivity to transport the second sequence and its fold equation to the original length `n`.
<!--zh-->
成对的结论 `q` 把码等式分成数码坐标的相等与终端折叠值的相等。族 `P m` 准确记录长度为 `m` 时尚待证明的结论，使数码单射性能够把第二条序列及其折叠等式传输到原长度 `n`。
<!--ja-->
対になった結論 `q` は、符号の等式を数項座標の等しさと終端の畳み込み値の等しさに分ける。族 `P m` は、長さ `m` の列について残る主張を正確に記録する。これにより、数項の単射性に沿って第二の列とその畳み込みの等式をもとの長さ `n` へ輸送できる。
<!--/-->

```agda
    q = app-inj (num n) (chain n g n) (num n') (chain n' g' n') e
    P : ℕ → Type (ℓ-suc ℓ)
    P m = (h : Fin m → ⟪ fst α ⟫)
        → fst (fst (chain n g n)) ≡ fst (fst (chain m h m))
        → fst (envS α g) ≡ fst (envS α h)
```

<!--en-->
Once the lengths coincide, equality of the environment graphs follows from function extensionality. For each finite index `i`, the proof compares the corresponding presented members of `α`; injectivity of the presentation embedding reduces their equality to equality of the underlying sets recovered from the two chains.
<!--zh-->
长度一致后，环境图的相等由函数外延性推出。对每个有穷索引 `i`，证明比较 `α` 的两个相应呈现成员；呈现嵌入的单射性把成员相等化为从两条链恢复的底层集合相等。
<!--ja-->
長さが一致すれば、環境グラフの等しさは関数外延性から従う。各有限添字 `i` について、`α` の提示における対応する二要素を比較する。提示の埋め込みの単射性により、その等しさは二つの鎖から得た底集合の等しさへ帰着する。
<!--/-->

```agda
    same : P n
    same h e' = cong (λ (f : Fin n → ⟪ fst α ⟫) → fst (envS α f)) (funExt pt)
      where
      pt : (i : Fin n) → g i ≡ h i
      pt i = ↪-inj {a = fst α}
```

<!--en-->
The comparison at `i` begins by using `ext-at` to identify the bounded total function `ext n g` with the genuine entry `g i`. The chain-cancellation lemma supplies equality of the two extended entries because `toℕ i<n`, and a second use of `ext-at` identifies the other side with `h i`. Values of `ext` outside this bound play no mathematical role.
<!--zh-->
位置 `i` 处的比较先用 `ext-at` 把有界全域函数 `ext n g` 的取值认同为真正条目 `g i`。由于 `toℕ i<n`，链消去引理给出两个全域取值的相等；再次使用 `ext-at`，便把另一端认同为 `h i`。`ext` 在此界之外的取值不具数学作用。
<!--ja-->
位置 `i` での比較では、まず `ext-at` によって全域関数 `ext n g` の有界位置での値を本来の項 `g i` と同一視する。`toℕ i<n` なので鎖の消去補題から二つの全域関数の値が等しいと分かり、もう一度 `ext-at` を用いて他方を `h i` と同一視する。この範囲外での `ext` の値には数学的な意味を持たせない。
<!--/-->

```agda
        ( sym (cong (λ z → fst (fst z)) (ext-at n g i))
        ∙ chain-inj n g h n e' (toℕ i) (toℕ<n i)
        ∙ cong (λ z → fst (fst z)) (ext-at n h i) )
```

<!--en-->
To describe one recursive transition semantically, fix an index object `i`. A `StepAt s C i` merely records objects `j,a,u,w` such that `j` is the successor of `i`, the sequence graph gives `s(i)=a`, the trace gives `C(i)=u` and `C(j)=w`, and the graph `F` gives `F(a,u)=w`. The whole package is propositionally truncated.
<!--zh-->
为在语义层描述一次递归转移，固定索引对象 `i`。`StepAt s C i` 仅记录对象 `j,a,u,w`，满足：`j` 是 `i` 的后继，序列图给出 `s(i)=a`，轨迹给出 `C(i)=u` 与 `C(j)=w`，而图 `F` 给出 `F(a,u)=w`。整组数据经过命题截断。
<!--ja-->
再帰の一回の遷移を意味論的に記述するため、添字対象 `i` を固定する。`StepAt s C i` は、`j` が `i` の後者であり、列のグラフが `s(i)=a`、軌跡が `C(i)=u` と `C(j)=w`、グラフ `F` が `F(a,u)=w` を与えるような対象 `j,a,u,w` を記録するだけである。このデータ全体は命題的に切り詰められている。
<!--/-->

```agda
  StepAt : (s C i : S) → Type (ℓ-suc ℓ)
  StepAt s C i = ∥ Σ[ j ∈ S ] Σ[ a ∈ S ] Σ[ u ∈ S ] Σ[ w ∈ S ]
      ( (fst j ≡ sucV (fst i))
      × ⟨ pr (fst i) (fst a) ∈ fst s ⟩
      × ⟨ pr (fst i) (fst u) ∈ fst C ⟩
```

<!--en-->
The last membership assertion is the recurrence equation written as a graph fact. Its input is the ordered pair `(a,u)`, and its output is `w`. Thus `StepAt` is the host-level meaning that the later first-order step formula must express; it does not yet add any decoder or choice of a global trace.
<!--zh-->
最后一条隶属断言把递推等式写成图事实：输入是有序对 `(a,u)`，输出是 `w`。因此 `StepAt` 是稍后的一阶步进公式所要表达的宿主层含义；它尚未加入任何解码器，也未选择一条全局轨迹。
<!--ja-->
最後の所属の主張は、漸化式をグラフの事実として書いたものである。入力は順序対 `(a,u)`、出力は `w` である。したがって `StepAt` は、後の一階のステップ論理式が表すべきホスト側の意味であり、復号写像や大域的な軌跡の選択を加えるものではない。
<!--/-->

```agda
      × ⟨ pr (fst j) (fst w) ∈ fst C ⟩
      × ⟨ pr (pr (fst a) (fst u)) (fst w) ∈ fst F ⟩ ) ∥₁
```

<!--en-->
`DomIs s n` says that `n` is exactly the domain of the sequence graph `s`. Every `x∈n` has some value `y` with `(x,y)∈s`, while every pair `(x,y)∈s` has its first coordinate `x` in `n`. Existence of a value is retained only propositionally; uniqueness comes from the separate environment conditions when it is needed.
<!--zh-->
`DomIs s n` 表示 `n` 恰是序列图 `s` 的定义域。每个 `x∈n` 都有某个 `y` 使 `(x,y)∈s`，而每个 `(x,y)∈s` 的第一坐标 `x` 都属于 `n`。取值的存在性只以命题截断保留；需要唯一性时，则由另行给出的环境条件保证。
<!--ja-->
`DomIs s n` は、`n` が列のグラフ `s` のちょうど定義域であることを述べる。各 `x∈n` には `(x,y)∈s` となる値 `y` があり、逆に `(x,y)∈s` なら第一座標 `x` は `n` に属する。値の存在は命題的切り詰めのもとでだけ保たれ、一意性が必要な箇所では別の環境条件を用いる。
<!--/-->

```agda
  DomIs : (s n : S) → Type (ℓ-suc ℓ)
  DomIs s n = (x : S)
    → (⟨ fst x ∈ fst n ⟩ → ∥ Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst s ⟩ ∥₁)
    × ((y : S) → ⟨ pr (fst x) (fst y) ∈ fst s ⟩ → ⟨ fst x ∈ fst n ⟩)
```

<!--en-->
`EnvC m C` says that `C` is an environment over `α` with exact domain `m`. Through `envOverAt`, this includes single-valuedness, the domain condition, the requirement that all values lie in `α`, and the requirement that every member of `C` is an ordered pair. Here `m` will be the successor of the sequence length, so the trace has positions from `0` through `n`.
<!--zh-->
`EnvC m C` 表示 `C` 是取值于 `α`、定义域恰为 `m` 的环境。通过 `envOverAt`，这同时包含单值性、定义域条件、所有取值均属于 `α`，以及 `C` 的每个成员都是有序对。这里 `m` 将是序列长度的后继，因此轨迹具有从 `0` 到 `n` 的各个位置。
<!--ja-->
`EnvC m C` は、`C` が `α` に値を取り、ちょうど `m` を定義域とする環境であることを述べる。`envOverAt` には、一価性、定義域の条件、すべての値が `α` に属すこと、そして `C` の各要素が順序対であることが含まれる。ここで `m` は列の長さの後者になるので、軌跡は `0` から `n` までの位置をもつ。
<!--/-->

```agda
  EnvC : (m C : S) → Type (ℓ-suc ℓ)
  EnvC m C = ⟨ (α ∷ m ∷ C ∷ []) ⊨ envOverAt (suc (suc zero)) (suc zero) zero ⟩
```

<!--en-->
The complete semantic witness begins with a numeral `n∈ω`, its successor `m`, and a trace environment `C`. It requires `s` to have domain `n`, `C` to have domain `m` and values in `α`, and the trace to start at `C(0)=0`. A transition is supplied for each `i∈n`, followed by a final value at `C(n)` whose pairing with `n` yields `y`. This witness is propositionally truncated.
<!--zh-->
完整的语义见证先给出数码 `n∈ω`、其后继 `m` 与轨迹环境 `C`。它要求 `s` 的定义域为 `n`，`C` 的定义域为 `m` 且取值于 `α`，并以 `C(0)=0` 开始。随后对每个 `i∈n` 给出一次转移，最后给出 `C(n)` 处的取值，使它与 `n` 配对后得到 `y`。这项见证经过命题截断。
<!--ja-->
完全な意味論的証人は、数項 `n∈ω`、その後者 `m`、軌跡の環境 `C` から始まる。`s` の定義域が `n`、`C` の定義域が `m` で値が `α` に属し、軌跡が `C(0)=0` から始まることを要求する。各 `i∈n` について一つの遷移を与え、最後に `C(n)` の値を `n` と対にすると `y` になることを記録する。この証人は命題的に切り詰められている。
<!--/-->

```agda
  Wit : (y s : S) → Type (ℓ-suc ℓ)
  Wit y s = ∥ Σ[ n ∈ S ] Σ[ m ∈ S ] Σ[ C ∈ S ]
      ( ⟨ fst n ∈ ω ⟩
      × (fst m ≡ sucV (fst n))
      × DomIs s n
```

<!--en-->
The last component separates the terminal trace value from the length tag. It gives some `v` with `(n,v)∈C` and `F(n,v)=y`. The transition clauses determine `v` as the result after `n` folds; this final application of `F` then records the length and prevents sequences of different lengths from sharing a code.
<!--zh-->
最后一个分量把终端轨迹值与长度标签分开记录。它给出某个 `v`，满足 `(n,v)∈C` 且 `F(n,v)=y`。转移子句把 `v` 确定为 `n` 次折叠后的结果；最后这次 `F` 的应用再记录长度，使不同长度的序列不能具有相同码。
<!--ja-->
最後の成分は、軌跡の終端値と長さのタグを分けて記録する。ある `v` について `(n,v)∈C` かつ `F(n,v)=y` を与える。遷移の条件が `v` を `n` 回の畳み込み後の値として決定し、最後の `F` の適用が長さを記録するため、長さの異なる列が同じ符号をもつことはない。
<!--/-->

```agda
      × EnvC m C
      × ⟨ pr (# zero) (# zero) ∈ fst C ⟩
      × ((i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C i)
      × ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                     × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁ ) ∥₁
```

<!--en-->
Nested quantifiers shift the de Bruijn positions of every previously available variable. The abbreviations `i0,i1,…` name these positions uniformly: `i0` is the newest bound variable, and each successor moves one place outward. This bookkeeping lets the formulas below state the finite-trace equations without obscuring which object each occurrence denotes.
<!--zh-->
嵌套量词会移动此前各变元的 de Bruijn 位置。缩写 `i0,i1,…` 统一命名这些位置：`i0` 是最新约束的变元，每取一次后继便向外移动一位。借助这套记号，下列公式能够陈述有限轨迹等式，并保持每次出现所指对象清楚可辨。
<!--ja-->
量化子を入れ子にすると、それまで使えた各変数の de Bruijn 位置がずれる。略記 `i0,i1,…` はこれらの位置を一様に表し、`i0` が直前に束縛された変数、後者を一回取るごとに一つ外側の変数を指す。この記法により、以下の論理式は各出現がどの対象を指すかを保ったまま有限軌跡の等式を述べられる。
<!--/-->

```agda
  private
    i0 : ∀ {k} → Fin (suc k)
    i0 = zero
    i1 : ∀ {k} → Fin (suc (suc k))
    i1 = suc i0
```

<!--en-->
The names through `i4` cover the shallow part of the trace formulas: the current index, its successor, and the nearby values introduced for one recurrence step. Their polymorphic lengths allow the same position name to be reused after further binders have been added.
<!--zh-->
从 `i0` 到 `i4` 的名称覆盖轨迹公式的浅层部分，包括当前索引、其后继，以及一次递推步骤中新引入的邻近取值。它们的长度参数是多态的，因此增加更多约束后仍可复用同一位置名称。
<!--ja-->
`i0` から `i4` までの名前は、現在の添字、その後者、一回の漸化段階で導入される近くの値など、軌跡論理式の浅い部分を扱う。長さについて多相的なので、さらに束縛子を加えた後も同じ位置名を再利用できる。
<!--/-->

```agda
    i2 : ∀ {k} → Fin (suc (suc (suc k)))
    i2 = suc i1
    i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
    i3 = suc i2
    i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
```

<!--en-->
The next positions reach the trace environment and the original free variables after several existential witnesses have been introduced. In particular, the same formula can still refer simultaneously to the old trace value, the new trace value, and the sequence entry that relates them.
<!--zh-->
接下来的位置在引入若干存在见证后，仍能指向轨迹环境与原有自由变元。因此同一公式可以同时指称旧轨迹值、新轨迹值，以及把二者联系起来的序列条目。
<!--ja-->
次の位置は、いくつかの存在証人を導入した後にも、軌跡の環境ともとの自由変数へ届く。そのため同じ論理式の中で、古い軌跡値、新しい軌跡値、両者を結ぶ列の項を同時に指せる。
<!--/-->

```agda
    i4 = suc i3
    i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
    i5 = suc i4
    i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
    i6 = suc i5
```

<!--en-->
The step formula introduces five witnesses in all: the successor index `j`, the values `a,u,w`, and the pair code for `(a,u)`. Beneath all five binders, the original sequence variable has moved to position `i12`; the long index is therefore forced by the binding depth, not by an additional mathematical assumption.
<!--zh-->
步进公式总共引入五个见证：后继索引 `j`、取值 `a,u,w`，以及 `(a,u)` 的对码。在这五层约束之下，原序列变元移动到位置 `i12`；这个较深索引来自约束深度，并不表示新增数学假设。
<!--ja-->
ステップ論理式は全部で五つの証人を導入する。後者添字 `j`、値 `a,u,w`、そして `(a,u)` の対の符号である。五つの束縛子の内側では、もとの列変数は位置 `i12` まで移る。この深い添字は束縛の深さから生じるもので、新たな数学的仮定ではない。
<!--/-->

```agda
    i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
    i7 = suc i6
    i8 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))
    i8 = suc i7
    i12 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))))))
```

<!--en-->
Concretely, `i12` is four successors beyond `i8`. With the index names fixed, the next definitions can be read by following the mathematical roles of the variables rather than recounting nested successor constructors.
<!--zh-->
具体而言，`i12` 是在 `i8` 上再取四次后继。位置名称固定后，阅读下列定义时便可追踪各变元的数学角色，而无须逐层数后继构造子。
<!--ja-->
具体的に、`i12` は `i8` からさらに四回後者を取った位置である。位置名を固定したので、以下の定義では後者構成子を一段ずつ数えず、各変数の数学的役割を追える。
<!--/-->

```agda
    i12 = suc (suc (suc (suc i8)))
```

<!--en-->
The formula `stepFo` is the object-language counterpart of `StepAt`. It first chooses `j` and asserts that `j` is the successor of the current index `i`. It then chooses the sequence value `a`, the old and new trace values `u,w`, and a code for the ordered pair `(a,u)`.
<!--zh-->
公式 `stepFo` 是 `StepAt` 的对象语言版本。它先选取 `j`，并断言 `j` 是当前索引 `i` 的后继；随后选取序列取值 `a`、新旧轨迹值 `u,w`，以及有序对 `(a,u)` 的码。
<!--ja-->
論理式 `stepFo` は `StepAt` の対象言語での表現である。まず `j` を選び、それが現在の添字 `i` の後者であると述べる。次に列の値 `a`、古い軌跡値 `u`、新しい軌跡値 `w`、順序対 `(a,u)` の符号を選ぶ。
<!--/-->

```agda
  opaque
    private
      stepFo : Formula S 8
      stepFo = ∃̇ (
            sucAtL i1 i0
```

<!--en-->
The four inner existential quantifiers bind `a,u,w` and their pair code. The first three application clauses state `s(i)=a`, `C(i)=u`, and `C(j)=w`; the pair clause identifies the auxiliary code with `(a,u)`. These facts prepare the single recurrence assertion at the center of the formula.
<!--zh-->
内层四个存在量词约束 `a,u,w` 及其对码。前三个应用子句分别表示 `s(i)=a`、`C(i)=u` 与 `C(j)=w`；配对子句把辅助码认同为 `(a,u)`。这些事实共同准备公式核心处的一条递推断言。
<!--ja-->
内側の四つの存在量化子は `a,u,w` とその対の符号を束縛する。最初の三つの適用条件はそれぞれ `s(i)=a`、`C(i)=u`、`C(j)=w` を述べ、対の条件は補助符号を `(a,u)` と同一視する。これらが論理式の中心にある一つの漸化条件を準備する。
<!--/-->

```agda
         ∧̇ (∃̇ (∃̇ (∃̇ (∃̇ (
              appAt i12 i5 i3
           ∧̇ appAt i8 i5 i2
           ∧̇ appAt i8 i4 i1
           ∧̇ prAtL i0 i3 i2
```

<!--en-->
The innermost conjunct is the recurrence graph fact: applying `F` to the auxiliary input code produces the new value `w`. The preceding pair conjunct identifies that auxiliary code with the ordered pair `(a,u)`. Together the two conjuncts express the folding equation `F(a,u)=w` in the object language.
<!--zh-->
最内层合取项是递推的图事实：把 `F` 作用于辅助输入码，产出新值 `w`。前一条配对子句把该辅助码认同为有序对 `(a,u)`。两项合在一起，才在对象语言中表达折叠等式 `F(a,u)=w`。
<!--ja-->
最も内側の連言項は、漸化式を表すグラフの事実である。補助的な入力符号に `F` を適用すると、新しい値 `w` が得られると述べる。その直前の対の条件が、この補助符号を順序対 `(a,u)` と同一視する。二つの条件を合わせて、対象言語で畳み込みの等式 `F(a,u)=w` を表す。
<!--/-->

```agda
           ∧̇ appC F i0 i1 ))))))
```

<!--en-->
The final-length formula says: there exists a value in the coded environment at the numeral slot, and the coded pairing applied to the numeral and this value produces the output.
<!--zh-->
最终长度公式说：编码环境中数码槽位处存在取值，且编码配对施于数码与该取值产出输出。
<!--ja-->
最終長の論理式はこう言う。符号化された環境の数項の枠に値があり、数項とその値に符号化された対を適用すると出力になる、と。
<!--/-->

```agda
      finFo : Formula S 7
      finFo = ∃̇ (∃̇ (
            appAt i4 i6 i1
         ∧̇ prAtL i0 i6 i1
         ∧̇ appC F i0 i7 ))
```

<!--en-->
The body keeps two auxiliary parameters explicit before stating the trace conditions. It identifies `b` with the fixed alphabet `α` and `z` with the zero numeral, then asserts that `m` is the successor of the chosen length `n`. The equalities let later generic environment and application formulas be specialized to `α` and `0`.
<!--zh-->
公式体在陈述轨迹条件前先显式保留两个辅助参数。它把 `b` 认同为固定字母表 `α`，把 `z` 认同为零数码，再断言 `m` 是所选长度 `n` 的后继。这些等式使后续通用的环境与应用公式能够特化到 `α` 与 `0`。
<!--ja-->
本体は軌跡の条件を述べる前に、二つの補助パラメータを明示的に保つ。`b` を固定したアルファベット `α`、`z` を零の数項と同一視し、続いて `m` が選んだ長さ `n` の後者であると述べる。これらの等式により、後の一般的な環境と適用の論理式を `α` と `0` に特殊化できる。
<!--/-->

```agda
      body : Formula S 7
      body =
          (var i1 ≐ con α)
       ∧̇ (var i0 ≐ con (nn zero))
       ∧̇ sucAtL i4 i3
```

<!--en-->
The remaining conjuncts impose the domain condition, the environment-over condition, the zero-entry equation, every transition below `n`, and the final-length clause. For the currently named objects, they say that `C` is a finite trace connecting the initial zero to the output through the coded pairing. The outer quantifiers in `fo` will then assert that such a length and trace exist.
<!--zh-->
其余合取项依次施加定义域条件、环境覆盖条件、零条目等式、`n` 以下的全部转移，以及最终长度子句。对当前已经命名的对象而言，这些条件说明 `C` 是一条经编码配对从初始零连到输出的有限轨迹。随后 `fo` 的外层量词才断言这样的长度与轨迹存在。
<!--ja-->
残りの連言項は、定義域の条件、環境の上の条件、零の項目の等式、`n` 未満のすべての遷移、そして最終長の条件を課す。現在名前の付いている対象について、これらは `C` が符号化された対を通して初期の零から出力へ至る有限な軌跡であることを述べる。その後で `fo` の外側の量化子が、そのような長さと軌跡の存在を主張する。
<!--/-->

```agda
       ∧̇ domAt i6 i4
       ∧̇ envOverAt i2 i3 i1
       ∧̇ appAt i2 i0 i0
       ∧̇ ∀̇∈ (var i4) stepFo
       ∧̇ finFo
```

<!--en-->
The full graph formula binds the numeral by the bounded quantifier over `ωʟ` and then the four auxiliary objects by nested existentials, producing a two-place formula over the output and the sequence.
<!--zh-->
完整图公式先用 `ωʟ` 上的有界量词绑定数码，再以嵌套存在量词绑定四个辅助对象，产出关于输出与序列的二元公式。
<!--ja-->
完全なグラフの論理式は、`ωʟ` の上の有界量化子で数項を束縛し、つづいて入れ子の存在量化子で四つの補助の対象を束縛して、出力と列の上の二つの枠の論理式を作る。
<!--/-->

```agda
    fo : Formula S 2
    fo = ∃̇∈ (con ωʟ) (∃̇ (∃̇ (∃̇ (∃̇ body))))
```

<!--en-->
The environment `e7` contains the seven objects available before the quantifiers inside `stepFo` and `finFo` are opened. In de Bruijn order they are `z,b,C,m,n,y,s`, so slot zero is the auxiliary zero, while the original output and sequence occupy the two outermost slots. Later binders extend this environment at the front.
<!--zh-->
环境 `e7` 包含进入 `stepFo` 与 `finFo` 的内部量词前已有的七个对象。按 de Bruijn 次序，它们是 `z,b,C,m,n,y,s`，所以第零位是辅助零，而原输出与序列占据最外侧两位。后续约束会从环境前端继续扩张。
<!--ja-->
環境 `e7` は、`stepFo` と `finFo` の内側の量化子へ入る前に利用できる七つの対象を含む。de Bruijn 順では `z,b,C,m,n,y,s` であり、位置零は補助的な零、もとの出力と列は最も外側の二位置にある。後の束縛子はこの環境の先頭を拡張する。
<!--/-->

```agda
    private
      e7 : S → S → S → S → S → S → S → S ^ 7
      e7 y s n m C b z = z ∷ b ∷ C ∷ m ∷ n ∷ y ∷ s ∷ []
```

<!--en-->
To read `stepFo` outward, the proof eliminates its propositionally truncated witnesses into the proposition `StepAt s C i`. It obtains `j,a,u,w` and the auxiliary pair code, together with the successor, three graph-application, pair, and `F`-application clauses. The auxiliary pair code will disappear after its equality is used.
<!--zh-->
为向外读取 `stepFo`，证明把其中经过命题截断的见证消去到命题 `StepAt s C i`。由此得到 `j,a,u,w` 与辅助对码，并取得后继子句、三个图应用子句、配对子句和 `F` 应用子句。辅助对码在其等式使用后便不再保留。
<!--ja-->
`stepFo` を外向きに読むため、その命題的に切り詰められた証人を命題 `StepAt s C i` へ除去する。これにより `j,a,u,w` と補助的な対の符号、さらに後者条件、三つのグラフ適用条件、対の条件、`F` の適用条件が得られる。補助的な対の符号は、その等式を使った後には残らない。
<!--/-->

```agda
      stepOut : (y s n m C b z i : S)
              → ⟨ (i ∷ e7 y s n m C b z) ⊨ stepFo ⟩ → StepAt s C i
      stepOut y s n m C b z i = rec₁ squash₁ (λ { (j , (ej , ha)) →
        rec₁ squash₁ (λ { (a , hu) → rec₁ squash₁ (λ { (u , hw) →
        rec₁ squash₁ (λ { (w , hp) → rec₁ squash₁ (λ { (p , (h1 , (h2 , (h3 , (h4 , h5))))) →
```

<!--en-->
Each adequacy equation changes one satisfaction judgment into its intended equality or graph membership. The resulting facts identify `j` as the successor of `i`, read `a` from `s`, and read `u,w` from `C`. Together with the final graph fact for `F`, they have exactly the semantic shape required by `StepAt`.
<!--zh-->
每条充分性等式都把一项满足判断传输为其预期的等式或图隶属。所得事实把 `j` 认作 `i` 的后继，从 `s` 读出 `a`，并从 `C` 读出 `u,w`；连同关于 `F` 的最后一条图事实，它们恰好组成 `StepAt` 所需的语义形状。
<!--ja-->
各妥当性の等式は、一つの充足判断を意図された等式またはグラフ所属へ輸送する。得られた事実は `j` を `i` の後者と同一視し、`s` から `a`、`C` から `u,w` を読み取る。最後の `F` に関するグラフの事実と合わせると、ちょうど `StepAt` が要求する意味論的な形になる。
<!--/-->

```agda
          let γ = p ∷ w ∷ u ∷ a ∷ j ∷ i ∷ e7 y s n m C b z in
          ∣ j , a , u , w
          , ( subst ⟨_⟩ (sucAtL-adequate i1 i0 (j ∷ i ∷ e7 y s n m C b z)) ej
            , subst ⟨_⟩ (appAt-adequate i12 i5 i3 γ) h1
            , subst ⟨_⟩ (appAt-adequate i8 i5 i2 γ) h2
```

<!--en-->
The pair-adequacy equation identifies the auxiliary object with the ordered pair `(a,u)`. Transporting the `F`-application fact along that equality yields the recurrence membership `((a,u),w)∈F`. This completes the outward passage from the first-order step formula to one semantic transition.
<!--zh-->
配对充分性等式把辅助对象认同为有序对 `(a,u)`。沿这条等式传输 `F` 的应用事实，便得到递推所需的隶属 `((a,u),w)∈F`。至此完成从一阶步进公式到一次语义转移的向外读取。
<!--ja-->
対についての妥当性の等式は、補助対象を順序対 `(a,u)` と同一視する。その等式に沿って `F` の適用の事実を輸送すると、漸化式を表す所属 `((a,u),w)∈F` が得られる。これで一階のステップ論理式から一回の意味論的遷移への外向きの読み取りが完了する。
<!--/-->

```agda
            , subst ⟨_⟩ (appAt-adequate i8 i4 i1 γ) h3
            , subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩)
                (subst ⟨_⟩ (prAtL-adequate i0 i3 i2 γ) h4)
                (subst ⟨_⟩ (appC-adequate F i0 i1 γ) h5) ) ∣₁ }) hp }) hw }) hu }) ha })
```

<!--en-->
The outward reading of `finFo` first obtains a terminal trace value `v` and an auxiliary object `q`. Its clauses say `C(n)=v`, `q=(n,v)`, and `F(q)=y`. Because the target is propositionally truncated, both existential witnesses can be eliminated while retaining only `v` and the two graph facts needed by `Wit`.
<!--zh-->
向外读取 `finFo` 时，先取得终端轨迹值 `v` 与辅助对象 `q`。三个子句分别表示 `C(n)=v`、`q=(n,v)` 与 `F(q)=y`。由于目标经过命题截断，可以消去两个存在见证，只保留 `Wit` 所需的 `v` 及两条图事实。
<!--ja-->
`finFo` を外向きに読むと、まず軌跡の終端値 `v` と補助対象 `q` が得られる。三つの条件は `C(n)=v`、`q=(n,v)`、`F(q)=y` を述べる。目標は命題的に切り詰められているので、二つの存在証人を除去し、`Wit` に必要な `v` と二つのグラフの事実だけを残せる。
<!--/-->

```agda
      finOut : (y s n m C b z : S) → ⟨ e7 y s n m C b z ⊨ finFo ⟩
             → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                            × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
      finOut y s n m C b z = rec₁ squash₁ (λ { (v , hq) →
        rec₁ squash₁ (λ { (q , (h1 , (h2 , h3))) →
```

<!--en-->
Adequacy turns the three clauses into the memberships expressing `C(n)=v` and `F(q)=y`, together with the equality `q=(n,v)`. Transport along the last equality replaces `q` in the `F`-membership, producing exactly `F(n,v)=y` in graph form.
<!--zh-->
充分性把三个子句分别化为表示 `C(n)=v` 与 `F(q)=y` 的隶属，以及等式 `q=(n,v)`。沿最后这条等式传输 `F` 中的隶属，便以 `(n,v)` 替换 `q`，得到图形式的 `F(n,v)=y`。
<!--ja-->
妥当性により、三つの条件は `C(n)=v` と `F(q)=y` を表す所属、および等式 `q=(n,v)` へ移される。最後の等式に沿って `F` への所属を輸送し、`q` を `(n,v)` で置き換えると、グラフの形で `F(n,v)=y` が得られる。
<!--/-->

```agda
          let γ = q ∷ v ∷ e7 y s n m C b z in
          ∣ v , ( subst ⟨_⟩ (appAt-adequate i4 i6 i1 γ) h1
                , subst (λ r → ⟨ pr r (fst y) ∈ fst F ⟩)
                    (subst ⟨_⟩ (prAtL-adequate i0 i6 i1 γ) h2)
                    (subst ⟨_⟩ (appC-adequate F i0 i7 γ) h3) ) ∣₁ }) hq })
```

<!--en-->
The body has eight conjuncts. The first two identify the auxiliaries `b=α` and `z=0`; the remaining six assert `m=n+1`, the exact domain of `s`, the environment conditions on `C`, `C(0)=0`, all transitions below `n`, and the final tagged value. Together with the separately supplied fact `n∈ω`, these data form `Wit y s`.
<!--zh-->
公式体含有八个合取项。前两项认同辅助对象 `b=α` 与 `z=0`；其余六项断言 `m=n+1`、`s` 的准确规定义域、`C` 的环境条件、`C(0)=0`、`n` 以下的全部转移，以及最终带长度标签的取值。再加上另行给出的 `n∈ω`，这些数据构成 `Wit y s`。
<!--ja-->
本体には八つの連言項がある。最初の二つは補助対象を `b=α`、`z=0` と同一視し、残る六つは `m=n+1`、`s` の正確な定義域、`C` の環境条件、`C(0)=0`、`n` 未満のすべての遷移、最後の長さ付きの値を述べる。別に与えられた `n∈ω` と合わせると、これらが `Wit y s` を構成する。
<!--/-->

```agda
      bodyOut : (y s n m C b z : S) → ⟨ fst n ∈ ω ⟩
              → ⟨ e7 y s n m C b z ⊨ body ⟩ → Wit y s
      bodyOut y s n m C b z n∈ω (eb , (ez , (em , (hd , (hE , (h0 , (hS , hF))))))) =
        ∣ n , m , C
        , ( n∈ω
```

<!--en-->
The successor adequacy equation supplies `m=n+1`, while the two readings of `domAt` give both directions of exact-domain membership for `s`. The environment formula is transported from the auxiliary base `b` to the fixed `α` using `b=α`; no equality between complete traces is required.
<!--zh-->
后继公式的充分性等式给出 `m=n+1`，而 `domAt` 的两个读法给出 `s` 的准确定义域隶属的两个方向。再利用 `b=α`，把环境公式从辅助基集 `b` 传输到固定的 `α`；这里不需要证明两条完整轨迹相等。
<!--ja-->
後者論理式の妥当性の等式から `m=n+1` が得られ、`domAt` の二つの読み方から `s` の正確な定義域について両方向の所属が得られる。さらに `b=α` を用い、環境の論理式を補助的な基礎集合 `b` から固定した `α` へ輸送する。軌跡全体の等しさは必要ない。
<!--/-->

```agda
          , subst ⟨_⟩ (sucAtL-adequate i4 i3 (e7 y s n m C b z)) em
          , (λ x → domAt-in i6 i4 (e7 y s n m C b z) hd x
                 , domAt-out i6 i4 (e7 y s n m C b z) hd x)
          , envOverAt-transport (e7 y s n m C b z) (α ∷ m ∷ C ∷ [])
              i2 i3 i1 (suc (suc zero)) (suc zero) zero refl refl eb hE
```

<!--en-->
The equality `z=0` converts the body clause `C(z)=z` into the initial condition `C(0)=0`. The bounded universal clause is read pointwise by `stepOut`, and `finOut` supplies the terminal tagged value. These are the remaining components of the propositionally truncated witness.
<!--zh-->
等式 `z=0` 把公式体中的子句 `C(z)=z` 化为初始条件 `C(0)=0`。有界全称子句由 `stepOut` 逐点读取，`finOut` 则给出带标签的终端取值。这些就是命题截断见证余下的各个分量。
<!--ja-->
等式 `z=0` によって、本体の条件 `C(z)=z` は初期条件 `C(0)=0` へ移される。有界全称の条件は `stepOut` によって各点で読まれ、`finOut` がタグ付きの終端値を与える。これらが命題的に切り詰められた証人の残りの成分である。
<!--/-->

```agda
          , subst (λ w → ⟨ pr w w ∈ fst C ⟩) ez
              (subst ⟨_⟩ (appAt-adequate i2 i0 i0 (e7 y s n m C b z)) h0)
          , (λ i i∈n → stepOut y s n m C b z i (hS i i∈n))
          , finOut y s n m C b z hF ) ∣₁
```

<!--en-->
The outward reading of the full formula eliminates the five nested existentials one by one, feeding each into the body reading until the complete witness is assembled.
<!--zh-->
完整公式的向外读法逐一消去五层嵌套存在量词，每层喂给体读取，直至装配出完整见证。
<!--ja-->
完全な論理式の外向きの読み出しは、五重の入れ子の存在量化子を一つずつ消去し、それぞれを本体の読み出しに渡して、完全な証人が組み立てられるまで続ける。
<!--/-->

```agda
    fo-out : (y s : S) → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩ → Wit y s
    fo-out y s = rec₁ squash₁ (λ { (n , (n∈ω , hm)) →
      rec₁ squash₁ (λ { (m , hC) → rec₁ squash₁ (λ { (C , hb) →
      rec₁ squash₁ (λ { (b , hz) → rec₁ squash₁ (λ { (z , hbody) →
        bodyOut y s n m C b z n∈ω hbody }) hz }) hb }) hC }) hm })
```

<!--en-->
The converse direction begins with one propositionally truncated `StepAt` witness and maps it to a satisfaction of `stepFo`. For representatives `j,a,u,w`, the environment is extended by their pair code and by the four values themselves. The following clauses then rebuild the successor and graph assertions in object-language form.
<!--zh-->
反向构造从一项经过命题截断的 `StepAt` 见证出发，把它映到 `stepFo` 的满足。对代表 `j,a,u,w`，先以其对码及这四个取值扩张环境；随后的子句再以对象语言形式重建后继断言与各条图断言。
<!--ja-->
逆向きの構成は、命題的に切り詰められた一つの `StepAt` 証人を `stepFo` の充足へ写すことから始まる。代表 `j,a,u,w` に対し、その対の符号と四つの値で環境を拡張する。続く条件が、後者と各グラフに関する主張を対象言語の形で組み立て直す。
<!--/-->

```agda
    private
      stepIn : (y s n m C i : S) → StepAt s C i
             → ⟨ (i ∷ e7 y s n m C α (nn zero)) ⊨ stepFo ⟩
      stepIn y s n m C i = map₁ (λ { (j , a , u , w , (ej , ha , hu , hw , hF)) →
        let γ = prʟ a u ∷ w ∷ u ∷ a ∷ j ∷ i ∷ e7 y s n m C α (nn zero) in
```

<!--en-->
The witnesses are inserted in the same order in which `stepFo` binds them. Reversing the successor and application adequacy equations turns the semantic facts `j=i+1`, `s(i)=a`, `C(i)=u`, and `C(j)=w` into the corresponding satisfaction judgments. The nested truncations are preserved by introducing, rather than selecting, these witnesses.
<!--zh-->
各见证按 `stepFo` 约束它们的次序引入。反向使用后继与应用的充分性等式，把语义事实 `j=i+1`、`s(i)=a`、`C(i)=u` 与 `C(j)=w` 化为相应的满足判断。这里只是引入已有见证，并未从命题截断中作出选择，因此各层截断均得到保留。
<!--ja-->
各証人は `stepFo` が束縛する順序で導入される。後者と適用に関する妥当性の等式を逆向きに用い、意味論的事実 `j=i+1`、`s(i)=a`、`C(i)=u`、`C(j)=w` を対応する充足判断へ移す。既にある証人を導入するだけで、命題的切り詰めから選択するのではないため、入れ子の切り詰めは保たれる。
<!--/-->

```agda
        j , ( subst ⟨_⟩ (sym (sucAtL-adequate i1 i0 (j ∷ i ∷ e7 y s n m C α (nn zero)))) ej
            , ∣ a , ∣ u , ∣ w , ∣ prʟ a u
            , ( subst ⟨_⟩ (sym (appAt-adequate i12 i5 i3 γ)) ha
              , ( subst ⟨_⟩ (sym (appAt-adequate i8 i5 i2 γ)) hu
              , ( subst ⟨_⟩ (sym (appAt-adequate i8 i4 i1 γ)) hw
```

<!--en-->
The canonical constructible pair `prʟ a u` witnesses the auxiliary pair variable. Pair adequacy identifies its underlying set with `(a,u)`, and transport of the membership `((a,u),w)∈F` gives the required object-language application clause. This completes the inward reading of one transition.
<!--zh-->
典范可构造对 `prʟ a u` 充当辅助对变元的见证。配对充分性把其底层集合认同为 `(a,u)`，再传输隶属 `((a,u),w)∈F`，便得到所需的对象语言应用子句。一次转移的向内读取至此完成。
<!--ja-->
標準的な構成可能な対 `prʟ a u` が、補助的な対変数の証人になる。対についての妥当性がその底集合を `(a,u)` と同一視し、所属 `((a,u),w)∈F` を輸送すると、必要な対象言語の適用条件が得られる。これで一回の遷移の内向きの読み取りが完了する。
<!--/-->

```agda
              , ( subst ⟨_⟩ (sym (prAtL-adequate i0 i3 i2 γ)) (prʟ-fst a u)
                , subst ⟨_⟩ (sym (appC-adequate F i0 i1 γ))
                    (subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩) (sym (prʟ-fst a u)) hF) )))) ∣₁ ∣₁ ∣₁ ∣₁ ) })
```

<!--en-->
The inward reading of `finFo` starts from a propositionally truncated terminal value `v` with `C(n)=v` and `F(n,v)=y`. It maps this witness through the two existential quantifiers of `finFo`: one binds `v`, and the other binds an explicit code for the ordered pair `(n,v)`.
<!--zh-->
向内读取 `finFo` 时，从经过命题截断的终端取值 `v` 出发，其中 `C(n)=v` 且 `F(n,v)=y`。构造把这项见证映过 `finFo` 的两个存在量词：一个约束 `v`，另一个约束有序对 `(n,v)` 的显式码。
<!--ja-->
`finFo` の内向きの読み取りは、`C(n)=v` かつ `F(n,v)=y` を満たす、命題的に切り詰められた終端値 `v` から始まる。この証人を `finFo` の二つの存在量化子へ写す。一つは `v`、もう一つは順序対 `(n,v)` の明示的な符号を束縛する。
<!--/-->

```agda
      finIn : (y s n m C : S)
            → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                           × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
            → ⟨ e7 y s n m C α (nn zero) ⊨ finFo ⟩
      finIn y s n m C = map₁ (λ { (v , (hv , hy)) →
```

<!--en-->
Extend the environment by `v` and the canonical pair `prʟ n v`. Reversing application adequacy expresses `C(n)=v`; reversing pair adequacy identifies the pair witness; and reversing the adequacy of application to the constant graph `F` expresses `F(n,v)=y`.
<!--zh-->
以 `v` 与典范对 `prʟ n v` 扩张环境。反向使用应用充分性可表达 `C(n)=v`，反向使用配对充分性可认同对见证，再反向使用常元图 `F` 的应用充分性即可表达 `F(n,v)=y`。
<!--ja-->
環境を `v` と標準的な対 `prʟ n v` で拡張する。適用の妥当性を逆向きに用いて `C(n)=v` を表し、対の妥当性を逆向きに用いて対の証人を同一視し、定数グラフ `F` への適用の妥当性を逆向きに用いて `F(n,v)=y` を表す。
<!--/-->

```agda
        let γ = prʟ n v ∷ v ∷ e7 y s n m C α (nn zero) in
        v , ∣ prʟ n v
            , ( subst ⟨_⟩ (sym (appAt-adequate i4 i6 i1 γ)) hv
              , ( subst ⟨_⟩ (sym (prAtL-adequate i0 i6 i1 γ)) (prʟ-fst n v)
                , subst ⟨_⟩ (sym (appC-adequate F i0 i7 γ))
```

<!--en-->
The final transport changes the graph membership whose input is the ambient pair `(n,v)` into satisfaction using the constructible representative `prʟ n v`. The terminal clause is therefore rebuilt without choosing anything beyond the witness already carried by the propositional truncation.
<!--zh-->
最后一次传输把以外围有序对 `(n,v)` 为输入的图隶属，化为使用可构造代表 `prʟ n v` 的满足。因此，终端子句得以重建，而没有在命题截断已携带的见证之外再作选择。
<!--ja-->
最後の輸送は、周囲の順序対 `(n,v)` を入力とするグラフ所属を、構成可能な代表 `prʟ n v` を用いた充足へ移す。したがって、命題的切り詰めが既に保持する証人以外を選ぶことなく、終端条件が再構成される。
<!--/-->

```agda
                    (subst (λ q → ⟨ pr q (fst y) ∈ fst F ⟩) (sym (prʟ-fst n v)) hy) )) ∣₁ })
```

<!--en-->
To rebuild the body, assume the six substantive trace conditions: `m=n+1`, the exact domain of `s`, the environment conditions for `C`, the initial value, all bounded transitions, and the terminal tagged value. The two remaining body conjuncts are the fixed identifications `b=α` and `z=0`, which need no additional hypotheses.
<!--zh-->
为重建公式体，假设六项实质性的轨迹条件：`m=n+1`、`s` 的准确规定义域、`C` 的环境条件、初始值、全部有界转移，以及带标签的终端取值。公式体余下两个合取项是固定的认同 `b=α` 与 `z=0`，无需额外假设。
<!--ja-->
本体を再構成するため、六つの実質的な軌跡条件を仮定する。すなわち `m=n+1`、`s` の正確な定義域、`C` の環境条件、初期値、すべての有界な遷移、タグ付きの終端値である。本体に残る二つの連言項は固定された同一視 `b=α` と `z=0` であり、追加の仮定を必要としない。
<!--/-->

```agda
      bodyIn : (y s n m C : S) → fst m ≡ sucV (fst n) → DomIs s n → EnvC m C
             → ⟨ pr (# zero) (# zero) ∈ fst C ⟩
             → ((i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C i)
             → ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C ⟩
                            × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁
```

<!--en-->
In the chosen seven-object environment, the auxiliary entries are literally `α` and `0`. Consequently the first two conjuncts of the body are witnessed by reflexivity. The rest of the proof converts the six supplied semantic conditions into the remaining six object-language conjuncts.
<!--zh-->
在所选的七对象环境中，两个辅助条目按定义就是 `α` 与 `0`，所以公式体前两个合取项均由自反性证明。余下证明把已给的六项语义条件化为其余六个对象语言合取项。
<!--ja-->
選んだ七対象の環境では、二つの補助項目は定義上そのまま `α` と `0` である。したがって本体の最初の二つの連言項は反射律で証明される。残りの証明は、与えられた六つの意味論的条件を残る六つの対象言語の連言項へ移す。
<!--/-->

```agda
             → ⟨ e7 y s n m C α (nn zero) ⊨ body ⟩
      bodyIn y s n m C em hd hE h0 hS hF =
        let γ = e7 y s n m C α (nn zero) in
          refl
        , ( refl
```

<!--en-->
Reversing successor adequacy supplies the conjunct for `m=n+1`. The introduction reading of `domAt` combines the two directions in `DomIs`: one direction uses propositional elimination because the existence of a graph value is truncated, and the other is already a direct implication. The environment condition is then transported into the selected variable positions.
<!--zh-->
反向使用后继充分性，便得到表示 `m=n+1` 的合取项。`domAt` 的引入读法组合 `DomIs` 的两个方向：由于图取值的存在经过命题截断，其中一个方向使用命题消去，另一方向本来就是直接蕴含。随后把环境条件传输到所选变元位置。
<!--ja-->
後者についての妥当性を逆向きに用いると、`m=n+1` を表す連言項が得られる。`domAt` の導入方向は `DomIs` の二方向を組み合わせる。グラフ値の存在が命題的に切り詰められているため一方では命題への除去を用い、他方はもともと直接の含意である。続いて環境条件を選ばれた変数位置へ輸送する。
<!--/-->

```agda
        , ( subst ⟨_⟩ (sym (sucAtL-adequate i4 i3 γ)) em
        , ( domAt-intro i6 i4 γ (λ x →
              rec₁ (snd (fst x ∈ fst n)) (λ { (yy , p) → hd x .snd yy p })
            , hd x .fst)
        , ( envOverAt-transport (α ∷ m ∷ C ∷ []) γ
```

<!--en-->
The initial membership `C(0)=0` gives the sixth conjunct through application adequacy. Each transition below `n` is sent inward by `stepIn`, and `finIn` rebuilds the final tagged-value clause. Along with the preceding five facts, these complete all eight conjuncts of the finite-trace body.
<!--zh-->
初始隶属 `C(0)=0` 经应用充分性给出第六个合取项。`n` 以下的每次转移由 `stepIn` 向内送入，`finIn` 则重建最终带标签的取值子句。连同此前五项事实，这些内容补全有限轨迹公式体的全部八个合取项。
<!--ja-->
初期の所属 `C(0)=0` は、適用の妥当性を通して第六の連言項を与える。`n` 未満の各遷移は `stepIn` によって内向きに送られ、`finIn` が最後のタグ付きの値の条件を再構成する。先の五つの事実と合わせて、有限軌跡の本体にある八つの連言項がすべて完成する。
<!--/-->

```agda
              (suc (suc zero)) (suc zero) zero i2 i3 i1 refl refl refl hE
        , ( subst ⟨_⟩ (sym (appAt-adequate i2 i0 i0 γ)) h0
        , ( (λ i i∈n → stepIn y s n m C i (hS i i∈n))
        , finIn y s n m C hF ))))))
```

<!--en-->
The inward reading of the full formula eliminates the truncated witness and injects the five objects through the five nested existentials, assembling the object-language satisfaction of the graph formula.
<!--zh-->
完整公式的向内读法消去截断见证，并把五个对象沿五层嵌套存在量词注入，装配图公式的对象语言满足。
<!--ja-->
完全な論理式の内向きの読み出しは、切り詰められた証人を消去し、五つの対象を五重の入れ子の存在量化子を通して注入して、グラフの論理式の対象言語の充足を組み立てる。
<!--/-->

```agda
    fo-in : (y s : S) → Wit y s → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩
    fo-in y s = rec₁ (snd ((y ∷ s ∷ []) ⊨ fo))
      (λ { (n , m , C , (n∈ω , em , hd , hE , h0 , hS , hF)) →
        ∣ n , ( n∈ω
              , ∣ m , ∣ C , ∣ α , ∣ nn zero
```

<!--en-->
The five witnesses are `n,m,C,α,0`: the first is introduced through the bounded existential over `ω`, and the remaining four through ordinary existentials. The fixed choices `α` and `0` make the first two body equalities reflexive, while `bodyIn` supplies the successor, domain, environment, initial, transition, and terminal clauses. Thus `fo-in` reconstructs the complete satisfaction without selecting a representative from the truncated witness globally.
<!--zh-->
五个见证是 `n,m,C,α,0`：第一个通过 `ω` 上的有界存在量词引入，其余四个通过普通存在量词引入。固定选择 `α` 与 `0` 使公式体前两条等式由自反性成立，而 `bodyIn` 则提供后继、定义域、环境、初始、转移与终端子句。因此 `fo-in` 重建完整满足，而没有从命题截断见证中作出全局代表选择。
<!--ja-->
五つの証人は `n,m,C,α,0` である。最初のものは `ω` 上の有界存在量化子、残る四つは通常の存在量化子を通して導入される。固定した `α` と `0` によって本体の最初の二等式は反射律で成り立ち、`bodyIn` が後者、定義域、環境、初期値、遷移、終端の条件を与える。したがって `fo-in` は、切り詰められた証人から大域的に代表を選ぶことなく、完全な充足を再構成する。
<!--/-->

```agda
              , bodyIn y s n m C em hd hE h0 hS hF ∣₁ ∣₁ ∣₁ ∣₁ ) ∣₁ })
```

<!--en-->
It remains to test the semantic formula on a genuine finite sequence. Fix a length `N`, an assignment `g : Fin N → α`, a constructible set `s`, and an equality identifying the underlying set of `s` with the environment graph `envS α g`. The following construction proves existence and uniqueness of the formula's output for this represented sequence.
<!--zh-->
接下来要在一条真正的有限序列上检验该语义公式。固定长度 `N`、赋值 `g : Fin N → α`、可构造集合 `s`，以及一条把 `s` 的底层集合认同为环境图 `envS α g` 的等式。下列构造将证明这条已表示序列的公式输出存在且唯一。
<!--ja-->
次に、この意味論的論理式を実際の有限列に適用する。長さ `N`、割り当て `g : Fin N → α`、構成可能集合 `s`、そして `s` の底集合を環境グラフ `envS α g` と同一視する等式を固定する。以下では、この表現された列について論理式の出力が存在し一意であることを示す。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module AtSeq (N : ℕ) (g : Fin N → ⟪ fst α ⟫) (s : S) (e : fst s ≡ fst (envS α g)) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
For the standard environment graph, three objects suffice to invoke the generic environment formulas: the base set `α`, the length numeral `N`, and `envS α g`. Their de Bruijn order in `δ` places the graph at slot two, the numeral at slot one, and the base at slot zero.
<!--zh-->
对标准环境图，调用通用环境公式只需三个对象：基集 `α`、长度数码 `N` 与 `envS α g`。它们在 `δ` 中的 de Bruijn 次序使环境图位于第二位，数码位于第一位，基集位于第零位。
<!--ja-->
標準的な環境グラフについて一般的な環境論理式を使うには、基礎集合 `α`、長さの数項 `N`、`envS α g` の三対象で十分である。`δ` における de Bruijn 順では、グラフが位置二、数項が位置一、基礎集合が位置零に置かれる。
<!--/-->

```agda
    private
      δ : S ^ 3
      δ = α ∷ nn N ∷ envS α g ∷ []
```

<!--en-->
The standard graph `envS α g` is already known to be an environment over `α` with domain `N`. Projecting the domain clause from this environment fact proves that its exact domain is the numeral `#N`. This fact will later force every competing witness for the same sequence to use that same finite length.
<!--zh-->
标准图 `envS α g` 已知是取值于 `α`、定义域为 `N` 的环境。从这项环境事实中投影定义域子句，便证明其准确定义域是数码 `#N`。稍后，这项事实将迫使同一序列的任何其他见证使用相同的有限长度。
<!--ja-->
標準グラフ `envS α g` は、`α` に値を取り、`N` を定義域とする環境であることが既に分かっている。この環境の事実から定義域の条件を取り出すと、その正確な定義域が数項 `#N` であることが示される。後でこの事実により、同じ列に対するどの別の証人も同じ有限長を使うことが強制される。
<!--/-->

```agda
      dom0 : ⟨ δ ⊨ domAt (suc (suc zero)) (suc zero) ⟩
      dom0 = envOver-dom (suc (suc zero)) (suc zero) zero δ (envOver α g)
```

<!--en-->
To use the environment lookup theorem, the assignment must first be viewed as a family of sets in `V`. The map `gV` sends each finite index to the underlying set named by the corresponding presentation element `g i`; because `g i` presents a member of `α`, this is exactly the value recorded at that index.
<!--zh-->
为使用环境的查表定理，先要把赋值看成 `V` 中的一族集合。映射 `gV` 把每个有穷索引送到呈现元素 `g i` 所指名的底层集合；由于 `g i` 呈现 `α` 的一个成员，这正是该索引处记录的取值。
<!--ja-->
環境の参照定理を使うには、まず割り当てを `V` の集合族として見る。写像 `gV` は各有限添字を、表示要素 `g i` が名指す底集合へ送る。`g i` は `α` の要素を表示しているので、これはその添字に記録される値そのものである。
<!--/-->

```agda
      gV : Fin N → V ℓ
      gV i = ⟪ fst α ⟫↪ (g i)
```

<!--en-->
If `k < N`, then the canonical environment contains the pair whose first coordinate is the numeral `# k` and whose second coordinate is the `k`-th sequence entry. The proof converts `k` to an element of `Fin N`, applies the lookup specification there, and transports the resulting membership back to the natural-number index.
<!--zh-->
若 `k < N`，则典范环境包含一个有序对，其第一坐标是数码 `# k`，第二坐标是序列的第 `k` 项。证明先把 `k` 转为 `Fin N` 的元素，在该处应用查表规格，再把所得隶属证明运输回自然数索引。
<!--ja-->
`k < N` なら、正準な環境は、第一成分が数項 `# k`、第二成分が列の第 `k` 項である順序対を含む。証明では `k` を `Fin N` の要素に直し、そこで参照の仕様を適用して、得られた所属を自然数の添字へ戻す。
<!--/-->

```agda
      extMem : (k : ℕ) (p : k < N)
             → ⟨ pr (# k) (fst (fst (ext N g k))) ∈ fst (envS α g) ⟩
      extMem k p = subst (λ k → ⟨ pr (# k) (fst (fst (ext N g k))) ∈ fst (envS α g) ⟩)
        (toFromId' N k p)
        (subst ⟨_⟩ (sym (lookup-spec gV i (fst (fst (ext N g (toℕ i))))))
```

<!--en-->
The comparison `ext-at` identifies the totalized lookup `ext N g (toℕ i)` with the genuine entry `g i`. The identities for conversion between bounded natural numbers and `Fin N` then return both the index and the displayed value to the original `k`.
<!--zh-->
等式 `ext-at` 把全域化查找 `ext N g (toℕ i)` 与真正的条目 `g i` 等同。随后，有界自然数与 `Fin N` 之间的往返恒等式把索引及所展示的取值都还原到原来的 `k`。
<!--ja-->
等式 `ext-at` は、全域化された参照 `ext N g (toℕ i)` を本来の項 `g i` と同一視する。続いて、有界な自然数と `Fin N` の間の往復等式により、添字と表示された値の両方が元の `k` に戻る。
<!--/-->

```agda
          (cong (λ z → fst (fst z)) (ext-at N g i)))
        where
        i : Fin N
        i = fromℕ' N k p
```

<!--en-->
The converse lookup statement expresses single-valuedness at every valid index. If the environment contains `(# k,a)` with `k < N`, then the underlying set of `a` must be the underlying set of the actual `k`-th entry; no second value can be recorded at that index.
<!--zh-->
反向查表陈述表达每个合法索引处的单值性。若环境在 `k < N` 时包含 `(# k,a)`，则 `a` 的底层集合必等于真正第 `k` 项的底层集合；该索引处不能记录第二个不同的取值。
<!--ja-->
逆向きの参照は、各有効添字での単値性を表す。`k < N` のとき環境が `(# k,a)` を含むなら、`a` の底集合は実際の第 `k` 項の底集合に等しく、その添字に別の値を記録することはできない。
<!--/-->

```agda
      s-uniq : (k : ℕ) (p : k < N) (a : S)
             → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩
             → fst a ≡ fst (fst (ext N g k))
      s-uniq k p a ha =
          subst ⟨_⟩ (lookup-spec gV i (fst a))
```

<!--en-->
This identification is made at the corresponding `Fin N` index. The lookup equation first determines `a`, `ext-at` replaces the totalized entry by the original assignment entry, and the conversion identity transports the result back to `k`.
<!--zh-->
这一等同先在相应的 `Fin N` 索引处建立。查表等式首先确定 `a`，`ext-at` 再把全域化条目换回原赋值条目，最后由转换恒等式把结论运输回 `k`。
<!--ja-->
この同一視は、対応する `Fin N` の添字で行う。参照等式がまず `a` を決定し、`ext-at` が全域化された項を元の割り当ての項に戻し、変換の恒等式が結論を `k` へ運ぶ。
<!--/-->

```agda
            (subst (λ k → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩) (sym (toFromId' N k p)) ha)
        ∙ sym (cong (λ z → fst (fst z)) (ext-at N g i))
        ∙ cong (λ k → fst (fst (ext N g k))) (toFromId' N k p)
        where
        i : Fin N
```

<!--en-->
Here `i = fromℕ' N k p` is the finite index justified by the bound `p : k < N`. Keeping the bound explicit is essential: the total function `ext` has no sequence meaning outside this range.
<!--zh-->
这里 `i = fromℕ' N k p` 是由界 `p : k < N` 保证存在的有穷索引。显式保留这个界十分关键，因为全域函数 `ext` 在该范围之外没有序列意义。
<!--ja-->
ここで `i = fromℕ' N k p` は、境界 `p : k < N` によって正当化される有限添字である。この境界を明示することが大切である。全域関数 `ext` は、この範囲の外では列としての意味をもたない。
<!--/-->

```agda
        i = fromℕ' N k p
```

<!--en-->
The fold has `N + 1` states, from the initial value through the state after all `N` entries have been processed. Each state already comes with a proof that it belongs to `α`; `fiber` turns that membership into a presentation element, producing an assignment `h` indexed by `Fin (suc N)`.
<!--zh-->
折叠共有 `N + 1` 个状态，从初值一直到处理完全部 `N` 个条目后的状态。每个状态已经带有属于 `α` 的证明；`fiber` 把这份隶属证明转成呈现元素，从而得到由 `Fin (suc N)` 索引的赋值 `h`。
<!--ja-->
畳み込みには、初期値から `N` 個すべての項を処理した後の状態まで、`N + 1` 個の状態がある。各状態にはすでに `α` への所属証明があり、`fiber` はその所属を表示要素へ変えて、`Fin (suc N)` で添字づけられた割り当て `h` を作る。
<!--/-->

```agda
      h : Fin (suc N) → ⟪ fst α ⟫
      h i = fiber (fst α) (snd (chain N g (toℕ i))) .fst
```

<!--en-->
The family `hV` forgets the presentation indices and returns to their underlying `V`-sets. The fiber equation used below shows that these sets are precisely the fold states from which `h` was obtained.
<!--zh-->
族 `hV` 忘去呈现索引，回到它们所指名的 `V` 中底层集合。下文使用的纤维等式说明，这些集合恰是构造 `h` 时所取的折叠状态。
<!--ja-->
族 `hV` は表示添字を忘れて、それらが名指す `V` の底集合へ戻る。後で使うファイバー等式により、これらが `h` のもとになった畳み込み状態そのものであることが分かる。
<!--/-->

```agda
      hV : Fin (suc N) → V ℓ
      hV i = ⟪ fst α ⟫↪ (h i)
```

<!--en-->
Let `C` be the environment graph of this state assignment. Its domain has length `N + 1`, and its entry at `k` records the fold state after the first `k` sequence entries, including the initial state at `k = 0` and the final state at `k = N`.
<!--zh-->
令 `C` 为这族状态的环境图。它的定义域长度为 `N + 1`，在 `k` 处记录处理完前 `k` 个序列条目后的折叠状态，其中包括 `k = 0` 处的初值与 `k = N` 处的终值。
<!--ja-->
この状態割り当ての環境グラフを `C` とする。その定義域の長さは `N + 1` で、`k` 番目には列の最初の `k` 項を処理した後の畳み込み状態が記録される。`k = 0` の初期状態と `k = N` の最終状態も含まれる。
<!--/-->

```agda
      C : S
      C = envS α h
```

<!--en-->
For every `k < N + 1`, `chainMem` exhibits the expected graph entry `(# k, chain N g k)` in `C`. As for the original sequence, the proof passes through the corresponding element of `Fin (suc N)` and invokes the environment lookup specification.
<!--zh-->
对每个 `k < N + 1`，`chainMem` 给出预期图条目 `(# k, chain N g k)` 属于 `C` 的证明。与原序列相同，证明先转到 `Fin (suc N)` 中对应的元素，再调用环境的查表规格。
<!--ja-->
各 `k < N + 1` に対し、`chainMem` は期待されるグラフ項 `(# k, chain N g k)` が `C` に属することを示す。元の列の場合と同様に、対応する `Fin (suc N)` の要素へ移り、環境の参照仕様を使う。
<!--/-->

```agda
      chainMem : (k : ℕ) (p : k < suc N)
               → ⟨ pr (# k) (fst (fst (chain N g k))) ∈ fst C ⟩
      chainMem k p = subst (λ k → ⟨ pr (# k) (fst (fst (chain N g k))) ∈ fst C ⟩)
        (toFromId' (suc N) k p)
        (subst ⟨_⟩ (sym (lookup-spec hV i (fst (fst (chain N g (toℕ i))))))
```

<!--en-->
The fiber equation identifies the value named by `h i` with the actual fold state, while `toFromId'` restores the original natural-number index. These two identifications complete the graph-membership proof without asserting anything about indices outside `N + 1`.
<!--zh-->
纤维等式把 `h i` 所指名的取值与实际折叠状态等同，而 `toFromId'` 还原原来的自然数索引。这两项等同完成图隶属证明，并未对 `N + 1` 之外的索引作任何断言。
<!--ja-->
ファイバー等式は `h i` が名指す値を実際の畳み込み状態と同一視し、`toFromId'` は元の自然数添字を復元する。この二つの同一視によってグラフへの所属が証明され、`N + 1` の外の添字については何も主張しない。
<!--/-->

```agda
          (sym (fiber (fst α) (snd (chain N g (toℕ i))) .snd)))
        where
        i : Fin (suc N)
        i = fromℕ' (suc N) k p
```

<!--en-->
The fixed equation `e : fst s ≡ fst (envS α g)` lets us use the canonical environment facts for the represented sequence `s`. The map `inS` transports a canonical graph entry from `envS α g` into `s`.
<!--zh-->
固定等式 `e : fst s ≡ fst (envS α g)` 使我们能够把典范环境的事实用于被表示的序列 `s`。映射 `inS` 把 `envS α g` 中的典范图条目运输到 `s` 中。
<!--ja-->
固定した等式 `e : fst s ≡ fst (envS α g)` により、正準な環境についての事実を、表示される列 `s` に使える。`inS` は `envS α g` の正準なグラフ項を `s` へ運ぶ。
<!--/-->

```agda
      inS : (k : ℕ) (a : S) → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩ → ⟨ pr (# k) (fst a) ∈ fst s ⟩
      inS k a = subst (λ w → ⟨ pr (# k) (fst a) ∈ w ⟩) (sym e)
```

<!--en-->
The reverse transport `outS` moves any graph entry of `s` back to `envS α g`. This direction will be used in the uniqueness argument, where an entry supplied by an arbitrary witness chain must be compared with the actual assignment entry.
<!--zh-->
反向运输 `outS` 把 `s` 的任意图条目移回 `envS α g`。唯一性论证将使用这一方向，把任意见证链给出的条目与实际赋值条目比较。
<!--ja-->
逆向きの輸送 `outS` は、`s` の任意のグラフ項を `envS α g` へ戻す。一意性の議論では、任意の証人となる連鎖が与える項を実際の割り当ての項と比較するために、この向きを使う。
<!--/-->

```agda
      outS : (k : ℕ) (a : S) → ⟨ pr (# k) (fst a) ∈ fst s ⟩ → ⟨ pr (# k) (fst a) ∈ fst (envS α g) ⟩
      outS k a = subst (λ w → ⟨ pr (# k) (fst a) ∈ w ⟩) e
```

<!--en-->
We now verify that the canonical code satisfies the graph formula. The witnesses choose the finite length numeral `# N`, its successor `#(N+1)`, and the state environment `C`; the remaining fields establish the domain of `s`, the `α`-valued state chain, its zero initial state, every transition, and the final application of the pairing graph.
<!--zh-->
现在验证典范码满足图公式。见证取有限长度数码 `# N`、它的后继 `#(N+1)` 以及状态环境 `C`；其余各项依次证明 `s` 的定义域、取值于 `α` 的状态链、零初值、每一步转移与最后一次配对图应用。
<!--ja-->
ここで正準な符号がグラフ論理式を満たすことを確かめる。証人には有限長の数項 `# N`、その後続 `#(N+1)`、状態環境 `C` を選ぶ。残りの成分は、`s` の定義域、`α` に値をとる状態列、零の初期状態、各遷移、最後の対グラフの適用を証明する。
<!--/-->

```agda
    wit : Wit (fst (code N g)) s
    wit = ∣ nn N , nn (suc N) , C
          , ( #∈ω N
            , refl
            , domIs
```

<!--en-->
The last existential clause is witnessed by the state `chain N g N`. It occurs in `C` at index `N`, and applying `F` to the pair consisting of the length numeral and that state gives `code N g`; the whole existence statement remains propositionally truncated.
<!--zh-->
最后的存在子句由状态 `chain N g N` 见证。它在 `C` 的索引 `N` 处出现，而把配对图 `F` 应用于长度数码与该状态组成的有序对，所得正是 `code N g`；整个存在陈述仍经过命题截断。
<!--ja-->
最後の存在節は、状態 `chain N g N` によって証される。この状態は `C` の添字 `N` に現れ、長さの数項とこの状態の対に `F` を適用すると `code N g` が得られる。存在の主張全体は命題的に切り詰められたままである。
<!--/-->

```agda
            , envOver α h
            , chainMem zero (suc-≤-suc zero-≤)
            , step
            , ∣ fst (chain N g N)
              , ( chainMem N ≤-refl , app-graph (num N) (chain N g N) ) ∣₁ ) ∣₁
```

<!--en-->
To prove that `s` has domain `# N`, start with an index in `# N`. The canonical environment supplies a merely existing value at that index, and transport along `e` turns its graph membership into membership in `s`.
<!--zh-->
为证明 `s` 的定义域是 `# N`，先取 `# N` 中的一个索引。典范环境在该索引处给出一个仅保持存在性的取值，再沿 `e` 运输其图隶属，便得到该有序对属于 `s`。
<!--ja-->
`s` の定義域が `# N` であることを示すため、まず `# N` の添字を取る。正準な環境はその添字で単に存在する値を与え、`e` に沿ってグラフへの所属を運ぶと、その順序対が `s` に属することが得られる。
<!--/-->

```agda
      where
      domIs : DomIs s (nn N)
      domIs x =
          (λ m → map₁ (λ { (yy , p) → yy , subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) (sym e) p })
                   (domAt-in (suc (suc zero)) (suc zero) δ dom0 x m))
```

<!--en-->
Conversely, if `s` contains a pair with first coordinate `x`, transport sends it back to the canonical environment. The known domain of that environment then implies `x ∈ # N`, completing the two directions of the domain characterization.
<!--zh-->
反过来，若 `s` 包含第一坐标为 `x` 的有序对，运输会把它送回典范环境。该环境的已知定义域于是推出 `x ∈ # N`，从而完成定义域刻画的两个方向。
<!--ja-->
逆に、`s` が第一成分 `x` の順序対を含むなら、それを正準な環境へ戻す。その環境の既知の定義域から `x ∈ # N` が従い、定義域の特徴づけの両方向がそろう。
<!--/-->

```agda
        , (λ yy p → domAt-out (suc (suc zero)) (suc zero) δ dom0 x yy
                      (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) e p))
```

<!--en-->
For a set-theoretic index `i ∈ # N`, numeral elimination supplies a natural number `k < N` whose numeral is `i`. The transition witness then chooses the successor numeral, the actual `k`-th sequence entry, and the fold states at `k` and `k+1`.
<!--zh-->
对集合论索引 `i ∈ # N`，数码消去给出一个自然数 `k < N`，其数码与 `i` 相等。转移见证随后选取后继数码、序列真正的第 `k` 项以及折叠在 `k` 与 `k+1` 处的状态。
<!--ja-->
集合論的な添字 `i ∈ # N` に数項の除去を使うと、その数項が `i` に等しい自然数 `k < N` が得られる。遷移の証人には、後続の数項、列の実際の第 `k` 項、`k` と `k+1` における畳み込み状態を選ぶ。
<!--/-->

```agda
      step : (i : S) → ⟨ fst i ∈ # N ⟩ → StepAt s C i
      step i i∈N = rec₁ squash₁ (λ { (k , p , ei) →
        ∣ nn (suc k) , fst (ext N g k) , fst (chain N g k) , fst (chain N g (suc k))
        , ( cong sucV (sym ei)
          , subst (λ w → ⟨ pr w (fst (fst (ext N g k))) ∈ fst s ⟩) (sym ei)
```

<!--en-->
The required transition facts now follow from the two canonical environments and the defining equation of the fold. The sequence entry lies in `s`, both adjacent states lie in `C`, and `app-graph` records that `F` sends the pair of the entry and the old state to the new state; transports only replace `# k` by the originally given index `i`.
<!--zh-->
所需的转移事实现由两个典范环境与折叠的定义等式给出。序列条目属于 `s`，相邻的两个状态都属于 `C`，而 `app-graph` 记录 `F` 把该条目与旧状态组成的有序对送到新状态；各次运输只负责把 `# k` 换回原先给定的索引 `i`。
<!--ja-->
必要な遷移の事実は、二つの正準な環境と畳み込みの定義式から得られる。列の項は `s` に属し、隣り合う二状態はともに `C` に属し、`app-graph` は項と旧状態の対を `F` が新状態へ送ることを記録する。輸送は `# k` を最初に与えられた添字 `i` へ戻すためだけに使われる。
<!--/-->

```agda
              (inS k (fst (ext N g k)) (extMem k p))
          , subst (λ w → ⟨ pr w (fst (fst (chain N g k))) ∈ fst C ⟩) (sym ei)
              (chainMem k (≤-suc p))
          , chainMem (suc k) (suc-≤-suc p)
          , app-graph (ext N g k) (chain N g k) ) ∣₁ }) (∈#-elim N (fst i) i∈N)
```

<!--en-->
Existence alone does not yet make `fo` a function graph. The theorem `only` proves that every output `y` admitted by a `Wit y s` has the same underlying set as the canonical code. Since this equality is a proposition, the propositionally truncated witness may be eliminated before the uniqueness argument begins.
<!--zh-->
仅有存在性还不足以使 `fo` 成为函数图。定理 `only` 证明：凡由 `Wit y s` 接受的输出 `y`，其底层集合都等于典范码。由于该等式是命题，可以先消去经过命题截断的见证，再开始唯一性论证。
<!--ja-->
存在だけでは、まだ `fo` は関数グラフにならない。定理 `only` は、`Wit y s` が認めるどの出力 `y` も、正準な符号と同じ底集合をもつことを示す。この等式は命題なので、命題的に切り詰められた証人を除去してから一意性の議論を進められる。
<!--/-->

```agda
    only : (y : S) → Wit y s → fst y ≡ fst (fst (code N g))
    only y = rec₁ (setIsSet (fst y) (fst (fst (code N g))))
      (λ { (n , m , C' , (n∈ω , em , hd , hE , h0 , hS , hF)) →
        Only.final n m C' n∈ω em hd hE h0 hS hF })
      where
```

<!--en-->
Fix an arbitrary witness with length object `n`, successor `m`, and state environment `C'`. Its hypotheses say that `s` has domain `n`, that `C'` is an `α`-valued environment of length `m`, that its initial entry is zero, that it obeys every fold step below `n`, and that its terminal state is paired with `n` to produce `y`.
<!--zh-->
固定一个任意见证，其中长度对象为 `n`，其后继为 `m`，状态环境为 `C'`。各项假设说明：`s` 的定义域是 `n`，`C'` 是长度为 `m` 且取值于 `α` 的环境，其初始条目为零，它在 `n` 以下遵守每一步折叠规则，并且终止状态与 `n` 配对后产生 `y`。
<!--ja-->
長さの対象を `n`、その後続を `m`、状態環境を `C'` とする任意の証人を固定する。仮定は、`s` の定義域が `n` であること、`C'` が長さ `m` で `α` に値をとる環境であること、初期項が零であること、`n` より下の各畳み込み段階に従うこと、終状態を `n` と対にすると `y` が得られることを述べる。
<!--/-->

```agda
      module Only (n m C' : S) (n∈ω : ⟨ fst n ∈ ω ⟩) (em : fst m ≡ sucV (fst n))
                  (hd : DomIs s n) (hE : EnvC m C')
                  (h0 : ⟨ pr (# zero) (# zero) ∈ fst C' ⟩)
                  (hS : (i : S) → ⟨ fst i ∈ fst n ⟩ → StepAt s C' i)
                  (hF : ∥ Σ[ v ∈ S ] ( ⟨ pr (fst n) (fst v) ∈ fst C' ⟩
```

<!--en-->
The terminal clause `hF` merely asserts the existence of a state `v` recorded by `C'` at index `n` and mapped by `F` together with `n` to `y`. It does not choose a terminal state globally; later it is eliminated only into the set equality that states uniqueness of the output.
<!--zh-->
终止子句 `hF` 只断言存在一个状态 `v`：它由 `C'` 记录在索引 `n` 处，并与 `n` 一同经 `F` 映到 `y`。它并未全局选取终止状态；下文只把它消去到表达输出唯一性的集合等式中。
<!--ja-->
終端節 `hF` は、状態 `v` が単に存在し、それが `C'` の添字 `n` に記録され、`n` とともに `F` で `y` へ写されることを述べる。終状態を大域的に選ぶものではなく、後では出力の一意性を述べる集合の等式へだけ除去する。
<!--/-->

```agda
                                     × ⟨ pr (pr (fst n) (fst v)) (fst y) ∈ fst F ⟩ ) ∥₁)
                  where
```

<!--en-->
The witness length `n` must equal the canonical numeral `# N` as a set. Both describe the domain of the same sequence `s`: `hd` gives the description through the arbitrary witness, while `dom0` gives it through the chosen representation `s = envS α g`. Extensionality reduces the equality to the two membership implications.
<!--zh-->
见证中的长度 `n` 作为集合必等于典范数码 `# N`。二者都描述同一序列 `s` 的定义域：`hd` 给出任意见证中的描述，`dom0` 则经所选表示 `s = envS α g` 给出描述。外延性把该等式化为两个隶属蕴涵。
<!--ja-->
証人の長さ `n` は、集合として正準な数項 `# N` に等しくなければならない。どちらも同じ列 `s` の定義域を表し、`hd` は任意の証人から、`dom0` は選んだ表示 `s = envS α g` からその記述を与える。外延性により、この等式は所属の二つの含意へ帰着する。
<!--/-->

```agda
        n≡ : fst n ≡ # N
        n≡ = cong fst (extensionalL {a = n} {b = nn N} (λ x → ⇔toPath (fwd x) (bwd x)))
          where
          fwd : (x : S) → ⟨ fst x ∈ fst n ⟩ → ⟨ fst x ∈ # N ⟩
          fwd x x∈n = rec₁ (snd (fst x ∈ # N))
```

<!--en-->
For the forward implication, an element `x ∈ n` yields, by `hd`, a merely existing pair in `s` with first coordinate `x`. Transporting that pair to the canonical environment and reading its known domain proves `x ∈ # N`.
<!--zh-->
对向前蕴涵，由 `x ∈ n` 与 `hd` 可得 `s` 中仅保持存在性的一个有序对，其第一坐标为 `x`。把该有序对运输到典范环境，再读取其已知定义域，便得 `x ∈ # N`。
<!--ja-->
順方向では、`x ∈ n` と `hd` から、第一成分が `x` である順序対が `s` に単に存在することが得られる。その対を正準な環境へ運び、既知の定義域を読むと `x ∈ # N` が従う。
<!--/-->

```agda
            (λ { (yy , p) → domAt-out (suc (suc zero)) (suc zero) δ dom0 x yy
                              (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) e p) })
            (hd x .fst x∈n)
          bwd : (x : S) → ⟨ fst x ∈ # N ⟩ → ⟨ fst x ∈ fst n ⟩
          bwd x x∈N = rec₁ (snd (fst x ∈ fst n))
```

<!--en-->
For the reverse implication, `x ∈ # N` gives an entry of the canonical environment. After transport to `s`, the converse half of `hd` shows `x ∈ n`. Thus the length is recovered from the sequence domain, without selecting a representation for every sequence.
<!--zh-->
对反向蕴涵，`x ∈ # N` 给出典范环境中的一个条目。把它运输到 `s` 后，`hd` 的反向部分推出 `x ∈ n`。因此，长度由序列的定义域恢复，而无须为每个序列选定一种表示。
<!--ja-->
逆方向では、`x ∈ # N` から正準な環境の項が得られる。それを `s` へ運ぶと、`hd` の逆向きの部分から `x ∈ n` が従う。したがって、各列の表示を選ぶことなく、その定義域から長さを復元できる。
<!--/-->

```agda
            (λ { (yy , p) → hd x .snd yy (subst (λ w → ⟨ pr (fst x) (fst yy) ∈ w ⟩) (sym e) p) })
            (domAt-in (suc (suc zero)) (suc zero) δ dom0 x x∈N)
```

<!--en-->
Because `C'` satisfies the environment condition, it is single-valued. Hence two pairs in `C'` with the same first coordinate must have equal second coordinates as underlying sets. This fact will compare the arbitrary state recorded by `C'` with the state forced by the fold equations.
<!--zh-->
由于 `C'` 满足环境条件，它是单值的。因此，`C'` 中第一坐标相同的两个有序对，其第二坐标的底层集合必相等。这个事实将用于比较 `C'` 记录的任意状态与折叠等式所强制的状态。
<!--ja-->
`C'` は環境条件を満たすので単値である。したがって、`C'` に属する二つの順序対の第一成分が同じなら、第二成分の底集合は等しくなる。この事実を用いて、`C'` が記録する任意の状態を、畳み込み方程式が定める状態と比較する。
<!--/-->

```agda
        svC : (x v v' : S) → ⟨ pr (fst x) (fst v) ∈ fst C' ⟩ → ⟨ pr (fst x) (fst v') ∈ fst C' ⟩
            → fst v ≡ fst v'
        svC = svAt-out (suc (suc zero)) (α ∷ m ∷ C' ∷ [])
                (envOver-sv (suc (suc zero)) (suc zero) zero (α ∷ m ∷ C' ∷ []) hE)
```

<!--en-->
The central induction states that every value recorded by `C'` at an index `k < N + 1` equals the canonical fold state `chain N g k`. At `k = 0`, both values are forced to be zero by the initial clause and single-valuedness of `C'`.
<!--zh-->
核心归纳断言：对每个 `k < N + 1`，`C'` 在索引 `k` 处记录的任何取值都等于典范折叠状态 `chain N g k`。在 `k = 0` 时，初始子句与 `C'` 的单值性强制两者都等于零。
<!--ja-->
中心となる帰納命題は、各 `k < N + 1` について、`C'` が添字 `k` に記録するどの値も正準な畳み込み状態 `chain N g k` に等しいというものである。`k = 0` では、初期節と `C'` の単値性により、両方の値が零に定まる。
<!--/-->

```agda
        entry : (k : ℕ) → k < suc N → (v : S)
              → ⟨ pr (# k) (fst v) ∈ fst C' ⟩ → fst v ≡ fst (fst (chain N g k))
        entry zero    p v hv = svC (nn zero) v (nn zero) hv h0
        entry (suc k) p v hv = rec₁ (setIsSet (fst v) (fst (fst (chain N g (suc k)))))
          (λ { (j , a , u , w , (ej , ha , hu , hw , hFw)) →
```

<!--en-->
In the successor case, a transition witness supplies an entry `a` of the sequence, an old state `u`, and a new state `w`. The canonical sequence lookup identifies `a` with the `k`-th input, the induction hypothesis identifies `u` with the canonical old state, and functionality of `F` then identifies `w` with the canonical new state.
<!--zh-->
在后继情形，转移见证给出序列条目 `a`、旧状态 `u` 与新状态 `w`。典范序列的查表性质把 `a` 等同于第 `k` 个输入，归纳假设把 `u` 等同于典范旧状态，而 `F` 的功能性随后把 `w` 等同于典范新状态。
<!--ja-->
後続の場合、遷移の証人は列の項 `a`、旧状態 `u`、新状態 `w` を与える。正準な列の参照によって `a` は第 `k` 入力に等しく、帰納法の仮定によって `u` は正準な旧状態に等しくなる。すると `F` の機能性から、`w` は正準な新状態に等しいと分かる。
<!--/-->

```agda
            let ea : fst a ≡ fst (fst (ext N g k))
                ea = s-uniq k p' a (outS k a ha)
                eu : fst u ≡ fst (fst (chain N g k))
                eu = entry k (≤-suc p') u hu
                ew : fst w ≡ fst (fst (chain N g (suc k)))
```

<!--en-->
The step clause is available because `k < N`, obtained from the successor bound. It places `w` in `C'` at the successor index; single-valuedness first equates the originally given value `v` with `w`, and the preceding application argument then equates `w` with `chain N g (suc k)`.
<!--zh-->
由后继索引的界可得 `k < N`，因而可以调用步进子句。该子句把 `w` 放在 `C'` 的后继索引处；单值性先把原先给定的取值 `v` 与 `w` 等同，前述应用论证再把 `w` 与 `chain N g (suc k)` 等同。
<!--ja-->
後続添字の境界から `k < N` が得られるので、段階の節を使える。この節は `w` を `C'` の後続添字に置く。単値性がまず最初に与えられた値 `v` を `w` と同一視し、先の適用についての議論が `w` を `chain N g (suc k)` と同一視する。
<!--/-->

```agda
                ew = app-uniq (ext N g k) (chain N g k) w
                       (subst (λ q → ⟨ pr q (fst w) ∈ fst F ⟩) (cong₂ pr ea eu) hFw)
            in svC (nn (suc k)) v w hv
                 (subst (λ z → ⟨ pr z (fst w) ∈ fst C' ⟩) ej hw) ∙ ew })
          (hS (nn k) (subst (λ z → ⟨ # k ∈ z ⟩) (sym n≡) (#mono k N p')))
```

<!--en-->
The predecessor bound is the small arithmetic fact needed by the induction: from `suc k < suc N` one obtains `k < N`. It ensures that the `k`-th input entry is genuine and that the fold step at `k` lies within the sequence.
<!--zh-->
前驱界是归纳所需的小型算术事实：由 `suc k < suc N` 得到 `k < N`。它保证第 `k` 个输入条目确实存在，并且 `k` 处的折叠步骤位于序列范围内。
<!--ja-->
前者の境界は帰納法に必要な小さな算術事実である。`suc k < suc N` から `k < N` を得る。これにより、第 `k` 入力が実際の項であり、`k` での畳み込み段階が列の範囲内にあることが保証される。
<!--/-->

```agda
          where
          p' : k < N
          p' = pred-≤-pred p
```

<!--en-->
It remains to determine the candidate output `y`. Eliminating the propositionally truncated terminal witness gives a state `v` recorded at the witness length `n`; the underlying-set equality `n≡ : fst n ≡ # N` transports this membership to index `N`, where the induction identifies `v` with the canonical final fold state.
<!--zh-->
最后还需确定所给输出 `y`。消去经过命题截断的终止见证后，得到见证长度 `n` 处记录的状态 `v`；底层集合等式 `n≡ : fst n ≡ # N` 把该隶属运输到索引 `N`，归纳结论便把 `v` 与典范折叠的最终状态等同。
<!--ja-->
残るのは、与えられた出力 `y` を決定することである。命題的に切り詰められた終端の証人を除去すると、証人の長さ `n` に記録された状態 `v` が得られる。底集合の等式 `n≡ : fst n ≡ # N` でこの所属を添字 `N` へ運ぶと、帰納法の結論が `v` を正準な最終畳み込み状態と同一視する。
<!--/-->

```agda
        final : fst y ≡ fst (fst (code N g))
        final = rec₁ (setIsSet (fst y) (fst (fst (code N g))))
          (λ { (v , (hv , hy)) →
            let hv' : ⟨ pr (# N) (fst v) ∈ fst C' ⟩
                hv' = subst (λ z → ⟨ pr z (fst v) ∈ fst C' ⟩) n≡ hv
```

<!--en-->
The terminal clause also says that `F` maps the pair formed from `fst n` and `fst v` to the underlying set of `y`. After replacing these inputs by `# N` and the canonical final state, functionality of `F` gives `fst y ≡ fst (fst (code N g))`. This proves uniqueness only for outputs satisfying the graph formula; it does not define a decoder on arbitrary elements of `α`.
<!--zh-->
终止子句还说明，`F` 把由 `fst n` 与 `fst v` 组成的有序对映到底层集合 `fst y`。把这两个输入换成 `# N` 与典范终态后，`F` 的功能性给出 `fst y ≡ fst (fst (code N g))`。这只证明满足图公式的输出具有唯一性，并未在 `α` 的任意元素上定义解码函数。
<!--ja-->
終端節はさらに、`F` が `fst n` と `fst v` からなる対を `y` の底集合 `fst y` へ写すことを述べる。これらの入力を `# N` と正準な最終状態に置き換えると、`F` の機能性から `fst y ≡ fst (fst (code N g))` が得られる。これはグラフ論理式を満たす出力の一意性だけを示し、`α` の任意の要素に対する復号関数を定義するものではない。
<!--/-->

```agda
                ev : fst v ≡ fst (fst (chain N g N))
                ev = entry N ≤-refl v hv'
            in app-uniq (num N) (chain N g N) y
                 (subst (λ q → ⟨ pr q (fst y) ∈ fst F ⟩) (cong₂ pr n≡ ev) hy) })
          hF
```
</div>
</details>

<!--en-->
The predicate `Mem s` is simply membership of `s` in `seqL α`. Thus every later construction is restricted to sets that are finite `α`-valued environment graphs, rather than arbitrary elements of the ambient universe.
<!--zh-->
谓词 `Mem s` 就是 `s` 属于 `seqL α`。因此，后续构造只作用于取值于 `α` 的有穷环境图，而不是外围宇宙中的任意元素。
<!--ja-->
述語 `Mem s` は、`s` が `seqL α` に属するという意味である。したがって、以後の構成の対象は有限な `α` 値環境グラフに限られ、周囲の宇宙の任意の要素ではない。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem s = ⟨ fst s ∈ˢ fst (seqL α) ⟩
```

<!--en-->
A representation of `s` consists merely of a natural length `n`, an assignment `g : Ix α n`, and equality of `s` with the environment graph of `g`. The propositional truncation deliberately forgets which representation supplied these data; no global choice of lengths or assignments is made.
<!--zh-->
`s` 的一种表示只保留如下存在性：某个自然数长度 `n`、某个赋值 `g : Ix α n`，以及 `s` 与 `g` 的环境图相等。命题截断刻意忘去究竟是哪一种表示提供这些数据；这里没有全局选取长度或赋值。
<!--ja-->
`s` の表示とは、自然数の長さ `n`、割り当て `g : Ix α n`、`s` が `g` の環境グラフに等しいことが、単に存在するという内容である。命題的切り詰めによって、どの表示がデータを与えたかは意図的に忘れられ、長さや割り当てを大域的に選ぶことはない。
<!--/-->

```agda
  Rep : S → Type (ℓ-suc ℓ)
  Rep s = ∥ Σ[ n ∈ ℕ ] Σ[ g ∈ Ix α n ] (fst s ≡ fst (envS α g)) ∥₁
```

<!--en-->
Membership in `seqL α` first yields, through `seqL-out`, a merely existing finite length at which `s` belongs to an environment set. The converse description of that environment set then supplies a merely existing assignment and the required graph equality, establishing `Rep s`.
<!--zh-->
由 `s ∈ seqL α`，`seqL-out` 首先给出仅保持存在性的某个有限长度，使 `s` 属于相应环境集。再读取该环境集的反向刻画，便得到仅保持存在性的赋值及所需图等式，从而建立 `Rep s`。
<!--ja-->
`s ∈ seqL α` から、`seqL-out` はまず、`s` が対応する環境集合に属するような有限長が単に存在することを与える。その環境集合の逆向きの特徴づけから、割り当てと必要なグラフ等式が単に存在することが得られ、`Rep s` が成立する。
<!--/-->

```agda
  rep : (s : S) → Mem s → Rep s
  rep s m = rec₁ squash₁
    (λ { (n , hn) → map₁ (λ { (g , e) → n , g , e }) (envSet-out α n s hn) })
    (seqL-out α s m)
```

<!--en-->
The graph formula can now be turned into a function on `seqL α`. Each concrete representation `(n,g,e)` yields the candidate `fst (code n g)` together with a proof that it uniquely fills the graph fiber over `s`. Mapping the truncated representation into this propositionally truncated unique-existence statement makes it a valid input to `mereFunct`, which converts it into the required contractibility without selecting a preferred representation.
<!--zh-->
现在可以把图公式化为 `seqL α` 上的函数。每个具体表示 `(n,g,e)` 都给出候选值 `fst (code n g)`，并证明它唯一地占据 `s` 上的图纤维。把经过命题截断的表示映到这条同样经过命题截断的唯一存在陈述后，便可将其交给 `mereFunct`；后者把它转成所需的可缩性，而不选取首选表示。
<!--ja-->
これでグラフ論理式から `seqL α` 上の関数を得られる。具体的な各表示 `(n,g,e)` から、候補 `fst (code n g)` と、それが `s` 上のグラフのファイバーを一意に占めることの証明が得られる。切り詰められた表示を、この命題的に切り詰められた一意存在の主張へ写せば、`mereFunct` への入力になる。`mereFunct` は優先する表示を選ぶことなく、それを必要な可縮性へ変換する。
<!--/-->

```agda
  R : Recursion
  R = record
    { dom   = seqL α
    ; graph = fo
    ; funct = λ s m → mereFunct fo s (map₁ (λ { (n , g , e) →
```

<!--en-->
For each representation, `fo-in` proves that the canonical code lies in the graph fiber. If another `y'` lies in that fiber, `fo-out` turns its satisfaction proof into a witness and `AtSeq.only` identifies it with the canonical code. Since constructibility proofs are propositional, equality of the underlying sets gives equality of the packaged elements.
<!--zh-->
对每一种表示，`fo-in` 证明典范码属于相应图纤维。若另一个 `y'` 也属于该纤维，`fo-out` 把其满足性证明转成见证，`AtSeq.only` 再把它与典范码等同。由于可构造性证明是命题，底层集合的相等即可给出带证明元素的相等。
<!--ja-->
各表示について、`fo-in` は正準な符号がグラフのファイバーに属することを示す。別の `y'` も同じファイバーに属するなら、`fo-out` がその充足証明を証人へ変え、`AtSeq.only` が正準な符号と同一視する。構成可能性の証明は命題なので、底集合の等式から証明つき要素の等式が得られる。
<!--/-->

```agda
        fst (code n g)
        , ( fo-in (fst (code n g)) s (AtSeq.wit n g s e)
          , λ y' h → Σ≡Prop (λ v → snd (isL v)) (AtSeq.only n g s e y' (fo-out y' s h)) ) })
        (rep s m)) }
```

<!--en-->
The general theorem for a functional definable relation now supplies its unique value operation. We retain the function value and the principle that any output satisfying `fo` is equal to that value; these are the two facts needed to construct the internal injection.
<!--zh-->
关于可定义函数关系的一般定理现在给出其唯一取值运算。这里保留函数值，以及任何满足 `fo` 的输出都等于该值的原理；构造内部单射只需要这两项事实。
<!--ja-->
定義可能な関数的関係についての一般定理から、一意な値を与える演算が得られる。ここでは関数値と、`fo` を満たすどの出力もその値に等しいという原理を取り出す。内部単射の構成に必要なのはこの二つである。
<!--/-->

```agda
  module T = Of R using ( funct; val; val-uniq )
```

<!--en-->
Define `fn s m` to be this unique value for the sequence member `s`. Although the notation includes the membership proof `m`, membership is proposition-valued, so the mathematical value does not depend on a choice among distinct proofs.
<!--zh-->
把 `fn s m` 定义为序列成员 `s` 的这个唯一取值。虽然记号中包含隶属证明 `m`，但隶属关系取值于命题，因此数学上的取值不依赖于在不同证明之间作选择。
<!--ja-->
列の要素 `s` に対するこの一意な値を `fn s m` と定める。記法には所属証明 `m` が含まれるが、所属は命題値なので、数学的な値は異なる証明の選び方に依存しない。
<!--/-->

```agda
  fn : (s : S) → Mem s → S
  fn = T.val
```

<!--en-->
Whenever `s` is represented by an assignment `g` of length `n`, the underlying `S`-value `fst (code n g)` satisfies `fo`; uniqueness of the graph value therefore gives `fn s m ≡ fst (code n g)`. This comparison holds for every supplied representation and so does not require choosing a preferred one.
<!--zh-->
只要 `s` 由长度为 `n` 的赋值 `g` 表示，作为 `S` 元素的编码值 `fst (code n g)` 就满足 `fo`；图取值的唯一性因而给出 `fn s m ≡ fst (code n g)`。这个比较对每个给定表示都成立，所以无须选取首选表示。
<!--ja-->
`s` が長さ `n` の割り当て `g` で表示されるなら、`S` の要素としての符号値 `fst (code n g)` は `fo` を満たす。したがってグラフ値の一意性から `fn s m ≡ fst (code n g)` が得られる。この比較は与えられたどの表示についても成り立つので、優先する表示を選ぶ必要はない。
<!--/-->

```agda
  fn-code : (s : S) (m : Mem s) (n : ℕ) (g : Ix α n) → fst s ≡ fst (envS α g)
          → fn s m ≡ fst (code n g)
  fn-code s m n g e = T.val-uniq s m (fst (code n g)) (fo-in (fst (code n g)) s (AtSeq.wit n g s e))
```

<!--en-->
The value of `fn` remains inside `α`. A truncated representation may be eliminated into this membership proposition; for each representative `(n,g)`, the second component of `code n g` proves membership in `α`, and `fn-code` transports that fact to `fn s m`.
<!--zh-->
`fn` 的取值仍位于 `α` 中。由于目标隶属陈述是命题，可以消去经过命题截断的表示；对每个代表 `(n,g)`，`code n g` 的第二分量证明它属于 `α`，再由 `fn-code` 把该事实运输到 `fn s m`。
<!--ja-->
`fn` の値は `α` の内部にとどまる。目標となる所属は命題なので、命題的に切り詰められた表示を除去できる。各代表 `(n,g)` については、`code n g` の第二成分が `α` への所属を証し、`fn-code` がその事実を `fn s m` へ運ぶ。
<!--/-->

```agda
  into : (s : S) (m : Mem s) → ⟨ fst (fn s m) ∈ˢ fst α ⟩
  into s m = rec₁ (snd (fst (fn s m) ∈ˢ fst α))
    (λ { (n , g , e) → subst (λ w → ⟨ fst w ∈ˢ fst α ⟩) (sym (fn-code s m n g e)) (snd (code n g)) })
    (rep s m)
```

<!--en-->
These facts form a `DefinableMap` from `seqL α` to `α`. The record stores the host-level function and the proof that its values lie in the codomain together with the first-order formula `fo`: `defines` proves that the selected value satisfies the formula, while `only` proves that every satisfying output is that selected value. After injectivity is established, the following `Inj` construction uses this definability data to build the actual graph set in `L`.
<!--zh-->
这些事实组成一个从 `seqL α` 到 `α` 的 `DefinableMap`。该记录把宿主层函数、函数值落在陪域中的证明与一阶公式 `fo` 一同保存：`defines` 证明所取之值满足该公式，`only` 则证明每个满足公式的输出都是这个值。下文证明单射性后，`Inj` 构造再用这些可定义性数据在 `L` 中构造实际的函数图集合。
<!--ja-->
これらの事実から、`seqL α` から `α` への `DefinableMap` が得られる。このレコードは、ホスト側の関数と、その値が終域に属することの証明を一階論理式 `fo` とともに保持する。`defines` は選ばれた値が論理式を満たすことを示し、`only` は論理式を満たすどの出力もその値であることを示す。続いて単射性を証明すると、`Inj` の構成がこの定義可能性のデータを用いて、`L` の中に実際の関数グラフを作る。
<!--/-->

```agda
  D : DefinableMap
  D = record
    { dom = seqL α ; cod = α ; fn = fn ; into = into ; graph = fo
    ; defines = λ s m → T.funct s m .fst .snd
    ; only    = λ s m y h → sym (T.val-uniq s m y h) }
```

<!--en-->
To prove injectivity, suppose two sequence members have equal `fn` values. Their representations are propositionally truncated, but the desired equality of underlying sets is itself a proposition, so both truncations may be eliminated to compare arbitrary representatives `(n,g)` and `(n',g')`.
<!--zh-->
为证明单射性，设两个序列成员的 `fn` 取值相等。它们的表示都经过命题截断，但所求的底层集合等式本身是命题，因此可以同时消去两份截断，比较任意代表 `(n,g)` 与 `(n',g')`。
<!--ja-->
単射性を示すため、二つの列の要素が同じ `fn` の値をもつと仮定する。それぞれの表示は命題的に切り詰められているが、求める底集合の等式も命題なので、両方の切り詰めを除去して任意の代表 `(n,g)` と `(n',g')` を比較できる。
<!--/-->

```agda
  inj : (s : S) (m : Mem s) (s' : S) (m' : Mem s')
      → fst (fn s m) ≡ fst (fn s' m') → fst s ≡ fst s'
  inj s m s' m' e = rec2 (setIsSet (fst s) (fst s'))
    (λ { (n , g , es) (n' , g' , es') →
        es
```

<!--en-->
The equations `fn-code` turn equality of the two `fn` values into equality of the two canonical codes. The previously proved `code-inj` then gives equality of their environment graphs; composing with the two representation equations yields `fst s ≡ fst s'`. This is a proof by comparison of valid codes, not a total decoding operation on `α`.
<!--zh-->
等式 `fn-code` 把两个 `fn` 取值的相等转为两个典范码的相等。先前证明的 `code-inj` 随即给出相应环境图相等；再与两条表示等式复合，便得 `fst s ≡ fst s'`。这是对合法码进行比较的证明，而不是定义在 `α` 全域上的解码运算。
<!--ja-->
等式 `fn-code` により、二つの `fn` の値の等しさは二つの正準な符号の等しさへ変わる。先に示した `code-inj` から対応する環境グラフの等しさが得られ、二つの表示等式と合成すると `fst s ≡ fst s'` となる。これは正しい符号どうしを比較する証明であり、`α` 全体で定義された復号演算ではない。
<!--/-->

```agda
      ∙ code-inj n g n' g'
          (sym (cong fst (fn-code s m n g es)) ∙ e ∙ cong fst (fn-code s' m' n' g' es'))
      ∙ sym es' })
    (rep s m) (rep s' m')
```

<!--en-->
The definable map and the preceding injectivity proof determine an internal injection from `seqL α` into `α`. The conclusion `InjL` is propositionally truncated existence of a suitable graph in `L`; it asserts neither that the map is surjective nor that arbitrary elements of `α` can be decoded as finite sequences.
<!--zh-->
该可定义映射与前述单射性证明共同给出从 `seqL α` 到 `α` 的内部单射。结论 `InjL` 是 `L` 中存在合适函数图的命题截断；它既不声称该映射满射，也不声称 `α` 的任意元素都能解码为有穷序列。
<!--ja-->
定義可能な写像と先の単射性証明から、`seqL α` から `α` への内部単射が得られる。結論 `InjL` は、適切なグラフが `L` に存在するという命題的に切り詰められた主張である。この写像の全射性も、`α` の任意の要素を有限列として復号できることも主張しない。
<!--/-->

```agda
  injL : InjL (seqL α) α
  injL = Inj.injL D inj
```
</div>
</details>

<!--en-->
## Finite sequences inject into an infinite ordinal
<!--zh-->
## 有限序列单射到无穷序数
<!--ja-->
## 有限列を無限順序数へ単射する
<!--/-->

<!--en-->
The final theorem removes the temporary assumption that a pairing injection on `α` has already been supplied. Once an internal injection `prodL α ↪ α` is constructed, its truncated graph witness provides the single-valuedness, exact domain, injectivity, and range facts required by the fold construction, yielding `seqL α ↪ α` inside `L`.
<!--zh-->
最终定理去掉先前临时采用的假设，即已经给定 `α` 上的配对单射。构造出内部单射 `prodL α ↪ α` 后，其经过命题截断的图见证提供折叠构造所需的单值性、准确的定义域、单射性与值域事实，从而在 `L` 内得到 `seqL α ↪ α`。
<!--ja-->
最後の定理では、`α` 上の対の単射があらかじめ与えられているという一時的な仮定を取り除く。内部単射 `prodL α ↪ α` を構成すると、その命題的に切り詰められたグラフの証人から、畳み込みに必要な単値性、正確な定義域、単射性、値域の事実が得られ、`L` の内部で `seqL α ↪ α` が従う。
<!--/-->

```agda
seq-count :
    (α : SL.S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → ⊥₀)
  → InjL (seqL α) α
seq-count α oα α∉ω = rec₁ squash₁
  (λ { (F , sv , dm , ij , ran) → Code.injL α oα α∉ω F sv dm ij ran }) pairing
```

<!--en-->
To build the pairing injection, choose only locally a cardinal representative `μ` supplied by `cardOf α oα`. This representative is available under propositional truncation, but the target `InjL (prodL α) α` is also a proposition, so the construction may be carried out for an arbitrary representative without making a global choice.
<!--zh-->
为构造配对单射，只在局部取 `cardOf α oα` 给出的基数代表 `μ`。这个代表经过命题截断才可得，但目标 `InjL (prodL α) α` 本身也是命题，所以可以对任意代表完成构造，而不作全局选择。
<!--ja-->
対の単射を作るため、`cardOf α oα` が与える基数代表 `μ` を局所的にだけ取る。この代表は命題的切り詰めのもとで得られるが、目標 `InjL (prodL α) α` も命題なので、大域的な選択をせず任意の代表について構成できる。
<!--/-->

```agda
  where
  pairing : InjL (prodL α) α
  pairing = rec₁ squash₁ build (cardOf α oα)
    where
    build : Σ[ μ ∈ S ]
```

<!--en-->
The representative `μ` is an ordinal and an internal cardinal, with internal injections in both directions between `α` and `μ`; `cardOf` also supplies an inclusion `μ ⊆ α`, although this construction does not use it. The two injections compare cardinality in both directions without identifying `μ` and `α` definitionally.
<!--zh-->
代表 `μ` 是序数也是内部基数，并且 `α` 与 `μ` 之间各有一条内部单射；`cardOf` 还给出包含 `μ ⊆ α`，不过本构造没有使用它。两条单射从两个方向比较基数大小，但并不把 `μ` 与 `α` 定义性地等同。
<!--ja-->
代表 `μ` は順序数であり内部の基数でもあり、`α` と `μ` の間には両方向の内部単射がある。`cardOf` は包含 `μ ⊆ α` も与えるが、この構成では使わない。二つの単射は濃度を両方向から比較するが、`μ` と `α` を定義的に同一視するものではない。
<!--/-->

```agda
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩)
              × InjL α μ × InjL μ α )
          → InjL (prodL α) α
    build (μ , oμ , cardμ , _ , α↪μ , μ↪α) =
```

<!--en-->
The desired pairing is the composite `α² ↪ μ² ↪ μ ↪ α`. The first arrow applies `α ↪ μ` to both coordinates, the middle arrow is the square law for the infinite internal cardinal `μ`, and the last arrow returns to `α`. The square law is therefore used at the cardinal representative, not directly at an arbitrary infinite ordinal.
<!--zh-->
所需配对单射是复合 `α² ↪ μ² ↪ μ ↪ α`。第一条箭头把 `α ↪ μ` 逐坐标应用，居中的箭头是无穷内部基数 `μ` 的平方律，最后一条箭头回到 `α`。因此，平方律施用于基数代表，而不是直接施用于任意无穷序数。
<!--ja-->
必要な対の単射は、合成 `α² ↪ μ² ↪ μ ↪ α` である。最初の矢印は `α ↪ μ` を両座標に適用し、中央の矢印は無限な内部基数 `μ` に対する平方律で、最後の矢印が `α` へ戻す。したがって平方律は、任意の無限順序数に直接ではなく、基数代表に適用される。
<!--/-->

```agda
      injl-trans (prodL α) (prodL μ) α (prod-inj α μ α↪μ)
        (injl-trans (prodL μ) μ α
          (WF.WFI.induction regularityV {P = Goal} Step.result (fst μ) (snd μ) oμ cardμ μ∉ω)
          μ↪α)
      where
```

<!--en-->
It remains to show that `μ` is infinite in the sense required by the square law. If `μ ∈ ω`, then `μ` would be a finite ordinal, while the supplied internal injection `α ↪ μ` would inject the infinite ordinal `α` into it; `no-fin` rules this out using the ordinality and infinitude hypotheses on `α` and `μ`.
<!--zh-->
最后还要证明 `μ` 具有平方律所需的无穷性。若 `μ ∈ ω`，则 `μ` 是有穷序数，而已有的内部单射 `α ↪ μ` 会把无穷序数 `α` 单射到其中；`no-fin` 利用 `α`、`μ` 的序数性与 `α` 的无穷性排除这种情形。
<!--ja-->
最後に、平方律が必要とする意味で `μ` が無限であることを示す。もし `μ ∈ ω` なら `μ` は有限順序数であるが、与えられた内部単射 `α ↪ μ` は無限順序数 `α` をそこへ単射することになる。`no-fin` は、`α` と `μ` の順序数性および `α` の無限性を用いてこれを排除する。
<!--/-->

```agda
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → ⊥₀
      μ∉ω h = no-fin α μ oα α∉ω oμ h α↪μ
```
