```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Adequate stages for the GCH argument
<!--zh-->
# GCH 论证所需的充分层
<!--ja-->
# GCH の議論に必要な十分な段階
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and excluded middle for propositions at level `ℓ-suc ℓ`. The adequate indices and their corresponding stages constructed below depend on this single classical hypothesis.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上命题的排中律。下文构造的充分指标及其对应的层都依赖这一个经典假设。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` の命題に対する排中律を固定する。以下で構成する十分な添字と、それらに対応する段階は、この一つの古典的仮定に依存する。
<!--/-->

```agda
module L.GCH.AdequateStages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( union-family-in; union-family-out )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; isL; IsOrd; isPropIsOrd; Lset; Lset-mono; Lset→isL; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( boundingOrd; bound2; setUnion-ord; mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.EnvironmentTower {ℓ} lem using ( module Tower )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
```

<!--en-->

The internal descriptions used by condensation require four witness sets to be present together. This chapter defines when an ordinal index is adequate, constructs such an index `γ` above any given ordinal, and then constructs an index `λ` whose members are locally covered by smaller adequate indices. The corresponding constructible stages are `Lset γ` and `Lset λ`. Here adequate is a term of this book for a four-part closure condition tailored to the GCH argument, not the classical notion of an admissible ordinal.
<!--zh-->

凝聚所用的内部描述要求四个见证集合同时出现。本章定义序数指标何时充分，在任意给定序数之上构造这样的指标 `γ`，再构造指标 `λ`，使它的每个成员都在某个更小的充分指标中得到局部覆盖。相应的可构造层分别是 `Lset γ` 与 `Lset λ`。充分层是本书为 GCH 论证所需四项闭合条件所定的术语，并非通常所谓容许序数。
<!--ja-->

凝縮で用いる内部記述には、四つの証人集合が同時に存在する必要がある。この章では、順序数添字が十分であるための条件を定め、任意の順序数より上にその条件を満たす添字 `γ` を構成する。さらに、各要素がより小さい十分な添字によって局所的に覆われる添字 `λ` を構成する。対応する構成可能段階は `Lset γ` と `Lset λ` である。十分な段階は、GCH の議論に合わせた四項目の閉包条件を表す本書固有の用語であり、通常の admissible 順序数ではない。
<!--/-->

<!--en-->
All constructions in this chapter are relative to one explicit instance of excluded middle. It enters through the construction of birth stages and of the coded witnesses; it does not supply a choice function. In particular, the existence obtained later from membership in a union remains propositionally truncated.
<!--zh-->
本章的全部构造都相对于一个显式的排中律实例。它通过诞生层和编码见证的构造进入论证，却不提供选择函数。特别地，后文从属于并集所得的存在性仍带有命题截断。
<!--ja-->
この章のすべての構成は、一つの明示的な排中律の実例に相対している。この仮定は誕生段階と符号化された証人の構成を通して議論に入るが、選択関数を与えるものではない。とくに、後で合併への所属から得る存在は、命題的切り詰めの中にとどまる。
<!--/-->



<!--en-->
The construction takes place in the ambient cumulative hierarchy `V ℓ`. Its objects `c`, `γ`, and later `λ` are ordinal indices, whereas `Lset c`, `Lset γ`, and `Lset λ` are the constructible stages indexed by them. Unions are formed among the ordinal indices in the ambient hierarchy; the truth formula will be used only at the end to show that a whole constructible stage is an element of its successor stage.
<!--zh-->
这一构造在外围累积层级 `V ℓ` 中进行。其中的对象 `c`、`γ` 以及后文的 `λ` 是序数指标，而 `Lset c`、`Lset γ` 与 `Lset λ` 才是由它们索引的可构造层。并集是在外围层级的序数指标之间形成的；恒真公式只在最后用于证明整个可构造层属于其后继层。
<!--ja-->
この構成は周囲の累積階層 `V ℓ` の中で行われる。ここで `c`、`γ`、そして後の `λ` は順序数の添字であり、`Lset c`、`Lset γ`、`Lset λ` がそれぞれにより添字づけられた構成可能段階である。合併は周囲の階層にある順序数添字の間で作られる。恒真論理式を使うのは最後だけで、構成可能段階全体がその後続段階の要素になることを示す。
<!--/-->

<!--en-->
To place a constructible witness in a later stage, first take its birth-stage index, then bound that ordinal index, and finally use monotonicity of `Lset`. Separate ordinal facts ensure that members of an ordinal, their successors, and the common bounds used along the way are still ordinals. Thus the bounding argument acts on indices, while its conclusion places witness sets inside a stage.
<!--zh-->
要把一个可构造见证放入更后的层，先取它的诞生层索引，再约束这个序数指标，最后使用 `Lset` 的单调性。另一些序数事实保证序数的成员、这些成员的后继以及途中使用的公共界仍是序数。因此，取界论证作用于指标，而其结论则把见证集合放进一层之内。
<!--ja-->
構成可能な証人を後の段階に入れるには、まずその誕生段階の添字を取り、その順序数添字を上から抑え、最後に `Lset` の単調性を使う。別の順序数に関する事実により、順序数の要素、その後続、そして途中で使う共通上界も順序数であることが保証される。したがって上界の議論が扱うのは添字であり、その結論によって証人集合が一つの段階に入る。
<!--/-->

<!--en-->
For a fixed ordinal index `c`, the later hierarchy description needs four constructible sets associated with `Lset c`: the internal hierarchy table, the set of all formula codes, the graph of uniform satisfaction, and the environment tower. Adequacy places all four together in one later constructible stage, where a single bounded description can range over them.
<!--zh-->
对固定的序数指标 `c`，后续的层级描述需要与 `Lset c` 相关的四个可构造集合：内部层级表、全体公式码之集、统一满足关系的图，以及环境塔。充分性把这四个集合一同放进同一个更后的可构造层，使一条有界描述能够在那里遍历它们。
<!--ja-->
固定した順序数添字 `c` に対し、後の階層記述には `Lset c` に結びつく四つの構成可能集合、すなわち内部の階層表、すべての論理式符号の集合、一様な充足関係のグラフ、環境の塔が必要である。妥当性はこの四つを一つの後の構成可能段階にまとめて入れ、一つの有界な記述がそこでそれらを量化できるようにする。
<!--/-->

<!--en-->
Membership assertions and the witness conditions built from them are propositions. This matters when an element of a union yields only propositionally truncated information about which member of the family contains it: such information may be eliminated into a proposition, without choosing and retaining a particular index.
<!--zh-->
隶属断言以及由它们组成的见证条件都是命题。这一点在处理并集元素时至关重要：从并集隶属只能命题截断地知道该元素落在哪个族成员中；这些信息可以消去到一个命题中，却不能借此选定并保留某个特定指标。
<!--ja-->
所属の主張と、それらから組み立てる証人条件はいずれも命題である。このことは、合併の要素から、それを含む族の要素について命題的に切り詰められた情報しか得られない場面で重要である。その情報は命題へ消去できるが、特定の添字を選んで保持することはできない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
```

<!--en-->
Every set in the cumulative hierarchy has a small presentation: a small index type maps onto its elements. This presentation permits the next bounding construction to range over all members of an ordinal. In the other direction, membership in a family union exposes a family index only under propositional truncation, a distinction used essentially in the countable-chain arguments below.
<!--zh-->
累积层级中的每个集合都有一个小呈现：一个小索引类型映到它的全部元素。借助这个呈现，下一步取界可以遍历一个序数的所有成员。反过来，从属于集合族之并只能在命题截断下得到族的索引；这一差别是下文可数链论证的关键。
<!--ja-->
累積階層の各集合には小さな提示があり、小さな添字型からそのすべての要素への写像が与えられる。この提示により、次の上界構成は順序数の全要素にわたって動ける。逆に、族の合併への所属から族の添字が得られるのは命題的切り詰めの中だけである。この違いが、以下の可算鎖の議論で本質的に使われる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )
```

<!--en-->
We read ambient membership `x ∈ y` through its proposition of witnesses `⟨ x ∈ y ⟩`. This is membership in `V ℓ`; it should not be confused with membership in the constructible carrier introduced next.
<!--zh-->
我们通过见证命题 `⟨ x ∈ y ⟩` 读取外围隶属 `x ∈ y`。这是 `V ℓ` 中的隶属，不应与下一步引入的可构造载体内部隶属混同。
<!--ja-->
周囲の所属 `x ∈ y` を、その証人の命題 `⟨ x ∈ y ⟩` として読む。これは `V ℓ` における所属であり、次に導入する構成可能な台の内部の所属とは区別しなければならない。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
```

<!--en-->
An element of the constructible carrier `CS.S` packages an ambient set together with evidence that it is constructible. Consequently, the four witnesses below are first produced as elements of `CS.S`, and their first projections are the actual ambient sets whose membership in a later `Lset` is required.
<!--zh-->
可构造载体 `CS.S` 的一个元素把外围集合与其可构造性证据打包在一起。因此，下文的四个见证先构造成 `CS.S` 的元素；它们的第一投影才是需要证明属于某个更后 `Lset` 的实际外围集合。
<!--ja-->
構成可能な台 `CS.S` の要素は、周囲の集合と、それが構成可能であることの証拠をひとまとめにする。したがって以下の四つの証人は、まず `CS.S` の要素として構成される。その第一射影が、後の `Lset` への所属を示すべき実際の周囲の集合である。
<!--/-->

```agda
module CS = hPropStructure 𝒮ʟ using (S)
```

<!--en-->
## The four witnesses held by an adequate stage
<!--zh-->
## 充分层所容纳的四个见证
<!--ja-->
## 十分な段階が含む四つの証人
<!--/-->

<!--en-->
The witness module fixes an ordinal `c` with the proof that it is an ordinal.
<!--zh-->
见证模块固定一个序数 `c` 连同它是序数的证明。
<!--ja-->
証人のモジュールは、順序数 `c` と、それが順序数であることの証明を固定する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module At (c : V ℓ) (oc : IsOrd c) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The constructible stage `Lset c` is packaged as the carrier `A`. The hierarchy table, formula-code set, satisfaction graph and environment tower are then constructed from this carrier as four separate witnesses.
<!--zh-->
可构造层 `Lset c` 被打包为载体 `A`。随后以这个载体为基础，分别构造层级表、公式码集合、满足关系图与环境塔这四个见证。
<!--ja-->
構成可能段階 `Lset c` を台 `A` としてまとめる。この台から、階層表、論理式符号の集合、充足関係のグラフ、環境の塔という四つの証人をそれぞれ構成する。
<!--/-->

```agda
  A : CS.S
  A = LsetS c oc
```

<!--en-->
The ordinal index `c` is itself constructible: `ord∈Lset-suc` places it in `Lset (sucV c)`, and membership in an ordinal-indexed constructible stage yields the required evidence `cL`.
<!--zh-->
序数指标 `c` 自身也是可构造的：`ord∈Lset-suc` 把它放入 `Lset (sucV c)`，而属于一个由序数索引的可构造层便给出所需的可构造性证据 `cL`。
<!--ja-->
順序数添字 `c` 自身も構成可能である。`ord∈Lset-suc` が `c` を `Lset (sucV c)` に入れ、順序数で添字づけられた構成可能段階への所属から、必要な構成可能性の証拠 `cL` が得られる。
<!--/-->

```agda
  cL : ⟨ isL c ⟩
  cL = Lset→isL (sucV c) (suc-ord oc) c (ord∈Lset-suc c oc)
```

<!--en-->
The first witness is the internal hierarchy table at `c`. It records within `L` the constructible stages whose ordinal indices lie below `c`.
<!--zh-->
第一个见证是 `c` 处的内部层级表。它在 `L` 内部记录序数指标位于 `c` 以下的各个可构造层。
<!--ja-->
最初の証人は `c` における内部の階層表である。これは `L` の内部で、順序数添字が `c` より下にある構成可能段階を記録する。
<!--/-->

```agda
  hier : CS.S
  hier = hierL c cL oc
```

<!--en-->
The second witness is the set of all formula codes over the stage carrier. These are the codes later used by the hierarchy description.
<!--zh-->
第二个见证是层载体上全体公式码之集。这些码将在后续的层级描述中使用。
<!--ja-->
第二の証人は、段階の台の上のすべての論理式符号からなる集合である。これらの符号は、後の階層記述で使われる。
<!--/-->

```agda
  codes : CS.S
  codes = AllCodes A
```

<!--en-->
The ordered-pair graph of the uniform satisfaction table is the third witness: it records the value assigned to each key.
<!--zh-->
统一满足表的有序对图是第三个见证：它记录每个键被赋予的值。
<!--ja-->
一様な充足の表の順序対のグラフが第三の証人である。それぞれのキーに割り当てられた値を記録する。
<!--/-->

```agda
  table : CS.S
  table = SatGraph.pairs A
```

<!--en-->
The environment tower is the fourth witness: it collects the environments of every finite length.
<!--zh-->
环境塔是第四个见证：它收集每个有限长度的环境。
<!--ja-->
環境の塔が第四の証人である。すべての有限の長さの環境を集める。
<!--/-->

```agda
  tower : CS.S
  tower = Tower.tower A
```
</div>
</details>

<!--en-->
For an ordinal stage index `c`, the witness predicate requires the four underlying sets just constructed to belong to one common container `K`. It quantifies over the proof `oc : IsOrd c`, so the predicate does not retain a preferred proof of ordinality. Later `K` will be `Lset γ`, where `γ` is a larger ordinal index.
<!--zh-->
对一个序数层索引 `c`，见证谓词要求刚构造的四个底层集合都属于同一个公共容器 `K`。它量化证明 `oc : IsOrd c`，因而不会保留某一份偏好的序数性证明。后文将令 `K` 为 `Lset γ`，其中 `γ` 是更大的序数指标。
<!--ja-->
順序数である段階の添字 `c` に対し、証人述語は、いま構成した四つの基礎となる集合が一つの共通の容器 `K` に属することを要求する。証明 `oc : IsOrd c` を量化するため、特定の順序数性の証明を選んで保持しない。後では、より大きな順序数添字 `γ` に対する `Lset γ` を `K` とする。
<!--/-->

```agda
Witnesses : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Witnesses K c = (oc : IsOrd c)
  → ⟨ fst (At.hier c oc) ∈ K ⟩
  × ⟨ fst (At.codes c oc) ∈ K ⟩
  × ⟨ fst (At.table c oc) ∈ K ⟩
```

<!--en-->
The fourth membership completes the witness predicate: the environment tower belongs to the same container.
<!--zh-->
第四个隶属补全见证谓词：环境塔也属于同一容器。
<!--ja-->
四つ目の所属が証人の述語を完成させる。環境の塔も同じ容器の中にある。
<!--/-->

```agda
  × ⟨ fst (At.tower c oc) ∈ K ⟩
```

<!--en-->
The witness predicate is a proposition. For each possible proof that `c` is an ordinal, its conclusion is a product of four membership propositions; a dependent function whose values are propositions is again a proposition. This propositionhood later permits elimination from a propositionally truncated chain index directly into `Witnesses`, without selecting that index as data.
<!--zh-->
见证谓词是命题。对 `c` 为序数的每份可能证明，其结论都是四个隶属命题的积；取值均为命题的依赖函数仍是命题。这一命题性使后文能够把命题截断的链索引直接消去到 `Witnesses`，而不把该索引选作数据。
<!--ja-->
証人述語は命題である。`c` が順序数であることの各証明に対し、その結論は四つの所属命題の積である。また、値がすべて命題である依存関数も命題である。この命題性により、後では命題的に切り詰められた鎖の添字から `Witnesses` へ直接消去でき、その添字をデータとして選ぶ必要がない。
<!--/-->

```agda
isPropWitnesses : (K c : V ℓ) → isProp (Witnesses K c)
isPropWitnesses K c = isPropΠ λ oc →
  isProp× (snd (fst (At.hier c oc) ∈ K))
    (isProp× (snd (fst (At.codes c oc) ∈ K))
      (isProp× (snd (fst (At.table c oc) ∈ K)) (snd (fst (At.tower c oc) ∈ K))))
```

<!--en-->
An adequate index `γ` is an ordinal with three further properties: every `x ∈ γ` has `sucV x ∈ γ`, the ordinal `ω` belongs to `γ`, and every ordinal `c ∈ γ` has its four witness sets inside the single constructible stage `Lset γ`. The closure conditions concern the ordinal index `γ`; the witness condition concerns the distinct set `Lset γ`.
<!--zh-->
充分指标 `γ` 是一个序数，并满足另外三条性质：每个 `x ∈ γ` 都有 `sucV x ∈ γ`，序数 `ω` 属于 `γ`，且每个序数 `c ∈ γ` 的四个见证集合都位于同一个可构造层 `Lset γ` 内。闭合条件谈的是序数指标 `γ`，见证条件谈的则是与之不同的集合 `Lset γ`。
<!--ja-->
十分な添字 `γ` は順序数であり、さらに三つの性質をもつ。各 `x ∈ γ` に対して `sucV x ∈ γ` であり、順序数 `ω` が `γ` に属し、各順序数 `c ∈ γ` の四つの証人集合が一つの構成可能段階 `Lset γ` の中にある。閉包条件が述べる対象は順序数添字 `γ` であり、証人条件が述べる対象は、それとは異なる集合 `Lset γ` である。
<!--/-->

```agda
Adequate : V ℓ → Type (ℓ-suc ℓ)
Adequate γ =
    IsOrd γ
  × ((x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩)
  × ⟨ ω ∈ γ ⟩
```

<!--en-->
The last clause is where the two levels of the construction meet. Its argument `c ∈ γ` is a membership fact about ordinal indices, while its conclusion places the four sets associated with `c` inside the constructible stage `Lset γ`.
<!--zh-->
最后一条正是两种层次相接之处。前提 `c ∈ γ` 是序数指标之间的隶属事实，结论则把与 `c` 相关的四个集合放进可构造层 `Lset γ`。
<!--ja-->
最後の条項で、この構成の二つの層面が結びつく。前提 `c ∈ γ` は順序数添字どうしの所属であり、結論は `c` に結びつく四つの集合を構成可能段階 `Lset γ` に入れる。
<!--/-->

```agda
  × ((c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c)
```

<!--en-->
The four fields are named for the arguments ahead: ordinalness, successor closure, membership of the infinite ordinal, and the witness clause.
<!--zh-->
四个字段为后文论证命名：序数性、后继封闭、无穷序数的隶属，以及见证子句。
<!--ja-->
四つの欄が、これからの議論のために名付けられる。順序数性・後続の閉性・無限順序数の所属・そして証人の節である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Adequate (γ : V ℓ) (ad : Adequate γ) where
```
</summary>
<div class="submodule-fold-content">

```agda
  ord = ad .fst
  succ = ad .snd .fst
  ω∈ = ad .snd .snd .fst
  wit = ad .snd .snd .snd
```
</div>
</details>

<!--en-->
## Constructing an adequate stage above any ordinal
<!--zh-->
## 在任意序数之上构造充分层
<!--ja-->
## 任意の順序数より上に十分な段階を構成する
<!--/-->

<!--en-->
To take bounds over all members of a set `α`, use its small presentation `⟪ α ⟫`. The map `ι α` sends each presentation index to the ambient set it names. At this point `α` need not be described by the notation itself as an ordinal; ordinality enters when the construction proves that each named member is an ordinal.
<!--zh-->
为了对集合 `α` 的全体成员取界，使用它的小呈现 `⟪ α ⟫`。映射 `ι α` 把每个呈现索引送到它所指名的外围集合。此处这套记号本身并不要求 `α` 是序数；序数性将在构造证明每个被指名成员都是序数时进入。
<!--ja-->
集合 `α` のすべての要素にわたって上界を取るため、その小さな提示 `⟪ α ⟫` を使う。写像 `ι α` は、各提示添字を、それが名指す周囲の集合へ送る。この記法自体は、この時点で `α` を順序数とは仮定しない。順序数性は、名指された各要素が順序数であることを構成が示す段階で用いられる。
<!--/-->

```agda
private
  ι : (α : V ℓ) → ⟪ α ⟫ → V ℓ
  ι α = ⟪ α ⟫↪
```

<!--en-->
Every presented index names a member of the ordinal, through the bridge between the small and ambient membership relations.
<!--zh-->
每个被呈现索引经由小隶属与外围隶属之间的桥，指名该序数的一个成员。
<!--ja-->
提示された索引はどれも、小さな所属と周囲の所属の橋を通して、順序数の一つの要素を名指す。
<!--/-->

```agda
  ι∈ : (α : V ℓ) (m : ⟪ α ⟫) → ⟨ ι α m ∈ α ⟩
  ι∈ α m = ∈∈ₛ {a = ι α m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
```

<!--en-->
The transitivity of an ordinal is packaged once: two chained memberships inside the ordinal collapse into a single membership in it.
<!--zh-->
序数的传递性被打包一次：序数内两条链式隶属坍缩为对该序数的一次隶属。
<!--ja-->
順序数の推移性は一度だけまとめられる。順序数の内側でつらなった二つの所属は、その順序数への一つの所属になる。
<!--/-->

```agda
  tr : (β : V ℓ) → IsOrd β → (x y : V ℓ) → ⟨ x ∈ β ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ β ⟩
  tr β oβ x y x∈ y∈ = oβ .fst {x = x} {y = y} y∈ x∈
```

<!--en-->
Starting from an ordinal index `α`, one bounding step will construct a larger ordinal index `β`. The step pays all obligations generated by members of `α`: their successors and the birth-stage indices of their four witness sets. It does not yet claim that `β` is adequate, because it has not paid the corresponding obligations for new members of `β`.
<!--zh-->
从序数指标 `α` 出发，一步取界将构造一个更大的序数指标 `β`。这一步履行由 `α` 的成员产生的全部义务：它们的后继，以及它们四个见证集合的诞生层索引。此时尚不能断言 `β` 已经充分，因为对 `β` 中新增成员的相应义务还没有履行。
<!--ja-->
順序数添字 `α` から出発し、一回の上界構成で、より大きな順序数添字 `β` を作る。この一回で、`α` の要素から生じるすべての要請、すなわちそれらの後続と、四つの証人集合の誕生段階の添字を満たす。しかし、`β` に新たに加わった要素について同じ要請をまだ満たしていないので、この時点で `β` が十分であるとは主張しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Bound1 (α : V ℓ) (oα : IsOrd α) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Every packaged constructible set `s : CS.S` has a birth-stage index `stage (fst s) (snd s)`. The auxiliary expression records this operation in the context of a presented member of `α`; the resulting index depends on the witness set `s`, while the surrounding arguments keep track of the member for which that witness was built.
<!--zh-->
每个打包后的可构造集合 `s : CS.S` 都有诞生层索引 `stage (fst s) (snd s)`。这个辅助表达式在 `α` 的一个被呈现成员的语境中记录该运算；所得指标取决于见证集合 `s`，而外围参数则记录这个见证是为哪个成员构造的。
<!--ja-->
まとめられた各構成可能集合 `s : CS.S` には、誕生段階の添字 `stage (fst s) (snd s)` がある。この補助式は、`α` の提示された一要素という文脈の中で、この操作を記録する。得られる添字は証人集合 `s` に依存し、周囲の引数は、その証人がどの要素について作られたかを記録する。
<!--/-->

```agda
  private
    W : ⟪ α ⟫ → (c : V ℓ) → IsOrd c → CS.S → V ℓ
    W m c oc s = stage (fst s) (snd s)
```

<!--en-->
Every presented member of `α` is an ordinal, since members of ordinals are ordinals.
<!--zh-->
`α` 的每个被呈现成员都是序数，因为序数的成员是序数。
<!--ja-->
`α` の提示されたすべての要素は順序数である。順序数の要素は順序数だからである。
<!--/-->

```agda
    oc : (m : ⟪ α ⟫) → IsOrd (ι α m)
    oc m = mem-ord {A = α} oα (ι α m) (ι∈ α m)
```

<!--en-->
Applying `st` to each of the four witness constructions produces four ordinal-indexed families of birth stages. These are the families that the next common bounds must dominate.
<!--zh-->
把 `st` 分别用于四类见证构造，便得到四族由序数索引的诞生层指标。下一步的公共界必须严格界住的正是这四族指标。
<!--ja-->
`st` を四つの証人構成にそれぞれ適用すると、誕生段階の添字からなる四つの族が得られる。次の共通上界は、これら四つの族を厳密に上から抑える必要がある。
<!--/-->

```agda
    st : (f : (c : V ℓ) (o : IsOrd c) → CS.S) → ⟪ α ⟫ → V ℓ
    st f m = stage (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))
```

<!--en-->
The birth-stage index `st f m` is an ordinal. This follows from the general theorem `stage-ord` for the birth-stage construction, applied to the underlying set of the witness together with its constructibility evidence.
<!--zh-->
诞生层索引 `st f m` 是序数。这由诞生层构造的一般定理 `stage-ord` 得出；应用时使用见证的底层集合及其可构造性证据。
<!--ja-->
誕生段階の添字 `st f m` は順序数である。これは誕生段階の構成に関する一般定理 `stage-ord` を、証人の基礎となる集合とその構成可能性の証拠に適用して得られる。
<!--/-->

```agda
    st-ord : (f : (c : V ℓ) (o : IsOrd c) → CS.S) (m : ⟪ α ⟫) → IsOrd (st f m)
    st-ord f m = stage-ord (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))
```

<!--en-->
Five strict common bounds are taken. The first four bound the birth-stage indices of the hierarchy table, code set, satisfaction graph, and environment tower for every presented member of `α`. The fifth bounds the ordinal successors `sucV (ι α m)` themselves. These are bounds among ordinal indices; the fifth family is not a family of birth stages.
<!--zh-->
这里取五个严格公共界。前四个分别约束 `α` 的每个被呈现成员所对应的层级表、码集、满足图与环境塔的诞生层索引；第五个直接约束各序数后继 `sucV (ι α m)`。这些都是序数指标之间的界；第五族并不是一族诞生层。
<!--ja-->
ここで五つの厳密な共通上界を取る。最初の四つは、`α` の提示された各要素について、階層表、符号集合、充足グラフ、環境の塔の誕生段階の添字をそれぞれ上から抑える。五つ目は、順序数の後続 `sucV (ι α m)` 自身を上から抑える。これらは順序数添字の間の上界であり、五つ目の族は誕生段階の族ではない。
<!--/-->

```agda
    b1 = boundingOrd ⟪ α ⟫ (st At.hier) (st-ord At.hier)
    b2 = boundingOrd ⟪ α ⟫ (st At.codes) (st-ord At.codes)
    b3 = boundingOrd ⟪ α ⟫ (st At.table) (st-ord At.table)
    b4 = boundingOrd ⟪ α ⟫ (st At.tower) (st-ord At.tower)
    b5 = boundingOrd ⟪ α ⟫ (λ m → sucV (ι α m)) (λ m → suc-ord (oc m))
```

<!--en-->
A sixth strict bound contains both the starting index `α` and `ω`. Binary bounds then combine the six obligations: `b7` joins the first two witness bounds, `b8` joins the other two, `b9` joins the successor bound with the bound for `α` and `ω`, and `b10` joins the four witness bounds. No least bound is asserted; these operations merely provide strict common bounds with the required membership proofs.
<!--zh-->
第六个严格界同时包含起始指标 `α` 与 `ω`。随后用二元界合并六项义务：`b7` 合并前两个见证界，`b8` 合并另外两个见证界，`b9` 合并后继界与 `α`、`ω` 的公共界，`b10` 则合并四个见证界。这里不声称所得界最小；这些运算只给出严格公共界及所需的隶属证明。
<!--ja-->
六つ目の厳密な上界は、出発点の添字 `α` と `ω` の両方を含む。次に二項上界で六つの要請をまとめる。`b7` は最初の二つの証人上界を、`b8` は残る二つを、`b9` は後続の上界と `α` および `ω` の上界を、`b10` は四つの証人上界をそれぞれまとめる。最小の上界であるとは主張しない。これらの操作が与えるのは、必要な所属証明を伴う厳密な共通上界である。
<!--/-->

```agda
    b6 = bound2 α ω oα ω-ord
    b7 = bound2 (b1 .fst) (b2 .fst) (b1 .snd .fst) (b2 .snd .fst)
    b8 = bound2 (b3 .fst) (b4 .fst) (b3 .snd .fst) (b4 .snd .fst)
    b9 = bound2 (b5 .fst) (b6 .fst) (b5 .snd .fst) (b6 .snd .fst)
    b10 = bound2 (b7 .fst) (b8 .fst) (b7 .snd .fst) (b8 .snd .fst)
```

<!--en-->
One final binary bound joins the branch carrying successor, `α` and `ω` with the branch carrying the four birth-stage bounds. Its first component will therefore dominate all six kinds of obligation at once.
<!--zh-->
最后一次二元取界把两条分支合并：一条携带后继、`α` 与 `ω`，另一条携带四类诞生层之界。因此，它的第一分量同时严格界住全部六类义务。
<!--ja-->
最後の二項上界は、後者、`α`、`ω` を担う枝と、四種類の誕生段階の上界を担う枝とを合わせる。したがって、その第一成分は六種類の要請すべてを同時に厳密に上から抑える。
<!--/-->

```agda
    b11 = bound2 (b9 .fst) (b10 .fst) (b9 .snd .fst) (b10 .snd .fst)
```

<!--en-->
The first component of the final bound is the new ordinal index `β`. It is an index in `V ℓ`; the constructible stage used for witnesses will be `Lset β`.
<!--zh-->
最终界的第一分量是新的序数指标 `β`。它是 `V ℓ` 中的指标；容纳见证的可构造层将是 `Lset β`。
<!--ja-->
最終上界の第一成分を、新しい順序数添字 `β` とする。これは `V ℓ` の中の添字であり、証人を収める構成可能段階は `Lset β` である。
<!--/-->

```agda
  β : V ℓ
  β = b11 .fst
```

<!--en-->
The final bound is an ordinal, since it was built from ordinals by the binary bound.
<!--zh-->
最终界是序数，因为它由二元取界从序数构造而来。
<!--ja-->
最終の上界は順序数である。二項の上界の操作によって順序数から作られたからである。
<!--/-->

```agda
  oβ : IsOrd β
  oβ = b11 .snd .fst
```

<!--en-->
The two partial bounds feeding the last combination lie below the final bound.
<!--zh-->
喂给最后一次合并的两个部分界位于最终界之下。
<!--ja-->
最後の合成に供給された二つの部分的な上界は、最終の上界の下にある。
<!--/-->

```agda
  private
    b9∈ : ⟨ b9 .fst ∈ β ⟩
    b9∈ = b11 .snd .snd .fst
    b10∈ : ⟨ b10 .fst ∈ β ⟩
    b10∈ = b11 .snd .snd .snd
```

<!--en-->
Because `β` is transitive, strict membership can be propagated down the bound tree. From `b9 ∈ β` one obtains both the successor bound `b5 ∈ β` and the joint bound `b6 ∈ β` for `α` and `ω`; from `b10 ∈ β` one first obtains `b7 ∈ β`.
<!--zh-->
因为 `β` 具有传递性，严格隶属可以沿取界树向下传播。从 `b9 ∈ β` 可分别得到后继界 `b5 ∈ β`，以及 `α` 与 `ω` 的公共界 `b6 ∈ β`；从 `b10 ∈ β` 则先得到 `b7 ∈ β`。
<!--ja-->
`β` は推移的なので、厳密な所属を上界の木に沿って下へ伝えられる。`b9 ∈ β` から、後続の上界 `b5 ∈ β` と、`α` および `ω` の共通上界 `b6 ∈ β` が得られる。また `b10 ∈ β` から、まず `b7 ∈ β` が得られる。
<!--/-->

```agda
    b5∈ : ⟨ b5 .fst ∈ β ⟩
    b5∈ = tr β oβ (b9 .fst) (b5 .fst) b9∈ (b9 .snd .snd .fst)
    b6∈ : ⟨ b6 .fst ∈ β ⟩
    b6∈ = tr β oβ (b9 .fst) (b6 .fst) b9∈ (b9 .snd .snd .snd)
    b7∈ : ⟨ b7 .fst ∈ β ⟩
```

<!--en-->
The other branch gives `b8 ∈ β`. Descending once more through `b7`, the first witness bound `b1` also belongs to `β`. Repeating the same transitivity argument will place every remaining witness bound in `β`.
<!--zh-->
另一条分支给出 `b8 ∈ β`。再沿 `b7` 向下一步，第一个见证界 `b1` 也属于 `β`。重复同一传递性论证，便会把其余每个见证界都放入 `β`。
<!--ja-->
もう一方の枝から `b8 ∈ β` が得られる。さらに `b7` を一段下ると、最初の証人上界 `b1` も `β` に属する。同じ推移性の議論を繰り返せば、残る各証人上界も `β` に入る。
<!--/-->

```agda
    b7∈ = tr β oβ (b10 .fst) (b7 .fst) b10∈ (b10 .snd .snd .fst)
    b8∈ : ⟨ b8 .fst ∈ β ⟩
    b8∈ = tr β oβ (b10 .fst) (b8 .fst) b10∈ (b10 .snd .snd .snd)
    b1∈ : ⟨ b1 .fst ∈ β ⟩
    b1∈ = tr β oβ (b7 .fst) (b1 .fst) b7∈ (b7 .snd .snd .fst)
```

<!--en-->
The second and third witness bounds, `b2` and `b3`, are obtained from the two branches `b7` and `b8`. The fourth bound `b4` has the same position under `b8`, so the following line closes the symmetric argument.
<!--zh-->
第二、第三个见证界 `b2` 与 `b3` 分别从分支 `b7` 与 `b8` 得出。第四个见证界 `b4` 在 `b8` 下处于相同位置，所以下一行将闭合这个对称论证。
<!--ja-->
第二と第三の証人上界 `b2` と `b3` は、それぞれ枝 `b7` と `b8` から得られる。第四の上界 `b4` も `b8` の下で同じ位置にあるので、次の行でこの対称な議論が完結する。
<!--/-->

```agda
    b2∈ : ⟨ b2 .fst ∈ β ⟩
    b2∈ = tr β oβ (b7 .fst) (b2 .fst) b7∈ (b7 .snd .snd .snd)
    b3∈ : ⟨ b3 .fst ∈ β ⟩
    b3∈ = tr β oβ (b8 .fst) (b3 .fst) b8∈ (b8 .snd .snd .fst)
    b4∈ : ⟨ b4 .fst ∈ β ⟩
```

<!--en-->
The last descent through the witness branch gives `b4 ∈ β`. At this point each of the four birth-stage bounds has been related to the common ordinal index `β`.
<!--zh-->
沿见证分支的最后一次下降给出 `b4 ∈ β`。至此，四个诞生层之界都已与公共序数指标 `β` 建立严格隶属关系。
<!--ja-->
証人側の枝を最後に一段下ると `b4 ∈ β` が得られる。これで、四つの誕生段階の上界すべてが、共通の順序数添字 `β` に厳密に属することが分かった。
<!--/-->

```agda
    b4∈ = tr β oβ (b8 .fst) (b4 .fst) b8∈ (b8 .snd .snd .snd)
```

<!--en-->
The branch through `b6` also preserves the starting ordinal index: from `α ∈ b6` and `b6 ∈ β`, transitivity gives `α ∈ β`.
<!--zh-->
经过 `b6` 的分支还保留起始序数指标：由 `α ∈ b6` 与 `b6 ∈ β`，传递性给出 `α ∈ β`。
<!--ja-->
`b6` を通る枝は、出発点の順序数添字も保つ。`α ∈ b6` と `b6 ∈ β` から、推移性により `α ∈ β` が得られる。
<!--/-->

```agda
  α∈β : ⟨ α ∈ β ⟩
  α∈β = tr β oβ (b6 .fst) α b6∈ (b6 .snd .snd .fst)
```

<!--en-->
The same branch preserves `ω`: its membership in `b6`, followed by `b6 ∈ β`, yields the membership `ω ∈ β` needed later.
<!--zh-->
同一分支也保留 `ω`：先有 `ω ∈ b6`，再接上 `b6 ∈ β`，便得到后文所需的 `ω ∈ β`。
<!--ja-->
同じ枝は `ω` も保つ。`ω ∈ b6` に `b6 ∈ β` をつなぐと、後で必要となる `ω ∈ β` が得られる。
<!--/-->

```agda
  ω∈β : ⟨ ω ∈ β ⟩
  ω∈β = tr β oβ (b6 .fst) ω b6∈ (b6 .snd .snd .snd)
```

<!--en-->
If `x ∈ α`, the presentation fibre supplies an index `m` with `ι α m ≡ x`. The fifth common bound contains `sucV (ι α m)`, and its membership in `β` follows through `b5 ∈ β`; substitution along the fibre equality then yields `sucV x ∈ β`. Thus this step proves successor closure only for members of `α`, as required of one bounding step.
<!--zh-->
若 `x ∈ α`，呈现纤维便给出索引 `m` 及等式 `ι α m ≡ x`。第五个公共界包含 `sucV (ι α m)`，再经 `b5 ∈ β` 得到它属于 `β`；最后沿纤维等式作替换，便有 `sucV x ∈ β`。因此，这一步只对 `α` 的成员证明后继闭合，恰好符合一步取界的任务。
<!--ja-->
`x ∈ α` ならば、提示のファイバーから、`ι α m ≡ x` を満たす添字 `m` が得られる。五つ目の共通上界は `sucV (ι α m)` を含み、`b5 ∈ β` を経て、それが `β` に属することが分かる。最後にファイバーの等式に沿って置換し、`sucV x ∈ β` を得る。したがって、この一回の構成が示す後続閉包は `α` の要素に対するものだけであり、一回の上界構成に必要な結論と正確に一致する。
<!--/-->

```agda
  suc∈β : (x : V ℓ) → ⟨ x ∈ α ⟩ → ⟨ sucV x ∈ β ⟩
  suc∈β x x∈ = subst (λ u → ⟨ sucV u ∈ β ⟩) (fib .snd)
    (tr β oβ (b5 .fst) (sucV (ι α (fib .fst))) b5∈ (b5 .snd .snd (fib .fst)))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ x)
```

<!--en-->
The fibre is recovered from the ambient membership proof by `∈-asFiber`. Here the conclusion is an actual dependent pair, rather than merely a propositionally truncated existence: the small presentation uses an embedding, so the fibre identifying the presentation index of `x` is proposition-valued.
<!--zh-->
`∈-asFiber` 从外围隶属证明恢复这个纤维。这里的结论是一个实际的依值对，而不只是命题截断的存在：小呈现使用嵌入，所以识别 `x` 的呈现索引之纤维取值于命题。
<!--ja-->
`∈-asFiber` は、周囲の所属の証明からこのファイバーを復元する。ここで得られるのは実際の依存対であり、命題的に切り詰められた存在だけではない。小さな提示は埋め込みを使うため、`x` の提示添字を同定するファイバーは命題値だからである。
<!--/-->

```agda
    fib = ∈-asFiber {a = x} {b = α} x∈
```

<!--en-->
The common ordinal bound `β` has already been arranged to dominate the birth-stage bounds for all four witnesses. We now use that arrangement to place the witnesses themselves in the constructible level `Lset β`.
<!--zh-->
公共序数界 `β` 已经严格界住四类见证的出生层指标。现在要利用这些界，把见证本身放入可构造层 `Lset β`。
<!--ja-->
共通の順序数上界 `β` は、四種類の証人の出生段階の添字をすべて厳密に上から押さえるように構成されている。ここから、その証人自身を構成可能段階 `Lset β` に入れる。
<!--/-->

```agda
  private
```

<!--en-->
Fix one of the four witness constructions `f` and an index `m` presenting a member of `α`. Its value is born in `Lset (st f m)`; the recorded bound `b.fst` strictly contains this birth index, and the final bound `β` strictly contains `b.fst`. The landing lemma packages the resulting membership in `Lset β`.
<!--zh-->
固定四类见证构造之一 `f`，并取一个呈现 `α` 的成员的索引 `m`。相应见证出生于 `Lset (st f m)`；记录的界 `b.fst` 严格包含这个出生指标，而最终界 `β` 又严格包含 `b.fst`。安放引理把由此得到的 `Lset β` 中的隶属关系封装起来。
<!--ja-->
四つの証人構成の一つ `f` と、`α` の要素を呈示する添字 `m` を固定する。対応する証人は `Lset (st f m)` に現れ、その出生添字は記録された上界 `b.fst` に属し、さらに `b.fst` は最終上界 `β` に属する。着地の補題は、ここから得られる `Lset β` への所属をまとめる。
<!--/-->

```agda
    land : (f : (c : V ℓ) (o : IsOrd c) → CS.S)
           (b : Σ[ σ ∈ V ℓ ] (IsOrd σ × ((m : ⟪ α ⟫) → ⟨ st f m ∈ σ ⟩)))
         → ⟨ b .fst ∈ β ⟩
         → (m : ⟪ α ⟫) → ⟨ fst (f (ι α m) (oc m)) ∈ Lset β ⟩
    land f b b∈ m =
```

<!--en-->
The inner use of `Lset-mono` moves the witness from `Lset (st f m)` to `Lset (b.fst)`. The outer use then moves it from `Lset (b.fst)` to `Lset β`; both moves follow from strict membership between the corresponding ordinal indices.
<!--zh-->
内层的 `Lset-mono` 把见证从 `Lset (st f m)` 搬到 `Lset (b.fst)`，外层的应用再把它搬到 `Lset β`。两步分别依据相应序数指标之间的严格隶属关系。
<!--ja-->
内側の `Lset-mono` は証人を `Lset (st f m)` から `Lset (b.fst)` へ運び、外側の適用がさらに `Lset β` へ運ぶ。どちらの移動も、対応する順序数添字どうしの厳密な所属に基づく。
<!--/-->

```agda
      Lset-mono {α = β} {β = b .fst} b∈
        (Lset-mono {α = b .fst} {β = st f m} (b .snd .snd m)
          (stage-mem (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))))
```

<!--en-->
For the member presented by `m`, the proof first lands the hierarchy table and the formula-code set in `Lset β`. The caller may supply any proof `o : IsOrd (ι α m)`; since ordinality is a proposition, it can be identified with the proof `oc m` used to construct the witnesses.
<!--zh-->
对由 `m` 呈现的成员，证明先把层级表与公式码集合放入 `Lset β`。调用者可以给出任意证明 `o : IsOrd (ι α m)`；由于序数性是命题，它可与构造见证时使用的证明 `oc m` 认同。
<!--ja-->
`m` が呈示する要素について、まず階層表と論理式コードの集合を `Lset β` に入れる。呼び出し側は任意の証明 `o : IsOrd (ι α m)` を与えられるが、順序数性は命題なので、証人の構成に用いた `oc m` と同一視できる。
<!--/-->

```agda
    witAt : (m : ⟪ α ⟫) → Witnesses (Lset β) (ι α m)
    witAt m o =
        subst (λ u → ⟨ fst (At.hier (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
          (land At.hier b1 b1∈ m)
      , ( subst (λ u → ⟨ fst (At.codes (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
```

<!--en-->
The same argument completes the code-set membership and places the satisfaction graph and the environment tower in `Lset β`. Thus all four components of `Witnesses (Lset β) (ι α m)` are obtained with no dependence on a particular proof of ordinality.
<!--zh-->
同一论证完成码集合的隶属证明，并把满足关系图与环境塔放入 `Lset β`。于是得到 `Witnesses (Lset β) (ι α m)` 的全部四个分量，而且结果不依赖某一份特定的序数性证明。
<!--ja-->
同じ議論でコード集合の所属を完成し、充足関係のグラフと環境の塔も `Lset β` に入れる。これで `Witnesses (Lset β) (ι α m)` の四成分がすべて得られ、その結果は特定の順序数性証明に依存しない。
<!--/-->

```agda
            (land At.codes b2 b2∈ m)
        , ( subst (λ u → ⟨ fst (At.table (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.table b3 b3∈ m)
          , subst (λ u → ⟨ fst (At.tower (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.tower b4 b4∈ m) ))
```

<!--en-->
A membership proof `c ∈ α` has an actual presentation fibre: it yields an index `m` together with an equality `ι α m ≡ c`. Transporting `witAt m` along that equality gives the four witnesses for the abstractly named member `c`; this step does not eliminate a propositional truncation or make a choice.
<!--zh-->
一份成员证明 `c ∈ α` 带有实际的呈现纤维：它给出索引 `m` 以及等式 `ι α m ≡ c`。沿该等式搬运 `witAt m`，便得到抽象指定的成员 `c` 的四个见证；这一步既不消去命题截断，也不作选择。
<!--ja-->
所属の証明 `c ∈ α` からは実際の提示ファイバーが得られ、添字 `m` と等式 `ι α m ≡ c` が取り出される。その等式に沿って `witAt m` を輸送すれば、抽象的に指定された要素 `c` の四つの証人が得られる。ここでは命題的切り詰めの除去も選択も行わない。
<!--/-->

```agda
  wit : (c : V ℓ) → ⟨ c ∈ α ⟩ → Witnesses (Lset β) c
  wit c c∈ = subst (Witnesses (Lset β)) (fib .snd) (witAt (fib .fst))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ c)
    fib = ∈-asFiber {a = c} {b = α} c∈
```
</div>
</details>

<!--en-->
The union construction begins with an arbitrary natural-number-indexed family `ch` of ordinals. No monotonicity assumption is needed for the union itself; the two later applications will separately prove that each entry belongs to its successor.
<!--zh-->
并构造从任意自然数索引的序数族 `ch` 开始。取并本身不要求该族单调；后面的两次应用会另行证明每一项属于其后继项。
<!--ja-->
合併の構成は、自然数で添字づけられた任意の順序数族 `ch` から始まる。合併そのものには単調性を仮定せず、後の二つの適用で各項が次の項に属することを別に証明する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Union (ch : ℕ → V ℓ) (och : (n : ℕ) → IsOrd (ch n)) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The cumulative-hierarchy union expects a small index type at the ambient universe level. Replacing `ℕ` by `Lift ℕ` changes only its universe placement: `F (lift n)` is still the ordinal `ch n`.
<!--zh-->
累积层级中的并要求索引小类型位于外围宇宙层级。用 `Lift ℕ` 代替 `ℕ` 只改变其宇宙位置：`F (lift n)` 仍是序数 `ch n`。
<!--ja-->
累積階層の合併は、周囲の宇宙レベルにある小さな添字型を要求する。`ℕ` を `Lift ℕ` に替えても変わるのは宇宙での位置だけで、`F (lift n)` は依然として順序数 `ch n` である。
<!--/-->

```agda
  private
    F : Lift {ℓ-zero} {ℓ} ℕ → V ℓ
    F n = ch (lower n)
```

<!--en-->
The set-theoretic union of the family is denoted by the ordinal index `γ`. At this point `γ` is a set in the ambient cumulative hierarchy; the associated constructible level is `Lset γ`.
<!--zh-->
这个序数族的集合论并记为序数指标 `γ`。此时 `γ` 是外围累积层级中的集合；与它对应的可构造层是 `Lset γ`。
<!--ja-->
この順序数族の集合論的な合併を、順序数添字 `γ` と書く。この時点で `γ` は周囲の累積階層の集合であり、対応する構成可能段階は `Lset γ` である。
<!--/-->

```agda
  γ : V ℓ
  γ = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) F)
```

<!--en-->
The set-theoretic union of any family of ordinals is again an ordinal. Applying that fact to `F` proves `IsOrd γ`; no ordering or cofinality property of the natural-number index is used here.
<!--zh-->
任意序数族的集合论并仍是序数。把这一事实用于 `F` 便得到 `IsOrd γ`；这里没有使用自然数索引的次序性质或共尾性质。
<!--ja-->
任意の順序数族の集合論的合併は、再び順序数である。この事実を `F` に適用して `IsOrd γ` を得る。ここでは自然数添字の順序や共終性に関する性質を使わない。
<!--/-->

```agda
  oγ : IsOrd γ
  oγ = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) F (λ n → och (lower n))
```

<!--en-->
The inward reading admits every member of every chain entry into the union.
<!--zh-->
向内读式把链中每一项的每个成员都纳入并。
<!--ja-->
内向きの読み出しが、列のそれぞれの項目のすべての要素を、合併の中に受け入れる。
<!--/-->

```agda
  into : (n : ℕ) (x : V ℓ) → ⟨ x ∈ ch n ⟩ → ⟨ x ∈ γ ⟩
  into n x = union-family-in (Lift {ℓ-zero} {ℓ} ℕ) F (lift n) x
```

<!--en-->
The outward reading recovers, under truncation, a chain entry containing any given member of the union. The truncated index is consumed only into propositions.
<!--zh-->
向外读法在截断下恢复包含并中任一给定成员的链项。截断索引仅被消耗到命题。
<!--ja-->
外向きの読み出しは、切り詰めのもとで、合併の任意の要素を含む列の項目を復元する。切り詰められた添字は、命題の中だけで消費される。
<!--/-->

```agda
  outof : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ ch n ⟩ ∥₁
  outof x h = map₁ (λ { (n , hn) → lower n , hn })
    (union-family-out (Lift {ℓ-zero} {ℓ} ℕ) F x h)
```
</div>
</details>

<!--en-->
One bounding step settles only the obligations generated by the preceding ordinal. To settle every obligation generated along the construction, start above `p` and `ω`, repeat `Bound1` through a natural-number sequence, and take the union of the resulting ordinal indices.
<!--zh-->
一步取界只履行前一个序数所产生的义务。为了履行构造途中出现的每一项义务，先取一个严格包含 `p` 与 `ω` 的起点，沿自然数序列反复应用 `Bound1`，再对所得序数指标取并。
<!--ja-->
一回の上界構成が満たすのは、直前の順序数から生じた要請だけである。構成の途中で生じるすべての要請を満たすため、`p` と `ω` を厳密に含む点から始め、自然数列に沿って `Bound1` を繰り返し、得られた順序数添字の合併を取る。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Above (p : V ℓ) (op : IsOrd p) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The initial bound is an ordinal that strictly contains both the starting ordinal `p` and the ordinal `ω`. This immediately supplies the two memberships that must survive into the final union.
<!--zh-->
初始界是一个同时严格包含起始序数 `p` 与序数 `ω` 的序数。这直接给出随后要保留到最终并中的两条隶属关系。
<!--ja-->
最初の上界は、出発順序数 `p` と順序数 `ω` の両方を厳密に含む順序数である。これにより、最終的な合併まで保つべき二つの所属が直ちに得られる。
<!--/-->

```agda
  private
    base = bound2 p ω op ω-ord
```

<!--en-->
The zeroth ordinal is the initial common bound. Each later ordinal applies `Bound1` to its predecessor, so obligations arising from members of `ch n` are fulfilled in `ch (suc n)`; a single step is not claimed to be adequate for all of its own members.
<!--zh-->
第零个序数是初始公共界。此后每个序数都对前一项应用 `Bound1`，因此由 `ch n` 的成员产生的义务会在 `ch (suc n)` 中得到满足；这里并未声称单独一步已对其自身所有成员充分。
<!--ja-->
第零の順序数は最初の共通上界である。その後は各順序数を直前の項に `Bound1` を適用して作るので、`ch n` の要素から生じる義務は `ch (suc n)` で満たされる。一回の構成だけで、その結果自身の全要素について十分になるとは主張していない。
<!--/-->

```agda
  ch : ℕ → Σ[ β ∈ V ℓ ] IsOrd β
  ch zero = base .fst , base .snd .fst
  ch (suc n) = Bound1.β (ch n .fst) (ch n .snd) , Bound1.oβ (ch n .fst) (ch n .snd)
```

<!--en-->
We now apply the preceding union construction to these ordinal indices. Its inward map will insert known memberships into the union, while its outward map will locate an arbitrary member only under propositional truncation.
<!--zh-->
现在把前面的并构造应用于这些序数指标。其向内映射把已知成员关系送入并，其向外映射则只能在命题截断下定位包含任意给定成员的某一项。
<!--ja-->
ここで、先の合併構成をこれらの順序数添字に適用する。内向きの写像は既知の所属を合併へ送り、外向きの写像は任意の要素を含む項を命題的切り詰めのもとでのみ位置づける。
<!--/-->

```agda
  module C = Union (λ n → ch n .fst) (λ n → ch n .snd) using (into; outof; oγ; γ)
```

<!--en-->
Let `γ` be this union of ordinal indices. The one-step delay is now absorbed by the union: any member found at one entry has its successor and four witness sets handled by a later entry. The witnesses ultimately have to lie in `Lset γ`, not in the index `γ` itself.
<!--zh-->
令 `γ` 为这些序数指标之并。取并吸收了一步延迟：任何在某一项中出现的成员，其后继与四个见证都会由后续项处理。最终，见证必须属于 `Lset γ`，而不是属于指标 `γ` 本身。
<!--ja-->
これらの順序数添字の合併を `γ` とする。一段階の遅れは合併によって吸収される。ある項に現れた要素について、その後者と四つの証人集合は後の項で処理される。最終的に証人が属すべき先は添字 `γ` 自身ではなく、`Lset γ` である。
<!--/-->

```agda
  γ : V ℓ
  γ = C.γ
```

<!--en-->
Because every `ch n` is an ordinal, their set-theoretic union `γ` is an ordinal as well. This establishes only `IsOrd γ`; the closure and witness fields of `Adequate γ` are proved separately below.
<!--zh-->
由于每个 `ch n` 都是序数，它们的集合论并 `γ` 也是序数。这里仅得到 `IsOrd γ`；`Adequate γ` 的闭包字段与见证字段将在下文分别证明。
<!--ja-->
各 `ch n` が順序数なので、その集合論的合併 `γ` も順序数である。ここで得られるのは `IsOrd γ` だけであり、`Adequate γ` の閉性と証人の成分は以下で別に証明する。
<!--/-->

```agda
  oγ : IsOrd γ
  oγ = C.oγ
```

<!--en-->
Each chain entry is strictly below its successor entry, by the membership clause of the one-step bound.
<!--zh-->
链的每项严格低于其后继项，由一步取界的隶属子句而来。
<!--ja-->
列のそれぞれの項目は、その後続の項目より厳密に下にある。一段階の上界の所属の条項によるものである。
<!--/-->

```agda
  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = Bound1.α∈β (ch n .fst) (ch n .snd)
```

<!--en-->
To put the ordinal index `ch n` itself into the union `γ`, use its strict membership in `ch (suc n)` and then include every member of `ch (suc n)` in the union. This fact later provides the index comparison needed for monotonicity of `Lset`.
<!--zh-->
要把序数指标 `ch n` 本身放入并 `γ`，先用它严格属于 `ch (suc n)`，再把 `ch (suc n)` 的每个成员纳入并。这个事实稍后提供应用 `Lset` 单调性所需的指标比较。
<!--ja-->
順序数添字 `ch n` 自身を合併 `γ` に入れるには、まず `ch n ∈ ch (suc n)` を使い、ついで `ch (suc n)` の各要素を合併へ入れる。この事実が、後で `Lset` の単調性に必要な添字の比較を与える。
<!--/-->

```agda
    ch∈γ : (n : ℕ) → ⟨ ch n .fst ∈ γ ⟩
    ch∈γ n = C.into (suc n) (ch n .fst) (up n)
```

<!--en-->
The base bound already contains `p`. Since the base is the zeroth entry of the family, the inward union map preserves this membership and yields `p ∈ γ`.
<!--zh-->
基础界已经包含 `p`。它是该序列的第零项，所以并的向内映射保留这条隶属关系，得到 `p ∈ γ`。
<!--ja-->
基底の上界はすでに `p` を含む。これは列の第零項なので、合併の内向きの写像がこの所属を保ち、`p ∈ γ` を与える。
<!--/-->

```agda
  p∈γ : ⟨ p ∈ γ ⟩
  p∈γ = C.into zero p (base .snd .snd .fst)
```

<!--en-->
The same inward map carries `ω ∈ ch 0` to `ω ∈ γ`. This supplies the specific membership field required by `Adequate γ`.
<!--zh-->
同一个向内映射把 `ω ∈ ch 0` 送为 `ω ∈ γ`。这给出 `Adequate γ` 所要求的那项具体隶属事实。
<!--ja-->
同じ内向きの写像が `ω ∈ ch 0` を `ω ∈ γ` へ送る。これが `Adequate γ` に必要な所属の成分である。
<!--/-->

```agda
  ω∈γ : ⟨ ω ∈ γ ⟩
  ω∈γ = C.into zero ω (base .snd .snd .snd)
```

<!--en-->
Given `x ∈ γ`, the outward map produces the propositionally truncated existence of an index `n` with `x ∈ ch n`. In each branch, the next application of `Bound1` puts `sucV x` in `ch (suc n)`, hence in `γ`. The branches may be recombined because the target membership `sucV x ∈ γ` is a proposition; no particular `n` escapes the truncation.
<!--zh-->
给定 `x ∈ γ`，向外映射只给出命题截断的存在性：某个指标 `n` 满足 `x ∈ ch n`。在截断内的每个分支中，下一次 `Bound1` 把 `sucV x` 放入 `ch (suc n)`，继而放入 `γ`。目标成员关系 `sucV x ∈ γ` 是命题，所以这些分支可以重新合并；没有任何特定的 `n` 逸出命题截断。
<!--ja-->
`x ∈ γ` が与えられると、外向きの写像は `x ∈ ch n` を満たす添字 `n` の命題的に切り詰められた存在だけを与える。切り詰めの各分岐では、次の `Bound1` が `sucV x` を `ch (suc n)` に入れ、そこから `γ` に入れる。目標の所属 `sucV x ∈ γ` は命題なので、各分岐を再びまとめられる。特定の `n` が命題的切り詰めの外へ取り出されることはない。
<!--/-->

```agda
  succ : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩
  succ x x∈ = rec₁ (snd (sucV x ∈ γ))
    (λ { (n , x∈n) → C.into (suc n) (sucV x) (Bound1.suc∈β (ch n .fst) (ch n .snd) x x∈n) })
    (C.outof x x∈)
```

<!--en-->
For `c ∈ γ`, the outward map likewise gives the propositionally truncated existence of `n` with `c ∈ ch n`. In each branch, the one-step bound supplies the four witnesses in `Lset (ch (suc n))`, and `ch (suc n) ∈ γ` lets `Lset-mono` move them into `Lset γ`. The result can be eliminated from the truncation because `Witnesses (Lset γ) c` is a proposition.
<!--zh-->
对 `c ∈ γ`，向外映射同样只给出命题截断的存在性：某个 `n` 满足 `c ∈ ch n`。在每个分支中，一步取界在 `Lset (ch (suc n))` 中提供四个见证，而 `ch (suc n) ∈ γ` 使 `Lset-mono` 能把它们搬入 `Lset γ`。由于 `Witnesses (Lset γ) c` 是命题，可以把所得结果从命题截断中消去。
<!--ja-->
`c ∈ γ` に対しても、外向きの写像が与えるのは `c ∈ ch n` を満たす `n` の命題的に切り詰められた存在だけである。各分岐では、一段階の上界構成が四つの証人を `Lset (ch (suc n))` に用意し、`ch (suc n) ∈ γ` に沿う `Lset-mono` がそれらを `Lset γ` へ運ぶ。`Witnesses (Lset γ) c` は命題なので、得られた結果を命題的切り詰めから除去できる。
<!--/-->

```agda
  wit : (c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c
  wit c c∈ = rec₁ (isPropWitnesses (Lset γ) c)
    (λ { (n , c∈n) → λ oc →
      let w = Bound1.wit (ch n .fst) (ch n .snd) c c∈n oc
          mono = Lset-mono {α = γ} {β = ch (suc n) .fst} (ch∈γ (suc n))
```

<!--en-->
The single map `mono` is monotonicity of the constructible hierarchy from the index `ch (suc n)` to the index `γ`. Applying it separately to the hierarchy table, code set, satisfaction graph and environment tower completes the four-component witness tuple.
<!--zh-->
映射 `mono` 表示可构造层级从指标 `ch (suc n)` 到指标 `γ` 的单调性。分别把它用于层级表、码集合、满足关系图与环境塔，便完成四分量的见证元组。
<!--ja-->
写像 `mono` は、添字 `ch (suc n)` から添字 `γ` への構成可能階層の単調性を表す。これを階層表、コード集合、充足関係のグラフ、環境の塔にそれぞれ適用して、四成分の証人を完成する。
<!--/-->

```agda
      in mono (w .fst) , ( mono (w .snd .fst) , ( mono (w .snd .snd .fst) , mono (w .snd .snd .snd) )) })
    (C.outof c c∈)
```

<!--en-->
The ordinal index `γ` now satisfies all four clauses of `Adequate`: ordinality, successor closure, membership of `ω`, and containment of the four witnesses for every `c ∈ γ` in the distinct constructible stage `Lset γ`. This four-part conclusion is the full content of adequacy used later.
<!--zh-->
序数指标 `γ` 现在满足 `Adequate` 的全部四条：它是序数，对后继封闭，包含 `ω`，并把每个 `c ∈ γ` 的四个见证放入与指标有别的可构造层 `Lset γ`。后文所用的充分性，其全部内容正是这四条。
<!--ja-->
順序数添字 `γ` は、ここで `Adequate` の四つの条項をすべて満たす。すなわち、順序数性、後者閉包、`ω` の所属、そして各 `c ∈ γ` に対応する四つの証人を、添字とは別の構成可能段階 `Lset γ` に入れることである。後で使う妥当性の内容は、この四項目に尽きる。
<!--/-->

```agda
  adequate : Adequate γ
  adequate = oγ , ( succ , ( ω∈γ , wit ))
```
</div>
</details>

<!--en-->
The theorem returns an explicit ordinal index `γ`, together with `p ∈ γ` and `Adequate γ`. The outer dependent pair is not truncated, so later arguments may name this `γ`; the construction proves neither that it is least nor that it is obtained by a standard ordinal operation such as `p + ω`.
<!--zh-->
该定理显式返回序数指标 `γ`，并附带 `p ∈ γ` 与 `Adequate γ`。外层依值对没有截断，所以后续论证可以指称这个 `γ`；构造既不证明它最小，也不证明它由 `p + ω` 之类的标准序数运算得到。
<!--ja-->
この定理は順序数添字 `γ` を明示的に返し、`p ∈ γ` と `Adequate γ` を添える。外側の依存対は切り詰められていないので、後の議論はこの `γ` を名指せる。ただし、それが最小であることも、`p + ω` のような標準的順序数演算で得られることも証明していない。
<!--/-->

```agda
adequate-above : (p : V ℓ) → IsOrd p
               → Σ[ γ ∈ V ℓ ] (IsOrd γ × ⟨ p ∈ γ ⟩ × Adequate γ)
adequate-above p op = Above.γ p op , ( Above.oγ p op , ( Above.p∈γ p op , Above.adequate p op ))
```

<!--en-->
## Strengthening the conditions throughout a stage
<!--zh-->
## 在整个层中强化充分性
<!--ja-->
## 段階全体で十分性を強化する
<!--/-->

<!--en-->
`Superadequate λ` means that for every `d ∈ λ` there merely exists an adequate ordinal index `γ` with both `γ ∈ λ` and `d ∈ γ`. Thus `γ` lies strictly below the ordinal `λ` and covers `d`, but the propositional truncation retains neither a chosen `γ` nor a least one.
<!--zh-->
`Superadequate λ` 表示：对每个 `d ∈ λ`，仅仅存在充分序数指标 `γ`，满足 `γ ∈ λ` 且 `d ∈ γ`。因此 `γ` 严格位于序数 `λ` 之下并覆盖 `d`，但命题截断既不保留选定的 `γ`，也不保留最小的 `γ`。
<!--ja-->
`Superadequate λ` は、各 `d ∈ λ` に対して、`γ ∈ λ` と `d ∈ γ` を満たす十分な順序数添字 `γ` が単に存在することを意味する。したがって `γ` は順序数 `λ` より厳密に下にあり、`d` を含むが、命題的切り詰めは特定の `γ` も最小の `γ` も保持しない。
<!--/-->

```agda
Superadequate : V ℓ → Type (ℓ-suc ℓ)
Superadequate lam = (d : V ℓ) → ⟨ d ∈ lam ⟩
  → ∥ Σ[ γ ∈ V ℓ ] (⟨ γ ∈ lam ⟩ × ⟨ d ∈ γ ⟩ × Adequate γ) ∥₁
```

<!--en-->
To build such a strengthened adequate stage above an ordinal `α`, we iterate `adequate-above` once more. This time every entry in the natural-number sequence is already an adequate ordinal index, so the entries themselves can later serve as local adequate witnesses.
<!--zh-->
为在序数 `α` 之上构造这样的超充分层，再次迭代 `adequate-above`。这一次，自然数序列的每一项已经是充分序数指标，因而这些项本身稍后可充当局部充分见证。
<!--ja-->
順序数 `α` より上にこの強化された十分な段階を作るため、`adequate-above` をもう一度反復する。今度は自然数列の各項がすでに十分な順序数添字なので、その項自身を後で局所的な十分な証人として使える。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Super (α : V ℓ) (oα : IsOrd α) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The zeroth entry is the explicit ordinal index returned by `adequate-above α oα`. It is adequate and strictly contains the starting ordinal `α`; these facts are stored with the entry for later use.
<!--zh-->
第零项是 `adequate-above α oα` 显式返回的序数指标。它是充分的，并严格包含起始序数 `α`；这两项事实随该项保存，供后文使用。
<!--ja-->
第零項は `adequate-above α oα` が明示的に返す順序数添字である。この添字は十分であり、出発順序数 `α` を厳密に含む。これらの事実は後で使えるよう項とともに保持される。
<!--/-->

```agda
  ch : ℕ → Σ[ γ ∈ V ℓ ] (IsOrd γ × Adequate γ)
  ch zero =
    adequate-above α oα .fst
    , ( adequate-above α oα .snd .fst , adequate-above α oα .snd .snd .snd )
  ch (suc n) =
```

<!--en-->
From an adequate ordinal index `ch n`, another application of `adequate-above` produces the next adequate index `ch (suc n)` with `ch n ∈ ch (suc n)`. The theorem supplies some such next index explicitly, without asserting minimality.
<!--zh-->
从充分序数指标 `ch n` 出发，再次应用 `adequate-above` 得到下一充分指标 `ch (suc n)`，并有 `ch n ∈ ch (suc n)`。该定理显式提供某个这样的下一指标，但不声称其最小。
<!--ja-->
十分な順序数添字 `ch n` にもう一度 `adequate-above` を適用すると、次の十分な添字 `ch (suc n)` と所属 `ch n ∈ ch (suc n)` が得られる。この定理はそのような次の添字を明示的に与えるが、最小性は主張しない。
<!--/-->

```agda
    adequate-above (ch n .fst) (ch n .snd .fst) .fst
    , ( adequate-above (ch n .fst) (ch n .snd .fst) .snd .fst
      , adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .snd )
```

<!--en-->
Apply the union construction to this sequence of adequate ordinal indices. As before, membership in the union can be localized to an entry only under propositional truncation.
<!--zh-->
把并构造应用于这个充分序数指标序列。与前面一样，并中的成员只能在命题截断下局部化到某一项。
<!--ja-->
この十分な順序数添字の列に合併構成を適用する。先ほどと同様、合併の要素をある項に位置づけられるのは命題的切り詰めのもとだけである。
<!--/-->

```agda
  module U = Union (λ n → ch n .fst) (λ n → ch n .snd .fst) using (into; outof; oγ; γ)
```

<!--en-->
Denote the union of these ordinal indices by `lam` in the code and by `λ` in the exposition. The proof concerns the ordinal index `λ`: it will satisfy both `Adequate λ` and `Superadequate λ`. The corresponding constructible stage, used only in the witness clauses, is `Lset λ`.
<!--zh-->
把这些序数指标的并在代码中记作 `lam`，在正文中记作 `λ`。下文证明的是序数指标 `λ` 同时满足 `Adequate λ` 与 `Superadequate λ`；只在见证子句中使用的相应可构造层是 `Lset λ`。
<!--ja-->
これらの順序数添字の合併を、コードでは `lam`、本文では `λ` と書く。以下で示すのは、順序数添字 `λ` が `Adequate λ` と `Superadequate λ` の両方を満たすことである。対応する構成可能段階 `Lset λ` は、証人の条項でのみ使われる。
<!--/-->

```agda
  lam : V ℓ
  lam = U.γ
```

<!--en-->
The set-theoretic union `λ` is an ordinal because all entries `ch n` are ordinals. No stronger limit, regularity or cardinal property follows from this argument.
<!--zh-->
由于每个 `ch n` 都是序数，集合论并 `λ` 也是序数。这个论证不推出更强的极限性、正则性或基数性质。
<!--ja-->
各 `ch n` が順序数なので、その集合論的合併 `λ` も順序数である。この議論から、より強い極限性、正則性、基数としての性質は導かれない。
<!--/-->

```agda
  olam : IsOrd lam
  olam = U.oγ
```

<!--en-->
Each chain entry is strictly below its successor, by the strict membership produced by `adequate-above`.
<!--zh-->
链的每项严格低于其后继，由 `adequate-above` 产出的严格隶属而来。
<!--ja-->
列のそれぞれの項目は、その後続の項目より厳密に下にある。`adequate-above` が産出する厳密な所属によるものである。
<!--/-->

```agda
  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .fst
```

<!--en-->
Since `ch n ∈ ch (suc n)`, the inward map for the union shows `ch n ∈ λ`. Thus every adequate index in the sequence is itself available as a member of the final ordinal index `λ`.
<!--zh-->
由 `ch n ∈ ch (suc n)`，并的向内映射给出 `ch n ∈ λ`。因此序列中的每个充分指标本身都是最终序数指标 `λ` 的成员。
<!--ja-->
`ch n ∈ ch (suc n)` なので、合併の内向きの写像から `ch n ∈ λ` が得られる。したがって、列にある各十分な添字自身が最終的な順序数添字 `λ` の要素として利用できる。
<!--/-->

```agda
    ch∈λ : (n : ℕ) → ⟨ ch n .fst ∈ lam ⟩
    ch∈λ n = U.into (suc n) (ch n .fst) (up n)
```

<!--en-->
The zeroth adequate index strictly contains `α`, and it is one of the sets forming the union. Consequently `α ∈ λ`.
<!--zh-->
第零个充分指标严格包含 `α`，而它又是构成该并的集合之一。因此 `α ∈ λ`。
<!--ja-->
第零の十分な添字は `α` を厳密に含み、しかも合併を構成する集合の一つである。したがって `α ∈ λ` が従う。
<!--/-->

```agda
  α∈λ : ⟨ α ∈ lam ⟩
  α∈λ = U.into zero α (adequate-above α oα .snd .snd .fst)
```

<!--en-->
Given `x ∈ λ`, the outward map supplies only the propositionally truncated existence of an `n` with `x ∈ ch n`. In each branch, adequacy of that entry gives `sucV x ∈ ch n`, and the inward map yields `sucV x ∈ λ`. Since the target is a membership proposition, the result may be eliminated from the truncation without retaining `n`.
<!--zh-->
给定 `x ∈ λ`，向外映射只给出命题截断的存在性：某个 `n` 满足 `x ∈ ch n`。在每个分支中，该项的充分性给出 `sucV x ∈ ch n`，向内映射继而给出 `sucV x ∈ λ`。目标是一个隶属命题，所以可以从命题截断中消去结果，而不保留 `n`。
<!--ja-->
`x ∈ λ` が与えられると、外向きの写像が与えるのは `x ∈ ch n` を満たす `n` の命題的に切り詰められた存在だけである。各分岐では、その項の妥当性から `sucV x ∈ ch n` が得られ、内向きの写像が `sucV x ∈ λ` を与える。目標は所属命題なので、`n` を保持せずに結果を命題的切り詰めから除去できる。
<!--/-->

```agda
  succ : (x : V ℓ) → ⟨ x ∈ lam ⟩ → ⟨ sucV x ∈ lam ⟩
  succ x x∈ = rec₁ (snd (sucV x ∈ lam))
    (λ { (n , x∈n) → U.into n (sucV x) (Adequate.succ (ch n .fst) (ch n .snd .snd) x x∈n) })
    (U.outof x x∈)
```

<!--en-->
The zeroth entry is adequate and therefore contains `ω`. The inward union map carries this fact to the membership `ω ∈ λ` required by `Adequate λ`.
<!--zh-->
第零项是充分的，因而包含 `ω`。并的向内映射把这一事实送为 `Adequate λ` 所要求的成员关系 `ω ∈ λ`。
<!--ja-->
第零項は十分なので `ω` を含む。合併の内向きの写像がこの事実を、`Adequate λ` に必要な所属 `ω ∈ λ` へ送る。
<!--/-->

```agda
  ω∈λ : ⟨ ω ∈ lam ⟩
  ω∈λ = U.into zero ω (Adequate.ω∈ (ch zero .fst) (ch zero .snd .snd))
```

<!--en-->
For `c ∈ λ`, the outward map gives the propositionally truncated existence of an `n` with `c ∈ ch n`. In each branch, adequacy of `ch n` supplies the four witnesses in `Lset (ch n)`, and `ch n ∈ λ` lets monotonicity move them into `Lset λ`. Elimination from the truncation is valid because `Witnesses (Lset λ) c` is a proposition.
<!--zh-->
对 `c ∈ λ`，向外映射只给出命题截断的存在性：某个 `n` 满足 `c ∈ ch n`。在每个分支中，`ch n` 的充分性在 `Lset (ch n)` 中提供四个见证，而 `ch n ∈ λ` 允许通过单调性把它们搬入 `Lset λ`。由于 `Witnesses (Lset λ) c` 是命题，可以合法地从命题截断中消去。
<!--ja-->
`c ∈ λ` に対し、外向きの写像が与えるのは `c ∈ ch n` を満たす `n` の命題的に切り詰められた存在だけである。各分岐では、`ch n` の妥当性が四つの証人を `Lset (ch n)` に与え、`ch n ∈ λ` に沿う単調性がそれらを `Lset λ` へ運ぶ。`Witnesses (Lset λ) c` は命題なので、命題的切り詰めから正当に除去できる。
<!--/-->

```agda
  wit : (c : V ℓ) → ⟨ c ∈ lam ⟩ → Witnesses (Lset lam) c
  wit c c∈ = rec₁ (isPropWitnesses (Lset lam) c)
    (λ { (n , c∈n) → λ oc →
      let w = Adequate.wit (ch n .fst) (ch n .snd .snd) c c∈n oc
      in  Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .fst)
```

<!--en-->
Each component is transported by monotonicity of the constructible levels along `ch n ∈ λ`: the hierarchy table, code set, satisfaction graph and environment tower all pass from `Lset (ch n)` to `Lset λ`.
<!--zh-->
四个分量都沿 `ch n ∈ λ`，由可构造层的单调性分别搬运：层级表、码集合、满足关系图与环境塔全都从 `Lset (ch n)` 进入 `Lset λ`。
<!--ja-->
各成分は `ch n ∈ λ` に沿う構成可能段階の単調性によって運ばれる。階層表、コード集合、充足関係のグラフ、環境の塔はいずれも `Lset (ch n)` から `Lset λ` へ移る。
<!--/-->

```agda
        , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .fst)
          , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .fst)
            , Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .snd) )) })
    (U.outof c c∈)
```

<!--en-->
Ordinality of the union, successor closure, `ω ∈ λ`, and the transported witnesses together prove `Adequate λ`. The first three facts concern the ordinal index `λ`; the fourth places sets in the constructible stage `Lset λ`. These are closure facts used by the later hierarchy description, rather than a model-theoretic assertion about `Lset λ`.
<!--zh-->
并的序数性、后继封闭、`ω ∈ λ` 与搬运后的见证合在一起，便得到 `Adequate λ`。前三项谈的是序数指标 `λ`，第四项则把集合放入可构造层 `Lset λ`。这些是后续层级描述所需的闭合事实，并非关于 `Lset λ` 的模型论断言。
<!--ja-->
合併の順序数性、後者閉包、`ω ∈ λ`、そして輸送した証人を組み合わせると `Adequate λ` が得られる。最初の三項は順序数添字 `λ` に関する事実であり、第四項は集合を構成可能段階 `Lset λ` に入れる。これらは後の階層記述が使う閉包の事実であり、`Lset λ` に関するモデル理論的な主張ではない。
<!--/-->

```agda
  adequate : Adequate lam
  adequate = olam , ( succ , ( ω∈λ , wit ))
```

<!--en-->
For `d ∈ λ`, the outward map gives only the propositionally truncated existence of an `n` with `d ∈ ch n`. Mapping within that truncation uses `γ = ch n`: this index belongs to `λ`, contains `d`, and is adequate. The result remains truncated, so it defines no choice function `d ↦ γ`.
<!--zh-->
对 `d ∈ λ`，向外映射只给出命题截断的存在性：某个 `n` 满足 `d ∈ ch n`。在该截断内作映射并令 `γ = ch n`；这个指标属于 `λ`，包含 `d`，而且充分。结果仍在截断下，因此并未定义选择函数 `d ↦ γ`。
<!--ja-->
`d ∈ λ` に対し、外向きの写像が与えるのは `d ∈ ch n` を満たす `n` の命題的に切り詰められた存在だけである。その切り詰めの内部で `γ = ch n` と置けば、この添字は `λ` に属し、`d` を含み、十分である。結果は切り詰められたままなので、選択関数 `d ↦ γ` は定義されない。
<!--/-->

```agda
  super : Superadequate lam
  super d d∈ = map₁
    (λ { (n , d∈n) → ch n .fst , ( ch∈λ n , ( d∈n , ch n .snd .snd )) })
    (U.outof d d∈)
```
</div>
</details>

<!--en-->
The exported theorem returns an explicit ordinal index `λ` above `α`, together with proofs of `Adequate λ` and `Superadequate λ`. Although `λ` itself is available as data, the local adequate indices promised for its members remain under propositional truncation; no least local index or global family of choices is produced.
<!--zh-->
导出的定理显式返回严格位于 `α` 之上的序数指标 `λ`，并附带 `Adequate λ` 与 `Superadequate λ` 的证明。虽然 `λ` 本身是可用的数据，但为其各成员保证的局部充分指标仍处于命题截断下；构造没有给出最小局部指标，也没有给出全局选择族。
<!--ja-->
公開される定理は、`α` を厳密に含む順序数添字 `λ` を明示的に返し、`Adequate λ` と `Superadequate λ` の証明を添える。`λ` 自身はデータとして使えるが、その各要素に保証される局所的な十分な添字は命題的切り詰めのもとにある。最小の局所添字も大域的な選択族も得られない。
<!--/-->

```agda
superadequate-above : (α : V ℓ) → IsOrd α
                    → Σ[ lam ∈ V ℓ ] (IsOrd lam × ⟨ α ∈ lam ⟩ × Adequate lam × Superadequate lam)
superadequate-above α oα =
  Super.lam α oα , ( Super.olam α oα , ( Super.α∈λ α oα , ( Super.adequate α oα , Super.super α oα )))
```

<!--en-->
## A stage belongs to its successor stage
<!--zh-->
## 一层属于其后继层
<!--ja-->
## 段階はその後者段階に属する
<!--/-->

<!--en-->
For every ambient set `β`, the whole set `Lset β` is an element of `Lset (sucV β)`; no ordinality hypothesis on `β` is needed. The equation `Lset (sucV β) = 𝒟ₒ (Lset β)` reduces the claim to definability over `Lset β`, and the constant-true formula defines the whole carrier as a subset of itself. The conclusion is membership of the set `Lset β` in the next constructible stage, a different statement from pointwise inclusion of one stage in another.
<!--zh-->
对每个外围集合 `β`，整个集合 `Lset β` 都是 `Lset (sucV β)` 的元素；这里不需要假设 `β` 是序数。等式 `Lset (sucV β) = 𝒟ₒ (Lset β)` 把目标化为 `Lset β` 上的可定义性，而恒真公式恰把整个载体定义为其自身的一个子集。结论是集合 `Lset β` 属于下一可构造层，这与一个层逐点包含于另一个层是不同的陈述。
<!--ja-->
周囲の任意の集合 `β` について、集合 `Lset β` 全体は `Lset (sucV β)` の要素であり、`β` が順序数であるという仮定は要らない。等式 `Lset (sucV β) = 𝒟ₒ (Lset β)` により、主張は `Lset β` 上での定義可能性に帰着し、恒真な論理式が台全体をそれ自身の部分集合として定義する。結論は集合 `Lset β` が次の構成可能段階に属することであり、一つの段階が別の段階に要素ごとに含まれることとは異なる主張である。
<!--/-->

```agda
Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)
```
