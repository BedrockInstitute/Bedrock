<!--en-->
# The counting tools for infinite constructible stages

Counting the stage `Lset δ` of an infinite ordinal `δ` inside `L` rests on two ingredients: a base injection `Lω ↪ ω`, and a way of lifting injections through finite environments. This chapter supplies both, and everything here is proved for exactly the constructs named in the text.
<!--zh-->
# 计数无穷可构造层的工具

在 `L` 内部计数无穷序数 `δ` 的层 `Lset δ`，依赖两件材料：基础单射 `Lω ↪ ω`，以及把单射逐项提升到有限环境的手段。本章给出这两者；本章所证的一切，都恰针对文中点名的构造。
<!--ja-->
# 無限な構成可能段階を数える道具

無限順序数 `δ` の段階 `Lset δ` を `L` の内部で数えるには、二つの材料が要る。基底の単射 `Lω ↪ ω` と、単射を有限環境へ持ち上げる方法である。この章はその両方を供給する。ここで証明されることは、すべて本文で名指しされた構成についてのものである。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The chapter works under excluded middle at the fixed universe level. This hypothesis is inherited by the constructions used throughout; its clearest local roles are to search a finite-stage tally for a name and to compare a collapse value with `ω` by ordinal trichotomy.
<!--zh-->
本章在固定宇宙层级的排中律下工作。全章调用的构造都继承这一假设；它在本章中最清楚的两项作用，是在有穷层的点名册中搜索一个名称，以及用序数三歧比较塌缩值与 `ω`。
<!--ja-->
本章では、固定した宇宙レベルにおける排中律を仮定する。この仮定は章全体で用いる構成に受け継がれる。本章内でとくに明瞭な役割は、有限段階の一覧から名前を探索することと、順序数の三分律によって崩壊値を `ω` と比較することである。
<!--/-->

```agda
open import Base.Prelude
open import Cubical.HITs.PropositionalTruncation using ( rec2 )
open import Cubical.Foundations.HLevels using ( isPropΠ2; isPropΠ3 )
open import Cubical.Data.FinData using ( inj-toℕ )
open import Base.Classical using ( LEM )

```

<!--en-->
All constructions therefore share the single hypothesis `lem : LEM (ℓ-suc ℓ)`. In particular, the finite search below is a consequence of excluded middle and does not invoke a choice principle.
<!--zh-->
因此，所有构造共享唯一的假设 `lem : LEM (ℓ-suc ℓ)`。特别地，下文的有限搜索由排中律推出，并不调用选择公理。
<!--ja-->
したがって、すべての構成はただ一つの仮定 `lem : LEM (ℓ-suc ℓ)` を共有する。とくに、後の有限探索は排中律から得られるものであり、選択原理を用いるものではない。
<!--/-->

```agda
module L.GCH.StageCountingTools {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The internal graphs used below must be described by formulas that `L` itself can interpret. Equality, membership, conjunction, implication, and bounded and unbounded quantifiers provide the language for saying that a relation is a total single-valued injection and for defining its action on finite environments.
<!--zh-->
下文使用的内部图必须由 `L` 自身能够解释的公式描述。相等、隶属、合取、蕴涵以及有界和无界量词，共同提供了表达「一个关系是全域单值单射」并定义它在有限环境上作用的语言。
<!--ja-->
以下で使う内部グラフは、`L` 自身が解釈できる論理式で記述する必要がある。等号、所属、連言、含意、有界量化子と非有界量化子によって、関係が全域的で一価な単射であることと、その有限環境への作用を表す。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
There are two levels of data throughout the argument. A set in the cumulative hierarchy has a small presentation whose indices name its members, while an element of `L` also carries a proof of constructibility. Moving between these levels lets an internal graph act as an ordinary function on presentation indices.
<!--zh-->
整个论证始终涉及两层数据。累积层级中的集合带有小呈现，其索引为成员命名；`L` 的元素还携带可构造性证明。在这两层之间往返，便可让内部图作为普通函数作用于呈现索引。
<!--ja-->
議論では一貫して二つの水準のデータを扱う。累積階層の集合には、その要素を名指す小さな提示があり、`L` の要素には構成可能性の証明も添えられている。この二つの水準を行き来することで、内部グラフを提示のインデックス上の通常の関数として働かせられる。
<!--/-->

```agda
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL )
```

<!--en-->
Ordinal structure enters twice. Numerals identify the finite domains of environments, while the order on constructible stages later gives a canonical well order of `Lset ω`. Trichotomy will then decide how each value of its ordinal collapse sits relative to `ω`.
<!--zh-->
序数结构在两处进入论证。数码标识环境的有限定义域，而可构造层上的序稍后给出 `Lset ω` 的典范良序。随后，三分法判断序数塌缩的每个值相对于 `ω` 所处的位置。
<!--ja-->
順序数の構造は二度使われる。数項は環境の有限な定義域を識別し、構成可能段階の順序は後で `Lset ω` の標準的な整列順序を与える。その後、三岐性によって順序数崩壊の各値が `ω` に対してどこに位置するかを判定する。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( ∈#-elim; mem-ord; ω-ord; numeral-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
```

<!--en-->
A coded injection is represented by a set of ordered pairs. Its four obligations say that the graph is single-valued, has exactly the stated domain, is injective on inputs, and takes values in the stated target. The first part of the chapter starts from such an actual coded graph.
<!--zh-->
编码单射由一个有序对集合表示。它的四项义务分别断言：图是单值的、定义域恰为指定集合、在输入上单射，并且取值落在指定目标中。本章第一部分从这样一个实际给定的编码图出发。
<!--ja-->
符号化された単射は順序対の集合で表される。その四つの条件は、グラフが一価であること、定義域が指定された集合とちょうど一致すること、入力について単射であること、値が指定された目標に属すことである。章の前半では、このように実際に与えられた符号化グラフから出発する。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro; appAt; appAt-adequate; envOverAt; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( numL )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-in; injAt-out; module Small )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
```

<!--en-->
For each natural number `n`, the set of environments over `A` of length `n` has a concrete presentation. The union `seqL A` ranges over every finite length. Thus an entrywise map that preserves length is exactly the operation needed to map all finite sequences over `A` into those over `B`.
<!--zh-->
对每个自然数 `n`，取值于 `A` 的长度 `n` 环境都有具体呈现。集合 `seqL A` 汇集所有有限长度。因此，一个逐项作用并保持长度的映射，正是把 `A` 上所有有限序列送入 `B` 上有限序列所需的操作。
<!--ja-->
各自然数 `n` について、`A` に値を取る長さ `n` の環境には具体的な提示がある。集合 `seqL A` はすべての有限な長さをまとめたものである。したがって、成分ごとに作用して長さを保つ写像こそ、`A` 上のすべての有限列を `B` 上の有限列へ送るために必要な操作である。
<!--/-->

```agda
open import L.Coding.EnvironmentSet {ℓ} lem
  using ( Ix; envS; envSet-in; envSet-out; envOver; module Recover )
open import L.Choice.NameComparison {ℓ} lem using ( domAt-numeral; domAt-fill )
open import L.Choice.StageOrders {ℓ} lem
  using ( carry; memOf; orderAt; orderAt-step; relOf
```

<!--en-->
The second part orders the members of `Lset ω` first by birth stage and then, when birth stages agree, by the local step order. This distinction matters: a predecessor may have the same birth stage as its successor, although every predecessor still lies in the successor of that common stage.
<!--zh-->
第二部分先按诞生层排列 `Lset ω` 的成员；诞生层相同时，再按该层上的步进序排列。这一区分不可忽略：一个前驱可以与其后继具有相同诞生层，但每个前驱仍落在该共同层的后继层中。
<!--ja-->
後半では、`Lset ω` の要素をまず誕生段階で並べ、誕生段階が等しいときにはその段階の局所的な順序で並べる。この区別は欠かせない。前者が後者の前者であっても誕生段階が同じ場合があるが、それでも各前者はその共通段階の後続段階に属する。
<!--/-->

```agda
        ; birth-mem; module Family )
  renaming ( Mem to MemOf )
open import L.Choice.OrderTable {ℓ} lem using ( Related; IsRel; ixRel-rep; ixRel-fill )
open import L.Choice.InternalWellOrder {ℓ} lem using ( relL; relL-spec )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
```

<!--en-->
Collapsing this well order assigns an ordinal to each member of `Lset ω`. The task is then to prove that every collapse value belongs to `ω`. The proof will bound one predecessor segment at a time by a finite constructible stage and rule out an injection of `ω` into that stage.
<!--zh-->
塌缩这一良序，会为 `Lset ω` 的每个成员赋予一个序数。接下来的任务是证明每个塌缩值都属于 `ω`。证明逐个处理前驱段，把它界定在某个有限可构造层内，并排除从 `ω` 到该层的单射。
<!--ja-->
この整列順序を崩壊させると、`Lset ω` の各要素に順序数が割り当てられる。次の課題は、すべての崩壊値が `ω` に属すことを示すことである。証明では前者切片を一つずつ有限な構成可能段階で抑え、`ω` からその段階への単射を排除する。
<!--/-->

```agda
  using ( SWO; lt; eq; gt ) renaming ( Tri to TriW )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
```

<!--en-->
Finite-sequence coding and the collapse argument meet in later cardinal calculations. The former transports an already given coded injection coordinatewise; the latter provides the base result `Lset ω ↪ ω`. Neither statement asserts a bijection or counts arbitrary infinite sequences.
<!--zh-->
有限序列编码与塌缩论证会在后续基数计算中汇合。前者把一个已给定的编码单射逐坐标搬运，后者给出基础结论 `Lset ω ↪ ω`。两条陈述都不主张双射，也不计数任意无穷序列。
<!--ja-->
有限列の符号化と崩壊の議論は、後の基数計算で合流する。前者はすでに与えられた符号化単射を成分ごとに移し、後者は基礎となる結論 `Lset ω ↪ ω` を与える。どちらも全単射を主張せず、任意の無限列を数えるものでもない。
<!--/-->

```agda
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( isL-ord )
open import L.GCH.FiniteSequenceCoding {ℓ} lem using ( seqL; seqL-in; seqL-out )
open import L.Ordinal.SquareLaw {ℓ} lem using ( module FiniteBase )
open FiniteBase using ( fromFin; fromFin-inj )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate; ω-limit; finite-excl-ω )
```

<!--en-->
A finite stage comes with a finite tally that lists all its members. Repetitions may occur, so the tally is a surjective naming device rather than a bijection. This is enough: excluded middle permits a bounded search for one name of each given member.
<!--zh-->
每个有限层都带有列出其全部成员的有限名册。名册中可以出现重复，因此它只是满射式的命名手段，并非双射。这已经足够：排中律允许通过有界搜索，为每个给定成员找到一个名字。
<!--ja-->
有限段階には、その全要素を列挙する有限な名簿がある。重複していてもよいので、この名簿は全単射ではなく、全射的に名前を与えるものである。それで十分である。排中律を使った有界探索により、与えられた各要素の名前を一つ見つけられる。
<!--/-->

```agda
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( Tally; StageOrder; stageOrder; finiteStage )  -- lint-agda: keep (StageOrder used as the projection qualifier)
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )

```

<!--en-->
The chosen tally index places each member of a finite stage in a finite ordinal presentation. Composing a hypothetical injection from `ω` with this naming map, and then duplicating the result on the diagonal, contradicts the finite square exclusion theorem.
<!--zh-->
所找出的名册索引把有限层的每个成员送入一个有限序数呈现。若假设存在从 `ω` 出发的单射，把它与这一命名映射复合，再沿对角线复制所得值，就会与有限平方排除定理矛盾。
<!--ja-->
見つけた名簿のインデックスによって、有限段階の各要素を有限順序数の提示へ送れる。`ω` からの単射があると仮定してこの命名写像と合成し、得られた値を対角線上で二重にすると、有限平方の排除定理に反する。
<!--/-->

```agda
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.FinData.FinSet using ( DecΣ )
open import Cubical.Relation.Nullary using ( decRec )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId'; inj-toℕ )
```

<!--en-->
Several later equalities concern dependent pairs whose second components are proofs. Since those components are propositions, equality of the underlying sets determines equality of the packaged elements. This allows the argument to move cleanly between elements of `L`, their presentations, and their graph codes.
<!--zh-->
后文有若干等式涉及第二分量为证明的依赖对。由于这些分量都是命题，底层集合的相等便决定打包元素的相等。由此，论证可以在 `L` 的元素、它们的呈现与图编码之间顺畅往返。
<!--ja-->
後で現れるいくつかの等しさは、第二成分が証明である依存対についてのものである。その成分は命題なので、底の集合の等しさから包装された要素の等しさが決まる。これにより、`L` の要素、その提示、グラフの符号の間を円滑に行き来できる。
<!--/-->

```agda
```

<!--en-->
Numerals have a second role besides marking environment lengths. Membership in `ω` says merely that an ambient set is equal to some numeral, while the proof keeps no globally chosen natural-number representative. Later eliminations respect this propositional character.
<!--zh-->
数码除标记环境长度外还有第二项作用。一个外围集合属于 `ω`，只表示它等于某个数码，并不保留一个全局选定的自然数表示。后文的消去始终遵守这一命题性。
<!--ja-->
数項には、環境の長さを示す以外にも役割がある。周囲の集合が `ω` に属すという主張は、それが何らかの数項に等しいことだけを述べ、自然数による大域的に選ばれた表示を保持しない。後の消去もこの命題性を守る。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
```

<!--en-->
Existence in membership and graph readings is often retained only under propositional truncation `∥_∥₁`. Such a witness may be eliminated when the target is a proposition, or when uniqueness first makes the target type a proposition; the operation does not select arbitrary representatives.
<!--zh-->
隶属关系与图的读法中的存在性，往往只保留在命题截断 `∥_∥₁` 之下。只有当目标是命题，或先由唯一性使目标类型成为命题时，才能消去这样的见证；这一操作不会任意选取代表。
<!--ja-->
所属やグラフの読みで現れる存在は、しばしば命題的切り詰め `∥_∥₁` の下にだけ保たれる。この証人を消去できるのは、行き先が命題である場合、または一意性によって行き先の型をまず命題にした場合である。この操作は任意の代表を選ぶものではない。
<!--/-->

```agda
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )

```

<!--en-->
The same distinction applies to the final count. `InjL A B` retains only the proposition that some constructible graph codes an injection from `A` to `B`; it does not expose a globally selected host-level function.
<!--zh-->
同一区分也适用于最终的计数结论。`InjL A B` 只保留「存在某个可构造图编码从 `A` 到 `B` 的单射」这一命题，并不公开一个全局选定的宿主层函数。
<!--ja-->
同じ区別は最後の数え上げにも当てはまる。`InjL A B` が保持するのは、`A` から `B` への単射を符号化する構成可能グラフが存在するという命題だけであり、大域的に選ばれた台の水準の関数を公開しない。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
By contrast, the sequence construction begins with a particular graph `E` and the full data `InjCode E A B`. Its host-level function can therefore be read from that graph and used coordinatewise before the resulting graph is hidden again by `InjL`.
<!--zh-->
与此相对，序列构造从一个特定的图 `E` 及完整数据 `InjCode E A B` 出发。因此，可以从该图读出宿主层函数并逐坐标使用，最后再由 `InjL` 隐去所得图。
<!--ja-->
これに対して、列の構成は特定のグラフ `E` と完全なデータ `InjCode E A B` から始まる。したがって、そのグラフから台の水準の関数を読み取り、成分ごとに用いた後、得られたグラフを `InjL` によって再び隠せる。
<!--/-->

```agda
module SV = hPropStructure 𝒮ᵥ using ()
```

<!--en-->
Every entry read from a member of a constructible set is itself constructible, by transitivity of `L`. This elementary fact is what permits finite environments and the ordered pairs in their graphs to remain objects of the internal model.
<!--zh-->
从可构造集合的成员中读出的每个条目，本身也因 `L` 的传递性而可构造。正是这一基本事实，使有限环境及其图中的有序对仍然是内部模型的对象。
<!--ja-->
構成可能集合の要素から読み取った各項目は、`L` の推移性によってそれ自身も構成可能である。この基本的な事実により、有限環境とそのグラフに現れる順序対を内部モデルの対象として扱える。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

```

<!--en-->
Satisfaction notation connects the formula-level description of a graph with these ambient membership facts. Adequacy lemmas will be used in both directions, so the proof can build an internal formula from concrete graph data and later read that formula back.
<!--zh-->
满足记号把公式层的图描述与这些外围隶属事实连接起来。充分性引理将在两个方向上使用，因此证明既能由具体图数据填充内部公式，也能随后从该公式读回这些数据。
<!--ja-->
充足の記法は、論理式の水準でのグラフの記述を、これらの周囲の所属の事実と結び付ける。妥当性補題を両方向に用いることで、具体的なグラフのデータから内部論理式を満たし、後でその論理式からデータを読み戻せる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
For a natural number `k`, `nn k` packages the numeral `# k` with its proof of constructibility. These packaged numerals serve as the finite domain objects in satisfaction environments.
<!--zh-->
对自然数 `k`，`nn k` 把数码 `# k` 与其可构造性证明打包。满足关系的环境用这些打包数码表示有限定义域。
<!--ja-->
自然数 `k` に対し、`nn k` は数項 `# k` とその構成可能性の証明を組にする。この包装された数項を、充足の環境における有限な定義域の対象として用いる。
<!--/-->

```agda
nn : ℕ → S
nn k = # k , numL k

```

<!--en-->
The graph formula below introduces several nested binders. Names `i0`, `i1`, and so on abbreviate their de Bruijn positions, with `i0` always denoting the most recently bound variable.
<!--zh-->
下文的图公式会引入多层嵌套约束。名字 `i0`、`i1` 等缩写相应的 De Bruijn 位置，其中 `i0` 总是表示最近约束的变元。
<!--ja-->
後のグラフ論理式では、束縛子が何重にも入れ子になる。`i0`、`i1` などの名前は対応する De Bruijn 位置の略記であり、`i0` は常に最も新しく束縛された変数を表す。
<!--/-->

```agda
private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
```

<!--en-->
As binders are added, older variables shift to the next position. The typed abbreviations record those shifts once, so the formula can display its mathematical pattern without repeating long successor expressions.
<!--zh-->
每增加一层约束，原有变元便向后移动一个位置。这些带类型的缩写统一记录这种移动，使公式能够显出数学结构，而无须反复写出冗长的后继表达式。
<!--ja-->
束縛子が一つ加わるたびに、それまでの変数は一つ後の位置へ移る。型の付いた略記がその移動をまとめて記録するので、長い後続式を繰り返さずに論理式の数学的な形を示せる。
<!--/-->

```agda
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
```

<!--en-->
The positions through `i6` will suffice to relate an input environment `s`, its image `y`, a common domain `n`, an index `i`, and the two entries connected by `E`.
<!--zh-->
直到 `i6` 的位置，足以同时指向输入环境 `s`、其像 `y`、公共定义域 `n`、索引 `i`，以及由 `E` 联系的两个条目。
<!--ja-->
`i6` までの位置があれば、入力環境 `s`、その像 `y`、共通の定義域 `n`、インデックス `i`、そして `E` で結ばれる二つの項目を同時に参照できる。
<!--/-->

```agda
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5
```

<!--en-->
Later formulas for coded injections require a few deeper positions. Extending the same naming scheme avoids changing the convention when those additional binders are introduced.
<!--zh-->
后文表达编码单射的公式还需要几个更深的位置。沿用同一命名方式，便无需在引入额外约束时改变记号约定。
<!--ja-->
後で符号化された単射を表す論理式では、さらに深い位置もいくつか必要になる。同じ命名法を延長しておけば、追加の束縛子を導入しても記法の約束を変えずに済む。
<!--/-->

```agda
  i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
  i7 = suc i6
  i8 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))
  i8 = suc i7
  i9 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))
```

<!--en-->
The last abbreviation completes the range needed in this module. These names carry no mathematical assumptions; they only keep the variable bookkeeping legible.
<!--zh-->
最后一个缩写补齐本模块所需的位置范围。这些名字不携带任何数学假设，只用于让变元位置的记录清晰可读。
<!--ja-->
最後の略記で、このモジュールに必要な位置がすべてそろう。これらの名前は数学的な仮定を何も加えず、変数位置の管理を読みやすくするだけである。
<!--/-->

```agda
  i9 = suc i8
```

<!--en-->
## Length and extensionality of environments
<!--zh-->
## 环境的长度与外延性
<!--ja-->
## 環境の長さと外延性
<!--/-->

<!--en-->
The first rigidity fact compares the lengths of two coded environments. If one underlying set equals both environments `env h` and `env h'`, with every entry constructible, then the two lengths are equal: the domain of a coded environment is its length numeral, and the two readings of the same set are identified by the numeral projections.
<!--zh-->
第一条刚性事实比较两个编码环境的长度。若同一个底层集合同时等于 `env h` 与 `env h'`，且两列每项都可构造，则两个长度相等：编码环境的定义域就是其长度数码，而对同一集合的两次读取由数码投影认同。
<!--ja-->
最初の剛性の事実は、二つの符号化された環境の長さを比較する。一つの底の集合が `env h` とも `env h'` とも等しく、各項目が構成可能なら、二つの長さは等しくなる。符号化された環境の定義域はその長さの数項であり、同じ集合の二つの読みが数項の射影で同一視されるのである。
<!--/-->

```agda
env-len : (E : S) {n n' : ℕ} (h : Fin n → V ℓ) (h' : Fin n' → V ℓ)
        → ((i : Fin n) → ⟨ isL (h i) ⟩) → ((i : Fin n') → ⟨ isL (h' i) ⟩)
        → fst E ≡ env h → fst E ≡ env h' → n ≡ n'
env-len E {n} {n'} h h' cg cg' q q' =
  #-inj′ (domAt-numeral (suc zero) zero (nn n ∷ E ∷ []) n' h' cg' q'
```

<!--en-->
The proof fills the domain of the first presentation with the numeral of `n`, reads the same domain back as the numeral of `n'`, and applies the injectivity of numerals. The conclusion is only the equality of lengths, not an equality of the two presenting functions.
<!--zh-->
证明先用 `n` 的数码填充第一种呈现的定义域，再把同一定义域读回为 `n'` 的数码，最后应用数码单射性。结论只是长度相等，而非两个呈现函数的相等。
<!--ja-->
証明は、最初の提示の定義域を `n` の数項で埋め、同じ定義域を `n'` の数項として読み戻し、数項の単射性を適用する。結論は長さの等式だけであり、二つの提示の関数の等式ではない。
<!--/-->

```agda
            (domAt-fill (suc zero) zero (nn n ∷ E ∷ []) n h cg q refl))

```

<!--en-->
The second rigidity fact assumes that two columns already have the same length and their coded graphs are equal. Looking up the numeral key for an index in both graphs then recovers equality of the corresponding entries. The converse, constructing equality of graphs from pointwise equality, is proved later at the place where it is needed.
<!--zh-->
第二条刚性事实假设两列已有相同长度，且其编码图相等。分别在两个图中查找某个索引的数码键，便得到对应条目的相等。反方向，即由逐点相等构造图的相等，将在后文实际需要之处证明。
<!--ja-->
二つ目の剛性の事実では、二つの列の長さがすでに同じで、符号化されたグラフも等しいと仮定する。両方のグラフでインデックスに対応する数項のキーを参照すると、対応する項目の等しさが得られる。逆向き、すなわち各点の等しさからグラフの等しさを作る方向は、後で必要になる箇所で証明する。
<!--/-->

```agda
env-pt : {n : ℕ} (h h' : Fin n → V ℓ) → env h ≡ env h' → (i : Fin n) → h i ≡ h' i
env-pt h h' q i = subst ⟨_⟩ (lookup-spec h' i (h i))
  (subst (λ w → ⟨ pr (# (toℕ i)) (h i) ∈ w ⟩) q
    (subst ⟨_⟩ (sym (lookup-spec h i (h i))) refl))
```

<!--en-->
## Lifting a coded injection to finite sequences
<!--zh-->
## 把编码单射提升到有限序列
<!--ja-->
## 符号化された単射を有限列へ持ち上げる
<!--/-->

<!--en-->
The lifting module is stated for a constructible graph `E` with four data: single-valuedness, totality on `A`, injectivity on `A`, and values in `B`. These are exactly the four clauses of a coded injection from `A` into `B`.
<!--zh-->
提升模块以四条数据对可构造图 `E` 陈述：单值性、在 `A` 上的全域性、在 `A` 上的单射性、值落在 `B`。这恰是从 `A` 到 `B` 的编码单射的四条条款。
<!--ja-->
持ち上げのモジュールは、構成可能なグラフ `E` に対して四つのデータとともに述べられる。一価性、`A` の上の全域性、`A` の上の単射性、そして `B` の中の値である。これらはちょうど、`A` から `B` への符号化された単射の四つの条項である。
<!--/-->

```agda
module SeqMap (A B E : S)
              (sv : ⟨ (E ∷ A ∷ []) ⊨ svAt zero ⟩)
              (dm : ⟨ (E ∷ A ∷ []) ⊨ domAt zero (suc zero) ⟩)
              (ij : ⟨ (E ∷ A ∷ []) ⊨ injAt zero ⟩)
              (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst E ⟩
```

<!--en-->
The final range clause says only that every value occurring in `E` belongs to `B`. It does not require every member of `B` to occur, so the data describe an injection rather than a surjection or a bijection.
<!--zh-->
最后的值域条款只要求 `E` 中出现的每个值都属于 `B`。它不要求 `B` 的每个成员都被命中，因此这些数据描述的是单射，而非满射或双射。
<!--ja-->
最後の値域条件が述べるのは、`E` に現れるすべての値が `B` に属すことだけである。`B` の各要素が像になることは要求しないので、このデータが表すのは単射であり、全射や全単射ではない。
<!--/-->

```agda
                   → ⟨ fst y ∈ fst B ⟩) where

```

<!--en-->
The extraction machinery reads the internal graph as an actual function between the presentations of `A` and `B`: single-valuedness makes the fiber of each value a proposition, so the value can be recovered without any choice principle.
<!--zh-->
提取机制把内部图读作 `A` 与 `B` 的呈现之间的实际函数：单值性使每个值的纤维成为命题，因此无需任何选择原理即可恢复该值。
<!--ja-->
抽出の仕組みは、内部のグラフを、`A` と `B` の提示の間の実際の関数として読む。一価性により各値の繊維は命題になるので、選択の原理なしに値を復元できる。
<!--/-->

```agda
  module Sm = Small E A B sv dm ij ran using ( at; fib; small; small-inj; module E )
```

<!--en-->
The extracted function is kept opaque: later arguments use it through its graph and its injectivity.
<!--zh-->
提取出的函数保持不透明：后文只通过其图与单射性使用它。
<!--ja-->
抽出された関数は不透明に保たれる。後の議論は、そのグラフと単射性を通してだけそれを使う。
<!--/-->

```agda
  opaque
    f : ⟪ fst A ⟫ → ⟪ fst B ⟫
    f = Sm.small

```

<!--en-->
The graph record states that the pair of an index's presented element and the presented image belongs to `E`; it is transported from the term algebra's own graph record along the identification of the presented value.
<!--zh-->
图记录陈述：索引的呈现元素与被呈现像构成的有序对属于 `E`；它由项代数自身的图记录、沿被呈现值的同一视搬运而来。
<!--ja-->
グラフの記録は、索引の提示された要素と提示された像の順序対が `E` に属することを述べる。これは、項代数自身のグラフの記録から、提示された値の同一視に沿って運ばれる。
<!--/-->

```agda
    f-graph : (m : ⟪ fst A ⟫)
            → ⟨ pr (⟪ fst A ⟫↪ m) (⟪ fst B ⟫↪ (f m)) ∈ fst E ⟩
    f-graph m = subst (λ w → ⟨ pr (⟪ fst A ⟫↪ m) w ∈ fst E ⟩)
      (sym (Sm.fib m .snd)) (Sm.E.toFun-graph (Sm.at m))

```

<!--en-->
The extracted function is injective on the presentation of `A`, which is the pointwise injectivity that the sequence lifting will inherit.
<!--zh-->
提取出的函数在 `A` 的呈现上单射；这正是序列提升将要逐坐标继承的逐点单射性。
<!--ja-->
抽出された関数は `A` の提示の上で単射である。これが、列の持ち上げが成分ごとに受け継ぐ、各点の単射性である。
<!--/-->

```agda
    f-inj : (m n : ⟪ fst A ⟫) → f m ≡ f n → m ≡ n
    f-inj = Sm.small-inj

```

<!--en-->
An environment entry of `A` is read as an ambient set through the embedding of the presentation.
<!--zh-->
`A` 的环境条目经呈现的嵌入被读作外围集合。
<!--ja-->
`A` の環境の項目は、提示の埋め込みを通して周囲の集合として読まれる。
<!--/-->

```agda
  vA : {n : ℕ} → Ix A n → Fin n → V ℓ
  vA g i = ⟪ fst A ⟫↪ (g i)

```

<!--en-->
Likewise for the entries of `B`-environments.
<!--zh-->
`B` 环境的条目亦然。
<!--ja-->
`B` の環境の項目についても同様である。
<!--/-->

```agda
  vB : {n : ℕ} → Ix B n → Fin n → V ℓ
  vB h i = ⟪ fst B ⟫↪ (h i)

```

<!--en-->
The lifted assignment applies the extracted function entry by entry: the image of a length-`n` environment of `A` is a length-`n` environment of `B`, so lengths never change.
<!--zh-->
提升后的赋值逐条目施加提取出的函数：`A` 的长度 `n` 环境的像是 `B` 的长度 `n` 环境，长度不变。
<!--ja-->
持ち上げられた割り当ては、抽出された関数を項目ごとに適用する。`A` の長さ `n` の環境の像は `B` の長さ `n` の環境であり、長さは変わらない。
<!--/-->

```agda
  fg : {n : ℕ} → Ix A n → Ix B n
  fg g i = f (g i)

```

<!--en-->
Every entry of an `A`-environment is constructible, by transporting the membership in `A` along the transitivity of constructibility.
<!--zh-->
`A` 环境的每个条目都可构造：把对 `A` 的隶属沿可构造性的传递性搬运。
<!--ja-->
`A` の環境のどの項目も構成可能である。`A` への所属を、構成可能性の推移性に沿って運ぶからである。
<!--/-->

```agda
  isLA : {n : ℕ} (g : Ix A n) (i : Fin n) → ⟨ isL (vA g i) ⟩
  isLA g i = isL-trans (member (fst A) (g i)) (snd A)

```

<!--en-->
Likewise for the entries of `B`-environments.
<!--zh-->
`B` 环境的条目亦然。
<!--ja-->
`B` の環境の項目についても同様である。
<!--/-->

```agda
  isLB : {n : ℕ} (h : Ix B n) (i : Fin n) → ⟨ isL (vB h i) ⟩
  isLB h i = isL-trans (member (fst B) (h i)) (snd B)
```

<!--en-->
For an index object `i`, `Ent y s i` says merely that there are model elements `u` and `v` such that `s(i)=u`, `y(i)=v`, and the graph `E` sends `u` to `v`. The witnesses and all three graph-membership facts are kept under propositional truncation.
<!--zh-->
对索引对象 `i`，`Ent y s i` 仅仅断言存在模型元素 `u` 与 `v`，使得 `s(i)=u`、`y(i)=v`，且图 `E` 把 `u` 送到 `v`。这些见证以及三项图隶属事实都保留在命题截断之下。
<!--ja-->
インデックス対象 `i` に対し、`Ent y s i` は、`s(i)=u`、`y(i)=v` であり、グラフ `E` が `u` を `v` へ送るような模型の要素 `u` と `v` がもっぱら存在することを述べる。これらの証人と三つのグラフ所属の事実は、すべて命題的切り詰めの下に保たれる。
<!--/-->

```agda
  Ent : (y s i : S) → Type (ℓ-suc ℓ)
  Ent y s i = ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
      ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
      × ⟨ pr (fst i) (fst v) ∈ fst y ⟩
      × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ ) ∥₁
```

<!--en-->
The host reading `Wit y s` says merely that some object `n` is the domain of `s`, that `y` is an environment over the fixed target `B` with that same domain, and that every `i∈n` satisfies `Ent y s i`. Thus `y` has the same finite shape as `s`, and its entries are the pointwise `E`-images of those of `s`.
<!--zh-->
宿主层读法 `Wit y s` 仅仅断言：存在对象 `n`，它是 `s` 的定义域；`y` 是固定目标 `B` 上以同一 `n` 为定义域的环境；并且每个 `i∈n` 都满足 `Ent y s i`。因此，`y` 与 `s` 具有相同的有限形状，且其条目逐点为 `s` 中条目在 `E` 下的像。
<!--ja-->
台の水準での読み `Wit y s` は、ある対象 `n` が `s` の定義域であり、`y` が固定された目標 `B` 上で同じ `n` を定義域にもつ環境であり、すべての `i∈n` が `Ent y s i` を満たすことを、もっぱら存在する形で述べる。したがって `y` は `s` と同じ有限な形をもち、その各項目は `s` の項目の `E` による像である。
<!--/-->

```agda

  Wit : (y s : S) → Type (ℓ-suc ℓ)
  Wit y s = ∥ Σ[ n ∈ S ]
      ( ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      × ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      × ((i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) ) ∥₁
```

<!--en-->
The entry formula expresses exactly the three equations hidden in `Ent`: two existentially bound values `u` and `v` satisfy `s(i)=u`, `y(i)=v`, and `E(u)=v`. The variable positions account for the surrounding parameters and the two new witnesses.
<!--zh-->
条目公式恰好表达 `Ent` 中隐藏的三项等式：存在量化的两个值 `u` 与 `v` 满足 `s(i)=u`、`y(i)=v` 以及 `E(u)=v`。变元位置同时计入外围参数与这两个新见证。
<!--ja-->
項目の論理式は、`Ent` に含まれる三つの等式をそのまま表す。存在量化された二つの値 `u` と `v` が `s(i)=u`、`y(i)=v`、`E(u)=v` を満たす。変数位置には、周囲の引数と二つの新しい証人がともに数えられている。
<!--/-->

```agda

  opaque
    private
      entFo : Formula S 5
      entFo = ∃̇ (∃̇ ( appAt i6 i2 i1 ∧̇ appAt i5 i2 i0 ∧̇ appC E i1 i0 ))

```

<!--en-->
The full formula first binds the common domain `n`, then binds an object `b` and requires it to equal the fixed constant `B`. It says that `y` is a `b`-environment on `n` and that the entry formula holds for every `i∈n`; the equality `b=B` makes this exactly an environment over the intended target.
<!--zh-->
完整公式先绑定公共定义域 `n`，再绑定对象 `b` 并要求它等于固定常元 `B`。公式断言 `y` 是定义域为 `n` 的 `b` 环境，且条目公式对每个 `i∈n` 成立；等式 `b=B` 使它恰好成为预期目标上的环境。
<!--ja-->
論理式全体は、まず共通の定義域 `n` を束縛し、次に対象 `b` を束縛して、それが固定した定数 `B` に等しいことを要求する。そして `y` が定義域 `n` をもつ `b` 上の環境であり、すべての `i∈n` で項目の論理式が成り立つと述べる。等式 `b=B` により、これは意図した目標上の環境になる。
<!--/-->

```agda
    fo : Formula S 2
    fo = ∃̇ ( domAt i2 i0
           ∧̇ ∃̇ ( (var i0 ≐ con B)
                ∧̇ envOverAt i2 i1 i0
                ∧̇ ∀̇∈ (var i1) entFo ) )
```

<!--en-->
To read an entry from the formula, the proof eliminates the two nested existential witnesses `u` and `v`. This elimination is valid because `Ent y s i` is itself a proposition under propositional truncation.
<!--zh-->
从公式读出条目时，证明依次消去两层存在见证 `u` 与 `v`。由于 `Ent y s i` 本身经命题截断成为命题，这一消去是合法的。
<!--ja-->
論理式から項目を読み取るため、証明は入れ子になった二つの存在証人 `u` と `v` を順に消去する。`Ent y s i` 自体が命題的切り詰めによって命題になっているので、この消去は正当である。
<!--/-->

```agda

    private
      entOut : (y s n b i : S) → ⟨ (i ∷ b ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩ → Ent y s i
      entOut y s n b i = rec₁ squash₁ (λ { (u , hv) →
        rec₁ squash₁ (λ { (v , (h1 , (h2 , h3))) →
          let γ = v ∷ u ∷ i ∷ b ∷ n ∷ y ∷ s ∷ [] in
```

<!--en-->
The adequacy laws for the two environment applications and for application of `E` convert formula satisfaction into the three ambient memberships. Packaging the recovered `u`, `v`, and these memberships produces the required truncated entry.
<!--zh-->
两个环境应用以及图 `E` 的应用各有充分性定律，它们把公式的满足转换为三项外围隶属。把读回的 `u`、`v` 与这些隶属打包，便得到所需的截断条目。
<!--ja-->
二つの環境の適用とグラフ `E` の適用についての妥当性法則により、論理式の充足を三つの周囲の所属へ変換する。読み戻した `u`、`v` とこれらの所属を組にすると、必要な切り詰められた項目が得られる。
<!--/-->

```agda
          ∣ u , v
          , ( subst ⟨_⟩ (appAt-adequate i6 i2 i1 γ) h1
            , subst ⟨_⟩ (appAt-adequate i5 i2 i0 γ) h2
            , subst ⟨_⟩ (appC-adequate E i1 i0 γ) h3 ) ∣₁ }) hv })

```

<!--en-->
The reverse direction maps a truncated entry into satisfaction of the formula. It uses the same three adequacy equalities in reverse, turning the ambient graph memberships into the two environment-application clauses and the application clause for `E`.
<!--zh-->
反方向把一个截断条目映为公式的满足。证明反向使用同三条充分性等式，把外围图隶属转换为两项环境应用条款与一项 `E` 的应用条款。
<!--ja-->
逆方向では、切り詰められた項目を論理式の充足へ写す。同じ三つの妥当性の等しさを逆向きに用い、周囲のグラフ所属を二つの環境適用の条項と `E` の適用の条項へ変換する。
<!--/-->

```agda
      entIn : (y s n i : S) → Ent y s i → ⟨ (i ∷ B ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩
      entIn y s n i = map₁ (λ { (u , v , (h1 , h2 , h3)) →
        let γ = v ∷ u ∷ i ∷ B ∷ n ∷ y ∷ s ∷ [] in
        u , ∣ v , ( subst ⟨_⟩ (sym (appAt-adequate i6 i2 i1 γ)) h1
                  , subst ⟨_⟩ (sym (appAt-adequate i5 i2 i0 γ)) h2
```

<!--en-->
After both witnesses are repackaged under the nested existential quantifiers, the graph-membership clause for `E` completes satisfaction of the entry formula. Hence `entOut` and `entIn` establish the exact correspondence needed for each index.
<!--zh-->
把两个见证重新装入嵌套存在量词后，`E` 的图隶属条款补全条目公式的满足。因此，`entOut` 与 `entIn` 给出了每个索引处所需的精确对应。
<!--ja-->
二つの証人を入れ子の存在量化子の下へ戻すと、`E` のグラフ所属の条項によって項目の論理式の充足が完成する。こうして `entOut` と `entIn` は、各インデックスで必要となる正確な対応を与える。
<!--/-->

```agda
                  , subst ⟨_⟩ (sym (appC-adequate E i1 i0 γ)) h3 ) ∣₁ })

```

<!--en-->
The body reader receives the three components exposed by the outer formula: `n` is the domain of `s`, the auxiliary object `b` has the same underlying set as `B`, and `y` is an environment over `b` on `n` whose every index satisfies the entry formula. It must convert these data into `Wit y s`.
<!--zh-->
主体读取器接收外层公式展开后的三项数据：`n` 是 `s` 的定义域；辅助对象 `b` 的底层集合与 `B` 相等；`y` 是以 `n` 为定义域的 `b` 环境，且每个索引都满足条目公式。它需要把这些数据转换为 `Wit y s`。
<!--ja-->
本体の読み取りは、外側の論理式から現れる三つの成分を受け取る。`n` は `s` の定義域であり、補助対象 `b` の底の集合は `B` の底の集合と等しく、`y` は定義域 `n` をもつ `b` 上の環境で、その各インデックスが項目の論理式を満たす。これらを `Wit y s` へ変換することが目標である。
<!--/-->

```agda
      bodyOut : (y s n b : S)
              → ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
              → fst b ≡ fst B
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ ∀̇∈ (var i1) entFo ⟩
```

<!--en-->
The equality between the underlying sets of `b` and `B` transports the environment-over assertion from `b` to the fixed target `B`. Each bounded instance of the entry formula is read by `entOut`, and the common domain together with these two components is then packaged under propositional truncation.
<!--zh-->
`b` 与 `B` 的底层集合相等，据此可把「在 `b` 上的环境」这一断言搬运到固定目标 `B`。每个有界索引处的条目公式由 `entOut` 读回，最后把公共定义域与这两项数据一并装入命题截断。
<!--ja-->
`b` と `B` の底の集合の等しさに沿って、`b` 上の環境であるという主張を固定された目標 `B` へ移す。各有界インデックスでの項目の論理式を `entOut` で読み戻し、共通の定義域とこれら二つの成分を命題的切り詰めの下にまとめる。
<!--/-->

```agda
              → Wit y s
      bodyOut y s n b hd eb he hS =
        ∣ n , ( hd
              , envOverAt-transport (b ∷ n ∷ y ∷ s ∷ []) (B ∷ n ∷ y ∷ s ∷ [])
                  i2 i1 i0 i2 i1 i0 refl refl eb he
```

<!--en-->
The bounded universal clause is used pointwise: for each `i∈n`, `entOut` turns its satisfaction proof into `Ent y s i`. Together with the domain equation and the transported environment condition, these entries form the three components of the truncated witness `Wit y s`.
<!--zh-->
有界全称子句按点使用：对每个 `i∈n`，`entOut` 把其满足证明转成 `Ent y s i`。这些条目与定义域等式及搬运后的环境条件一起，构成截断见证 `Wit y s` 的三个分量。
<!--ja-->
有界全称の節は各点で用いる。各 `i∈n` について、`entOut` がその充足の証明を `Ent y s i` へ変換する。これらの項目を、定義域の等式および移送した環境条件と合わせると、切り詰められた証人 `Wit y s` の三成分が得られる。
<!--/-->

```agda
              , λ i i∈n → entOut y s n b i (hS i i∈n) ) ∣₁

```

<!--en-->
To read the whole graph formula outward, we first eliminate the truncated witness `n`, then the truncated witness `b`. Their accompanying clauses give the domain condition, the equality `fst b ≡ fst B`, the environment condition, and the bounded step condition; `bodyOut` turns exactly these data into `Wit y s`. The eliminations are legitimate because `Wit y s` is itself propositionally truncated.
<!--zh-->
向外读取整个图公式时，先消去截断见证 `n`，再消去截断见证 `b`。与它们相伴的子句分别给出定义域条件、等式 `fst b ≡ fst B`、环境条件和有界步骤条件；`bodyOut` 恰把这些数据变成 `Wit y s`。由于 `Wit y s` 本身经过命题截断，这两次消去是合法的。
<!--ja-->
グラフ論理式全体を外向きに読むには、まず切り詰められた証人 `n` を除去し、次に切り詰められた証人 `b` を除去する。それらに伴う節から、定義域条件、等式 `fst b ≡ fst B`、環境条件、有界ステップ条件が得られ、`bodyOut` がちょうどこれらを `Wit y s` に変える。`Wit y s` 自体が命題的に切り詰められているので、この二つの除去は正当である。
<!--/-->

```agda
    fo-out : (y s : S) → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩ → Wit y s
    fo-out y s = rec₁ squash₁ (λ { (n , (hd , hb)) →
      rec₁ squash₁ (λ { (b , (eb , (he , hS))) → bodyOut y s n b hd eb he hS }) hb })

```

<!--en-->
Conversely, a host-level witness supplies the outer existential with `n` and the inner existential with the fixed element `B`. Reflexivity proves that this element denotes the required target, while `entIn` converts every pointwise entry back into the bounded formula. Together, `fo-out` and `fo-in` establish the adequacy of `fo` for `Wit`.
<!--zh-->
反过来，宿主层见证以 `n` 填入外层存在量词，以固定元素 `B` 填入内层存在量词。自反性证明该元素正表示所需目标，而 `entIn` 把每个逐点条目转回有界公式。于是，`fo-out` 与 `fo-in` 共同确立 `fo` 对 `Wit` 的充分性。
<!--ja-->
逆に、ホスト側の証人は外側の存在量化に `n` を、内側の存在量化に固定された要素 `B` を与える。反射律がこの要素は必要な目標を表すことを示し、`entIn` が各点の項目を有界論理式へ戻す。したがって `fo-out` と `fo-in` は、`Wit` に対する `fo` の妥当性を両方向から確立する。
<!--/-->

```agda
    fo-in : (y s : S) → Wit y s → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩
    fo-in y s = rec₁ (snd ((y ∷ s ∷ []) ⊨ fo))
      (λ { (n , (hd , he , hS)) →
        ∣ n , ( hd , ∣ B , ( refl , he , λ i i∈n → entIn y s n i (hS i i∈n) ) ∣₁ ) ∣₁ })
```

<!--en-->
Fix a sequence `g` of length `N` over `A`, a carrier element `s`, and an equation identifying the underlying set of `s` with the environment graph of `g`. This concrete representation lets us construct the coordinatewise image and then prove that any output satisfying the same graph formula has the same underlying set.
<!--zh-->
固定 `A` 上长度为 `N` 的序列 `g`、载体元素 `s`，以及把 `s` 的底层集合认同于 `g` 的环境图的等式。借助这一具体表示，可以构造逐坐标像，并证明任何满足同一图公式的输出都具有相同的底层集合。
<!--ja-->
`A` 上の長さ `N` の列 `g`、台の要素 `s`、および `s` の底の集合を `g` の環境グラフと同一視する等式を固定する。この具体的な表示から成分ごとの像を構成し、同じグラフ論理式を満たす任意の出力が同じ底の集合をもつことを示せる。
<!--/-->

```agda
  module AtSeq (N : ℕ) (g : Ix A N) (s : S) (e : fst s ≡ fst (envS A g)) where

```

<!--en-->
The intended output is the environment graph of the coordinatewise image `fg g`. At index `j`, its value is `f (g j)`, so the source and target sequences have the same finite length and corresponding entries are related by the input graph `E`.
<!--zh-->
预期输出是逐坐标像 `fg g` 的环境图。在索引 `j` 处，它的值为 `f (g j)`；因此源序列与目标序列具有相同的有限长度，对应条目由输入图 `E` 联系。
<!--ja-->
意図する出力は、成分ごとの像 `fg g` の環境グラフである。添字 `j` での値は `f (g j)` なので、源の列と目標の列は同じ有限長をもち、対応する項は入力グラフ `E` によって関係づけられる。
<!--/-->

```agda
    y₀ : S
    y₀ = envS B (fg g)

```

<!--en-->
The next lemma exposes the elementary membership fact needed to build this witness: each coordinate pair occurs in the graph of an environment. It remains local because the public result of the subsection is the existence and uniqueness of the whole image environment.
<!--zh-->
下一个引理给出构造该见证所需的基本隶属事实：每个坐标对都属于环境图。它保持为局部引理，因为本小节的公开结论是整个像环境的存在性与唯一性。
<!--ja-->
次の補題は、この証人を構成するために必要な基本的な所属の事実を与える。各座標の対は環境グラフに属する。この補題が局所的なのは、この小節で公開する結論が像の環境全体の存在と一意性だからである。
<!--/-->

```agda
    private
```

<!--en-->
The entry lemma says that the coded graph of a function contains the ordered pair of each natural index with its value. The proof is by the specification of the environment constructor: the pair is there by definition.
<!--zh-->
条目引理说：函数的编码图包含每个自然索引与其值组成的有序对。证明由环境构造子的规格而来：该对由定义即在。
<!--ja-->
項目の補題は、関数の符号化されたグラフが、それぞれの自然数の添字とその値の順序対を含むと言う。証明は、環境の構成子の仕様から来る。その対は定義によってそこにあるのである。
<!--/-->

```agda
      at : {k : ℕ} (h : Fin k → V ℓ) (j : Fin k)
         → ⟨ pr (# (toℕ j)) (h j) ∈ env h ⟩
      at h j = subst ⟨_⟩ (sym (lookup-spec h j (h j))) refl

```

<!--en-->
The canonical image satisfies the host predicate `Wit`: the numeral `nn N` records the common domain, `he` records that `y₀` is an environment over `B` of that length, and `step` verifies the relation at every index below `N`. These three clauses are then placed under propositional truncation, preserving existence without exposing a chosen decomposition later.
<!--zh-->
典范像满足宿主谓词 `Wit`：数码 `nn N` 记录公共定义域，`he` 记录 `y₀` 是长度为 `N`、取值于 `B` 的环境，`step` 则在每个小于 `N` 的索引处验证关系。最后把这三条子句置于命题截断之下，只保留存在性，而不让后文依赖某个选定的分解。
<!--ja-->
標準的な像はホスト側の述語 `Wit` を満たす。数項 `nn N` が共通の定義域を記録し、`he` が `y₀` は長さ `N` の `B` 上の環境であることを記録し、`step` が `N` 未満の各添字で関係を確かめる。最後にこの三つの節を命題的切り詰めの中へ入れ、後の議論が特定の分解に依存しない形で存在だけを残す。
<!--/-->

```agda
    wit : Wit y₀ s
    wit = ∣ nn N , ( hd , he , step ) ∣₁
      where
      hd : ⟨ (nn N ∷ y₀ ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      hd = domAt-fill i2 i0 (nn N ∷ y₀ ∷ s ∷ []) N (vA g) (isLA g) e refl
```

<!--en-->
The fact `envOver B (fg g)` is initially stated in the shorter environment containing `B`, `nn N`, and `y₀`. The transport lemma moves this same formula to the longer assignment that also contains `s`; the three reflexivity proofs say that the slots used by the formula still contain exactly the same elements. Hence adding the unused source sequence does not change the environment-over assertion.
<!--zh-->
事实 `envOver B (fg g)` 起初在只含 `B`、`nn N` 与 `y₀` 的较短环境中陈述。运输引理把同一公式搬到还含有 `s` 的较长赋值；三条自反性证明表明，公式实际使用的槽位仍含有完全相同的元素。因此，加入未被该公式使用的源序列不会改变环境覆盖断言。
<!--ja-->
事実 `envOver B (fg g)` は、初めは `B`、`nn N`、`y₀` だけを含む短い環境について述べられている。移送補題は同じ論理式を、さらに `s` を含む長い割当てへ移す。三つの反射律の証明は、論理式が使う各位置にまったく同じ要素が残っていることを示す。したがって、使われない源の列を加えても環境についての主張は変わらない。
<!--/-->

```agda

      he : ⟨ (B ∷ nn N ∷ y₀ ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      he = envOverAt-transport (B ∷ nn N ∷ y₀ ∷ []) (B ∷ nn N ∷ y₀ ∷ s ∷ [])
             i2 i1 i0 i2 i1 i0 refl refl refl (envOver B (fg g))

```

<!--en-->
The step clause at each position is proved by eliminating the numeral membership into a bounded natural number. The eliminated data names a specific index whose value is available in both sequences.
<!--zh-->
每个位置处的步进子句由消去数码隶属为有界自然数证明。消去的数据名指一个具体索引，其取值在两条序列中都可用。
<!--ja-->
それぞれの位置でのステップの条項は、数項の所属を有界の自然数へ消去することで証明される。消去されたデータが、両方の列で値の得られる具体的な添字を名指す。
<!--/-->

```agda
      step : (i : S) → ⟨ fst i ∈ # N ⟩ → Ent y₀ s i
      step i i∈N = map₁ atIndex (∈#-elim N (fst i) i∈N)
        where
        atIndex : Σ[ k ∈ ℕ ] ((k < N) × (fst i ≡ # k))
                → Σ[ u ∈ S ] Σ[ v ∈ S ]
```

<!--en-->
For the recovered finite index `j`, the required entry consists of the source value `vA g j`, the target value `vB (fg g) j`, and three graph memberships: the source environment stores the first value at `j`, the target environment stores the second there, and `E` relates the first value to the second. Constructibility proofs turn both values into elements of the carrier `S`.
<!--zh-->
对恢复出的有限索引 `j`，所需条目由源值 `vA g j`、目标值 `vB (fg g) j` 与三条图隶属组成：源环境在 `j` 处存放前者，目标环境在该处存放后者，而 `E` 把前者联系到后者。可构造性证明把这两个值提升为载体 `S` 的元素。
<!--ja-->
復元された有限添字 `j` に対し、必要な項目は源の値 `vA g j`、目標の値 `vB (fg g) j`、および三つのグラフ所属からなる。源の環境は `j` に前者を、目標の環境は同じ位置に後者を格納し、`E` は前者を後者に関係づける。構成可能性の証明により、二つの値はいずれも台 `S` の要素になる。
<!--/-->

```agda
                    ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
                    × ⟨ pr (fst i) (fst v) ∈ fst y₀ ⟩
                    × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
        atIndex (k , p , ei) =
            (vA g j , isLA g j) , (vB (fg g) j , isLB (fg g) j)
```

<!--en-->
The environment-entry lemma supplies the first two memberships, transported along the equation that identifies the given position with the numeral for `j` and, for the source, along the presentation equation `e`. The graph theorem `f-graph` supplies the third. The finite index `j` is defined immediately below from the bounded natural number obtained in the preceding step.
<!--zh-->
环境条目引理给出前两条隶属，并沿「给定位置等于 `j` 的数码」这一等式运输；源环境的一项还要沿呈现等式 `e` 运输。图定理 `f-graph` 给出第三条隶属。有限索引 `j` 随即由上一步得到的有界自然数定义。
<!--ja-->
環境の項目補題が最初の二つの所属を与え、それらを、与えられた位置と `j` の数項を同一視する等式に沿って移送する。源の環境については、さらに提示の等式 `e` に沿って移送する。三つ目の所属はグラフ定理 `f-graph` から得られる。有限添字 `j` は、直前に得た有界自然数からすぐ下で定義される。
<!--/-->

```agda
          , ( subst2 (λ a w → ⟨ pr a (vA g j) ∈ w ⟩) (sym qi) (sym e) (at (vA g) j)
            , subst (λ a → ⟨ pr a (vB (fg g) j) ∈ fst y₀ ⟩) (sym qi) (at (vB (fg g)) j)
            , f-graph (g j) )
          where
          j : Fin N
```

<!--en-->
The internal index `j` is constructed from the bounded natural number by the finite decoding, and the numeral equation composes the membership transport with the recovery of the index value.
<!--zh-->
内部索引 `j` 由有界自然数的有限解码构造，数码等式由隶属运输与索引值恢复复合而成。
<!--ja-->
内部の添字 `j` は、有界の自然数の有限の復号から構成され、数項の等式は、所属の輸送と添字の値の復元を合成したものである。
<!--/-->

```agda
          j = fromℕ' N k p
          qi : fst i ≡ # (toℕ j)
          qi = ei ∙ cong #_ (sym (toFromId' N k p))

```

<!--en-->
Uniqueness starts with an arbitrary candidate `y` satisfying `Wit y s` and aims to prove equality of its underlying set with that of `y₀`. The truncated witness may be eliminated because equality in the cumulative hierarchy is a proposition. Once its three clauses are exposed, the local module `Only` derives the desired equality from them.
<!--zh-->
唯一性证明从任意满足 `Wit y s` 的候选 `y` 出发，目标是证明它与 `y₀` 的底层集合相等。累积层级中的相等是命题，因此可以消去截断见证。展开其中三条子句后，局部模块 `Only` 从这些数据推出所需等式。
<!--ja-->
一意性の証明では、`Wit y s` を満たす任意の候補 `y` から始め、その基礎にある集合が `y₀` のものと等しいことを目標とする。累積階層の等しさは命題なので、切り詰められた証人を除去できる。三つの節を取り出した後、局所モジュール `Only` がそれらから必要な等式を導く。
<!--/-->

```agda
    only : (y : S) → Wit y s → fst y ≡ fst y₀
    only y = rec₁ (setIsSet (fst y) (fst y₀))
      (λ { (n , (hd , he , hS)) → Only.final n hd he hS })
      where
      module Only (n : S)
```

<!--en-->
The inner module collects the three clauses of the witness: the domain condition, the environment-over condition, and the step clause at every position.
<!--zh-->
内部模块收集见证的三条子句：定义域条件、环境覆盖条件与每个位置处的步进子句。
<!--ja-->
内側のモジュールは、証人の三つの条項を集める。定義域の条件、環境の上の条件、そしてすべての位置でのステップの条項である。
<!--/-->

```agda
                  (hd : ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩)
                  (he : ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩)
                  (hS : (i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) where

```

<!--en-->
The numeral equation identifies the unknown length with the known length `N`, by the adequacy of the domain coding.
<!--zh-->
数码等式按域编码的充分性，把未知长度认同于已知长度 `N`。
<!--ja-->
数項の等式が、定義域の符号化の妥当性によって、未知の長さを既知の長さ `N` と同一視する。
<!--/-->

```agda
        qn : fst n ≡ # N
        qn = domAt-numeral i2 i0 (n ∷ y ∷ s ∷ []) N (vA g) (isLA g) e hd
```

<!--en-->
The environment condition and the recovered length determine an index function `gR : Ix B N` whose graph presents the candidate `y`. This definition is opaque because its construction eliminates truncated data; subsequent reasoning uses the recovered function through its stated equations rather than unfolding that elimination.
<!--zh-->
环境条件与恢复出的长度确定索引函数 `gR : Ix B N`，其环境图呈现候选 `y`。这个定义是不透明的，因为它的构造会消去截断数据；后续论证通过已陈述的等式使用恢复函数，而不展开这次消去。
<!--ja-->
環境条件と復元された長さから、候補 `y` を環境グラフとして表示する添字関数 `gR : Ix B N` が定まる。この定義は、切り詰められたデータを除去して構成されるため不透明である。以後はその除去を展開せず、述べられた等式を通して復元関数を使う。
<!--/-->

```agda
        opaque
          gR : Ix B N
          gR = Recover.g B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he

```

<!--en-->
Recovery also proves that the underlying set of `y` is the environment graph generated by `gR`. This equation replaces the arbitrary presentation in the witness by a fixed-length coordinate presentation, so uniqueness can now be checked one coordinate at a time.
<!--zh-->
恢复过程还证明，`y` 的底层集合正是 `gR` 生成的环境图。这个等式把见证中的任意呈现换成定长的逐坐标呈现，因此现在可以逐坐标证明唯一性。
<!--ja-->
復元はさらに、`y` の基礎にある集合が `gR` から生成される環境グラフであることを示す。この等式によって、証人に含まれる任意の提示を固定長の座標表示へ置き換えられるので、一意性を座標ごとに確かめられる。
<!--/-->

```agda
          gR-eq : fst y ≡ fst (envS B gR)
          gR-eq = Recover.recovers B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he
```

<!--en-->
At each index `j`, the step clause yields, under propositional truncation, a source value, a candidate target value, and the three graph memberships relating them. The target equality is a proposition, so `rec₁` may pass these data to `read`. That lemma proves equality of the represented values; injectivity of the presentation of `B` then gives `gR j ≡ fg g j`.
<!--zh-->
在每个索引 `j` 处，步骤子句在命题截断下给出一个源值、一个候选目标值以及联系二者的三条图隶属。目标等式是命题，因此 `rec₁` 可以把这些数据交给 `read`。该引理证明两个被呈现的值相等，再由 `B` 的呈现单射性得到 `gR j ≡ fg g j`。
<!--ja-->
各添字 `j` で、ステップの節は命題的切り詰めのもとに、源の値、候補となる目標値、および両者を結ぶ三つのグラフ所属を与える。目標の等式は命題なので、`rec₁` はこれらのデータを `read` に渡せる。この補題が表示された二つの値の等しさを示し、`B` の表示の単射性から `gR j ≡ fg g j` が従う。
<!--/-->

```agda
        pt : (j : Fin N) → gR j ≡ fg g j
        pt j = ↪-inj {a = fst B} (rec₁ (setIsSet _ _) read (hS (nn (toℕ j)) j∈n))
          where
          j∈n : ⟨ # (toℕ j) ∈ fst n ⟩
          j∈n = subst (λ w → ⟨ # (toℕ j) ∈ w ⟩) (sym qn) (#mono (toℕ j) N (toℕ<n j))
```

<!--en-->
The reading lemma states what the step clause provides: two elements and three memberships, identifying the argument in the source sequence, the value in the unknown environment, and the relation fact connecting them through the coded pairing.
<!--zh-->
读取引理陈述步进子句所供内容：两个元素与三条隶属，认同源序列中的实参、未知环境中的取值，以及经编码配对连接二者的关系事实。
<!--ja-->
読み出しの補題は、ステップの条項が供給するものを述べる。二つの要素と三つの所属であり、源の列の中の引数、未知の環境の中の値、そして符号化された対でそれらを結ぶ関係の事実を同定する。
<!--/-->

```agda

          read : Σ[ u ∈ S ] Σ[ v ∈ S ]
                   ( ⟨ pr (# (toℕ j)) (fst u) ∈ fst s ⟩
                   × ⟨ pr (# (toℕ j)) (fst v) ∈ fst y ⟩
                   × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
               → vB gR j ≡ vB (fg g) j
```

<!--en-->
The equation of the source argument is recovered by the lookup specification of the source environment, transported along the identifying equation.
<!--zh-->
源实参的等式由源环境的查询规格恢复，沿认同等式运输。
<!--ja-->
源の引数の等式は、源の環境の参照の仕様によって復元され、同定の等式に沿って運ばれる。
<!--/-->

```agda
          read (u , v , (hu , hv , hE)) = sym qv ∙ qv'
            where
            qu : fst u ≡ vA g j
            qu = subst ⟨_⟩ (lookup-spec (vA g) j (fst u))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst u) ∈ w ⟩) e hu)
```

<!--en-->
The candidate value `v` has two descriptions. Looking it up in the recovered environment gives `fst v ≡ vB gR j`. On the other hand, `hE` says that `E` relates the recovered source argument to `v`; after identifying that argument with `vA g j`, single-valuedness of `E` compares this edge with `f-graph (g j)` and yields `fst v ≡ vB (fg g) j`.
<!--zh-->
候选值 `v` 有两种刻画。由恢复环境中的查询可得 `fst v ≡ vB gR j`。另一方面，`hE` 说明 `E` 把恢复出的源实参联系到 `v`；把该实参认同为 `vA g j` 后，`E` 的单值性将这条边与 `f-graph (g j)` 比较，从而得到 `fst v ≡ vB (fg g) j`。
<!--ja-->
候補値 `v` には二つの記述がある。復元された環境から読み取ると `fst v ≡ vB gR j` が得られる。一方、`hE` は、`E` が復元された源の引数を `v` に関係づけることを述べる。その引数を `vA g j` と同一視した後、`E` の一価性によってこの辺を `f-graph (g j)` と比較し、`fst v ≡ vB (fg g) j` を得る。
<!--/-->

```agda
            qv : fst v ≡ vB gR j
            qv = subst ⟨_⟩ (lookup-spec (vB gR) j (fst v))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst v) ∈ w ⟩) gR-eq hv)
            qv' : fst v ≡ vB (fg g) j
            qv' = svAt-out zero (E ∷ A ∷ []) sv u v (vB (fg g) j , isLB (fg g) j) hE
```

<!--en-->
The final equation composes the function-graph fact with the reversed argument equation, completing the identification of the two image values.
<!--zh-->
最后的等式复合函数图事实与反向的实参等式，完成两个像取值的认同。
<!--ja-->
最後の等式が、関数のグラフの事実と逆向きの引数の等式を合成して、二つの像の値の同定を完成させる。
<!--/-->

```agda
                    (subst (λ w → ⟨ pr w (vB (fg g) j) ∈ fst E ⟩) (sym qu) (f-graph (g j)))

```

<!--en-->
It remains to pass from coordinatewise agreement to equality of the two environment graphs. The desired path begins with the recovered presentation of `y` and ends at the canonical graph `y₀`.
<!--zh-->
现在只需把逐坐标一致提升为两个环境图的相等。所需路径从 `y` 的恢复呈现出发，终止于典范图 `y₀`。
<!--ja-->
残るのは、座標ごとの一致を二つの環境グラフの等しさへ高めることである。必要なパスは `y` の復元された提示から始まり、標準グラフ `y₀` に至る。
<!--/-->

```agda
        final : fst y ≡ fst y₀
```

<!--en-->
Function extensionality turns `pt` into equality of the two index functions. Applying `envS B` along that path identifies their environment graphs, and composing with `gR-eq` proves `fst y ≡ fst y₀`. The path-lambda expression is the direct cubical action of the environment graph along this equality.
<!--zh-->
函数外延性把 `pt` 提升为两个索引函数的相等。让 `envS B` 沿这条路径变化即可认同两个环境图，再与 `gR-eq` 复合便得到 `fst y ≡ fst y₀`。这里的路径 lambda 直接表示环境图沿该等式的立方作用。
<!--ja-->
関数外延性により、`pt` は二つの添字関数の等しさになる。そのパスに沿って `envS B` を動かすと二つの環境グラフが同一視され、これを `gR-eq` と合成して `fst y ≡ fst y₀` を得る。ここでのパスラムダは、この等しさに沿う環境グラフの cubical な作用を直接表している。
<!--/-->

```agda
        final = gR-eq ∙ λ i → fst (envS B (funExt pt i))
```

<!--en-->
Membership in the sequence set is stated as a type so that the argument can carry it alongside each element.
<!--zh-->
序列集的隶属被陈述为类型，使论证能把它与每个元素并肩携带。
<!--ja-->
列の集合への所属は型として記録され、議論が、写す各要素とともにそれを運べるようにする。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem s = ⟨ fst s ∈ˢ fst (seqL A) ⟩

```

<!--en-->
A representation is the truncated record of a length, an index function and the equation identifying the two presentations. The truncated form is what `seqL-out` supplies.
<!--zh-->
表示是「长度、索引函数与认同两种呈现的等式」的截断记录。截断形式正是 `seqL-out` 所供给的。
<!--ja-->
表示とは、長さ、添字の関数、そして二つの提示を同一視する等式の、切り詰められた記録である。切り詰められた形こそ、`seqL-out` が供給するものである。
<!--/-->

```agda
  Rep : S → Type (ℓ-suc ℓ)
  Rep s = ∥ Σ[ n ∈ ℕ ] Σ[ g ∈ Ix A n ] (fst s ≡ fst (envS A g)) ∥₁

```

<!--en-->
Starting from membership in `seqL A`, `seqL-out` gives a propositionally truncated length `n` together with membership in the corresponding fixed-length environment set. For that `n`, `envSet-out` gives a truncated index function and presentation equation. Mapping and eliminating only into the truncated target combines the two stages without choosing a global representation.
<!--zh-->
从 `seqL A` 中的隶属出发，`seqL-out` 在命题截断下给出长度 `n` 及相应定长环境集中的隶属。对这个 `n`，`envSet-out` 再给出截断的索引函数与呈现等式。映射这些数据，并且只向截断目标作消去，就能合并两个阶段而不选择全局表示。
<!--ja-->
`seqL A` への所属から、`seqL-out` は命題的切り詰めのもとで長さ `n` と、対応する固定長環境集合への所属を与える。その `n` に対して `envSet-out` は、切り詰められた添字関数と提示の等式を与える。これらを写し、切り詰められた目標にだけ除去することで、大域的な表示を選ばずに二段階を合成できる。
<!--/-->

```agda
  rep : (s : S) → Mem s → Rep s
  rep s m = rec₁ squash₁
    (λ { (n , hn) → map₁ (λ { (g , e) → n , g , e }) (envSet-out A n s hn) })
    (seqL-out A s m)

```

<!--en-->
The recursion package uses `seqL A` as its domain and `fo` as its graph. For every member `s`, a truncated representation of `s` determines the canonical image environment; `AtSeq.wit` proves that this image satisfies the graph, while `AtSeq.only` proves that every other satisfying value has the same underlying set. Thus the graph is total and single-valued in the sense required by `mereFunct`.
<!--zh-->
递归包以 `seqL A` 为定义域，以 `fo` 为图。对每个成员 `s`，它的一个截断表示确定典范像环境；`AtSeq.wit` 证明该像满足图，而 `AtSeq.only` 证明任何其他满足图的值都具有相同的底层集合。因此，这个图具有 `mereFunct` 所要求的全定义性与单值性。
<!--ja-->
再帰の構造は `seqL A` を定義域、`fo` をグラフとする。各要素 `s` の切り詰められた表示から標準的な像の環境が定まり、`AtSeq.wit` はその像がグラフを満たすことを、`AtSeq.only` はほかのどの充足値も同じ基礎の集合をもつことを示す。したがって、このグラフは `mereFunct` が要求する意味で全域的かつ一価である。
<!--/-->

```agda
  R : Recursion
  R = record
    { dom   = seqL A
    ; graph = fo
    ; funct = λ s m → mereFunct fo s (map₁ (λ { (n , g , e) →
```

<!--en-->
For a concrete representation `(n , g , e)`, the functionality witness consists of the canonical image `AtSeq.y₀`, its proof of satisfying `fo`, and the proof that every other satisfying carrier element is equal to it. `Σ≡Prop` lifts equality of underlying sets to equality in `S`, since constructibility proofs form proposition-valued fibres. `map₁` then keeps the whole construction under truncation.
<!--zh-->
对具体表示 `(n , g , e)`，函数性见证由典范像 `AtSeq.y₀`、它满足 `fo` 的证明，以及任何其他满足公式的载体元素都与它相等的证明组成。由于可构造性证明形成命题值纤维，`Σ≡Prop` 把底层集合的相等提升为 `S` 中的相等；`map₁` 随后让整个构造继续处于截断之下。
<!--ja-->
具体的な表示 `(n , g , e)` に対する関数性の証人は、標準的な像 `AtSeq.y₀`、それが `fo` を満たす証明、およびほかのどの充足する台の要素もそれに等しいという証明からなる。構成可能性の証明は命題値のファイバーをなすので、`Σ≡Prop` は基礎にある集合の等しさを `S` での等しさへ持ち上げる。続いて `map₁` が構成全体を切り詰めの中に保つ。
<!--/-->

```agda
        AtSeq.y₀ n g s e
        , ( fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e)
          , λ y' h → Σ≡Prop (λ v → snd (isL v)) (AtSeq.only n g s e y' (fo-out y' s h)) ) })
        (rep s m)) }

```

<!--en-->
The recursion table machinery is opened, supplying the actual function, its values, and the uniqueness of values.
<!--zh-->
递归表机制被打开，供给实际函数、其取值与取值的唯一性。
<!--ja-->
再帰の表の機構が開かれ、実際の関数、その値、そして値の一意性を供給する。
<!--/-->

```agda
  module T = Of R using ( funct; val; val-uniq )

```

<!--en-->
The resulting value `fn s m` is the unique carrier element satisfying `fo` at `s`; although its construction starts from a truncated representation of `s`, uniqueness makes the value independent of which length and index function represent that sequence.
<!--zh-->
所得值 `fn s m` 是在 `s` 处满足 `fo` 的唯一载体元素。尽管它的构造从 `s` 的截断表示出发，唯一性保证其值不依赖于用哪个长度和索引函数表示该序列。
<!--ja-->
得られる値 `fn s m` は、`s` において `fo` を満たす一意な台の要素である。その構成は `s` の切り詰められた表示から始まるが、一意性により、どの長さと添字関数でその列を表示しても値は変わらない。
<!--/-->

```agda
  fn : (s : S) → Mem s → S
  fn = T.val

```

<!--en-->
Whenever `s` is presented by a length `n` and an index function `g`, the computed value `fn s m` equals the canonical coordinatewise image `AtSeq.y₀ n g s e`. Both values satisfy the recursion graph at `s`, so the uniqueness theorem `T.val-uniq` supplies the equality. This equation will let later proofs reason from any available presentation of `s`.
<!--zh-->
只要 `s` 由长度 `n` 与索引函数 `g` 呈现，计算值 `fn s m` 就等于典范逐坐标像 `AtSeq.y₀ n g s e`。两者都在 `s` 处满足递归图，因此唯一性定理 `T.val-uniq` 给出该等式。后续证明由此可以从 `s` 的任一现有呈现出发推理。
<!--ja-->
`s` が長さ `n` と添字関数 `g` で表示されるとき、計算された値 `fn s m` は標準的な成分ごとの像 `AtSeq.y₀ n g s e` に等しくなる。両方が `s` における再帰グラフを満たすので、一意性定理 `T.val-uniq` がこの等しさを与える。この等式により、以後の証明では `s` について手元にあるどの表示からでも推論できる。
<!--/-->

```agda
  fn-code : (s : S) (m : Mem s) (n : ℕ) (g : Ix A n) (e : fst s ≡ fst (envS A g))
          → fn s m ≡ AtSeq.y₀ n g s e
  fn-code s m n g e =
    T.val-uniq s m (AtSeq.y₀ n g s e) (fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e))

```

<!--en-->
Membership in the target sequence set is proved by transporting along the code equation and applying the inward reading of the target sequence set.
<!--zh-->
目标序列集的隶属由沿码等式运输并应用目标序列集的向内读式证明。
<!--ja-->
目標の列の集合への所属は、符号の等式に沿って運び、目標の列の集合の内向きの読み出しを適用することで証明される。
<!--/-->

```agda
  into : (s : S) (m : Mem s) → ⟨ fst (fn s m) ∈ˢ fst (seqL B) ⟩
  into s m = rec₁ (snd (fst (fn s m) ∈ˢ fst (seqL B)))
    (λ { (n , g , e) → subst (λ w → ⟨ fst w ∈ˢ fst (seqL B) ⟩) (sym (fn-code s m n g e))
           (seqL-in B n (envS B (fg g)) (envSet-in B (fg g))) })
    (rep s m)
```

<!--en-->
These facts define a map from `seqL A` to `seqL B`: `fo` gives its graph, `fn` gives its unique value at each source member, and `into` proves that this value is again a finite sequence over `B`. The remaining task is to show that equality of two values forces equality of their source sequences.
<!--zh-->
这些事实定义了从 `seqL A` 到 `seqL B` 的映射：`fo` 给出其图，`fn` 给出每个源元素处的唯一值，`into` 证明该值仍是 `B` 上的有限序列。余下任务是证明两个值相等必迫使其源序列相等。
<!--ja-->
以上の事実から `seqL A` から `seqL B` への写像が定まる。`fo` がそのグラフを、`fn` が各始域要素での一意な値を与え、`into` はその値が再び `B` 上の有限列であることを示す。残る課題は、二つの値が等しければ元の列も等しいと示すことである。
<!--/-->

```agda

  D : DefinableMap
  D = record
    { dom = seqL A ; cod = seqL B ; fn = fn ; into = into ; graph = fo
    ; defines = λ s m → T.funct s m .fst .snd
    ; only    = λ s m y h → sym (T.val-uniq s m y h) }
```

<!--en-->
To prove injectivity, it suffices first to compare canonical presentations. Suppose two coordinatewise image environments are equal, although their displayed lengths may differ. The helper `same` recovers equality of the lengths, transports the second source sequence to the common finite index type, and then uses injectivity of `f` at every coordinate to prove equality of the source environment graphs.
<!--zh-->
为证明单射性，先比较典范呈现即可。设两个逐坐标像环境相等，尽管它们所显示的长度可能不同。辅助引理 `same` 先恢复长度相等，把第二条源序列搬运到共同的有限索引类型，再逐坐标使用 `f` 的单射性，证明两个源环境图相等。
<!--ja-->
単射性を示すには、まず標準的な表示どうしを比較すれば十分である。表示上の長さが異なるかもしれない二つの成分ごとの像の環境が等しいと仮定する。補助補題 `same` は長さの等しさを復元し、二つ目の源の列を共通の有限添字型へ移送した後、各座標で `f` の単射性を使って源の環境グラフの等しさを示す。
<!--/-->

```agda
  private
    same : (n : ℕ) (g : Ix A n) (n' : ℕ) (g' : Ix A n')
         → fst (envS B (fg g)) ≡ fst (envS B (fg g'))
         → fst (envS A g) ≡ fst (envS A g')
    same n g n' g' q =
```

<!--en-->
The equality of the two target environment graphs determines equality of their finite lengths by `env-len`, because the coded domain of an environment is its numeral length. Substitution along that equality reduces the problem to two sequences indexed by the same `Fin n`; the local family `P` records the statement that remains after this alignment.
<!--zh-->
由 `env-len`，两个目标环境图的相等决定其有限长度相等，因为环境的编码定义域就是表示长度的数码。沿该等式作替换后，问题化为比较两条同以 `Fin n` 为索引的序列；局部类型族 `P` 记录对齐后尚待证明的命题。
<!--ja-->
二つの目標環境グラフの等しさから、`env-len` によって有限長の等しさが定まる。環境の符号化された定義域が、その長さを表す数項だからである。この等しさに沿って置換すると、問題は同じ `Fin n` で添字づけられた二つの列の比較に帰着し、局所的な型族 `P` が整列後に残る主張を記録する。
<!--/-->

```agda
      subst P (env-len (envS B (fg g)) (vB (fg g)) (vB (fg g')) (isLB (fg g)) (isLB (fg g')) refl q)
        base g' q
      where
      P : ℕ → Type (ℓ-suc ℓ)
      P k = (h : Ix A k) → fst (envS B (fg g)) ≡ fst (envS B (fg h))
```

<!--en-->
With a common length, `env-pt` reads equality of the target graphs as equality of their values at each index. Injectivity of the presentation of `B` turns this into equality `f (g j) ≡ f (h j)`, and `f-inj` recovers `g j ≡ h j`. Function extensionality then identifies the source index functions, hence their environment graphs.
<!--zh-->
长度相同后，`env-pt` 把目标图的相等读成每个索引处取值相等。`B` 的呈现单射性将其化为 `f (g j) ≡ f (h j)`，再由 `f-inj` 恢复 `g j ≡ h j`。函数外延性于是认同两个源索引函数，进而认同其环境图。
<!--ja-->
長さが共通になれば、`env-pt` は目標グラフの等しさを各添字での値の等しさとして読む。`B` の表示の単射性により、これは `f (g j) ≡ f (h j)` となり、`f-inj` から `g j ≡ h j` が復元される。関数外延性が源の添字関数を同一視し、したがってその環境グラフも同一視する。
<!--/-->

```agda
          → fst (envS A g) ≡ fst (envS A h)
      base : P n
      base h q' = λ i → fst (envS A (funExt (λ j →
        f-inj (g j) (h j) (↪-inj {a = fst B} (env-pt (vB (fg g)) (vB (fg h)) q' j))) i))

```

<!--en-->
For arbitrary members `s` and `s'`, their representations are available only under propositional truncation. The desired equality `fst s ≡ fst s'` is a proposition because cumulative-hierarchy values form a set, so `rec2` may expose one representation of each input locally and pass them to the canonical comparison.
<!--zh-->
对任意成员 `s` 与 `s'`，它们的表示只在命题截断下可用。累积层级的值形成集合，因此目标等式 `fst s ≡ fst s'` 是命题；于是 `rec2` 可以在局部展开两个输入各自的一个表示，并把它们交给典范呈现的比较。
<!--ja-->
任意の要素 `s` と `s'` について、その表示は命題的切り詰めのもとでしか得られない。累積階層の値は集合をなすため、目標の等式 `fst s ≡ fst s'` は命題である。そこで `rec2` により、各入力の表示を局所的に一つずつ取り出し、標準表示どうしの比較に渡せる。
<!--/-->

```agda
  inj : (s : S) (m : Mem s) (s' : S) (m' : Mem s')
      → fst (fn s m) ≡ fst (fn s' m') → fst s ≡ fst s'
  inj s m s' m' q = rec2 (setIsSet (fst s) (fst s'))
    (λ { (n , g , e) (n' , g' , e') →
        e
```

<!--en-->
The code equations identify the actual outputs `fn s m` and `fn s' m'` with their respective canonical image environments. Composing these identifications with the assumed output equality gives the hypothesis required by `same`; finally, the presentation equations `e` and `e'` transfer the resulting equality of source environment graphs back to `fst s ≡ fst s'`.
<!--zh-->
两个编码等式分别把实际输出 `fn s m` 与 `fn s' m'` 认同于各自的典范像环境。将这些认同与假设的输出相等复合，便得到 `same` 所需的前提；最后，呈现等式 `e` 与 `e'` 把所得源环境图相等转回 `fst s ≡ fst s'`。
<!--ja-->
二つの符号等式は、実際の出力 `fn s m` と `fn s' m'` を、それぞれの標準的な像の環境と同一視する。これらを仮定された出力の等しさと合成すると `same` が必要とする前提が得られ、最後に提示の等式 `e` と `e'` が源の環境グラフの等しさを `fst s ≡ fst s'` へ戻す。
<!--/-->

```agda
      ∙ same n g n' g'
          (sym (cong fst (fn-code s m n g e)) ∙ q ∙ cong fst (fn-code s' m' n' g' e'))
      ∙ sym e' })
    (rep s m) (rep s' m')

```

<!--en-->
The injectivity just proved upgrades the definable map to an internal coded injection `seqL A ↪ seqL B`. Its graph still records the same coordinatewise action; the conclusion retains only the propositional existence of a suitable code.
<!--zh-->
刚证明的单射性把这条可定义映射提升为内部编码单射 `seqL A ↪ seqL B`。其图仍记录同一逐坐标作用；结论只保留适当编码的命题性存在。
<!--ja-->
いま示した単射性により、この定義可能な写像は内部の符号化された単射 `seqL A ↪ seqL B` になる。そのグラフは同じ成分ごとの作用を記録するが、結論に残るのは適切な符号の命題的な存在だけである。
<!--/-->

```agda
  injL : InjL (seqL A) (seqL B)
  injL = Inj.injL D inj
```

<!--en-->
The exported theorem starts from an actual code `E` witnessing an injection from `A` to `B`: it is single-valued, has domain `A`, is injective, and has range contained in `B`. Passing these four components to `SeqMap` yields the propositionally truncated existence of a coded injection from `seqL A` to `seqL B`. The result concerns finite sequences of arbitrary length, not infinite sequences.
<!--zh-->
导出的定理从一个实际的编码图 `E` 出发，它见证从 `A` 到 `B` 的单射：该图单值，定义域为 `A`，具有单射性，且值域包含于 `B`。把这四个分量交给 `SeqMap`，就得到从 `seqL A` 到 `seqL B` 的编码单射之命题截断存在性。该结论涵盖任意长度的有限序列，不涉及无穷序列。
<!--ja-->
公開される定理は、`A` から `B` への単射を証明する実際の符号化グラフ `E` から始める。このグラフは一価で、定義域が `A` であり、単射的で、値域が `B` に含まれる。これら四つの成分を `SeqMap` に渡すと、`seqL A` から `seqL B` への符号化された単射の命題的に切り詰められた存在が得られる。この結果が扱うのは任意の長さの有限列であり、無限列ではない。
<!--/-->

```agda
seq-map : (A B E : S) → InjCode E A B → InjL (seqL A) (seqL B)
seq-map A B E (sv , dm , ij , ran) = SeqMap.injL A B E sv dm ij ran
```

<!--en-->
## Pinning a quantified variable to a constant
<!--zh-->
## 把量化变量固定为常元
<!--ja-->
## 量化変数を定数に固定する
<!--/-->

<!--en-->
The pinning formula binds one existential to fix a free slot to a chosen constant: it says merely that some value equals the constant and satisfies the inner formula.
<!--zh-->
钉扎公式绑定一个存在量词以把自由槽固定到选定常元：它仅说某个值等于该常元且满足内层公式。
<!--ja-->
釘づけの論理式は、一つの存在量化子を束縛して、自由な枠を選んだ定数に固定する。ある値が定数に等しく、内側の論理式を満たす、と言うだけである。
<!--/-->

```agda
pinAt : ∀ {n} → S → Formula S (suc n) → Formula S n
pinAt c φ = ∃̇ ((var zero ≐ con c) ∧̇ φ)

```

<!--en-->
The inward reading exhibits the constant as the witness and the body satisfaction at the extended environment.
<!--zh-->
向内读式出示该常元作为见证，以及体在扩展环境处的满足。
<!--ja-->
内向きの読み出しは、定数を証人として示し、拡張された環境での本体の充足を与える。
<!--/-->

```agda
pin-in : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
       → ⟨ (c ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ pinAt c φ ⟩
pin-in c φ γ h = ∣ c , (refl , h) ∣₁

```

<!--en-->
For the outward direction, the existential supplies a carrier element `z`, an equality of its underlying set with that of `c`, and a proof of the body at `z`. Since constructibility is proposition-valued, `Σ≡Prop` lifts the underlying-set equality to an equality `z ≡ c` in `S`; transport along it gives satisfaction at the pinned environment. Elimination from propositional truncation is valid because formula satisfaction is a proposition.
<!--zh-->
在向外方向，存在量词给出载体元素 `z`、它与 `c` 的底层集合相等，以及公式体在 `z` 处成立的证明。由于可构造性取命题值，`Σ≡Prop` 把底层集合相等提升为 `S` 中的等式 `z ≡ c`；沿该等式运输便得到公式体在钉扎环境中的满足。公式满足是命题，因此从命题截断作此消去是合法的。
<!--ja-->
外向きには、存在量化から台の要素 `z`、その基礎にある集合と `c` のものとの等しさ、および `z` で本体が成り立つ証明を得る。構成可能性は命題値なので、`Σ≡Prop` は基礎の集合の等しさを `S` における等式 `z ≡ c` へ持ち上げる。これに沿って移送すれば、固定された環境での充足が得られる。論理式の充足は命題なので、命題的切り詰めからのこの除去は正当である。
<!--/-->

```agda
pin-out : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
        → ⟨ γ ⊨ pinAt c φ ⟩ → ⟨ (c ∷ γ) ⊨ φ ⟩
pin-out c φ γ = rec₁ (snd ((c ∷ γ) ⊨ φ))
  (λ { (z , (ez , h)) → subst (λ v → ⟨ (v ∷ γ) ⊨ φ ⟩) (Σ≡Prop (λ v → snd (isL v)) ez) h })
```

<!--en-->
## A formula for coded injections into a fixed target
<!--zh-->
## 到固定目标的编码单射公式
<!--ja-->
## 固定した終域への符号化された単射の論理式
<!--/-->

<!--en-->
An `InjCode F a b` consists of four proposition-valued conditions: single-valuedness of `F`, the assertion that its domain is `a`, injectivity of its graph, and containment of its values in `b`. Formula satisfaction is proposition-valued, and the last condition is a dependent function into membership propositions, so their nested product is again a proposition.
<!--zh-->
`InjCode F a b` 由四个命题值条件组成：`F` 的单值性、其定义域为 `a`、图的单射性，以及其取值包含于 `b`。公式满足取命题值，最后一个条件则是取值于隶属命题的依值函数，因此它们的嵌套积仍是命题。
<!--ja-->
`InjCode F a b` は四つの命題値の条件からなる。`F` の一価性、その定義域が `a` であること、グラフの単射性、そして値が `b` に含まれることである。論理式の充足は命題値であり、最後の条件は所属命題を値とする依存関数なので、それらの入れ子の積も命題になる。
<!--/-->

```agda
isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
```

<!--en-->
The remaining range condition quantifies over an argument, a value, and a proof that the graph relates them. Its conclusion is membership of the value in `b`, which is a proposition; repeated dependent products therefore preserve propositionality and complete the proof for `InjCode`.
<!--zh-->
余下的值域条件依次量化实参、取值以及图联系二者的证明，其结论是该取值属于 `b`。隶属是命题，故反复形成依值函数仍保持命题性，从而完成 `InjCode` 为命题的证明。
<!--ja-->
残る値域条件は、引数、値、およびグラフが両者を関係づける証明を順に量化する。その結論は値が `b` に属するという命題である。したがって依存関数を繰り返しても命題性が保たれ、`InjCode` が命題であることの証明が完成する。
<!--/-->

```agda
        (isPropΠ3 (λ _ y _ → snd (fst y ∈ fst b)))))

```

<!--en-->
Only the underlying sets represented by the graph and domain arguments matter to `InjCode`. Because constructibility proofs are propositions, equalities `fst F ≡ fst F'` and `fst a ≡ fst a'` lift uniquely to equalities in `S`; two-variable substitution then transports an injection code from `(F , a)` to `(F' , a')`, while the target `b` remains fixed.
<!--zh-->
`InjCode` 对图参数与定义域参数只依赖它们所呈现的底层集合。由于可构造性证明是命题，等式 `fst F ≡ fst F'` 与 `fst a ≡ fst a'` 可唯一提升为 `S` 中的等式；随后二元替换把 `(F , a)` 上的单射码搬运到 `(F' , a')`，目标 `b` 保持不变。
<!--ja-->
`InjCode` がグラフ引数と定義域引数について参照するのは、それらが表示する基礎の集合だけである。構成可能性の証明は命題なので、等式 `fst F ≡ fst F'` と `fst a ≡ fst a'` は `S` での等式へ一意に持ち上がる。続いて二変数の置換により、目標 `b` を固定したまま、単射の符号を `(F , a)` から `(F' , a')` へ移送する。
<!--/-->

```agda
injcode-resp : (F F' a a' b : S) → fst F ≡ fst F' → fst a ≡ fst a'
             → InjCode F a b → InjCode F' a' b
injcode-resp F F' a a' b qF qa = subst2 {x = F} {y = F'} {z = a} {w = a'}
  (λ E A → InjCode E A b)
  (Σ≡Prop (λ v → snd (isL v)) qF) (Σ≡Prop (λ v → snd (isL v)) qa)

```

<!--en-->
The formula `injFo b f B` expresses the four conditions of an injection code using the graph in slot `f` and the domain in slot `B`. The graph is single-valued, has exactly that domain, and is injective; moreover, whenever it relates an argument to a value, that value belongs to the fixed target `b`. The last clause gives range containment, rather than surjectivity onto `b`.
<!--zh-->
公式 `injFo b f B` 用槽位 `f` 中的图与槽位 `B` 中的定义域表达单射码的四个条件：该图单值，定义域恰为所给集合，并且具有单射性；此外，只要它把某个实参联系到某个取值，该取值就属于固定目标 `b`。最后一条表达值域包含，而非到 `b` 的满射性。
<!--ja-->
論理式 `injFo b f B` は、位置 `f` のグラフと位置 `B` の定義域を使って、単射の符号の四条件を表す。グラフは一価で、定義域がちょうど指定された集合であり、単射的である。さらに、グラフが引数を値に関係づけるなら、その値は固定された目標 `b` に属する。最後の節が表すのは値域の包含であり、`b` への全射性ではない。
<!--/-->

```agda
injFo : ∀ {n} → S → Fin n → Fin n → Formula S n
injFo b f B = svAt f ∧̇ domAt f B ∧̇ injAt f
            ∧̇ ∀̇ (∀̇ (appAt (suc (suc f)) i1 i0 ⇒̇ (var i0 ∈̇ con b)))

```

<!--en-->
To prove the reading laws for `injFo`, fix the target `b`, the two relevant slots `f` and `B`, and an assignment `γ`. The local names `F` and `A` denote the carrier elements found in those slots. The following arguments can then state the result directly as an `InjCode F A b`, keeping the bookkeeping of variable lookup out of the mathematical statement.
<!--zh-->
为证明 `injFo` 的读法，固定目标 `b`、两个相关槽位 `f` 与 `B`，以及赋值 `γ`。局部名称 `F` 与 `A` 分别表示这两个槽位中的载体元素。后续论证于是可以把结论直接陈述为 `InjCode F A b`，不让变量查询的簿记遮蔽数学内容。
<!--ja-->
`injFo` の読み出し則を示すため、目標 `b`、関係する二つの位置 `f` と `B`、および割当て `γ` を固定する。局所名 `F` と `A` は、それぞれの位置にある台の要素を表す。これにより、後の議論では変数参照の処理を数学的な主張から切り離し、結論を直接 `InjCode F A b` と述べられる。
<!--/-->

```agda
module InjFo {n : ℕ} (b : S) (f B : Fin n) (γ : S ^ n) where
  private
    F A : S
    F = lookup f γ
    A = lookup B γ
```

<!--en-->
The reading lemma turns satisfaction of the injection formula into the four clauses of an injection code. For the domain clause, a graph witness for an input is eliminated from propositional truncation into the proposition that the input belongs to `A`; conversely, membership in `A` produces the required domain witness.
<!--zh-->
读取引理把单射公式的满足转换为单射码的四条性质。对定义域条款，输入的图见证从命题截断消去到「该输入属于 `A`」这一命题；反过来，`A` 中的隶属给出所需的定义域见证。
<!--ja-->
読み取りの補題は、単射論理式の充足を単射符号の四つの条件へ変換する。定義域の条件では、入力に対するグラフの証人を命題的切り詰めから「その入力が `A` に属する」という命題へ除去する。逆に、`A` への所属から必要な定義域の証人が得られる。
<!--/-->

```agda

  read : ⟨ γ ⊨ injFo b f B ⟩ → InjCode F A b
  read (sv , dm , ij , ran) =
      svAt-in zero (F ∷ A ∷ []) (λ x y y' p q → svAt-out f γ sv x y y' p q)
    , domAt-intro zero (suc zero) (F ∷ A ∷ []) (λ x →
          (λ h → rec₁ (snd (fst x ∈ fst A))
```

<!--en-->
Single-valuedness and injectivity are transferred by reading their semantic clauses at `γ` and rebuilding the corresponding clauses for the two-entry environment `(F,A)`. The range condition uses adequacy of application to turn graph membership in `F` into the application atom expected by the formula, after which its last clause yields membership of the value in the fixed target `b`.
<!--zh-->
单值性与单射性通过如下方式搬运：先在 `γ` 处读出各自的语义条款，再为二元环境 `(F,A)` 重建相应条款。值域条件利用应用的充分性，把 `F` 中的图隶属转换为公式所需的应用原子，随后公式的末条款给出该值属于固定目标 `b`。
<!--ja-->
一価性と単射性については、それぞれの意味論的な条件を `γ` で読み取り、二項環境 `(F,A)` に対する対応する条件を組み立て直す。値域の条件では、適用の妥当性によって `F` のグラフ所属を論理式が要求する適用原子へ変換し、最後の条項から値が固定された目標 `b` に属することを得る。
<!--/-->

```agda
                   (λ { (y , p) → domAt-out f B γ dm x y p }) h)
        , (λ hx → domAt-in f B γ dm x hx))
    , injAt-in zero (F ∷ A ∷ []) (λ y x x' p q → injAt-out f γ ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ))) p)

```

<!--en-->
The filling lemma is the converse construction: from the four data of a coded injection it builds the satisfaction of the injection formula, this time reading all atoms over the structure in which the formula is stated.
<!--zh-->
填充引理是反向构造：由编码单射的四份数据构造单射公式的满足，这次是在公式陈述所在的那个结构上读取所有原子。
<!--ja-->
埋めの補題は逆向きの構成である。符号化された単射の四つのデータから、単射の論理式の充足を作る。今度は、論理式が述べられている構造のもとですべてのアトムを読む。
<!--/-->

```agda
  fill : InjCode F A b → ⟨ γ ⊨ injFo b f B ⟩
  fill (sv , dm , ij , ran) =
      svAt-in f γ (λ x y y' p q → svAt-out zero (F ∷ A ∷ []) sv x y y' p q)
    , domAt-intro f B γ (λ x →
          (λ h → rec₁ (snd (fst x ∈ fst A))
```

<!--en-->
For totality, a truncated graph witness is eliminated only into the proposition that the input lies in `A`, while membership in `A` supplies a witness in the other direction. The remaining clauses rebuild single-valuedness and injectivity at `γ`, and application adequacy converts the range hypothesis into the final formula clause. Together, `read` and `fill` give both directions between formula satisfaction and the four injection-code conditions.
<!--zh-->
对于全域性，截断的图见证只被消去到「输入属于 `A`」这一命题，而 `A` 中的隶属则在反方向提供见证。其余条款在 `γ` 处重建单值性与单射性，并由应用的充分性把值域假设转换为公式的末条款。因此，`read` 与 `fill` 给出公式满足和单射码四项条件之间的两个方向。
<!--ja-->
全域性については、切り詰められたグラフの証人を「入力が `A` に属する」という命題にだけ除去し、逆向きには `A` への所属から証人を与える。残りの条項は `γ` で一価性と単射性を組み立て直し、適用の妥当性によって値域の仮定を論理式の最後の条項へ変換する。したがって `read` と `fill` は、論理式の充足と単射符号の四条件の間の両方向を与える。
<!--/-->

```agda
                   (λ { (y , p) → domAt-out zero (suc zero) (F ∷ A ∷ []) dm x y p }) h)
        , (λ hx → domAt-in zero (suc zero) (F ∷ A ∷ []) dm x hx))
    , injAt-in f γ (λ y x x' p q → injAt-out zero (F ∷ A ∷ []) ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ)) p)
```

<!--en-->
## Reducing the infinite-stage count to `L_ω`
<!--zh-->
## 把无穷层计数归约到 `L_ω`
<!--ja-->
## 無限段階の計数を `L_ω` に帰着する
<!--/-->

<!--en-->
The stage at the infinite ordinal `ω` is presented as a constructible set: the ordinal stage `Lset ω` together with its ordinalness is packaged by the stage presentation.
<!--zh-->
无穷序数 `ω` 处的层被呈现为可构造集合：序数层 `Lset ω` 连同其序数性由层呈现打包。
<!--ja-->
無限順序数 `ω` における段階は、構成可能な集合として提示される。順序数の段階 `Lset ω` とその順序数性が、段階の提示によってまとめられる。
<!--/-->

```agda
Lω : S
Lω = LsetS ω ω-ord

```

<!--en-->
The goal of the section is then stated as a type: an internal coded injection from the constructible presentation of `Lset ω` into the internal `ω`. This is the base case on which the counting of larger stages is built.
<!--zh-->
本节的目标随之陈述为一个类型：从 `Lset ω` 的可构造呈现到内部 `ω` 的内部编码单射。这是更大层级计数所依赖的基底情形。
<!--ja-->
この節の目標は、型として述べられる。`Lset ω` の構成可能な提示から内部の `ω` への、符号化された内部単射である。これが、より大きな段階の数え上げが依拠する基底の場合である。
<!--/-->

```agda
LimitStageCounted : Type (ℓ-suc ℓ)
LimitStageCounted = InjL Lω ωʟ
```

<!--en-->
The move lemma transports a coded internal injection along equalities of the underlying source and target sets. The source equality gives an inclusion from the new source `a'` into the old source `a`; after the given injection is applied, the target equality gives an inclusion from the old target `b` into the new target `b'`. Composing these three injections yields `InjL a' b'`.
<!--zh-->
搬运引理沿源与目标底层集合的等式搬运内部编码单射。源等式给出从新源 `a'` 到旧源 `a` 的包含；应用给定单射后，目标等式再给出从旧目标 `b` 到新目标 `b'` 的包含。复合这三条单射便得到 `InjL a' b'`。
<!--ja-->
移送の補題は、始域と目標の底の集合の等しさに沿って、内部の符号化された単射を移す。始域の等しさから新しい始域 `a'` を古い始域 `a` へ含め、与えられた単射を適用した後、目標の等しさから古い目標 `b` を新しい目標 `b'` へ含める。この三つの単射の合成によって `InjL a' b'` が得られる。
<!--/-->

```agda
move : (a a' b b' : S) → fst a ≡ fst a' → fst b ≡ fst b' → InjL a b → InjL a' b'
move a a' b b' qa qb h =
  injl-trans a' a b' (inclusion-coded a' a (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym qa) hz))
    (injl-trans a b b' h (inclusion-coded b b' (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) qb hz)))
```

<!--en-->
## The base count: `L_ω` injects into `ω`
<!--zh-->
## 基础计数：`L_ω` 单射到 `ω`
<!--ja-->
## 基底の計数：`L_ω` を `ω` へ単射する
<!--/-->

<!--en-->
The exclusion argument works with finite stages of the form `Lset (# n)`, and begins by taking the tally of such a finite stage: an indexed enumeration of its members.
<!--zh-->
排除论证处理形如 `Lset (# n)` 的有限层，并从取该有限层的名册开始：即其成员的一个带索引枚举。
<!--ja-->
排除の議論は、`Lset (# n)` の形の有限段階を扱い、そのような有限段階の名簿を取ることから始まる。すなわちその要素の、索引づけられた列挙である。
<!--/-->

```agda
private
  module FinNo (n : ℕ) where
    t : Tally (finiteStage n)
    t = StageOrder.tally (stageOrder n)

```

<!--en-->
The tally supplies its size, its member at each index, and the covering fact that every member appears at some index.
<!--zh-->
名册供给其大小、每个索引处的成员，以及「每个成员都出现在某个索引处」的覆盖事实。
<!--ja-->
名簿は、その大きさ、各索引での要素、そしてすべての要素がある索引に現れるという覆いの事実を供給する。
<!--/-->

```agda
    open Tally t using ( size; item; onto )
```

<!--en-->
The search lemma names a member: for each member `x` of the finite stage it runs a decidable search through the finitely many indices, comparing each entry with `x` by excluded middle, and returns an index whose entry is `x`. The search returns some index; it does not claim that index to be unique, and it is a finitary decision on a finite family rather than an appeal to any choice principle.
<!--zh-->
搜索引理为成员命名：对有限层的每个成员 `x`，它在有限多个索引上运行可判定搜索，用排中律逐项比较条目与 `x`，返回条目等于 `x` 的某索引。搜索返回的是某个索引；并不主张该索引唯一，而且这是对有限族的有限判定，不是诉诸任何选择原理。
<!--ja-->
探索の補題は要素に名前を与える。有限段階の各要素 `x` に対して、有限の索引の上で判定可能な探索を走らせ、排中律で各項目を `x` と比較し、その項目が `x` に等しい索引を返す。探索が返すのはある索引であって、それが一意だとは主張しない。これは有限の族の上の有限の判定であり、選択の原理への訴えではない。
<!--/-->

```agda
    named : (x : V ℓ) → ⟨ x ∈ˢ finiteStage n ⟩ → Σ[ i ∈ Fin size ] (item i ≡ x)
    named x hx = decRec (λ q → q) (λ nq → ⊥₀-rec (rec₁ isProp⊥ nq (onto x hx)))
      (DecΣ size (λ i → item i ≡ x)
        (λ i → lem ((item i ≡ x) , setIsSet (item i) x)))

```

<!--en-->
Suppose that `f` injected the presentation of `ω` into a finite stage. Each value `f x` can be assigned a tally index `q x`; duplicating that index gives the map `x ↦ (q x,q x)` required by the finite exclusion theorem. Equality of these pairs forces equality of the corresponding values of `f`, and then injectivity of `f` forces equality of the original inputs.
<!--zh-->
假设 `f` 把 `ω` 的呈现单射到某个有限层。每个值 `f x` 都可取得一个名册索引 `q x`；把该索引复制成 `x ↦ (q x,q x)`，便得到有限排除定理所需的映射。这些索引对相等会迫使相应的 `f` 值相等，再由 `f` 的单射性迫使原输入相等。
<!--ja-->
`f` が `ω` の提示を有限段階へ単射すると仮定する。各値 `f x` には名簿のインデックス `q x` を割り当てられ、そのインデックスを二つ並べた写像 `x ↦ (q x,q x)` が有限性による排除定理の入力になる。この対が等しければ対応する `f` の値が等しくなり、さらに `f` の単射性から元の入力が等しくなる。
<!--/-->

```agda
    noinj : (f : ⟪ ω ⟫ → ⟪ Lset (# n) ⟫)
          → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → ⊥₀
    noinj f finj = finite-excl-ω (# size) (numeral-ord size) (#∈ω size)
      (λ x → q x , q x) (λ x y e → finj x y (qq x y (cong fst e)))
      where
```

<!--en-->
The auxiliary map reads each value of `f` as an ambient element, certifies that it belongs to the finite stage, and names it by the finite index found above.
<!--zh-->
辅助映射把 `f` 的每个值读作外围元素，证明它属于该有限层，并用上一步找到的有限索引为其命名。
<!--ja-->
補助の写像は、`f` のそれぞれの値を周囲の要素として読み、それが有限の段階に属することを証明し、先ほど見つかった有限の索引で名前を与える。
<!--/-->

```agda
      vl : ⟪ ω ⟫ → V ℓ
      vl x = ⟪ Lset (# n) ⟫↪ (f x)
      mm : (x : ⟪ ω ⟫) → ⟨ vl x ∈ˢ finiteStage n ⟩
      mm x = member (Lset (# n)) (f x)
      q : ⟪ ω ⟫ → ⟪ # size ⟫
```

<!--en-->
The map `q` converts the chosen tally index into the corresponding element of the finite ordinal presentation `⟪# size⟫`. If two such names agree, injectivity of that presentation makes their natural-number indices equal, so the two tally entries agree. The presentation of `Lset (# n)` then turns this ambient equality back into equality of the two values of `f`.
<!--zh-->
映射 `q` 把选出的名册索引转换为有限序数呈现 `⟪# size⟫` 中的相应元素。若两个这样的名字相等，该呈现的单射性使其自然数索引相等，因而两项名册条目相等。随后，`Lset (# n)` 的呈现把这一外围等式转回 `f` 的两个值相等。
<!--ja-->
写像 `q` は、選ばれた名簿のインデックスを有限順序数の提示 `⟪# size⟫` の対応する要素へ変換する。その二つの名前が等しければ、この提示の単射性によって自然数インデックスが等しくなり、二つの名簿項目も等しくなる。最後に `Lset (# n)` の提示が、この周囲での等しさを `f` の二つの値の等しさへ戻す。
<!--/-->

```agda
      q x = fromFin size (toℕ (named (vl x) (mm x) .fst) , toℕ<n (named (vl x) (mm x) .fst))
      qq : (x y : ⟪ ω ⟫) → q x ≡ q y → f x ≡ f y
      qq x y e = ↪-inj {a = Lset (# n)}
        (sym (named (vl x) (mm x) .snd)
          ∙ cong item (inj-toℕ (cong fst (fromFin-inj size _ _ e)))
```

<!--en-->
The chain of identifications is closed by the named entry of the second point, completing the proof that equal names force equal values.
<!--zh-->
同一视链以第二点的被命名条目闭合，完成「名字相等迫使值相等」的证明。
<!--ja-->
同一視の連鎖は、二つ目の点の名指しされた項目で閉じる。名前が等しければ値が等しい、という証明がこれで完成する。
<!--/-->

```agda
          ∙ named (vl y) (mm y) .snd)

```

<!--en-->
For an arbitrary index `w`, `NoInto w` is the proposition that no host-level injection exists from the presentation of `ω` into the presentation of `Lset w`. The next lemma will establish this proposition under the additional hypothesis that `w` belongs to `ω`.
<!--zh-->
对任意指标 `w`，`NoInto w` 是这样一个命题：不存在从 `ω` 的呈现到 `Lset w` 的呈现的宿主层单射。下一条引理将在附加假设 `w∈ω` 下证明这一命题。
<!--ja-->
任意の添字 `w` に対して、`NoInto w` は `ω` の提示から `Lset w` の提示への周囲の水準での単射が存在しないという命題である。次の補題では、`w` が `ω` に属するという追加の仮定のもとで、この命題を証明する。
<!--/-->

```agda
  NoInto : V ℓ → Type ℓ
  NoInto w = (f : ⟪ ω ⟫ → ⟪ Lset w ⟫)
           → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → ⊥₀

```

<!--en-->
The general form follows by transporting the finite case along the membership of `g` in `ω`: a member of `ω` is, merely, a numeral, and the transport moves the whole exclusion statement to the stage of that numeral. The elimination is legitimate because the target is a contradiction.
<!--zh-->
一般形式沿 `g` 在 `ω` 中的隶属搬运有限情形而得：`ω` 的成员仅仅是某个数码，该搬运把整条排除陈述移至该数码的层。由于目标是矛盾命题，消去合法。
<!--ja-->
一般の形は、`g` の `ω` への所属に沿って有限の場合を運ぶことで得られる。`ω` の要素は、単に、ある数項であり、この輸送が排除の主張全体をその数項の段階へ移す。目標が矛盾の命題であるため、消去は正当である。
<!--/-->

```agda
  no-inj-fin : (g : V ℓ) → ⟨ g ∈ˢ ω ⟩ → NoInto g
  no-inj-fin g g∈ω = rec₁ (isPropΠ2 (λ _ _ → isProp⊥))
    (λ { (k , e) → subst NoInto e (FinNo.noinj (lower k)) }) g∈ω
```

<!--en-->
The infinite ordinal `ω` is constructible: its ordinalness feeds the ordinal stage construction.
<!--zh-->
无穷序数 `ω` 是可构造的：其序数性供给序数层构造。
<!--ja-->
無限順序数 `ω` は構成可能である。その順序数性が、順序数の段階の構成を供給する。
<!--/-->

```agda
hω : ⟨ isL ω ⟩
hω = isL-ord ω ω-ord

```

<!--en-->
The stage order of `Lset ω` is implemented as a constructible set `Rω` of coded pairs inside `L`.
<!--zh-->
`Lset ω` 的层序被实现为 `L` 内部由编码对构成的可构造集合 `Rω`。
<!--ja-->
`Lset ω` の段階の順序は、`L` の内部の、符号化された対からなる構成可能な集合 `Rω` として実装される。
<!--/-->

```agda
Rω : SL.S
Rω = relL ω hω ω-ord

```

<!--en-->
The relation specification says that the coded pairs of `Rω` are exactly the ordered pairs of `L`-elements related by the stage order.
<!--zh-->
关系规格说明：`Rω` 的编码对恰是由层序关联的 `L` 元素构成的有序对。
<!--ja-->
関係の仕様は、`Rω` の符号化された対が、段階の順序で関係づけられた `L` の要素の順序対にちょうど一致することを言う。
<!--/-->

```agda
specω : IsRel ω Rω
specω = relL-spec ω hω ω-ord

```

<!--en-->
The endpoint condition recovers stage membership for both endpoints of every related pair. Unfolding the coded pair yields two members of `Lset ω`, and the component equations identify their underlying sets with the endpoints `y` and `x`.
<!--zh-->
端点条件从每个相关对中恢复两个端点的层隶属。展开编码对会得到 `Lset ω` 的两个成员，而分量等式把它们的底层集合分别认同于端点 `y` 与 `x`。
<!--ja-->
端点条件は、関係する各対の両端点について段階への所属を復元する。符号化された対を展開すると `Lset ω` の二つの要素が得られ、成分の等式がそれらの底の集合を端点 `y` と `x` にそれぞれ同一視する。
<!--/-->

```agda
Rsub : (y x : SL.S) → Holds Rω y x
     → ⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩
Rsub y x h = rec₁ isP
  (λ { (_ , h₁) → rec₁ isP
    (λ { (a , h₂) → rec₁ isP
```

<!--en-->
Both memberships are transported along the two component equations supplied by the injectivity of the ordered-pair coding.
<!--zh-->
两个隶属沿有序对编码的单射性所供给的两条分量等式搬运。
<!--ja-->
二つの所属は、順序対の符号化の単射性が供給する、二つの成分の等式に沿って運ばれる。
<!--/-->

```agda
      (λ { (b , (q , _)) →
             subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .fst)) (a .snd)
           , subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .snd)) (b .snd) })
      h₂ })
    h₁ })
```

<!--en-->
The conjunction of the two memberships is a proposition, and the relatedness of the coded pair is produced from the relation specification at the constructible ordered pair.
<!--zh-->
两个隶属的合取是命题；编码对的关联性由可构造有序对处的关系规格产出。
<!--ja-->
二つの所属の連言は命題であり、符号化された対の関係は、構成可能な順序対のもとの関係の仕様から産み出される。
<!--/-->

```agda
  rel
  where
  isP : isProp (⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩)
  isP = isProp× (snd (fst y ∈ˢ Lset ω)) (snd (fst x ∈ˢ Lset ω))
  rel : ⟨ Related ω (pr (fst y) (fst x)) ⟩
```

<!--en-->
The relatedness is transported along the identification of the coded pair with the plain ordered pair of the two underlying sets.
<!--zh-->
关联性沿「编码对与两个底层集的朴素有序对」的同一视搬运。
<!--ja-->
関係は、符号化された対を、二つの底の集合の素の順序対と同一視する輸送に沿って運ばれる。
<!--/-->

```agda
  rel = subst (λ w → ⟨ Related ω w ⟩) (prʟ-fst y x)
    (specω (prʟ y x) .fst
      (subst (λ w → ⟨ w ∈ˢ fst Rω ⟩) (sym (prʟ-fst y x)) h))

```

<!--en-->
The order-type machinery is instantiated at the stage `Lset ω` with the internal relation and its endpoint condition: this fixes the small domain, the internal relation, and the collapse construction of the previous chapter.
<!--zh-->
序型机制在层 `Lset ω` 处、以内部关系及其端点条件实例化：由此固定小定义域、内部关系，以及上一章的塌缩构造。
<!--ja-->
順序型の仕組みは、内部の関係とその端点の条件とともに、段階 `Lset ω` のもとで具体化される。これにより、小さな定義域・内部の関係・そして前章の崩壊の構成が固定される。
<!--/-->

```agda
module OT = Code Lω Rω Rsub using ( module Conjuncts; Dom; _≺_; isProp≺; ≺-in; ≺-out )
```

<!--en-->
The host well order is the stage order carried to the presentation of `Lset ω`, so the abstract well-order machinery can be used on the small index type.
<!--zh-->
宿主良序是搬到 `Lset ω` 的呈现上的层序，于是抽象良序机制可用于该小索引类型。
<!--ja-->
ホストの整列順序は、`Lset ω` の提示に運ばれた段階の順序であり、抽象的な整列順序の仕組みを小さな索引型の上で使える。
<!--/-->

```agda
Wω : SWO ⟪ Lset ω ⟫
Wω = carry (Lset ω) (orderAt ω ω-ord)

```

<!--en-->
Write `a <ω b` for the strict comparison supplied by this well order on the presentation of `Lset ω`. The next two lemmas show that this relation and the internally coded predecessor relation `a OT.≺ b` express the same comparison.
<!--zh-->
把该良序在 `Lset ω` 的呈现上给出的严格比较记作 `a <ω b`。下面两条引理证明，此关系与内部编码的前驱关系 `a OT.≺ b` 表达同一个比较。
<!--ja-->
この整列順序が `Lset ω` の提示上に与える狭義の比較を `a <ω b` と書く。次の二つの補題は、この関係と内部で符号化された先行関係 `a OT.≺ b` が同じ比較を表すことを示す。
<!--/-->

```agda
open SWO Wω using () renaming ( _<∙_ to _<ω_ )

```

<!--en-->
The internal relation and the host stage order agree on the common presentation. The first direction reads an internal predecessor proof `a OT.≺ b` as the host-order comparison `a <ω b`, using the representation theorem for the coded relation.
<!--zh-->
内部关系与宿主层序在共同呈现上相符。第一个方向利用编码关系的表示定理，把内部前驱证明 `a OT.≺ b` 读为宿主序比较 `a <ω b`。
<!--ja-->
内部関係と周囲の段階順序は、共通の提示の上で一致する。最初の向きでは、符号化された関係の表現定理を使い、内部の先行関係の証明 `a OT.≺ b` を周囲の順序比較 `a <ω b` として読み取る。
<!--/-->

```agda
≺→< : (a b : OT.Dom) → a OT.≺ b → a <ω b
≺→< a b k = ixRel-rep ω ω-ord Rω specω a b (OT.≺-out a b k)

```

<!--en-->
Conversely, the filling theorem for the coded relation turns a host-order comparison `a <ω b` into the internal predecessor proof `a OT.≺ b`. These two conversions let the order-theoretic properties of the host relation be transferred to the internal one.
<!--zh-->
反过来，编码关系的填充定理把宿主序比较 `a <ω b` 转换为内部前驱证明 `a OT.≺ b`。借助这两个方向，宿主关系的序论性质可以搬运到内部关系。
<!--ja-->
逆に、符号化された関係の充足定理は、周囲の順序比較 `a <ω b` を内部の先行関係の証明 `a OT.≺ b` へ変換する。この二方向の変換により、周囲の関係がもつ順序論的性質を内部関係へ移せる。
<!--/-->

```agda
<→≺ : (a b : OT.Dom) → a <ω b → a OT.≺ b
<→≺ a b k = OT.≺-in a b (ixRel-fill ω ω-ord Rω specω a b k)

```

<!--en-->
Well-foundedness of the internal relation follows from well-foundedness of the host order. Accessibility is transported point by point: each predecessor inside the internal relation is first converted into a host predecessor.
<!--zh-->
内部关系的良基性由宿主序的良基性得出。可达性逐点搬运：内部关系中的每个前驱先被转换为宿主前驱。
<!--ja-->
内部の関係の整礎性は、ホストの順序の整礎性から従う。到達可能性は点ごとに運ばれる。内部の関係のそれぞれの先行者は、まずホストの先行者に変換されるのである。
<!--/-->

```agda
wfω : WellFounded OT._≺_
wfω m = go (SWO.wf∙ Wω m)
  where
  go : {n : OT.Dom} → Acc _<ω_ n → Acc OT._≺_ n
  go {n} (acc r) = acc (λ n' k → go (r n' (≺→< n' n k)))
```

<!--en-->
Transitivity of the internal relation is likewise transported through the host order: two consecutive internal steps are converted, composed, and converted back.
<!--zh-->
内部关系的传递性同样经宿主序搬运：两个相邻的内部步先转换、再复合、最后转回。
<!--ja-->
内部の関係の推移性も、ホストの順序を通して運ばれる。連なる二つの内部の一歩が変換され、合成され、そして元に戻される。
<!--/-->

```agda

transω : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
transω {a} {b} {c} k k' =
  <→≺ a c (SWO.trans∙ Wω a b c (≺→< a b k) (≺→< b c k'))

```

<!--en-->
For any `a` and `b`, trichotomy of the host well order gives exactly one of three forms: `a <ω b`, equality, or `b <ω a`. The result is expressed as a nested sum so that each comparison can be converted into the matching case for the internal relation.
<!--zh-->
对任意 `a` 与 `b`，宿主良序的三分法给出三种形式之一：`a <ω b`、二者相等或 `b <ω a`。结论写成嵌套和，使每个比较都能转换为内部关系的对应情形。
<!--ja-->
任意の `a` と `b` に対して、周囲の整列順序の三岐性は `a <ω b`、等しい、または `b <ω a` のいずれかを与える。結論を入れ子の直和で表すことで、各比較を内部関係の対応する場合へ変換できる。
<!--/-->

```agda
triω : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
triω a b = go (SWO.tri∙ Wω a b)
  where
  go : TriW (a <ω b) (a ≡ b) (b <ω a)
     → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
```

<!--en-->
Each host case is converted back into the corresponding internal case: less-than, equality, or greater-than.
<!--zh-->
宿主的每种情形都被转换回相应的内部情形：小于、相等或大于。
<!--ja-->
ホストのそれぞれの場合が、対応する内部の場合、すなわち小さい・等しい・大きいへ変換される。
<!--/-->

```agda
  go (lt h) = inl (<→≺ a b h)
  go (eq e) = inr (inl e)
  go (gt h) = inr (inr (<→≺ b a h))

```

<!--en-->
Well-foundedness and transitivity now define the collapse values and their ordinal image `otL`. Trichotomy proves that distinct points have distinct collapse values, so the collapse graph `colTable` satisfies the injectivity clause and yields the code used below.
<!--zh-->
良基性与传递性现在给出塌缩值及其序数像 `otL`。三分法证明不同点具有不同塌缩值，因此塌缩图 `colTable` 满足单射性条款，并给出下文所用的编码。
<!--ja-->
整礎性と推移性から、崩壊値とその順序数像 `otL` が得られる。三岐性により異なる点の崩壊値が異なることが分かるので、崩壊グラフ `colTable` は単射性の条件を満たし、後で使う符号を与える。
<!--/-->

```agda
module C = OT.Conjuncts wfω transω using ( module Inj; col; col-ord; col-out; colTable; otL; otL-out )
module I = C.Inj triω using ( code; col-inj )
```

<!--en-->
The birth-stage family is instantiated at the internal `ω`: every presented member of `Lset ω` has a birth stage in `ω`, ordered by a family relation.
<!--zh-->
诞生层族在内部 `ω` 处实例化：`Lset ω` 的每个被呈现成员在 `ω` 中有一个诞生层，族关系对其排序。
<!--ja-->
誕生段階の族は、内部の `ω` のもとで具体化される。`Lset ω` の提示されたすべての要素は `ω` の中に誕生段階をもち、族の関係がそれを順序づける。
<!--/-->

```agda
private
  module F = Family ω (λ δ _ → orderAt δ) ω-ord using ( _≺_; bornAt )

```

<!--en-->
The unfolded reading of the family relation is proved: at `ω`, the abstractly stated order equals the concrete birth-stage-then-step order.
<!--zh-->
证明族关系的展开读法：在 `ω` 处，抽象陈述的序等于具体的「先生于后步进」之序。
<!--ja-->
族の関係の展開された読みが証明される。`ω` のもとでは、抽象的に述べられた順序は、誕生段階とその次の一歩からなる具体的な順序と等しくなる。
<!--/-->

```agda
  unfoldω : (a b : MemOf (Lset ω))
          → relOf (orderAt ω ω-ord) a b ≡ F._≺_ a b
  unfoldω a b = cong (λ z → relOf (z ω-ord) a b) (orderAt-step ω)

```

<!--en-->
The birth stage of a member is read as an ambient set.
<!--zh-->
成员的诞生层被读作外围集合。
<!--ja-->
要素の誕生段階は、周囲の集合として読まれる。
<!--/-->

```agda
  bAt : MemOf (Lset ω) → V ℓ
  bAt a = F.bornAt a .fst

```

<!--en-->
Every birth stage belongs to the internal `ω`, since the whole family lives below `ω`.
<!--zh-->
每个诞生层都属于内部 `ω`，因为整个族都在 `ω` 之下。
<!--ja-->
すべての誕生段階は内部の `ω` に属する。族の全体が `ω` より下にあるからである。
<!--/-->

```agda
  bAt∈ω : (a : MemOf (Lset ω)) → ⟨ bAt a ∈ˢ ω ⟩
  bAt∈ω a = F.bornAt a .snd

```

<!--en-->
Every birth stage is an ordinal: it is a member of the ordinal `ω`, and members of ordinals are ordinals.
<!--zh-->
每个诞生层都是序数：它是序数 `ω` 的成员，而序数的成员是序数。
<!--ja-->
すべての誕生段階は順序数である。順序数 `ω` の要素であり、順序数の要素は順序数だからである。
<!--/-->

```agda
  bAt-ord : (a : MemOf (Lset ω)) → IsOrd (bAt a)
  bAt-ord a = mem-ord {A = ω} ω-ord (bAt a) (bAt∈ω a)

```

<!--en-->
Every presented member of `Lset ω` belongs to the stage indexed by its own birth stage raised by one: the member's constructibility is transported into that successor stage.
<!--zh-->
`Lset ω` 的每个被呈现成员都属于以其诞生层后继为指数的层：该成员的可构造性被搬运进该后继层。
<!--ja-->
`Lset ω` の提示されたすべての要素は、その自身の誕生段階を一つ上げた段階に属する。要素の構成可能性が、その後続の段階の中へ運ばれるのである。
<!--/-->

```agda
  self-at : (a : MemOf (Lset ω)) → ⟨ a .fst ∈ˢ Lset (sucV (bAt a)) ⟩
  self-at a = birth-mem (a .fst) (Lset→isL ω ω-ord (a .fst) (a .snd))

```

<!--en-->
The step bound says: if `a` precedes `b` in the family order, then the underlying set of `a` belongs to the stage indexed by one plus the birth stage of `b`. In the strictly earlier birth case, the successor comparison is decided by ordinal linearity.
<!--zh-->
步进界说：若 `a` 在族序中先于 `b`，则 `a` 的底层集属于以「`b` 的诞生层加一」为指数的层。在诞生层严格更早的情形，后继比较由序数线性性判定。
<!--ja-->
ステップの上界は次を言う。族の順序で `a` が `b` に先行するなら、`a` の底の集合は、`b` の誕生段階に一つを加えたものが添字づける段階に属する。誕生段階が真に早い場合には、後続の比較が順序数の線形性によって判定される。
<!--/-->

```agda
  step-bound : (a b : MemOf (Lset ω)) → F._≺_ a b
             → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
  step-bound a b (inl h) =
    raise (suc∈or≡ (bAt a) (bAt b) (bAt-ord a) (bAt-ord b) h)
    where
```

<!--en-->
In the strictly earlier-birth branch, ordinal discreteness compares `sucV (bAt a)` directly with `bAt b`. If the successor still lies below `bAt b`, or is equal to it, stage monotonicity carries the known membership of `a` in `Lset (sucV (bAt a))` into `Lset (sucV (bAt b))`.
<!--zh-->
在诞生层严格较早的分支中，序数的离散性直接比较 `sucV (bAt a)` 与 `bAt b`。无论该后继仍低于 `bAt b`，还是恰与之相等，层单调性都把已知的 `a∈Lset (sucV (bAt a))` 搬入 `Lset (sucV (bAt b))`。
<!--ja-->
誕生段階が真に早い分岐では、順序数の離散性によって `sucV (bAt a)` と `bAt b` を直接比較する。この後続がなお `bAt b` より下にある場合も、それと等しい場合も、段階の単調性によって既知の `a∈Lset (sucV (bAt a))` を `Lset (sucV (bAt b))` へ移す。
<!--/-->

```agda
    raise : ⟨ sucV (bAt a) ∈ˢ bAt b ⟩ ⊎ (sucV (bAt a) ≡ bAt b)
          → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
    raise (inl k) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (∈sucV-inl {A = bAt b} {x = sucV (bAt a)} k) (self-at a)
    raise (inr e) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
```

<!--en-->
In the equality subcase `sucV (bAt a) ≡ bAt b`, the proof first places this ordinal in the successor of `bAt b` and then applies stage monotonicity. The other main branch has equal birth stages; there the step-order witness itself contains membership of `a` in the successor stage of their common birth stage, and transport along the equality gives the stated bound.
<!--zh-->
在等式子情形 `sucV (bAt a) ≡ bAt b` 中，证明先把该序数置于 `bAt b` 的后继中，再应用层单调性。另一个主分支中两个诞生层相等；此时步进序见证本身就包含 `a` 属于其公共诞生层的后继层，沿该等式搬运便得到所述界。
<!--ja-->
等式の場合 `sucV (bAt a) ≡ bAt b` には、まずこの順序数を `bAt b` の後続に入れ、それから段階の単調性を適用する。もう一方の主な分岐では誕生段階が等しく、ステップ順序の証人そのものが `a` の共通の誕生段階の後続段階への所属を含む。その等しさに沿って移送すれば、求める上界が得られる。
<!--/-->

```agda
      (subst (λ w → ⟨ sucV (bAt a) ∈ˢ sucV w ⟩) e (self∈sucV (sucV (bAt a))))
      (self-at a)
  step-bound a b (inr (e , u)) =
    subst (λ w → ⟨ a .fst ∈ˢ Lset (sucV w) ⟩) (sym e) (u .fst)

```

<!--en-->
Every point of the internal collapse domain is read as a presented member of `Lset ω`.
<!--zh-->
内部塌缩定义域的每个点都被读作 `Lset ω` 的被呈现成员。
<!--ja-->
内部の崩壊の定義域のすべての点は、`Lset ω` の提示された要素として読まれる。
<!--/-->

```agda
  atIx : OT.Dom → MemOf (Lset ω)
  atIx m = ⟪ Lset ω ⟫↪ m , memOf (Lset ω) m

```

<!--en-->
For a collapse-domain point `p`, the guard index `gOf p` is the successor of the birth stage of the member represented by `p`. The finite stage `Lset (gOf p)` will contain every predecessor of `p`.
<!--zh-->
对塌缩定义域中的点 `p`，护卫指标 `gOf p` 是 `p` 所表示成员的诞生层后继。有限层 `Lset (gOf p)` 将包含 `p` 的每个前驱。
<!--ja-->
崩壊領域の点 `p` に対し、護衛となる添字 `gOf p` は、`p` が表す要素の誕生段階の後続である。有限段階 `Lset (gOf p)` が `p` のすべての先行者を含むことになる。
<!--/-->

```agda
  gOf : OT.Dom → V ℓ
  gOf p = sucV (bAt (atIx p))

```

<!--en-->
Every guard belongs to the internal `ω`, since it is the successor of a member of `ω`.
<!--zh-->
每个护卫层都属于内部 `ω`，因为它是 `ω` 中某成员的后继。
<!--ja-->
どの衛も内部の `ω` の中にある。`ω` の要素の後続だからである。
<!--/-->

```agda
  gOf∈ω : (p : OT.Dom) → ⟨ gOf p ∈ˢ ω ⟩
  gOf∈ω p = ω-limit (bAt (atIx p)) (bAt∈ω (atIx p))

```

<!--en-->
The predecessor bound says that every predecessor `r` of a point `p` presents an ambient element of the finite stage guarded by `p`. The proof transports the step bound through the unfolded reading of the family order.
<!--zh-->
前驱界说：点 `p` 的每个前驱 `r` 都呈现由 `p` 的护卫层所界定层的一个外围元素。证明把步进界穿过族序的展开读法搬运。
<!--ja-->
先行者の上界は、点 `p` のすべての先行者 `r` が、`p` の衛とされる有限の段階の周囲の要素を提示することを言う。証明は、ステップの上界を、族の順序の展開された読みを通して運ぶ。
<!--/-->

```agda
  seg-bound : (p r : OT.Dom) → r OT.≺ p
            → ⟨ ⟪ Lset ω ⟫↪ r ∈ˢ Lset (gOf p) ⟩
  seg-bound p r k =
    step-bound (atIx r) (atIx p) (transport (unfoldω (atIx r) (atIx p)) (≺→< r p k))
```

<!--en-->
A predecessor segment records a predecessor `r` of `p` together with the identification of its collapse value with a given set.
<!--zh-->
前驱段记录 `p` 的一个前驱 `r`，连同其塌缩值与给定集合的同一视。
<!--ja-->
先行者の区間は、`p` の先行者 `r` と、その崩壊の値が与えられた集合と等しいことの同一視を記録する。
<!--/-->

```agda
private
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))

```

<!--en-->
Predecessor segments are propositions: two records with the same collapse value are identified because the collapse is injective on the small domain, the relation is proposition-valued, and the underlying sets form an h-set.
<!--zh-->
前驱段是命题：塌缩在小定义域上单射、关系取值于命题、底层集合构成 h-集合，三者合起来把塌缩值相同的两条记录等同。
<!--ja-->
先行者の区間は命題である。同じ崩壊の値をもつ二つの記録は、崩壊が小さな定義域の上で単射であり、関係が命題値であり、底の集合が h-集合を作ることによって、同一視される。
<!--/-->

```agda
  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ z → isProp× (OT.isProp≺ z p) (setIsSet _ _))
      (I.col-inj r r' (e ∙ sym e'))

```

<!--en-->
Every membership in a collapse value yields a predecessor segment: the truncated reading of the collapse is eliminated into the proposition-valued segment.
<!--zh-->
塌缩值中的每个隶属都给出一个前驱段：塌缩的截断读取被消去到取值于命题的段中。
<!--ja-->
崩壊の値の中の所属はどれも、先行者の区間を与える。崩壊の切り詰められた読みが、命題値の区間の中へ消去されるのである。
<!--/-->

```agda
  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = rec₁ (isPropSeg p b) (λ z → z) (C.col-out p b h)

```

<!--en-->
It remains to show that each ordinal `C.col p` lies below `ω`. Ordinal trichotomy leaves two obstructing possibilities, equality with `ω` and membership of `ω` in the collapse. Both will imply the same inclusion `ω ⊆ C.col p`, so we first prove that such an inclusion would force an impossible injection into the finite stage `Lset (gOf p)`.
<!--zh-->
现在只须证明每个序数 `C.col p` 都低于 `ω`。序数三歧留下两种阻碍情形：它等于 `ω`，或 `ω` 属于该塌缩。二者都会推出同一个包含 `ω ⊆ C.col p`，因此先证明这一包含会迫使一个不可能的单射进入有穷层 `Lset (gOf p)`。
<!--ja-->
残るのは、各順序数 `C.col p` が `ω` より下にあることの証明である。順序数の三分律で妨げとなるのは、`ω` に等しい場合と、崩壊が `ω` を要素として含む場合である。どちらからも同じ包含 `ω ⊆ C.col p` が従うので、まずこの包含が有限段階 `Lset (gOf p)` へのありえない単射を導くことを示す。
<!--/-->

```agda
col-fin : (p : OT.Dom) → ⟨ C.col p ∈ˢ ω ⟩
col-fin p = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
  where
  refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → ⊥₀
  refute sub = no-inj-fin (gOf p) (gOf∈ω p) f f-inj
```

<!--en-->
Assume for contradiction that every element of `ω` belongs to `C.col p`. For a presented element `x` of `ω`, membership in the collapse yields a predecessor `r ≺ p` whose collapse value is the set presented by `x`. The type `Seg` of such predecessors is a proposition, so `seg` may eliminate the truncated membership evidence and `s x` records this uniquely determined predecessor. The bound on the segment places the set represented by `r`, rather than its collapse value, in `Lset (gOf p)`; `fb x` chooses its canonical presentation there.
<!--zh-->
反设 `ω` 的每个元素都属于 `C.col p`。给定 `ω` 的一个呈现元素 `x`，它属于塌缩这一事实给出一个前驱 `r ≺ p`，且 `r` 的塌缩值就是 `x` 所呈现的集合。这样的前驱所成的类型 `Seg` 是命题，因此 `seg` 可以消去截断的隶属证据，而 `s x` 记录这个唯一确定的前驱。前驱段的界把 `r` 所表示的集合，而非它的塌缩值，放入 `Lset (gOf p)`；`fb x` 随后取出该集合在此层中的典范呈现。
<!--ja-->
背理法のため、`ω` のすべての要素が `C.col p` に属すると仮定する。`ω` の提示要素 `x` に対し、崩壊への所属から、崩壊値が `x` の提示する集合に等しい前者 `r ≺ p` が得られる。そのような前者からなる型 `Seg` は命題なので、`seg` は切り詰められた所属の証拠を除去でき、`s x` は一意に定まる前者を記録する。前者区間の界が `Lset (gOf p)` に入れるのは `r` の表す集合であって、その崩壊値ではない。`fb x` はその集合のこの段階での標準的な提示を取り出す。
<!--/-->

```agda
    where
    s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
    s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
    fb : (x : ⟪ ω ⟫)
       → Σ[ m ∈ ⟪ Lset (gOf p) ⟫ ] (⟪ Lset (gOf p) ⟫↪ m ≡ ⟪ Lset ω ⟫↪ (s x .fst))
```

<!--en-->
Thus `f` sends each presented element of `ω` to the presentation, in the common finite stage, of its recovered predecessor. To prove this map injective, suppose `f x = f y`. Equality of these finite-stage indices first gives equality of the sets represented by the two predecessors. The remaining path calculation then recovers equality of the original elements `x` and `y`.
<!--zh-->
于是，`f` 把 `ω` 的每个呈现元素送到共同有穷层中相应前驱的呈现。为证此映射为单射，设 `f x = f y`。这些有穷层索引相等，首先推出两个前驱所表示的集合相等；余下的路径计算再追回原元素 `x` 与 `y` 相等。
<!--ja-->
こうして `f` は、`ω` の各提示要素を、共通の有限段階における対応する前者の提示へ送る。この写像の単射性を示すため `f x = f y` と仮定する。有限段階の添字の等しさから、まず二つの前者が表す集合の等しさが得られ、残る道の計算によって元の要素 `x` と `y` の等しさが復元される。
<!--/-->

```agda
    fb x = fiber (Lset (gOf p)) (seg-bound p (s x .fst) (s x .snd .fst))
    f : ⟪ ω ⟫ → ⟪ Lset (gOf p) ⟫
    f x = fb x .fst
    f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
    f-inj x y e = ↪-inj {a = ω}
```

<!--en-->
Presentation injectivity turns equality of the two values of `f` into equality `rr` of the recovered predecessor indices in `Lset ω`. Applying the collapse function to `rr`, and composing with the equations stored in `s x` and `s y`, shows that the sets presented by `x` and `y` are equal. Injectivity of the presentation of `ω` then gives `x = y`. Hence the assumed inclusion `ω ⊆ C.col p` would produce an injection from `ω` into the finite stage `Lset (gOf p)`.
<!--zh-->
呈现的单射性把 `f` 的两个值相等化为 `Lset ω` 中所恢复前驱索引的等式 `rr`。对 `rr` 应用塌缩函数，再与 `s x`、`s y` 中保存的等式复合，便得到 `x` 与 `y` 所呈现的集合相等；最后由 `ω` 的呈现的单射性得到 `x = y`。因此，假设的包含 `ω ⊆ C.col p` 会产生从 `ω` 到有穷层 `Lset (gOf p)` 的单射。
<!--ja-->
提示の単射性により、`f` の二つの値の等しさは、`Lset ω` で復元された前者の添字の等式 `rr` になる。`rr` に崩壊関数を作用させ、`s x` と `s y` に記録された等式と合成すると、`x` と `y` が提示する集合は等しいと分かる。最後に `ω` の提示の単射性から `x = y` を得る。したがって、仮定した包含 `ω ⊆ C.col p` は、`ω` から有限段階 `Lset (gOf p)` への単射を与えてしまう。
<!--/-->

```agda
      (sym (s x .snd .snd) ∙ cong C.col rr ∙ s y .snd .snd)
      where
      rr : s x .fst ≡ s y .fst
      rr = ↪-inj {a = Lset ω}
        (sym (fb x .snd) ∙ cong ⟪ Lset (gOf p) ⟫↪ e ∙ fb y .snd)
```

<!--en-->
Ordinal trichotomy compares `C.col p` with `ω`. If the collapse is already a member of `ω`, the desired conclusion is immediate. If `C.col p = ω`, transport along that equality makes every element of `ω` an element of the collapse. This is precisely the inclusion refuted above, since it would yield the impossible injection into `Lset (gOf p)`.
<!--zh-->
序数三歧比较 `C.col p` 与 `ω`。若塌缩已经属于 `ω`，结论立即成立。若 `C.col p = ω`，沿此等式运输便使 `ω` 的每个元素都属于该塌缩。这恰是上文所反驳的包含，因为它会给出到 `Lset (gOf p)` 的不可能单射。
<!--ja-->
順序数の三分律で `C.col p` と `ω` を比較する。崩壊がすでに `ω` の要素なら、求める結論は直ちに得られる。`C.col p = ω` なら、この等式に沿う輸送によって `ω` のすべての要素が崩壊の要素になる。これは上で反駁した包含そのものであり、`Lset (gOf p)` へのありえない単射を与えてしまう。
<!--/-->

```agda

  go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
  go (inl k) = k
  go (inr (inl e)) =
    ⊥₀-rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
  go (inr (inr ω∈c)) =
```

<!--en-->
In the remaining case `ω ∈ C.col p`. Since `C.col p` is an ordinal and therefore transitive, every element of `ω` then belongs to `C.col p`. This again supplies the forbidden inclusion and closes the last trichotomy branch. Consequently every collapse value `C.col p` is a member of `ω`.
<!--zh-->
余下情形为 `ω ∈ C.col p`。由于 `C.col p` 是序数，因而具有传递性，`ω` 的每个元素随即都属于 `C.col p`。这再次给出被禁止的包含并排除三歧性的最后一支。因此，每个塌缩值 `C.col p` 都属于 `ω`。
<!--ja-->
残る場合は `ω ∈ C.col p` である。`C.col p` は順序数であり、したがって推移的なので、`ω` のすべての要素も `C.col p` に属する。これも禁止された包含を与え、三分律の最後の枝が閉じる。ゆえに、すべての崩壊値 `C.col p` は `ω` の要素である。
<!--/-->

```agda
    ⊥₀-rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))

```

<!--en-->
The order-type image is therefore contained in `ω`. Its outward reading supplies, under propositional truncation, an index `b` and an equation identifying a given image member `z` with `C.col b`. Because the target assertion `z∈ω` is a proposition, this witness may be eliminated there; transport of `col-fin b` along the equation proves the required membership. This establishes only `C.otL ⊆ ω`, not the reverse inclusion.
<!--zh-->
因此，序型像包含于 `ω`。其向外读法在命题截断下给出索引 `b`，以及把给定像元素 `z` 认同于 `C.col b` 的等式。目标断言 `z∈ω` 是命题，故可向其中消去该见证；沿等式搬运 `col-fin b` 即得所需隶属。这里仅证明 `C.otL ⊆ ω`，并未证明反向包含。
<!--ja-->
したがって、順序型の像は `ω` に含まれる。その外向きの読みは、命題的切り詰めのもとで、添字 `b` と、与えられた像の要素 `z` を `C.col b` と同一視する等式を与える。目標の命題 `z∈ω` は命題なので、そこへこの証人を除去でき、`col-fin b` を等式に沿って移送すれば求める所属が得られる。ここで示すのは `C.otL ⊆ ω` だけであり、逆向きの包含ではない。
<!--/-->

```agda
otL⊆ω : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ ω ⟩
otL⊆ω z h = rec₁ (snd (z ∈ˢ ω))
  (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ ω ⟩) e (col-fin b) })
  (C.otL-out z h)
```

<!--en-->
The collapse table gives a coded injection from `L_ω` into its image `C.otL`, and the proved containment gives a coded inclusion from `C.otL` into `ωʟ`. Their composition yields `limit-stage-counted : InjL Lω ωʟ`. Thus the formal conclusion is the propositionally retained existence of an internal injection `L_ω ↪ ω`; no surjection, bijection, or equality `C.otL=ω` is asserted. Later stage counts use this result as their base injection.
<!--zh-->
塌缩表给出从 `L_ω` 到其像 `C.otL` 的编码单射，而已经证明的包含给出从 `C.otL` 到 `ωʟ` 的编码包含。复合二者得到 `limit-stage-counted : InjL Lω ωʟ`。因此，形式结论是内部单射 `L_ω ↪ ω` 的命题性存在；这里不声称满射、双射，也不声称 `C.otL=ω`。后续层计数把此结果用作基础单射。
<!--ja-->
崩壊表は `L_ω` からその像 `C.otL` への符号化された単射を与え、証明した包含は `C.otL` から `ωʟ` への符号化された包含を与える。両者を合成すると `limit-stage-counted : InjL Lω ωʟ` が得られる。したがって形式的な結論は、内部単射 `L_ω ↪ ω` の命題的に保持された存在である。全射、全単射、あるいは等式 `C.otL=ω` は主張していない。後の段階計数はこの結果を基底単射として用いる。
<!--/-->

```agda
limit-stage-counted : LimitStageCounted
limit-stage-counted =
  injl-trans Lω C.otL ωʟ ∣ C.colTable , I.code ∣₁
    (inclusion-coded C.otL ωʟ otL⊆ω)
```
