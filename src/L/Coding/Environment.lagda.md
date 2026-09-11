<!--en-->
# Finite environments as set-coded graphs

A satisfaction clause of the first-order language speaks about the value of a variable, but it can only quantify over sets. So before satisfaction can be computed inside set theory, a variable assignment itself must become a set. This chapter performs that encoding: a finite assignment, a function from variable indices to sets of `V ℓ`, is represented by its graph, the set of ordered pairs of the numeral for an index with the value there.

The encoding is designed so that lookup inside the graph is exact. Because the key side consists of numerals, and numerals are injective, a pair sitting at the key for `i` in the graph has as its second component exactly the value at `i`, and nothing else. That functionality statement is the main lemma here.

The second concern is extension. When satisfaction descends under a quantifier, the new value is placed at index zero and every old index moves up by one; on the key side this is precisely the von Neumann successor. The chapter therefore builds bounded formulas that say, in membership alone, that one index is the successor of another, that one pair is obtained from another by shifting its key, and finally that a whole set is the graph of the extended assignment. Each of these is proved as an adequacy statement: satisfaction of the formula is a path of truth values to the corresponding external fact about sets, and the graphs involved are compared by extensionality, member by member, never by selecting witnesses out of the truncated membership data.
<!--zh-->
# 作为集合编码图的有穷环境

一阶语言的满足子句谈论变元的取值，却只能对集合作量化。因此，要使满足关系能在集合论内部被计算，变元赋值本身必须先成为一个集合。本章完成这一编码：一个有穷赋值，即从变元序号到 `V ℓ` 中集合的函数，由它的图表示，也就是「序号的数码与该处取值」之对的集合。

这一编码的设计目标是图中的查值精确。由于键的一侧由数码构成，而数码是单射的，坐在键 `i` 处的那个对的第二分量恰为 `i` 处的值，别无他物。这条函数性命题是本章的主引理。

第二个关注点是扩张。当满足关系下降到量词之下时，新值被放在索引零处，每个旧索引上移一位；在键的一侧，这恰是 von Neumann 后继。故本章构造若干有界公式，仅凭隶属说出：一个索引是另一个的后继；一个对是把另一个的键移位后得到的；以及最终，一个集合是扩张后赋值的图。每一条都以充分性命题的形式证明：公式的满足是一条真值路径，通向关于集合的相应外部事实，而所涉的图都靠外延性逐成员比较，从不从截断的隶属数据中挑选见证。
<!--ja-->
# 集合で符号化した有限環境

一階言語の充足の各節は変数の値について語りますが、量化できるのは集合の上だけです。したがって充足関係を集合論の内部で計算するには、変数割当てそのものが先に集合にならなければなりません。本章はこの符号化を行います。すなわち、変数の添字から `V ℓ` の集合への関数という有限な割当てを、そのグラフ、つまり「添字の数項とそこでの値」の対の集合として表します。

この符号化の設計目標は、グラフの中での参照を正確にすることです。鍵の側が数項からなり、数項が単射であるため、鍵 `i` の位置に座る対の第二成分は `i` での値にちょうど等しく、それ以外の何ものでもありません。この関数性の主張が本章の主補題です。

第二の関心事は拡張です。充足が量化子の内側へ降りるとき、新しい値は添字 0 に置かれ、すべての旧添字は一つ上へ動きます。鍵の側では、これはまさに von Neumann 後者です。そこで本章は、所属だけを用いて、一方の添字が他方の後者であること、ある対が他の対の鍵をずらして得られること、そして最後に、ある集合が拡張後の割当てのグラフであることを述べる有界論理式を組み立てます。それぞれは妥当性の主張として証明されます。論理式の充足は真理値のパスであり、集合についての対応する外側の事実へ通じており、そこで扱われるグラフは外延性によって一要素ずつ比較され、切り捨てられた所属データから証人を選び出すことは決してありません。
<!--/-->

<!--en-->
Everything in this chapter takes place at one fixed universe level `ℓ`: the sets being manipulated are elements of `V ℓ`, and the formulas of the language quantify over those sets. Keeping the level as an explicit parameter means the whole construction can be instantiated wherever a hierarchy at that level is available.
<!--zh-->
本章的一切都在一个固定的宇宙层级 `ℓ` 上进行：所操作的集合是 `V ℓ` 的元素，语言中的公式对这些集合作量化。把层级作为显式参数，意味着整个构造可以在任何拥有该层级的地方被实例化。
<!--ja-->
本章のすべてのことは、固定された一つの宇宙レベル `ℓ` の上で行われます。操作される集合は `V ℓ` の要素であり、言語の論理式はそれらの集合の上で量化します。レベルを明示的なパラメータとして保つことで、この構成全体は、そのレベルの階層が利用できるどこでもインスタンス化できます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Environment {ℓ : Level} where

open import FOL.Syntax using ( var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈; ⊥̇ )
```

<!--en-->
The chapter works inside the bounded fragment of the first-order language: a Δ₀ formula is one whose every quantifier is bounded by a variable of the environment, so its satisfaction under an assignment depends only on membership in the exhibited bounding sets. Two host-level facts do the mathematical work of the encoding. The Kuratowski pair `pr` is injective, so a pair determines its components; and the numerals `# n` are injective, so a numeral determines its index. Between them, these two injections are what make the graph of an assignment behave like the graph of a function.
<!--zh-->
本章在一阶语言的有界片段内工作：Δ₀ 公式指每个量词都以环境中的某个变元为界，故其满足只依赖于已给出的界定集合中的隶属。编码在数学上依赖两条宿主层事实：Kuratowski 对 `pr` 是单射的，故一个对决定其分量；数码 `# n` 是单射的，故一个数码决定其序号。这两条单射性合在一起，使一个赋值的图表现出函数图的行为。
<!--ja-->
本章は一階言語の有界な断片の中で作業します。Δ₀ 論理式とは、すべての量化子が環境の変数によって有界化されている論理式であり、その充足は提示された界定集合への所属のみに依存します。符号化の数学的な仕事を担うのは、ホスト側の二つの事実です。Kuratowski 対 `pr` が単射であること、すなわち対がその成分を決めること。そして数項 `# n` が単射であること、すなわち数項がその添字を決めることです。この二つの単射性が合わさって、割当てのグラフに関数のグラフとしての振る舞いを与えます。
<!--/-->

```agda
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-∀∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
```

<!--en-->
The bounded reader `prAt`, proved adequate in the chapter on pair formulas, says of a set at a given variable slot that it is the Kuratowski pair of the sets at two other slots. Its adequacy lemma and the two introduction rules placing a component inside a pair are reused here directly, since a shifted entry is still a Kuratowski pair, only with a moved key. The binary sum type serves on the host side wherever a formula produces a disjunction: a value is one thing or another, recorded as a choice of side without claiming uniqueness of the witness.
<!--zh-->
有界读式 `prAt` 在配对公式一章中已被证明是充分的，它断言给定变元槽位处的集合是另外两个槽位处的集合的 Kuratowski 对。本章直接复用其充分性引理，以及把一个分量放入对内的两条引入规则，因为移位后的条目仍是 Kuratowski 对，只是键被移动了。宿主侧使用二元和类型的地方，对应公式产生析取之处：一个值是此物或彼物，只记录取了哪一侧，不断言见证唯一。
<!--ja-->
有界な読み取り `prAt` は対の論理式の章で妥当であることが証明されており、指定された変数スロットの集合が、他の二つのスロットの集合の Kuratowski 対であることを述べます。ここでは、その妥当性補題と、成分を対の内側に置く二つの導入規則をそのまま再利用します。ずらされた項目もまた Kuratowski 対であり、鍵が動いただけだからです。ホスト側で二元の直和型が使われるのは、論理式が選言を生む場所に対応します。値がこれかあれかであることを、どちらの側かの選択として記録し、証人の一意性を主張しません。
<!--/-->

```agda
open import L.Coding.PairFormulas {ℓ}
  using ( prAt; prAt-adequate; prChar-fwd; prChar-bwd
        ; ∈pair-introL; ∈pair-introR )

open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Sum as Sum
```

<!--en-->
Membership in a set of the hierarchy is a proposition, so a proof that some entry of the graph is related to a given pair is always a *merely exists*: it records that a witness exists without providing it as ordinary data. Eliminating such a truncation is legitimate only into a proposition-valued target, and no chosen witness can be recovered from it globally. Whenever two propositions are identified in this chapter, the identification is built by `⇔toPath`, which turns an if-and-only-if into a path between truth values; that is the shape every adequacy lemma here takes.
<!--zh-->
层级中集合的隶属是一个命题，因此「图中某个条目与给定的对相关」的证明总是**仅仅存在**：它记录见证存在，却不把它当作普通数据提供。这种截断只能消除到取值为命题的目标中，且无法由此整体恢复出一个被选定的见证。本章凡辨认两个命题为同一，都经 `⇔toPath` 完成，它把一个当且仅当变成真值之间的路径；这里的每条充分性引理都是这个形状。
<!--ja-->
階層の集合への所属は命題であるため、「グラフのある項目が与えられた対と関係する」という証明は常に「単に存在する」という形をとります。証人が存在することは記録されますが、通常のデータとして与えられるわけではありません。この切り捨てを消除できるのは命題値の対象へのみであり、そこから全体として選ばれた証人を取り戻すことはできません。本章で二つの命題が同一視されるときは、常に `⇔toPath` によって行われます。これは同値を真理値の間のパスに変えるもので、ここにある各妥当性補題はみなこの形をしています。
<!--/-->

```agda
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as E hiding ( elim )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
The ambient universe is the cubical cumulative hierarchy. A set is introduced as `sett A f`, an index type together with a family of elements, and its membership relation is truncated like any other membership in this setting. The principle `extensionality` says that two sets with the same members are equal as paths. This is the tool by which encoded graphs will be compared: to show that one candidate graph equals another, one proves, for each element, that membership in the first is a path of truth values away from membership in the second.
<!--zh-->
背景宇宙是 cubical 累积层级。集合以 `sett A f` 引入，即一个索引类型配一个元素族，其隶属关系与该设定中其他隶属一样是截断的。外延性原理断言：成员相同的两个集合作为路径相等。这正是比较编码图所用的工具：要证明一个候选图等于另一个，只需对每个元素证明，属于前者的命题与属于后者的命题相差一条真值路径。
<!--ja-->
背景となる宇宙は cubical 累積階層です。集合は `sett A f` として導入されます。これは索引型と要素の族の組であり、その所属関係はこの設定における他の所属と同様に切り捨てられます。外延性の原理は、同じ要素を持つ二つの集合がパスとして等しいと述べます。符号化されたグラフの比較はまさにこの道具によって行われます。ある候補グラフが別のグラフに等しいことを示すには、各要素について、一方への所属という命題が他方への所属という命題と真理値のパス一本分しか違わないことを証明すればよいのです。
<!--/-->

```agda
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality )
```

<!--en-->
The constructions of the hierarchy supply the pieces the encoding uses: the empty set, singletons, the unordered pair `⁅_,_⁆`, and the numerals. The numeral recursion is the key point: `# 0` is `∅` and `# (suc n)` is `sucV (# n)`, the von Neumann successor. So incrementing an index and taking the successor of its key are the same operation, which is exactly why extending an environment can be described by a bounded formula. On the semantic side, truth values are propositions packaged with proofs of propositionhood, so the satisfaction of a formula is itself a proposition and can be identified with an external set-theoretic statement by a path.
<!--zh-->
层级的构造给出编码所用的材料：空集、单点集、无序对 `⁅_,_⁆`，以及数码。数码的递归定义是关键：`# 0` 是 `∅`，`# (suc n)` 是 `sucV (# n)`，即 von Neumann 后继。于是「序号加一」与「键取后继」是同一个运算，这正是环境扩张能够被有界公式描述的原因。在语义一侧，真值是伴随命题性证明的命题，故公式的满足本身是一个命题，可以经一条路径与外部的集合论陈述相等同。
<!--ja-->
階層の構成は、符号化が使う材料を供給します。空集合、単集合、非順序対 `⁅_,_⁆`、そして数項です。ここで鍵となるのは数項の再帰的定義です。`# 0` は `∅` であり、`# (suc n)` は `sucV (# n)`、つまり von Neumann 後者です。したがって「添字を一つ進めること」と「鍵の後者を取ること」は同じ操作であり、これこそ環境の拡張が有界論理式で記述できる理由です。意味論の側では、真理値は命題性の証明を伴う命題なので、論理式の充足それ自体が命題であり、一つのパスによって外側の集合論的な主張と同一視できます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
```

<!--en-->
Finally, the satisfaction relation `_⊨_` and the term interpretation `⟦_⟧` are taken over the carrier `V ℓ` itself, with the identity embedding of constants. An environment for a formula of arity `n` is then an honest function `(V ℓ) ^ n`, a finite tuple of sets. What this chapter encodes is the assignment carried inside certificate data, not this semantic carrier: the tuple form is what the semantics evaluates, while the graph form is what certificates can store and manipulate as a single set.
<!--zh-->
最后，满足关系 `_⊨_` 与项解释 `⟦_⟧` 取在载体 `V ℓ` 自身上，常元解释为恒等。于是元数为 `n` 的公式的环境就是真正的函数 `(V ℓ) ^ n`，即有穷的集合组。本章编码的是证书数据所携带的赋值，而非这个语义载体：组形式是语义求值所用的，图形式才是证书能够作为单个集合存储与操作的。
<!--ja-->
最後に、充足関係 `_⊨_` と項の解釈 `⟦_⟧` は、台となる集合として `V ℓ` 自身の上に、定数の恒等解釈とともに取られます。したがって項数 `n` の論理式に対する環境とは、正しくは関数 `(V ℓ) ^ n`、すなわち集合の有限な組です。本章が符号化するのは、証明書データが担う割当てであって、この意味論の台となる集合ではありません。組の形は意味論が評価する対象であり、グラフの形こそが証明書が一つの集合として保管し操作できる対象です。
<!--/-->

```agda
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## The graph of an environment

An assignment `g : Fin n → V ℓ` becomes the set `env g` whose entry at the key for index `i` is the ordered pair of the numeral `# (toℕ i)` with the value `g i`. The section proves the statement that makes this representation usable: `lookup-spec` identifies membership of a pair at key `i` in `env g` with the proposition that its second component equals `g i`.

Membership in `env g` is truncated, as all hierarchy membership is; the point of `lookup-spec` is that this truncated fiber data nevertheless determines the value exactly.
<!--zh-->
## 环境的图

赋值 `g : Fin n → V ℓ` 成为集合 `env g`，其在索引 `i` 的键处的条目是数码 `# (toℕ i)` 与值 `g i` 的有序对。本节证明使这一表示可用的命题：`lookup-spec` 把「键 `i` 处的对属于 `env g`」等同于「该对的第二分量等于 `g i`」这一命题。

与其他层级隶属一样，`env g` 中的隶属是截断的；`lookup-spec` 的要点在于：这截断的纤维数据仍然精确地决定取值。
<!--ja-->
## 環境のグラフと参照

割当て `g : Fin n → V ℓ` は集合 `env g` になります。添字 `i` の鍵の位置にある項目は、数項 `# (toℕ i)` と値 `g i` の順序対です。この節は、この表現を使い物にする主張を証明します。`lookup-spec` は、「鍵 `i` の対が `env g` に属する」という命題を、「その対の第二成分が `g i` に等しい」という命題と同一視するのです。`env g` への所属は、他の階層の所属と同様に切り捨てられています。`lookup-spec` の要点は、この切り捨てられたファイバーデータであっても、値を正確に決定するという点にあります。
<!--/-->

<!--en-->
The gathering is an instance of the set constructor `sett`, which takes an index type and a family of elements. The finite index type `Fin n` lives below level `ℓ`, so it is lifted first; `Lift` adjusts only the universe, and `lower` recovers the index. Each index `li` then contributes one entry, the pair of the numeral for its index with the value of `g` there. The entries themselves are ordinary data; it is only membership in the resulting set that is truncated. The index is turned into a key `# (toℕ i)` rather than used directly, because the formula language must be able to talk about keys, and what formulas talk about are sets, here the numerals.
<!--zh-->
这一汇集是集合构造子 `sett` 的实例，它取一个索引类型与一个元素族。有穷索引类型 `Fin n` 层级低于 `ℓ`，故先提升；`Lift` 只调整宇宙，`lower` 取回索引。于是每个索引 `li` 贡献一个条目，即其序号的数码与 `g` 在该处的值配成的对。条目本身是普通数据；被截断的只是最终集合中的隶属。索引之所以换成键 `# (toℕ i)` 而非直接使用，是因为公式语言必须能够谈论键，而公式所谈论的是集合，在这里就是数码。
<!--ja-->
この集め方は集合の構成子 `sett` のインスタンスであり、索引型と要素の族を受け取ります。有限な索引型 `Fin n` はレベル `ℓ` より下に住むので、先に持ち上げます。`Lift` は宇宙を調整するだけであり、`lower` が索引を取り戻します。そして各索引 `li` は一つの項目、すなわちその添字の数項と `g` のそこでの値の対に寄与します。項目そのものは通常のデータであり、切り捨てられるのは結果の集合への所属だけです。索引をそのまま使わず鍵 `# (toℕ i)` に変えるのは、論理式言語が鍵について語えなければならず、論理式が語る対象は集合、ここでは数項だからです。
<!--/-->

```agda
env : ∀ {n} → (Fin n → V ℓ) → V ℓ
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))

```

<!--en-->
The graph is *functional*: a pair belongs to `env g` at key `i` exactly when its second component is the value `g i`. This is an extensional statement about membership, and it is what makes the encoding usable for lookup rather than merely definable.

The argument reads off the three layers of the key. The witnessing entry is a Kuratowski pair, and the pair is injective, so its key equals the key asked about. The keys are numerals, and numerals are injective, so the underlying indices agree as natural numbers. Finally `Fin n` embeds in the naturals, so the two indices are the same index, and the value component says it holds `g i`. The reverse direction simply exhibits the entry at `i` itself.
<!--zh-->
这个图是**函数性的**：一个对属于 `env g` 在键 `i` 处，恰当其第二分量为值 `g i`。这是关于隶属的外延陈述，也正是这个编码不只可定义、而且可用于查值的原因。

论证沿着键的三个层次展开。作证的条目是一个 Kuratowski 对，而对是单射的，故其键等于所问的键。键是数码，数码是单射的，故底层的序号作为自然数相等。最后 `Fin n` 嵌入自然数，故两个序号是同一个索引，值分量便说明那里放着 `g i`。反向只需展示 `i` 处的条目本身。
<!--ja-->
このグラフは**関数的**です。すなわち、ある対が鍵 `i` の位置で `env g` に属するのは、その第二成分が値 `g i` であるとき、そのときに限ります。これは所属についての外延的な主張であり、この符号化が単に定義可能であるだけでなく参照に使える理由でもあります。

議論は鍵の三つの層に沿って進みます。証拠となる項目は Kuratowski 対であり、対は単射なので、その鍵は問われた鍵と等しくなります。鍵は数項であり、数項は単射なので、根底にある添字は自然数として一致します。最後に `Fin n` は自然数へ埋め込まれるので、二つの添字は同じ索引であり、値の成分はそこに `g i` があることを示します。逆方向は `i` の項目そのものを示すだけです。
<!--/-->

<!--en-->
The statement is an equality of propositions: membership of the pair at key `i` in the graph is the proposition `v ≡ g i`, packaged with its proof of propositionhood, which comes from the fact that `V ℓ` is an h-set. An equivalence between propositions converts into a path of truth values, so the lemma is proved from two implications, one in each direction.
<!--zh-->
陈述是命题的等式：键 `i` 处的对属于图，这一命题恰为 `v ≡ g i`，并附有其命题性的证明，它来自 `V ℓ` 是 h-集这一事实。命题之间的等价可转换为真值之间的路径，故引理由两个方向各一的蕴含拼成。
<!--ja-->
主張は命題の等式です。鍵 `i` の対がグラフに属するという命題は、ちょうど `v ≡ g i` であり、その命題性の証明を伴います。これは `V ℓ` が h-集合であることから来ます。命題の間の同値は真理値の間のパスに変換できるので、補題は各方向一つずつの二つの含意から組み立てられます。
<!--/-->

```agda
lookup-spec : ∀ {n} (g : Fin n → V ℓ) (i : Fin n) (v : V ℓ)
  → (pr (# (toℕ i)) v ∈ env g) ≡ ((v ≡ g i) , setIsSet v (g i))
lookup-spec {n} g i v = ⇔toPath fwd bwd
  where
  step : (lj : Lift {ℓ-zero} {ℓ} (Fin n))
```

<!--en-->
The forward direction works on a truncated witness, so the case analysis is factored into an ordinary function on an explicit entry. Its input is a path saying that some entry of the graph equals the pair asked about, and its output is the goal `v ≡ g i`. Since the goal is a proposition, eliminating the truncation into it is legitimate; no entry is extracted into ordinary data.
<!--zh-->
正向作用于被截断的见证，故情形分析被分解为显式条目上的一个普通函数。其输入是一条路径，断言图中某个条目等于所问的对；其输出即目标 `v ≡ g i`。由于目标是命题，把截断消入其中是合法的；没有任何条目被提取为普通数据。
<!--ja-->
順方向は切り捨てられた証拠に作用するので、場合分けは明示的な項目上の通常の関数として切り出されます。入力は、グラフのある項目が問われた対と等しいというパスであり、出力は目標の `v ≡ g i` です。目標が命題であるため、切り捨てをそこへ消去することは正当であり、項目が通常のデータとして取り出されることはありません。
<!--/-->

```agda
       → pr (# (toℕ (lower lj))) (g (lower lj)) ≡ pr (# (toℕ i)) v
       → v ≡ g i
  step lj e = sym (ps .snd) ∙ cong g (inj-toℕ (#-inj′ (ps .fst)))
    where
    ps : (# (toℕ (lower lj)) ≡ # (toℕ i)) × (g (lower lj) ≡ v)
```

<!--en-->
Injectivity of the pair splits the assumed equality into a path of keys and a path of values. The reversed value path is one half of the goal. The key path says the two numerals agree; injectivity of numerals together with the embedding into the naturals turns that into equality of the indices themselves, and applying `g` gives the other half. The backward direction exhibits the entry at `i` directly: the truncated witness is the lifted index, and the path is filled by applying the pair constructor to the reversed assumption. No canonical witness is chosen, and uniqueness of the witness is not claimed.
<!--zh-->
对的单射性把假设的等式拆成键的路径与值的路径。值路径取反向即目标的一半。键路径说两个数码相符；数码的单射性连同到自然数的嵌入把它化为序号本身的相等，再用 `g` 作用得到另一半。反向直接展示 `i` 处的条目：截断见证是提升后的索引，路径由对构造子作用于反向假设填充。这里没有挑选任何典范见证，也不主张见证唯一。
<!--ja-->
対の単射性が仮定された等式を、鍵のパスと値のパスに分解します。値のパスを逆向きにしたものが目標の半分です。鍵のパスは二つの数項が一致することを言い、数項の単射性と自然数への埋め込みがそれを添字自身の等式に変え、`g` を適用して残りの半分を得ます。逆方向は `i` の項目を直接示します。切り捨てられた証拠は持ち上げられた索引であり、パスは対の構成子を逆向きの仮定に適用して埋められます。正準な証拠は選ばれず、証拠の一意性も主張されません。
<!--/-->

```agda
    ps = pr-inj e
  fwd : ⟨ pr (# (toℕ i)) v ∈ env g ⟩ → v ≡ g i
  fwd = PT.rec (setIsSet v (g i)) (λ { (lj , e) → step lj e })
  bwd : v ≡ g i → ⟨ pr (# (toℕ i)) v ∈ env g ⟩
  bwd e = ∣ lift i , cong (pr (# (toℕ i))) (sym e) ∣₁
```

<!--en-->
## Recognizing successor indices

`sucAt i j` is a bounded formula saying that the value at `j` is the von Neumann successor of the value at `i`; `sucAt-adequate` proves that satisfaction of the formula under an environment is exactly this equality of values.

The extension of an environment shifts every index up by one, and on numerals that shift is the von Neumann successor. So the certificate machinery, which descends under a binder, must be able to say "this index is the successor of that one". The language has no successor symbol, so the relation is said with membership alone, in three clauses: the smaller belongs to the larger, everything belonging to the smaller belongs to the larger, and everything belonging to the larger merely belongs to the smaller or equals it.
<!--zh-->
## 识别后继索引

有界公式 `sucAt i j` 表示 `j` 处的值是 `i` 处的值的 von Neumann 后继；`sucAt-adequate` 证明该公式在环境下的满足恰好就是这两个值的相等。

环境的扩张把每个序号上移一位，而在数码上这一移位就是 von Neumann 后继。因此要下降到约束之下的证书机制，必须能说出「这个序号是那个的后继」。语言中没有后继符号，故该关系只用隶属来说，分三条子句：小者属于大者；属于小者的一切都属大者；而属于大者的一切仅仅属于小者或与之相等。
<!--ja-->
## 後者となる添字を認識する

有界論理式 `sucAt i j` は、`j` での値が `i` での値の von Neumann 後者であることを表します。`sucAt-adequate` は、環境の下でのこの論理式の充足が、ちょうどこの二つの値の等しいことであることを証明します。

環境の拡張はすべての添字を一つずつずらし、数項の上ではこのずれが von Neumann 後者にあたります。したがって、束縛子の内側へ降りていく証明書の機構は、「この添字はあの添字の後者である」と言えなければなりません。言語には後者の記号がないため、この関係は所属だけを用いて三つの節で述べられます。小さい方が大きい方に属すること、小さい方に属するすべてが大きい方に属すること、そして大きい方に属するすべてが、命題的に小さい方に属するかそれと等しいかのいずれかであることです。
<!--/-->

<!--en-->
Three bounded clauses do it: the smaller set belongs to the larger; membership in the smaller transfers into the larger; and membership in the larger is merely classified, as belonging to the smaller or being the smaller itself. The bounded quantifiers bind `var zero`, and inside a quantifier body every other variable is read at its shifted slot, so `var (suc i)` in the body refers to the value that `var i` had before descending. The second and third clauses say exactly that the larger set has no members beyond those of the smaller together with the smaller itself, which is the extensional content of being its successor. Boundedness is recorded separately by `Δ₀-sucAt`: conjunction, bounded universal quantification, and the leaves, membership and equality, all preserve Δ₀.
<!--zh-->
三条有界子句即可做到：小者属于大者；小者中的隶属可转移到大者中；而大者中的隶属只被**仅仅**分类，为属于小者或等于小者。有界量词约束 `var zero`，量词体内的其余变元按移位后的槽位读取，故体内的 `var (suc i)` 指的正是下降前 `var i` 的值。第二、三条子句恰说明：大者除小者的成员与小者自身之外别无成员，这正是「是其后继」的外延内容。有界性由 `Δ₀-sucAt` 单独记录：合取、有界全称量词，以及叶子的隶属与相等，都保持 Δ₀。
<!--ja-->
三つの有界な条件でそれができます。小さい方が大きい方に属すること、小さい方への所属が大きい方へ移ること、そして大きい方への所属は切り捨てられた形で分類され、小さい方に属するか小さい方と等しいかのいずれかであることです。有界量化子は `var zero` を束縛し、量化子の本体では他の変数はずらしたスロットで読まれるため、本体の `var (suc i)` は降りる前の `var i` の値を指します。第二と第三の節は、大きい方が小さい方の要素と小さい方自身のほかに要素を持たないことを、まさに述べており、これがその後者であることの外延的な内容です。有界性は `Δ₀-sucAt` によって別途記録されます。連言、有界な全称量化、そして葉にあたる所属と等式は、いずれも Δ₀ を保ちます。
<!--/-->

```agda
sucAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
sucAt i j = (var i ∈̇ var j)
         ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
         ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

Δ₀-sucAt : ∀ {n} (i j : Fin n) → Δ₀ (sucAt i j)
```

<!--en-->
The adequacy proof rests on a host-level characterization, stated first at the level of sets. It says that the three formula clauses, read as facts about sets `I` and `J`, hold exactly when `J` and `sucV I` are equal as sets.
<!--zh-->
充分性证明建立在集合层面的宿主级刻画之上。它说：把三条公式子句读作关于集合 `I` 与 `J` 的事实，它们成立恰当 `J` 与 `sucV I` 作为集合相等时。
<!--ja-->
妥当性の証明は、まず集合のレベルで述べたホスト側の特徴づけに依拠します。それは、三つの論理式の節を集合 `I` と `J` についての事実として読んだとき、それらが成り立つのは、`J` と `sucV I` が集合として等しいとき、ちょうどそのときだというものです。
<!--/-->

```agda
Δ₀-sucAt i j = δ-∧ δ-∈ (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ (δ-∨ δ-∈ δ-≐)))

private
  suc-char : (I J : V ℓ)
    → ⟨ I ∈ J ⟩
    → ((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
```

<!--en-->
The forward lemma takes the three clauses as hypotheses, now at the level of sets: `I` is a member of `J`, membership in `I` transfers into `J`, and every member of `J` is merely in `I` or equal to `I`. Its conclusion is a path `J ≡ sucV I`, a genuine equality of sets, not merely a biconditional of memberships.
<!--zh-->
正向引理把三条子句作为假设，落在集合层面：`I` 属于 `J`；`I` 中的隶属可转移到 `J` 中；`J` 的每个成员**仅仅**属于 `I` 或等于 `I`。结论是路径 `J ≡ sucV I`，即集合的真正相等，而非隶属间的双条件。
<!--ja-->
順方向の補題は、三つの節を仮定として、今度は集合のレベルで取ります。`I` が `J` に属すること、`I` への所属が `J` へ移ること、そして `J` の各要素は切り捨てられた形で `I` に属するか `I` と等しいかのいずれかであることです。結論はパス `J ≡ sucV I` であり、所属同士の双条件ではなく集合の本当の等式です。
<!--/-->

```agda
    → ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁)
    → J ≡ sucV I
  suc-char I J hIJ mono cover = extensionality J (sucV I) (sub₁ , sub₂)
    where
    sub₁ : ⟨ J ⊆ sucV I ⟩
```

<!--en-->
The equality is produced by extensionality, split into two inclusions. The first inclusion sends each member of `J` across. The classification hypothesis yields a truncated disjunction, and both disjuncts are eliminated into the proposition-valued membership in `sucV I`: in the left case the member transfers through the union clause of the successor, in the right case the member is `I` itself, which belongs to `sucV I` as its own top element.
<!--zh-->
相等由外延性产生，拆成两个包含。第一个包含把 `J` 的每个成员送过去：分类假设给出一个截断的析取，两个析取支都被消入「属于 `sucV I`」这一取值为命题的目标。左支的成员经后继的并集分支转移；右支的成员就是 `I` 本身，它作为自身的顶端元素属于 `sucV I`。
<!--ja-->
等式は外延性によって作られ、二つの包含に分けられます。第一の包含は `J` の各要素を送ります。分類の仮定は切り捨てられた選言を与え、各選言肢は「`sucV I` に属する」という命題値の対象へと消去されます。左の場合、要素は後者の合併の枝を通して移り、右の場合、要素は `I` 自身であり、それは自分自身を頂点要素として `sucV I` に属します。
<!--/-->

```agda
    sub₁ z z∈ₛJ = PT.rec ((z ∈ₛ sucV I) .snd)
      (Sum.rec
        (λ h → ∈∈ₛ {a = z} {b = sucV I} .fst (∈sucV-inl {A = I} {x = z} h))
        (λ e → subst (λ w → ⟨ w ∈ₛ sucV I ⟩) (sym e)
                 (∈∈ₛ {a = I} {b = sucV I} .fst (self∈sucV I))))
```

<!--en-->
The second inclusion reads members of `sucV I` back into `J`. Membership in a successor is classified by an eliminator with two cases, and this is where the truncation of the classification hypothesis is discharged: the eliminator's target is the proposition `z ∈ J`, so case analysis on the truncated classification is legitimate. The two cases use the two clauses already in hand, transferring the member from `I` or rewriting it to `I`.
<!--zh-->
第二个包含把 `sucV I` 的成员读回 `J`。属于后继这一事实由带两个分支的消去器分类，分类假设的截断正是在此处被消费：消去器的目标是命题 `z ∈ J`，故对截断分类作情形分析是合法的。两个分支各自使用已有的子句：把成员从 `I` 中转移过来，或把它改写成 `I`。
<!--ja-->
第二の包含は `sucV I` の要素を `J` の方へ読み戻します。後者への所属は二つの場合を持つ消去子によって分類され、分類の仮定の切り捨てがここで消費されます。消去子の対象が命題 `z ∈ J` であるため、切り捨てられた分類についての場合分けが正当化されます。二つの場合は、すでに手元にある節をそれぞれ使い、要素を `I` から移すか、`I` へと書き換えます。
<!--/-->

```agda
      (cover z (∈∈ₛ {a = z} {b = J} .snd z∈ₛJ))
    sub₂ : ⟨ sucV I ⊆ J ⟩
    sub₂ z z∈ₛs = ∈∈ₛ {a = z} {b = J} .fst
      (∈sucV-elim {A = I} {x = z} {P = ⟨ z ∈ J ⟩} ((z ∈ J) .snd)
        (∈∈ₛ {a = z} {b = sucV I} .snd z∈ₛs)
```

<!--en-->
The converse lemma `suc-intro` runs the characterization in the opposite direction. Given `J ≡ sucV I`, it transports the first two successor-membership facts to `J`. For the third clause it transports a member of `J` to `sucV I` and applies the successor-membership eliminator, whose result is already the required truncated classification. Thus this direction does not consume an assumed truncated classification.
<!--zh-->
逆命题 `suc-intro` 把刻画沿反方向运行。给定 `J ≡ sucV I`，前两条子句由后继集合的隶属事实搬运到 `J` 得到。第三条先把 `J` 的成员搬到 `sucV I`，再用后继隶属的消去器，直接得到所需的截断分类。因此这一方向并不消除一条作为假设给出的截断分类。
<!--ja-->
逆の補題 `suc-intro` は特徴づけを逆向きに用います。`J ≡ sucV I` が与えられると、最初の二条件は後者集合についての所属の事実を `J` へ輸送して得られます。第三条件では `J` の要素を `sucV I` へ輸送し、後者への所属の消去子を適用して、必要な切り捨てられた分類を直接得ます。したがってこの方向は、仮定として与えられた切り捨てられた分類を消去するものではありません。
<!--/-->

```agda
        (λ h → mono z h)
        (λ e → subst (λ w → ⟨ w ∈ J ⟩) (sym e) hIJ))

  suc-intro : (I J : V ℓ) → J ≡ sucV I
    → ⟨ I ∈ J ⟩
    × (((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
```

<!--en-->
Each clause is produced by transporting a membership fact about `sucV I` along the assumed path, in whichever direction lands it at `J`. The first clause transports the fact that `I` belongs to its own successor; the second transports the transfer rule `∈sucV-inl` member by member.
<!--zh-->
每条子句都是把关于 `sucV I` 的隶属事实沿已给路径搬运得到，方向以使事实落在 `J` 上为准。第一条搬运「`I` 属于自己的后继」这一事实；第二条逐成员搬运转移规则 `∈sucV-inl`。
<!--ja-->
各条件は、`sucV I` に関する所属の事実を仮定されたパスに沿って輸送することで作られます。向きは、事実が `J` の側に着くように選びます。第一の条件は「`I` が自身の後者に属する」という事実を輸送し、第二の条件は移行規則 `∈sucV-inl` を要素ごとに輸送します。
<!--/-->

```agda
    × ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁))
  suc-intro I J e =
      subst (λ w → ⟨ I ∈ w ⟩) (sym e) (self∈sucV I)
    , (λ z h → subst (λ w → ⟨ z ∈ w ⟩) (sym e) (∈sucV-inl {A = I} {x = z} h))
    , (λ z z∈J → ∈sucV-elim {A = I} {x = z} {P = ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁} squash₁
```

<!--en-->
The third clause is the classification of the members of `J`, and its target is the truncated disjunction itself. The successor eliminator is applied with that truncation as the elimination target, so each of its two cases is met by simply re-truncating the corresponding branch. With all three clauses assembled, the adequacy statement takes the same shape as `lookup-spec`: satisfaction of `sucAt i j` under `γ` is the proposition that the value at `j` equals the von Neumann successor of the value at `i`.
<!--zh-->
第三条子句是对 `J` 成员的分类，其目标正是那个截断析取本身。后继消去器以该截断为消除目标而施用，于是它的两个分支情形各由重新截断相应分支来回应。三条子句齐备后，充分性陈述取得与 `lookup-spec` 相同的形状：`γ` 满足 `sucAt i j` 这一命题，就是「`j` 处的值等于 `i` 处的值的 von Neumann 后继」。
<!--ja-->
第三の条件は `J` の要素の分類であり、その対象は切り捨てられた選言そのものです。後者の消去子はこの切り捨てを消除の対象として適用されるので、二つの分岐はいずれも、対応する枝を切り捨て直すだけで応えられます。三つの条件がそろえば、妥当性の主張は `lookup-spec` と同じ形を取ります。`γ` が `sucAt i j` を充足するという命題とは、`j` での値が `i` での値の von Neumann 後者と等しいことです。
<!--/-->

```agda
        (subst (λ w → ⟨ z ∈ w ⟩) e z∈J)
        (λ h → ∣ inl h ∣₁)
        (λ q → ∣ inr q ∣₁))

sucAt-adequate : ∀ {n} (i j : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ sucAt i j) ≡ ((⟦ var j ⟧ γ ≡ sucV (⟦ var i ⟧ γ)) , setIsSet _ _)
```

<!--en-->
The two lemmas fit the adequacy statement exactly. Forwards, the satisfaction of the conjunction unpacks into three clauses, which `suc-char` receives as its three hypotheses and turns into the semantic equation; since the conclusion is a proposition, the truncated structure of the quantifier data passes through the elimination legally. Backwards, `suc-intro` produces the three clauses from the semantic equation. The two directions compose into the path of truth values that an adequacy lemma is.
<!--zh-->
两条引理与充分性陈述恰好吻合。正向：合取的满足拆成三条子句，`suc-char` 把它们当作三条假设，转为语义等式；由于结论是命题，量词数据的截断结构得以合法通过消除。反向：`suc-intro` 从语义等式产出三条子句。两个方向复合成一条真值路径，这正是充分性引理的形态。
<!--ja-->
二つの補題は妥当性の主張にちょうどはまります。順方向では、連言の充足が三つの条件にほどけ、`suc-char` がそれを三つの仮定として受け取り意味論の等式へ変えます。結論が命題であるため、量化子データの切り捨てられた構造は消去を正しく通過します。逆方向では、`suc-intro` が意味論の等式から三つの条件を作ります。二方向が合成されて一つの真理値のパスになり、それが妥当性補題の姿です。
<!--/-->

```agda
sucAt-adequate i j γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → suc-char (⟦ var i ⟧ γ) (⟦ var j ⟧ γ) h₁ h₂ h₃ })
  (suc-intro (⟦ var i ⟧ γ) (⟦ var j ⟧ γ))
```

<!--en-->
## Shifting an entry

`shiftPairAt p' p` recognizes when the pair at `p'` is obtained from the pair at `p` by replacing its numeral key with its von Neumann successor and keeping the value unchanged.

Extending an environment does not only insert a new entry at key zero; it renumbers the old ones, so that what was keyed `# i` becomes keyed `# (suc i)`. This section isolates one step of that renumbering and gives it a bounded description. Since a single bounded quantifier can only bind one member of a set, and one entry of a Kuratowski pair yields its index and value one at a time, the formula runs five bounded quantifiers in sequence to hold the two entries, their two indices and their shared value simultaneously. Its body is then the two Kuratowski readers of the pair-reader chapter, plus the successor reader of the previous section, and together they say precisely that the two entries share a value while the keys are one successor step apart.
<!--zh-->
## 移位一个条目

`shiftPairAt p' p` 识别如下情形：把 `p` 处有序对的数码键换成其 von Neumann 后继、值保持不变，便得到 `p'` 处的有序对。

扩张环境不只是在零键处插入一个新条目，它还给旧条目重新编号：原来键为 `# i` 的条目变为键为 `# (suc i)`。本节把这一重编号的单步分离出来，给它一个有界的描述。由于一个有界量词只能约束集合的一个成员，而一个 Kuratowski 对的条目一次只给出索引与值之一，公式便依次运行五层有界量词，同时持有两个条目、各自的索引以及共享的值。其主体随后是配对读式一章的两条 Kuratowski 读式，加上上一节的后继读式，合起来恰好说明：两个条目共享一个值，而两个键相差一个后继步。
<!--ja-->
## 一つの項目をずらす

`shiftPairAt p' p` は、`p` にある対の数項の鍵をその von Neumann 後者に置き換え、値を変えずに得られる対が `p'` にあることを認識します。

環境を拡張すると、鍵 0 に新しい項目を挿入するだけでなく、既存の項目の番号も付け替わります。鍵 `# i` だったものが鍵 `# (suc i)` になるのです。この節ではその付け替えの一歩を切り出し、有界な記述を与えます。一つの有界量化子が束縛できるのは集合の一つの要素だけで、Kuratowski 対の一つの要素からは添字と値が一度に一つずつしか得られないため、論理式は五つの有界量化子を順に重ね、二つの項目、それぞれの添字、そして共有される値を同時に手元に置きます。本体は対読み取りの章の二つの Kuratowski 読み取りと前節の後者の読み取りであり、合わせて、二つの項目が同じ値を共有し鍵が一歩の後者だけ違うことを正確に述べます。
<!--/-->

<!--en-->
The formula is a five-fold bounded quantification over the value at `p`. Each bounded existential extends the environment by one slot, so the bound witnesses are read at positions determined by how many quantifiers have been entered: the first three quantifiers produce the entry at `p`, its index, and its value.
<!--zh-->
公式是对 `p` 处之值的五层有界量化。每个有界存在量词都给环境增添一个槽位，故被约束的见证按已进入量词的层数落在确定的位置上：前三层量词产出 `p` 处的条目、其索引与值。
<!--ja-->
この論理式は、`p` の値に対する五重の有界量化です。各有界存在量化子は環境に一つのスロットを加えるので、束縛された証人はすでに入った量化子の数で決まる位置に現れます。最初の三つは `p` の項目、その添字、その値を捉えます。
<!--/-->

```agda
shiftPairAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
shiftPairAt p' p =
  ∃̇∈ (var p)
    (∃̇∈ (var zero)
      (∃̇∈ (var (suc zero))
```

<!--en-->
The remaining two quantifiers produce the entry at `p'` and its index. At that point all five pieces are simultaneously available to the body: the original entry, its index, its value, the shifted entry, and the shifted index.
<!--zh-->
剩下的两层量词产出 `p'` 处的条目及其索引。至此主体可以同时使用全部五件东西：原条目、其索引、其值、移位条目、以及移位索引。
<!--ja-->
残りの二つの量化子は `p'` の項目とその添字を捉えます。ここで本体は、元の項目、その添字、その値、ずらされた項目、そしてずらされた添字の五つを同時に使えます。
<!--/-->

```agda
        (∃̇∈ (var (suc (suc (suc p'))))
          (∃̇∈ (var zero)
            ( prAt (suc (suc (suc (suc (suc p)))))
                   (suc (suc (suc zero))) (suc (suc zero))
            ∧̇ ( prAt (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
```

<!--en-->
The body is the conjunction of three bounded assertions about those five witnesses. The two Kuratowski readers say that the original entry is the pair of its index and value, and that the shifted entry is the pair of the shifted index and the same value; the successor reader says that the shifted index is the von Neumann successor of the original one. Read together, the shifted entry carries the same value at a key one successor step higher.
<!--zh-->
主体是对这五个见证的三条有界断言的合取。两条 Kuratowski 读式说：原条目是其索引与值的对，移位条目是移位索引与同一个值的对；后继读式说：移位索引是原索引的 von Neumann 后继。合起来读，移位条目在升高一个后继步的键处携带同一个值。
<!--ja-->
本体は、この五つの証人についての三つの有界な主張の連言です。二つの Kuratowski 読み取りは、元の項目がその添字と値の対であり、ずらされた項目がずらされた添字と同じ値の対であると言い、後者の読み取りは、ずらされた添字が元の添字の von Neumann 後者であると言います。合わせて読めば、ずらされた項目は一歩の後者だけ高い鍵で同じ値を担っています。
<!--/-->

```agda
            ∧̇ sucAt (suc (suc (suc zero))) zero ))))))

shiftPairAt-adequate : ∀ {n} (p' p : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ shiftPairAt p' p)
  ≡ (∥ Σ[ i ∈ V ℓ ] Σ[ v ∈ V ℓ ]
       ((⟦ var p ⟧ γ ≡ pr i v) × (⟦ var p' ⟧ γ ≡ pr (sucV i) v)) ∥₁ , squash₁)
```

<!--en-->
The adequacy statement records what satisfaction of such nested quantification actually provides: a merely-exists claim. It says that the set at slot `p` is, merely, the pair of some index and value, and the set at slot `p'` is, merely, the pair of the successor of that index and the same value. The truncation is faithful to the formula: nothing in it singles out a particular decomposition of either entry, and none is needed.
<!--zh-->
充分性陈述记录了这种嵌套量化的满足实际提供的东西：一个仅仅存在的断言。它说槽位 `p` 处的集合仅仅是某个索引与值的对，槽位 `p'` 处的集合仅仅是该索引的后继与同一个值的对。截断忠实于公式本身：公式中没有挑出任何一个条目的特定分解，也不需要。
<!--ja-->
妥当性の主張は、このような入れ子の量化の充足が実際に何を与えるかを記録します。すなわち「単に存在する」という主張です。スロット `p` の集合はある添字と値の対として単に存在し、スロット `p'` の集合はその添字の後者と同じ値の対として単に存在する、と言います。切り捨ては論理式に忠実です。式のどこにも特定の分解が選ばれておらず、それを選ぶ必要もありません。
<!--/-->

```agda
shiftPairAt-adequate p' p γ = ⇔toPath fwd bwd
  where
  P = ⟦ var p ⟧ γ
  P' = ⟦ var p' ⟧ γ
  Tgt : Type (ℓ-suc ℓ)
```

<!--en-->
The forward direction must convert a chain of truncated witnesses into one inhabitant of the truncated target, and it does so by working with all five witnesses at once once they are explicit. The hypotheses available at that point are the three body conjuncts, each asserted in the environment extended by all five bound witnesses, and the conclusion is a single inhabitant of the truncated existence statement.
<!--zh-->
正向要把一串截断的见证转换成截断目标的一个居民，其做法是在五个见证全部显式之后一次性使用它们。此时可用的假设是主体的三个合取支，各自在扩张了全部五个被约束见证的环境中陈述；结论是截断存在陈述的一个居民。
<!--ja-->
順方向は、切り捨てられた証人の連なりを切り捨てられた対象の一つの要素へ変換します。やり方は、五つの証人がすべて明示になった時点でそれらを一度に使うことです。その時点で使える仮定は本体の三つの連言肢であり、いずれも五つの束縛された証人全員で拡張した環境の中で述べられています。結論は、切り捨てられた存在の主張の一つの要素です。
<!--/-->

```agda
  Tgt = ∥ Σ[ i ∈ V ℓ ] Σ[ v ∈ V ℓ ] ((P ≡ pr i v) × (P' ≡ pr (sucV i) v)) ∥₁

  conclude : (c i v c' j : V ℓ)
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ)
        ⊨ prAt (suc (suc (suc (suc (suc p))))) (suc (suc (suc zero))) (suc (suc zero)) ⟩
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ)
```

<!--en-->
Once the five witnesses are explicit, the truncated target is filled by the index `i`, the value `v`, and two path equations. The three satisfaction hypotheses yield those equations through the adequacy lemmas already proved; transporting along the resulting paths aligns their endpoints with the target. The propositionhood of the outer target matters for the surrounding truncation eliminations, while path transport itself requires no such assumption.
<!--zh-->
五个见证都显式之后，以索引 `i`、值 `v` 与两条路径等式即可填入截断目标。三条满足假设经前面证明的充分性引理给出这些等式，再沿所得路径搬运，使端点与目标对齐。外层目标的命题性用于周围的截断消除；路径搬运本身并不要求这一条件。
<!--ja-->
五つの証人が明示されれば、添字 `i`、値 `v`、二つのパス等式を切り捨てられた対象へ入れられます。三つの充足仮定は既に証明した妥当性補題を通してそれらの等式を与え、得られたパスに沿う輸送が端点を対象に合わせます。外側の対象が命題であることは周囲の切り捨て消去に必要ですが、パスに沿う輸送そのものにはその仮定は要りません。
<!--/-->

```agda
        ⊨ prAt (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero)) ⟩
    → ⟨ (j ∷ c' ∷ v ∷ i ∷ c ∷ γ) ⊨ sucAt (suc (suc (suc zero))) zero ⟩
    → Tgt
  conclude c i v c' j sat₁ sat₂ sat₃ =
    ∣ i , v
```

<!--en-->
The adequacy lemma for the pair reader reinterprets its satisfaction hypothesis at slot `p`: it says precisely that the entry there is the Kuratowski pair of the bound index and the bound value. This turns the first satisfaction proof into the first of the two recorded equations, `P ≡ pr i v`.
<!--zh-->
配对读式的充分性引理重新解释槽位 `p` 处的满足假设：它恰断言该处的条目是约束索引与约束值的 Kuratowski 对。这把第一条满足证明转成了所记录的两条等式中的第一条：`P ≡ pr i v`。
<!--ja-->
対の読み取りに対する妥当性補題は、スロット `p` での充足仮定を再解釈します。それは、そこにある項目が束縛された添字と束縛された値の Kuratowski 対であることを、ちょうど述べています。これにより最初の充足の証明が、記録された二つの等式のうちの第一、すなわち `P ≡ pr i v` に変わります。
<!--/-->

```agda
    , subst ⟨_⟩
        (prAt-adequate (suc (suc (suc (suc (suc p)))))
          (suc (suc (suc zero))) (suc (suc zero)) (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
        sat₁
    , (subst ⟨_⟩
```

<!--en-->
The second pair reader's hypothesis yields the equation `P' ≡ pr j v`, and the successor reader's hypothesis yields `j ≡ sucV i`. Composing the second into the first and mapping the successor operation over the first component of the pair produces the second recorded equation, `P' ≡ pr (sucV i) v`. Together with the first equation this is exactly the target: the two entries share a value, and the second key is the von Neumann successor of the first.
<!--zh-->
第二条配对读式的假设给出等式 `P' ≡ pr j v`，后继读式的假设给出 `j ≡ sucV i`。把第二条复合进第一条，并让后继运算作用于对的第一个分量，便产生所记录的第二条等式：`P' ≡ pr (sucV i) v`。它与第一条等式合起来恰是目标：两个条目共享一个值，且第二个键是第一个键的 von Neumann 后继。
<!--ja-->
二つ目の対の読み取りの仮定からは等式 `P' ≡ pr j v` が、後者の読み取りの仮定からは `j ≡ sucV i` が得られます。後者を前者に合成し、対の第一成分に後者の操作を作用させれば、記録された第二の等式 `P' ≡ pr (sucV i) v` が生まれます。これと第一の等式を合わせたものがまさに目標です。二つの項目は値を共有し、第二の鍵は第一の鍵の von Neumann 後者です。
<!--/-->

```agda
        (prAt-adequate (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
          (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
        sat₂
       ∙ cong (λ z → pr z v)
          (subst ⟨_⟩
```

<!--en-->
The assembled index, value and two equations are then truncated into the target. This completes the forward direction of adequacy, which unwraps the five quantifiers one at a time. Each is a truncated existential, so each elimination must land in a proposition; the target is truncated precisely so that this nesting of eliminations is legal.
<!--zh-->
拼装好的索引、值与两条等式随后被截断入目标。至此充分性的正向完成，它逐层剥开五个量词。每层都是截断的存在，故每次消除都必须落入命题；目标恰被截断，正是为了使这层消除嵌套合法。
<!--ja-->
組み上げられた添字、値、二つの等式は、切り詰められて目標の中へ入ります。これで妥当性の順方向が完成します。この方向は五つの量化子を一度に一つずつほどいていきます。各量化子は切り詰められた存在なので、各消除は命題へ着地しなければなりません。目標が切り詰められているのは、まさにこの消除の入れ子を正当化するためです。
<!--/-->

```agda
            (sucAt-adequate (suc (suc (suc zero))) zero (j ∷ c' ∷ v ∷ i ∷ c ∷ γ))
            sat₃))
    ∣₁

  fwd : ⟨ γ ⊨ shiftPairAt p' p ⟩ → Tgt
  fwd = PT.rec squash₁ (λ { (c , _ , h₁) → PT.rec squash₁
```

<!--en-->
The innermost elimination reaches the three satisfaction proofs, and with them the forward proof is done. Note that the five witnesses never become ordinary data outside the eliminations: each elimination consumes a truncated layer into a proposition, so the witnesses exist only inside that chain.
<!--zh-->
最内层的消除到达三条满足证明，正向证明随之完成。注意这五个见证从未成为消除之外的普通数据：每次消除都把一个截断层消耗进一个命题，见证只存在于这条链之内。
<!--ja-->
最も内側の消除が三つの充足の証明に到達し、順方向の証明はこれで完成します。五つの証人が消除の外で通常のデータになることは決してありません。各消除は切り詰められた一層を命題の中へ消費するので、証人はその連鎖の中にのみ存在します。
<!--/-->

```agda
    (λ { (i , _ , h₂) → PT.rec squash₁
      (λ { (v , _ , h₃) → PT.rec squash₁
        (λ { (c' , _ , h₄) → PT.rec squash₁
          (λ { (j , _ , sat₁ , sat₂ , sat₃) → conclude c i v c' j sat₁ sat₂ sat₃ })
          h₄ })
```

<!--en-->
The backward direction runs on introduction instead of analysis. Given an index, a value, and the two equations identifying the slots with the corresponding pairs, a satisfaction proof must be produced, and everything it needs is ordinary set construction: the entry sets are built with the pairing operation, and their memberships follow from the component introduction rules.
<!--zh-->
反向依靠引入而非分析。给定一个索引、一个值，以及把两个槽位与相应配对等同的两条等式，需要产出一条满足证明；它所需的每件东西都是普通的集合构造：条目集合用配对运算造出，其隶属由分量引入规则给出。
<!--ja-->
逆方向は分析ではなく導入で進みます。添字、値、そして二つのスロットを対応する対と同一視する等式が与えられれば、充足の証明を作らねばなりません。そこで必要なものはすべて通常の集合の構成です。項目の集合は対の操作で作られ、その所属は成分の導入規則から従います。
<!--/-->

```agda
        h₃ })
      h₂ })
    h₁ })

  build : (i v : V ℓ) → P ≡ pr i v → P' ≡ pr (sucV i) v → ⟨ γ ⊨ shiftPairAt p' p ⟩
  build i v eP eP' =
```

<!--en-->
The first witness for the outer existential is the pair `⁅ i , v ⁆` itself. It belongs to the set at slot `p` because the assumed equation identifies that set with `pr i v`, and by the component introduction rule the unordered pair `⁅ i , v ⁆` sits inside its own Kuratowski encoding; transporting along the equation moves the membership to the right side. Opening the pair then needs no work: its index witness is `i` and its value witness is `v`, each supplied by one of the two component rules.
<!--zh-->
最外层存在的第一个见证就是对 `⁅ i , v ⁆` 本身。它属于槽位 `p` 处的集合，因为假定的等式把该集合等同于 `pr i v`，而由分量引入规则，无序对 `⁅ i , v ⁆` 就在其自身的 Kuratowski 编码之内；沿等式搬运即把隶属移到正确的位置。随后打开这个对无需任何工作：索引见证是 `i`，值见证是 `v`，各由一条分量规则给出。
<!--ja-->
最外層の存在に対する最初の証人は、対 `⁅ i , v ⁆` そのものです。仮定の等式がスロット `p` の集合を `pr i v` と同一視し、成分の導入規則により非順序対 `⁅ i , v ⁆` はそれ自身の Kuratowski 符号化の内側にあるので、これはその集合に属します。等式に沿って輸送すれば所属が正しい側に移ります。次に対を開くのに仕事は要りません。添字の証人は `i`、値の証人は `v` であり、それぞれ一つの成分規則が与えます。
<!--/-->

```agda
    ∣ ⁅ i , v ⁆
    , subst (λ z → ⟨ ⁅ i , v ⁆ ∈ z ⟩) (sym eP)
        (∈pair-introR {u = ⁅ i ⁆s} {v = ⁅ i , v ⁆} {y = ⁅ i , v ⁆} refl)
    , ∣ i , ∈pair-introL {u = i} {v = v} {y = i} refl
      , ∣ v , ∈pair-introR {u = i} {v = v} {y = v} refl
```

<!--en-->
The shifted entry is built from `sucV i` and `v` by the same construction, with the shifted index witness being the successor set itself. The remaining clauses are satisfied by the two assumed equations, which the adequacy lemmas read back as satisfaction proofs. Where the forward direction had to analyze a hypothetical witness, the backward direction simply assembles the five witnesses the formula asks for, and the truncated outer layer receives a single explicit one.
<!--zh-->
移位条目由 `sucV i` 与 `v` 经同一构造得到，移位索引见证就是后继集合本身。其余子句由两条假定的等式满足，充分性引理会把它们读回满足证明。正向不得不分析一个假想的见证，反向则只是装配公式要求的五个见证，截断的外层由一个显式见证填充。
<!--ja-->
ずらされた項目は `sucV i` と `v` から同じ構成で作られ、ずらされた添字の証人は後者の集合そのものです。残りの節は仮定された二つの等式で満たされ、妥当性補題がそれらを充足の証明として読み戻します。順方向が仮想的な証人を分析しなければならなかったのに対し、逆方向は論理式が求める五つの証人を組み立てるだけで、切り詰められた外側の層は一つの明示的な証人で満たされます。
<!--/-->

```agda
        , ∣ ⁅ sucV i , v ⁆
          , subst (λ z → ⟨ ⁅ sucV i , v ⁆ ∈ z ⟩) (sym eP')
              (∈pair-introR {u = ⁅ sucV i ⁆s} {v = ⁅ sucV i , v ⁆}
                            {y = ⁅ sucV i , v ⁆} refl)
          , ∣ sucV i
```

<!--en-->
The innermost witness is the shifted entry `⁅ sucV i , v ⁆`, and its index witness is the successor set `sucV i` itself, introduced by the left-component rule for a Kuratowski pair. The two clauses about the entries remain. The first is filled from the assumed equation `eP : ⟦ var p ⟧ γ ≡ pr i v`. The clause is evaluated in the environment extended five times, holding `sucV i`, the shifted pair, `v`, `i` and the original pair in slots zero through four; the bound variables occupy those slots, so slot `p` still reads `⟦ var p ⟧ γ`, which is exactly the left side of `eP`. The adequacy lemma for the pair reader identifies the clause's satisfaction with that equation, so transporting `eP` along the symmetric adequacy path fills the clause.
<!--zh-->
最内层的见证是移位后的条目 `⁅ sucV i , v ⁆`，其索引见证就是后继集合 `sucV i` 本身，由 Kuratowski 对的左分量规则引入。剩下的是关于两个条目的子句。第一条由假定的等式 `eP : ⟦ var p ⟧ γ ≡ pr i v` 填入。该子句在扩张五次的环境中求值，槽位零至四依次放着 `sucV i`、移位后的对、`v`、`i` 与原对；被约束的变元占据这些槽位，故槽位 `p` 在其中读出的仍是 `⟦ var p ⟧ γ`，恰为 `eP` 的左侧。配对读式的充分性引理把该子句的满足等同于这条等式，因此沿对称的充分性路径搬运 `eP` 即填入第一条子句。
<!--ja-->
最も内側の証人はずらされた項目 `⁅ sucV i , v ⁆` であり、その添字の証人は後者の集合 `sucV i` そのものです。これは Kuratowski 対の左成分規則で導入されます。残るのは二つの項目に関する節です。第一の節は仮定された等式 `eP : ⟦ var p ⟧ γ ≡ pr i v` から埋められます。この節は五回拡張された環境で評価されます。スロット 0 から 4 に `sucV i`、ずらされた対、`v`、`i`、元の対が並び、束縛された変数がこれらのスロットを占めるため、スロット `p` が読む値はそこでも `⟦ var p ⟧ γ` であり、これは `eP` の左辺そのものです。対の読み取りの妥当性補題はこの節の充足をその等式と同一視するので、対称な妥当性のパスに沿って `eP` を輸送すれば第一の節が満たされます。
<!--/-->

```agda
            , ∈pair-introL {u = sucV i} {v = v} {y = sucV i} refl
            , subst ⟨_⟩
                (sym (prAt-adequate (suc (suc (suc (suc (suc p)))))
                  (suc (suc (suc zero))) (suc (suc zero))
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
```

<!--en-->
The second clause about the entries is filled the same way from `eP'`. The pair reader at slot `p'` reads its index from slot zero, which now holds `sucV i`, and its value from slot two, which holds `v`; so the equation the adequacy lemma expects is precisely `⟦ var p' ⟧ γ ≡ pr (sucV i) v`, the second assumption. Note that the shifted entry itself never needs to be taken apart here: the pair readers supply the two decompositions, and the successor reader, filled by `refl` since slot zero holds the successor of slot three, records that the new key is the successor of the old one with the value preserved.
<!--zh-->
关于条目的第二条子句同样由 `eP'` 填入。槽位 `p'` 处的配对读式从槽位零取索引，而槽位零现在放着 `sucV i`；从槽位二取值，槽位二放着 `v`。于是充分性引理所期待的等式恰为 `⟦ var p' ⟧ γ ≡ pr (sucV i) v`，即第二条假定。注意此处无需拆开移位后的条目本身：两条配对读式给出两个分解，而后继读式由于槽位零放着槽位三的后继而由 `refl` 填入，它记录了新键是旧键的后继且值保持不变。
<!--ja-->
項目に関する第二の節も同じやり方で `eP'` から埋められます。スロット `p'` の対の読み取りは添字をスロット 0 から読みますが、そこには今 `sucV i` が入っており、値は `v` の入るスロット 2 から読みます。したがって妥当性補題が期待する等式はちょうど `⟦ var p' ⟧ γ ≡ pr (sucV i) v`、すなわち第二の仮定です。ここでずらされた項目そのものを分解する必要はない点に注意してください。二つの対の読み取りが二つの分解を与え、後者の読み取りはスロット 0 にスロット 3 の後者が入っているため `refl` で満たされ、新しい鍵が古い鍵の後者であり値が保たれていることを記録します。
<!--/-->

```agda
                eP
            , subst ⟨_⟩
                (sym (prAt-adequate (suc (suc (suc (suc (suc p'))))) zero (suc (suc zero))
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
                eP'
```

<!--en-->
The last conjunct of the body is the successor reader of the previous section, applied to the two index witnesses. In the assembled environment the value at slot three is the index `i` and the value at slot zero is its von Neumann successor `sucV i`, so the characterization of that reader is witnessed by the reflexive path `sucV i ≡ sucV i`, transported through its adequacy lemma into the satisfaction clause. With this, all three assertions of the body hold: the two entries are genuine pairs sharing a value, and the second key is the successor of the first. This is exactly the mathematical content of one renumbered entry.
<!--zh-->
主体的最后一个合取支是上一节的后继读式，作用于两个索引见证。在拼装好的环境中，槽位三处的值是索引 `i`，槽位零处的值是它的 von Neumann 后继 `sucV i`，故该读式的刻画由自反路径 `sucV i ≡ sucV i` 见证，再经其充分性引理搬运为满足子句。至此主体的三条断言全部成立：两个条目都是真正的对且共享一个值，第二个键是第一个键的后继。这正是一条重编号条目的数学内容。
<!--ja-->
本体の最後の連言肢は、前節の後者の読み取りを二つの添字の証人に適用したものです。組み上げた環境では、スロット 3 の値が添字 `i` であり、スロット 0 の値がその von Neumann 後者 `sucV i` です。したがってこの読み取りの特徴づけは自反パス `sucV i ≡ sucV i` によって与えられ、その妥当性補題を通して充足の節へと輸送されます。これで本体の三つの主張がすべて成立します。二つの項目が値を共有する本物の対であり、第二の鍵が第一の鍵の後者である、ということが。これこそ一項目分の番号付け替えの数学的内容です。
<!--/-->

```agda
            , subst ⟨_⟩
                (sym (sucAt-adequate (suc (suc (suc zero))) zero
                  (sucV i ∷ ⁅ sucV i , v ⁆ ∷ v ∷ i ∷ ⁅ i , v ⁆ ∷ γ)))
                refl
            ∣₁
```

<!--en-->
What remains is bookkeeping across the five nested bounded existentials. Each layer is a proposition, so supplying one witness at a time and sealing it as merely present is legitimate: no choice among candidates is being made, because no candidate was competing. Once each existential has its witness, the satisfaction proof of the whole formula stands assembled.
<!--zh-->
剩下的只是跨越五层嵌套有界存在量词的整理。每一层都是命题，因此逐层给出一个见证、并把它封为「仅仅在场」是合法的：并未在候选之间作选择，因为本无候选在竞争。每层存在量词各有见证之后，整条公式的满足证明便拼装完成。
<!--ja-->
残るのは、五重に入れ子になった有界存在量化子をまたぐ整理です。各層は命題なので、一つずつ証人を示し、それを「単に存在する」として封入することは正当です。候補が競合していたわけではないので、候補の中から選択が行われることもありません。各存在量化子に証人が揃えば、論理式全体の充足の証明が組み上がります。
<!--/-->

```agda
          ∣₁
        ∣₁
      ∣₁
    ∣₁
```

<!--en-->
The backward direction closes the adequacy theorem. Its input is the truncated existence of an index and value with the two equations, and its output is a satisfaction proof, itself a proposition. Elimination of a truncation into a proposition-valued target is exactly what the rules allow, so the assumed pair decomposition may be used inside the elimination even though it is not recovered as ordinary data outside. The constructed witness then matches the formula clause by clause, completing the identification: satisfaction of the shift formula is, as a truth value, the truncated statement that the two entries are pairs sharing a value with successor-related keys.
<!--zh-->
反向方向完成充分性定理。其输入是「存在索引与值以及两条等式」的截断存在，其输出是满足证明，而满足证明本身是命题。把截断消除到取值为命题的目标正是规则所允许的，因此假定的一对分解可在消除内部使用，尽管它不会在消除之外作为普通数据被取回。构造出的见证随后逐子句匹配公式，完成了这层等同：移位公式的满足作为真值，恰是「两个条目是以对的形式共享一个值且键相差一个后继」这一截断陈述。
<!--ja-->
逆方向で妥当性定理が閉じます。入力は「添字と値、そして二つの等式が存在する」という切り詰められた主張であり、出力は充足の証明、それ自体命題です。切り詰めを命題値の対象へ消除することはまさに規則が許すところなので、仮定された対の分解は消除の内部で使えます。ただし、消除の外では通常のデータとして取り出されることはありません。構成された証人は論理式の各節と一致し、次の同一視が完成します。ずらしの論理式の充足とは、真理値として、二つの項目が対として値を共有し鍵が後者関係にあるという切り詰められた主張なのです。
<!--/-->

```agda

  bwd : Tgt → ⟨ γ ⊨ shiftPairAt p' p ⟩
  bwd = PT.rec ((γ ⊨ shiftPairAt p' p) .snd)
    (λ { (i , v , eP , eP') → build i v eP eP' })
```

<!--en-->
## Coding the empty entry

The new zeroth entry of an extended environment is a Kuratowski pair tagged with `# 0`, and `# 0` is the empty set by definition. This section builds readers that recognize such a pair while mentioning the tag only through its mathematical property: a member is empty, expressible by bounded quantification into the falsity formula, with no constant needed. The three formulas `sgl0At`, `pair0At` and `tag0At` say, respectively, that a set is the singleton of the empty set, the unordered pair of the empty set with a given set, and the tagged pair assembled from these.

The metalevel work converts the satisfaction reading of these formulas, phrased with the predicate `Empty'` saying that a set has no members, into the shapes that the pair characterization `prChar-fwd` and `prChar-bwd` of the pair-reader chapter already accept, where the empty set appears by name. Since a set with no members is equal to `∅` by extensionality, the two phrasings describe the same mathematics, and the adequacy lemma `tag0At-adequate` identifies satisfaction of the tag reader with the equation that the tagged set is `pr ∅` applied to the value at the second slot.
<!--zh-->
## 编码空条目

扩张后的环境的第零个新条目是带标签 `# 0` 的 Kuratowski 对，而 `# 0` 按定义就是空集。本节构造的读式识别这样的对，但只通过标签的数学性质提到它：一个成员是空的，这可用进入否定式公式的有界量化表达，无需任何常元。三条公式 `sgl0At`、`pair0At` 与 `tag0At` 分别说：一个集合是空集的单点集，是空集与给定集合的无序对，以及是由前两者装配的带标签对。

元层工作把这些公式的满足读式，即以谓词 `Empty'` (说一个集合没有成员) 表述的版本，转换为配对读式一章中 `prChar-fwd` 与 `prChar-bwd` 已接受的形状，在那里空集是直接点名的。由于没有成员的集合按外延性等于 `∅`，两种表述描述的是同一数学内容；充分性引理 `tag0At-adequate` 把标签读式的满足等同于「带标签的集合等于 `pr ∅` 作用于第二槽位之值」这条等式。
<!--ja-->
## 空の項目を符号化する

拡張された環境の新しい第 0 項目は、タグ `# 0` を付された Kuratowski 対であり、`# 0` は定義により空集合です。本節で構成する読み取りは、このような対を、タグをその数学的性質を通してのみ言及することで認識します。すなわち、ある要素が空であるということを、偽の論理式への有界量化で表し、定数を一切必要としません。三つの論理式 `sgl0At`、`pair0At`、`tag0At` はそれぞれ、ある集合が空集合の一元集合であること、空集合と与えられた集合の非順序対であること、そして両者から組み立てられるタグ付きの対であることを述べます。

メタレベルの仕事は、これらの論理式の充足の読み、すなわち集合が要素を持たないことを述べる述語 `Empty'` による表現を、対読み取りの章の `prChar-fwd` と `prChar-bwd` がすでに受け入れる形、つまり空集合が名指しで現れる形へ変換することです。要素を持たない集合は外延性により `∅` と等しいので、二つの表現は同じ数学を述べています。そして妥当性補題 `tag0At-adequate` は、タグの読み取りの充足を、「タグ付きの集合が `pr ∅` を第二のスロットの値に作用したものと等しい」という等式と同一視します。
<!--/-->

<!--en-->
The first reader describes the singleton `{∅}` without naming the empty set. `sgl0At k` conjoins two bounded clauses about the value at `k`: merely some member satisfies the body `∀̇∈ (var zero) ⊥̇`, and every member does. Under the bounded quantifier, the body `⊥̇` holds exactly when the bound member has no members of its own, so each clause says its subject is empty. The existential clause is what allows the value to be inhabited at all; without it, the condition would also be satisfied by the empty set itself. Together the two clauses say that the value at `k` has a member and all its members are empty, which pins it down extensionally as `{∅}`.
<!--zh-->
第一条读式在不点名空集的情况下描述单点集 `{∅}`。`sgl0At k` 对 `k` 处的值合取两条有界子句：仅仅有一个成员满足主体 `∀̇∈ (var zero) ⊥̇`，且每个成员都满足。在有界量词之下，主体 `⊥̇` 恰在被量化的成员自身没有成员时成立，故每条子句都说其主语是空的。存在子句保证该值确实非空；没有它，空集自身也会满足该条件。两条子句合起来说：`k` 处的值有成员，且其成员全为空集，这在外延上把它确定为 `{∅}`。
<!--ja-->
最初の読み取りは、空集合を名指しすることなく一元集合 `{∅}` を記述します。`sgl0At k` は `k` の値について二つの有界な節を連言します。すなわち、本体 `∀̇∈ (var zero) ⊥̇` を満たす要素が命題的に一つあることと、すべての要素がそれを満たすことです。有界な量化子の下では、本体 `⊥̇` は量化された要素が自身の要素を持たないとき、そのときに限って成り立つので、各節はその主語が空であると言っています。存在の節があるおかげで値が非空であることが保証されます。これがなければ、空集合自身も条件を満たしてしまいます。二つの節を合わせると、`k` の値は要素を持ち、その要素がすべて空集合であり、これは外延的にちょうど `{∅}` です。
<!--/-->

```agda
sgl0At : ∀ {n} → Fin n → Formula (V ℓ) n
sgl0At k = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) ⊥̇))

pair0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
pair0At k j = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
```

<!--en-->
The second reader `pair0At k j` describes the unordered pair `{∅, W}`, where `W` is the value at slot `j` of the original assignment; under the new binder it is addressed by `suc j`. Its three clauses are: the value at `k` merely has an empty member; the value at `j` belongs to it; and every member of it merely is empty or equals `W`. The first clause is the same empty-member existence the singleton reader used, and the third is the pair classification with the first component fixed at `∅`. The third formula `tag0At s x` combines the two readers: the value at `s` merely has a member satisfying the empty singleton clause, merely has one satisfying the empty pair clause, and every member merely satisfies one or the other.
<!--zh-->
第二条读式 `pair0At k j` 描述无序对 `{∅, W}`，其中 `W` 是原赋值槽位 `j` 处的值；进入新绑定后由 `suc j` 指向同一取值。它的三条子句是：`k` 处的值仅仅有一个空成员；`j` 处的值属于它；它的每个成员仅仅是空的或等于 `W`。第一子句正是单点集读式用过的那个空成员存在，第三子句是把第一分量固定为 `∅` 的配对分类。第三条公式 `tag0At s x` 把两条读式合并：`s` 处的值仅仅有一个成员满足空单点集子句，仅仅有一个成员满足空对子句，且每个成员仅仅满足其一。
<!--ja-->
第二の読み取り `pair0At k j` は非順序対 `{∅, W}` を記述します。ここで `W` は元の割り当てのスロット `j` の値であり、新しい束縛子の内側では `suc j` が同じ値を指します。三つの節は、`k` の値に空な要素が命題的に存在すること、`j` の値がそれに属すること、そしてそのすべての要素が命題的に空であるか `W` と等しいか、です。第一の節は単集合の読み取りが使ったのと同じ空要素の存在であり、第三の節は第一成分を `∅` に固定した対の分類です。第三の論理式 `tag0At s x` はこの二つの読み取りを組み合わせます。`s` の値は空単集合の節を満たす要素を命題的に持ち、空対の節を満たす要素を命題的に持ち、そのすべての要素は命題的にいずれかを満たします。
<!--/-->

```agda
           ∧̇ ((var j ∈̇ var k)
           ∧̇ (∀̇∈ (var k) ((∀̇∈ (var zero) ⊥̇) ∨̇ (var zero ≐ var (suc j)))))

tag0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
tag0At s x = (∃̇∈ (var s) (sgl0At zero))
          ∧̇ ((∃̇∈ (var s) (pair0At zero (suc x)))
```

<!--en-->
On the metalevel side, emptiness is expressed by the private predicate `Empty' z`, a function that takes any member `y` of `z` and returns an inhabitant of the empty type `⊥*`. This function expresses that `z` has no members: any alleged membership produces a term of `⊥*`, and `⊥*` is the empty type. It is distinct from the object-language falsity formula `⊥̇`, which is syntax. The first lemma, `empty'→∅`, is the bridge to the named empty set: any set of which `Empty'` holds equals `∅`.
<!--zh-->
在元层一侧，空性由私有谓词 `Empty' z` 表达：它是一个函数，取 `z` 的任意成员 `y`，返回空类型 `⊥*` 的一个元素。这个函数表达 `z` 没有成员：任何声称的隶属都会产生空类型 `⊥*` 的元素。它不同于对象语言中的否定式公式 `⊥̇`，后者是语法。第一条引理 `empty'→∅` 是通向被点名的空集的桥梁：凡使 `Empty'` 成立的集合都等于 `∅`。
<!--ja-->
メタレベルでは、空性は private な述語 `Empty' z` で表されます。これは `z` への任意の所属から空の型 `⊥*` の要素を導く関数であり、`z` が要素を持たないことを表します。空の型なのは `⊥*` であり、`Empty' z` はその型へ至る関数型です。対象言語の偽の論理式 `⊥̇` は構文なので、これとは区別されます。最初の補題 `empty'→∅` が、名指しされた空集合への橋となります。`Empty'` が成り立つ集合はすべて `∅` と等しい、というものです。
<!--/-->

```agda
          ∧̇ (∀̇∈ (var s) (sgl0At zero ∨̇ pair0At zero (suc x))))

private
  Empty' : V ℓ → Type (ℓ-suc ℓ)
  Empty' z = (y : V ℓ) → ⟨ y ∈ z ⟩ → E.⊥* {ℓ-suc ℓ}

  empty'→∅ : (z : V ℓ) → Empty' z → z ≡ ∅
```

<!--en-->
The proof of the bridge is extensionality with both directions vacuous. To show each `y` belongs to `z` exactly when it belongs to `∅`, suppose `y` belonged to `z`: applying `Empty' z` to that membership yields an inhabitant of the empty type, from which anything follows, in particular membership in `∅`. In the other direction, `∅-empty` refutes any membership in `∅`, and from that refutation membership in `z` follows as well. The converse bridge `∅→empty'` needs only the defining path: a membership of `z` transported along `e : z ≡ ∅` lands in `∅`, where `∅-empty` again contradicts it. Thus `Empty' z` and `z ≡ ∅` are interchangeable.
<!--zh-->
这座桥的证明是外延性，且两个方向都是空洞的。为证每个 `y` 属于 `z` 恰当其属于 `∅`：设 `y` 属于 `z`，把 `Empty' z` 施于该隶属便得空类型的一个元素，由此可得任何结论，特别是属于 `∅`。另一方向上，`∅-empty` 反驳任何属于 `∅` 的隶属，而由这个反驳同样可得属于 `z`。反向的桥 `∅→empty'` 只需定义性路径：把 `z` 的一个隶属沿 `e : z ≡ ∅` 搬运落入 `∅`，在那里 `∅-empty` 再次给出矛盾。于是 `Empty' z` 与 `z ≡ ∅` 可以互换。
<!--ja-->
この橋の証明は外延性であり、どちらの向きも空虚に成り立ちます。各 `y` が `z` に属することと `∅` に属することがちょうど一致することを示すには、`y` が `z` に属すると仮定します。その所属に `Empty' z` を適用すれば空の型の住人が得られ、そこから何でも、特に `∅` への所属が従います。逆の向きでは、`∅-empty` が `∅` へのあらゆる所属を反駁し、その反駁から同じく `z` への所属が従います。逆向きの橋 `∅→empty'` は定義的なパスだけで足ります。`z` への所属を `e : z ≡ ∅` に沿って輸送すれば `∅` の中に落ち、そこで再び `∅-empty` が矛盾を与えます。こうして `Empty' z` と `z ≡ ∅` は取り替え可能です。
<!--/-->

```agda
  empty'→∅ z hz = extensionalV (λ y → ⇔toPath
    (λ h → E.rec (lower (hz y h)))
    (λ h → E.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst h))))

  ∅→empty' : (z : V ℓ) → z ≡ ∅ → Empty' z
  ∅→empty' z e y y∈z = lift (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst (subst (λ w → ⟨ y ∈ w ⟩) e y∈z)))
```

<!--en-->
The satisfaction of the two readers, once unfolded, takes the shape of two metalevel packages. `EmptySgl w` consists of a truncated existence of a member of `w` that is empty, and an untruncated universal clause demanding that every member is empty. `EmptyPair W w` keeps the truncated empty-member existence and replaces the rest by a membership of `W` in `w` together with a truncated classification: every member is merely empty or equals `W`. The truncations sit exactly where the bounded existentials and the truncated disjunction of the formulas put them; in particular no chosen pair decomposition is ever extracted.
<!--zh-->
两条读式的满足展开后，呈两个元层包裹的形状。`EmptySgl w` 由「`w` 有一个空成员」的截断存在，加上非截断的全称子句「每个成员都是空的」组成。`EmptyPair W w` 保留截断的空成员存在，把其余换成 `W` 属于 `w`，加上截断的分类：每个成员仅仅是空的或等于 `W`。截断的位置恰是公式的有界存在量词与截断析取所放置之处；特别地，任何时候都不会取出一个被选定的对分解。
<!--ja-->
二つの読み取りの充足を展開すると、二つのメタレベルの包みの形になります。`EmptySgl w` は、「`w` の空な要素が存在する」という切り詰められた存在と、「すべての要素が空である」という切り詰められていない全称の節からなります。`EmptyPair W w` は切り詰められた空要素の存在を保ち、残りを `W` の `w` への所属と、切り詰められた分類、すなわちすべての要素が命題的に空であるか `W` と等しいか、に置き換えます。切り詰めの位置は、論理式の有界存在量化子と切り詰められた選言が置いた場所とまさに一致します。特に、選ばれた対の分解が取り出されることは決してありません。
<!--/-->

```agda

  EmptySgl : V ℓ → Type (ℓ-suc ℓ)
  EmptySgl w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
            × ((z : V ℓ) → ⟨ z ∈ w ⟩ → Empty' z)

  EmptyPair : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  EmptyPair W w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
```

<!--en-->
The counterpart packages name the empty set outright. `SglOf∅ w` states that `∅` belongs to `w` and every member of `w` equals `∅`, with no truncation since the witness is given. `PairOf∅ W w` states that `∅` and `W` belong to `w` and every member is merely `∅` or `W`; the classification stays truncated, matching the unordered-pair membership of the hierarchy, from which one does not get to choose a side. These are exactly the shapes the pair characterization of the pair-reader chapter consumes, with its first component instantiated at `∅`, so the whole remaining task is to pass between the two phrasings of the same membership facts.
<!--zh-->
对应的包裹直接点名空集。`SglOf∅ w` 断言 `∅` 属于 `w` 且 `w` 的每个成员都等于 `∅`，因见证已给出而无需截断。`PairOf∅ W w` 断言 `∅` 与 `W` 属于 `w` 且每个成员仅仅是 `∅` 或 `W`；分类保持截断，与层级的无序对隶属一致，从那里并不能选出在哪一侧。这些恰是配对读式一章的配对刻画所消耗的形状，只是第一分量取在 `∅`，于是剩下的全部任务就是在同一隶属事实的两种表述之间往返。
<!--ja-->
対応する包みは空集合を直接名指しします。`SglOf∅ w` は、`∅` が `w` に属し `w` のすべての要素が `∅` と等しいと主張します。証人が与えられているため、切り詰めは不要です。`PairOf∅ W w` は、`∅` と `W` が `w` に属し、すべての要素が命題的に `∅` か `W` であると主張します。分類は切り詰められたままであり、階層の非順序対の所属と一致します。そこからどちらの側かを選び取ることはできません。これらはまさに、対読み取りの章の対の特徴づけが受け取る形であり、第一成分を `∅` に具体化したものです。したがって残る仕事のすべては、同じ所属の事実の二つの表現の間を行き来することです。
<!--/-->

```agda
               × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ Empty' z ⊎ (z ≡ W) ∥₁))

  SglOf∅ : V ℓ → Type (ℓ-suc ℓ)
  SglOf∅ w = ⟨ ∅ ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ ∅)

  PairOf∅ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PairOf∅ W w = ⟨ ∅ ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ ∅) ⊎ (z ≡ W) ∥₁))
```

<!--en-->
The forward conversion turns the truncated existence of an empty member into the plain fact that `∅` belongs to `w`. Membership in a set of the hierarchy is a proposition, so eliminating the truncation into `⟨ ∅ ∈ w ⟩` is legitimate. Inside, an explicitly given witness `z`, with a membership proof and a proof of `Empty' z`, is first identified with `∅` by the previous lemma; its membership in `w` then transports along that path to a membership of `∅`. The rest of `EmptySgl w` converts wholesale: the untruncated universal clause hands back `Empty' z` for each member `z` of `w`, and the same lemma rewrites that into `z ≡ ∅`.
<!--zh-->
正向转换把「存在一个空成员」的截断陈述变成直接的事实：`∅` 属于 `w`。层级中集合的隶属是一个命题，故把截断消除到 `⟨ ∅ ∈ w ⟩` 是合法的。在内部，显式给出的见证 `z` 带有隶属证明与 `Empty' z` 的证明，先由前一条引理把它与 `∅` 等同，其隶属便沿该路径搬运成 `∅` 的隶属。`EmptySgl w` 的其余部分随之整体转换：非截断的全称子句对 `w` 的每个成员 `z` 给出 `Empty' z`，同一引理再把它改写为 `z ≡ ∅`。
<!--ja-->
順方向の変換は、空な要素の存在という切り捨てられた主張を、`∅` が `w` に属するという普通の事実へ変えます。階層の集合への所属は命題なので、切り詰めを `⟨ ∅ ∈ w ⟩` へ消除するのは正当です。内部では、所属の証明と `Empty' z` の証明を伴って明示的に与えられた証人 `z` を、まず前の補題で `∅` と同一視し、その所属をこのパスに沿って輸送して `∅` の所属にします。`EmptySgl w` の残りの部分はそのまま変換されます。切り詰められていない全称の節は `w` の各要素 `z` に対して `Empty' z` を与え、同じ補題がそれを `z ≡ ∅` に書き換えます。
<!--/-->

```agda

  empty-member : (w : V ℓ) → ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁ → ⟨ ∅ ∈ w ⟩
  empty-member w = PT.rec ((∅ ∈ w) .snd)
    (λ { (z , hz , ez) → subst (λ u → ⟨ u ∈ w ⟩) (empty'→∅ z ez) hz })

  EmptySgl→SglOf∅ : (w : V ℓ) → EmptySgl w → SglOf∅ w
  EmptySgl→SglOf∅ w (h₁ , hall) = empty-member w h₁ , (λ z hz → empty'→∅ z (hall z hz))
```

<!--en-->
The pair case follows the same plan. `EmptyPair→PairOf∅` reuses the empty-member conversion for the first component, keeps the membership of `W` unchanged, and rewrites the classification member by member: a truncated statement that each member is empty or equals `W` maps to the corresponding truncated statement with `Empty'` replaced by equality with `∅`. The result is exactly the `∅`-based classification, and the truncation is preserved throughout rather than resolved into a chosen side.
<!--zh-->
有序对情形沿用同一方案。`EmptyPair→PairOf∅` 对第一分量复用空成员转换，`W` 的隶属保持不变，并逐成员改写分类：把「每个成员是空的或等于 `W`」的截断陈述，映射为把 `Empty'` 换成「等于 `∅`」后的对应截断陈述。结果恰是以 `∅` 为基准的分类，且截断全程保留，并未被解析为选定的某一边。
<!--ja-->
対の場合も同じ計画に従います。`EmptyPair→PairOf∅` は第一成分に空要素の変換を再利用し、`W` の所属はそのまま保ち、分類を要素ごとに書き換えます。すなわち、各要素が空であるか `W` と等しいかという切り捨てられた主張を、`Empty'` を `∅` との等しさに置き換えた対応する切り捨てられた主張へ写すのです。結果はまさに `∅` を基準とする分類であり、切り詰めは選ばれた側に解決されることなく全体を通じて保たれます。
<!--/-->

```agda

  EmptyPair→PairOf∅ : (W w : V ℓ) → EmptyPair W w → PairOf∅ W w
  EmptyPair→PairOf∅ W w (h₁ , hW , hall) = empty-member w h₁ , hW
    , (λ z hz → PT.map (Sum.map (empty'→∅ z) (λ e → e)) (hall z hz))

  SglOf∅→EmptySgl : (w : V ℓ) → SglOf∅ w → EmptySgl w
  SglOf∅→EmptySgl w (h∅ , hall) =
```

<!--en-->
The converse direction needs no witness at all, since the empty set is named from the start. `SglOf∅→EmptySgl` produces the truncated witness directly: `∅` belongs to `w` by assumption, and it is empty by the converse lemma applied to the definitional path `∅ ≡ ∅`. The universal clause converts by the same lemma in the other direction. `PairOf∅→EmptyPair` keeps that witness, carries the membership of `W` over unchanged, and rewrites the classification clause pointwise.
<!--zh-->
反方向完全不需要寻找见证，因为空集从一开始就被点名。`SglOf∅→EmptySgl` 直接产出截断见证：`∅` 按假定属于 `w`，而由沿定义性路径 `∅ ≡ ∅` 应用反向引理知它是空的。全称子句由同一引理朝另一方向转换。`PairOf∅→EmptyPair` 保留该见证，原样继承 `W` 的隶属，并逐点改写分类子句。
<!--ja-->
逆方向では証人を探す必要はまったくありません。空集合が最初から名指しされているからです。`SglOf∅→EmptySgl` は切り詰められた証人を直接作ります。`∅` は仮定により `w` に属し、定義的なパス `∅ ≡ ∅` に逆向きの補題を適用すれば空であることが分かります。全称の節は同じ補題を逆の向きで変換します。`PairOf∅→EmptyPair` はこの証人を保ち、`W` の所属をそのまま引き継ぎ、分類の節を各点で書き換えます。
<!--/-->

```agda
      (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
    , (λ z z∈w → ∅→empty' z (hall z z∈w))

  PairOf∅→EmptyPair : (W w : V ℓ) → PairOf∅ W w → EmptyPair W w
  PairOf∅→EmptyPair W w (h∅ , hW , hall) =
      (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
```

<!--en-->
In that pair conversion, the classification runs in the opposite direction: a member known merely to be `∅` or `W` becomes one that is empty or equals `W`, using `∅→empty'` on the first branch and nothing on the second. The section then abstracts the pattern both directions share. `PairWitness P R Q` packages the three clauses that a Kuratowski-pair characterization reads off a set `Q`: a truncated existence of a member of `Q` carrying `P`, the same for `R`, and a truncated dichotomy assigning to every member of `Q` one of `P` or `R`.
<!--zh-->
在这条有序对转换中，分类沿反方向运行：仅已知为 `∅` 或 `W` 的成员变成「空的或等于 `W`」的成员，第一分支用 `∅→empty'`，第二分支无需改动。本节随后抽象出两个方向共享的模式。`PairWitness P R Q` 打包了从集合 `Q` 读出 Kuratowski 对刻画所需的三条子句：`Q` 的某个携带 `P` 的成员的截断存在，对 `R` 同样，以及给 `Q` 的每个成员指派 `P` 或 `R` 之一的截断二分。
<!--ja-->
この対の変換では、分類が逆向きに走ります。`∅` か `W` であると命題的に分かっている要素を、空であるか `W` と等しいかの要素へ変えます。第一の分岐には `∅→empty'` を使い、第二の分岐はそのままで構いません。続いてこの節は、両方向が共有するパターンを抽象化します。`PairWitness P R Q` は、Kuratowski 対の特徴づけが集合 `Q` から読み取る三つの節を束ねます。すなわち、`P` を持つ `Q` の要素の切り詰められた存在、`R` についても同様、そして `Q` のすべての要素に `P` か `R` のいずれかを割り当てる切り詰められた二分法です。
<!--/-->

```agda
    , (hW , λ z z∈w → PT.map (Sum.rec (λ e → inl (∅→empty' z e)) (λ e → inr e))
        (hall z z∈w))

  PairWitness : (V ℓ → Type (ℓ-suc ℓ)) → (V ℓ → Type (ℓ-suc ℓ)) → V ℓ → Type (ℓ-suc ℓ)
  PairWitness P R Q = ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × P w) ∥₁
    × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × R w) ∥₁
```

<!--en-->
Everything above is one conversion applied three times. `map-witness` takes a `PairWitness P R Q` together with two pointwise implications, one sending each `P w` to `P' w` and one sending each `R w` to `R' w`, and returns a `PairWitness P' R' Q`. This is exactly the shape of the whole section: the empty-based predicates and the `∅`-based predicates package the same three-clause structure about the same set, and the four conversion lemmas supply the required pointwise implications in both directions.
<!--zh-->
上述的一切只是同一次转换应用三遍。`map-witness` 取一个 `PairWitness P R Q` 以及两条逐点蕴含，一条把每个 `P w` 送到 `P' w`，另一条把每个 `R w` 送到 `R' w`，并返回 `PairWitness P' R' Q`。这正是整节的形状：以空性为基准的谓词与以 `∅` 为基准的谓词，是关于同一集合的同一三子句结构的两种包装，而四条转换引理恰在两个方向提供所需的逐点蕴含。
<!--ja-->
ここまでの内容は、一つの変換を三度適用したものにすぎません。`map-witness` は `PairWitness P R Q` と二つの各点の含意、すなわち各 `P w` を `P' w` に送るものと各 `R w` を `R' w` に送るものを受け取り、`PairWitness P' R' Q` を返します。これがまさにこの節全体の形です。空性に基づく述語と `∅` に基づく述語は、同じ集合についての同じ三節の構造を包んだ二つの形であり、四つの変換補題が必要な各点の含意を両方向に供給します。
<!--/-->

```agda
    × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ P y ⊎ R y ∥₁))

  map-witness : {P R P' R' : V ℓ → Type (ℓ-suc ℓ)} (Q : V ℓ)
    → ((w : V ℓ) → P w → P' w) → ((w : V ℓ) → R w → R' w)
    → PairWitness P R Q → PairWitness P' R' Q
  map-witness Q f g (h₁ , h₂ , h₃) =
```

<!--en-->
The forward theorem `prChar∅-fwd` now takes the three empty-based hypotheses, in the truncated shapes in which satisfaction of `tag0At` presents them, and concludes the path `Q ≡ pr ∅ W`. The conversion lemma is applied once, transforming the hypotheses into the three clauses about `∅`; the general pair characterization then identifies `Q` with the Kuratowski pair of `∅` and `W` by extensionality. The truncated witnesses are never extracted into ordinary data; they are used only inside conversions whose outputs are the proposition-shaped clauses the characterization accepts.
<!--zh-->
于是正向定理 `prChar∅-fwd` 取三条以空性为基准的假设，其截断形状正是 `tag0At` 的满足呈现出来的形状，并得出路径 `Q ≡ pr ∅ W`。转换引理被应用一次，把假设变成关于 `∅` 的三子句；随后一般配对刻画由外延性把 `Q` 等同为 `∅` 与 `W` 的 Kuratowski 对。截断的见证从不被提取为普通数据；它们只在转换内部使用，而转换的输出正是该刻画所接受的取值为命题的子句。
<!--ja-->
そこで順方向の定理 `prChar∅-fwd` は、空性に基づく三つの仮定、すなわち `tag0At` の充足が現す切り詰められた形の仮定を受け取り、パス `Q ≡ pr ∅ W` を結論します。変換補題が一度適用され、仮定は `∅` に関する三つの節へ変わります。続いて一般の対の特徴づけが外延性により、`Q` を `∅` と `W` の Kuratowski 対と同一視します。切り詰められた証人が通常のデータとして取り出されることは決してなく、それらは変換の内部でのみ使われ、その出力は特徴づけが受け入れる命題の形をした節です。
<!--/-->

```agda
      PT.map (λ { (w , hw , h) → w , hw , f w h }) h₁
    , PT.map (λ { (w , hw , h) → w , hw , g w h }) h₂
    , (λ y hy → PT.map (Sum.map (f y) (g y)) (h₃ y hy))

prChar∅-fwd : (Q W : V ℓ)
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
```

<!--en-->
The backward theorem `prChar∅-bwd` mirrors this: from the path `Q ≡ pr ∅ W` it returns the three empty-based clauses, by running the general pair characterization backwards with its first component at `∅` and its second at `W`, and then converting each resulting clause into its empty-based counterpart. With both theorems in place, satisfaction of `tag0At s x` is interchangeable with the equality of the value at slot `s` with the tagged pair `pr ∅ (⟦ var x ⟧ γ)`, which is the reading the extension clauses of the next section consume.
<!--zh-->
反向定理 `prChar∅-bwd` 与之互为镜像：从路径 `Q ≡ pr ∅ W` 出发，先把一般配对刻画反向运行，第一分量取 `∅`、第二分量取 `W`，再把所得的每条子句转换成以空性为基准的对应物，返回三条这样的子句。两条定理就位后，`tag0At s x` 的满足即可与「槽位 `s` 处的值等于带标签对 `pr ∅ (⟦ var x ⟧ γ)`」互换，这正是下一节扩张子句要使用的读式。
<!--ja-->
逆方向の定理 `prChar∅-bwd` はこれと鏡像です。パス `Q ≡ pr ∅ W` から出発し、一般の対の特徴づけを第一成分 `∅`、第二成分 `W` で逆向きに走らせ、得られた各節を空性に基づく対応物へ変換して、三つの節を返します。両定理がそろえば、`tag0At s x` の充足は「スロット `s` の値がタグ付き対 `pr ∅ (⟦ var x ⟧ γ)` と等しい」という主張と互いに交換可能になり、これが次の節の拡張の条件が使う読みになります。
<!--/-->

```agda
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁)
  → Q ≡ pr ∅ W
prChar∅-fwd Q W h₁ h₂ h₃ = prChar-fwd Q ∅ W (fst h) (fst (snd h)) (snd (snd h))
  where
```

<!--en-->
The intermediate predicate `PairWitness` keeps the argument independent of any particular construction of `Q`. Only the pointwise meaning of its two possible components changes: first emptiness is replaced by equality with `∅`, or conversely, and the general pair characterization then applies without reopening the truncated witnesses.
<!--zh-->
中间谓词 `PairWitness` 使论证不依赖于 `Q` 的具体构造。改变的只有两个可能分量的逐点含义：先把空性换成「等于 `∅`」，或沿反方向换回；随后即可应用一般的配对刻画，而无需重新打开截断见证。
<!--ja-->
中間述語 `PairWitness` によって、議論は `Q` の具体的な構成から独立になります。変わるのは二つの候補成分の各点での意味だけです。空であることを `∅` との等しさに置き換えるか、その逆に戻した後、切り捨てられた証人を開き直さずに一般の対の特徴づけを適用できます。
<!--/-->

```agda
  h : PairWitness SglOf∅ (PairOf∅ W) Q
  h = map-witness Q EmptySgl→SglOf∅ (EmptyPair→PairOf∅ W) (h₁ , h₂ , h₃)

prChar∅-bwd : (Q W : V ℓ) → Q ≡ pr ∅ W
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
```

<!--en-->
The adequacy lemma is stated as a path between truth values, in the same form the earlier readers used. On the left is the satisfaction of `tag0At s x`; on the right, the proposition that the value at slot `s` equals `pr ∅ (⟦ var x ⟧ γ)`, the Kuratowski pair whose tag is the empty set and whose second component is the value at slot `x`, packaged with the proof that the equality type is a proposition because `V ℓ` is an h-set. This says exactly that the encoded zeroth entry is the pair of the empty tag with the new value.
<!--zh-->
充分性引理与前面各读式一样，被陈述为真值之间的一条路径。左侧是 `tag0At s x` 的满足关系；右侧是命题「槽位 `s` 处的值等于 `pr ∅ (⟦ var x ⟧ γ)`」，即标签为空集、第二分量为槽位 `x` 处之值的 Kuratowski 对，并附上该相等类型为命题的证明，因为 `V ℓ` 是 h-集。这恰好说明：编码后的第零个条目就是空标签与新值组成的对。
<!--ja-->
妥当性補題は、これまでの読み取りと同じ形式で、真理値の間のパスとして述べられます。左辺は `tag0At s x` の充足であり、右辺は「スロット `s` の値が `pr ∅ (⟦ var x ⟧ γ)` と等しい」という命題です。これは空集合をタグとし第二成分にスロット `x` の値を持つ Kuratowski 対であり、`V ℓ` が h-集合であることから等号の型が命題である証明とともに包まれています。これはまさに、符号化された第 0 項目が空のタグと新しい値の対であることを言っています。
<!--/-->

```agda
  × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁))
prChar∅-bwd Q W e = map-witness Q SglOf∅→EmptySgl (PairOf∅→EmptyPair W) (prChar-bwd Q ∅ W e)

tag0At-adequate : ∀ {n} (s x : Fin n) (γ : (V ℓ) ^ n)
                → (γ ⊨ tag0At s x) ≡ ((⟦ var s ⟧ γ ≡ pr ∅ (⟦ var x ⟧ γ)) , setIsSet _ _)
tag0At-adequate s x γ = ⇔toPath
```

<!--en-->
The proof composes the two lemmas of this section in each direction. Unfolding the satisfaction of the conjunction and the three bounded quantifiers turns the left side into exactly the truncated existence of an empty singleton member, the truncated existence of an empty pair member, and the truncated classification, which is what `prChar∅-fwd` consumes. Backwards, the path `e` goes to `prChar∅-bwd`, whose output the semantics reassembles into satisfaction. Neither direction inspects how any set was built; emptiness is handled entirely through the equivalence between `Empty'` and equality with `∅`.
<!--zh-->
证明在两个方向各复合本节的两条引理。展开合取与三个有界量词的满足关系后，左边恰变成空单点集成员的截断存在、空对成员的截断存在与截断分类，这正是 `prChar∅-fwd` 所消耗的内容。反向则把路径 `e` 交给 `prChar∅-bwd`，其输出由语义重新组装为满足关系。两个方向都不检查任何集合是如何构造的；空性完全通过 `Empty'` 与「等于 `∅`」之间的等价来处理。
<!--ja-->
証明は両方向でこの節の二つの補題を合成します。連言と三つの有界量子の充足を展開すると、左辺はちょうど、空単集合の要素の切り詰められた存在、空対の要素の切り詰められた存在、そして切り詰められた分類になります。これは `prChar∅-fwd` が受け取るものです。逆方向ではパス `e` が `prChar∅-bwd` に渡され、その出力は意味論が充足へと組み立て直します。どちらの向きも集合の構成方法を検査せず、空性はすべて `Empty'` と `∅` との等しいことの間の同値を通じて処理されます。
<!--/-->

```agda
  (λ { (h₁ , h₂ , h₃) → prChar∅-fwd _ _ h₁ h₂ h₃ })
  (λ e → prChar∅-bwd _ _ e)
```

<!--en-->
## Extending an environment

Consing a value onto an assignment does two things at once: the new value lands at index zero, and every old index moves up by one. This section proves that a bounded formula, `consAt`, expresses exactly this transformation on encoded graphs, and that its adequacy holds against an *encoded* environment.

The formula has three clauses: an entry of the new set carries the empty tag and the new value; every entry of the old graph appears in the new one shifted; and every entry of the new one either is that new entry or is a shift of an old one. The adequacy statement is not that the formula merely relates two sets in a cons-like way. Given a function `g` and the hypothesis that the old slot equals the graph `env g`, it concludes the path from the new slot to the graph `env (cons M g)`. Both sides of that equation are sets of the hierarchy, so the proof is extensional: two inclusions are shown, member by member. One direction classifies each member of the new set using the readers of this chapter, the other walks the graph of `cons M g` key by key. At the index the agreement is definitional, since the numeral for `suc k` is the successor of the numeral for `k`.
<!--zh-->
## 扩张环境

向赋值前置一个值同时做两件事：新值落在索引零处，而每个旧序号上移一位。本节证明一条有界公式 `consAt` 恰好在编码图上表达这一变换，并且其充分性针对**编码后的**环境成立。

公式有三条子句：新集合的一个条目带有空标签与新值；旧图的每个条目都出现在新图中并已移位；新图的每个条目要么是那条新条目，要么是某个旧条目的移位。充分性陈述并不是说该公式仅以某种类似 cons 的方式把两个集合联系起来。在给定函数 `g` 与「旧槽位等于图 `env g`」这一假设后，它得出从新槽位到图 `env (cons M g)` 的路径。等式两侧都是层级中的集合，故证明是外延的：逐成员证明两个包含。一个方向用本章各读式对新集合的每个成员分类；另一方向按键逐个走遍 `cons M g` 的图。在索引处相符是定义性的，因为 `suc k` 的数码就是 `k` 的数码的后继。
<!--ja-->
## 環境を拡張する

割当てに値をひとつ前置きすると、二つのことが同時に起こります。新しい値が添字 0 に置かれ、すべての旧添字が一つずつ動くのです。本節は、有界論理式 `consAt` がこの変換を符号化されたグラフの上で正確に表すこと、そしてその妥当性が**符号化された**環境に対して成り立つことを証明します。

論理式は三つの節を持ちます。新しい集合のある項目が空のタグと新しい値を持つこと、旧グラフのすべての項目がずらされて新しいグラフに現れること、そして新しいグラフのすべての項目が、その新しい項目であるか旧項目のずらしであること、です。妥当性の主張は、この論理式が二つの集合を cons に似た形で結びつけるだけだと言うのではありません。関数 `g` と「旧スロットがグラフ `env g` と等しい」という仮定が与えられれば、新しいスロットからグラフ `env (cons M g)` へのパスが結論されます。この等式の両辺はともに階層の集合なので、証明は外延的です。すなわち二つの包含を一要素ずつ示します。一つの方向では本章の読み取りで新しい集合の各要素を分類し、もう一つの方向では鍵ごとに `cons M g` のグラフを辿ります。添字での一致は定義的です。`suc k` の数項は `k` の数項の後者だからです。
<!--/-->

<!--en-->
The host-level operation `cons m g` is the function on `Fin (suc n)` returning `m` at index zero and `g i` at index `suc i`: one value is prepended, and each old value keeps its value only after its index has moved up by one. The formula `consAt e' m e` names three environment variables: the value at `e'` is the candidate extended graph, the value at `m` is the element being consed on, and the value at `e` is the graph being extended.
<!--zh-->
宿主层运算 `cons m g` 是 `Fin (suc n)` 上的函数：索引零处返回 `m`，索引 `suc i` 处返回 `g i`。也就是前置一个值，而每个旧值只在序号上移一位之后仍取原值。公式 `consAt e' m e` 点名三个环境变元：`e'` 处的值是候选的扩张图，`m` 处的值是被前置的元素，`e` 处的值是被扩张的图。
<!--ja-->
ホストレベルの操作 `cons m g` は `Fin (suc n)` 上の関数で、添字 0 では `m` を、添字 `suc i` では `g i` を返します。すなわち値を一つ前置きし、各旧値は添字が一つ動いてから同じ値を保ちます。論理式 `consAt e' m e` は三つの環境変数を名指しします。`e'` の値が候補となる拡張グラフ、`m` の値が前置きされる要素、`e` の値が拡張されるグラフです。
<!--/-->

```agda
cons : ∀ {ℓ'} {X : Type ℓ'} {n : ℕ} → X → (Fin n → X) → Fin (suc n) → X
cons m g zero    = m
cons m g (suc i) = g i

consAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
consAt e' m e =
```

<!--en-->
The three clauses of `consAt` mirror the three defining equations of `cons`. Read under `γ`: the value at `e'` merely has a member satisfying the tagged-pair reader `tag0At zero (suc m)`, so it holds an entry whose tag is empty and whose second component is the value at `m`; every entry of the value at `e` merely has a shift inside the value at `e'`, said by `shiftPairAt` with the old entry in the later slot; and every entry of the value at `e'` merely is that tagged zero entry or the shift of an entry of the value at `e`. Each subformula is built from bounded quantifiers, equations and the two earlier readers, so the checker certifies the whole conjunction as Δ₀, recorded once and for all by `Δ₀-consAt`.
<!--zh-->
`consAt` 的三条子句与 `cons` 的三个定义等式一一对应。在 `γ` 下读：`e'` 处的值仅仅有一个成员满足带标签对读式 `tag0At zero (suc m)`，即它持有一个标签为空、第二分量为 `m` 处之值的条目；`e` 处之值的每个条目仅仅在 `e'` 处之值中有一个移位，由 `shiftPairAt` 表述且旧条目放在靠后的槽位；而 `e'` 处之值的每个条目仅仅是那条带标签的零条目，或 `e` 处之值某条目的移位。每条子公式都由有界量词、等式与前面两条读式构成，故检查器把整个合取认证为 Δ₀，由 `Δ₀-consAt` 一次性记录。
<!--ja-->
`consAt` の三つの節は `cons` の三つの定義等式と対応します。`γ` の下で読むと、`e'` の値はタグ付き対の読み取り `tag0At zero (suc m)` を満たす要素を命題的に一つ持ち、すなわちタグが空で第二成分が `m` の値である項目を保持します。`e` の値の各項目は、`e'` の値の中に自分のずらしが命題的に存在し、これは `shiftPairAt` で、旧項目を後ろのスロットに置いて述べられます。そして `e'` の値のすべての項目は、命題的に、そのタグ付き 0 項目であるか `e` の値の項目のずらしです。各部分式は有界量化子、等式、そして前の二つの読み取りから構成されるので、検査器は連言全体を Δ₀ として証明し、`Δ₀-consAt` が一度だけこれを記録します。
<!--/-->

```agda
  (∃̇∈ (var e') (tag0At zero (suc m)))
  ∧̇ ((∀̇∈ (var e) (∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero))))
  ∧̇ (∀̇∈ (var e') ((tag0At zero (suc m))
                   ∨̇ (∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero)))))

Δ₀-consAt : ∀ {n} (e' m e : Fin n) → Δ₀ (consAt e' m e)
```

<!--en-->
The adequacy lemma carries one extra hypothesis, and it is what makes the conclusion true. Satisfaction of `consAt` alone says only that the new set stands to the old one in the cons relation; to name the old set as a graph, the lemma is given a function `g` of length `k` together with the path `⟦ var e ⟧ γ ≡ env g`. This is the encoded form that certificates hold: a candidate environment appears in a slot as a set, and the hypothesis identifies that set with the graph of the assignment it encodes.
<!--zh-->
充分性引理带有一条额外假设，而正是它使命题为真。`consAt` 的满足本身只说新集合与旧集合处于 cons 关系；要把旧集合指认为一个图，引理额外给定长度为 `k` 的函数 `g` 与路径 `⟦ var e ⟧ γ ≡ env g`。这正是证书所持的编码形式：候选环境以集合的形式出现在槽位中，而该假设把这个集合等同于它所编码的赋值的图。
<!--ja-->
妥当性補題は一つの追加仮定を持ち、これこそが結論を真にするものです。`consAt` の充足だけでは、新しい集合が古い集合と cons の関係にあることしか言えません。古い集合をグラフとして名指しするために、補題は長さ `k` の関数 `g` とパス `⟦ var e ⟧ γ ≡ env g` を追加で受け取ります。これが証明書の保持する符号化された形です。候補の環境は集合としてスロットに現れ、仮定がその集合を、それが符号化する割当てのグラフと同一視します。
<!--/-->

```agda
Δ₀-consAt e' m e = checkΔ₀ (consAt e' m e) tt

consAt-adequate : ∀ {n} (e' m e : Fin n) (γ : (V ℓ) ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → ⟦ var e ⟧ γ ≡ env g
  → (γ ⊨ consAt e' m e)
```

<!--en-->
The conclusion is the analogous identification for the new slot: the value at `e'` equals the graph of `cons M g`, where `M` is the value at `m`. As with the earlier readers, the statement is a path of truth values, with the h-set property of `V ℓ` supplying the propositionhood of the equality. The abbreviations `M`, `E`, `E'` name the values at the three slots, and `⇔toPath` reduces the claim to the two inclusions.
<!--zh-->
结论是对新槽位的同类指认：`e'` 处的值等于 `cons M g` 的图，其中 `M` 是 `m` 处的值。与前面的读式一样，陈述是真值之间的一条路径，等式的命题性由 `V ℓ` 的 h-集性质提供。缩写 `M`、`E`、`E'` 命名三个槽位处的值，`⇔toPath` 把论断归约为两个包含。
<!--ja-->
結論は新しいスロットに対する同種の同一視です。`e'` の値は `cons M g` のグラフと等しく、ここで `M` は `m` の値です。これまでの読み取りと同様に、主張は真理値の間のパスであり、等式の型の命題性は `V ℓ` の h-集合性から供給されます。略称 `M`、`E`、`E'` が三つのスロットの値を名指しし、`⇔toPath` が主張を二つの包含へ帰着させます。
<!--/-->

```agda
  ≡ ((⟦ var e' ⟧ γ ≡ env (cons (⟦ var m ⟧ γ) g)) , setIsSet _ _)
consAt-adequate e' m e γ {k} g hE = ⇔toPath fwd bwd
  where
  M = ⟦ var m ⟧ γ
  E = ⟦ var e ⟧ γ
```

<!--en-->
The auxiliary `shift-path` records the renumbering arithmetic once: if two encoded entries are equal as pairs, then the entries with both keys replaced by their von Neumann successors and the values kept are equal as well. The injectivity of the Kuratowski pair `pr-inj` splits the assumed path into a path of keys and a path of values, and `cong₂` recombines them under the shifted pair constructor.
<!--zh-->
辅助引理 `shift-path` 一次性记录重编号算术：若两个编码条目作为对相等，则把两侧的键都换成各自的 von Neumann 后继、值保持不变后的条目也相等。Kuratowski 对的单射性 `pr-inj` 把假定路径拆成键的路径与值的路径，再用 `cong₂` 在移位后的对构造子下重新组合。
<!--ja-->
補助的な `shift-path` は番号付け替えの算術を一度に記録します。符号化された二つの項目が対として等しければ、両側の鍵をそれぞれの von Neumann 後者に置き換え、値を保った項目もまた等しい、というものです。Kuratowski 対の単射性 `pr-inj` が仮定のパスを鍵のパスと値のパスに分解し、`cong₂` がずらした対の構成子の下で再結合します。
<!--/-->

```agda
  E' = ⟦ var e' ⟧ γ
  G' : Fin (suc k) → V ℓ
  G' = cons M g

  shift-path : {a b x y : V ℓ} → pr a x ≡ pr b y → pr (sucV a) x ≡ pr (sucV b) y
  shift-path {a} {b} {x} {y} e = cong₂ (λ a b → pr (sucV a) b) (fst p) (snd p)
```

<!--en-->
The forward inclusion takes the third clause of the formula and turns it into a genuine membership statement. Its hypothesis says: every member `y` of `E'` merely either satisfies the tagged zero reader in the environment extended by `y`, or satisfies the bounded existential whose witness is an entry of `E` shifting to `y`. The goal is that `y` belongs to `env G'`, the graph of the extended assignment. Note the shape of the hypothesis: it is the truncated disjunction exactly as the bounded universal quantifier of the formula produces it.
<!--zh-->
正向包含取公式的第三条子句，把它变成真正的隶属陈述。其假设说：`E'` 的每个成员 `y`，仅仅或者在扩张了 `y` 的环境中满足带标签零读式，或者满足一个有界存在式，其见证是 `E` 中移位到 `y` 的条目。目标是 `y` 属于 `env G'`，即扩张后赋值的图。注意假设的形状：它恰如公式的有界全称量词所产出的那个截断析取。
<!--ja-->
順方向の包含は、論理式の第三の節を受け取り、それを本物の所属の主張に変えます。その仮定は、`E'` の各要素 `y` が、命題的に、`y` を追加した環境でタグ付き 0 の読み取りを満たすか、あるいは `E` の要素で `y` へとずらされるものを証人とする有界存在を満たすかのいずれかである、と言います。目標は `y` が拡張後の割当てのグラフ `env G'` に属することです。仮定の形に注意してください。これは論理式の有界全称量化子が生むのとまさに同じ、切り詰められた選言です。
<!--/-->

```agda
    where
    p : (a ≡ b) × (x ≡ y)
    p = pr-inj e

  classify : ((y : V ℓ) → ⟨ y ∈ E' ⟩
               → ∥ ⟨ (y ∷ γ) ⊨ tag0At zero (suc m) ⟩
```

<!--en-->
The truncated disjunction can be eliminated only into a proposition-valued target, and membership in `env G'` is one. The two branches are then handled separately: the first receives the satisfaction of the tagged zero reader and produces the zero key of the graph.
<!--zh-->
截断析取只能消除到取值为命题的目标，而「属于 `env G'`」正是命题。随后两个分支分别处理：第一分支接收带标签零读式的满足，产出图的零键。
<!--ja-->
切り詰められた選言は命題値の対象へしか消除できませんが、`env G'` への所属はまさに命題です。二つの分岐はそれぞれ別に処理されます。最初の分岐はタグ付き 0 の読み取りの充足を受け取り、グラフの鍵 0 を生み出します。
<!--/-->

```agda
                 ⊎ ⟨ (y ∷ γ) ⊨ ∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero) ⟩ ∥₁)
           → (y : V ℓ) → ⟨ y ∈ E' ⟩ → ⟨ y ∈ env G' ⟩
  classify h₃ y y∈E' = PT.rec ((y ∈ env G') .snd)
    (Sum.rec
      (λ tsat →
```

<!--en-->
In the first branch, the member `y` satisfies `tag0At zero (suc m)` in `y ∷ γ`, and the adequacy lemma for that reader converts the satisfaction into the path `y ≡ pr ∅ M`: the value in slot zero is `y` itself, and the original value at slot `m` is still addressed by `suc m` under the new binder. Reversing this path gives `pr ∅ M ≡ y`, which is exactly the entry of `env G'` at key zero, since `G' zero` computes to `M` and the numeral of zero computes to the empty set. The witness is therefore `lift zero` with that path.
<!--zh-->
第一分支中，成员 `y` 在 `y ∷ γ` 中满足 `tag0At zero (suc m)`，该读式的充分性引理把满足转换为路径 `y ≡ pr ∅ M`：槽位零处的值就是 `y` 本身，而新绑定之下的 `suc m` 仍指向原赋值槽位 `m` 的取值。反转这条路径得 `pr ∅ M ≡ y`，恰是 `env G'` 在键零处的条目，因为 `G' zero` 化归为 `M`，零的数码化归为空集。于是见证就是 `lift zero` 配上该路径。
<!--ja-->
第一の分岐では、要素 `y` が `y ∷ γ` の中で `tag0At zero (suc m)` を満たし、この読み取りの妥当性補題が充足をパス `y ≡ pr ∅ M` に変換します。スロット 0 の値は `y` そのものであり、新しい束縛子の内側で `suc m` は元の割り当てのスロット `m` の値を指します。このパスを逆向きにすれば `pr ∅ M ≡ y` が得られ、これは鍵 0 における `env G'` の項目そのものです。`G' zero` は `M` に、0 の数項は空集合に計算されるからです。したがって証人はこのパスを伴う `lift zero` です。
<!--/-->

```agda
        ∣ lift zero
        , sym (subst ⟨_⟩ (tag0At-adequate zero (suc m) (y ∷ γ)) tsat) ∣₁)
      (λ ssat → PT.rec ((y ∈ env G') .snd)
        (λ { (p , p∈E , sh) → PT.rec ((y ∈ env G') .snd)
          (λ { (li , peq) → PT.rec ((y ∈ env G') .snd)
```

<!--en-->
The second branch is the shift case, and it opens three nested truncations in turn. The satisfaction of the bounded existential yields merely an entry `p` of `E` together with a shift clause about the two-entry environment `p ∷ y ∷ γ`; the adequacy lemma for `shiftPairAt` converts that clause into the mere existence of sets `i` and `v` with `p ≡ pr i v` and `y ≡ pr (sucV i) v`. Here the roles of the two slots matter: in `shiftPairAt (suc zero) zero` the old entry sits in the later slot and the shifted one in slot zero, which is why `y` is the pair with the successor key.
<!--zh-->
第二分支是移位情形，它依次打开三层嵌套的截断。有界存在式的满足仅仅给出 `E` 的一个条目 `p`，以及关于二元环境 `p ∷ y ∷ γ` 的一条移位子句；`shiftPairAt` 的充分性引理把该子句转换为集合 `i` 与 `v` 的仅仅存在，使 `p ≡ pr i v` 且 `y ≡ pr (sucV i) v`。这里两个槽位的角色很关键：在 `shiftPairAt (suc zero) zero` 中，旧条目坐在靠后的槽位，被移位者坐在槽位零，故 `y` 是带后继键的那个对。
<!--ja-->
第二の分岐はずらしの場合で、入れ子になった三つの切り詰めを順に開きます。有界存在の充足は、`E` の要素 `p` と、二項目の環境 `p ∷ y ∷ γ` に関するずらしの節を命題的に与え、`shiftPairAt` の妥当性補題がその節を、`p ≡ pr i v` かつ `y ≡ pr (sucV i) v` となる集合 `i` と `v` の単なる存在へ変換します。ここで二つのスロットの役割が重要です。`shiftPairAt (suc zero) zero` では旧項目が後ろのスロットに、ずらされたものがスロット 0 に置かれるため、`y` が後続の鍵を持つ対になるのです。
<!--/-->

```agda
            (λ { (i , v , epv , eyv) →
                ∣ lift (suc (lower li))
                , sym (shift-path (sym epv ∙ sym peq))
                ∙ sym eyv ∣₁ })
            (subst ⟨_⟩ (shiftPairAt-adequate (suc zero) zero (p ∷ y ∷ γ)) sh) })
```

<!--en-->
In the shift case, once the index `i` and value `v` behind the old entry are explicit, the membership in `env G'` is assembled from what the graph of the extended assignment holds. Its entry at the successor of the old key carries the old value, so the required witness is the index `suc (lower li)` together with a path from that entry to `y`. The path is composed from three equations: the old entry equals the pair `pr i v`, shifting both keys by the von Neumann successor turns it into the pair with the shifted key and the same value, and the entry of `env G'` at that key equals `y`. What the composition records is exactly the mathematical content of the case: the new key is the successor of the old one and the value is preserved.
<!--zh-->
在移位情形中，一旦旧条目背后的索引 `i` 与值 `v` 显式可得，`env G'` 中的隶属便可由扩张后赋值的图直接拼出。图在后继键处的条目携带旧值，故所需的见证是索引 `suc (lower li)` 连同从该条目到 `y` 的一条路径。这条路径由三个等式复合：旧条目等于对 `pr i v`；把两侧的键都换成 von Neumann 后继后，它变成带后继键、值不变的对；而 `env G'` 在该键处的条目等于 `y`。这一复合记录的正是该情形的数学内容：新键是旧键的后继，且值保持不变。
<!--ja-->
ずらしの場合では、古い項目の背後にある添字 `i` と値 `v` が明示できれば、`env G'` への所属は拡張後の割当てのグラフが持つ項目から直接組み立てられます。グラフは後続の鍵の位置で古い値を担うので、必要な証人は添字 `suc (lower li)` と、その項目から `y` へのパスです。このパスは三つの等式の合成です。古い項目が対 `pr i v` に等しいこと、両側の鍵を von Neumann 後者に置き換えると同じ値を持つずらされた鍵の対になること、そして `env G'` のその鍵での項目が `y` に等しいことです。この合成が記録しているのはまさにこの場合の数学的内容、すなわち新しい鍵が古い鍵の後者であり値が保たれるということです。
<!--/-->

```agda
          (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E) })
        ssat))
    (h₃ y y∈E')

  covered : ⟨ γ ⊨ ∃̇∈ (var e') (tag0At zero (suc m)) ⟩
          → ((p : V ℓ) → ⟨ p ∈ E ⟩
```

<!--en-->
One step of the shift case remains. The entry `p` was found as a member of `E`, but the graph membership the argument needs sits in `env g`, and the hypothesis `E ≡ env g` transports the membership across. Inside the graph, the lookup lemma of the first section identifies the value stored at the key for the index the witness names. With this the first inclusion is complete: every member of the new set merely lands in the graph of the extended assignment.
<!--zh-->
移位情形还剩一步。条目 `p` 是作为 `E` 的成员找到的，而论证所需的图隶属在 `env g` 中，假设 `E ≡ env g` 把这条隶属沿路径搬运过去。在图内部，第一节证明的查值引理辨认出见证所指索引的键处存放的值。至此第一个包含完成：新集合的每个成员仅仅落入扩张后赋值的图。
<!--ja-->
ずらしの場合にはもう一歩残っています。項目 `p` は `E` の要素として見つかりましたが、議論が必要とするグラフへの所属は `env g` の中にあり、仮定 `E ≡ env g` がこの所属をパスに沿って輸送します。グラフの内部では、最初の節で証明した参照の補題が、証人の指す添字の鍵に格納された値を特定します。これで第一の包含は完成です。新しい集合のすべての要素が命題的に拡張後の割当てのグラフに落ちます。
<!--/-->

```agda
              → ⟨ (p ∷ γ) ⊨ ∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero)) ⟩)
          → (y : V ℓ) → ⟨ y ∈ env G' ⟩ → ⟨ y ∈ E' ⟩
  covered h₁ h₂ y y∈G' = PT.rec ((y ∈ E') .snd)
    (λ { (lj , eq) → byKey (lower lj) eq })
    y∈G'
```

<!--en-->
The reverse inclusion must show that every member of the graph of the extended assignment belongs to the new set. Membership in a graph is truncated fiber data: an index of the graph together with a path saying that the entry at that index equals the given element. So a member `y` is read off with its index and entry path, and the proof then splits on the index, because the two defining equations of `cons` produce exactly two kinds of entries: the new one at index zero and the shifted old ones at successor indices.
<!--zh-->
反向包含要证明：扩张后赋值的图的每个成员都属于新集合。图中的隶属是截断的纤维数据：一个图索引，加上说该索引处条目等于给定元素的路径。于是成员 `y` 连同它的索引与条目路径一起被读出，随后证明对索引分情形，因为 `cons` 的两条定义等式恰好产出两类条目：索引零处的新条目，以及各后继索引处的移位旧条目。
<!--ja-->
逆向きの包含は、拡張後の割当てのグラフのすべての要素が新しい集合に属することを示さねばなりません。グラフへの所属は切り詰められたファイバーのデータ、すなわちグラフの添字と、その添字の項目が与えられた要素に等しいというパスからなります。したがって要素 `y` はその添字と項目のパスとともに読み取られ、その後、証明は添字について場合分けして進みます。`cons` の二つの定義等式が生むのはちょうど二種類の項目、添字 0 の新しい項目と、後続の添字にあるずらされた古い項目だからです。
<!--/-->

```agda
    where
    byKey : (j : Fin (suc k)) → pr (# (toℕ j)) (G' j) ≡ y → ⟨ y ∈ E' ⟩
    byKey zero eq = PT.rec ((y ∈ E') .snd)
      (λ { (q , q∈E' , tsat) →
        subst (λ z → ⟨ z ∈ E' ⟩)
```

<!--en-->
In the zero case the entry equation computes to the statement that the entry with the empty tag and the value `M` equals `y`. The first clause of the formula supplies, merely, a member `q` of the new set whose tagged entry is the pair of the empty tag and `M`; its adequacy lemma turns the satisfaction into exactly that equality. Chaining the two paths gives `q ≡ y`, and transporting the membership of `q` along it yields the membership of `y` in the new set. Nothing about `q` beyond this equation is used, so the truncated witness inside the first clause is eliminated only into a proposition, as required. The successor case runs the argument the other way: the entry equation now names an old entry of `g`, and the second clause of the formula must produce its shift inside the new set.
<!--zh-->
零键情形中，条目等式按定义化归为「带空标签、值为 `M` 的条目等于 `y`」。公式的第一条子句仅仅给出新集合的一个成员 `q`，其带标签条目是空标签与 `M` 配成的对；它的充分性引理把满足关系变成恰好那条等式。把两条路径链接起来得 `q ≡ y`，沿它搬运 `q` 的隶属便得 `y` 在新集合中的隶属。除这条等式外并未使用 `q` 的任何信息，故第一条子句内部的截断见证只被消除进一个命题，恰如所需。后继情形则反向运行该论证：条目等式此时点名了 `g` 的一个旧条目，而公式的第二条子句必须在新集合中产出它的移位。
<!--ja-->
0 の場合、項目の等式は定義計算により「空のタグと値 `M` を持つ項目が `y` に等しい」という主張に帰着します。論理式の第一の節は、新しい集合の要素 `q` で、そのタグ付き項目が空のタグと `M` の対であるものを命題的に与え、その妥当性補題が充足をちょうどその等式に変えます。二つのパスを連結すれば `q ≡ y` となり、これに沿って `q` の所属を輸送すれば新しい集合への `y` の所属が得られます。この等式以外に `q` についての情報は使われないため、第一の節の内部の切り詰められた証人は、求められているとおり、命題の中へのみ消去されます。後続の場合は議論を逆向きに走らせます。項目の等式が今や `g` の古い項目を名指しし、論理式の第二の節がそのずらしを新しい集合の中に生み出さねばならないのです。
<!--/-->

```agda
          (subst ⟨_⟩ (tag0At-adequate zero (suc m) (q ∷ γ)) tsat ∙ eq)
          q∈E' })
      h₁
    byKey (suc i₀) eq = PT.rec ((y ∈ E') .snd)
      (λ { (p' , p'∈E' , sh) → PT.rec ((y ∈ E') .snd)
```

<!--en-->
In the successor case, the shift clause of the formula yields an index `i`, a value `v`, and two equations: the old entry equals the pair `pr i v`, and the candidate equals the shifted pair `pr (sucV i) v`. The goal is a path from the candidate to the member `y`, and the fiber equation provides the shifted graph entry at the successor key, which equals `y`. Since the numeral of the successor index is the successor of the numeral, replacing both keys of the pair `pr i v` by their successors lands exactly on that graph entry. The three equations compose into the required path, and transporting the candidate's membership along it closes the case.
<!--zh-->
后继情形中，公式的移位子句给出索引 `i`、值 `v` 以及两条等式：旧条目等于对 `pr i v`，候选者等于移位后的对 `pr (sucV i) v`。目标是得到从候选者到成员 `y` 的路径，而纤维等式提供后继键处的移位图条目，它等于 `y`。由于后继索引的数码是原数码的后继，把对 `pr i v` 的两个键都换成各自后继后，恰好落在那个图条目上。三条等式复合成所需的路径，沿它搬运候选者的隶属即闭合此情形。
<!--ja-->
後続の場合、論理式のずらしの節は添字 `i`、値 `v`、そして二つの等式を与えます。古い項目が対 `pr i v` に等しいことと、候補がずらされた対 `pr (sucV i) v` に等しいことです。目標は候補から要素 `y` へのパスであり、ファイバーの等式は後続の鍵にあるずらされたグラフの項目を提供し、それは `y` に等しくなります。後続の添字の数項は元の数項の後者なので、対 `pr i v` の両方の鍵をそれぞれの後者に置き換えると、ちょうどそのグラフの項目に着地します。三つの等式が合成されて必要なパスとなり、これに沿って候補の所属を輸送すればこの場合が閉じます。
<!--/-->

```agda
        (λ { (i , v , epv , ep'v) →
          subst (λ z → ⟨ z ∈ E' ⟩)
            (ep'v
             ∙ shift-path (sym epv)
             ∙ eq)
```

<!--en-->
One input was still missing. The shift clause is a satisfaction statement evaluated in an environment whose second slot must hold the old entry `pr (# (toℕ i₀)) (g i₀)` itself, and the second clause of the formula supplies the corresponding membership. This is where the lookup lemma is spent: at the key for `i₀` the graph of `g` holds exactly `g i₀`, and the canonical fiber consisting of the index and `refl` witnesses that membership. Transporting it along the hypothesis that the old set equals the graph of `g` turns it into membership in the encoded environment.
<!--zh-->
还差一个输入。移位子句是一条满足陈述，它所在环境的第二槽必须真的存放旧条目 `pr (# (toℕ i₀)) (g i₀)` 本身，而公式的第二条子句提供相应的隶属。查值引理正是在此处被使用：在 `i₀` 的键处，`g` 的图恰好存放 `g i₀`，由索引与 `refl` 组成的典范纤维见证这条隶属。沿「旧集合等于 `g` 的图」这条假设搬运，便把它变成编码环境中的隶属。
<!--ja-->
まだ一つ入力が欠けていました。ずらしの節は充足の主張であり、その評価に使われる環境の第 2 スロットには、古い項目 `pr (# (toℕ i₀)) (g i₀)` そのものが入っていなければなりません。この対応する所属を論理式の第二の節が供給します。参照の補題が使われるのはまさにここです。`i₀` の鍵の位置で `g` のグラフはちょうど `g i₀` を保持し、添字と `refl` からなる正準なファイバーがその所属を証します。これを「古い集合は `g` のグラフに等しい」という仮定に沿って輸送すれば、符号化された環境への所属になります。
<!--/-->

```agda
            p'∈E' })
        (subst ⟨_⟩
          (shiftPairAt-adequate zero (suc zero) (p' ∷ pr (# (toℕ i₀)) (g i₀) ∷ γ)) sh) })
      (h₂ (pr (# (toℕ i₀)) (g i₀))
          (subst (λ z → ⟨ pr (# (toℕ i₀)) (g i₀) ∈ z ⟩) (sym hE) ∣ lift i₀ , refl ∣₁))
```

<!--en-->
With both inclusions established, the forward direction of the adequacy lemma is a single appeal to extensionality of the cumulative hierarchy: two sets with the same members are equal. The three clauses of the formula supply, for each element `y`, the two directions of the membership comparison: from a member of the new set into the graph of the extended assignment, and back. Read in this direction, satisfaction of the formula is converted into an equality of encoded graphs. The remaining direction of the lemma constructs the satisfaction from such an equality.
<!--zh-->
两个包含都建立之后，充分性引理的正向只需一次引用累积层级的外延性：成员相同的两个集合相等。公式的三条子句对每个元素 `y` 给出隶属比较的两个方向：从新集合的成员到扩张后赋值的图，再从图回到新集合。沿这个方向读，公式的满足被转换成编码图之间的相等。引理剩下的方向则从这样的相等构造满足关系。
<!--ja-->
両方の包含が確立されれば、妥当性補題の順方向は累積階層の外延性への一度の訴えで済みます。同じ元を持つ二つの集合は等しいからです。論理式の三つの節が、各要素 `y` に対して所属の比較の二方向を与えます。新しい集合の要素から拡張後の割当てのグラフへ、そしてグラフから新しい集合へ、という方向です。この方向に読めば、論理式の充足は符号化されたグラフの間の等式へと変換されます。補題の残りの方向は、そのような等式から充足を構成します。
<!--/-->

```agda

  fwd : ⟨ γ ⊨ consAt e' m e ⟩ → E' ≡ env G'
  fwd (h₁ , h₂ , h₃) = extensionalV
    (λ y → ⇔toPath (classify h₃ y) (covered h₁ h₂ y))

  bwd : E' ≡ env G' → ⟨ γ ⊨ consAt e' m e ⟩
  bwd e'eq =
```

<!--en-->
The backward direction starts from a path identifying the new set with the graph of the extended assignment and builds the three satisfaction clauses directly. The first clause exhibits the entry at key zero: membership in the graph at index zero holds by the defining equation of `cons`, and the assumed path transfers it to membership in the new set. The tagged-entry clause then holds outright, since the entry with the empty tag and the value `M` is by construction the pair `pr ∅ M`, and the numeral of zero is the empty set.
<!--zh-->
反向从把新集合与扩张后赋值的图等同起来的那条路径出发，直接构造三条满足子句。第一条给出键零处的条目：按 `cons` 的定义等式，图在索引零处的隶属成立，而假定的路径把它转移到新集合中的隶属。带标签条目的子句随后直接成立，因为带空标签、值为 `M` 的条目按构造就是对 `pr ∅ M`，而零的数码就是空集。
<!--ja-->
逆方向は、新しい集合を拡張後の割当てのグラフと同一視するパスから出発し、三つの充足の節を直接構成します。第一の節は鍵 0 の項目を示します。`cons` の定義等式によりグラフの添字 0 での所属は成り立ち、仮定のパスがそれを新しい集合への所属へ移します。タグ付き項目の節はそのまま成り立ちます。空のタグと値 `M` を持つ項目は構成上対 `pr ∅ M` であり、0 の数項は空集合だからです。
<!--/-->

```agda
      ∣ pr (# 0) M
      , subst (λ z → ⟨ pr (# 0) M ∈ z ⟩) (sym e'eq) ∣ lift zero , refl ∣₁
      , subst ⟨_⟩ (sym (tag0At-adequate zero (suc m) (pr (# 0) M ∷ γ))) refl ∣₁
    , (λ p p∈E → PT.rec
        (((p ∷ γ) ⊨ ∃̇∈ (var (suc e')) (shiftPairAt zero (suc zero))) .snd)
```

<!--en-->
The second clause must produce, for every member of the old environment, its shifted counterpart inside the new set. The member's membership transports along the hypothesis to the graph of `g`, where the lookup lemma reads off an index and the equation identifying the entry with the member. The shifted entry is then the pair with the successor numeral as key and the same value; its membership in the new set again comes from the graph of the extended assignment, at the successor index, transferred through the assumed path. What remains is the satisfaction certificate for the shift formula itself.
<!--zh-->
第二条子句要对旧环境的每个成员给出它在新集合中的移位对应物。该成员的隶属沿假设搬运到 `g` 的图中，在那里查值引理读出一个索引以及把条目与该成员等同的等式。移位后的条目于是是以后继数码为键、值不变的对；它在新集合中的隶属同样来自扩张后赋值的图，位于后继索引处，再经假定的路径转移。剩下的只是移位公式本身的满足证书。
<!--ja-->
第二の節は、古い環境の各要素に対して、新しい集合の内側へそのずらされた対応物を生産しなければなりません。その要素の所属は仮定に沿って `g` のグラフへ輸送され、そこで参照の補題が添字と、項目をその要素と同一視する等式を読み取ります。ずらされた項目は、後続の数項を鍵とし値を保つ対です。新しい集合へのその所属も同様に、拡張後の割当てのグラフの後続の添字で成り立ち、仮定のパスを通して移されます。残るのはずらしの論理式そのものの充足の証明です。
<!--/-->

```agda
        (λ { (li , peq) →
          ∣ pr (# (suc (toℕ (lower li)))) (g (lower li))
          , subst (λ z → ⟨ pr (# (suc (toℕ (lower li)))) (g (lower li)) ∈ z ⟩)
              (sym e'eq) ∣ lift (suc (lower li)) , refl ∣₁
          , subst ⟨_⟩
```

<!--en-->
The certificate is produced by running the shift adequacy lemma backwards. Its reading of the formula asks for an index, a value, and two equations: one identifying the old entry with the pair at the index found by lookup, and one saying that the shifted pair is the shifted entry itself, which holds by computation. Because the adequacy statement is an equality of propositions, transporting `refl` along it yields the required satisfaction, and the second clause of the formula is complete for this member.
<!--zh-->
该证书靠反向运行移位的充分性引理得到。引理对公式的解读要求一个索引、一个值和两条等式：一条把旧条目与查值所得索引处的对等同；另一条说移位后的对就是移位后的条目本身，这一点按计算成立。由于充分性陈述是命题之间的相等，沿它搬运 `refl` 便得所需的满足，公式的第二条子句对该成员宣告完成。
<!--ja-->
この証明は、ずらしの妥当性補題を逆向きに走らせることで得られます。補題による論理式の読みは、添字、値、そして二つの等式を要求します。一方は古い項目を、参照が見つけた添字の位置の対と同一視し、もう一方はずらされた対がずらされた項目そのものであると言います。これは計算によって成り立ちます。妥当性の主張は命題の間の等式なので、それに沿って `refl` を輸送すれば必要な充足が得られ、この要素に対して論理式の第二の節が完成します。
<!--/-->

```agda
              (sym (shiftPairAt-adequate zero (suc zero)
                (pr (# (suc (toℕ (lower li)))) (g (lower li)) ∷ p ∷ γ)))
              ∣ # (toℕ (lower li)) , g (lower li) , sym peq , refl ∣₁ ∣₁ })
        (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E))
    , (λ p' p'∈E' → PT.rec squash₁
```

<!--en-->
The third clause is the classification clause: every member of the new environment must satisfy one of the two tagged clauses, merely. To use it, a member `p'` of `E'` is first transported along the path `e'eq` into membership in the encoded graph `env G'`, which is truncated fiber data: an index `j` and the equation `pr (# (toℕ j)) (G' j) ≡ p'` saying that the entry at that key is `p'`. The proof now splits on the index, because the consed graph has exactly two kinds of entries, one for each equation defining `cons`. Since the goal is a truncated disjunction of two propositions, each case may return its clause under the corresponding disjunct, and the truncation wraps the case distinction.
<!--zh-->
第三条子句是分类子句：新环境的每个成员都必须**仅仅**满足两条带标签子句之一。为使用它，先把 `E'` 的成员 `p'` 沿路径 `e'eq` 搬运为编码图 `env G'` 中的隶属，那是截断的纤维数据：一个索引 `j`，以及说该键处条目等于 `p'` 的等式 `pr (# (toℕ j)) (G' j) ≡ p'`。随后按索引分情形，因为 cons 后的图恰有两类条目，对应定义 `cons` 的两条等式。由于目标是一个由两个命题组成的截断析取，每个情形都可以在相应析取支下给出自己的子句，而截断把情形划分包裹起来。
<!--ja-->
第三の節は分類の節です。新しい環境のすべての要素が、タグ付きの二つの節のいずれかを命題的に満たさねばなりません。これを使うには、まず `E'` の要素 `p'` をパス `e'eq` に沿って符号化グラフ `env G'` への所属へ輸送します。これは切り捨てられたファイバーデータ、すなわちインデックス `j` と、その鍵の項目が `p'` に等しいという等式 `pr (# (toℕ j)) (G' j) ≡ p'` です。続いてインデックスで場合分けします。cons 後のグラフの項目は、`cons` を定義する二つの等式に対応して、ちょうど二種類あるからです。目標は二つの命題からなる切り捨てられた選言なので、各場合は対応する選言肢の下で自らの節を返すことができ、切り捨てが場合分けを包み込みます。
<!--/-->

```agda
        (λ { (lj , eq) → byKey' p' (lower lj) eq })
        (subst (λ z → ⟨ p' ∈ z ⟩) e'eq p'∈E'))
    where
    byKey' : (p' : V ℓ) (j : Fin (suc k))
           → pr (# (toℕ j)) (G' j) ≡ p'
```

<!--en-->
At index zero the entry of `G'` is the new one: the equation is `pr (# 0) M ≡ p'`. This is the statement, up to the direction of the path, that `p'` carries the empty tag with value `M`. The adequacy lemma for the tagged reader identifies its satisfaction proposition with the equality `⟦ var zero ⟧ (p' ∷ γ) ≡ pr ∅ M`, and `# 0` computes to `∅`. So the reversed equation, transported along the adequacy path, yields the left disjunct.
<!--zh-->
索引零处 `G'` 的条目是新条目：等式为 `pr (# 0) M ≡ p'`。在调整路径方向之后，这恰好是说 `p'` 带有以 `M` 为值的空标签。带标签读式的充分性引理把其满足命题等同于等式 `⟦ var zero ⟧ (p' ∷ γ) ≡ pr ∅ M`，而 `# 0` 计算为 `∅`。于是取反向的等式、沿充分性路径搬运，便得到左边的析取支。
<!--ja-->
インデックス 0 における `G'` の項目は新しい項目で、等式は `pr (# 0) M ≡ p'` です。パスの向きを整えれば、これは `p'` が値 `M` を伴う空のタグを持つという主張そのものです。タグ付き読み取りの妥当性補題はその充足命題を等式 `⟦ var zero ⟧ (p' ∷ γ) ≡ pr ∅ M` と同一視し、`# 0` は `∅` に計算されます。そこで逆向きの等式を妥当性のパスに沿って輸送すれば、左の選言肢が得られます。
<!--/-->

```agda
           → ∥ ⟨ (p' ∷ γ) ⊨ tag0At zero (suc m) ⟩
             ⊎ ⟨ (p' ∷ γ) ⊨ ∃̇∈ (var (suc e)) (shiftPairAt (suc zero) zero) ⟩ ∥₁
    byKey' p' zero eq =
      ∣ inl (subst ⟨_⟩ (sym (tag0At-adequate zero (suc m) (p' ∷ γ))) (sym eq)) ∣₁
    byKey' p' (suc i₀) eq =
```

<!--en-->
At a successor index, the entry of `G'` is a shifted old entry, and the right disjunct must certify this with the shift formula. The fiber the shift formula asks for has five components, of which the index-as-set and the value slot are straightforward. The old entry slot needs `pr (# (toℕ i₀)) (g i₀)` to be a member of the old environment, which follows from `lookup-spec`: at index `i₀` of `env g`, the entry at that key is the pair with value `g i₀`, and this membership is transported along `hE` into membership in `E`. The shifted entry slot is filled by the numeral-keyed entry `pr (# (toℕ i₀)) (g i₀)` itself, which by `eq` equals `p'`, up to orientation.
<!--zh-->
后继索引处，`G'` 的条目是一个移位后的旧条目，右边的析取支必须用移位公式给出证书。移位公式要求的纤维有五个分量，其中「作为集合的索引」与值槽是直接的。旧条目槽需要 `pr (# (toℕ i₀)) (g i₀)` 属于旧环境，这由 `lookup-spec` 得到：在 `env g` 的索引 `i₀` 处，该键的条目正是以 `g i₀` 为值的对，再沿 `hE` 搬运即得 `E` 中的隶属。移位条目槽由以数码为键的条目 `pr (# (toℕ i₀)) (g i₀)` 本身填入，按 `eq` 它等于 `p'` (方向待调整)。
<!--ja-->
後続インデックスでは、`G'` の項目はずらされた旧項目であり、右の選言肢は shift 式による証明を与えねばなりません。shift 式が要求するファイバーは五つの成分を持ち、そのうち集合としてのインデックスと値のスロットは直接です。旧項目のスロットは `pr (# (toℕ i₀)) (g i₀)` が旧環境に属することを必要としますが、これは `lookup-spec` から従います。`env g` のインデックス `i₀` では、その鍵の項目が値 `g i₀` を持つ対であり、これを `hE` に沿って輸送すれば `E` への所属になります。ずらした項目のスロットは、数項を鍵とする項目 `pr (# (toℕ i₀)) (g i₀)` そのもので埋められ、`eq` により (向きを除けば)`p'` と等しくなります。
<!--/-->

```agda
      ∣ inr ∣ pr (# (toℕ i₀)) (g i₀)
            , subst (λ z → ⟨ pr (# (toℕ i₀)) (g i₀) ∈ z ⟩) (sym hE)
                ∣ lift i₀ , refl ∣₁
            , subst ⟨_⟩
                (sym (shiftPairAt-adequate (suc zero) zero
```

<!--en-->
The two remaining paths complete the fiber. The old-entry path is definitional: the chosen index and value are exactly the numeral of `i₀` and `g i₀`. The shifted path is the reversed `eq`, since the shifted entry is required to equal the candidate pair with the successor key, and that pair is `p'` by assumption. Running the adequacy lemma of `shiftPairAt (suc zero) zero` backwards converts the assembled fiber into its satisfaction, which sits in the right disjunct. Both branches of the case split thus supply their clause merely, exactly as the truncated disjunction of the third clause demands.
<!--zh-->
剩下的两条路径补全纤维。旧条目路径是定义性的：所选的索引与值恰是 `i₀` 的数码与 `g i₀`。移位路径取反向的 `eq`，因为移位条目须等于以后继键构成的那个对，而按假定它就是 `p'`。反向运行 `shiftPairAt (suc zero) zero` 的充分性引理，把装配好的纤维转换为它的满足关系，置于右边析取支之下。于是情形划分的两个分支都只是「仅仅」给出各自的子句，恰如第三条子句的截断析取所要求的那样。
<!--ja-->
残る二つのパスがファイバーを完成させます。旧項目のパスは定義的です。選ばれたインデックスと値は、ちょうど `i₀` の数項と `g i₀` だからです。ずらしのパスは逆向きの `eq` を取ります。ずらされた項目は後続の鍵を持つ対と等しくなければならず、仮定によりその対は `p'` だからです。`shiftPairAt (suc zero) zero` の妥当性補題を逆向きに走らせると、組み立てたファイバーはその充足に変換され、右の選言肢の下に置かれます。こうして場合分けの両分岐は、第三の節の切り捨てられた選言が求めるとおり、それぞれの節を命題的に与えるだけにとどまります。
<!--/-->

```agda
                  (pr (# (toℕ i₀)) (g i₀) ∷ p' ∷ γ)))
                ∣ # (toℕ i₀) , g i₀ , refl , sym eq ∣₁ ∣₁ ∣₁
```

<!--en-->
## Recap

The chapter turned the two environment operations that satisfaction clauses need into statements about sets: looking a value up, and extending an assignment under a quantifier.

The encoding itself is `env`, which stores an assignment as the graph of numeral-keyed pairs, and `lookup-spec` shows the graph is functional: membership of a pair at key `i` holds exactly when its value is `g i`. On the operation side, `sucAt` characterizes the von Neumann successor of a set by the three membership clauses the language can express, and `shiftPairAt` recognizes a single renumbered entry. `consAt` assembles these into the whole transformation: assuming the old slot is the graph of `g`, satisfaction of the formula is the equality of the new slot with the graph of `cons M g`, proved by two inclusions compared through set extensionality, with the truncated witnesses eliminated only into propositions.
<!--zh-->
## 小结

本章把满足关系子句所需的两种环境操作化为关于集合的陈述：查出一个值，以及在量词之下扩张赋值。

编码本身是 `env`，它把赋值存成以数码为键的对的图，而 `lookup-spec` 证明该图是函数性的：一个对在键 `i` 处属于图，恰在其值为 `g i` 时成立。在运算一侧，`sucAt` 用语言所能表达的三条隶属子句刻画一个集合的 von Neumann 后继，`shiftPairAt` 识别单个重编号的条目。`consAt` 把这些装配成整个变换：在旧槽位等于 `g` 的图的假设下，公式的满足就是新槽位与 `cons M g` 的图的相等，其证明由两个包含经集合外延性比较而成，截断的见证只被消除进命题。
<!--ja-->
## まとめ

本章は、充足関係の各節が必要とする二つの環境操作、すなわち値の参照と、量化子の下での割当ての拡張を、集合についての主張に変えました。

符号化そのものは `env` であり、割当てを数項を鍵とする対のグラフとして格納します。`lookup-spec` はこのグラフが関数的であることを示します。ある対が鍵 `i` の位置でグラフに属するのは、その値が `g i` であるとき、そのときに限ります。操作の側では、`sucAt` が言語で表現できる三つの所属の節によって集合の von Neumann 後者を特徴づけ、`shiftPairAt` が番号付け替えされた一つの項目を認識します。`consAt` はこれらを変換全体へ組み立てます。旧スロットが `g` のグラフに等しいという仮定のもとで、論理式の充足は、新しいスロットと `cons M g` のグラフとの等式であり、その証明は二つの包含を集合の外延性で比較するもので、切り捨てられた証人は命題の中へのみ消除されます。
<!--/-->
