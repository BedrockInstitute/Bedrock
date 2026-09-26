```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Adequacy of name comparison
<!--zh-->
# 名字比较的充分性
<!--ja-->
# 名前の比較の妥当性
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The module therefore carries `lem` at the successor universe level throughout.
Its role is inherited through naming, the order on finite syntax codes, and
uniform satisfaction; it is not a licence to extract arbitrary witnesses from
propositional truncations. The adequacy proved below has an intentionally
asymmetric shape: concrete names can be inserted into the formulas, while a
satisfying assignment is read back only as the propositionally truncated
existence of suitable names.
<!--zh-->
因此，模块始终携带后继宇宙层级上的 `lem`。它经命名、有限语法码上的序与一致满足关系传入论证，却不许可从命题截断中任意取出见证。下文证明的充分性有意保持不对称：给定具体名字，可以把它们填入公式；反向读取一个满足赋值时，只得到命题截断下合适名字的存在性。
<!--ja-->
したがって、モジュール全体が後続宇宙レベルの `lem` を携える。この仮定は、命名、有限構文コードの順序、統一充足関係を通して議論に入るが、命題的切り詰めから任意の証人を取り出す許可ではない。以下で示す妥当性は意図的に非対称である。具体的な名前から論理式を充足できる一方、充足する割り当てから読み戻せるのは、適切な名前が存在するという命題的に切り詰められた主張だけである。
<!--/-->

```agda
module L.Choice.NameComparisonAdequacy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp; embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Ordinal {ℓ} using ( #∈ω; ω-ord )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; LsetS )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.Model {ℓ} using ( envOverAt; envOverAt-transport; domAt )
open import L.Coding.Expressions {ℓ} using ( extAt-in; extAt-out; numL; consAtL )
open import L.Coding.EnvironmentSet {ℓ} lem using ( module Recover; envS; envOver )
open import L.Coding.SatisfactionGraph {ℓ} lem using ( satGraphAt )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
open import L.Coding.SatisfactionBridge {ℓ} lem
  using ( consAtL-in; consAtL-out; asConst; values; envFor; envFor-graph )
  renaming ( graph to envGraph )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; AllCodes )
open import L.Coding.UniformSatisfaction {ℓ} lem
  using ( val-at; val-sat; keyIn; keyIn≡; keyIn∈; module Table )
open import L.Choice.CanonicalNames {ℓ} lem using ( module Naming; limitCode )
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Limit; limitOrder )
open import L.Choice.NameComparison {ℓ} lem
  using ( NameAt; NameAt-in; LeastNameAt; ≺At; StepAt; StepOf; StepAt-in; StepAt-out; DenoteOf; DenoteBody; DenoteBody-in; DenoteBody-out
        ; FreeAt; codeFree-in; codeFree-out
        ; graphAt-value; graphAt-only
        ; domAt-numeral; domAt-fill; module Adequacy )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
```

<!--en-->
Many definable subsets admit more than one name. An internal comparison must
therefore do more than recognize a formula and its parameters: it must connect
each displayed set with names that denote it, express leastness among all names
of that same set, and compare the resulting least names. This chapter proves
that the object-language descriptions perform exactly these tasks. In the
reverse direction, the recovered names remain under propositional truncation.
<!--zh-->
同一个可定义子集可能有不止一条名字。因此，内部比较不能只辨认一条公式及其参数，还必须把每个给定集合接到指称它的名字，表达它在所有同指称名字中的最小性，再比较所得的最小名字。本章证明对象语言描述恰好完成这些任务；在反向读取中，恢复出的名字始终保留在命题截断之下。
<!--ja-->
同じ定義可能な部分集合が複数の名前をもつことがある。したがって内部の比較には、論理式とそのパラメータを認識するだけでなく、表示された各集合をそれを指示する名前に結び付け、同じ集合を指示するすべての名前の中での最小性を表し、得られた最小名を比較することが必要である。本章では、対象言語の記述がこれらの役割を正確に果たすことを証明する。逆向きに読み取った名前は、命題的切り詰めの中に保たれる。
<!--/-->

<!--en-->
The shared prelude supplies the book's universe, proposition, finite-index, and
vector conventions. The only classical hypothesis named by this chapter is the
law of excluded middle. It is imported as an ordinary type and will be passed
explicitly to the constructions that require it, so later uses of a satisfaction
table or a name order retain an auditable assumption boundary.
<!--zh-->
共用前奏给出全书关于宇宙、命题、有穷索引与向量的约定。本章明列的唯一经典假设是排中律。它作为普通类型导入，并将显式传给需要它的构造；因此，后文使用满足关系表或名字序时，所依赖的假设边界始终可以核查。
<!--ja-->
共通のプレリュードは、本書における宇宙、命題、有限添字、ベクトルの規約を与える。本章が明示する唯一の古典的仮定は排中律である。これは通常の型として取り込まれ、必要とする構成へ明示的に渡される。そのため、後で充足関係表や名前の順序を使っても、依存する仮定の境界を追跡できる。
<!--/-->



<!--en-->
The semantic comparison needs one syntax and two closely related structures.
`Formula` is the common object language, and constant relabelling moves a formula
between the empty constant domain, a carrier's members, and the surrounding set
universe. The structure on `V` supplies the ambient interpretation. Its
extensionality principle will later turn pointwise agreement of membership
propositions into equality of the sets denoted by two presentations.
<!--zh-->
这次语义比较需要一套语法与两个紧密相关的结构。`Formula` 是共用的对象语言，而常元改名把公式搬过空常元域、载体成员与外围集合宇宙。`V` 上的结构给出外围解释；其外延性原理稍后把成员命题的逐点一致化为两种呈现所指称集合的相等。
<!--ja-->
この意味論的比較には、一つの構文と密接に関係する二つの構造が必要である。`Formula` は共通の対象言語であり、定数の改名によって、空の定数域、台の要素、外側の集合宇宙のあいだで論理式を移す。`V` 上の構造が外側の解釈を与え、その外延性は後に、所属命題の点ごとの一致を、二つの表示が指す集合の等しさへ変える。
<!--/-->

<!--en-->
Names are finite syntactic data interpreted over a constructible carrier, so
the proof must connect coding with `L`. Formula codes are sets assembled from
numerals and pairs; a parameter-free code already lies in the limit stage where
`limitOrder` can compare it. On the semantic side, constructibility and its
transitivity package ambient sets as elements of the structure on `L`, while
internal numerals, the empty constructible set, and environment graphs provide
the concrete objects that the name formulas mention.
<!--zh-->
名字是解释于可构造载体之上的有限语法数据，因此证明必须把编码与 `L` 接起来。公式码是由数码与对组装出的集合；无参公式的码已经落在极限层中，因而可由 `limitOrder` 比较。在语义一侧，可构造性及其传递性把外围集合包装成 `L` 上结构的元素；内部数码、空可构造集与环境图则给出名字公式实际谈及的对象。
<!--ja-->
名前は構成可能な台の上で解釈される有限な構文データなので、証明は符号化と `L` を結ばなければならない。論理式のコードは数項と対から組み立てられ、無パラメータ論理式のコードはすでに極限段階に属するため、`limitOrder` で比較できる。意味論の側では、構成可能性とその推移性が外側の集合を `L` 上の構造の要素として包み、内部の数項、空の構成可能集合、環境グラフが名前の論理式に現れる具体的な対象を与える。
<!--/-->

<!--en-->
The model-side vocabulary expresses the data of a name without yet recovering
one. `envOverAt` says that a candidate set is a single-valued graph with the
prescribed domain, values in the carrier, and no non-pair debris; its transport
lemma lets those three named sets be replaced along slot equalities. `consAtL`
describes how an environment is enlarged by a candidate member, `domAt` records
its length, and `extAt` identifies a denotation by its members. The recovery
module will be crucial in the reverse direction, because the environment-graph
conditions determine each parameter value uniquely.
<!--zh-->
模型一侧的词汇先表达名字的数据，尚不从中恢复名字。`envOverAt` 断言一个候选集合是单值图，具有指定定义域，取值落在载体中，并且不含非对形式的冗余成员；其搬运引理允许沿槽位等式替换这三个指定集合。`consAtL` 描述环境如何添入候选成员，`domAt` 记录其长度，`extAt` 则由成员刻画指称。反向论证中，恢复模块至关重要，因为环境图的这些条件唯一决定每个参数值。
<!--ja-->
モデル側の語彙は、まず名前のデータを表現し、まだ名前そのものを復元しない。`envOverAt` は、候補となる集合が、指定された定義域をもち、値が台に属し、対でない余分な要素を含まない一価グラフであることを述べる。その輸送補題により、これら三つの指定された集合をスロットの等式に沿って置き換えられる。`consAtL` は候補要素を環境へ加える方法を表し、`domAt` はその長さを記録し、`extAt` は要素によって指示対象を特徴づける。逆向きでは、環境グラフのこれらの条件が各パラメータ値を一意に定めるため、復元モジュールが決定的な役割を担う。
<!--/-->

<!--en-->
The next bridge explains how a carrier-level formula becomes a value in the
uniform satisfaction table. Constants naming members of the carrier are
relabeled into the model, their assignment is represented both as an environment
and as an internal graph, and the formula is addressed by a genuine key in the
carrier's code set. Requiring that key to lie in `AllCodes` is essential: only at
such a key do the graph readings force the recorded value to agree with actual
satisfaction.
<!--zh-->
下一座桥说明载体层公式如何成为一致满足关系表中的一个取值。指名载体成员的常元被常元改名后进入模型，其赋值同时表示为环境与内部图，而公式由载体码集中的真实键寻址。要求该键属于 `AllCodes` 不可省略：只有在这样的键处，图的读式才迫使所记录的取值与实际满足关系一致。
<!--ja-->
次の橋は、台の上の論理式が統一充足関係表の値になる仕組みを説明する。台の要素を名指す定数はモデルへ定数改名され、その割り当ては環境と内部グラフの両方で表され、論理式は台のコード集合に属する真正な鍵で参照される。その鍵が `AllCodes` に属するという条件は欠かせない。そのような鍵で初めて、グラフの読みが記録値と実際の充足関係との一致を強制するからである。
<!--/-->

<!--en-->
The mathematical interface now comes into view. `CanonicalNames` supplies a
meta-language name, its code, parameter vector, denotation, and three-key order;
`FiniteStageOrders` supplies the order of the first key. `NameComparison`
supplies the object-language descriptions to be justified. In particular,
`NameAt` has exactly four conceptual conjuncts: a parameter-free skeleton, an
arity numeral in `ω`, a parameter graph of that arity over the carrier, and an
extensional account of the denotation.
<!--zh-->
数学接口至此显出全貌。`CanonicalNames` 给出元语言名字、它的码、参数向量、指称及三键名字序；`FiniteStageOrders` 给出第一键所用的序；`NameComparison` 则给出有待证明充分性的对象语言描述。尤其要注意，`NameAt` 恰有四个概念性合取项：无参骨架、属于 `ω` 的元数数码、该元数之上取值于载体的参数图，以及对指称的外延刻画。
<!--ja-->
ここで数学的なインターフェースの全体像が見える。`CanonicalNames` はメタ言語の名前、そのコード、パラメータ・ベクトル、指示対象、三つの鍵による名前の順序を与え、`FiniteStageOrders` は第一の鍵を比較する順序を与える。`NameComparison` は、これから妥当性を示す対象言語の記述を与える。特に `NameAt` は、無パラメータな骨格、`ω` に属するアリティの数項、そのアリティを定義域として台に値を取るパラメータ・グラフ、指示対象の外延的な特徴づけという、ちょうど四つの概念的な連言項からなる。
<!--/-->

<!--en-->
The rest of the imported interface separates three jobs that must not be
conflated. The code, graph, and domain readings recover the data represented in
slots. The `Adequacy` module compares two already given names by code, arity, and
parameters. This chapter adds the missing statement that arbitrary satisfying
slot data comes from names, and that the recovered names have the stated
minimality property. It still returns those names under propositional truncation,
so none of its read lemmas selects a witness. Only downstream does
`InternalWellOrder` use `leastNameOf`, built from the established well-order, to
obtain particular least names for the filling direction.
<!--zh-->
余下的导入接口把三项不可混同的工作分开。码、图与定义域的读式恢复槽位所表示的数据；`Adequacy` 模块按码、元数与参数比较两条已经给定的名字；本章则补上缺失的一步，证明任意满足槽位数据来自名字，并且恢复出的名字具有所述最小性。所得名字依然留在命题截断之下，所以这里的读取引理都不选出见证。只有到了下游，`InternalWellOrder` 才在填充方向使用由既有良序构造的 `leastNameOf`，取得具体最小名字。
<!--ja-->
残りのインターフェースは、混同してはならない三つの仕事を分ける。コード、グラフ、定義域の読みは、スロットに表現されたデータを復元する。`Adequacy` モジュールは、すでに与えられた二つの名前を、コード、アリティ、パラメータによって比較する。本章はさらに、任意の充足するスロット・データが名前に由来し、復元された名前が述べられた最小性をもつことを示す。ただし名前は命題的切り詰めの中に留まるので、ここでの読みの補題は証人を選ばない。具体的な最小名を得るのは下流だけであり、`InternalWellOrder` が充足を組み立てる向きで、既存の整列順序から構成された `leastNameOf` を使う。
<!--/-->

<!--en-->
Three representation changes recur in the proof. A family indexed by `Fin k`
is tabulated as a length-indexed vector and read back entrywise. Logical
equivalence between membership propositions is converted into the paths needed
for set extensionality. Finally, paths between proof-carrying carriers transport
formula codes and satisfaction sets whose types depend on those carriers. The
empty type handles the branches that these comparisons show to be impossible.
<!--zh-->
证明中反复出现三种表示转换。由 `Fin k` 索引的族被列表化为长度受索引的向量，也可以逐项读回。成员命题之间的逻辑等价被转成集合外延性所需的路径。最后，带证明载体之间的路径负责搬运类型依赖于载体的公式码与满足关系集。经这些比较判定为不可能的分支则由空类型消去。
<!--ja-->
証明では三種類の表示の変換を繰り返し用いる。`Fin k` で添字づけられた族を長さつきベクトルとして表にまとめ、各成分を再び読み取る。所属命題の論理的同値は、集合の外延性に必要なパスへ変換される。さらに、証明を伴う台の間のパスに沿って、型がその台に依存する論理式の符号と充足関係集合を輸送する。これらの比較によって不可能だと分かる分岐は空型から除去する。
<!--/-->

```agda
open import Cubical.Data.Vec.Properties using ( FinVec→Vec; FinVec→Vec→FinVec )
open import Cubical.Foundations.Transport using ( constSubstCommSlice )
```

<!--en-->
Propositional truncation records exactly the strength of the reverse readings.
It preserves that a witness exists while forgetting which witness it was, and
it can be eliminated when the target is itself a proposition. The hierarchy
operations complement this discipline: `⟪ A ⟫` is the small type indexing the
members of a set `A`, its embedding sends an index to the corresponding member,
and `∈-asFiber` recovers such an index from membership. Thus a uniquely
determined entry of an environment can be recovered as data without turning a
merely existing formula or name into chosen data.
<!--zh-->
命题截断精确记录反向读式的强度：它保留见证存在这一事实，却忘去见证是哪一个；当目标本身是命题时，才可从中消去。层级操作与这套纪律相辅相成：`⟪ A ⟫` 是索引集合 `A` 之成员的小类型，其嵌入把索引送到相应成员，而 `∈-asFiber` 从成员关系恢复这样的索引。因此，环境中由单值性唯一确定的条目可以作为数据恢复，却不能据此把仅仅存在的公式或名字变成选定的数据。这里用到的是命题截断，不是命题换级。
<!--ja-->
命題的切り詰めは、逆向きの読みがもつ強さを正確に記録する。証人が存在することは保つが、それがどの証人だったかは忘れ、除去できるのは行き先が命題である場合である。階層の操作はこの規律を補う。`⟪ A ⟫` は集合 `A` の要素を添字づける小さい型で、その埋め込みは添字を対応する要素へ送り、`∈-asFiber` は所属からそのような添字を復元する。したがって、一価性によって一意に定まる環境の成分はデータとして復元できるが、単に存在する論理式や名前を選択済みのデータへ変えることはできない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
```

<!--en-->
Arity crosses the semantic boundary through the von Neumann naturals. The
meta-language number `k` is represented by the set-theoretic numeral `# k`, and
`ω` contains precisely these numerals. Consequently the arity clause of a name
can be read in either direction, and the middle key of name comparison can be
expressed internally by membership of one numeral in another rather than by an
additional relation parameter.
<!--zh-->
元数经 von Neumann 自然数跨过语义边界。元语言自然数 `k` 由集合论数码 `# k` 表示，而 `ω` 恰好包含这些数码。因此，名字的元数条款可以双向读取；名字比较的中间键也可在内部直接写成一个数码属于另一个数码，无须再添一个关系参数。
<!--ja-->
アリティは von Neumann 自然数を通して意味論の境界を越える。メタ言語の自然数 `k` は集合論的な数項 `# k` で表され、`ω` はちょうどそれらの数項を含む。したがって、名前のアリティ条件は双方向に読め、名前比較の中央の鍵も、別の関係パラメータを加えず、一方の数項が他方に属することとして内部に表せる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )
```

<!--en-->
Opening the proposition-valued structure on `L` fixes the type `S` of model
elements and the set-theoretic vocabulary used by every later formula. An
element of `S` consists of an ambient set together with evidence that it is
constructible. Environments therefore store proof-carrying constructible sets,
while membership and equality in a formula inspect their underlying ambient
sets through the structure.
<!--zh-->
打开 `L` 上的命题值结构，便固定模型元素类型 `S` 以及后续每条公式采用的集合论词汇。`S` 的一个元素由外围集合及其可构造性证据组成。因此，环境存放带证明的可构造集合，而公式中的成员关系与等词则经该结构考察其底层外围集合。
<!--ja-->
`L` 上の命題値構造を開くことで、モデル要素の型 `S` と、以後すべての論理式が使う集合論的語彙が固定される。`S` の要素は、外側の集合と、それが構成可能であることの証拠からなる。したがって環境は証明を伴う構成可能集合を保存し、論理式の所属と等号は構造を通してその基礎となる外側の集合を調べる。
<!--/-->

```agda
open hPropStructure 𝒮ʟ
```

<!--en-->
The absoluteness module relates the ambient structure on `V` to the structure
whose elements are constructible sets. The notation `γ ⊨ φ` used below is the
satisfaction relation in this constructible structure. Every entry of `γ`
therefore carries both an underlying set and its constructibility proof, while
the established adequacy and absoluteness lemmas connect formula satisfaction
with membership and equality of the underlying sets.
<!--zh-->
绝对性模块把 `V` 上的外围结构与以可构造集合为元素的结构联系起来。下文的记号 `γ ⊨ φ` 表示公式 `φ` 在这个可构造结构中于环境 `γ` 下得到满足。因此，`γ` 的每个条目同时携带底层集合及其可构造性证明，而既有的充分性与绝对性引理把公式满足关系接到这些底层集合的隶属与相等。
<!--ja-->
絶対性モジュールは、`V` 上の外側の構造と、構成可能集合を要素とする構造を結ぶ。以下の記法 `γ ⊨ φ` は、この構成可能な構造における環境 `γ` のもとでの充足関係を表す。したがって `γ` の各成分は、基礎となる集合とその構成可能性の証明をともにもち、既に得られた妥当性と絶対性の補題が、論理式の充足を基礎集合の所属および等しさに結び付ける。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## One lemma about vectors
<!--zh-->
## 关于向量的一条引理
<!--ja-->
## ベクトルに関する一つの補題
<!--/-->

<!--en-->
The remaining private indices record how outer slots survive new quantifiers.
If a formula introduces two witnesses before consulting an old slot, its de
Bruijn index must be raised twice. The map `sh2` performs exactly this shift. It
is used when the denotation argument first binds a candidate member and then an
extended environment, after which the original parameter-graph slot must still
be found.
<!--zh-->
余下的私有索引记录外层槽位如何越过新量词。若公式先引入两个见证，再读取原有槽位，其 de Bruijn 索引就必须提升两次；`sh2` 恰执行这次移位。指称论证先绑定一个候选成员，再绑定扩张环境，此后仍须找到原来的参数图槽位，正是在这里使用它。
<!--ja-->
残りの非公開添字は、外側のスロットが新しい量化子を越えてどのように残るかを記録する。論理式が二つの証人を導入してから元のスロットを参照するなら、de Bruijn 添字を二度持ち上げなければならない。`sh2` はまさにこの移動を行う。指示対象の議論で候補要素と拡張環境を順に束縛した後、元のパラメータ・グラフのスロットを参照するために使われる。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```

<!--en-->
Minimality introduces a different local context. To test whether the current
name is least, the object language universally binds a competing skeleton code,
arity numeral, and parameter graph. Every previously available slot then lies
three places farther away, and `sh3` is the uniform embedding that preserves
those references beneath the competitor's three data.
<!--zh-->
最小性引入另一种局部语境。为检验当前名字是否最小，对象语言全称绑定一条竞争者的骨架码、元数数码与参数图。此前已有的每个槽位因而向外退后三位，`sh3` 正是把那些引用完整保留在竞争者三项数据之下的统一嵌入。
<!--ja-->
最小性は別の局所文脈を導入する。現在の名前が最小かを調べるため、対象言語は競合する骨格コード、アリティの数項、パラメータ・グラフを全称量化する。それまで使えた各スロットは三つ遠くなり、`sh3` が競合相手の三つのデータの下でそれらの参照を保つ一様な埋め込みとなる。
<!--/-->

```agda
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))
```

<!--en-->
Reading a denotation through the satisfaction graph creates the deepest local
context used in that argument. In front of the original environment stand five
new values: the candidate member, its extended environment, the environment
length, the formula key, and the table value at that key. `sh5` carries an outer
slot across all five, allowing the graph clause to refer back to the original
carrier.
<!--zh-->
经满足关系图读取指称时，会形成该论证使用的最深局部语境。原环境之前依次压入五个新值：候选成员、扩张环境、环境长度、公式键，以及该键处的表取值。`sh5` 把外层槽位越过这五项，使图条款仍能回指原来的载体。
<!--ja-->
充足関係グラフを通して指示対象を読むと、この議論で最も深い局所文脈が生じる。元の環境の前には、候補要素、その拡張環境、環境の長さ、論理式の鍵、その鍵における表の値という五つの新しい値が置かれる。`sh5` は外側のスロットをこの五項すべての向こうへ運び、グラフの条件から元の台を参照できるようにする。
<!--/-->

```agda
  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 i = suc (suc (suc (suc (suc i))))
```

<!--en-->
The step formula binds two complete pieces of name data before it compares
anything. Each piece consists of a skeleton code, an arity numeral, and a
parameter graph, giving six new entries in total. `sh6` embeds every outer slot
beneath this frame, so the two least-name clauses and the final name comparison
continue to speak about the same carrier, code sets, relation slots, and objects.
<!--zh-->
步进公式在作任何比较之前，先绑定两套完整的名字数据。每套包含骨架码、元数数码与参数图，合计六个新条目。`sh6` 把每个外层槽位嵌入这层框架之下，使两条最小名字子句与最后的名字比较仍谈论同一载体、码集、关系槽位及被比较对象。
<!--ja-->
ステップの論理式は、比較を始める前に二組の完全な名前データを束縛する。各組は骨格コード、アリティの数項、パラメータ・グラフからなり、合わせて六つの新しい成分になる。`sh6` はすべての外側のスロットをこの枠の下へ埋め込み、二つの最小名条件と最後の名前比較が、同じ台、コード集合、関係スロット、比較対象について語り続けられるようにする。
<!--/-->

```agda
  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))
```

<!--en-->
The six fixed indices name the entries of that local frame. Because successive
existential witnesses are pushed onto the front of the environment, the first
name's skeleton code, arity, and parameter graph are found at indices 5, 4, and
3, while the second name's skeleton code is at index 2. Recording these
positions once keeps every later occurrence aligned with the order in which the
witnesses were introduced.
<!--zh-->
六个固定索引为这层局部框架中的条目命名。由于相继引入的存在见证都压到环境前端，第一个名字的骨架码、元数与参数图最终位于索引 5、4、3，而第二个名字的骨架码位于索引 2。一次记下这些位置，便可保证后文每次引用都与见证的引入顺序对齐。
<!--ja-->
六つの固定添字は、この局所的な枠の成分に名前を与える。存在証人は導入されるたびに環境の先頭へ積まれるので、第一の名前の骨格コード、アリティ、パラメータ・グラフは添字 5、4、3 にあり、第二の名前の骨格コードは添字 2 にある。これらの位置を一度記録しておけば、後のすべての参照を証人の導入順序と一致させられる。
<!--/-->

```agda
  s6a a6a e6a s6b a6b e6b : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  s6a = suc (suc (suc (suc (suc zero))))
  a6a = suc (suc (suc (suc zero)))
  e6a = suc (suc (suc zero))
  s6b = suc (suc zero)
```

<!--en-->
Indices 1 and 0 hold the second name's arity and parameter graph, completing the
local environment in the order `p₂, k₂, s₂, p₁, k₁, s₁` from nearest to farthest.
These six bindings are the two names' data inside `StepAt`. They are distinct
from the six outer witnesses later bound by `InternalWellOrder.Stp`, which
describe a stage tower, its definable power set, a table value, a code set, a
code order, and the empty-alphabet code set. The inner formula supplies a local
name comparison to that consumer; it does not yet assert an internal well-order.
<!--zh-->
索引 1 与 0 存放第二个名字的元数与参数图，于是局部环境从近到远呈 `p₂, k₂, s₂, p₁, k₁, s₁` 的次序。这里六个绑定是 `StepAt` 内两条名字的数据，必须与 `InternalWellOrder.Stp` 稍后绑定的六个外围见证区分。后者依次描述层塔、其可定义幂集、一个表取值、一个码集、码序与空字母表码集。内层公式只为该使用者提供局部名字比较，此处尚未断言内部良序。
<!--ja-->
添字 1 と 0 には第二の名前のアリティとパラメータ・グラフが入り、局所環境は近い方から `p₂, k₂, s₂, p₁, k₁, s₁` という順序で完成する。この六つの束縛は `StepAt` 内部の二つの名前のデータであり、後に `InternalWellOrder.Stp` が束縛する六つの外側の証人とは別である。後者は、段階の塔、その定義可能冪集合、表の値、コード集合、コード順序、空アルファベットのコード集合を表す。内側の論理式がその使用側へ与えるのは局所的な名前比較であり、この時点では内部の整列順序を主張していない。
<!--/-->

```agda
  a6b = suc zero
  e6b = zero
```

<!--en-->
The first vector lemma normalizes lookup after an entrywise map. Looking up
index `i` in `map f v` gives exactly `f` applied to the entry of `v` at `i`.
Induction on the vector proves the head case by reflexivity and reduces the tail
case to the induction hypothesis. Later, this equality lets the proof move
without ambiguity between carrier indices and their images as model elements.
<!--zh-->
第一条向量引理规范化逐项映射后的查表。从 `map f v` 的索引 `i` 处读出的，恰是把 `f` 施于 `v` 在 `i` 处的条目。对向量归纳时，首项情形由自反性成立，尾项情形化归到归纳假设。后文借此等式，可在载体索引及其作为模型元素的像之间无歧义地转换。
<!--ja-->
最初のベクトル補題は、成分ごとの写像の後に行う参照を正規化する。`map f v` の添字 `i` にある成分は、`v` の `i` 番目の成分へ `f` を適用したものにちょうど等しい。ベクトルについて帰納すると、先頭の場合は反射性で成り立ち、後尾の場合は帰納法の仮定へ帰着する。後ではこの等式により、台の添字と、それをモデル要素へ写した像とのあいだを曖昧さなく移動できる。
<!--/-->

```agda
lookup-map : {ℓ' ℓ'' : Level} {X : Type ℓ'} {Y : Type ℓ''} (f : X → Y)
             {k : ℕ} (v : Vec X k) (i : Fin k)
           → lookup i (map f v) ≡ f (lookup i v)
lookup-map f (x ∷ v) zero    = refl
lookup-map f (x ∷ v) (suc i) = lookup-map f v i
```

<!--en-->
The second vector lemma normalizes the other presentation used by recovery.
Tabulating a family `g : Fin k → X` as `FinVec→Vec g` and then looking up `i`
returns `g i`. This is not the converse of `lookup-map`; rather, the two lemmas
remove two different representation layers. One exposes an entry through
entrywise mapping, and the other exposes an entry through tabulation. Together
they connect a recovered finite family with the parameter vector stored in a
name.
<!--zh-->
第二条向量引理规范化恢复过程采用的另一种呈现。把族 `g : Fin k → X` 列表化为 `FinVec→Vec g`，再查索引 `i`，所得就是 `g i`。这并非 `lookup-map` 的反向；两条引理分别消去两种不同的表示层：一条透过逐项映射显露条目，另一条透过列表化显露条目。合用时，它们把恢复出的有穷族接到名字所存的参数向量上。
<!--ja-->
第二のベクトル補題は、復元で使うもう一つの表示を正規化する。族 `g : Fin k → X` を `FinVec→Vec g` としてベクトル化し、添字 `i` を参照すると `g i` が返る。これは `lookup-map` の逆向きではない。二つの補題は異なる二つの表示層を取り除く。一方は成分ごとの写像を通した成分を露わにし、他方は表への変換を通した成分を露わにする。両者を合わせることで、復元された有限族と、名前に保存されたパラメータ・ベクトルが結ばれる。
<!--/-->

```agda
lookup-tab : {ℓ' : Level} {X : Type ℓ'} {k : ℕ} (g : Fin k → X) (i : Fin k)
           → lookup i (FinVec→Vec g) ≡ g i
lookup-tab g i j = FinVec→Vec→FinVec g j i
```

<!--en-->
## The chapter's frame
<!--zh-->
## 本章的框架
<!--ja-->
## 本章のフレーム
<!--/-->

<!--en-->
The local module now fixes the mathematical setting for every subsequent
reading. The ambient set `A` is accompanied by `pA`, making it an element `Aʟ`
of the constructible structure, and `w` is a well-order of the small type
`⟪ A ⟫` indexing its members. Slot equalities involving the carrier use the
proof-carrying element `Aʟ` because later formulas and transports depend on the
model element, not merely on its first projection.
<!--zh-->
局部模块现在固定后续每次读式采用的数学环境。外围集合 `A` 配上 `pA` 后成为可构造结构的元素 `Aʟ`，而 `w` 是索引其成员的小类型 `⟪ A ⟫` 上的良序。涉及载体的槽位等式使用带证明的元素 `Aʟ`，因为后续公式与搬运依赖完整模型元素，并非只依赖其第一投影。
<!--ja-->
ここで局所モジュールは、以後のすべての読みに共通する数学的設定を固定する。外側の集合 `A` は `pA` と組み合わされ、構成可能構造の要素 `Aʟ` となる。`w` は、その要素を添字づける小さい型 `⟪ A ⟫` 上の整列順序である。台に関するスロットの等式では、証明を伴う要素 `Aʟ` を使う。後の論理式と輸送が依存するのはモデル要素全体であり、その第一射影だけではないからである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module At (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Aʟ : S
    Aʟ = A , pA
```

<!--en-->
Opening `Naming A w` fixes the meta-language objects against which adequacy is
measured. A name is a dependent triple: an arity `k`, a parameter-free formula
with `suc k` variable positions, and a vector of exactly `k` members of `A`.
Its code comes from the formula, and its denotation is the subset of `A` cut out
by the formula under those parameters. The name order first compares formula
codes by `limitOrder`, then arities by the natural-number order, and finally
equal-length parameter vectors lexicographically by `w`. The remainder of the
chapter proves that the slot descriptions recover precisely this comparison at
the level of propositions, while retaining truncation and the stated
minimality conditions.
<!--zh-->
打开 `Naming A w`，便固定充分性所要对照的元语言对象。一条名字是依值三元组：元数 `k`、具有 `suc k` 个变量位置的无参公式，以及恰由 `A` 的 `k` 个成员组成的向量。名字的码取自该公式，名字的指称则是该公式在这些参数下从 `A` 中界定出的子集。名字序先由 `limitOrder` 比较公式码，再按自然数序比较元数，最后在元数相等时按 `w` 对参数向量作字典序比较。本章余下部分将在命题层证明槽位描述恰好恢复这次比较，同时保留命题截断与所陈述的最小性条件。
<!--ja-->
`Naming A w` を開くことで、妥当性の基準となるメタ言語の対象が固定される。名前は依存的な三つ組であり、アリティ `k`、`suc k` 個の変数位置をもつ無パラメータ論理式、`A` の要素をちょうど `k` 個並べたベクトルからなる。コードは論理式から得られ、指示対象は、そのパラメータのもとで論理式が `A` から切り出す部分集合である。名前の順序は、まず論理式コードを `limitOrder` で比較し、次にアリティを自然数の順序で比較し、長さが等しい場合にパラメータ・ベクトルを `w` によって辞書式に比較する。本章の残りは、スロットによる記述が命題の水準でこの比較を正確に復元することを、命題的切り詰めと所定の最小性条件を保ったまま証明する。
<!--/-->

```agda
    module NM = Naming A w
```

<!--en-->
Fixing the constructible carrier and its well-order puts two complementary
interfaces side by side. `Adequacy` supplies the embedding of carrier members,
the parameter family of a name, and the comparison module `Keys`; `Naming`
supplies names together with their arity, parameter-free formula, parameter
vector, and the code, extended environment, and denotation derived from those
data. The relation `_≺ₙ_` compares such names by their three keys.

This distinction also fixes the logical strength of the chapter. `NameAt` has
four conceptual conjuncts, for the skeleton, arity, parameter graph, and
denotation. Adequacy fills them from a given name and reads them back only as
the propositionally truncated existence of a name. Minimality will be a
property of a recovered name, while the choice of a particular least name
occurs downstream. When `InternalWellOrder` uses the result, the six bindings
inside `StepAt`, two triples of name data, remain distinct from the six outer
infrastructure witnesses of `Stp`.
<!--zh-->
固定可构造载体及其良序后，两套互补的接口便并列在一起。`Adequacy` 给出载体成员的嵌入、名字的参数族及比较模块 `Keys`；`Naming` 给出名字，以及名字的元数、无参公式、参数向量，还有由这些数据导出的码、扩张环境与指称。关系 `_≺ₙ_` 按三个键比较这样的名字。

这一区分也固定了本章结论的逻辑强度。`NameAt` 恰有四个概念性合取项，分别刻画骨架、元数、参数图与指称。充分性的填充方向从给定名字证明这四项，读取方向却只得到命题截断下名字的存在性。最小性稍后是恢复所得名字的一项性质，选出某个具体最小名字则发生在下游。`InternalWellOrder` 使用本章结论时，`StepAt` 内部的六个绑定是两组三项名字资料，与 `Stp` 外围的六个基础设施见证属于不同的环境。
<!--ja-->
構成可能な台とその整列順序を固定すると、相補的な二つのインターフェースが並ぶ。`Adequacy` は台の要素の埋め込み、名前のパラメータ族、比較を扱うモジュール `Keys` を与える。`Naming` は名前、そのアリティ、無パラメータ論理式、パラメータ・ベクトル、さらにそれらから導かれるコード、拡張環境、指示対象を与える。関係 `_≺ₙ_` は三つの鍵によって名前を比較する。

この区別は本章の結論の論理的な強さも定める。`NameAt` の概念的な連言項は、骨格、アリティ、パラメータ・グラフ、指示対象の四つである。妥当性の内向きは与えられた名前からこれらを満たし、外向きは名前の存在を命題的に切り詰めた形でのみ返す。最小性は後で復元された名前の性質として現れ、特定の最小名を選ぶ操作は下流で行われる。`InternalWellOrder` がこの結果を使うときも、`StepAt` 内部の六つの束縛は二つの名前の三項組であり、`Stp` 外側の六つの基盤的な証人とは別の環境に属する。
<!--/-->

```agda
  open Adequacy A pA w using ( ix; pfam; module Keys )
  open NM using
    ( Name; arity; formula; params; codeOf; denote; environment
    ; _≺ₙ_ )
```

<!--en-->
## The parameter sequence, filled in
<!--zh-->
## 参数序列，填进去
<!--ja-->
## パラメータ列を埋める
<!--/-->

<!--en-->
A parameter vector first has to cross from meta-language data to an
object-language environment. The family `g : Fin k → ⟪ A ⟫` gives one carrier
member at each of the `k` indices. If slots `e`, `a`, and `B` hold respectively
the graph of its embedded values, the numeral `# k`, and the carrier `A`, then
`envOverAt e a B` is satisfied. Its four conditions say that the graph is
single-valued, has exactly that finite domain, takes values in the carrier, and
contains only ordered pairs.
<!--zh-->
参数向量首先要从元语言数据跨入对象语言环境。族 `g : Fin k → ⟪ A ⟫` 在 `k` 个序号中的每一处给出一个载体成员。若位置 `e`、`a`、`B` 依次持有这些成员嵌入后的图、数码 `# k` 与载体 `A`，则 `envOverAt e a B` 得到满足。它的四项条件分别说明该图单值、定义域恰为这个有穷数码、取值落在载体中，并且只含有序对。
<!--ja-->
パラメータ・ベクトルは、まずメタ言語のデータから対象言語の環境へ移される。族 `g : Fin k → ⟪ A ⟫` は、`k` 個の各添字に台の要素を一つ与える。スロット `e`、`a`、`B` がそれぞれ、その要素を埋め込んだ値のグラフ、数項 `# k`、台 `A` を保持するなら、`envOverAt e a B` が充足される。その四条件は、グラフが一価であり、定義域がちょうどその有限な数項であり、値が台に属し、順序対以外の要素を含まないことを述べる。
<!--/-->

```agda
  paramSeq-in : ∀ {n} (e a B : Fin n) (γ : S ^ n) (k : ℕ) (g : Fin k → ⟪ A ⟫)
              → fst (lookup e γ) ≡ env (λ i → ix (g i))
              → fst (lookup a γ) ≡ # k
              → fst (lookup B γ) ≡ A
              → ⟨ γ ⊨ envOverAt e a B ⟩
```

<!--en-->
These four graph properties need not be proved again after the three sets have
been placed in arbitrary slots. The canonical environment with entries
`Aʟ`, `# k`, and `envS Aʟ g` already satisfies them at indices two, one, and
zero. `envOverAt-transport` carries that satisfaction to `γ` along the three
given equalities. The equalities are reversed because the transport starts at
the canonical sets and ends at the sets stored in the requested slots.
<!--zh-->
把这三个集合放入任意位置后，无须重新证明那四项图性质。由 `Aʟ`、`# k` 与 `envS Aʟ g` 组成的典范环境，已经在序号二、一、零处满足这些性质。`envOverAt-transport` 沿三条给定等式把这份满足关系搬到 `γ`。等式在调用中取反，是因为搬运从典范集合出发，抵达指定位置中存放的集合。
<!--ja-->
三つの集合を任意のスロットへ置いた後で、四つのグラフ条件を証明し直す必要はない。`Aʟ`、`# k`、`envS Aʟ g` を並べた標準的な環境は、添字二、一、零ですでにそれらを充足している。`envOverAt-transport` は、与えられた三つの等しさに沿って、その充足関係を `γ` へ運ぶ。呼び出しで等しさの向きが反転しているのは、標準的な集合から出発して、指定されたスロットに保存された集合へ移るためである。
<!--/-->

```agda
  paramSeq-in e a B γ k g qe qa qB =
    envOverAt-transport (Aʟ ∷ (# k , numL k) ∷ envS Aʟ g ∷ []) γ
      (suc (suc zero)) (suc zero) zero e a B
      (sym qe) (sym qa) (sym qB) (envOver Aʟ g)
```

<!--en-->
## And read back as a vector
<!--zh-->
## 又被读回成一个向量
<!--ja-->
## ベクトルとして読み戻す
<!--/-->

<!--en-->
For the reverse reading, the arity and carrier slots are fixed by `qa` and
`qB`, while `h` asserts that the set in slot `e` satisfies the environment
conditions. No graph presentation is assumed for `e`; finding one is precisely
the task. Opening `Recover` with these data exposes a family indexed by
`Fin k` and a proof that its canonical graph is the original set.
<!--zh-->
在反向读取中，等式 `qa` 与 `qB` 固定元数位和载体位，而 `h` 断言位置 `e` 中的集合满足环境条件。这里并未预先假定 `e` 的某种图表示；找出这样的表示正是任务所在。以这些数据打开 `Recover` 后，便得到一个由 `Fin k` 索引的族，以及其典范图就是原集合的证明。
<!--ja-->
逆向きの読みでは、`qa` と `qB` がアリティのスロットと台のスロットを固定し、`h` はスロット `e` の集合が環境条件を充足すると述べる。`e` のグラフ表示はあらかじめ仮定されていない。それを見つけることこそ、ここでの課題である。これらのデータで `Recover` を開くと、`Fin k` で添字づけられた族と、その標準的なグラフがもとの集合に等しいという証明が得られる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module _ {n : ℕ} (e a B : Fin n) (γ : S ^ n) (k : ℕ)
           (qa : fst (lookup a γ) ≡ # k) (qB : fst (lookup B γ) ≡ A)
           (h : ⟨ γ ⊨ envOverAt e a B ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
    private module R = Recover Aʟ k γ e a B qa qB h
```

<!--en-->
The recovered family is genuine data, so it can be tabulated as a vector of
length `k`. This does not remove a truncation by choice. At each index, the
domain condition merely supplies an entry, but single-valuedness makes the type
of entries a proposition; elimination of propositional truncation into that
proposition therefore yields the unique entry. Its value lies in `A`, and the
carrier's membership fibre supplies the corresponding element of `⟪ A ⟫`
without truncation. Applying `FinVec→Vec` to these elements produces
`paramSeq-out`.
<!--zh-->
恢复出的族是真正的数据，因而可以列表化为长度为 `k` 的向量。这里并未借助选择来解除截断。对每个序号，定义域条件只给出某个条目的仅仅存在，但单值性使条目类型成为命题；因此，可以把命题截断消去到这个命题中，取得唯一条目。该条目的值属于 `A`，而载体的成员纤维无截断地给出 `⟪ A ⟫` 中相应的元素。对这些元素应用 `FinVec→Vec`，便得到 `paramSeq-out`。这里使用的是命题截断，不是命题换级。
<!--ja-->
復元された族は実際のデータなので、長さ `k` のベクトルに表としてまとめられる。ここで選択によって切り詰めを外しているわけではない。各添字について、定義域条件は成分の単なる存在しか与えないが、一価性により成分の型は命題になる。したがって、命題的切り詰めをその命題へ除去して、一意な成分を得られる。その値は `A` に属し、台の所属ファイバーが対応する `⟪ A ⟫` の要素を切り詰めなしで与える。これらの要素に `FinVec→Vec` を適用したものが `paramSeq-out` である。
<!--/-->

```agda
    paramSeq-out : Vec ⟪ A ⟫ k
    paramSeq-out = FinVec→Vec R.g
```

<!--en-->
Tabulation changes the presentation of the family, so the graph equation closes
the round trip. `R.recovers` identifies the set in slot `e` with the graph of
the recovered finite family. The lookup law for `FinVec→Vec` then identifies
each entry of the tabulated vector with the corresponding family value;
function extensionality and congruence of `env` lift those pointwise paths to
an equality of graphs. Thus the recovered vector presents exactly the original
environment set, including the absence of extraneous members guaranteed by the
ordered-pair condition.
<!--zh-->
列表化改变了族的呈现方式，因而还要用图等式闭合这次往返。`R.recovers` 把位置 `e` 中的集合认作恢复所得有穷族的图。`FinVec→Vec` 的查取律再把列表化向量的每个条目认作相应的族值；函数外延性与 `env` 的同余把这些逐点路径提升为图的相等。因此，恢复所得向量精确呈现原环境集合，其中也没有「只由有序对构成」条件所排除的多余成员。
<!--ja-->
表への変換は族の表示を変えるため、グラフの等しさによって往復を閉じる。`R.recovers` は、スロット `e` の集合を復元された有限族のグラフと同一視する。続いて `FinVec→Vec` の参照則が、表にしたベクトルの各成分を対応する族の値と同一視する。関数外延性と `env` の合同性により、これらの点ごとのパスはグラフの等しさへ持ち上がる。したがって、復元されたベクトルはもとの環境集合を正確に表示し、順序対条件が排除する余分な要素も含まない。
<!--/-->

```agda
    paramSeq-graph : fst (lookup e γ)
                   ≡ env (λ i → ix (lookup i paramSeq-out))
    paramSeq-graph = R.recovers
                   ∙ cong env (funExt (λ i → cong ix (sym (lookup-tab R.g i))))
```
</div>
</details>

<!--en-->
## Four elements, sealed where they are made
<!--zh-->
## 四个元素，在造出之处封印
<!--ja-->
## 四つの要素を構成箇所で不透明化する
<!--/-->

<!--en-->
The denotation clause has four existential witnesses of its own, distinct from
the four conceptual conjuncts of `NameAt`. The first witness is the environment
obtained from a name `t` and a candidate carrier member `m`: place `m` before
the parameter vector of `t`, then represent that extended assignment as an
element of the model. The construction `envFor Aʟ` includes the required proof
of constructibility, so `envAt t m` can occupy an object-language slot.
<!--zh-->
指称条款自身含有四个存在见证，它们不同于 `NameAt` 的四个概念性合取项。第一个见证由名字 `t` 与候选载体成员 `m` 构成：把 `m` 放到 `t` 的参数向量之前，再把这个扩张赋值表示成模型元素。构造 `envFor Aʟ` 同时携带所需的可构造性证明，因此 `envAt t m` 可以占据一个对象语言位置。
<!--ja-->
指示対象の条件には、それ自身の四つの存在証人がある。これは `NameAt` の四つの概念的な連言項とは別である。第一の証人は、名前 `t` と候補となる台の要素 `m` から得られる環境である。`m` を `t` のパラメータ・ベクトルの先頭に置き、その拡張された割り当てをモデルの要素として表す。構成 `envFor Aʟ` は必要な構成可能性の証明も含むので、`envAt t m` は対象言語のスロットを占めることができる。
<!--/-->

```agda
  opaque
    envAt : Name → ⟪ A ⟫ → S
    envAt t m = envFor Aʟ (environment t m)
```

<!--en-->
The object-language formulas inspect the underlying set of that model element.
The equation `envAt-fst` identifies it with
`envGraph Aʟ (environment t m)`, the canonical graph of the candidate followed
by the parameters. This is the exact presentation needed both by the formula
that adjoins the candidate to the old parameter environment and by the formula
that checks the domain of the extended environment.
<!--zh-->
对象语言公式考察的是该模型元素的底层集合。等式 `envAt-fst` 把它认作 `envGraph Aʟ (environment t m)`，即候选元素置于诸参数之前所得的典范图。这一呈现恰好同时服务于两条公式：一条把候选元素添到原参数环境中，另一条检查扩张环境的定义域。
<!--ja-->
対象言語の論理式が調べるのは、このモデル要素の基礎集合である。等式 `envAt-fst` はそれを `envGraph Aʟ (environment t m)`、すなわち候補をパラメータの前に置いた標準的なグラフと同一視する。この表示は、候補をもとのパラメータ環境へ加える論理式と、拡張環境の定義域を調べる論理式の両方に必要な形である。
<!--/-->

```agda
    envAt-fst : (t : Name) (m : ⟪ A ⟫)
              → fst (envAt t m) ≡ envGraph Aʟ (environment t m)
    envAt-fst t m = envFor-graph Aʟ (environment t m)
```

<!--en-->
The second witness represents a natural number inside the constructible model.
`numAt j` pairs the von Neumann numeral `# j` with its constructibility proof
`numL j`. In the denotation argument it will be used at
`j = suc (arity t)`, because the extended environment contains the candidate
in addition to the `arity t` parameters.
<!--zh-->
第二个见证在可构造模型内部表示一个自然数。`numAt j` 把 von Neumann 数码 `# j` 与其可构造性证明 `numL j` 配成模型元素。在指称论证中，将取 `j = suc (arity t)`，因为扩张环境除 `arity t` 个参数外还含有候选元素。
<!--ja-->
第二の証人は、自然数を構成可能モデルの内部で表す。`numAt j` は von Neumann 数項 `# j` と、その構成可能性の証明 `numL j` を組にしてモデル要素を作る。指示対象の議論では `j = suc (arity t)` として使われる。拡張環境には `arity t` 個のパラメータに加えて候補が一つ入るからである。
<!--/-->

```agda
    numAt : ℕ → S
    numAt j = # j , numL j
```

<!--en-->
Projecting the underlying set of `numAt j` returns `# j` definitionally, so
`numAt-fst` is reflexivity. This simple equation is what connects the
meta-language length of the extended vector with the set-theoretic numeral
seen by `domAt`; no decoding of a numeral is needed in this filling direction.
<!--zh-->
投影 `numAt j` 的底层集合按定义便得到 `# j`，所以 `numAt-fst` 由自反性证明。这条简单等式把扩张向量的元语言长度与 `domAt` 所见的集合论数码连接起来；在这个填充方向无须解码数码。
<!--ja-->
`numAt j` の基礎集合を射影すると定義によって `# j` が得られるので、`numAt-fst` は反射性で証明される。この単純な等式が、拡張ベクトルのメタ言語での長さと `domAt` が見る集合論的な数項を結ぶ。この内向きでは数項を復号する必要はない。
<!--/-->

```agda
    numAt-fst : (j : ℕ) → fst (numAt j) ≡ # j
    numAt-fst j = refl
```

<!--en-->
The third witness is the key at which uniform satisfaction stores the formula
of the name. Since `formula t` has no constants, `embed (formula t)` regards it
as a formula whose constant alphabet is the member type of `A`; no constant is
actually introduced. `keyIn Aʟ` packages the resulting formula key as a
constructible model element, giving `keyAt t`.
<!--zh-->
第三个见证是统一满足关系存放名字公式的键。由于 `formula t` 没有常元，`embed (formula t)` 只是把它看成常元字母表为 `A` 的成员类型的公式，并未实际引入任何常元。`keyIn Aʟ` 把所得公式键包装成可构造模型元素，得到 `keyAt t`。
<!--ja-->
第三の証人は、統一充足関係が名前の論理式を保存する鍵である。`formula t` は定数をもたないので、`embed (formula t)` はそれを `A` の要素型を定数アルファベットとする論理式として見直すだけで、実際に定数を導入しない。`keyIn Aʟ` は得られた論理式の鍵を構成可能なモデル要素として包み、`keyAt t` を与える。
<!--/-->

```agda
    keyAt : Name → S
    keyAt t = keyIn Aʟ (embed (formula t))
```

<!--en-->
The packaged key and the key used by the code-set interface have the same
underlying set. The equation `keyAt-fst` states precisely that
`fst (keyAt t)` is `fst (keyS Aʟ (embed (formula t)))`. This lets later
membership and graph arguments use the abstract model element while reasoning
about the concrete ordered-pair code supplied by `keyS`.
<!--zh-->
包装后的键与码集接口所用的键具有同一底层集合。等式 `keyAt-fst` 精确断言 `fst (keyAt t)` 等于 `fst (keyS Aʟ (embed (formula t)))`。因此，后续隶属与图的论证可以把抽象模型元素放入位置，同时用 `keyS` 给出的具体有序对码进行推理。
<!--ja-->
包まれた鍵とコード集合のインターフェースが使う鍵は、同じ基礎集合をもつ。等式 `keyAt-fst` は、`fst (keyAt t)` が `fst (keyS Aʟ (embed (formula t)))` に等しいことを正確に述べる。これにより、後の所属とグラフの議論では抽象的なモデル要素をスロットに置きながら、`keyS` が与える具体的な順序対コードについて推論できる。
<!--/-->

```agda
    keyAt-fst : (t : Name)
              → fst (keyAt t) ≡ fst (keyS Aʟ (embed (formula t)))
    keyAt-fst t = keyIn≡ Aʟ (embed (formula t))
```

<!--en-->
The same key is certified to belong to `AllCodes Aʟ`. This membership is a
semantic condition, not redundant bookkeeping: the satisfaction graph is
required to have the intended value at genuine formula keys, whereas its
behaviour away from the code domain is irrelevant. Thus `keyAt-∈` is what
allows the table value at `keyAt t` to be read as satisfaction of the formula
of `t`.
<!--zh-->
同一个键还被证明属于 `AllCodes Aʟ`。这项隶属是语义条件，并非多余的簿记：满足关系图只在真实公式键处必须具有预期取值，而它在码域之外如何取值并不重要。因此，正是 `keyAt-∈` 使表在 `keyAt t` 处的取值可以被读成名字 `t` 的公式之满足关系。
<!--ja-->
同じ鍵が `AllCodes Aʟ` に属することも証明される。この所属は意味論的な条件であり、余分な帳尻合わせではない。充足関係のグラフが意図した値をもつことを要求されるのは真正な論理式の鍵においてであり、コード領域の外での振る舞いは問題にされないからである。したがって、表の `keyAt t` における値を `t` の論理式の充足関係として読めるのは `keyAt-∈` による。
<!--/-->

```agda
    keyAt-∈ : (t : Name) → ⟨ keyAt t ∈ˢ AllCodes Aʟ ⟩
    keyAt-∈ t = keyIn∈ Aʟ (embed (formula t))
```

<!--en-->
The fourth witness is the value selected by the uniform satisfaction table at
that genuine key. `Table.val Aʟ Aʟ` takes both the key and its membership in the
code domain, and returns a constructible model element. Its underlying set will
later be identified by `val-sat` with exactly the encoded environments over
`A` that satisfy `embed (formula t)`; here `valAt` records the table lookup
needed for that identification.
<!--zh-->
第四个见证是统一满足关系表在这个真实键处选定的取值。`Table.val Aʟ Aʟ` 同时接受该键及其属于码域的证明，并返回一个可构造模型元素。稍后，`val-sat` 将把它的底层集合认作所有满足 `embed (formula t)` 的 `A` 上编码环境之集；此处的 `valAt` 记录这次认同所需的表查询。
<!--ja-->
第四の証人は、統一充足関係の表がその真正な鍵で与える値である。`Table.val Aʟ Aʟ` は鍵と、それがコード領域に属する証明を受け取り、構成可能なモデル要素を返す。後で `val-sat` により、その基礎集合は `embed (formula t)` を充足する `A` 上の符号化環境全体と同一視される。ここで `valAt` は、その同一視に必要な表の参照を記録する。
<!--/-->

```agda
    valAt : Name → S
    valAt t = Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t)
```

<!--en-->
Because `valAt t` is defined by that table lookup, `valAt-val` is reflexivity.
Keeping the equation explicit lets the denotation argument pass cleanly
between the named fourth witness and the general theorem about `Table.val`.
Together, the four constructions now provide exactly the witnesses bound by
`DenoteOf`: an extended environment, its length numeral, a genuine formula key,
and the table value at that key.
<!--zh-->
由于 `valAt t` 就由这次表查询定义，`valAt-val` 以自反性成立。把这条等式显式列出，使指称论证可以在第四个具名见证与关于 `Table.val` 的一般定理之间直接转换。至此，四个构造恰好给出 `DenoteOf` 所绑定的见证：扩张环境、其长度数码、一个真实公式键，以及表在该键处的取值。
<!--ja-->
`valAt t` はこの表の参照そのものとして定義されているので、`valAt-val` は反射性で成り立つ。この等式を明示することで、指示対象の議論は、第四の名前つき証人と `Table.val` に関する一般定理のあいだを直接移れる。これで四つの構成は、`DenoteOf` が束縛する証人をちょうど与える。すなわち、拡張環境、その長さの数項、真正な論理式の鍵、その鍵における表の値である。
<!--/-->

```agda
    valAt-val : (t : Name) → valAt t ≡ Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t)
    valAt-val t = refl
```

<!--en-->
## What the key of a name's formula is
<!--zh-->
## 一个名字的公式之键是什么
<!--ja-->
## 名前の論理式の鍵
<!--/-->

<!--en-->
To compare the description's key with the table's key, first observe what
relabeling does to a parameter-free formula. The formula `χ` has constants in
the empty type. Embedding it directly into the ambient universe and first
embedding it into the carrier and then mapping carrier members into the
universe therefore use two functions with the same empty domain. Function
extensionality makes those functions equal, and the composition law for
`mapFo` yields `sameEmbed χ`. This is a fact about the empty constant alphabet,
not a claim that arbitrary relabeling leaves arbitrary formulas unchanged.
<!--zh-->
为了比较描述所造的键与表所用的键，先考察常元改名对无参公式的作用。公式 `χ` 的常元取自空类型。把它直接嵌入外围宇宙，与先嵌入载体、再把载体成员映入宇宙，所用的都是以空类型为定义域的函数。函数外延性使这两个函数相等，`mapFo` 的复合律随即给出 `sameEmbed χ`。这是关于空常元字母表的事实，并不是说任意公式经任意常元改名后都不变。
<!--ja-->
記述が作る鍵と表が使う鍵を比較するため、まず無パラメータ論理式に対する定数の付け替えを調べる。論理式 `χ` の定数は空型から取られる。これを周囲の宇宙へ直接埋め込む場合と、いったん台へ埋め込んでから台の要素を宇宙へ写す場合に使う関数は、どちらも空型を定義域とする。関数外延性により両者は等しくなり、`mapFo` の合成則から `sameEmbed χ` が得られる。これは空の定数アルファベットについての事実であり、任意の論理式が任意の定数の付け替えで不変だという主張ではない。
<!--/-->

```agda
  private
    sameEmbed : ∀ {m} (χ : Formula (⊥* {ℓ}) m)
              → mapFo ⟪ A ⟫↪ (embed χ) ≡ embed χ
    sameEmbed χ = mapFo-comp ⊥*-rec ⟪ A ⟫↪ χ
                ∙ cong (λ f → mapFo f χ) (funExt (λ b → ⊥*-rec b))
```

<!--en-->
The table key of a formula with `m` variable positions is an ordered pair: the
numeral `# m` and the code of the formula after its constants have been mapped
into the ambient universe. By `sameEmbed`, that mapped formula is the direct
embedding of `χ`, whose code is the underlying set of `limitCode χ`.
Congruence of the coding operation therefore gives `keyCode`. For a name, where
`m = suc (arity t)`, this is exactly the equality that will align the table key
with the pair formed from the extended-environment length and the skeleton
code.
<!--zh-->
一条具有 `m` 个变元位置的公式，其表键是一个有序对：数码 `# m` 与常元映入外围宇宙后所得公式的码。由 `sameEmbed`，这条改名后的公式就是 `χ` 的直接嵌入，而其码正是 `limitCode χ` 的底层集合。对编码操作使用同余，便得到 `keyCode`。对名字而言，`m = suc (arity t)`；因此，这条等式恰好把表键与「扩张环境的长度、骨架码」组成的对对齐。
<!--ja-->
`m` 個の変数位置をもつ論理式の表の鍵は、数項 `# m` と、定数を周囲の宇宙へ写した後の論理式コードとの順序対である。`sameEmbed` により、その付け替えられた論理式は `χ` の直接の埋め込みであり、そのコードは `limitCode χ` の基礎集合である。そこで符号化操作の合同性を使うと `keyCode` が得られる。名前については `m = suc (arity t)` なので、この等式は表の鍵を、拡張環境の長さと骨格コードからなる対にちょうど合わせる。
<!--/-->

```agda
    keyCode : ∀ {m} (χ : Formula (⊥* {ℓ}) m)
            → fst (keyS Aʟ (embed χ)) ≡ pr (# m) (fst (limitCode χ))
    keyCode χ = cong (λ u → pr (# _) VCode.⌜ u ⌝) (sameEmbed χ)
```

<!--en-->
The denotation proof also needs the parameter environment in two equivalent
presentations. The family `pfam t` sends each finite index to the ambient set
underlying the corresponding parameter. Alternatively, mapping the naming
embedding `NM.DA.ι` over `params t` gives a vector of model elements, whose
canonical graph is `envGraph Aʟ`. The lookup law for vector mapping identifies
their values pointwise; function extensionality and congruence of `env` then
give `valuesOf t`, an equality of the two environment graphs.
<!--zh-->
指称证明还需要参数环境的两种等价呈现。族 `pfam t` 把每个有穷序号送到相应参数的底层外围集合。另一种呈现先把命名模块的嵌入 `NM.DA.ι` 逐项作用于 `params t`，得到模型元素向量，再取其典范图 `envGraph Aʟ`。向量映射的查取律逐点认同两边的取值；函数外延性与 `env` 的同余随即给出 `valuesOf t`，即两张环境图的相等。
<!--ja-->
指示対象の証明には、パラメータ環境の二つの同値な表示も必要である。族 `pfam t` は各有限添字を、対応するパラメータの基礎となる周囲の集合へ送る。もう一つの表示では、命名モジュールの埋め込み `NM.DA.ι` を `params t` に成分ごとに施してモデル要素のベクトルを作り、その標準的なグラフ `envGraph Aʟ` を取る。ベクトルの写像に関する参照則が両者の値を点ごとに同一視し、関数外延性と `env` の合同性から、二つの環境グラフの等しさ `valuesOf t` が得られる。
<!--/-->

```agda
    valuesOf : (t : Name)
             → env (pfam t) ≡ envGraph Aʟ (map NM.DA.ι (params t))
    valuesOf t = cong env (funExt (λ i →
      sym (cong fst (lookup-map NM.DA.ι (params t) i))))
```

<!--en-->
Every entry of the extended environment is constructible. An index
`i : Fin (suc (arity t))` selects either the candidate or one of the parameters,
and in either case `lookup i (environment t m)` already carries proof that its
underlying set belongs to `A`. Since `A` is constructible, transitivity of
constructibility yields `valuesL t m i`. This pointwise fact supplies the
constructibility premise needed when `domAt` verifies the domain of the
extended environment.
<!--zh-->
扩张环境的每个条目都可构造。序号 `i : Fin (suc (arity t))` 选中候选元素或某个参数；无论哪种情形，`lookup i (environment t m)` 都已携带其底层集合属于 `A` 的证明。由于 `A` 可构造，可构造性的传递性给出 `valuesL t m i`。`domAt` 检查扩张环境的定义域时，所需的逐点可构造性前提正由这项事实提供。
<!--ja-->
拡張環境の各成分は構成可能である。添字 `i : Fin (suc (arity t))` は候補またはパラメータの一つを選ぶ。どちらの場合も、`lookup i (environment t m)` は、その基礎集合が `A` に属するという証明をすでに伴っている。`A` が構成可能なので、構成可能性の推移性から `valuesL t m i` が得られる。この点ごとの事実が、`domAt` が拡張環境の定義域を確かめる際に必要な構成可能性の前提を与える。
<!--/-->

```agda
    valuesL : (t : Name) (m : ⟪ A ⟫) (i : Fin (suc (arity t)))
            → ⟨ isL (values Aʟ (environment t m) i) ⟩
    valuesL t m i =
      isL-trans (snd (lookup i (environment t m))) pA
```

<!--en-->
## The denotation, both ways
<!--zh-->
## 指称，两个方向
<!--ja-->
## 表示を双方向に読む
<!--/-->

<!--en-->
Before comparing denotation membership with the object-language clause, one
must know that every member of `denote t` lies in the carrier. Membership in
this denotation merely presents a carrier index `mm` whose extended environment
satisfies the formula, together with a path from the represented carrier member
to the ambient set `y`. The witness is propositionally truncated, but the goal
`y ∈ A` is itself a proposition, so `rec₁` may use that witness without
selecting or retaining an index.
<!--zh-->
在把指称隶属与对象语言条款相比较之前，先要知道 `denote t` 的每个成员都属于载体。属于这个指称，仅仅给出一个载体序号 `mm`，其扩张环境满足公式，并给出所表示的载体成员到外围集合 `y` 的一条路径。这个见证位于命题截断之下，但目标 `y ∈ A` 本身是命题，所以 `rec₁` 可以使用该见证，而不选出或保留某个序号。这里同样没有命题换级。
<!--ja-->
指示対象への所属を対象言語の条件と比較する前に、`denote t` のすべての要素が台に属することを確かめる。この指示対象への所属は、その拡張環境が論理式を充足する台の添字 `mm` と、表された台の要素から周囲の集合 `y` へのパスが単に存在することを与える。この証人は命題的に切り詰められているが、目標 `y ∈ A` 自体が命題なので、`rec₁` は添字を選択して保持することなく、その証人を利用できる。
<!--/-->

```agda
  private
    denoteMem : (t : Name) (y : V ℓ) → ⟨ y ∈ denote t ⟩ → ⟨ y ∈ A ⟩
    denoteMem t y = rec₁ (snd (y ∈ A)) step
      where
      step : Σ[ p ∶ Σ[ mm ∶ ⟪ A ⟫ ] ⟨ NM.satAt t mm ⟩ ] (⟪ A ⟫↪ (p .fst) ≡ y)
```

<!--en-->
Inside the permitted truncation elimination, the recovered package is a pair
`p` and an equality `q`. Its first component is a concrete member index of
`A`, so the canonical small-membership witness, converted by `∈∈ₛ`, proves that
its embedded image belongs to `A`. Transporting this membership along `q`
proves `y ∈ A`. The argument uses only the presentation of membership and the
fact that its target is a proposition; it introduces neither a choice function
nor a new classical step.
<!--zh-->
在获准的截断消去内部，恢复所得资料是一对 `p` 与一条等式 `q`。`p` 的第一分量是 `A` 的一个具体成员序号，因而典范的小隶属见证经 `∈∈ₛ` 转换后，证明其嵌入像属于 `A`。沿 `q` 搬运这项隶属，即得 `y ∈ A`。论证只使用成员关系的呈现，以及目标为命题这一事实；它既不引入选择函数，也不增加新的经典步骤。
<!--ja-->
許された切り詰めの除去の内部では、復元されたデータは対 `p` と等式 `q` である。`p` の第一成分は `A` の具体的な要素添字なので、標準的な小さい所属の証人を `∈∈ₛ` で変換すれば、その埋め込み像が `A` に属することが分かる。この所属を `q` に沿って輸送すると `y ∈ A` が得られる。ここで使うのは所属の表示と、行き先が命題であるという事実だけである。選択関数も新たな古典的推論も導入しない。
<!--/-->

```agda
           → ⟨ y ∈ A ⟩
      step (p , q) = subst (λ u → ⟨ u ∈ A ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ (p .fst)} {b = A} .snd (∈ₛ⟪ A ⟫↪ (p .fst)))
```

<!--en-->
The module `Named` now fixes the slots in which the four pieces of `NameAt`
will be compared with a meta-language name: carrier `B`, the carrier code set
`C`, the empty-alphabet code set `C₀`, skeleton `s`, arity `a`, parameter graph
`e`, and denotation `d`. The carrier equation `qB` is an equality of complete
model elements, including their constructibility proofs, whereas `qC` and `q₀`
identify only underlying sets. The difference is forced by use: formulas below
are typed over the member type of the model element in slot `B`, while code-set
membership observes only the underlying sets in `C` and `C₀`.
<!--zh-->
模块 `Named` 现在固定若干位置，以便把 `NameAt` 的四项资料与一个元语言名字比较：载体 `B`、载体码集 `C`、空字母表码集 `C₀`、骨架 `s`、元数 `a`、参数图 `e` 及指称 `d`。载体等式 `qB` 是完整模型元素的相等，连同其可构造性证明；`qC` 与 `q₀` 则只认同底层集合。这一区别由后续用途决定：下面的公式以位置 `B` 中模型元素的成员类型为类型，而 `C` 与 `C₀` 中的码集隶属只考察底层集合。
<!--ja-->
モジュール `Named` はここで、`NameAt` の四つのデータをメタ言語の名前と比較するためのスロットを固定する。台 `B`、台のコード集合 `C`、空のアルファベットに対するコード集合 `C₀`、骨格 `s`、アリティ `a`、パラメータ・グラフ `e`、指示対象 `d` である。台についての等式 `qB` は構成可能性の証明を含むモデル要素全体の等しさであるが、`qC` と `q₀` は基礎集合だけを同一視する。この違いは用途から生じる。以下の論理式はスロット `B` にあるモデル要素の要素型の上で型づけられるが、`C` と `C₀` へのコード集合の所属が見るのは基礎集合だけである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Named {n : ℕ} (B C C₀ s a e d : Fin n) (γ : S ^ n)
               (qB : lookup B γ ≡ Aʟ)
               (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
               (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
```
</summary>
<div class="submodule-fold-content">

```agda
    private
```

<!--en-->
This dependence on the carrier is isolated in `Fo`. For a model element `X`
and an arity `j`, `Fo X j` is the type of formulas whose constants range over
the small member type `⟪ fst X ⟫`. Thus a formula read over the carrier stored
in a slot has the correct type before any semantic comparison is made; the
carrier cannot be replaced merely by an equality of underlying sets after the
fact.
<!--zh-->
缩写 `Fo` 把公式对载体的这项依赖单独列出。对模型元素 `X` 与元数 `j`，`Fo X j` 是常元取自小成员类型 `⟪ fst X ⟫` 的公式类型。因此，在位置所存载体上读取的公式，从语义比较开始之前就具有正确类型；事后只凭底层集合的相等，不能替换这一依值载体。
<!--ja-->
`Fo` は、論理式の台へのこの依存を切り出す。モデル要素 `X` とアリティ `j` に対して、`Fo X j` は、小さい要素型 `⟪ fst X ⟫` から定数を取る論理式の型である。したがって、スロットに保存された台の上で読む論理式は、意味論的な比較を始める前から正しい型をもつ。後になって基礎集合の等しさだけで、この依存する台を置き換えることはできない。
<!--/-->

```agda
      Fo : S → ℕ → Type ℓ
      Fo X j = Formula ⟪ fst X ⟫ j
```

<!--en-->
For a name `t`, the parameter-free `formula t` is first embedded into formulas
whose constants may range over members of the fixed carrier `A`; because the
original constant domain is empty, this adds no actual parameter. Its type is
then transported along `sym qB` from `Fo Aʟ` to
`Fo (lookup B γ)`, producing `ψAt t`. The transport is possible because `qB`
identifies the complete carrier elements. This slot-relative formula is the one
whose key and satisfaction value can now be compared with the fixed-carrier
constructions above.
<!--zh-->
对名字 `t`，先把无参公式 `formula t` 嵌入常元可取自固定载体 `A` 之成员的公式；原常元域为空，所以这一步没有增加实际参数。随后沿 `sym qB` 把它的类型从 `Fo Aʟ` 搬到 `Fo (lookup B γ)`，得到 `ψAt t`。这次搬运之所以成立，是因为 `qB` 认同完整的载体元素。至此，这条相对于位置的公式，其键与满足关系取值便可同上文固定载体上的构造比较。
<!--ja-->
名前 `t` に対して、まず無パラメータ論理式 `formula t` を、固定した台 `A` の要素を定数として許す論理式へ埋め込む。もとの定数域は空なので、実際のパラメータは追加されない。次に、その型を `sym qB` に沿って `Fo Aʟ` から `Fo (lookup B γ)` へ輸送し、`ψAt t` を得る。この輸送が可能なのは、`qB` が台のモデル要素全体を同一視するからである。こうして得られたスロット相対的な論理式について、その鍵と充足関係の値を、上で作った固定台上の構成と比較できるようになる。
<!--/-->

```agda
      ψAt : (t : Name) → Fo (lookup B γ) (suc (arity t))
      ψAt t = subst (λ X → Fo X (suc (arity t))) (sym qB) (embed (formula t))
```

<!--en-->
The formula used by the description is first transported from the fixed
carrier `Aʟ` to the carrier stored in slot `B`. Since the formula type itself
depends on the carrier, `qB` must identify the complete proof-carrying carrier,
not only its underlying set. Path induction on `qB` then shows that forming the
code-set key commutes with this transport. Thus the key computed from `ψAt t`
at the slot carrier is the same set as the key of `embed (formula t)` at `Aʟ`.
<!--zh-->
描述所用的公式先从固定载体 `Aʟ` 搬运到位置 `B` 所存的载体。公式的类型本身依赖载体，所以 `qB` 必须认同完整的带证明载体，而不只认同其底层集合。对 `qB` 作路径归纳即可证明：形成码集之键与这次搬运相交换。因此，在位置载体处由 `ψAt t` 算出的键，与在 `Aʟ` 处由 `embed (formula t)` 算出的键，是同一个集合。
<!--ja-->
記述で使う論理式は、まず固定された台 `Aʟ` からスロット `B` に格納された台へ輸送される。論理式の型そのものが台に依存するため、`qB` は基礎集合だけでなく、証明を伴う台全体を同一視しなければならない。`qB` に関するパス帰納法により、符号集合の鍵を作る操作がこの輸送と可換であることが分かる。したがって、スロットの台で `ψAt t` から得る鍵と、`Aʟ` で `embed (formula t)` から得る鍵は同じ集合である。
<!--/-->

```agda
      keyψ : (t : Name)
           → fst (keyS (lookup B γ) (ψAt t))
           ≡ fst (keyS Aʟ (embed (formula t)))
      keyψ t = sym (constSubstCommSlice (λ X → Fo X (suc (arity t))) (V ℓ)
        (λ X ψ → fst (keyS X ψ)) (sym qB) (embed (formula t)))
```

<!--en-->
The same dependence occurs for the value of uniform satisfaction. At the slot
carrier, the relevant set is `Sat` applied to the transported formula after
its constants have been relabelled into that carrier. At `Aʟ`, it is `Sat`
applied to the correspondingly relabelled embedded formula. Substitution along
`qB` commutes with this whole construction, so the two satisfaction sets have
equal underlying sets.
<!--zh-->
统一满足关系的取值也有同样的依赖。在位置载体处，所需集合是先把已搬运公式的常元改名到该载体，再对所得公式施用 `Sat`；在 `Aʟ` 处，则对相应改名后的嵌入公式施用 `Sat`。沿 `qB` 的代入与这整个构造相交换，所以两个满足关系集的底层集合相等。
<!--ja-->
統一充足関係の値にも同じ依存性がある。スロットの台では、輸送された論理式の定数をその台へ改名してから `Sat` を適用する。`Aʟ` では、対応する埋め込み済みの論理式を改名して `Sat` を適用する。`qB` に沿う代入はこの構成全体と可換なので、二つの充足関係集合の基礎集合は等しくなる。
<!--/-->

```agda
      satψ : (t : Name)
           → fst (Sat (lookup B γ) (mapFo (asConst (lookup B γ)) (ψAt t)))
           ≡ fst (Sat Aʟ (mapFo (asConst Aʟ) (embed (formula t))))
      satψ t = sym (constSubstCommSlice (λ X → Fo X (suc (arity t))) (V ℓ)
        (λ X ψ → fst (Sat X (mapFo (asConst X) ψ)))
```

<!--en-->
The final argument to the path-induction principle is the embedded formula
itself. This closes the proof of `satψ` without making any independent semantic
choice: the equality follows solely by substituting the carrier in a dependent
construction. Together, `keyψ` and `satψ` let the denotation argument pass
between the slot carrier and `Aʟ` while keeping both the formula key and its
satisfaction set aligned.
<!--zh-->
路径归纳原理的最后一个实参就是嵌入后的公式本身。由此 `satψ` 得证，过程中没有作任何独立的语义选择：这条等式只来自在依值构造中代入载体。`keyψ` 与 `satψ` 合在一起，使后面的指称论证可以在位置载体与 `Aʟ` 之间往返，同时保持公式键及其满足关系集对齐。
<!--ja-->
パス帰納法の原理へ最後に渡す引数は、埋め込まれた論理式そのものである。これで `satψ` の証明が閉じる。ここに独立な意味論的選択はなく、等式は依存的な構成で台を代入することだけから従う。`keyψ` と `satψ` を合わせると、後の表示の議論は、論理式の鍵とその充足関係集合を揃えたまま、スロットの台と `Aʟ` の間を移動できる。
<!--/-->

```agda
        (sym qB) (embed (formula t)))
```

<!--en-->
For a fixed meta-language name `t`, `Data t` records the four slot equalities
needed to represent it. The skeleton slot contains the underlying set of
`codeOf t`; the arity slot contains `# (arity t)`; the parameter slot contains
the environment graph `env (pfam t)`; and the denotation slot contains
`denote t`. These four equations mirror the four conceptual conjuncts of
`NameAt`. They assert that the current slots are aligned with this particular
name; they do not assert that all names with a given denotation are unique.
<!--zh-->
对一条固定的元语言名字 `t`，`Data t` 记录表示它所需的四条位置等式：骨架位置含有 `codeOf t` 的底层集合，元数位置含有 `# (arity t)`，参数位置含有环境图 `env (pfam t)`，指称位置含有 `denote t`。这四条等式恰与 `NameAt` 的四个概念性合取项相呼应。它们只断言当前诸位置与这条特定名字对齐，并不断言具有同一指称的所有名字都是唯一的。
<!--ja-->
固定したメタ言語の名前 `t` に対して、`Data t` はそれを表すために必要な四つのスロット等式を記録する。骨格のスロットは `codeOf t` の基礎集合を、アリティのスロットは `# (arity t)` を、パラメータのスロットは環境グラフ `env (pfam t)` を、表示のスロットは `denote t` を保持する。この四つの等式は `NameAt` の四つの概念的な連言項に対応する。ここで述べるのは現在のスロットがこの特定の名前と揃っていることであり、同じ指示対象をもつすべての名前の一意性ではない。
<!--/-->

```agda
    Data : Name → Type (ℓ-suc ℓ)
    Data t = (fst (lookup s γ) ≡ fst (codeOf t))
           × ( (fst (lookup a γ) ≡ # (arity t))
             × ( (fst (lookup e γ) ≡ env (pfam t))
               × (fst (lookup d γ) ≡ denote t) ) )
```

<!--en-->
To compare the denotation clause with `denote t`, the module `Body` fixes `t`
and the first three components of `Data t`. The skeleton equality `qs` aligns
the formula key, and the parameter equality `qe` aligns the parameter graph.
The arity equality `qa` records the remaining slot alignment for the same name;
once `t` is fixed, the denotation argument obtains the extended length directly
as `suc (arity t)`. The private vector `δp` presents the parameters in the
restricted semantic carrier required by the satisfaction bridge.
<!--zh-->
为了比较指称条款与 `denote t`，模块 `Body` 固定 `t` 以及 `Data t` 的前三个分量。骨架等式 `qs` 对齐公式键，参数等式 `qe` 对齐参数图；元数等式 `qa` 则记录同一名字余下的位置对齐。名字 `t` 固定以后，指称论证直接以 `suc (arity t)` 取得扩张环境的长度。私有向量 `δp` 把参数呈现在满足关系桥所需的限制语义载体中。
<!--ja-->
表示の条件を `denote t` と比較するため、モジュール `Body` は `t` と `Data t` の最初の三成分を固定する。骨格の等式 `qs` が論理式の鍵をそろえ、パラメータの等式 `qe` がパラメータ・グラフをそろえる。アリティの等式 `qa` は同じ名前について残るスロットの対応を記録するが、`t` が固定された後の表示の議論では、拡張環境の長さを `suc (arity t)` として直接得る。非公開のベクトル `δp` は、充足関係の橋が要求する制限された意味論的な台の中でパラメータを表す。
<!--/-->

```agda
    module Body (t : Name) (qs : fst (lookup s γ) ≡ fst (codeOf t))
                (qa : fst (lookup a γ) ≡ # (arity t))
                (qe : fst (lookup e γ) ≡ env (pfam t)) where
      private
        δp : Vec NM.DA.SM (arity t)
```

<!--en-->
The parameters of a name already lie in the small member type `⟪ A ⟫`.
Mapping `NM.DA.ι` over them does something more precise than merely retaining
their indices: it equips each represented set with its membership in `A`,
making an element of the restricted model carrier `NM.DA.SM`. The resulting
vector `δp` has length `arity t` and is therefore the exact tail of the inner
environment at which the name's formula will be evaluated.
<!--zh-->
名字的参数本来就属于小成员类型 `⟪ A ⟫`。逐项施用 `NM.DA.ι` 并非只保留这些索引，而是把每个索引所表示的集合与其属于 `A` 的证明配在一起，形成限制模型载体 `NM.DA.SM` 的元素。所得向量 `δp` 的长度为 `arity t`，因而恰是名字公式求值时所用内层环境的尾部。
<!--ja-->
名前のパラメータは、すでに小さな要素型 `⟪ A ⟫` に属している。それぞれに `NM.DA.ι` を写す操作は、添字を保つだけではない。各添字が表す集合に、その集合が `A` に属する証明を組み合わせて、制限モデルの台 `NM.DA.SM` の要素にする。得られるベクトル `δp` の長さは `arity t` であり、名前の論理式を評価する内側の環境の尾部そのものである。
<!--/-->

```agda
        δp = map NM.DA.ι (params t)
```

<!--en-->
The slot equation `qe` describes the same parameters through the external
family `pfam t`, whereas the satisfaction bridge expects the graph of the
restricted-carrier vector `δp`. The equality `valuesOf t` identifies these two
presentations entry by entry. Composing it with `qe` gives `qd'`, which says
that the parameter slot contains exactly `envGraph Aʟ δp`. This is the form
needed both to build an extended environment and to recognize one later.
<!--zh-->
位置等式 `qe` 通过外围参数族 `pfam t` 描述同一组参数，而满足关系桥需要的是限制载体向量 `δp` 的图。等式 `valuesOf t` 逐项认同这两种表示；将它与 `qe` 复合便得到 `qd'`，即参数位置所含的正是 `envGraph Aʟ δp`。这一形式既用于构造扩张环境，也用于稍后识别任意给出的扩张环境。
<!--ja-->
スロット等式 `qe` は外側のパラメータ族 `pfam t` によって同じパラメータを記述するが、充足関係の橋が必要とするのは、制限された台のベクトル `δp` のグラフである。等式 `valuesOf t` は二つの表現を成分ごとに同一視する。これを `qe` と合成して得る `qd'` は、パラメータのスロットがちょうど `envGraph Aʟ δp` を含むことを述べる。この形は、拡張環境を作るときにも、後で与えられた拡張環境を識別するときにも使われる。
<!--/-->

```agda
        qd' : fst (lookup e γ) ≡ envGraph Aʟ δp
        qd' = qe ∙ valuesOf t
```

<!--en-->
The fourth condition in the denotation payload identifies its key. Starting
from the sealed `keyAt t`, `keyAt-fst` exposes the code-set key of the embedded
formula, and `keyCode` computes that key as the ordered pair of
`# (suc (arity t))` with the formula's limit-stage code. The skeleton equation
`qs` replaces this second component by the set in slot `s`. What remains is to
express the first component through the sealed length numeral.
<!--zh-->
指称载荷的第四项条件用于认同其键。从封印元素 `keyAt t` 出发，`keyAt-fst` 暴露嵌入公式的码集之键，`keyCode` 再把该键算成 `# (suc (arity t))` 与公式极限层码的有序对。骨架等式 `qs` 把第二个分量替换成位置 `s` 中的集合。余下的一步，是通过封印的长度数码表示第一个分量。
<!--ja-->
表示の中身にある第四の条件は、その鍵を同一視する。封印された要素 `keyAt t` から始めると、`keyAt-fst` が埋め込まれた論理式の符号集合の鍵を取り出し、`keyCode` がその鍵を `# (suc (arity t))` と論理式の極限段階コードとの順序対として計算する。骨格の等式 `qs` は第二成分をスロット `s` の集合で置き換える。残るのは、第一成分を封印された長さの数項によって表すことである。
<!--/-->

```agda
        qkey : fst (keyAt t)
             ≡ pr (fst (numAt (suc (arity t)))) (fst (lookup s γ))
        qkey = keyAt-fst t ∙ keyCode (formula t)
             ∙ cong (pr (# (suc (arity t)))) (sym qs)
             ∙ cong (λ u → pr u (fst (lookup s γ)))
```

<!--en-->
The last congruence uses `numAt-fst` in the reverse direction, replacing the
set-theoretic numeral by the underlying set of `numAt (suc (arity t))` inside
the ordered pair. The completed equation `qkey` therefore has exactly the form
required by `DenoteOf`: the chosen key is the pair of the chosen domain numeral
and the skeleton slot. In the reverse proof, the same calculation will be
reconstructed from the payload's key equation.
<!--zh-->
最后一次同余反向使用 `numAt-fst`，在有序对中把集合论数码替换成 `numAt (suc (arity t))` 的底层集合。完成后的 `qkey` 因而恰具 `DenoteOf` 所需的形式：所选的键是所选定义域数码与骨架位置组成的对。反向证明将从载荷自带的键等式重新构造同一次计算。
<!--ja-->
最後の合同性では `numAt-fst` を逆向きに使い、順序対の中の集合論的な数項を `numAt (suc (arity t))` の基礎集合で置き換える。完成した `qkey` は `DenoteOf` が要求する形そのものである。選んだ鍵は、選んだ定義域の数項と骨格のスロットとの対である。逆向きの証明では、中身に含まれる鍵の等式から同じ計算を組み立て直す。
<!--/-->

```agda
                 (sym (numAt-fst (suc (arity t))))
```

<!--en-->
The forward direction begins with an actual member `m : ⟪ A ⟫`, an ambient
element `z` presenting the same underlying set, and a proof that this set lies
in `denote t`. It supplies the four witnesses of `DenoteOf` in semantic order:
the environment obtained by adjoining `m` to the parameters, its length
numeral, the formula key, and the table value at that key. Six conditions link
these witnesses. Five describe their shape and alignment; the sixth converts
the assumed denotation membership into membership of the environment in the
table value.
<!--zh-->
正向先给定一个实际成员 `m : ⟪ A ⟫`、一个与它表示同一底层集合的外围元素 `z`，以及该集合属于 `denote t` 的证明。随后按语义次序给出 `DenoteOf` 的四个见证：把 `m` 添到诸参数之前所得的环境、该环境的长度数码、公式键，以及表在该键处的取值。六项条件把这些见证连在一起。前五项说明它们的形状与对齐关系，第六项则把所设的指称成员资格转换成环境对表取值的成员资格。
<!--ja-->
順方向では、実際の要素 `m : ⟪ A ⟫`、それと同じ基礎集合を表す外側の要素 `z`、そしてその集合が `denote t` に属するという証明から始める。`DenoteOf` の四つの証人を意味の順に与える。すなわち、パラメータの前に `m` を加えた環境、その長さの数項、論理式の鍵、その鍵での表の値である。これらを結ぶ条件は六つある。最初の五つは形と対応を記述し、最後の一つが、仮定した表示への所属を、環境が表の値に属するという所属へ変換する。
<!--/-->

```agda
      denote-fill : (z : S) (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ≡ fst z
                  → ⟨ ⟪ A ⟫↪ m ∈ denote t ⟩ → DenoteOf B C s e γ z
      denote-fill z m qm hz =
        envAt t m , (numAt (suc (arity t)) , (keyAt t , (valAt t
        , ( hcons , (hdom , (hkey , (qkey , (hgraph , hmem))))))))
```

<!--en-->
The first condition says that the chosen environment is obtained by adjoining
the candidate member to the parameter environment. The inward reading of
`consAtL` receives `qd'` for the old parameter graph, `sym qm` for the
candidate stored in slot `z`, and `envAt-fst t m` for the newly constructed
graph. It then proves the object-language extension formula. This establishes
that the formula will be evaluated with the candidate in its extra variable
slot and the original parameters following it.
<!--zh-->
第一项条件说明，所选环境由候选成员添入参数环境而得。`consAtL` 的向内读式接收三条等式：`qd'` 给出原参数图，`sym qm` 认同位置 `z` 中的候选集合，`envAt-fst t m` 给出新构造的环境图。由此即可证明对象语言中的扩张公式。这保证公式求值时，额外的变元位置由候选成员占据，其后依次是原有参数。
<!--ja-->
第一の条件は、選んだ環境が候補の要素をパラメータ環境へ加えて得られることを述べる。`consAtL` の内向きの読みには、元のパラメータグラフを与える `qd'`、スロット `z` の候補集合を同一視する `sym qm`、新しく作った環境グラフを与える `envAt-fst t m` を渡す。すると対象言語の拡張論理式が証明される。これにより、論理式の余分な変数スロットには候補の要素が入り、その後に元のパラメータが続くことが保証される。
<!--/-->

```agda
        where
        hcons : ⟨ (envAt t m ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
        hcons = consAtL-in Aʟ δp (NM.DA.ι m) (envAt t m ∷ z ∷ γ)
                  zero (suc zero) (sh2 e) qd' (sym qm) (envAt-fst t m)
```

<!--en-->
The second condition fixes the domain of that extended environment. Its
length is `suc (arity t)`: one position for the candidate, followed by
`arity t` parameter positions. The inward adequacy lemma for `domAt` is given
the underlying values of `environment t m` and a proof that each value is
constructible. The latter follows from membership in the constructible carrier
and transitivity of `L`.
<!--zh-->
第二项条件固定扩张环境的定义域。其长度为 `suc (arity t)`：一个位置留给候选成员，随后是 `arity t` 个参数位置。`domAt` 的向内充分性引理接收 `environment t m` 的底层取值，以及每个取值皆可构造的证明。后一事实来自这些值属于可构造载体，以及 `L` 的传递性。
<!--ja-->
第二の条件は、拡張環境の定義域を定める。その長さは `suc (arity t)` である。候補の要素のための一つの位置に、`arity t` 個のパラメータ位置が続く。`domAt` の内向きの妥当性補題には、`environment t m` の基礎となる値と、それぞれの値が構成可能であることの証明を渡す。後者は、それらの値が構成可能な台に属することと、`L` の推移性から従う。
<!--/-->

```agda
        hdom : ⟨ (numAt (suc (arity t)) ∷ envAt t m ∷ z ∷ γ)
                 ⊨ domAt (suc zero) zero ⟩
        hdom = domAt-fill (suc zero) zero
                 (numAt (suc (arity t)) ∷ envAt t m ∷ z ∷ γ)
                 (suc (arity t)) (values Aʟ (environment t m)) (valuesL t m)
```

<!--en-->
The same domain lemma must also see the chosen witnesses as the sets it is
meant to compare. The equality `envAt-fst t m` exposes the environment graph
underlying `envAt t m`, while `numAt-fst (suc (arity t))` exposes the expected
von Neumann numeral under the length witness. With these two projections, the
domain formula states exactly that the numeral codes the length of the chosen
environment.
<!--zh-->
同一条定义域引理还必须把所选见证看成它要比较的底层集合。等式 `envAt-fst t m` 暴露 `envAt t m` 的环境图，而 `numAt-fst (suc (arity t))` 暴露长度见证之下预期的 von Neumann 数码。有了这两条投影等式，定义域公式所陈述的就恰是：该数码编码所选环境的长度。
<!--ja-->
同じ定義域の補題は、選んだ証人を、それが比較すべき基礎集合としても見る必要がある。等式 `envAt-fst t m` は `envAt t m` の下にある環境グラフを取り出し、`numAt-fst (suc (arity t))` は長さの証人の下にある期待された von Neumann 数項を取り出す。この二つの射影等式により、定義域の論理式は、その数項が選んだ環境の長さを符号化することを正確に述べる。
<!--/-->

```agda
                 (envAt-fst t m) (numAt-fst (suc (arity t)))
```

<!--en-->
The third condition places the chosen key in the genuine code domain. The
constructor `keyAt` already provides membership in `AllCodes Aʟ`; the slot
equation `qC` transports this membership to the set stored in slot `C`.
This hypothesis cannot be omitted. The satisfaction graph is forced to carry
the semantic value of a formula at genuine code keys, whereas its behavior
outside the code domain need not determine such a value.
<!--zh-->
第三项条件把所选键放入真正的码定义域。构造 `keyAt` 已经给出该键属于 `AllCodes Aʟ`；位置等式 `qC` 再把这一成员资格搬运到位置 `C` 所存的集合中。这项假设不可省略：满足关系图在真实公式键处必须给出公式的语义取值，而在码定义域之外，它的行为无须确定这样的取值。
<!--ja-->
第三の条件は、選んだ鍵を真正な符号領域に置く。構成 `keyAt` はすでに、その鍵が `AllCodes Aʟ` に属することを与える。スロット等式 `qC` に沿ってこの所属を輸送すれば、スロット `C` に格納された集合への所属が得られる。この仮定は省けない。充足関係グラフが論理式の意味論的な値を与えることを強制されるのは真正な符号の鍵においてであり、符号領域の外での振る舞いはそのような値を定める必要がないからである。
<!--/-->

```agda
        hkey : ⟨ fst (keyAt t) ∈ fst (lookup C γ) ⟩
        hkey = subst (λ u → ⟨ fst (keyAt t) ∈ u ⟩) (sym qC) (keyAt-∈ t)
```

<!--en-->
The fifth condition says that the chosen value is the value admitted by the
satisfaction graph at the chosen key. The graph formula is evaluated after
five new entries have been placed before the ambient assignment: value, key,
length numeral, extended environment, and candidate. Its first alignment
hypothesis identifies the underlying set of `keyAt t` with the key of `ψAt t`
at the slot carrier. This is exactly where `keyψ` carries the earlier key
calculation across `qB`.
<!--zh-->
第五项条件说明，所选取值正是满足关系图在所选键处容许的取值。求值该图公式时，外围赋值之前已经依次压入五项：取值、键、长度数码、扩张环境与候选成员。第一条对齐假设把 `keyAt t` 的底层集合认同为位置载体处 `ψAt t` 的键；先前的 `keyψ` 正是在这里把键的计算沿 `qB` 搬过载体边界。
<!--ja-->
第五の条件は、選んだ値が、選んだ鍵で充足関係グラフに許される値であることを述べる。グラフの論理式を評価するとき、外側の割り当ての前には、値、鍵、長さの数項、拡張環境、候補の要素という五項が順に置かれている。第一の対応条件は、`keyAt t` の基礎集合を、スロットの台における `ψAt t` の鍵と同一視する。先に示した `keyψ` は、まさにここで鍵の計算を `qB` に沿って台の境界の向こうへ運ぶ。
<!--/-->

```agda
        hgraph : ⟨ (valAt t ∷ keyAt t ∷ numAt (suc (arity t)) ∷ envAt t m
                    ∷ z ∷ γ) ⊨ satGraphAt (sh5 B) (suc zero) zero ⟩
        hgraph = graphAt-value (sh5 B) (suc zero) zero
                   (valAt t ∷ keyAt t ∷ numAt (suc (arity t)) ∷ envAt t m
                    ∷ z ∷ γ) (ψAt t)
```

<!--en-->
The second alignment hypothesis identifies the chosen value. First
`valAt-val` exposes it as the table value at `keyAt t`. The law `val-at`
identifies that table value with the `Sat` set of the embedded formula over
`Aʟ`. Finally `satψ`, read in the required direction, transports this set to
the slot carrier. The two alignment equations now allow `graphAt-value` to
establish the graph condition without changing either the key or its semantic
value.
<!--zh-->
第二条对齐假设认同所选取值。首先，`valAt-val` 把它暴露为表在 `keyAt t` 处的取值；定律 `val-at` 把该表取值认同为嵌入公式在 `Aʟ` 上的 `Sat` 集；最后按所需方向读取 `satψ`，把这个集合搬运到位置载体。有了两条对齐等式，`graphAt-value` 便可证明图条件，同时保持公式键及其语义取值不变。
<!--ja-->
第二の対応条件は、選んだ値を同一視する。まず `valAt-val` が、それを `keyAt t` における表の値として取り出す。法則 `val-at` は、その表の値を `Aʟ` 上の埋め込まれた論理式の `Sat` 集合と同一視する。最後に `satψ` を必要な向きに読んで、この集合をスロットの台へ輸送する。二つの対応等式が揃うと、`graphAt-value` は論理式の鍵とその意味論的な値を変えることなく、グラフの条件を証明できる。
<!--/-->

```agda
                   (keyAt-fst t ∙ sym (keyψ t))
                   ( cong fst (valAt-val t)
                   ∙ cong fst (val-at Aʟ Aʟ (embed (formula t))
                                 (keyAt t) (keyAt-∈ t) (keyAt-fst t))
                   ∙ sym (satψ t) )
```

<!--en-->
The sixth condition is the decisive membership: the encoded extended
environment must belong to the selected graph value. The hypothesis says that
the member represented by `m` lies in `denote t`. The characterization
`NM.denote-mem t m` turns this into inner satisfaction of
`embed (formula t)` by `environment t m`. Thus denotation membership supplies
exactly the semantic fact that the uniform table is designed to record.
<!--zh-->
第六项条件是决定性的成员关系：编码后的扩张环境必须属于所选的图取值。假设说由 `m` 表示的成员属于 `denote t`。刻画式 `NM.denote-mem t m` 把它化为内层满足关系，即 `environment t m` 满足 `embed (formula t)`。因此，指称成员资格恰好给出统一满足关系表所要记录的语义事实。
<!--ja-->
第六の条件は決定的な所属である。符号化された拡張環境は、選んだグラフの値に属さなければならない。仮定は、`m` が表す要素が `denote t` に属することを述べる。特徴づけ `NM.denote-mem t m` は、これを `environment t m` が `embed (formula t)` を内側で充足することへ変える。したがって表示への所属は、統一充足関係表が記録すべき意味論的な事実をちょうど与える。
<!--/-->

```agda
        hmem : ⟨ fst (envAt t m) ∈ fst (valAt t) ⟩
        hmem = subst (λ u → ⟨ envAt t m ∈ˢ u ⟩) (sym (valAt-val t)) inTable
          where
          inner : ⟨ NM.DA._⊨ᵐ_ (environment t m) (embed (formula t)) ⟩
          inner = subst ⟨_⟩ (NM.denote-mem t m) hz
```

<!--en-->
The law `val-sat` identifies that inner satisfaction with membership of
`envAt t m` in the table value at `keyAt t`; it is read backwards here because
the proof starts from satisfaction. Transport along `valAt-val` then replaces
the explicit table value by the sealed witness `valAt t`. This proves the
sixth condition and completes `denote-fill`: all four witnesses and all six
relations among them have been obtained from the data of `t` and the assumed
membership in its denotation.
<!--zh-->
定律 `val-sat` 把这项内层满足关系认同为 `envAt t m` 属于表在 `keyAt t` 处的取值；此处证明从满足关系出发，所以反向读取该定律。随后沿 `valAt-val` 搬运，把显式的表取值替换成封印见证 `valAt t`。第六项条件由此得证，`denote-fill` 也随之完成：四个见证及其间的六项关系，全都来自名字 `t` 的数据与所设的指称成员资格。
<!--ja-->
法則 `val-sat` は、この内側の充足関係を、`envAt t m` が `keyAt t` における表の値に属することと同一視する。ここでは充足関係から始めるため、この法則を逆向きに読む。次に `valAt-val` に沿って輸送し、明示的な表の値を封印された証人 `valAt t` で置き換える。これで第六の条件が証明され、`denote-fill` が完成する。四つの証人とそれらを結ぶ六つの関係は、すべて名前 `t` のデータと、その指示対象への仮定された所属から得られた。
<!--/-->

```agda
          inTable : ⟨ envAt t m ∈ˢ Table.val Aʟ Aʟ (keyAt t) (keyAt-∈ t) ⟩
          inTable = subst ⟨_⟩
            (sym (val-sat Aʟ (embed (formula t)) (keyAt t) (keyAt-∈ t)
                    (keyAt-fst t) (environment t m) (envAt t m)
                    (envAt-fst t m))) inner
```

<!--en-->
For the reverse direction, suppose an explicit `DenoteOf` payload is given for
`z`: four bound elements together with the six conditions just described. The
goal is to prove that the member `m` represented by `z` belongs to `denote t`.
By the reverse direction of `NM.denote-mem`, it is enough to reconstruct inner
satisfaction of the embedded formula at `environment t m`. The remaining
equalities successively identify the arbitrary environment, numeral, key, and
value supplied by the payload.
<!--zh-->
反向设已经给出 `z` 处的一份显式 `DenoteOf` 载荷，即四个被绑定元素连同上述六项条件。目标是证明由 `z` 表示的成员 `m` 属于 `denote t`。按 `NM.denote-mem` 的反向读式，只需重建嵌入公式在 `environment t m` 处的内层满足关系。余下诸等式将依次识别载荷任意给出的环境、数码、键与取值。
<!--ja-->
逆向きでは、`z` に対する明示的な `DenoteOf` の中身、すなわち四つの束縛された要素と先の六条件が与えられているとする。目標は、`z` が表す要素 `m` が `denote t` に属することである。`NM.denote-mem` を逆向きに読めば、埋め込まれた論理式が `environment t m` で内側の充足関係を満たすことを復元すれば十分である。残る等式は、中身が任意に与えた環境、数項、鍵、値を順に識別する。
<!--/-->

```agda
      denote-read : (z : S) (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ≡ fst z
                  → DenoteOf B C s e γ z → ⟨ ⟪ A ⟫↪ m ∈ denote t ⟩
      denote-read z m qm (c , (k , (key , (v , (hc , (hk , (hi , (hp , (hg , hm)))))))))
        = subst ⟨_⟩ (sym (NM.denote-mem t m)) inner
        where
```

<!--en-->
The extension condition is read first. Its outward adequacy theorem compares
the old graph `qd'`, the candidate identification `sym qm`, and the satisfaction
proof `hc`. It follows that the underlying set of the arbitrary witness `c` is
exactly `envGraph Aʟ (environment t m)`. Thus the first existential witness is
not merely some extension of the parameter graph: its graph is the canonical
environment obtained by putting `m` before the parameters of `t`.
<!--zh-->
首先读取扩张条件。它的向外充分性定理比较原图 `qd'`、候选成员等式 `sym qm` 与满足证明 `hc`，由此推出任意见证 `c` 的底层集合恰为 `envGraph Aʟ (environment t m)`。因此，第一个存在见证不只是参数图的某个扩张；它正是把 `m` 放在名字 `t` 的诸参数之前所得典范环境的图。
<!--ja-->
まず拡張の条件を読む。その外向きの妥当性定理は、元のグラフ `qd'`、候補の要素を同一視する `sym qm`、充足証明 `hc` を比較する。その結果、任意に与えられた証人 `c` の基礎集合は、ちょうど `envGraph Aʟ (environment t m)` だと分かる。したがって、最初の存在証人はパラメータグラフの単なる何らかの拡張ではなく、`m` を名前 `t` のパラメータの前に置いて得る正準な環境のグラフである。
<!--/-->

```agda
        qcg : fst c ≡ envGraph Aʟ (environment t m)
        qcg = consAtL-out Aʟ δp (NM.DA.ι m) (c ∷ z ∷ γ)
                zero (suc zero) (sh2 e) qd' (sym qm) hc
```

<!--en-->
The domain condition then determines the numeral witness. Since `qcg`
identifies `c` with the graph of `environment t m`, `domAt-numeral` reads `hk`
as an equality between the underlying set of `k` and the numeral for that
environment's length. The length is `suc (arity t)`, and `valuesL` supplies the
constructibility needed by the domain adequacy theorem. Hence
`fst k ≡ # (suc (arity t))`.
<!--zh-->
定义域条件继而确定数码见证。由于 `qcg` 已把 `c` 认同为 `environment t m` 的图，`domAt-numeral` 可把 `hk` 读成一条等式：`k` 的底层集合等于该环境长度的数码。此长度为 `suc (arity t)`，而 `valuesL` 提供定义域充分性定理所需的可构造性。因此得到 `fst k ≡ # (suc (arity t))`。
<!--ja-->
次に定義域の条件が数項の証人を決定する。`qcg` が `c` を `environment t m` のグラフと同一視しているので、`domAt-numeral` は `hk` を、`k` の基礎集合とその環境の長さを表す数項との等式として読める。この長さは `suc (arity t)` であり、`valuesL` が定義域の妥当性定理に必要な構成可能性を与える。したがって `fst k ≡ # (suc (arity t))` が得られる。
<!--/-->

```agda
        qk : fst k ≡ # (suc (arity t))
        qk = domAt-numeral (suc zero) zero (k ∷ c ∷ z ∷ γ) (suc (arity t))
               (values Aʟ (environment t m)) (valuesL t m) qcg hk
```

<!--en-->
The payload's fourth condition `hp` says that its key is the pair of its own
domain witness `k` and the skeleton slot. Rewriting the first component by
`qk` and the second by `qs` gives the pair of `# (suc (arity t))` with the
formula code. Finally, `keyCode (formula t)` is read backwards to recognize
this pair as the code-set key of `embed (formula t)`. The resulting equality
`qkey'` identifies the arbitrary payload key with the genuine formula key.
<!--zh-->
载荷的第四项条件 `hp` 说明，它的键是自身定义域见证 `k` 与骨架位置组成的对。用 `qk` 改写第一个分量、用 `qs` 改写第二个分量，便得到 `# (suc (arity t))` 与公式码之对。最后反向读取 `keyCode (formula t)`，把这一对识别为 `embed (formula t)` 的码集之键。所得等式 `qkey'` 因而把载荷任意给出的键认同为真正的公式键。
<!--ja-->
中身の第四の条件 `hp` は、その鍵が自身の定義域の証人 `k` と骨格のスロットとの対であることを述べる。第一成分を `qk` で、第二成分を `qs` で書き換えると、`# (suc (arity t))` と論理式コードとの対が得られる。最後に `keyCode (formula t)` を逆向きに読み、この対を `embed (formula t)` の符号集合の鍵として認識する。こうして得た等式 `qkey'` は、中身が任意に与えた鍵を真正な論理式の鍵と同一視する。
<!--/-->

```agda
        qkey' : fst key ≡ fst (keyS Aʟ (embed (formula t)))
        qkey' = hp ∙ cong (λ u → pr u (fst (lookup s γ))) qk
              ∙ cong (pr (# (suc (arity t)))) qs ∙ sym (keyCode (formula t))
```

<!--en-->
The membership condition `hi` says that this recovered key belongs to the set
stored in slot `C`. Transport along `qC` turns it into membership in
`AllCodes Aʟ`, producing `key∈`. This is a membership proof, not a choice of a
new key: the key has already been supplied by the `DenoteOf` payload and
identified by `qkey'`. Its role is to put that key inside the domain where the
uniform table and the satisfaction graph have their semantic specification.
<!--zh-->
成员条件 `hi` 说明这个已恢复的键属于位置 `C` 所存的集合。沿 `qC` 搬运后，它成为对 `AllCodes Aʟ` 的成员资格，即 `key∈`。这是一份成员证明，并非选择一个新键：该键早已由 `DenoteOf` 载荷给出，并经 `qkey'` 得到认同。它的作用是把这个键放入统一表与满足关系图具有语义规格的定义域中。
<!--ja-->
所属条件 `hi` は、復元された鍵がスロット `C` に格納された集合に属することを述べる。`qC` に沿って輸送すると、`AllCodes Aʟ` への所属 `key∈` が得られる。これは所属の証明であって、新しい鍵の選択ではない。鍵そのものはすでに `DenoteOf` の中身から与えられ、`qkey'` によって同一視されている。この証明の役割は、その鍵を、統一表と充足関係グラフの意味論的な仕様が成り立つ領域に置くことである。
<!--/-->

```agda
        key∈ : ⟨ key ∈ˢ AllCodes Aʟ ⟩
        key∈ = subst (λ u → ⟨ fst key ∈ u ⟩) qC hi
```

<!--en-->
It remains to identify the arbitrary value witness `v`. The uniqueness reading
`graphAt-only` applies to the graph proof `hg` once `qkey'` and `keyψ` have
aligned its key with `ψAt t` at the slot carrier. It first identifies `fst v`
with the corresponding `Sat` set. The transport `satψ` moves that set back to
`Aʟ`, and `val-at`, read backwards, identifies it with
`Table.val Aʟ Aʟ key key∈`. Thus `qval` recovers the table value required to
turn the final membership `hm` into inner satisfaction in the next step.
<!--zh-->
最后还须认同任意给出的取值见证 `v`。先用 `qkey'` 与 `keyψ` 把它的键同位置载体处 `ψAt t` 的键对齐，图证明 `hg` 便可交给唯一性读式 `graphAt-only`，从而先把 `fst v` 认同为相应的 `Sat` 集。搬运等式 `satψ` 把该集合送回 `Aʟ`，再反向读取 `val-at`，将它认同为 `Table.val Aʟ Aʟ key key∈`。于是 `qval` 恢复出所需的表取值，使下一步能够把末尾成员关系 `hm` 转成内层满足关系。
<!--ja-->
最後に、任意に与えられた値の証人 `v` を同一視する。`qkey'` と `keyψ` によって、その鍵をスロットの台における `ψAt t` の鍵と揃えると、グラフの証明 `hg` に一意性の読み `graphAt-only` を適用できる。これにより、まず `fst v` が対応する `Sat` 集合と同一視される。輸送 `satψ` がその集合を `Aʟ` へ戻し、`val-at` を逆向きに読むことで `Table.val Aʟ Aʟ key key∈` と同一視する。こうして `qval` が必要な表の値を復元し、次の段階で最後の所属 `hm` を内側の充足関係へ変換できるようになる。
<!--/-->

```agda
        qval : fst v ≡ fst (Table.val Aʟ Aʟ key key∈)
        qval = graphAt-only (sh5 B) (suc zero) zero
                 (v ∷ key ∷ k ∷ c ∷ z ∷ γ) (ψAt t) (qkey' ∙ sym (keyψ t)) hg
             ∙ satψ t
             ∙ sym (cong fst (val-at Aʟ Aʟ (embed (formula t)) key key∈ qkey'))
```

<!--en-->
The last component of `DenoteOf` says that the extended environment `c` belongs
to the recovered value `v`. The path `qval` identifies this value with the
uniform satisfaction table at the recovered code key. Transporting membership
along that path therefore gives exactly the table membership required for the
next semantic reading.
<!--zh-->
`DenoteOf` 的最后一个分量说，扩张环境 `c` 属于恢复出的取值 `v`。路径 `qval` 把这个取值认作统一满足表在恢复出的公式码键处的表值。沿该路径迁移隶属关系，便得到下一条语义读式所需的表隶属。
<!--ja-->
`DenoteOf` の最後の成分は、拡張された環境 `c` が復元された値 `v` に属することを述べる。パス `qval` は、この値を復元された論理式符号のキーにおける一様充足表の値と同定する。このパスに沿って所属を移送すると、次の意味論的な読みに必要な表への所属が得られる。
<!--/-->

```agda
        inTable : ⟨ c ∈ˢ Table.val Aʟ Aʟ key key∈ ⟩
        inTable = subst (λ u → ⟨ fst c ∈ u ⟩) qval hm
```

<!--en-->
The adequacy equation `val-sat` now reads membership in that table value as
satisfaction of the embedded formula. Its hypotheses use `qkey'` to identify
the recovered key and `qcg` to identify `c` with the graph of the extended
environment. Thus `inner` states that `environment t m` satisfies the formula
of `t`; the enclosing result then uses `denote-mem` in reverse to recover
membership in `denote t`.
<!--zh-->
充分性等式 `val-sat` 随即把对该表值的隶属读作对嵌入公式的满足。它的假设以 `qkey'` 认定恢复出的键，并以 `qcg` 把 `c` 认作扩张环境的图。因此，`inner` 断言 `environment t m` 满足名字 `t` 的公式；外层结果再反向使用 `denote-mem`，得到对 `denote t` 的隶属。
<!--ja-->
妥当性の等式 `val-sat` は、この表の値への所属を埋め込まれた論理式の充足として読む。その仮定では、`qkey'` が復元されたキーを同定し、`qcg` が `c` を拡張された環境のグラフと同定する。したがって `inner` は、`environment t m` が名前 `t` の論理式を満たすことを述べる。外側の結果では、さらに `denote-mem` を逆向きに用いて `denote t` への所属を得る。
<!--/-->

```agda
        inner : ⟨ NM.DA._⊨ᵐ_ (environment t m) (embed (formula t)) ⟩
        inner = subst ⟨_⟩
          (val-sat Aʟ (embed (formula t)) key key∈ qkey'
             (environment t m) c qcg) inTable
```

<!--en-->
The preceding readings were stated for a member `m` of the carrier. The lemma
`member-fill` reformulates the forward reading for an arbitrary constructible
element `z`: membership of its underlying set in `denote t` implies both
membership in the carrier slot and the full witness package `DenoteOf`. The
first conclusion is transported from actual membership in `A` along the slot
equation `qB`.
<!--zh-->
前面的读式以载体成员 `m` 为对象。引理 `member-fill` 把正向读式改写到任意可构造元素 `z` 上：若其底集属于 `denote t`，便可同时得到它对载体位置的隶属以及完整的见证组 `DenoteOf`。第一项结论先在集合 `A` 中取得，再沿位置等式 `qB` 迁移。
<!--ja-->
ここまでの読みは、台の元 `m` に対して述べられていた。補題 `member-fill` は順方向の読みを任意の構成可能な要素 `z` に言い換える。その台集合が `denote t` に属するなら、台のスロットへの所属と、証人の組 `DenoteOf` の両方が得られる。第一の結論は、集合 `A` への実際の所属から得た後、スロットの等式 `qB` に沿って移送される。
<!--/-->

```agda
      member-fill : (z : S) → ⟨ fst z ∈ denote t ⟩
                  → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
      member-fill z hz = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (cong fst qB)) hA
        , denote-fill z (fib .fst) (fib .snd)
            (subst (λ u → ⟨ u ∈ denote t ⟩) (sym (fib .snd)) hz)
```

<!--en-->
To apply the member-level lemma, one must recover the carrier member represented
by `z`. The containment lemma `denoteMem` first turns membership in the
denotation into membership in `A`. The fibre presentation of membership then
provides an `m : ⟪ A ⟫` together with the equation `⟪ A ⟫↪ m ≡ fst z`; this is
ordinary dependent data, so no choice principle or truncation elimination is
involved.
<!--zh-->
要应用成员层面的引理，必须先恢复 `z` 所表示的载体成员。包含引理 `denoteMem` 先把对指称的隶属变成对 `A` 的隶属。随后，隶属关系的纤维表示给出 `m : ⟪ A ⟫` 以及等式 `⟪ A ⟫↪ m ≡ fst z`；这是普通的依赖数据，不涉及选择原理或命题截断的消去。
<!--ja-->
元に対する補題を適用するには、`z` が表す台の元をまず復元する必要がある。包含補題 `denoteMem` は、表示への所属を `A` への所属に変える。次に、所属のファイバー表示から `m : ⟪ A ⟫` と等式 `⟪ A ⟫↪ m ≡ fst z` が得られる。これは通常の依存データなので、選択原理も命題的切り詰めの除去も使わない。
<!--/-->

```agda
        where
        hA : ⟨ fst z ∈ A ⟩
        hA = denoteMem t (fst z) hz
        fib : Σ[ mm ∶ ⟪ A ⟫ ] (⟪ A ⟫↪ mm ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = A} hA
```

<!--en-->
The converse reformulation starts with membership of `z` in the carrier slot
and a `DenoteOf` package. After recovering the represented carrier member, the
earlier lemma `denote-read` turns that package into membership of the embedded
member in `denote t`. Transport along the fibre equation changes this conclusion
back into membership of `fst z`.
<!--zh-->
反向改写从 `z` 对载体位置的隶属以及一组 `DenoteOf` 数据出发。恢复出它所表示的载体成员之后，前面的引理 `denote-read` 把该数据组读成嵌入成员对 `denote t` 的隶属。最后沿纤维等式迁移，便得到 `fst z` 对该指称的隶属。
<!--ja-->
逆向きの言い換えは、`z` の台のスロットへの所属と `DenoteOf` の証人の組から始まる。`z` が表す台の元を復元した後、先の補題 `denote-read` はその証人の組を、埋め込まれた元の `denote t` への所属として読む。最後にファイバーの等式に沿って移送し、`fst z` の所属へ戻す。
<!--/-->

```agda
      member-read : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩
                  → DenoteOf B C s e γ z → ⟨ fst z ∈ denote t ⟩
      member-read z hz hDen = subst (λ u → ⟨ u ∈ denote t ⟩) (fib .snd)
        (denote-read z (fib .fst) (fib .snd) hDen)
        where
```

<!--en-->
Here the required fibre comes from the carrier-slot hypothesis. The equation
`qB` identifies the underlying set in that slot with `A`, so transport first
produces `fst z ∈ A`; `∈-asFiber` then returns the corresponding member of
`⟪ A ⟫` and its embedding equation. Consequently the two member lemmas apply to
every element of the model that satisfies the relevant membership hypothesis,
not only to an element already presented in the small carrier type.
<!--zh-->
这里所需的纤维来自载体位置的隶属假设。等式 `qB` 把该位置的底集与 `A` 认同，所以迁移后先得到 `fst z ∈ A`；`∈-asFiber` 再给出 `⟪ A ⟫` 中对应的成员及其嵌入等式。因此，这两条成员引理适用于模型中满足相应隶属假设的每个元素，而不要求输入预先以小载体类型中的成员给出。
<!--ja-->
ここで必要なファイバーは、台のスロットへの所属という仮定から得られる。等式 `qB` はそのスロットの台集合を `A` と同定するので、移送によってまず `fst z ∈ A` が得られる。続いて `∈-asFiber` が `⟪ A ⟫` の対応する元と、その埋め込みの等式を返す。したがって二つの補題は、小さな台の型の元としてあらかじめ与えられた場合だけでなく、必要な所属を満たすモデルの任意の要素に適用できる。
<!--/-->

```agda
        fib : Σ[ mm ∶ ⟪ A ⟫ ] (⟪ A ⟫↪ mm ≡ fst z)
        fib = ∈-asFiber {a = fst z} {b = A}
          (subst (λ u → ⟨ fst z ∈ u ⟩) (cong fst qB) hz)
```

<!--en-->
## A name, assembled
<!--zh-->
## 一个名字，装配起来
<!--ja-->
## 名前を組み立てる
<!--/-->

<!--en-->
For a fixed name `t`, `Data t` records four equations: the skeleton slot is its
formula code, the arity slot is its numeral, the environment slot is its
parameter graph, and the denotation slot is `denote t`. `NameAt-fill` uses these
equations to establish the four conceptual conjuncts of `NameAt`: freeness from
constants, membership of the arity in `ω`, the environment condition, and the
extensional characterization of the denotation. The last conjunct is supplied
by its two membership directions `into` and `back`.
<!--zh-->
对于固定名字 `t`，`Data t` 记录四条等式：骨架位置是其公式码，元数位置是其数码，环境位置是其参数图，指称位置是 `denote t`。`NameAt-fill` 用这些等式证明 `NameAt` 的四个概念合取项：公式无常元、元数属于 `ω`、参数满足环境条件，以及指称的外延刻画。最后一个合取项由成员关系的两个方向 `into` 与 `back` 给出。
<!--ja-->
固定した名前 `t` に対して、`Data t` は四つの等式を記録する。骨格のスロットはその論理式の符号、アリティのスロットはその数項、環境のスロットはそのパラメータのグラフ、表示のスロットは `denote t` である。`NameAt-fill` はこれらの等式を用いて、`NameAt` の四つの概念的な連言、すなわち定数を含まないこと、アリティが `ω` に属すること、環境条件、表示の外延的な特徴付けを証明する。最後の連言は、所属の二方向 `into` と `back` によって与えられる。
<!--/-->

```agda
    NameAt-fill : (t : Name) → Data t → ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩
    NameAt-fill t (qs , (qa , (qe , qd))) =
      NameAt-in B C C₀ s a e d γ hf ha he into back
      where
      module Bt = Body t qs qa qe
```

<!--en-->
The first conjunct is obtained from the actual parameter-free formula carried by
`t`. Its formula has `suc (arity t)` variable positions, and `qs` identifies its
limit-stage code with the skeleton slot. With `qa` identifying the arity slot
and `q₀` identifying the empty-alphabet code set, `codeFree-in` turns precisely
this formula and code equation into satisfaction of `FreeAt`.
<!--zh-->
第一个合取项来自名字 `t` 所携带的实际无参公式。该公式有 `suc (arity t)` 个变量位置，而 `qs` 把它在极限层中的码与骨架位置认同。再用 `qa` 认定元数位置、用 `q₀` 认定空字母表的码集，`codeFree-in` 就把这条公式及其码等式转成对 `FreeAt` 的满足。
<!--ja-->
最初の連言は、名前 `t` がもつ具体的な無パラメータ論理式から得られる。この論理式には `suc (arity t)` 個の変数位置があり、`qs` はその極限段階での符号を骨格のスロットと同定する。さらに `qa` がアリティのスロットを、`q₀` が空のアルファベットの符号集合を同定するので、`codeFree-in` はこの論理式と符号の等式をそのまま `FreeAt` の充足へ変換する。
<!--/-->

```agda
      hf : ⟨ γ ⊨ FreeAt C₀ s a ⟩
      hf = codeFree-in C₀ s a γ (arity t) q₀ qa (formula t) qs
```

<!--en-->
The arity conjunct requires only membership in `ω`. The canonical fact
`#∈ω (arity t)` supplies membership of the numeral, and the equation `qa`
transports it to the value stored in the arity slot. No comparison relation is
used in this part of the description.
<!--zh-->
元数合取项只要求对 `ω` 的隶属。典范事实 `#∈ω (arity t)` 给出该数码对 `ω` 的隶属，等式 `qa` 再把它迁移到元数位置所存的值上。这部分描述不使用任何比较关系。
<!--ja-->
アリティの連言が要求するのは `ω` への所属だけである。標準的な事実 `#∈ω (arity t)` がその数項の `ω` への所属を与え、等式 `qa` がそれをアリティのスロットに格納された値へ移送する。この部分の記述では比較関係を使わない。
<!--/-->

```agda
      ha : ⟨ fst (lookup a γ) ∈ ω ⟩
      ha = subst (λ u → ⟨ u ∈ ω ⟩) (sym qa) (#∈ω (arity t))
```

<!--en-->
For the environment conjunct, the parameter vector of `t` is viewed as the
family `i ↦ lookup i (params t)`. Its graph equation is `qe`, its domain numeral
equation is `qa`, and `qB` identifies its codomain carrier with `Aʟ`.
`paramSeq-in` transports the standard environment property of this family to
the three slots, yielding satisfaction of `envOverAt`.
<!--zh-->
对于环境合取项，把名字 `t` 的参数向量看作族 `i ↦ lookup i (params t)`。它的图等式是 `qe`，定义域数码的等式是 `qa`，而 `qB` 把余域载体认作 `Aʟ`。`paramSeq-in` 将这个族的标准环境性质迁移到三个位置上，从而得到对 `envOverAt` 的满足。
<!--ja-->
環境の連言では、名前 `t` のパラメータベクトルを族 `i ↦ lookup i (params t)` とみなす。そのグラフの等式は `qe`、定義域の数項についての等式は `qa` であり、`qB` は終域の台を `Aʟ` と同定する。`paramSeq-in` はこの族の標準的な環境の性質を三つのスロットへ移送し、`envOverAt` の充足を与える。
<!--/-->

```agda
      he : ⟨ γ ⊨ envOverAt e a B ⟩
      he = paramSeq-in e a B γ (arity t) (λ i → lookup i (params t)) qe qa
             (cong fst qB)
```

<!--en-->
The forward direction of the extensional conjunct begins with an element of the
denotation slot. Transport along `qd` makes it a member of `denote t`.
`Bt.member-fill` then supplies exactly the two parts of the denotation body:
membership in the carrier slot and the witness package `DenoteOf`.
<!--zh-->
指称外延合取项的正向从指称位置的一个成员出发。沿 `qd` 迁移后，它成为 `denote t` 的成员。随后，`Bt.member-fill` 恰好给出指称公式体的两部分：对载体位置的隶属以及见证组 `DenoteOf`。
<!--ja-->
表示を外延的に特徴付ける連言の順方向は、表示のスロットの元から始まる。`qd` に沿って移送すると、その元は `denote t` の元になる。そこで `Bt.member-fill` が、表示の本体をなす二つの部分、すなわち台のスロットへの所属と証人の組 `DenoteOf` をちょうど与える。
<!--/-->

```agda
      into : (z : S) → ⟨ fst z ∈ fst (lookup d γ) ⟩
           → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
      into z hz = Bt.member-fill z (subst (λ u → ⟨ fst z ∈ u ⟩) qd hz)
```

<!--en-->
Conversely, carrier membership together with `DenoteOf` is read by
`Bt.member-read` as membership in `denote t`. Transport along the inverse of
`qd` places the element back in the denotation slot. These two functions are
the two directions required by the single extensional conjunct of `NameAt`.
<!--zh-->
反过来，`Bt.member-read` 把载体隶属与 `DenoteOf` 合在一起读作对 `denote t` 的隶属。再沿 `qd` 的逆向迁移，便把该元素放回指称位置。这两个函数正是 `NameAt` 中同一个外延合取项所需的两个方向。
<!--ja-->
逆に、`Bt.member-read` は台への所属と `DenoteOf` を合わせて、`denote t` への所属として読む。さらに `qd` の逆向きに沿って移送すると、その要素は表示のスロットへ戻る。この二つの関数が、`NameAt` にある一つの外延的な連言に必要な二方向である。
<!--/-->

```agda
      back : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf B C s e γ z
           → ⟨ fst z ∈ fst (lookup d γ) ⟩
      back z hzB hDen = subst (λ u → ⟨ fst z ∈ u ⟩) (sym qd)
        (Bt.member-read z hzB hDen)
```

<!--en-->
The reverse reading of `NameAt` returns only the propositional truncation of a
name with its four data equations. The arity conjunct `ha` is membership in
`ω`; its semantic presentation supplies, under propositional truncation, a
natural number `k` and an equation identifying the arity slot with `# k`.
`rec₁` may inspect that witness because the final result is itself a
propositionally truncated type.
<!--zh-->
`NameAt` 的反向读式只返回「一个名字及其四条数据等式」的命题截断。元数合取项 `ha` 是对 `ω` 的隶属；其语义表示在命题截断下给出自然数 `k`，并给出把元数位置认作 `# k` 的等式。由于最终结果本身也是一个命题截断类型，`rec₁` 可以在构造该结果时使用这个见证。
<!--ja-->
`NameAt` の逆方向の読みが返すのは、名前とその四つのデータの等式の命題的切り詰めだけである。アリティの連言 `ha` は `ω` への所属であり、その意味論的な表示は、命題的切り詰めのもとで自然数 `k` と、アリティのスロットを `# k` と同定する等式を与える。最終結果も命題的に切り詰められた型なので、`rec₁` はその結果を構成する範囲でこの証人を使える。
<!--/-->

```agda
    NameAt-read : ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩ → ∥ Σ[ t ∶ Name ] Data t ∥₁
    NameAt-read (hf , (ha , (he , hd))) =
      rec₁ squash₁ atArity ha
      where
      atCode : (k : ℕ) (qa : fst (lookup a γ) ≡ # k)
```

<!--en-->
Once `k` and the arity equation `qa` are fixed, `codeFree-out` reads the
freeness conjunct. It yields, still under propositional truncation, a formula
`χ : Formula ⊥* (suc k)` and an equation `qs` from the skeleton slot to its
limit-stage code. Inside this branch, `atCode` assembles the name and returns
its data: `qs` is the first equation and `qa` is the second.
<!--zh-->
固定 `k` 与元数等式 `qa` 后，`codeFree-out` 读取无常元合取项。它仍在命题截断下给出公式 `χ : Formula ⊥* (suc k)`，以及从骨架位置到该公式极限层码的等式 `qs`。在这个分支内，`atCode` 装配名字及其数据，其中 `qs` 是第一条等式，`qa` 是第二条。
<!--ja-->
`k` とアリティの等式 `qa` を固定すると、`codeFree-out` が定数を含まないという連言を読む。そこからは、なお命題的切り詰めのもとで、論理式 `χ : Formula ⊥* (suc k)` と、骨格のスロットからその極限段階での符号への等式 `qs` が得られる。この分岐の中で `atCode` が名前とそのデータを組み立て、`qs` が第一の等式、`qa` が第二の等式になる。
<!--/-->

```agda
             → Σ[ χ ∶ Formula (⊥* {ℓ}) (suc k) ]
                 (fst (lookup s γ) ≡ fst (limitCode χ))
             → Σ[ t ∶ Name ] Data t
      atCode k qa (χ , qs) = t , (qs , (qa , (qe , qd)))
        where
```

<!--en-->
The parameter component is recovered directly once the arity is known.
`paramSeq-out` reads `he` using `qa` and the carrier equation `qB`, producing a
vector of length `k` in `⟪ A ⟫`; together with `k` and `χ`, this vector defines
the name `t`. This recovery is untruncated at the level of the vector, although
the whole construction remains inside the truncations introduced by the arity
and formula readings.
<!--zh-->
元数确定后，参数分量可以直接恢复。`paramSeq-out` 以 `qa` 与载体等式 `qB` 读取 `he`，得到 `⟪ A ⟫` 中长度为 `k` 的向量；该向量与 `k`、`χ` 一起定义名字 `t`。向量层面的恢复不带命题截断，但整个构造仍处于元数读式与公式读式引入的截断之内。
<!--ja-->
アリティが定まると、パラメータ成分は直接復元できる。`paramSeq-out` は `qa` と台の等式 `qB` を用いて `he` を読み、`⟪ A ⟫` に値を取る長さ `k` のベクトルを得る。このベクトルを `k` と `χ` に組み合わせて名前 `t` を定義する。ベクトル自体の復元には命題的切り詰めがないが、構成全体はアリティと論理式の読みによる切り詰めの内側にある。
<!--/-->

```agda
        t : Name
        t = k , (χ , paramSeq-out e a B γ k qa (cong fst qB) he)
```

<!--en-->
The recovered vector must also satisfy the environment equation recorded in
`Data t`. The companion lemma `paramSeq-graph` states that the original
environment slot is exactly the encoded graph `env (pfam t)` of this vector.
This path is the third data equation `qe`.
<!--zh-->
恢复出的向量还必须满足 `Data t` 所记录的环境等式。配套引理 `paramSeq-graph` 断言，原环境位置恰等于该向量的编码图 `env (pfam t)`。这条路径就是第三条数据等式 `qe`。
<!--ja-->
復元されたベクトルは、`Data t` に記録される環境の等式も満たさなければならない。対応する補題 `paramSeq-graph` は、もとの環境のスロットがこのベクトルの符号化されたグラフ `env (pfam t)` に等しいことを述べる。このパスが第三のデータの等式 `qe` である。
<!--/-->

```agda
        qe : fst (lookup e γ) ≡ env (pfam t)
        qe = paramSeq-graph e a B γ k qa (cong fst qB) he
```

<!--en-->
The local module `Bt` instantiates the denotation-body readings at the recovered
name and at its first three data equations `qs`, `qa`, and `qe`. The remaining
component of `Data t` is therefore the set equality between the denotation slot
and `denote t`. It will be proved by comparing their members in both directions.
<!--zh-->
局部模块 `Bt` 在恢复出的名字及其前三条数据等式 `qs`、`qa`、`qe` 处实例化指称公式体的读式。因此，`Data t` 尚缺的分量是指称位置与 `denote t` 之间的集合等式。下面通过双向比较两者的成员来证明它。
<!--ja-->
局所モジュール `Bt` は、復元された名前と、その最初の三つのデータの等式 `qs`、`qa`、`qe` において、表示の本体の読みを具体化する。したがって `Data t` に残る成分は、表示のスロットと `denote t` の間の集合の等式である。これは両者の元を二方向に比較して証明する。
<!--/-->

```agda
        module Bt = Body t qs qa qe
```

<!--en-->
For the forward inclusion, let `y` belong to the denotation slot. Since that
slot is an element of the model, transitivity of `L` makes `y` constructible,
so it can be packaged as `z : S`. Reading the extensional conjunct `hd` outward
gives carrier membership and a propositionally truncated `DenoteOf` witness.
The target `y ∈ denote t` is a proposition, so `rec₁` may apply
`Bt.member-read` to any representative of that witness.
<!--zh-->
先证正向包含。设 `y` 属于指称位置。该位置是模型元素，所以由 `L` 的传递性可知 `y` 可构造，从而能把它包装为 `z : S`。向外读取外延合取项 `hd`，得到载体隶属以及经过命题截断的 `DenoteOf` 见证。目标 `y ∈ denote t` 是命题，因此 `rec₁` 可以对该见证的任一代表应用 `Bt.member-read`。
<!--ja-->
まず順方向の包含を示す。`y` が表示のスロットに属するとする。そのスロットはモデルの要素なので、`L` の推移性から `y` は構成可能であり、`z : S` としてまとめられる。外延的な連言 `hd` を外向きに読むと、台への所属と、命題的に切り詰められた `DenoteOf` の証人が得られる。目標 `y ∈ denote t` は命題なので、`rec₁` によってその証人の各代表へ `Bt.member-read` を適用できる。
<!--/-->

```agda
        fwd : (y : V ℓ) → ⟨ y ∈ fst (lookup d γ) ⟩ → ⟨ y ∈ denote t ⟩
        fwd y hy = rec₁ (snd (y ∈ denote t))
          (Bt.member-read z (body .fst)) (body .snd)
          where
          z : S
```

<!--en-->
The value `body` is obtained in two semantic steps. First `extAt-out` turns
membership in the denotation slot into satisfaction of `DenoteBody`; then
`DenoteBody-out` exposes its carrier conjunct and the four existential witnesses
collected in `DenoteOf`. Those witnesses remain propositionally truncated, as
required by the semantics of the existential quantifiers, and are consumed only
inside the proposition-valued membership proof above.
<!--zh-->
`body` 经过两步语义读取而得。首先，`extAt-out` 把对指称位置的隶属变成对 `DenoteBody` 的满足；随后，`DenoteBody-out` 读出其中的载体合取项，以及汇集在 `DenoteOf` 中的四个存在见证。按照存在量词的语义，这些见证仍处于命题截断之下，并且只在上面的命题值隶属证明内部使用。
<!--ja-->
`body` は二段階の意味論的な読みから得られる。まず `extAt-out` が表示のスロットへの所属を `DenoteBody` の充足に変え、次に `DenoteBody-out` がその台についての連言と、`DenoteOf` にまとめられた四つの存在証人を取り出す。存在量化の意味論に従って、これらの証人は命題的に切り詰められたままであり、上の命題値をもつ所属の証明の中だけで使われる。
<!--/-->

```agda
          z = y , isL-trans hy (snd (lookup d γ))
          body : ⟨ fst z ∈ fst (lookup B γ) ⟩ × ∥ DenoteOf B C s e γ z ∥₁
          body = DenoteBody-out B C s e γ z
                   (extAt-out d (DenoteBody B C s e) γ hd z hy)
```

<!--en-->
For the reverse inclusion, assume `y ∈ denote t`. The proof will first regard
`y` as an element `z : S`, then use `Bt.member-fill` to construct the denotation
body at `z`. The introduction lemmas `DenoteBody-in` and `extAt-in` rebuild the
body satisfaction and finally membership in the denotation slot.
<!--zh-->
反向包含从 `y ∈ denote t` 出发。证明先把 `y` 看作元素 `z : S`，再用 `Bt.member-fill` 构造 `z` 处的指称公式体。引入引理 `DenoteBody-in` 与 `extAt-in` 依次重建公式体的满足，最后得到对指称位置的隶属。
<!--ja-->
逆方向の包含では `y ∈ denote t` を仮定する。証明はまず `y` を要素 `z : S` とみなし、次に `Bt.member-fill` を用いて `z` における表示の本体を構成する。導入補題 `DenoteBody-in` と `extAt-in` が、本体の充足と表示のスロットへの所属を順に組み立て直す。
<!--/-->

```agda
        bwd : (y : V ℓ) → ⟨ y ∈ denote t ⟩ → ⟨ y ∈ fst (lookup d γ) ⟩
        bwd y hy = extAt-in d (DenoteBody B C s e) γ hd z
          (DenoteBody-in B C s e γ z (body .fst) (body .snd))
          where
          z : S
```

<!--en-->
The constructibility proof for `z` comes from two containments already known:
`denoteMem` puts every member of `denote t` in `A`, and `pA` says that `A` is
constructible. With this `z`, `Bt.member-fill` produces carrier membership and
an untruncated `DenoteOf` package. Hence the reverse inclusion does not need to
eliminate any propositional truncation.
<!--zh-->
`z` 的可构造性来自两项已有事实：`denoteMem` 把 `denote t` 的每个成员放入 `A`，而 `pA` 说明 `A` 可构造。对于这个 `z`，`Bt.member-fill` 给出载体隶属和一组未截断的 `DenoteOf` 数据。因此，反向包含不需要消去任何命题截断。
<!--ja-->
`z` の構成可能性は、すでに分かっている二つの包含関係から得られる。`denoteMem` は `denote t` の各要素を `A` に入れ、`pA` は `A` が構成可能であることを述べる。この `z` に対して、`Bt.member-fill` は台への所属と、切り詰められていない `DenoteOf` の証人の組を与える。したがって逆方向の包含では命題的切り詰めを除去する必要がない。
<!--/-->

```agda
          z = y , isL-trans (denoteMem t y hy) pA
          body : ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z
          body = Bt.member-fill z hy
```

<!--en-->
The functions `fwd y` and `bwd y` give the two implications between the
membership propositions for every set `y`. Since both sides are propositions,
`⇔toPath` turns these implications into an equality of truth values.
Extensionality for `V` then turns the pointwise membership equality into
`fst (lookup d γ) ≡ denote t`, the fourth equation `qd`.
<!--zh-->
对于每个集合 `y`，函数 `fwd y` 与 `bwd y` 给出两个隶属命题之间的双向蕴涵。由于两边都是命题，`⇔toPath` 把这对蕴涵变成真值的相等。`V` 的外延性再把逐点的隶属相等变成 `fst (lookup d γ) ≡ denote t`，即第四条等式 `qd`。
<!--ja-->
各集合 `y` に対して、関数 `fwd y` と `bwd y` は二つの所属命題の間の両方向の含意を与える。両辺は命題なので、`⇔toPath` はこの二つの含意を真理値の等式に変える。さらに `V` の外延性が、点ごとの所属の等式を `fst (lookup d γ) ≡ denote t`、すなわち第四の等式 `qd` に変える。
<!--/-->

```agda
        qd : fst (lookup d γ) ≡ denote t
        qd = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
```

<!--en-->
The branch `atArity` combines the two truncations without
selecting global witnesses. Its input presents the arity as a lifted natural
number; reversing `qk` gives the equation expected by `atCode`. Then
`codeFree-out` supplies the formula and code equation under propositional
truncation, and `map₁` applies `atCode` within that truncation. The result is
merely a name satisfying all four data equations, exactly the codomain of
`NameAt-read`.
<!--zh-->
分支 `atArity` 在不选择全局见证的前提下处理两层截断。它的输入把元数表示为一个提升后的自然数；反转 `qk` 后便得到 `atCode` 所需的等式。随后，`codeFree-out` 在命题截断下给出公式及其码等式，`map₁` 则在该截断内部应用 `atCode`。所得结论仅仅断言存在一个满足全部四条数据等式的名字，这正是 `NameAt-read` 的余域。
<!--ja-->
分岐 `atArity` は、大域的な証人を選ぶことなく二つの切り詰めを処理する。その入力はアリティを持ち上げられた自然数として表し、`qk` を逆向きにすると `atCode` が要求する等式になる。続いて `codeFree-out` が命題的切り詰めのもとで論理式と符号の等式を与え、`map₁` がその切り詰めの内側で `atCode` を適用する。結果は、四つのデータの等式をすべて満たす名前が存在するという命題的に切り詰められた主張であり、ちょうど `NameAt-read` の終域である。
<!--/-->

```agda
      atArity : Σ[ lk ∶ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower lk) ≡ fst (lookup a γ))
              → ∥ Σ[ t ∶ Name ] Data t ∥₁
      atArity (lk , qk) = map₁ (atCode (lower lk) (sym qk))
        (codeFree-out C₀ s a γ (lower lk) q₀ (sym qk) hf)
```
</div>
</details>

<!--en-->
## Least, described and meant
<!--zh-->
## 最小，描述出来与所指
<!--ja-->
## 最小性の記述と意味
<!--/-->

<!--en-->
The least-name formula quantifies over the three pieces that describe a
competing name. The first packaged element, `codeEl t`, places the formula code
of `t` in the model: `codeOf t` belongs to the limit stage `Lset ω`, and that
stage is constructible, so transitivity of `L` proves the code constructible.
The opaque definition exposes only the underlying-set equation `codeEl-fst`,
which is all later satisfaction arguments need when instantiating the universal
clause at a particular competitor.
<!--zh-->
最小名字公式量化一个竞争名字的三项描述数据。第一项包装元素 `codeEl t` 把名字 `t` 的公式码放入模型：`codeOf t` 属于极限层 `Lset ω`，而该层可构造，所以由 `L` 的传递性可知这个码也可构造。不透明定义只暴露底集等式 `codeEl-fst`；以后在某个具体竞争者处实例化全称子句时，满足关系的证明只需要这条等式。
<!--ja-->
最小の名前の論理式は、競合する名前を記述する三つのデータを量化する。最初にまとめられる要素 `codeEl t` は、名前 `t` の論理式符号をモデルに入れる。`codeOf t` は極限段階 `Lset ω` に属し、その段階は構成可能なので、`L` の推移性から符号自身も構成可能である。不透明な定義が公開するのは台集合の等式 `codeEl-fst` だけである。後で特定の競合相手について全称節を具体化する際、充足の証明が必要とするのはこの等式だけである。
<!--/-->

```agda
  opaque
    codeEl : Name → S
    codeEl t = fst (codeOf t)
             , isL-trans (snd (codeOf t)) (snd (LsetS ω ω-ord))
```

<!--en-->
The element `codeEl t` carries the formula code of a name into the model. Its
first projection is definitionally the underlying set of `codeOf t`, so the
equation needed when the universal clause is instantiated is reflexivity. The
constructibility proof stored in the second projection does not alter that
code.
<!--zh-->
元素 `codeEl t` 把名字的公式码带入模型。它的第一投影依定义就是`codeOf t` 的底层集合，因此实例化全称子句时所需的等式由自反性给出。第二投影中保存的可构造性证明不会改变这个码。
<!--ja-->
要素 `codeEl t` は名前の論理式の符号をモデルへ持ち込む。その第一射影は定義上 `codeOf t` の基礎集合そのものなので、全称節の具体化に必要な等式は反射律で得られる。第二射影に収められた構成可能性の証明は、この符号を変えない。
<!--/-->

```agda
    codeEl-fst : (t : Name) → fst (codeEl t) ≡ fst (codeOf t)
    codeEl-fst t = refl
```

<!--en-->
The parameter data of a name are represented by a second model element.
For `t`, the family `i ↦ lookup i (params t)` selects the carrier element at
each of its `arity t` positions, and `envS Aʟ` turns that family into its coded
environment graph. Thus `envEl t` has exactly the form expected by the
environment slot of `NameAt`.
<!--zh-->
名字的参数资料由第二个模型元素表示。对 `t` 而言，族`i ↦ lookup i (params t)` 在它的 `arity t` 个位置逐一选出载体元素，`envS Aʟ` 再把这个族变成编码后的环境图。因此，`envEl t` 恰具有 `NameAt`的环境槽所要求的形式。
<!--ja-->
名前のパラメータデータは、もう一つのモデル要素で表される。`t` に対する族`i ↦ lookup i (params t)` は `arity t` 個の各位置で台の要素を選び、`envS Aʟ` はその族を符号化された環境グラフにする。したがって `envEl t` は`NameAt` の環境スロットが要求する形を正確に備えている。
<!--/-->

```agda
    envEl : Name → S
    envEl t = envS Aʟ (λ i → lookup i (params t))
```

<!--en-->
Unfolding the environment wrapper gives the graph `env (pfam t)`, because
`pfam t` is precisely the family obtained by looking up the entries of
`params t`. Hence `envEl-fst` is again reflexivity. Together with
`codeEl-fst` and the earlier equation for `numAt`, this supplies the three
slot equations used to insert a concrete name into a quantified competitor.
<!--zh-->
展开环境包装便得到图 `env (pfam t)`，因为 `pfam t` 正是逐项读取`params t` 所得的族。因此 `envEl-fst` 同样由自反性证明。它与`codeEl-fst` 以及先前关于 `numAt` 的等式一起，给出把一条具体名字代入量化竞争者时所需的三条槽位等式。
<!--ja-->
環境の包装を展開するとグラフ `env (pfam t)` が得られる。`pfam t` は`params t` の成分を順に読み出して得る族そのものだからである。したがって`envEl-fst` も反射律で証明される。これは `codeEl-fst` および先に得た`numAt` の等式と合わせて、具体的な名前を量化された競合名へ代入するための三つのスロット等式を与える。
<!--/-->

```agda
    envEl-fst : (t : Name) → fst (envEl t) ≡ env (pfam t)
    envEl-fst t = refl
```

<!--en-->
## The least described name is the least name
<!--zh-->
## 被描述的最小名字就是最小的名字
<!--ja-->
## 記述された最小の名前は最小の名前である
<!--/-->

<!--en-->
Two strict well-orders enter the name comparison. The notation `_≺ˡ_`
denotes `limitOrder` on formula codes, while `_≺ₚ_` denotes the given order
`w` on parameters from the carrier. In `_≺ₙ_`, codes are compared first,
arities second, and parameter vectors third. Only the first and third keys
need relation sets in the object language; numeral membership expresses the
arity comparison.
<!--zh-->
名字比较使用两个严格良序。记号 `_≺ˡ_` 表示公式码上的 `limitOrder`，`_≺ₚ_` 表示载体参数上给定的序 `w`。在 `_≺ₙ_` 中，先比较码，再比较元数，最后比较参数向量。只有第一键和第三键需要对象语言中的关系集；元数比较由数码隶属表达。
<!--ja-->
名前比較には二つの狭義整列順序が入る。記法 `_≺ˡ_` は論理式の符号上の`limitOrder` を表し、`_≺ₚ_` は台のパラメータ上に与えられた順序 `w` を表す。`_≺ₙ_` では符号、アリティ、パラメータベクトルの順に比較する。対象言語で関係集合を必要とするのは第一と第三のキーだけであり、アリティの比較は数項の所属で表される。
<!--/-->

```agda
  open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )
  open SWO w using () renaming ( _<∙_ to _≺ₚ_ )
```

<!--en-->
The sets `Rs` and `Ps` represent these two orders inside the model. For
limits `u,v`, `Rrep` reads membership of the ordered pair in `Rs` as
`u ≺ˡ v`, and `Rfill` proves that membership from the comparison. The laws
`Prep` and `Pfill` give the analogous two directions for carrier elements and
`Ps`. These four representation laws are hypotheses of the adequacy result.
<!--zh-->
集合 `Rs` 与 `Ps` 在模型内部表示这两个序。对极限层元素 `u,v`，`Rrep`把有序对属于 `Rs` 读成 `u ≺ˡ v`，`Rfill` 则从该比较证明相应隶属。`Prep` 与 `Pfill` 对载体元素和 `Ps` 给出同样的两个方向。这四条表示律是充分性结果的假设。
<!--ja-->
集合 `Rs` と `Ps` は、この二つの順序をモデル内部で表す。極限段階の要素`u,v` に対し、`Rrep` は順序対の `Rs` への所属を `u ≺ˡ v` と読み、`Rfill` はその比較から所属を証明する。`Prep` と `Pfill` は台の要素と`Ps` について同じ二方向を与える。この四つの表現法則が妥当性結果の仮定である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Least (Rs Ps : S)
               (Rrep : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩ → u ≺ˡ v)
               (Rfill : (u v : Limit) → u ≺ˡ v → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩)
               (Prep : (u v : ⟪ A ⟫) → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩ → u ≺ₚ v)
               (Pfill : (u v : ⟪ A ⟫) → u ≺ₚ v → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩)
               where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The private module `K` specializes the three-key comparison adequacy to
`Rs`, `Ps`, and their representation laws. Its `order-in` turns a proof of
the meta-level name comparison into satisfaction of `_≺At_`; its `order-out`
recovers the comparison under propositional truncation. The arguments below
supply the code, numeral, and environment equations for the particular names
being compared.
<!--zh-->
私有模块 `K` 把三键比较的充分性专门化到 `Rs`、`Ps` 及其表示律。它的 `order-in` 把元层名字比较的证明转成 `_≺At_` 的满足，`order-out`则在命题截断之下恢复该比较。下文会为所比较的具体名字提供码、数码和环境等式。
<!--ja-->
非公開モジュール `K` は、三つのキーによる比較の妥当性を `Rs`、`Ps` とそれらの表現法則に特殊化する。`order-in` はメタ言語の名前比較の証明を`_≺At_` の充足へ変え、`order-out` は命題的切り詰めのもとで比較を回復する。以下では、比較する具体的な名前について符号、数項、環境の等式を与える。
<!--/-->

```agda
    private module K = Keys Rs Ps Rrep Rfill Prep Pfill
```

<!--en-->
The module `Min` fixes the nine positions used by a least-name formula:
the two relations `R,P`, the carrier `B`, the code sets `C,C₀`, the current
name's code, arity, and environment `s,a,e`, and its denotation `d`. The
equations `qR` and `qP` identify the underlying relation sets, while `qB` is
an equality of model elements because later formulas depend on the carrier.
The equation `qC` identifies the underlying set of the carrier's code set.
<!--zh-->
模块 `Min` 固定最小名字公式使用的九个位置：两个关系 `R,P`、载体 `B`、两个码集 `C,C₀`、当前名字的码、元数与环境 `s,a,e`，以及它的指称 `d`。等式 `qR` 与 `qP` 认同关系的底层集合；`qB` 则是模型元素的等式，因为后续公式依赖于载体。等式 `qC` 认同载体上的码集之底层集合。
<!--ja-->
モジュール `Min` は最小名の論理式で使う九つの位置を固定する。二つの関係`R,P`、台 `B`、二つの符号集合 `C,C₀`、現在の名前の符号、アリティ、環境`s,a,e`、そしてその指示対象 `d` である。等式 `qR` と `qP` は関係の基礎集合を同一視する。後の論理式は台に依存するため、`qB` はモデル要素そのものの等式である。`qC` は台に対する符号集合の基礎集合を同一視する。
<!--/-->

```agda
    module Min {n : ℕ} (R P B C C₀ s a e d : Fin n) (γ : S ^ n)
               (qR : fst (lookup R γ) ≡ fst Rs)
               (qP : fst (lookup P γ) ≡ fst Ps)
               (qB : lookup B γ ≡ Aʟ)
               (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
```

<!--en-->
The remaining equation `q₀` identifies `C₀` with the underlying set of
codes over the empty alphabet. With `qB`, `qC`, and `q₀` fixed, the private
module `N` supplies the already proved fill and read principles for `NameAt`
at exactly the slots used here. Least-name adequacy can therefore separate the
claim that the current data form a name from the additional minimality claim.
<!--zh-->
余下的等式 `q₀` 把 `C₀` 与空字母表上的码集之底层集合认同。固定 `qB`、`qC` 与 `q₀` 后，私有模块 `N` 在这里使用的各槽位上提供已经证明的 `NameAt`装填与读取原则。因此，最小名字的充分性可以把「当前资料构成一条名字」与附加的最小性断言分开处理。
<!--ja-->
残る等式 `q₀` は、`C₀` を空のアルファベット上の符号集合の基礎集合と同一視する。`qB`、`qC`、`q₀` を固定すると、非公開モジュール `N` はここで使う各スロットにおける `NameAt` の既証明の充填原理と読み取り原理を与える。そこで最小名の妥当性では、現在のデータが名前をなすという主張と、追加の最小性を分けて扱える。
<!--/-->

```agda
               (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      private module N = Named B C C₀ s a e d γ qB qC q₀
```

<!--en-->
For a name `t`, `IsMin t` states that no earlier name denotes the set in
slot `d`. Given any competitor `t'`, an equality identifying that slot with
`denote t'` and a proof `t' ≺ₙ t` must produce a contradiction. Thus only
names of the same displayed set are competitors, and `earlier` refers to the
full lexicographic order on names.
<!--zh-->
对名字 `t`，`IsMin t` 断言没有更早的名字指称槽 `d` 中的集合。给定任意竞争者 `t'`，若有等式把该槽认作 `denote t'`，并有证明 `t' ≺ₙ t`，就必须导出矛盾。因此，只有指称同一给定集合的名字才是竞争者，而「更早」使用名字上的完整字典序。
<!--ja-->
名前 `t` に対し、`IsMin t` は、スロット `d` の集合を指示するより早い名前がないことを述べる。任意の競合名 `t'` について、そのスロットを `denote t'` と同一視する等式と `t' ≺ₙ t` の証明から矛盾を導かなければならない。したがって競合名となるのは同じ集合を指示する名前だけであり、「より早い」は名前の完全な辞書式順序を意味する。
<!--/-->

```agda
      IsMin : Name → Type (ℓ-suc ℓ)
      IsMin t = (t' : Name) → fst (lookup d γ) ≡ denote t'
              → t' ≺ₙ t → ⊥₀
```

<!--en-->
The predicate `Least t` pairs `N.Data t` with `IsMin t`. Its first component
is the four-equation record identifying the code, arity numeral, parameter
environment, and denotation slots with the data of `t`. Its second component
rules out every smaller name of that same denotation. This matches the two
conjuncts of `LeastNameAt`: naming and the universal minimality condition.
<!--zh-->
谓词 `Least t` 把 `N.Data t` 与 `IsMin t` 配成一对。第一分量是四等式记录，把码、元数数码、参数环境和指称槽与 `t` 的资料认同；第二分量排除同一指称的每个更小名字。这正对应 `LeastNameAt` 的两个合取项：命名条件与全称最小性条件。
<!--ja-->
述語 `Least t` は `N.Data t` と `IsMin t` を対にする。第一成分は、符号、アリティの数項、パラメータ環境、指示対象の各スロットを `t` のデータと同一視する四つの等式の記録である。第二成分は、同じ指示対象をもつより小さい名前をすべて排除する。これは `LeastNameAt` の二つの連言、すなわち命名条件と全称的な最小性条件に対応する。
<!--/-->

```agda
      Least : Name → Type (ℓ-suc ℓ)
      Least t = N.Data t × IsMin t
```

<!--en-->
To fill `LeastNameAt`, `N.NameAt-fill` first establishes its naming
conjunct from the concrete name `t` and the record `dt`. The remaining
conjunct is a function implementing the three nested universal quantifiers.
For arbitrary sets `s'`, `a'`, and `e'`, it assumes both that they describe a
competitor naming the same `d` and that this competitor precedes the current
name, and it must derive contradiction.
<!--zh-->
为装填 `LeastNameAt`，`N.NameAt-fill` 先从具体名字 `t` 与记录 `dt` 证明其命名合取项。余下的合取项是实现三层全称量词的函数。对任意集合 `s'`、`a'` 与`e'`，它假设三者描述一个指称同一 `d` 的竞争者，并假设该竞争者先于当前名字，然后必须导出矛盾。
<!--ja-->
`LeastNameAt` を充填するため、まず `N.NameAt-fill` が具体的な名前 `t` と記録 `dt` から命名の連言を証明する。残る連言は三重の全称量化を実現する関数である。任意の集合 `s'`、`a'`、`e'` について、それらが同じ `d` を指示する競合名を記述し、さらにその競合名が現在の名前に先立つと仮定して、矛盾を導く。
<!--/-->

```agda
      LeastAt-fill : (t : Name) → Least t
                   → ⟨ γ ⊨ LeastNameAt R P B C C₀ s a e d ⟩
      LeastAt-fill t (dt , mt) = N.NameAt-fill t dt , univ
        where
        univ : (s' a' e' : S)
```

<!--en-->
After the three competitor data are added, the environment is
`e' ∷ a' ∷ s' ∷ γ`; hence their slots are zero, one, and two, while every
old slot is shifted by `sh3`. The first premise is satisfaction of `NameAt`
for the competitor with the shared denotation `sh3 d`. The second is
satisfaction of `_≺At_` from that competitor to the shifted current triple.
The result is `⊥*` at level `ℓ-suc ℓ`, the form of contradiction required
by the formula semantics.
<!--zh-->
加入竞争者的三项资料后，环境是 `e' ∷ a' ∷ s' ∷ γ`；因此三项分别位于零、一、二号槽，原有槽位都经 `sh3` 移位。第一个前提是竞争者的 `NameAt` 满足，并共享指称槽 `sh3 d`；第二个前提是从该竞争者到移位后当前三元组的 `_≺At_`满足。结果为层级 `ℓ-suc ℓ` 上的 `⊥*`，即公式语义所需的矛盾。
<!--ja-->
競合名の三つのデータを加えた環境は `e' ∷ a' ∷ s' ∷ γ` である。したがって各データは零、一、二番のスロットに入り、もとの各スロットは `sh3` で移動する。第一の前提は共有する指示対象 `sh3 d` に対する競合名の `NameAt` の充足である。第二の前提は、その競合名から移動後の現在の三つ組への `_≺At_` の充足である。結果はレベル `ℓ-suc ℓ` の `⊥*` であり、論理式の意味論が要求する矛盾である。
<!--/-->

```agda
             → ⟨ (e' ∷ a' ∷ s' ∷ γ) ⊨ NameAt (sh3 B) (sh3 C) (sh3 C₀)
                   (suc (suc zero)) (suc zero) zero (sh3 d) ⟩
             → ⟨ (e' ∷ a' ∷ s' ∷ γ) ⊨ ≺At (sh3 R) (sh3 P)
                   (suc (suc zero)) (suc zero) zero (sh3 s) (sh3 a) (sh3 e) ⟩
             → Lift {j = ℓ-suc ℓ} ⊥₀
```

<!--en-->
The proof first applies `Named.NameAt-read` to the competitor's naming
satisfaction. This yields, under propositional truncation, a name `t'` and
the four equations in its `Named.Data` record. Because the required result is
contradiction, a proposition, `rec₁` may eliminate that propositional
truncation. No competitor is selected or retained beyond this proof of
impossibility.
<!--zh-->
证明先把 `Named.NameAt-read` 施于竞争者的命名满足。所得结果是在命题截断之下的一条名字 `t'` 及其 `Named.Data` 记录中的四条等式。由于所需结果是作为命题的矛盾，`rec₁` 可以消去该命题截断。这里没有选出或保留竞争者，恢复出的名字只在这次不可能性证明中使用。
<!--ja-->
証明はまず、競合名の命名の充足に `Named.NameAt-read` を適用する。その結果は命題的切り詰めのもとにある名前 `t'` と、その `Named.Data` 記録の四つの等式である。求める結果は命題である矛盾なので、`rec₁` によってこの命題的切り詰めを除去できる。競合名を選択して保持するわけではなく、回復した名前はこの不可能性の証明の内部だけで使われる。
<!--/-->

```agda
        univ s' a' e' hn hlt = lift (rec₁ isProp⊥ step
          (Named.NameAt-read (sh3 B) (sh3 C) (sh3 C₀) (suc (suc zero))
             (suc zero) zero (sh3 d) (e' ∷ a' ∷ s' ∷ γ) qB qC q₀ hn))
          where
          step : Σ[ t' ∶ Name ] Named.Data (sh3 B) (sh3 C) (sh3 C₀)
```

<!--en-->
For a recovered competitor, the four data equations are named `qs'`, `qa'`,
`qe'`, and `qd'`. The last equation says that the shared denotation slot is
`denote t'`, so `mt t' qd'` is ready to refute any proof that `t' ≺ₙ t`.
That comparison is itself obtained under propositional truncation, and the
second `rec₁` may eliminate it because its target is again contradiction.
<!--zh-->
对恢复出的竞争者，四条资料等式依次命名为 `qs'`、`qa'`、`qe'` 与 `qd'`。最后一条说明共享的指称槽是 `denote t'`，所以 `mt t' qd'` 已可反驳任何`t' ≺ₙ t` 的证明。该比较本身也在命题截断之下取得；由于目标仍是矛盾，第二次`rec₁` 可以消去这个命题截断。
<!--ja-->
回復した競合名について、四つのデータ等式を `qs'`、`qa'`、`qe'`、`qd'`と名付ける。最後の等式は共有する指示対象スロットが `denote t'` であると述べるので、`mt t' qd'` は `t' ≺ₙ t` の証明を反駁できる。その比較自体も命題的切り詰めのもとで得られるが、目標は再び矛盾なので、二度目の `rec₁` による除去が許される。
<!--/-->

```agda
                   (suc (suc zero)) (suc zero) zero (sh3 d)
                   (e' ∷ a' ∷ s' ∷ γ) qB qC q₀ t'
               → ⊥₀
          step (t' , (qs' , (qa' , (qe' , qd')))) =
            rec₁ isProp⊥ (mt t' qd')
```

<!--en-->
The call to `K.order-out` supplies the truncated comparison. It uses the
relation equations `qR,qP`, the recovered competitor's code, numeral, and
environment equations, the corresponding three equations from `dt` for the
current name, and the assumed satisfaction `hlt`. Its result is
`∥ t' ≺ₙ t ∥₁`; eliminating it into `mt t' qd'` completes the universal
minimality clause.
<!--zh-->
`K.order-out` 的调用给出被截断的比较。它使用关系等式 `qR,qP`、恢复出的竞争者之码、数码与环境等式、`dt` 中当前名字对应的三条等式，以及所设的满足 `hlt`。其结果是 `∥ t' ≺ₙ t ∥₁`；把它消去到 `mt t' qd'` 所给的矛盾，便完成全称最小性子句。
<!--ja-->
`K.order-out` の呼び出しが切り詰められた比較を与える。そこでは関係の等式`qR,qP`、回復した競合名の符号、数項、環境の等式、`dt` にある現在の名前の対応する三つの等式、そして仮定した充足 `hlt` を使う。結果は`∥ t' ≺ₙ t ∥₁` である。これを `mt t' qd'` が与える矛盾へ除去すると、全称的な最小性の節が完成する。
<!--/-->

```agda
              (K.order-out (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
                 (sh3 s) (sh3 a) (sh3 e) (e' ∷ a' ∷ s' ∷ γ) t' t
                 qR qP qs' (dt .fst) qa' (dt .snd .fst)
                 qe' (dt .snd .snd .fst) hlt)
```

<!--en-->
Conversely, satisfaction of `LeastNameAt` splits into naming evidence `hn`
and the universal clause `hu`. Reading `hn` gives
`∥ Σ[ t ∶ Name ] N.Data t ∥₁`. The map shown here keeps that outer
propositional truncation and, for each recovered `t` and `dt`, adds a proof of
`IsMin t`. Consequently `LeastAt-read` proves only the propositionally
truncated existence of a least name.
<!--zh-->
反过来，`LeastNameAt` 的满足分成命名证据 `hn` 与全称子句 `hu`。读取 `hn`得到 `∥ Σ[ t ∶ Name ] N.Data t ∥₁`。这里的映射保留外层命题截断，并为每个恢复出的 `t` 与 `dt` 补上 `IsMin t` 的证明。因此，`LeastAt-read` 只证明最小名字的命题截断存在。
<!--ja-->
逆に、`LeastNameAt` の充足は命名の証拠 `hn` と全称節 `hu` に分かれる。`hn` を読むと `∥ Σ[ t ∶ Name ] N.Data t ∥₁` が得られる。ここでの写像は外側の命題的切り詰めを保ち、回復した各 `t` と `dt` に `IsMin t` の証明を加える。したがって `LeastAt-read` が証明するのは、最小名の命題的に切り詰められた存在だけである。
<!--/-->

```agda
      LeastAt-read : ⟨ γ ⊨ LeastNameAt R P B C C₀ s a e d ⟩
                   → ∥ Σ[ t ∶ Name ] Least t ∥₁
      LeastAt-read (hn , hu) = map₁ step (N.NameAt-read hn)
        where
        step : Σ[ t ∶ Name ] N.Data t → Σ[ t ∶ Name ] Least t
```

<!--en-->
To prove `IsMin t`, fix an explicit competitor `t'`, an equality `qd'`
showing that it denotes the set in slot `d`, and a comparison `lt : t' ≺ₙ t`.
The universal clause `hu` is instantiated with `codeEl t'`, the previously
defined `numAt (arity t')`, and `envEl t'`. Thus only the code and environment
wrappers are new here; the numeral wrapper is reused.
<!--zh-->
为证明 `IsMin t`，固定一个显式竞争者 `t'`、说明它指称槽 `d` 中集合的等式`qd'`，以及比较 `lt : t' ≺ₙ t`。全称子句 `hu` 在 `codeEl t'`、先前定义的`numAt (arity t')` 和 `envEl t'` 处实例化。因此，此处新定义的只有码与环境包装，数码包装是复用的。
<!--ja-->
`IsMin t` を証明するため、明示的な競合名 `t'`、それがスロット `d` の集合を指示することを示す等式 `qd'`、および比較 `lt : t' ≺ₙ t` を固定する。全称節 `hu` を `codeEl t'`、先に定義した `numAt (arity t')`、`envEl t'`で具体化する。したがって、ここで新たに定義された包装は符号と環境だけであり、数項の包装は再利用されている。
<!--/-->

```agda
        step (t , dt) = t , (dt , mt)
          where
          mt : IsMin t
          mt t' qd' lt = lower (hu (codeEl t') (numAt (arity t')) (envEl t')
            (Named.NameAt-fill (sh3 B) (sh3 C) (sh3 C₀) (suc (suc zero))
```

<!--en-->
The first premise for `hu` is built by `Named.NameAt-fill`. The equations
`codeEl-fst`, `numAt-fst`, and `envEl-fst` identify the competitor's three
data slots, while the assumed `qd'` identifies the shared denotation slot.
The second premise begins with `K.order-in`, which will translate the explicit
comparison `lt` into satisfaction of the comparison formula.
<!--zh-->
`hu` 的第一个前提由 `Named.NameAt-fill` 构造。等式 `codeEl-fst`、`numAt-fst` 与 `envEl-fst` 认同竞争者的三个资料槽，所设的 `qd'` 则认同共享的指称槽。第二个前提从 `K.order-in` 开始；它将把显式比较 `lt` 转成比较公式的满足。
<!--ja-->
`hu` の第一の前提は `Named.NameAt-fill` で構成する。等式 `codeEl-fst`、`numAt-fst`、`envEl-fst` が競合名の三つのデータスロットを同一視し、仮定`qd'` が共有する指示対象スロットを同一視する。第二の前提は `K.order-in`から始まり、明示的な比較 `lt` を比較論理式の充足へ移す。
<!--/-->

```agda
               (suc zero) zero (sh3 d)
               (envEl t' ∷ numAt (arity t') ∷ codeEl t' ∷ γ) qB qC q₀ t'
               (codeEl-fst t' , (numAt-fst (arity t')
                              , (envEl-fst t' , qd'))))
            (K.order-in (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
```

<!--en-->
The call to `K.order-in` also receives the current name's three equations
from `dt` and the relation equations `qR,qP`. It therefore proves the exact
comparison premise expected by `hu` in the extended environment. Applying
`hu` yields a lifted contradiction, and `lower` returns it at the universe
level required by `IsMin`. This lift and lowering concern universe placement;
they do not eliminate a propositional truncation.
<!--zh-->
`K.order-in` 的调用还接收 `dt` 中当前名字的三条等式以及关系等式 `qR,qP`，因而在扩张环境中证明 `hu` 所需的那条比较前提。施用 `hu` 得到被抬升的矛盾，`lower` 再把它带回 `IsMin` 所需的宇宙层级。这里的抬升与降位只处理宇宙安放，并不消去命题截断。
<!--ja-->
`K.order-in` の呼び出しには、`dt` にある現在の名前の三つの等式と関係の等式`qR,qP` も渡す。これにより、拡張された環境で `hu` が要求する比較の前提が正確に証明される。`hu` を適用すると持ち上げられた矛盾が得られ、`lower` がそれを `IsMin` の要求する宇宙レベルへ戻す。この持ち上げと引き下げは宇宙の配置に関するものであり、命題的切り詰めの除去ではない。
<!--/-->

```agda
               (sh3 s) (sh3 a) (sh3 e)
               (envEl t' ∷ numAt (arity t') ∷ codeEl t' ∷ γ) t' t
               qR qP (codeEl-fst t') (dt .fst) (numAt-fst (arity t'))
               (dt .snd .fst) (envEl-fst t') (dt .snd .snd .fst) lt))
```

<!--en-->
## One step, described and meant
<!--zh-->
## 一步，描述出来与所指
<!--ja-->
## 一つのステップの記述と意味
<!--/-->

<!--en-->
The module `Step` keeps the same two represented relations, carrier, and code
sets, and adds slots `x` and `y` for the sets to be compared. The five
equations have the same roles as in `Min`: `qR,qP` interpret the two relation
slots, `qB` identifies the carrier as a dependent model element, and `qC,q₀`
identify the two underlying code sets. This local statement concerns a
comparison of names for `x` and `y`; the later connection to a stage order is
proved outside this module.
<!--zh-->
模块 `Step` 保留同样的两个被表示关系、载体与码集，并加入被比较集合的槽 `x`与 `y`。五条等式的作用与 `Min` 中相同：`qR,qP` 解释两个关系槽，`qB` 以依值模型元素等式认同载体，`qC,q₀` 认同两个码集的底层集合。这里的局部陈述只比较`x` 与 `y` 的名字；它与层序的后续联系在本模块之外证明。
<!--ja-->
モジュール `Step` は同じ二つの表現された関係、台、符号集合を保ち、比較する集合のスロット `x` と `y` を加える。五つの等式の役割は `Min` と同じである。`qR,qP` は二つの関係スロットを解釈し、`qB` は依存するモデル要素の等式として台を同一視し、`qC,q₀` は二つの符号集合の基礎集合を同一視する。この局所的な主張は`x` と `y` の名前の比較だけを扱い、段階順序との接続はこのモジュールの外で証明される。
<!--/-->

```agda
    module Step {n : ℕ} (R P B C C₀ x y : Fin n) (γ : S ^ n)
                (qR : fst (lookup R γ) ≡ fst Rs)
                (qP : fst (lookup P γ) ≡ fst Ps)
                (qB : lookup B γ ≡ Aʟ)
                (qC : fst (lookup C γ) ≡ fst (AllCodes Aʟ))
```

<!--en-->
`LeastOf i t` is the meta-level property needed for either endpoint of a
step. Its first component says that slot `i` contains `denote t`. Its second
component says that any name `t'` whose denotation is also that slot cannot
precede `t`. Thus it asserts that `t` is a least name for the particular set
in slot `i`; it does not itself contain a satisfaction proof for any formula.
<!--zh-->
`LeastOf i t` 是步进任一端点所需的元层性质。第一分量说槽 `i` 含有`denote t`；第二分量说，任何指称也等于该槽的名字 `t'` 都不能先于 `t`。因此，它断言 `t` 是槽 `i` 中特定集合的一条最小名字；它本身不包含任何公式的满足证明。
<!--ja-->
`LeastOf i t` はステップの各端点に必要なメタ言語の性質である。第一成分はスロット`i` が `denote t` を含むことを述べる。第二成分は、指示対象が同じスロットである任意の名前 `t'` が `t` に先立つことを否定する。したがって、`t` がスロット `i` の特定の集合に対する最小名であると主張するが、それ自体は論理式の充足証明を含まない。
<!--/-->

```agda
                (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      LeastOf : Fin n → Name → Type (ℓ-suc ℓ)
      LeastOf i t = (fst (lookup i γ) ≡ denote t)
                  × ((t' : Name) → fst (lookup i γ) ≡ denote t'
                     → t' ≺ₙ t → ⊥₀)
```

<!--en-->
`StepAt-fill` starts with explicit names `t₁,t₂`, proofs that they are least
for `x,y`, and an explicit comparison `t₁ ≺ₙ t₂`. It supplies six witnesses
to `StepAt-in` in binder order: the code, arity numeral, and parameter
environment of `t₁`, followed by the corresponding three data of `t₂`.
The body then requires two least-name satisfactions and one comparison
satisfaction. No input to this filling theorem is propositionally truncated.
<!--zh-->
`StepAt-fill` 从显式名字 `t₁,t₂`、它们分别对 `x,y` 最小的证明，以及显式比较`t₁ ≺ₙ t₂` 出发。它按绑定次序向 `StepAt-in` 提供六个见证：`t₁` 的码、元数数码和参数环境，随后是 `t₂` 的对应三项资料。公式体继而要求两份最小名字满足与一份比较满足。此装填定理的输入没有处在命题截断之下。
<!--ja-->
`StepAt-fill` は明示的な名前 `t₁,t₂`、それらがそれぞれ `x,y` に対して最小であることの証明、明示的な比較 `t₁ ≺ₙ t₂` から始まる。`StepAt-in` には束縛順に六つの証人を渡す。まず `t₁` の符号、アリティの数項、パラメータ環境、続いて `t₂` の対応する三つのデータである。論理式本体には二つの最小名の充足と一つの比較の充足が必要である。この充填定理の入力は命題的に切り詰められていない。
<!--/-->

```agda
      StepAt-fill : (t₁ t₂ : Name) → LeastOf x t₁ → LeastOf y t₂ → t₁ ≺ₙ t₂
                  → ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
      StepAt-fill t₁ t₂ l₁ l₂ lt = StepAt-in R P B C C₀ x y γ
        ( codeEl t₁ , (numAt (arity t₁) , (envEl t₁
        , ( codeEl t₂ , (numAt (arity t₂) , (envEl t₂
```

<!--en-->
Existential witnesses are pushed onto the front of the environment, so the
six witnesses appear there in reverse binder order:
`envEl t₂`, its numeral and code, then `envEl t₁`, its numeral and code,
followed by `γ`. In this environment `s6a,a6a,e6a` locate the first name's
code, numeral, and environment. The proof `ln₁` applies `LeastAt-fill` with
the first name's three data equations, the denotation equation `l₁ .fst`, and
the minimality proof `l₁ .snd`.
<!--zh-->
存在见证会被压入环境前端，所以六个见证在环境中按绑定次序反向出现：先是`envEl t₂`、它的数码与码，再是 `envEl t₁`、它的数码与码，最后接原环境 `γ`。在这个环境中，`s6a,a6a,e6a` 定位第一名字的码、数码与环境。证明 `ln₁` 把第一名字的三条资料等式、指称等式 `l₁ .fst` 和最小性证明 `l₁ .snd` 交给`LeastAt-fill`。
<!--ja-->
存在証人は環境の先頭へ積まれるため、六つの証人は束縛順とは逆に現れる。`envEl t₂`、その数項と符号、次に `envEl t₁`、その数項と符号、最後にもとの環境 `γ` が続く。この環境で `s6a,a6a,e6a` は第一の名前の符号、数項、環境を指す。証明 `ln₁` は、第一の名前の三つのデータ等式、指示対象の等式`l₁ .fst`、最小性の証明 `l₁ .snd` を `LeastAt-fill` に渡す。
<!--/-->

```agda
        , ( ln₁ , (ln₂ , cmp) )))))))
        where
        ln₁ = Min.LeastAt-fill (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                s6a a6a e6a (sh6 x)
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
```

<!--en-->
The record passed to the first `LeastAt-fill` has exactly the expected two
parts. Its `N.Data` component consists of `codeEl-fst`, `numAt-fst`,
`envEl-fst`, and the equality `l₁ .fst` identifying slot `x` with the
denotation of `t₁`; its `IsMin` component is `l₁ .snd`. Thus `ln₁` proves
that the first bound triple is a least name of `x`. The analogous construction
for `t₂` and the comparison proof are the remaining components needed by
`StepAt-in`.
<!--zh-->
传给第一次 `LeastAt-fill` 的记录恰有预期的两个部分。其 `N.Data` 分量由`codeEl-fst`、`numAt-fst`、`envEl-fst` 以及把槽 `x` 与 `t₁` 的指称认同的等式 `l₁ .fst` 组成；其 `IsMin` 分量是 `l₁ .snd`。因此，`ln₁` 证明第一个被绑定三元组是 `x` 的一条最小名字。对 `t₂` 的同类构造与比较证明则给出`StepAt-in` 所需的其余分量。
<!--ja-->
最初の `LeastAt-fill` に渡す記録には、要求どおり二つの部分がある。`N.Data` 成分は `codeEl-fst`、`numAt-fst`、`envEl-fst`、およびスロット `x`を `t₁` の指示対象と同一視する等式 `l₁ .fst` からなる。`IsMin` 成分は`l₁ .snd` である。したがって `ln₁` は、最初の束縛された三つ組が `x` の最小名であることを証明する。`t₂` に対する同様の構成と比較の証明が、`StepAt-in`に必要な残りの成分を与える。
<!--/-->

```agda
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ)
                qR qP qB qC q₀ t₁
                ( (codeEl-fst t₁ , (numAt-fst (arity t₁)
                                 , (envEl-fst t₁ , l₁ .fst)))
                , l₁ .snd )
```

<!--en-->
The second least-name condition is filled by the same adequacy map as the first,
now at the slots `s6b`, `a6b`, and `e6b`.  The shared six-witness environment
identifies these slots with the code, arity numeral, and parameter environment of
`t₂`, while `sh6 y` identifies the set that `t₂` must denote.  The remaining
argument must therefore establish both that denotation and the leastness of `t₂`.
<!--zh-->
第二个最小名字条件由与第一个相同的充分性映射填充，只是这次使用槽位 `s6b`、`a6b` 与 `e6b`。共享的六见证环境把这些槽位分别认同为 `t₂` 的码、元数数码与参数环境，而 `sh6 y` 指定 `t₂` 必须指称的集合。因此，余下的实参必须同时证明这项指称与 `t₂` 的最小性。
<!--ja-->
第二の最小の名前の条件は、第一の場合と同じ妥当性の写像によって満たされる。ただし、今度使うスロットは `s6b`、`a6b`、`e6b` である。共通の六証人環境は、これらのスロットを `t₂` の符号、アリティの数項、パラメータ環境とそれぞれ同一視し、`sh6 y` は `t₂` が表示すべき集合を指定する。したがって残る引数は、その表示と `t₂` の最小性の両方を示さなければならない。
<!--/-->

```agda
        ln₂ = Min.LeastAt-fill (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                s6b a6b e6b (sh6 y)
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ)
                qR qP qB qC q₀ t₂
```

<!--en-->
The nested pair has exactly the type required by `LeastAt-fill`: the four data
equalities for `t₂`, followed by its leastness proof.  The first three equalities
come from the sealed code, numeral, and environment elements; `l₂ .fst` identifies
the denotation with the value in slot `y`; and `l₂ .snd` rules out every `t'` with
that same denotation and `t' ≺ₙ t₂`.  Thus leastness has the required direction:
no smaller competing name precedes `t₂`.
<!--zh-->
这组嵌套序对恰好具有 `LeastAt-fill` 所需的类型：先给出 `t₂` 的四条数据等式，再给出它的最小性证明。前三条等式来自封装好的码元素、数码元素与环境元素；`l₂ .fst` 把指称认同为槽位 `y` 中的值；`l₂ .snd` 则排除每个指称相同且满足 `t' ≺ₙ t₂` 的 `t'`。因此，最小性的方向是：没有更小的竞争名字先于 `t₂`。
<!--ja-->
この入れ子の対は、`LeastAt-fill` が要求する型を正確に持つ。まず `t₂` に関する四つのデータの等しさがあり、その後に最小性の証明が続く。最初の三つの等しさは、封じた符号、数項、環境の各要素から得られる。`l₂ .fst` は表示対象をスロット `y` の値と同一視し、`l₂ .snd` は、同じ集合を表示して `t' ≺ₙ t₂` を満たす任意の `t'` を排除する。したがって最小性の向きは、`t₂` に先行するより小さな競合名がない、という向きである。
<!--/-->

```agda
                ( (codeEl-fst t₂ , (numAt-fst (arity t₂)
                                 , (envEl-fst t₂ , l₂ .fst)))
                , l₂ .snd )
```

<!--en-->
The comparison condition uses only the three ordering keys of each name.  The
call to `order-in` begins with `qR` and `qP`, which interpret the two relation
slots, and then supplies the two code equalities and the two arity-numeral
equalities.  Together with the two environment equalities on the following
line, these make the eight equalities required by the call.  Denotation and
leastness are absent because `_≺ₙ_` compares names by those three keys alone.
<!--zh-->
比较条件只使用每个名字的三个排序键。对 `order-in` 的调用先取得解释两个关系槽位的 `qR` 与 `qP`，再给出两条码等式与两条元数数码等式。加上下行的两条环境等式，便是这次调用所需的八条等式。指称与最小性没有传入，因为 `_≺ₙ_` 只按这三个键比较名字。
<!--ja-->
比較条件が使うのは、各名前を順序づける三つの鍵だけである。`order-in` の呼び出しは、二つの関係スロットを解釈する `qR` と `qP` から始まり、続いて二つの符号の等しさと二つのアリティの数項の等しさを渡す。次の行にある二つの環境の等しさを合わせると、この呼び出しが要求する八つの等しさになる。`_≺ₙ_` はこの三つの鍵だけで名前を比較するので、表示と最小性は含まれない。
<!--/-->

```agda
        cmp = K.order-in (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b
                (envEl t₂ ∷ numAt (arity t₂) ∷ codeEl t₂
                 ∷ envEl t₁ ∷ numAt (arity t₁) ∷ codeEl t₁ ∷ γ) t₁ t₂
                qR qP (codeEl-fst t₁) (codeEl-fst t₂)
                (numAt-fst (arity t₁)) (numAt-fst (arity t₂))
```

<!--en-->
The two environment equalities complete the slot identifications, and the final
argument `lt` supplies the actual comparison `t₁ ≺ₙ t₂`.  Hence `cmp` is a
satisfaction proof for the object-language comparison between the two triples.
Together with `ln₁` and `ln₂`, it supplies the three conjuncts packed by
`StepAt-in`.  This filling direction starts with specified names and a specified
comparison, so it introduces the six existential witnesses directly.
<!--zh-->
两条环境等式补全槽位认同，最后的实参 `lt` 给出实际比较 `t₁ ≺ₙ t₂`。因此，`cmp` 是两个三元组之间对象语言比较公式的满足证明。它与 `ln₁`、`ln₂` 一同给出 `StepAt-in` 所装入的三个合取项。这个填充方向从指定的两个名字与一项指定的比较出发，因而可以直接引入六个存在见证。
<!--ja-->
二つの環境の等しさによってスロットの同一視がそろい、最後の引数 `lt` が実際の比較 `t₁ ≺ₙ t₂` を与える。したがって `cmp` は、二つの三つ組の間にある対象言語の比較論理式の充足証明である。これは `ln₁`、`ln₂` と合わせて、`StepAt-in` が包む三つの連言を与える。この充填の向きでは、指定された二つの名前と指定された比較から出発するため、六つの存在証人を直接導入できる。
<!--/-->

```agda
                (envEl-fst t₁) (envEl-fst t₂) lt
```

<!--en-->
The converse theorem states the exact witness boundary. From satisfaction of
`StepAt`, it returns only `∥ Σ[ t₁ ∶ Name ] Σ[ t₂ ∶ Name ] (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁`.
The outer dependent sum ranges `t₁` over all names, and for each such `t₁` the
inner sum ranges `t₂` over all names. Their payload says precisely that `t₁` is
least for the value in slot `x`, `t₂` is least for the value in slot `y`, and
`t₁ ≺ₙ t₂`. The first `rec₁` opens the truncated six-witness payload supplied
by `StepAt-out`, with this still-truncated conclusion as its target.
<!--zh-->
反向定理精确标明见证的边界。从 `StepAt` 的满足关系出发，它只返回 `∥ Σ[ t₁ ∶ Name ] Σ[ t₂ ∶ Name ] (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁`。外层依值和让 `t₁` 遍历全部名字；对每个这样的 `t₁`，内层依值和再让 `t₂` 遍历全部名字。其载荷精确断言：`t₁` 是槽 `x` 中取值的最小名字，`t₂` 是槽 `y` 中取值的最小名字，并且 `t₁ ≺ₙ t₂`。第一个 `rec₁` 打开 `StepAt-out` 给出的六见证之命题截断，而消去目标仍是这条带有命题截断的结论。
<!--ja-->
逆向きの定理は、証人を取り出せる境界を正確に示す。`StepAt` の充足から返されるのは、`∥ Σ[ t₁ ∶ Name ] Σ[ t₂ ∶ Name ] (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁` だけである。外側の依存和では `t₁` がすべての名前を動き、その各 `t₁` に対して内側の依存和では `t₂` がすべての名前を動く。中身が正確に述べるのは、`t₁` がスロット `x` の値に対する最小名であり、`t₂` がスロット `y` の値に対する最小名であり、さらに `t₁ ≺ₙ t₂` であることである。最初の `rec₁` は `StepAt-out` が与える六証人の命題的切り詰めを開くが、除去先はこの切り詰められた結論のままである。
<!--/-->

```agda
      StepAt-read : ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
                  → ∥ Σ[ t₁ ∶ Name ] Σ[ t₂ ∶ Name ]
                      (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁
      StepAt-read h = rec₁ squash₁ atSix (StepAt-out R P B C C₀ x y γ h)
        where
```

<!--en-->
`Goal` names that codomain once so that every truncation elimination has the
same target.  Because `Goal` is itself a propositional truncation, `squash₁`
proves that it is a proposition.  This is the precise reason that the outer
six-witness truncation and the two later least-name truncations may all be
eliminated while the final pair of names remains hidden by one truncation.
<!--zh-->
`Goal` 为该陪域命名，使各次截断消去具有同一个目标。由于 `Goal` 本身就是命题截断，`squash₁` 证明它是命题。这正是外层六见证截断以及后续两次最小名字截断都可以被消去的理由，同时最终的一对名字仍由一道命题截断隐藏。
<!--ja-->
`Goal` はこの余域に一度だけ名前を付け、すべての切り詰めの消去先を同じ型にする。`Goal` 自身が命題的切り詰めなので、`squash₁` はそれが命題であることを示す。外側の六証人に関する切り詰めと、後に現れる二つの最小の名前に関する切り詰めをすべて消去でき、それでも最終的な名前の対が一つの命題的切り詰めに隠れたままである理由は、正確にここにある。
<!--/-->

```agda
        Goal : Type (ℓ-suc ℓ)
        Goal = ∥ Σ[ t₁ ∶ Name ] Σ[ t₂ ∶ Name ]
                 (LeastOf x t₁ × (LeastOf y t₂ × (t₁ ≺ₙ t₂))) ∥₁
```

<!--en-->
Inside that permitted elimination, `atSix` receives an ordinary `StepOf`
witness and separates it into the triples `(s₁,k₁,p₁)` and `(s₂,k₂,p₂)`.
Because existential witnesses are added at the head of an environment, the body
is evaluated in the reverse order
`p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ`.  The first call to `LeastAt-read` therefore
uses the first triple's fixed positions `s6a`, `a6a`, and `e6a` to read a least
name for the value in slot `x`.
<!--zh-->
在这次获准的消去内部，`atSix` 取得普通的 `StepOf` 见证，并把它分成 `(s₁,k₁,p₁)` 与 `(s₂,k₂,p₂)` 两个三元组。由于存在见证逐个加入环境头部，公式体在反序环境 `p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ` 中求值。因此，第一次调用 `LeastAt-read` 时使用第一组三元数据的固定位置 `s6a`、`a6a` 与 `e6a`，读取槽位 `x` 中的值的一个最小名字。
<!--ja-->
この許された消去の内側で、`atSix` は通常の `StepOf` の証人を受け取り、それを `(s₁,k₁,p₁)` と `(s₂,k₂,p₂)` の二つの三つ組に分ける。存在証人は環境の先頭へ順に加えられるので、本体は逆順の環境 `p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ` で評価される。したがって最初の `LeastAt-read` は、第一の三つ組の固定位置 `s6a`、`a6a`、`e6a` を用いて、スロット `x` の値を表示する最小の名前を読み取る。
<!--/-->

```agda
        atSix : StepOf R P B C C₀ x y γ → Goal
        atSix (s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , hb)))))) =
          rec₁ squash₁ atFirst
            (Min.LeastAt-read (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
               s6a a6a e6a (sh6 x)
```

<!--en-->
The body proof `hb` contains three conjuncts.  Its projections name them as
`h₁`, the first triple's `LeastNameAt` satisfaction, `h₂`, the corresponding
satisfaction for the second triple, and `hc`, satisfaction of `≺At` from the
first triple to the second.  The proof first gives `h₁` to `LeastAt-read`.
The other two conjuncts are retained until both meta-level names have been
recovered, since only then can `hc` be interpreted as a comparison of those
names.
<!--zh-->
公式体证明 `hb` 含有三个合取项。各投影依次把它们命名为 `h₁`、`h₂` 与 `hc`：前两项分别是第一、第二组三元数据对 `LeastNameAt` 的满足，第三项是从第一组三元数据到第二组三元数据的 `≺At` 满足。证明先把 `h₁` 交给 `LeastAt-read`。另外两项保留到两个元语言名字都恢复以后，因为只有到那时，`hc` 才能解释为这两个名字之间的比较。
<!--ja-->
本体の証明 `hb` は三つの連言を含む。その射影を順に `h₁`、`h₂`、`hc` と名付ける。最初の二つは第一と第二の三つ組についての `LeastNameAt` の充足であり、三つ目は第一の三つ組から第二の三つ組への `≺At` の充足である。証明はまず `h₁` を `LeastAt-read` に渡す。残る二つは、メタ言語の二つの名前がともに復元されるまで保たれる。その時点で初めて、`hc` をそれらの名前の比較として解釈できるからである。
<!--/-->

```agda
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ h₁)
          where
          h₁ = hb .fst
          h₂ = hb .snd .fst
          hc = hb .snd .snd
```

<!--en-->
`atSecond` records what remains after the first least name has been read.  It
accepts a particular `t₁` with its full `Min.Least` record, then a particular
`t₂` with the analogous record, and must produce `Goal`.  Each record contains
four data equalities together with the correctly directed leastness assertion.
Thus this continuation has enough information both to recover the two
`LeastOf` facts and to interpret the still-object-language comparison `hc`.
<!--zh-->
`atSecond` 记录读出第一个最小名字后尚需完成的工作。它先取得一个特定的 `t₁` 及其完整 `Min.Least` 记录，再取得一个特定的 `t₂` 及相应记录，最后必须构造 `Goal`。每份记录都含有四条数据等式，以及方向正确的最小性断言。因此，这个后续函数既有足够信息恢复两项 `LeastOf` 事实，也能解释仍处于对象语言层面的比较 `hc`。
<!--ja-->
`atSecond` は、第一の最小の名前を読み取った後に残る仕事を表す。特定の `t₁` とその完全な `Min.Least` の記録を受け取り、続いて特定の `t₂` と同様の記録を受け取って、`Goal` を構成しなければならない。各記録には四つのデータの等しさと、正しい向きの最小性の主張が含まれる。したがって、この継続は二つの `LeastOf` の事実を復元し、まだ対象言語の側にある比較 `hc` を解釈するために十分な情報を持っている。
<!--/-->

```agda
          atSecond : (t₁ : Name)
                   → Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
                       s6a a6a e6a (sh6 x)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₁
                   → Σ[ t₂ ∶ Name ] Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C)
```

<!--en-->
Once both records are available, only a proof `lt : t₁ ≺ₙ t₂` is missing from
the final statement.  The function mapped over that comparison keeps from each
data record precisely its denotation equality, `dᵢ .snd .snd .snd`, and pairs it
with the leastness proof `mᵢ`; these are exactly the two components of
`LeastOf`.  It then joins the resulting least-name facts with `lt` and inserts
the complete pair of names into `Goal` without removing the surrounding
truncation.
<!--zh-->
两份记录就绪后，最终陈述只缺一项证明 `lt : t₁ ≺ₙ t₂`。映射到该比较之上的函数，从每份数据记录中只保留指称等式 `dᵢ .snd .snd .snd`，并将它与最小性证明 `mᵢ` 配对；这两项恰好组成 `LeastOf`。随后，它把所得的两项最小名字事实与 `lt` 合并，并把完整的名字对放入 `Goal`，全程不移除外围的命题截断。
<!--ja-->
二つの記録がそろうと、最終的な主張に足りないのは `lt : t₁ ≺ₙ t₂` の証明だけである。その比較上で写される関数は、各データの記録から表示の等しさ `dᵢ .snd .snd .snd` だけを取り、それを最小性の証明 `mᵢ` と組にする。この二つがちょうど `LeastOf` の成分である。次に、得られた二つの最小の名前に関する事実を `lt` と合わせ、外側の命題的切り詰めを取り除くことなく、名前の完全な対を `Goal` に入れる。
<!--/-->

```agda
                       (sh6 C₀) s6b a6b e6b (sh6 y)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₂
                   → Goal
          atSecond t₁ (d₁ , m₁) (t₂ , (d₂ , m₂)) =
            map₁ (λ lt → t₁ , (t₂ , ( (d₁ .snd .snd .snd , m₁)
```

<!--en-->
`order-out` now interprets `hc`.  Besides `qR` and `qP`, it receives from `d₁`
and `d₂` the code, arity-numeral, and parameter-environment equalities for the
two recovered names.  The denotation equalities are unnecessary for this
three-key comparison.  The result is only `∥ t₁ ≺ₙ t₂ ∥₁`; `map₁` transforms
each comparison inside that propositional truncation into the complete witness
required by `Goal`.
<!--zh-->
此时，`order-out` 解释 `hc`。除 `qR` 与 `qP` 外，它还从 `d₁`、`d₂` 取得两个已恢复名字各自的码等式、元数数码等式与参数环境等式。三键比较不需要指称等式。所得结果只有 `∥ t₁ ≺ₙ t₂ ∥₁`；`map₁` 把这道命题截断内的每项比较变换成 `Goal` 所需的完整见证。
<!--ja-->
ここで `order-out` が `hc` を解釈する。`qR` と `qP` に加えて、復元された二つの名前について、符号、アリティの数項、パラメータ環境の等しさを `d₁` と `d₂` から受け取る。この三鍵比較には、表示の等しさは必要ない。得られるのは `∥ t₁ ≺ₙ t₂ ∥₁` だけである。`map₁` は、その命題的切り詰めの内側にある各比較を、`Goal` が要求する完全な証人へ変換する。
<!--/-->

```agda
                                      , ( (d₂ .snd .snd .snd , m₂) , lt ))))
              (K.order-out (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b
                 (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) t₁ t₂
                 qR qP (d₁ .fst) (d₂ .fst) (d₁ .snd .fst) (d₂ .snd .fst)
                 (d₁ .snd .snd .fst) (d₂ .snd .snd .fst) hc)
```

<!--en-->
`atFirst` is the continuation for the first least-name reading.  Given its
recovered pair `(t₁,l₁)`, it applies `LeastAt-read` to `h₂` at the second
triple's slots, obtaining the second pair only under propositional truncation.
The following `rec₁` may pass that pair to `atSecond t₁ l₁` because the target
is the proposition `Goal`.  The second truncation is therefore eliminated only
while constructing the final truncated existence statement.
<!--zh-->
`atFirst` 是读取第一个最小名字时使用的后续函数。取得已恢复的 `(t₁,l₁)` 后，它在第二组三元数据的槽位处对 `h₂` 应用 `LeastAt-read`，而第二个名字及其记录仍只在命题截断下得到。随后，`rec₁` 可以把这对数据交给 `atSecond t₁ l₁`，因为消去目标是命题 `Goal`。因此，第二道截断只在构造最终的截断存在陈述时被消去。
<!--ja-->
`atFirst` は、第一の最小の名前を読み取るための継続である。復元された対 `(t₁,l₁)` を受け取ると、第二の三つ組のスロットで `h₂` に `LeastAt-read` を適用し、第二の対を命題的切り詰めの下でだけ得る。消去先が命題 `Goal` なので、続く `rec₁` はその対を `atSecond t₁ l₁` に渡せる。したがって第二の切り詰めは、最終的な切り詰められた存在命題を構成する間に限って消去される。
<!--/-->

```agda
          atFirst : Σ[ t₁ ∶ Name ] Min.Least (sh6 R) (sh6 P) (sh6 B) (sh6 C)
                      (sh6 C₀) s6a a6a e6a (sh6 x)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ t₁
                  → Goal
          atFirst (t₁ , l₁) = rec₁ squash₁ (atSecond t₁ l₁)
```

<!--en-->
The final invocation supplies the second triple's fixed slots, the same reversed
six-witness environment, and `h₂`.  It completes a chain of four truncated
interfaces: `StepAt-out`, the two calls to `LeastAt-read`, and `order-out`.
Their composition proves exactly that satisfaction of `StepAt` entails the
propositionally truncated existence of names `t₁,t₂` such that `t₁` is least for
`x`, `t₂` is least for `y`, and `t₁ ≺ₙ t₂`.  No particular pair of names is
exported outside that truncation.
<!--zh-->
最后一次调用传入第二组三元数据的固定槽位、同一个反序六见证环境以及 `h₂`。它完成了四个截断接口的复合：`StepAt-out`、两次 `LeastAt-read` 与 `order-out`。这个复合精确证明：`StepAt` 的满足关系蕴含命题截断下的名字 `t₁,t₂` 的存在性，其中 `t₁` 是 `x` 的最小名字，`t₂` 是 `y` 的最小名字，并且 `t₁ ≺ₙ t₂`。任何特定的名字对都不会被导出这道截断。
<!--ja-->
最後の呼び出しは、第二の三つ組の固定スロット、同じ逆順の六証人環境、および `h₂` を渡す。これにより、`StepAt-out`、二回の `LeastAt-read`、`order-out` という四つの切り詰められたインターフェースの合成が完成する。この合成が正確に証明するのは、`StepAt` の充足から、`t₁` が `x` の最小の名前であり、`t₂` が `y` の最小の名前であり、さらに `t₁ ≺ₙ t₂` であるような名前 `t₁,t₂` の存在が、命題的切り詰めの下で従うことである。特定の名前の対がこの切り詰めの外へ取り出されることはない。
<!--/-->

```agda
            (Min.LeastAt-read (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀)
               s6b a6b e6b (sh6 y)
               (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) qR qP qB qC q₀ h₂)
```
</div>
</details>

</div>
</details>

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
This chapter establishes both directions of the semantic correspondence for names. In the adequacy direction, a concrete name fills `NameAt` from its formula code, arity, parameter environment, and denotation; a proof that it is least among the names with that denotation fills `LeastNameAt`; and two such least names with `t₁ ≺ₙ t₂` fill `StepAt`. In the completeness direction, satisfaction recovers the same data in reverse. Consequently, the formula comparing the two least descriptions agrees with the meta-language comparison: formula codes are compared first, then arities when the codes agree, and finally parameter vectors when both earlier keys agree.

The completeness statements retain propositional truncation. Uniqueness lets the parameter graph determine its vector without truncation, but reading a whole name, a least name, or a pair of compared least names proves only that suitable witnesses exist. Every truncation is eliminated only into a proposition, and no particular name or pair of names is exported. No propositional resizing occurs here. This is exactly the boundary used when `StepAt` is connected to the host-level step order.
<!--zh-->
本章建立了名字之语义对应的两个方向。在充分性方向，一条具体名字凭其公式码、元数、参数环境与指称装填 `NameAt`；再给出它在同指称名字中最小的证明，便装填 `LeastNameAt`；两条这样的最小名字连同 `t₁ ≺ₙ t₂` 则装填 `StepAt`。在完备性方向，从满足关系反向恢复的正是这些资料。因此，比较两条最小描述的公式与元语言比较一致：先比较公式码，码相同时比较元数，前两项都相同时再比较参数向量。

这些完备性陈述保留命题截断。唯一性使参数图能够无截断地决定其向量，但读取整条名字、最小名字或一对已比较的最小名字时，只证明合适见证的存在性。每次截断消去都只以命题为目标，不会导出某条特定名字或某对特定名字；这里也没有实施命题换级。下游正是在这个边界上把 `StepAt` 接到宿主层的步序。
<!--ja-->
本章では、名前の意味論的な対応について二つの方向を確立した。妥当性の向きでは、具体的な名前の論理式符号、アリティ、パラメータ環境、指示対象から `NameAt` を充足できる。その名前が同じ指示対象をもつ名前の中で最小であることを加えれば `LeastNameAt` を充足でき、さらに二つの最小の名前と `t₁ ≺ₙ t₂` から `StepAt` を充足できる。完全性の向きでは、充足関係からこれらと同じデータを逆に復元する。したがって、二つの最小の記述を比較する論理式はメタ言語の比較と一致し、まず論理式符号を比較し、それが等しければアリティを比較し、最初の二つのキーがともに等しければパラメータベクトルを比較する。

完全性の各主張には命題的切り詰めが残る。一意性により、パラメータグラフからそのベクトルだけは切り詰めなしで定まるが、名前全体、最小の名前、または比較された最小の名前の対を読み取る結果は、適切な証人が存在することだけを述べる。切り詰めは常に命題を目標として除去され、特定の名前や名前の対が外へ取り出されることはない。ここでは命題リサイズも行われない。この境界のまま、後続の議論は `StepAt` をホスト側のステップ順序へ接続する。
<!--/-->
