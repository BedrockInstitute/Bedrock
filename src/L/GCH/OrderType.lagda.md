<!--en-->
# Constructing order types inside `L`

A well-founded relation coded in `L` can be collapsed after its members are presented by a small type. Transitivity then makes every individual collapse value an ordinal and hence an element of `L`. This chapter collects those values into the exact range `otL` and separately collects the graph `colTable`; it does not package an ordinality theorem for `otL`. Only after trichotomy is added does the graph become a coded injection from the original domain into that range.
<!--zh-->
# 在 `L` 内部构造序型

把 `L` 中编码的关系成员表示为小类型后，便可对良基关系作塌缩。传递性进一步保证每个塌缩值都是序数，因而属于 `L`。本章把这些值收集成精确值域 `otL`，并另行收集图 `colTable`；本章没有封装 `otL` 的序数性定理。只有再加入三歧性之后，这张图才成为从原定义域到该值域的编码单射。
<!--ja-->
# `L` の内部で順序型を構成する

`L` で符号化された関係の要素を小さな型で表示すれば、整礎関係を崩壊できます。さらに推移性があれば、個々の崩壊値は順序数となり、したがって `L` の要素になります。本章はそれらの値を正確な値域 `otL` に集め、グラフ `colTable` を別に集めますが、`otL` の順序数性を定理としてまとめてはいません。三分法を追加して初めて、このグラフは元の領域からその値域への符号化された単射になります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The classical assumption is explicit because one later existence proof must decide whether a candidate point precedes the point currently being treated. Well-founded recursion itself does not require this decision; excluded middle enters when a single replacement function is defined by the relation case and its complement.
<!--zh-->
经典假设在此显式给出，因为后文的一项存在性证明必须判定候选点是否在当前点之前。良基递归本身不需要这项判定；排中律进入之处，是按关系成立与否定义一项统一的替换函数时。
<!--ja-->
古典的仮定を明示するのは、後の存在証明で、候補となる点が現在扱う点に先行するかどうかを判定する必要があるからです。整礎再帰そのものはこの判定を必要としません。排中律が使われるのは、関係が成り立つ場合と成り立たない場合に分けて一つの置換関数を定める箇所です。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and an instance of excluded middle at the level needed by the constructible carrier. All later constructions in this module inherit this one classical parameter; it is not hidden as an axiom.
<!--zh-->
固定宇宙层级 `ℓ`，并在可构造载体所需的层级上给定排中律实例。此模块后续的构造都继承这一项经典参数；它没有被隐藏成公理。
<!--ja-->
宇宙レベル `ℓ` と、構成可能な台に必要なレベルでの排中律の実例を固定します。このモジュール以後の構成はすべて、この一つの古典的パラメータを受け継ぎます。排中律が公理として隠されているわけではありません。
<!--/-->

```agda
module L.GCH.OrderType {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The collapse will be recognized by formulas of the first-order language of sets. Ordered-pair membership and equality provide the atomic tests, while conjunction, disjunction, implication, negation, and the unbounded quantifiers express the table conditions. Apparent restrictions such as“for every predecessor”are written by placing the relation atom in an implication, rather than by using a bounded-quantifier constructor.
<!--zh-->
塌缩将由集合论一阶语言中的公式识别。有序对的隶属与相等提供原子检验，合取、析取、蕴含、否定及无界量词则表达表的各项条件。「对每个前驱」这类看似受限的量化，通过把关系原子放在蕴含前件中表达，而不是使用有界量词构造子。
<!--ja-->
崩壊は集合論の一階言語の論理式によって特徴づけられます。順序対の所属と等号が原子的な判定を与え、連言、選言、含意、否定、および非有界量化子が表の条件を表します。「すべての先行者について」のような制限は、関係の原子論理式を含意の前件に置いて表し、有界量化子の構成子は使いません。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
```

<!--en-->
Two representations must agree throughout the construction. Members of `D` are handled through a small presentation so that well-founded recursion is available, whereas graph entries remain sets encoded as ordered pairs in the cumulative hierarchy. Injectivity of the presentation and of ordered-pair coding lets later proofs return from these representations to the original members and coordinates.
<!--zh-->
整个构造必须协调两种表示。为了进行良基递归，`D` 的成员通过一个小表示来处理；图的条目则仍是累积层级中编码为有序对的集合。表示与有序对编码的单射性，使后文能够从这些表示返回原成员和两个坐标。
<!--ja-->
構成の全体を通して、二つの表示を対応させる必要があります。整礎再帰を使うために `D` の要素は小さな表示を通して扱い、グラフの項目は累積階層の中で順序対として符号化された集合のまま扱います。表示と順序対符号化の単射性により、後の証明でこれらの表示から元の要素と二つの座標へ戻れます。
<!--/-->

```agda
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
```

<!--en-->
The proof has to connect a recursively defined value with a formula that `L` can satisfy internally. Well-founded recursion produces the collapse, recursion graphs collect its values and pairs into sets, and the coding formulas interpret those pairs as applications. The stage theorem then places each ordinal collapse value inside `L`.
<!--zh-->
证明必须把递归定义的取值与 `L` 内部可满足的公式连接起来。良基递归产生塌缩，递归图把其取值与有序对收集成集合，编码公式再把这些对解释为应用。最后，层定理把每个序数塌缩值放入 `L`。
<!--ja-->
証明では、再帰的に定めた値を、`L` の内部で充足できる論理式へ結び付ける必要があります。整礎再帰が崩壊を作り、再帰グラフがその値と順序対を集合へ集め、符号化の論理式がそれらの対を適用として解釈します。最後に段階についての定理が、各順序数である崩壊値を `L` の中に置きます。
<!--/-->

```agda
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Recursion.Graph {ℓ} lem
  using () renaming ( module Graph to RecursionGraph )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; appC; appC-adequate; prʟ; prʟ-fst; svAt; domAt )
```

<!--en-->
There are two distinct goals for the collected graph. First it must represent the collapse as a total single-valued relation on `D`; only later, under trichotomy, may it satisfy the extra input-uniqueness clause of an internal injection. The ordered-pair formulas express the graph, and the injection code packages the four clauses only after each has been proved.
<!--zh-->
收集所得的图有两个不同层次的目标。首先，它必须把塌缩表示为 `D` 上全定义的单值关系；此后只有在三歧性下，它才能满足内部单射额外要求的输入唯一性条款。有序对公式表达这张图，而四项单射条件要在分别证明之后才被封装为单射码。
<!--ja-->
集められたグラフには、二段階の目標があります。まず崩壊を `D` 上の全域的な一価関係として表さなければなりません。その後、三分法のもとで初めて、内部単射に必要な入力の一意性も満たせます。順序対の論理式がグラフを表し、単射の四条件はそれぞれ証明された後に初めて単射符号へまとめられます。
<!--/-->

```agda
open import L.Coding.Expressions {ℓ} using ( module PairExpression )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap ) renaming ( module Inj to DefinableInj )
open import L.Mostowski {ℓ} using ( module Mostowski )
```

<!--en-->
The later uniqueness argument repeatedly compares constructible sets by their members. Extensionality turns pointwise equivalence of membership into equality of the underlying sets, and proposition-valued evidence makes equality of the paired constructible objects proof-irrelevant. This is also what permits truncated case analyses to end in equalities without extracting permanent choices.
<!--zh-->
后文的唯一性论证反复通过成员来比较可构造集合。外延性把逐点的隶属等价化为底层集合的相等，而取值为命题的证据使配对而成的可构造对象之相等不依赖具体证明。这也允许命题截断下的分情形以相等为目标结束，而不抽取固定选择。
<!--ja-->
後の一意性証明では、構成可能な集合をその要素によって繰り返し比較します。外延性は所属の点ごとの同値を基礎集合の等しさに変え、命題値の証拠によって、対として作られた構成可能な対象の等しさは証明の取り方に依存しません。そのため、切り詰められた場合分けから恒久的な選択を取り出さずに、等しさを結論できます。
<!--/-->

```agda

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ; isPropΣ; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
The cumulative hierarchy supplies both the ambient sets and a small presentation of each set's members. Thus an element of `D` can be viewed either as an ambient set or as a small index, and membership transports the necessary constructibility evidence between the two views. The successor operation on hierarchy sets will later locate an ordinal collapse value at the stage following that ordinal.
<!--zh-->
累积层级同时提供外围集合及其成员的小表示。因此，`D` 的一个元素既可视为外围集合，也可视为小索引；隶属关系在两种视角之间传递所需的可构造性证据。层级集合上的后继运算稍后用于把序数塌缩值定位到该序数的后继层。
<!--ja-->
累積階層は、周囲の集合と、その各集合の要素の小さな表示を同時に与えます。したがって `D` の要素は、周囲の集合としても小さな添字としても見ることができ、所属によって二つの見方の間で必要な構成可能性の証拠を渡せます。階層の集合に対する後続操作は、後で順序数である崩壊値をその順序数の次の段階に位置付けるために使われます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
```

<!--en-->
Well-foundedness supplies the induction principle that defines and analyzes the collapse. Empty types discharge impossible relation cases, while propositional truncation records existence when later arguments need only that a predecessor or table entry exists, not a chosen witness.
<!--zh-->
良基性提供定义并分析塌缩所需的归纳原理。空类型排除不可能的关系情形；当后续论证只需知道前驱或表项存在、而不需选定见证时，命题截断记录这种存在性。
<!--ja-->
整礎性は、崩壊を定義して調べるための帰納原理を与えます。空の型は不可能な関係の場合を排除し、命題的切り詰めは、後の議論が特定の証人ではなく先行者や表項目の存在だけを必要とするとき、その存在を記録します。
<!--/-->

```agda
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

```

<!--en-->
Write `S` for the carrier of the constructible structure. Its structure membership `_∈ˢ_` expresses membership between elements of `L`; it is distinct from the small membership `_∈ₛ_` used below to read the presentation of an ambient hierarchy set.
<!--zh-->
以 `S` 表示可构造结构的载体。结构隶属 `_∈ˢ_` 表达 `L` 的元素之间的隶属；它不同于下文用于读取外围层级集合之表示的小隶属 `_∈ₛ_`。
<!--ja-->
構成可能構造の台を `S` と書きます。構造の所属 `_∈ˢ_` は `L` の要素間の所属を表し、後で周囲の階層にある集合の表示を読むために使う小さな所属 `_∈ₛ_` とは異なります。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

```

<!--en-->
Formulas will be interpreted in the structure carried by `L`. The notation `S ^ n` denotes an environment of `n` constructible sets, and `γ ⊨ φ` says that the formula `φ` is satisfied by such an environment `γ` inside the restricted constructible structure.
<!--zh-->
这些公式将在 `L` 所承载的结构中解释。记号 `S ^ n` 表示由 `n` 个可构造集合组成的环境，而 `γ ⊨ φ` 表示公式 `φ` 在受限的可构造结构内部由环境 `γ` 满足。
<!--ja-->
論理式は `L` が担う構造で解釈します。記法 `S ^ n` は `n` 個の構成可能集合からなる環境を表し、`γ ⊨ φ` は、制限された構成可能構造の内部で環境 `γ` が論理式 `φ` を満たすことを表します。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
The underlying hierarchy carrier `V ℓ` is an h-set, and constructibility evidence is proposition-valued. Therefore the dependent-pair carrier `S` is also an h-set: equalities of constructible sets are propositions. This is what lets later truncated case analyses eliminate into equalities of carrier elements.
<!--zh-->
底层层级载体 `V ℓ` 是 h-集合，而可构造性证据取值于命题。因此，依值对载体 `S` 也是 h-集合，即可构造集合之间的相等是命题。后文遂可把截断分情形消去到载体元素的等式中。
<!--ja-->
基礎となる階層の台 `V ℓ` は h-集合であり、構成可能性の証拠は命題値です。したがって、依存対からなる台 `S` も h-集合であり、構成可能な集合の間の等式は命題になります。このため、後の切り詰められた場合分けを台の要素の等式へ除去できます。
<!--/-->

```agda
isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))
```

<!--en-->
A coded graph is read on the underlying sets: `F` holds of `x` and `y` when the ordered pair of their underlying elements belongs to the underlying set of `F`. Every clause below reads this shape.
<!--zh-->
编码图在底层集合上读取：当 `x` 与 `y` 的底层元素构成的有序对属于 `F` 的底层集合时，记 `F` 对 `x`、`y` 成立。下文每条子句读取的都是这一形状。
<!--ja-->
符号化されたグラフは、底の集合の上で読まれます。底の要素の順序対が `F` の底の集合に属するとき、`F` は `x` と `y` について成立すると書きます。以下のすべての節が、この形を読みます。
<!--/-->

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

<!--en-->
Fix a constructible set `D` and a constructible code `R` for ordered pairs. The hypothesis `Rsub` says only that the two endpoints of every pair occurring in `R` belong to `D`. Well-foundedness and transitivity are added later when the collapse is formed, and trichotomy is added still later to prove injectivity. No extensionality hypothesis on the relation is assumed anywhere in this chapter.
<!--zh-->
固定可构造集合 `D` 与编码有序对的可构造集合 `R`。假设 `Rsub` 只说明 `R` 中每个实际出现的有序对之两个端点都属于 `D`。形成塌缩时另加良基性与传递性，证明单射性时才再加三歧性。本章始终没有假设关系具有外延性。
<!--ja-->
構成可能集合 `D` と、順序対を符号化する構成可能集合 `R` を固定します。仮定 `Rsub` が述べるのは、`R` に実際に現れる各順序対の二つの端点が `D` に属することだけです。崩壊を作る段階で整礎性と推移性を加え、さらに後で単射性を証明するときに三分法を加えます。この章では関係の外延性を仮定しません。
<!--/-->

```agda
module Collapse (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

```

<!--en-->
Membership in `D` is stated as a one-place predicate on the carrier.
<!--zh-->
`D` 中的隶属被陈述为载体上的一元谓词。
<!--ja-->
`D` への所属は、台の上の一項の述語として述べられます。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst D ⟩

```

<!--en-->
This predicate is a proposition, since it is membership in the underlying set of a presented set. Propositionhood here matters later: a construction may depend on a membership proof without thereby carrying choice data.
<!--zh-->
该谓词是命题，因为它是被呈现集合的底层集合中的隶属。这一命题性后文有用：某构造可以依赖于隶属证明，而不因此携带任何选择数据。
<!--ja-->
この述語は命題です。提示された集合の底の集合への所属だからです。この命題性は後で重要になります。ある構成が所属の証明に依存しても、それで選択のデータを運ぶことはないのです。
<!--/-->

```agda
  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ fst D)
```

<!--en-->
The members of `D` are presented by a small type, the index type of the presentation.
<!--zh-->
`D` 的成员由一个小类型呈现；这个小类型就是该呈现的索引类型。
<!--ja-->
`D` の要素は、小さな型、すなわち提示の添字型によって提示されます。
<!--/-->

```agda
  Dom : Type ℓ
  Dom = ⟪ fst D ⟫

```

<!--en-->
The presentation embeds its indices into the ambient hierarchy.
<!--zh-->
呈现把其索引嵌入外围层级。
<!--ja-->
提示は、その索引を周囲の階層の中へ埋め込みます。
<!--/-->

```agda
  ↪ : Dom → V ℓ
  ↪ = ⟪ fst D ⟫↪

```

<!--en-->
An index is turned back into a constructible set: the embedded member is paired with a constructibility proof transported along the membership of `D`, using the transitivity of constructibility.
<!--zh-->
索引被转回可构造集合：嵌入的成员与沿 `D` 的隶属、由可构造性传递性搬运而来的可构造性证明配对。
<!--ja-->
索引は構成可能な集合へ戻されます。埋め込まれた要素には、`D` への所属に沿って、構成可能性の推移性によって運ばれた構成可能性の証明が対にされます。
<!--/-->

```agda
  up : Dom → S
  up m = ↪ m , isL-trans {x = fst D} {y = ↪ m} (member (fst D) m) (snd D)

```

<!--en-->
The rebuilt constructible set is a member of `D`, by the presentation's own membership record.
<!--zh-->
重建出的可构造集合是 `D` 的成员，这由呈现自身的隶属记录给出。
<!--ja-->
作り直された構成可能な集合は `D` の要素です。これは、提示自身の所属の記録によるものです。
<!--/-->

```agda
  up-mem : (m : Dom) → Mem (up m)
  up-mem m = member (fst D) m

```

<!--en-->
The presentation has no duplicate indices: equality of two embedded members forces equality of their indices. This will later identify the index recovered from the known member `up b` with `b` itself, so that the collected graph contains the expected pair `(↪ b, col b)`. Injectivity of the collapse is a different result and will require trichotomy.
<!--zh-->
该表示没有重复索引：两个嵌入成员相等会迫使其索引相等。后文从已知成员 `up b` 恢复索引时，这一点把恢复所得索引认同为 `b` 本身，从而证明收集所得的图含有预期的对 `(↪ b, col b)`。塌缩函数的单射性是另一项结论，并且需要三歧性。
<!--ja-->
この表示には重複する添字がありません。埋め込まれた二つの要素が等しければ、その添字も等しくなります。後で既知の要素 `up b` から添字を復元するとき、復元された添字を `b` 自身と同一視できるため、集めたグラフが期待する対 `(↪ b, col b)` を含むことが分かります。崩壊関数の単射性は別の結果であり、三分法を必要とします。
<!--/-->

```agda
  Dom≡ : {a b : Dom} → ↪ a ≡ ↪ b → a ≡ b
  Dom≡ {a} {b} e = ↪-inj {a = fst D} {m = a} {n = b} e

```

<!--en-->
Conversely, a member of `D` together with its membership proof recovers a presenting index, by taking the fiber of the presentation at that member.
<!--zh-->
反过来，`D` 的成员连同其隶属证明，通过取呈现在该成员处的纤维，恢复出一个呈现索引。
<!--ja-->
逆に、`D` の要素とその所属の証明からは、提示のその要素における繊維を取ることで、提示の索引が復元されます。
<!--/-->

```agda
  toDom : (x : S) → Mem x → Dom
  toDom x mx = fst (fiber (fst D) mx)

```

<!--en-->
The recovered index presents exactly the given member: the fiber carries the identification of the embedded index with the member.
<!--zh-->
恢复出的索引恰好呈现所给的成员：纤维携带嵌入索引与该成员的同一视。
<!--ja-->
復元された索引は、与えられた要素をちょうど提示します。繊維が、埋め込まれた索引とその要素の同一視を運ぶからです。
<!--/-->

```agda
  toDom-val : (x : S) (mx : Mem x) → ↪ (toDom x mx) ≡ fst x
  toDom-val x mx = snd (fiber (fst D) mx)
```

<!--en-->
The code `R` induces a relation on the small presentation: `a ≺ b` means that the ordered pair of the represented members `↪ a` and `↪ b` belongs to `R`. This is the relation on which well-founded recursion runs. The two lemmas below connect it in both directions with `Holds R (up a) (up b)` on constructible sets.
<!--zh-->
码 `R` 在小表示上诱导一条关系：`a ≺ b` 表示由被表示成员 `↪ a` 与 `↪ b` 组成的有序对属于 `R`。良基递归正沿这条关系进行。下面两条引理把它与可构造集合上的 `Holds R (up a) (up b)` 双向连接起来。
<!--ja-->
符号 `R` は小さな表示の上に関係を誘導します。`a ≺ b` とは、表示された要素 `↪ a` と `↪ b` の順序対が `R` に属することです。整礎再帰はこの関係に沿って進みます。続く二つの補題が、この関係を構成可能集合上の `Holds R (up a) (up b)` と両方向に結び付けます。
<!--/-->

```agda
  opaque
    _≺_ : Dom → Dom → Type ℓ
    a ≺ b = ⟨ pr (↪ a) (↪ b) ∈ₛ fst R ⟩

```

<!--en-->
For fixed indices `a` and `b`, the relation type `a ≺ b` is a proposition because it is a membership statement in a hierarchy set. Thus the relation records only whether the edge exists, not additional data carried by a particular proof. This propositionhood does not itself decide the edge; excluded middle is invoked later only where such a decision is needed.
<!--zh-->
对固定索引 `a` 与 `b`，关系类型 `a ≺ b` 是命题，因为它陈述一个层级集合中的隶属。因此，这条关系只记录边是否存在，不包含由某个特定证明携带的额外数据。这项命题性本身并不判定边是否存在；只有后文真正需要这种判定时才使用排中律。
<!--ja-->
添字 `a` と `b` を固定すると、関係の型 `a ≺ b` は階層内の集合への所属を述べる命題です。したがって、この関係が記録するのは辺の有無だけであり、特定の証明が担う追加のデータではありません。この命題性だけでは辺の有無を判定できず、その判定が実際に必要となる後の箇所で初めて排中律を使います。
<!--/-->

```agda
    isProp≺ : (a b : Dom) → isProp (a ≺ b)
    isProp≺ a b = snd (pr (↪ a) (↪ b) ∈ₛ fst R)

```

<!--en-->
Membership in the coded relation yields the small relation: the ordered pair recorded in `L` is recognized by the bridge between the two membership relations.
<!--zh-->
编码关系中的隶属给出小关系：`L` 中记录的有序对由两种隶属关系之间的桥识别。
<!--ja-->
符号化された関係の中の所属は、小さな関係を与えます。`L` の中に記録された順序対が、二つの所属の関係をつなぐ橋によって認められるのです。
<!--/-->

```agda
    ≺-in : (a b : Dom) → Holds R (up a) (up b) → a ≺ b
    ≺-in a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .fst

```

<!--en-->
Conversely, the small relation records a genuine pair of `R`, so the two readings of the relation agree in both directions.
<!--zh-->
反过来，小关系记录了 `R` 中真实的对，于是关系的两种读法在两个方向上一致。
<!--ja-->
逆に、小さな関係は `R` の本当の対を記録するので、関係の二つの読みは両方向で一致します。
<!--/-->

```agda
    ≺-out : (a b : Dom) → a ≺ b → Holds R (up a) (up b)
    ≺-out a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .snd

```

<!--en-->
Well-foundedness of `_≺_` supplies the recursion and induction by which `col` is defined. Transitivity has a different role: it lets predecessor chains remain below their upper endpoint, which is needed to prove that every collapse value is transitive and hence an ordinal. Neither assumption yet makes the collapse injective or the relation a well-order.
<!--zh-->
关系 `_≺_` 的良基性提供定义 `col` 所需的递归与归纳。传递性承担另一项作用：它保证前驱链仍位于其上端点之下，从而可以证明每个塌缩值传递并成为序数。这两项假设尚不能保证塌缩单射，也没有把该关系封装成良序。
<!--ja-->
関係 `_≺_` の整礎性は、`col` を定義する再帰と帰納を与えます。推移性の役割は別です。先行者の列が上端の点より下にとどまることを保証し、各崩壊値が推移的で順序数になることを証明するために使われます。この二つの仮定だけでは、崩壊の単射性も、関係が整列順序であることも得られません。
<!--/-->

```agda
  module Col (wf : WellFounded _≺_)
             (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where
```

<!--en-->
The Mostowski construction now defines `col p` as the set of values `col r` for predecessors `r ≺ p`. Its computation rule `col-eq` identifies the recursive value with this explicit predecessor image. The membership lemmas give `col r ∈ col p` from a specified predecessor and, conversely, only a propositionally truncated predecessor from an arbitrary member; `col-ord` proves each individual `col p` is an ordinal.
<!--zh-->
Mostowski 构造把 `col p` 定义为所有前驱 `r ≺ p` 的取值 `col r` 所成的集合。计算律 `col-eq` 把递归取值与这一显式前驱像认同。隶属引理从指定前驱得到 `col r ∈ col p`；反过来，从任意成员只得到命题截断下的前驱存在。`col-ord` 则证明每个单独的 `col p` 都是序数。
<!--ja-->
Mostowski の構成は、`col p` を先行者 `r ≺ p` の値 `col r` からなる集合として定めます。計算規則 `col-eq` は、再帰的な値をこの明示的な先行者像と同一視します。所属の補題は、指定された先行者から `col r ∈ col p` を与えますが、逆に任意の要素から得る先行者は命題的に切り詰められた存在にとどまります。`col-ord` は個々の `col p` が順序数であることを証明します。
<!--/-->

```agda
    open Mostowski Dom _≺_ wf ≺-trans public
      using ( module W; col; col-eq; col-in; col-out; col-ord )
```

<!--en-->
Every collapse value is constructible. The lemma `col-ord` first shows that `col p` is an ordinal; the stage lemma then places this ordinal in the stage indexed by its successor, yielding `col-isL p`.
<!--zh-->
每个塌缩值都可构造。引理 `col-ord` 先说明 `col p` 是序数；层引理随后把这个序数置于由其后继索引的层中，从而得到 `col-isL p`。
<!--ja-->
すべての崩壊値は構成可能です。まず補題 `col-ord` が `col p` は順序数であることを示し、次に段階の補題がこの順序数をその後続で添字づけられた段階に置くことで、`col-isL p` が得られます。
<!--/-->

```agda
    opaque
      col-isL : (p : Dom) → ⟨ isL (col p) ⟩
      col-isL p = Lset→isL (sucV (col p)) (suc-ord (col-ord p)) (col p)
                    (ord∈Lset-suc (col p) (col-ord p))

```

<!--en-->
Each collapse value is packaged with its constructibility proof into a constructible set. The collapse thus produces not merely ambient sets but actual elements of the constructible universe.
<!--zh-->
每个塌缩值连同其可构造性证明被打包为可构造集合。塌缩因此产出的不只是外围集合，而是可构造宇宙的真实元素。
<!--ja-->
それぞれの崩壊の値は、その構成可能性の証明とともに、構成可能な集合として包まれます。崩壊が産み出すのは、周囲の集合だけではなく、構成可能宇宙の実際の要素です。
<!--/-->

```agda
    colʟ : Dom → S
    colʟ p = col p , col-isL p

```

<!--en-->
## The formulas
<!--zh-->
## 诸公式
<!--ja-->
## 崩壊表を記述する論理式
<!--/-->

<!--en-->
A table `F` is complete at `x` when every `R`-predecessor `y` of `x` has some recorded value `u`. The existence of `u` is propositionally truncated: completeness remembers that an entry exists but does not choose one, and it does not yet assert that the value is unique.
<!--zh-->
若 `x` 的每个 `R` 前驱 `y` 都在表 `F` 中记录了某个取值 `u`，就称 `F` 在 `x` 处完备。`u` 的存在处于命题截断之下：完备性只保留表项存在这一事实，既不选定某个表项，也尚未断言取值唯一。
<!--ja-->
`x` の各 `R`-先行者 `y` に対して表 `F` が何らかの値 `u` を記録するとき、`F` は `x` で完全です。`u` の存在は命題的に切り詰められています。完全性が保つのは項目が存在するという事実だけで、特定の項目を選ばず、値の一意性もまだ主張しません。
<!--/-->

```agda
Complete : S → S → S → Type (ℓ-suc ℓ)
Complete F R x = (y : S) → Holds R y x → ∥ Σ[ u ∈ S ] Holds F y u ∥₁

```

<!--en-->
The predicate `Src F R x w` says that `w` occurs as a value recorded by `F` at some `R`-predecessor of `x`. Both the predecessor and its table entry remain under propositional truncation, since later reasoning uses only the resulting membership fact.
<!--zh-->
谓词 `Src F R x w` 表示：`F` 在 `x` 的某个 `R` 前驱处把 `w` 记录为取值。该前驱及其表项都留在命题截断之下，因为后文只使用由此得到的隶属事实。
<!--ja-->
述語 `Src F R x w` は、`x` のある `R`-先行者において `F` が `w` を値として記録することを表します。その先行者と表項目はともに命題的切り詰めの中にとどまります。後の議論が使うのは、そこから得られる所属の事実だけだからです。
<!--/-->

```agda
Src : S → S → S → S → Type (ℓ-suc ℓ)
Src F R x w = ∥ Σ[ y ∈ S ] (Holds R y x × Holds F y w) ∥₁

```

<!--en-->
A value `v` is correct for `x` when its members are exactly the source values: membership in `v` yields a source, and every source is a member. The two directions together say that `v` is the set of recorded predecessor values, read purely through membership.
<!--zh-->
值 `v` 对 `x` 是正确的，当其成员恰为来源值：`v` 中的隶属给出一个来源，而每个来源都是成员。两个方向合起来说：`v` 就是所记录的前驱值之集，完全通过隶属读取。
<!--ja-->
値 `v` が `x` に対して正しいのは、その要素がちょうど源となる値であるときです。`v` の中の所属から源が得られ、すべての源が要素です。二つの方向合わせて、`v` が記録された先行者の値の集合であることを、所属だけを通して言っています。
<!--/-->

```agda
ValueIs : S → S → S → S → Type (ℓ-suc ℓ)
ValueIs F R x v = (w : S) → (⟨ fst w ∈ fst v ⟩ → Src F R x w)
                          × (Src F R x w → ⟨ fst w ∈ fst v ⟩)

```

<!--en-->
A table is correct when each pair it actually contains is complete at its input and has exactly the predecessor values as its output. This condition does not specify a domain, so it neither requires entries for all of `D` nor forbids entries outside `D`. The later uniqueness theorem identifies a recorded value with the collapse only when the recorded input is a member of `D`.
<!--zh-->
若一张表实际包含的每个有序对都在其输入处完备，并且输出恰由前驱取值组成，就称该表正确。这项条件没有指定定义域，因此既不要求覆盖整个 `D`，也不禁止在 `D` 之外出现条目。后文的唯一性定理只在被记录的输入属于 `D` 时，才把相应取值认同为塌缩值。
<!--ja-->
表が実際に含む各順序対について、その入力で完全性が成り立ち、出力が先行者の値だけからなるとき、その表を正しいといいます。この条件は領域を指定しないので、`D` 全体の項目を要求せず、`D` の外の項目も禁止しません。後の一意性定理が記録された値を崩壊値と同一視するのは、記録された入力が `D` の要素である場合だけです。
<!--/-->

```agda
Correct : S → S → Type (ℓ-suc ℓ)
Correct F R = (x v : S) → Holds F x v → Complete F R x × ValueIs F R x v
```

<!--en-->
The formula `completeAt f R x` uses an unbounded universal quantifier for a candidate predecessor `y`. The implication restricts attention to those `y` for which `R` records the pair `(y,x)`, and its conclusion uses an unbounded existential quantifier for a value `u` such that `F` records `(y,u)`. Under the existential binder, `u` occupies the new zeroth slot and the earlier variables are shifted.
<!--zh-->
公式 `completeAt f R x` 用无界全称量词引入候选前驱 `y`。蕴含只关注 `R` 记录有序对 `(y,x)` 的那些 `y`，其结论再用无界存在量词引入取值 `u`，要求 `F` 记录 `(y,u)`。进入存在量词后，`u` 占据新的第零槽位，原有变量相应后移。
<!--ja-->
論理式 `completeAt f R x` は、候補となる先行者 `y` を非有界全称量化子で導入します。含意によって、`R` が対 `(y,x)` を記録する `y` だけに条件を課し、その結論では非有界存在量化子で値 `u` を導入して、`F` が `(y,u)` を記録することを要求します。存在量化子の内側では `u` が新しい第零スロットを占め、それまでの変数は一つずつずれます。
<!--/-->

```agda
opaque
  completeAt : ∀ {n} → Fin n → S → Fin n → Formula S n
  completeAt f R x =
    ∀̇ ( appC R zero (suc x)
      ⇒̇ ∃̇ (appAt (suc (suc f)) (suc zero) zero) )
```

<!--en-->
To read the formula as host-level completeness, fix a predecessor `y` and a proof that `R` records `(y,x)`. The adequacy path for `appC` converts this premise into the antecedent expected by the satisfaction proof `h`. Applying `h` yields a propositionally truncated candidate value; `PT.map` keeps the truncation and converts its graph atom into `Holds F y u` using the adequacy path for `appAt`.
<!--zh-->
要把该公式读成宿主层完备性，先固定前驱 `y` 及 `R` 记录 `(y,x)` 的证明。`appC` 的充分性路径把这一前提化为满足证明 `h` 所需的蕴含前件。应用 `h` 后得到命题截断下的候选取值；`PT.map` 保留该截断，并沿 `appAt` 的充分性路径把其中的图原子化为 `Holds F y u`。
<!--ja-->
この論理式をホスト側の完全性として読むには、先行者 `y` と、`R` が `(y,x)` を記録する証明を固定します。`appC` の妥当性を表すパスがこの前提を、充足の証明 `h` が要求する含意の前件へ変えます。`h` を適用すると命題的に切り詰められた候補値が得られます。`PT.map` は切り詰めを保ったまま、`appAt` の妥当性を表すパスによって、そのグラフ原子を `Holds F y u` へ変えます。
<!--/-->

```agda

  complete-out : ∀ {n} (f : Fin n) (R : S) (x : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ completeAt f R x ⟩
               → Complete (lookup f γ) R (lookup x γ)
  complete-out f R x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ)) q })
```

<!--en-->
The final application in this direction performs the first of those conversions: it transports the given relation fact along `appC-adequate` and supplies it to `h y`. The result is still the truncated existential produced by the object-language semantics; the mapping in the preceding lines changes only the contents of that truncation.
<!--zh-->
这一方向的最后一次应用完成上述第一项转换：它沿 `appC-adequate` 搬运已给的关系事实，再把结果交给 `h y`。所得结果仍是对象语言语义产生的截断存在；前几行的映射只改变命题截断内部的内容。
<!--ja-->
この向きの最後の適用は、上で述べた最初の変換を行います。与えられた関係の事実を `appC-adequate` に沿って運び、その結果を `h y` に渡します。得られるものは、対象言語の意味論が作る切り詰められた存在のままです。前の行の写像は、その切り詰めの中身だけを変えます。
<!--/-->

```agda
    (h y (subst ⟨_⟩ (sym (appC-adequate R zero (suc x) (y ∷ γ))) p))

```

<!--en-->
Conversely, assume host-level completeness. For a candidate predecessor satisfying the formula's antecedent, `appC-adequate` first turns that antecedent into `Holds R y x`. Completeness supplies a propositionally truncated value `u`, and `PT.map` transports the accompanying fact `Holds F y u` back into satisfaction of the application atom required by the existential conclusion.
<!--zh-->
反过来，假设宿主层完备性。对满足公式前件的候选前驱，先由 `appC-adequate` 把该前件化为 `Holds R y x`。完备性给出命题截断下的取值 `u`，`PT.map` 再把伴随的 `Holds F y u` 搬回存在结论所需的应用原子满足证明。
<!--ja-->
逆に、ホスト側の完全性を仮定します。論理式の前件を満たす候補の先行者について、まず `appC-adequate` がその前件を `Holds R y x` に変えます。完全性は命題的に切り詰められた値 `u` を与え、`PT.map` がそれに伴う `Holds F y u` を、存在結論が要求する適用原子の充足へ戻します。
<!--/-->

```agda
  complete-in : ∀ {n} (f : Fin n) (R : S) (x : Fin n) (γ : S ^ n)
              → Complete (lookup f γ) R (lookup x γ)
              → ⟨ γ ⊨ completeAt f R x ⟩
  complete-in f R x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ))) q })
```

<!--en-->
This line converts the satisfied relation atom into `Holds R y x` and applies completeness at `x` to the candidate predecessor `y`. That application supplies the truncated value which the surrounding map turns into the object-language existential witness.
<!--zh-->
这一行把已满足的关系原子式转换为 `Holds R y x`，再把 `x` 处的完备性施用于候选前驱 `y`。这次应用给出截断取值，外围的映射随后把它转换为对象语言存在量词所需的见证。
<!--ja-->
この行は、充足された関係原子を `Holds R y x` へ変換し、`x` における完全性を候補の先行者 `y` に適用します。この適用が切り詰められた値を与え、外側の写像がそれを対象言語の存在量化子が求める証人へ変換します。
<!--/-->

```agda
    (h y (subst ⟨_⟩ (appC-adequate R zero (suc x) (y ∷ γ)) p))
```

<!--en-->
The formula `srcAt f R x w` uses an unbounded existential quantifier to say that some `y` is both an `R`-predecessor of `x` and an input at which `F` records `w`. The restriction to predecessors is expressed by the first conjunct, rather than by a bounded existential quantifier.
<!--zh-->
公式 `srcAt f R x w` 用无界存在量词断言某个 `y` 同时是 `x` 的 `R` 前驱，并且 `F` 在输入 `y` 处记录 `w`。对前驱的限制由第一个合取项表达，而不是由有界存在量词表达。
<!--ja-->
論理式 `srcAt f R x w` は非有界存在量化子を使い、ある `y` が `x` の `R`-先行者であると同時に、`F` が入力 `y` で `w` を記録することを述べます。先行者への制限は最初の連言肢で表し、有界存在量化子は使いません。
<!--/-->

```agda
opaque
  srcAt : ∀ {n} → Fin n → S → Fin n → Fin n → Formula S n
  srcAt f R x w = ∃̇ ( appC R zero (suc x) ∧̇ appAt (suc f) zero (suc w) )

```

<!--en-->
The semantic existential is already propositionally truncated. The map defining `src-out` preserves that truncation and converts each hypothetical witness `y`: `appC-adequate` reads the first conjunct as `Holds R y x`, while `appAt-adequate` reads the second as `Holds F y w`.
<!--zh-->
该语义存在式已经处于命题截断之下。定义 `src-out` 的映射保留这一截断，并转换其中每个假定见证 `y`：`appC-adequate` 把第一个合取项读成 `Holds R y x`，`appAt-adequate` 把第二个读成 `Holds F y w`。
<!--ja-->
意味論上の存在はすでに命題的に切り詰められています。`src-out` を定める写像はその切り詰めを保ち、内部の仮の証人 `y` を変換します。`appC-adequate` が最初の連言肢を `Holds R y x` として読み、`appAt-adequate` が第二の連言肢を `Holds F y w` として読みます。
<!--/-->

```agda
  src-out : ∀ {n} (f : Fin n) (R : S) (x w : Fin n) (γ : S ^ n)
          → ⟨ γ ⊨ srcAt f R x w ⟩
          → Src (lookup f γ) R (lookup x γ) (lookup w γ)
  src-out f R x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (appC-adequate R zero (suc x) (y ∷ γ)) p
```

<!--en-->
The graph membership of the predecessor closes the reading.
<!--zh-->
前驱的图隶属闭合该读取。
<!--ja-->
先行者のグラフへの所属が、読みを閉じます。
<!--/-->

```agda
      , subst ⟨_⟩ (appAt-adequate (suc f) zero (suc w) (y ∷ γ)) q ) })

```

<!--en-->
Filling a source is the converse: the predecessor is introduced into the existential with both atoms transported against their adequacy lemmas.
<!--zh-->
填充来源是其反向：把前驱引入存在量词，两个原子逆着各自充分性引理搬运。
<!--ja-->
源の埋めはその逆です。先行者を存在量化子の中に導入し、二つのアトムをそれぞれの妥当性の補題に逆らって運びます。
<!--/-->

```agda
  src-in : ∀ {n} (f : Fin n) (R : S) (x w : Fin n) (γ : S ^ n)
         → Src (lookup f γ) R (lookup x γ) (lookup w γ)
         → ⟨ γ ⊨ srcAt f R x w ⟩
  src-in f R x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (sym (appC-adequate R zero (suc x) (y ∷ γ))) p
```

<!--en-->
The graph atom is written last, completing the fill.
<!--zh-->
图原子最后写入，填充完成。
<!--ja-->
グラフのアトムが最後に書き込まれ、埋めが完成します。
<!--/-->

```agda
      , subst ⟨_⟩ (sym (appAt-adequate (suc f) zero (suc w) (y ∷ γ))) q ) })

```

<!--en-->
The formula `valueAt f R x v` quantifies over an arbitrary set `w` and states both implications between `w ∈ v` and `srcAt f R x w`. Thus it expresses the extensional characterization of `v`: its members are exactly the values recorded at predecessors of `x`. The definition unfolds `srcAt` so that this characterization is presented as one first-order formula.
<!--zh-->
公式 `valueAt f R x v` 对任意集合 `w` 量化，并同时陈述 `w ∈ v` 与 `srcAt f R x w` 之间的两个方向。因此，它给出 `v` 的外延刻画：`v` 的成员恰是 `x` 的各前驱处所记录的取值。定义展开 `srcAt`，使这一刻画成为一条完整的一阶公式。
<!--ja-->
論理式 `valueAt f R x v` は任意の集合 `w` を量化し、`w ∈ v` と `srcAt f R x w` の間の二つの含意をともに述べます。したがって、`v` を外延的に特徴づけています。つまり `v` の要素は、`x` の先行者で記録された値にちょうど一致します。定義では `srcAt` を展開し、この特徴づけを一つの一階論理式として表します。
<!--/-->

```agda
opaque
  unfolding srcAt
  valueAt : ∀ {n} → Fin n → S → Fin n → Fin n → Formula S n
  valueAt f R x v =
    ∀̇ ( ((var zero ∈̇ var (suc v)) ⇒̇ srcAt (suc f) R (suc x) zero)
```

<!--en-->
The biconditional is the conjunction of its two directions, with the source formula unfolded inside both.
<!--zh-->
双条件即其两个方向的合取，而来源公式在两个方向内均已展开。
<!--ja-->
同値はその二つの方向の連言であり、源の論理式はどちらの方向でも展開されています。
<!--/-->

```agda
      ∧̇ (srcAt (suc f) R (suc x) zero ⇒̇ (var zero ∈̇ var (suc v))) )

```

<!--en-->
Reading `valueAt` outward instantiates its universal quantifier at each `w`. The forward implication first turns membership in `v` into satisfaction of the source formula, and `src-out` then reads that satisfaction as `Src F R x w`, giving the forward half of `ValueIs`.
<!--zh-->
向外读取 `valueAt` 时，要在每个 `w` 处实例化其全称量词。正向蕴含先把 `v` 中的隶属转换为来源公式的满足，`src-out` 再把这份满足读成 `Src F R x w`，从而得到 `ValueIs` 的正向一半。
<!--ja-->
`valueAt` を外向きに読むとき、その全称量化子を各 `w` で具体化します。前向きの含意はまず `v` への所属を出所の論理式の充足へ変え、次に `src-out` がその充足を `Src F R x w` として読みます。これにより `ValueIs` の前向きの半分が得られます。
<!--/-->

```agda
  value-out : ∀ {n} (f : Fin n) (R : S) (x v : Fin n) (γ : S ^ n)
            → ⟨ γ ⊨ valueAt f R x v ⟩
            → ValueIs (lookup f γ) R (lookup x γ) (lookup v γ)
  value-out f R x v γ h w =
      (λ w∈ → src-out (suc f) R (suc x) zero (w ∷ γ) (h w .fst w∈))
```

<!--en-->
The backward direction is read symmetrically, through the source filling. Thus the formula says exactly that `v` collects the source values, which is the reading the later uniqueness argument consumes.
<!--zh-->
反向对称地经来源填充读取。于是该公式恰在说：`v` 收集来源值；这正是后文唯一性论证所消耗的读法。
<!--ja-->
逆方向は、源の埋めを通して対称的に読まれます。こうして、この論理式は、`v` が源となる値を集めていることをちょうど述べており、これが後の一意性の議論が消費する読みです。
<!--/-->

```agda
    , (λ s → h w .snd (src-in (suc f) R (suc x) zero (w ∷ γ) s))

```

<!--en-->
To prove the forward implication of `valueAt`, take a member `w` of the proposed value `v`. The host-level value equation says, merely, that `w` already occurs as the value of some `R`-predecessor of `x`. Reading that source statement inward supplies the existential witness required by the object-language formula in the environment extended by `w`.
<!--zh-->
为证明 `valueAt` 的正向蕴含，取候选取值 `v` 的一个成员 `w`。宿主级取值方程说，在命题截断下，`w` 已经作为 `x` 的某个 `R` 前驱之取值出现。把这条来源陈述向内读取，便在以 `w` 扩展的环境中给出对象语言公式所需的存在见证。
<!--ja-->
`valueAt` の前向きの含意を示すため、候補となる値 `v` の要素 `w` を取ります。ホストレベルの値の方程式は、`w` が `x` のある `R`-先行者で記録された値として単に現れることを述べます。この出所の主張を内向きに読むと、`w` で拡張した環境において、対象言語の論理式が求める存在証人が得られます。
<!--/-->

```agda
  value-in : ∀ {n} (f : Fin n) (R : S) (x v : Fin n) (γ : S ^ n)
           → ValueIs (lookup f γ) R (lookup x γ) (lookup v γ)
           → ⟨ γ ⊨ valueAt f R x v ⟩
  value-in f R x v γ h w =
      (λ w∈ → src-in (suc f) R (suc x) zero (w ∷ γ) (h w .fst w∈))
```

<!--en-->
For the converse implication, a satisfaction proof of the source formula is first read as the mere existence of a predecessor whose table value is `w`. The reverse half of `ValueIs` then places `w` in the recorded value. Thus `valueAt` expresses exactly the recursive value equation relative to the candidate table; identifying that value with the Mostowski collapse will require well-founded induction later.
<!--zh-->
对逆向蕴含，先把来源公式的满足读成一种命题截断的存在：某个前驱的表值是 `w`。随后，`ValueIs` 的反向一半证明 `w` 属于所记录的值。因此，`valueAt` 恰好表达相对于候选表的递归取值方程；稍后还须借助良基归纳，才能把这个值认同为 Mostowski 塌缩。
<!--ja-->
逆向きの含意では、まず出所の論理式の充足を、表の値が `w` となる先行者が単に存在することとして読みます。次に `ValueIs` の逆向きの半分から、`w` が記録された値に属することが従います。したがって `valueAt` が表すのは候補となる表についての再帰方程式そのものであり、その値を Mostowski 崩壊と同定するには、後で整礎帰納が必要です。
<!--/-->

```agda
    , (λ s → h w .snd (src-out (suc f) R (suc x) zero (w ∷ γ) s))
```

<!--en-->
Correctness is tested only where the candidate table actually has an entry. The two universal quantifiers range over an argument `x` and a value `v`; if the table contains the ordered pair `(x,v)`, the formula requires the two conditions that make this entry a valid recursive step.
<!--zh-->
正确性只在候选表确实含有表项之处接受检验。两层全称量词遍历实参 `x` 与取值 `v`；若表中含有有序对 `(x,v)`，公式便要求这个表项满足递归步骤所需的两项条件。
<!--ja-->
正しさが検査されるのは、候補となる表が実際に項目をもつ点だけです。二つの全称量化子は入力 `x` と値 `v` を動き、表が順序対 `(x,v)` を含むなら、その項目が再帰の一段として正しいための二条件を要求します。
<!--/-->

```agda
opaque
  unfolding completeAt valueAt
  correctAt : ∀ {n} → Fin n → S → Formula S n
  correctAt f R =
    ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
```

<!--en-->
Those two conditions separate existence from the value equation. Completeness says that every `R`-predecessor of `x` has some entry in the table, while the value clause says that the members of `v` are exactly the values appearing at those predecessor entries. The formula imposes no domain condition beyond entries already present in the table.
<!--zh-->
这两项条件把存在性与取值方程分开。完备性说，`x` 的每个 `R` 前驱在表中都有某个表项；取值子句则说，`v` 的成员恰是这些前驱表项处出现的取值。除此以外，公式并不规定表的定义域。
<!--ja-->
二つの条件は、存在と値の方程式を分けて述べます。完全性は `x` の各 `R`-先行者に表の項目があることを述べ、値の条項は `v` の要素がそれらの先行者で記録された値とちょうど一致することを述べます。この論理式は、表にすでに現れる項目以外について定義域を指定しません。
<!--/-->

```agda
          ⇒̇ ( completeAt (suc (suc f)) R (suc zero)
            ∧̇ valueAt (suc (suc f)) R (suc zero) zero ) ))

```

<!--en-->
To read the formula outward, begin with an actual table entry `(x,v)`. Adequacy of `appAt` turns its membership proof into the antecedent required by the formula. Instantiating the two quantifiers at `x` and `v` then yields completeness at `x` and the corresponding value equation; this line reads the completeness half back into the host-level predicate.
<!--zh-->
向外读取公式时，先取表中一个实际表项 `(x,v)`。`appAt` 的充分性把它的隶属证明转换为公式前件所需的证明。在 `x` 与 `v` 处实例化两层量词后，便得到 `x` 处的完备性及相应的取值方程；本行把其中的完备性一半读回宿主级谓词。
<!--ja-->
論理式を外向きに読むには、まず表の実際の項目 `(x,v)` を取ります。`appAt` の妥当性によって、その所属証明は論理式の前件へ移されます。二つの量化子を `x` と `v` で具体化すると、`x` での完全性と対応する値の方程式が得られ、この行では完全性の側をホストレベルの述語へ読み戻します。
<!--/-->

```agda
  correct-out : ∀ {n} (f : Fin n) (R : S) (γ : S ^ n)
              → ⟨ γ ⊨ correctAt f R ⟩ → Correct (lookup f γ) R
  correct-out f R γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ))) p)
    in complete-out (suc (suc f)) R (suc zero) (v ∷ x ∷ γ) c
```

<!--en-->
The second component is read by `value-out`, giving the equivalence between membership in `v` and occurrence as a value at an `R`-predecessor of `x`. Paired with completeness, this proves the host-level correctness of the chosen entry. Since the construction works for every entry of the table, it proves `Correct F R`.
<!--zh-->
第二分量由 `value-out` 读取，得到「属于 `v`」与「作为 `x` 的某个 `R` 前驱之取值出现」之间的等价。它与完备性配对后，证明所选表项在宿主级正确。由于该构造适用于表中每个表项，最终便得到 `Correct F R`。
<!--ja-->
第二成分を `value-out` で読むと、`v` への所属と、`x` のある `R`-先行者で値として現れることとの同値が得られます。これを完全性と組にすれば、選んだ項目がホストレベルで正しいことが示されます。同じ構成は表の各項目に適用できるので、`Correct F R` が従います。
<!--/-->

```agda
     , value-out (suc (suc f)) R (suc zero) zero (v ∷ x ∷ γ) w

```

<!--en-->
Conversely, suppose the table is correct at the host level. After choosing an argument `x`, a value `v`, and an entry `(x,v)`, adequacy of `appAt` turns the antecedent of the object-language implication into the corresponding host-level entry. Correctness then supplies completeness and the value equation for that entry; this line inserts the completeness half into the formula.
<!--zh-->
反过来，设该表在宿主级正确。选定实参 `x`、取值 `v` 与表项 `(x,v)` 后，`appAt` 的充分性把对象语言蕴含的前件转换为相应的宿主级表项。正确性随即给出该表项的完备性与取值方程；本行把其中的完备性一半填入公式。
<!--ja-->
逆に、表がホストレベルで正しいとします。入力 `x`、値 `v`、項目 `(x,v)` を選ぶと、`appAt` の妥当性によって対象言語の含意の前件が対応するホストレベルの項目へ移ります。正しさから、その項目の完全性と値の方程式が得られ、この行では完全性の側を論理式へ入れます。
<!--/-->

```agda
  correct-in : ∀ {n} (f : Fin n) (R : S) (γ : S ^ n)
             → Correct (lookup f γ) R → ⟨ γ ⊨ correctAt f R ⟩
  correct-in f R γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ)) p)
    in complete-in (suc (suc f)) R (suc zero) (v ∷ x ∷ γ) c
```

<!--en-->
The value equation is inserted by `value-in`, completing the conjunction required for the entry `(x,v)`. Abstracting over the two chosen elements gives the two universal quantifiers. Thus `correct-in` and `correct-out` establish the exact correspondence between `correctAt` and the host-level predicate `Correct`.
<!--zh-->
取值方程由 `value-in` 填入，从而补全表项 `(x,v)` 所需的合取。再对选定的两个元素作抽象，便得到两层全称量词。因此，`correct-in` 与 `correct-out` 建立了 `correctAt` 和宿主级谓词 `Correct` 之间的精确对应。
<!--ja-->
値の方程式を `value-in` で入れると、項目 `(x,v)` に必要な連言が完成します。選んだ二要素について抽象すれば、二つの全称量化子が得られます。したがって `correct-in` と `correct-out` は、`correctAt` とホストレベルの述語 `Correct` の正確な対応を与えます。
<!--/-->

```agda
     , value-in (suc (suc f)) R (suc zero) zero (v ∷ x ∷ γ) w
```

<!--en-->
The next formula fixes the relation `R` but leaves the witnessing table existentially bound. This separation is mathematically useful: a value can be recognized locally by some correct table before a single table over the whole domain has been constructed.
<!--zh-->
下一个公式固定关系 `R`，但仍以存在量词绑定作为见证的表。这种区分具有数学作用：在尚未构造出覆盖整个定义域的单一表之前，便可先借某张正确表局部识别一个取值。
<!--ja-->
次の論理式では関係 `R` を固定しますが、証人となる表は存在量化されたままです。この区別により、定義域全体を覆う一つの表を構成する前でも、ある正しい表を使って値を局所的に認識できます。
<!--/-->

```agda
module ColFo (R : S) where

```

<!--en-->
At an environment `(z ∷ p ∷ [])`, the formula says that there merely exists a set `F` which is correct for `R` and contains the entry `(p,z)`. The table is bound existentially, so this is a local characterization of the value at `p`; it does not yet assert that one fixed table works simultaneously over the whole domain.
<!--zh-->
在环境 `(z ∷ p ∷ [])` 中，该公式说：命题截断地存在集合 `F`，它对 `R` 正确，并含有表项 `(p,z)`。表由存在量词绑定，所以这里只是刻画 `p` 处取值的局部陈述，尚未断言有一张固定表同时适用于整个定义域。
<!--ja-->
環境 `(z ∷ p ∷ [])` で、この論理式は、`R` に対して正しく項目 `(p,z)` を含む集合 `F` が単に存在することを述べます。表は存在量化されているので、これは `p` での値を局所的に特徴づけるだけであり、一つの固定された表が定義域全体で同時に働くとはまだ述べていません。
<!--/-->

```agda
  opaque
    unfolding correctAt
    colFo : Formula S 2
    colFo = ∃̇ ( correctAt zero R
              ∧̇ appAt zero (suc (suc zero)) (suc zero) )
```

<!--en-->
Reading `colFo` outward preserves the propositional truncation around its table witness. The existential supplies a table `F`; inside the same truncation, the conjunction supplies a proof that `F` is correct for `R` and the object-language application atom for the entry `(p,z)`.
<!--zh-->
向外读取 `colFo` 时，表见证外面的命题截断仍被保留。存在量词给出表 `F`；在同一截断内部，合取项给出 `F` 对 `R` 正确的证据，以及表示表项 `(p,z)` 的对象语言应用原子式。
<!--ja-->
`colFo` を外向きに読むとき、表の証人を包む命題的切り詰めは保たれます。存在量化子が表 `F` を与え、同じ切り詰めの内側で、連言が `F` は `R` に対して正しいという証拠と、項目 `(p,z)` を表す対象言語の適用原子式を与えます。
<!--/-->

```agda

    colFo-out : (z p : S) → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
              → ∥ Σ[ F ∈ S ] (Correct F R × Holds F p z) ∥₁
    colFo-out z p = PT.map (λ { (F , (hc , ha)) → F
      , ( correct-out zero R (F ∷ z ∷ p ∷ []) hc
        , subst ⟨_⟩ (appAt-adequate zero (suc (suc zero)) (suc zero)
```

<!--en-->
Adequacy of `appAt` converts the remaining application atom into `Holds F p z`. The result is therefore merely a correct table together with the required entry, exactly the host-level reading of the formula.
<!--zh-->
`appAt` 的充分性把余下的应用原子式转换为 `Holds F p z`。因此，结果是在命题截断下得到一张正确表及所需表项，这正是该公式的宿主级读法。
<!--ja-->
`appAt` の妥当性は、残った適用原子式を `Holds F p z` へ変換します。したがって得られるのは、正しい表と必要な項目が単に存在するという、論理式のホストレベルでの読みそのものです。
<!--/-->

```agda
            (F ∷ z ∷ p ∷ [])) ha ) })

```

<!--en-->
For the inward direction, an explicitly given correct table `F` containing `(p,z)` serves as the existential witness. The correctness proof is translated by `correct-in`; the remaining task is to express the given table entry by the application atom.
<!--zh-->
对向内方向，一张明确给定且含有 `(p,z)` 的正确表 `F` 充当存在见证。正确性证明由 `correct-in` 转入公式；余下任务是用应用原子式表达给定的表项。
<!--ja-->
内向きには、明示的に与えられた、`(p,z)` を含む正しい表 `F` を存在証人とします。正しさの証明は `correct-in` によって論理式へ移され、残る仕事は与えられた表の項目を適用原子式で表すことです。
<!--/-->

```agda
    colFo-in : (z p F : S) → Correct F R → Holds F p z
             → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
    colFo-in z p F hc hp = ∣ F
      , ( correct-in zero R (F ∷ z ∷ p ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc zero)) (suc zero)
```

<!--en-->
Adequacy of `appAt`, used in the reverse direction, turns `Holds F p z` into satisfaction of that atom. The table witness, its correctness, and this entry are then enclosed by the existential truncation, proving `colFo` at `(z,p)`.
<!--zh-->
反向使用 `appAt` 的充分性，便把 `Holds F p z` 转换为该原子式的满足。随后将表见证、其正确性与这个表项一起置于存在量词的命题截断中，即得 `colFo` 在 `(z,p)` 处的满足。
<!--ja-->
`appAt` の妥当性を逆向きに用いると、`Holds F p z` はその原子式の充足へ移ります。表の証人、その正しさ、この項目を存在量化の切り詰めに包むことで、`(z,p)` における `colFo` の充足が得られます。
<!--/-->

```agda
            (F ∷ z ∷ p ∷ []))) hp ) ∣₁
```

<!--en-->
A pointwise value formula such as `colFo` must later be used to define a set of ordered pairs. The generic `PairFo` construction makes that passage: it recognizes a pair `(p,z)` precisely when `z` satisfies the chosen formula at `p`. This lets the local collapse formula serve as the value relation for the recursion constructed below.
<!--zh-->
稍后需要把 `colFo` 这样的逐点取值公式用于定义有序对集合。通用构造 `PairFo` 完成这一转换：它恰在 `z` 于 `p` 处满足给定公式时识别有序对 `(p,z)`。因此，局部塌缩公式能够充当下文递归构造的取值关系。
<!--ja-->
後では、`colFo` のような各点での値の論理式から、順序対の集合を定める必要があります。一般的な構成 `PairFo` は、`z` が `p` で与えられた論理式を満たすとき、かつそのときに限って順序対 `(p,z)` を認識します。これにより、局所的な崩壊の論理式を、以下で構成する再帰の値関係として使えます。
<!--/-->

```agda
open import L.Recursion.Graph {ℓ} lem public using ( module PairFo )
```

<!--en-->
## Uniqueness, existence, and the tables
<!--zh-->
## 唯一性、存在性与诸表
<!--ja-->
## 一意性、存在、崩壊表
<!--/-->

<!--en-->
The internal construction starts with a coded domain `D` and a coded relation `R`. Its only initial side condition is that every pair belonging to `R` has both coordinates in `D`. Well-foundedness and transitivity are absent from this module boundary and will be supplied separately when the collapse argument begins.
<!--zh-->
内部构造从编码定义域 `D` 与编码关系 `R` 出发。起初唯一的附加条件是：属于 `R` 的每个有序对，其两个坐标都属于 `D`。该模块边界尚未要求良基性与传递性；塌缩论证开始时才会另行给出这两项条件。
<!--ja-->
内部の構成は、符号化された定義域 `D` と関係 `R` から始まります。最初の付帯条件は、`R` に属する各順序対の両成分が `D` に属することだけです。整礎性と推移性はこのモジュールの境界では仮定されず、崩壊の議論を始めるときに別々に与えられます。
<!--/-->

```agda
module Internal (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

```

<!--en-->
The domain representation and its coded relation now provide the common setting for two formula constructions. `CF` is the local collapse-value formula for `R`, and `PF` recognizes the ordered pair formed from an argument and a value satisfying that formula. Neither construction at this point asserts existence or uniqueness of collapse values.
<!--zh-->
定义域表示及其编码关系现在成为两种公式构造的共同背景。`CF` 是关系 `R` 的局部塌缩取值公式，`PF` 则识别由实参与满足该公式的取值组成的有序对。此时，这两个构造都尚未断言塌缩取值存在或唯一。
<!--ja-->
定義域の表示と符号化された関係を共通の土台として、二つの論理式を用意します。`CF` は `R` に対する局所的な崩壊値の論理式であり、`PF` は入力と、その論理式を満たす値との順序対を認識します。この時点では、どちらも崩壊値の存在や一意性を主張しません。
<!--/-->

```agda
  open Collapse D R Rsub public
  module CF = ColFo R using ( colFo; colFo-in; colFo-out )
  module PF = PairFo CF.colFo using ( pair-in; pair-out; pairFo )

```

<!--en-->
If `q` is a member of `D`, decoding its membership proof gives an index `toDom q mq`. Re-embedding that index has the same underlying iterative set as `q` by `toDom-val`; since the constructibility component of `S` is proposition-valued, equality of the underlying sets upgrades to equality in `S`.
<!--zh-->
若 `q` 是 `D` 的成员，对其成员证明解码便得到索引 `toDom q mq`。由 `toDom-val`，把该索引重新嵌入后所得元素与 `q` 具有相同的底层迭代集合；又因 `S` 的可构造性分量为命题，底层集合的相等可提升为 `S` 中的相等。
<!--ja-->
`q` が `D` の要素なら、その所属証明を復号して添字 `toDom q mq` を得ます。`toDom-val` により、この添字を埋め戻したものと `q` は同じ基礎の反復的集合をもちます。さらに `S` の構成可能性の成分は命題なので、基礎の集合の等しさから `S` における等しさが従います。
<!--/-->

```agda
  up-toDom : (q : S) (mq : Mem q) → up (toDom q mq) ≡ q
  up-toDom q mq = Σ≡Prop (λ v → snd (isL v)) (toDom-val q mq)
```

<!--en-->
The collapse formula depends on its argument through the second environment slot. Hence an equality `x ≡ y` permits direct substitution in that slot: any value `v` satisfying the formula at `x` also satisfies it at `y`. This is what later reconciles the canonical representative `up (toDom q mq)` with the original element `q`.
<!--zh-->
塌缩公式通过环境的第二槽依赖实参。因此，等式 `x ≡ y` 允许直接在该槽中替换：若取值 `v` 在 `x` 处满足公式，它也在 `y` 处满足公式。稍后正是借此把典范表示 `up (toDom q mq)` 与原元素 `q` 协调起来。
<!--ja-->
崩壊の論理式は、環境の第二の枠を通して入力に依存します。したがって等式 `x ≡ y` に沿ってその枠で直接置換でき、値 `v` が `x` で論理式を満たすなら `y` でも満たします。後で正準な表示 `up (toDom q mq)` と元の要素 `q` を結びつけるのは、この置換です。
<!--/-->

```agda
  colFo-at : (v : S) {x y : S} → x ≡ y
           → ⟨ (v ∷ x ∷ []) ⊨ CF.colFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ CF.colFo ⟩
  colFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ CF.colFo ⟩) e

```

<!--en-->
The module now assumes that the small relation is well-founded and transitive. Well-foundedness supports the recursive definition of `col` and the inductions used for uniqueness; transitivity is used to show that the resulting collapse values are ordinals. These assumptions play different roles and neither follows from the earlier endpoint condition on `R`.
<!--zh-->
此模块现在假定小关系既良基又传递。良基性支撑 `col` 的递归定义以及唯一性证明中的诸次归纳；传递性则用于证明所得塌缩值为序数。这两项假设作用不同，且都不由先前对 `R` 的端点条件推出。
<!--ja-->
ここで小さな関係が整礎かつ推移的であると仮定します。整礎性は `col` の再帰的定義と一意性証明の帰納を支え、推移性は得られる崩壊値が順序数であることを示すために使われます。二つの仮定の役割は異なり、先の `R` の端点条件からはどちらも従いません。
<!--/-->

```agda
  module Graph (wf : WellFounded _≺_)
               (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

```

<!--en-->
With these two hypotheses, the Mostowski recursion assigns to each `a` the set `col a` of collapse values of its predecessors. Its introduction and elimination lemmas characterize membership in that set, and `col-ord` proves that each individual `col a` is an ordinal. This statement concerns the pointwise collapse values, not yet the set `otL` collected later.
<!--zh-->
在这两项假设下，Mostowski 递归为每个 `a` 指派集合 `col a`，其成员是诸前驱的塌缩值。相应的引入与消去引理刻画该集合的隶属，而 `col-ord` 证明每个单独的 `col a` 都是序数。这里说的是逐点塌缩值，尚不是稍后收集得到的集合 `otL`。
<!--ja-->
この二つの仮定のもとで、Mostowski 再帰は各 `a` に、その先行者の崩壊値からなる集合 `col a` を割り当てます。導入と除去の補題がその集合への所属を特徴づけ、`col-ord` は個々の `col a` が順序数であることを示します。ここでの主張は各点の崩壊値についてであり、後で集める集合 `otL` についてではありません。
<!--/-->

```agda
    open Col wf ≺-trans public

```

<!--en-->
Well-foundedness rules out a loop `a ≺ a`. In the induction step, such a loop lets the induction hypothesis for predecessors be applied to `a` itself, with the same loop serving both as the evidence that `a` is smaller and as the contradiction-producing hypothesis.
<!--zh-->
良基性排除了环 `a ≺ a`。在归纳步骤中，若有这样的环，便可把面向前驱的归纳假设施于 `a` 自身；同一份环证明既说明 `a` 比自身更小，也充当归纳假设产出矛盾时的输入。
<!--ja-->
整礎性はループ `a ≺ a` を排除します。帰納段階でそのようなループがあると、先行者についての帰納仮定を `a` 自身に適用できます。同じループが、`a` が自分自身より小さいことの証拠と、帰納仮定から矛盾を得るための入力の両方になります。
<!--/-->

```agda
    ≺-irrefl : (a : Dom) → a ≺ a → Empty.⊥
    ≺-irrefl = W.induction {P = λ a → a ≺ a → Empty.⊥} (λ a rec h → rec a h h)
```

<!--en-->
The uniqueness statement is conditional on an entry being present: if a correct table `F` records `v` at the genuine domain point `up a`, then the underlying set of `v` equals `col a`. It does not claim that every correct table contains an entry at every member of `D`. The proof proceeds by well-founded induction on `a`, with the displayed equality as its motive.
<!--zh-->
此处的唯一性陈述以表项已经存在为条件：若正确表 `F` 在真实定义域点 `up a` 记录取值 `v`，则 `v` 的底层集合等于 `col a`。它并不声称每张正确表在 `D` 的每个成员处都有表项。证明对 `a` 作良基归纳，并以所示等式为归纳谓词。
<!--ja-->
ここでの一意性は、項目が存在することを条件とします。正しい表 `F` が実際の定義域の点 `up a` で値 `v` を記録するなら、`v` の基礎の集合は `col a` に等しくなります。すべての正しい表が `D` の全要素で項目をもつとは主張していません。証明は `a` に関する整礎帰納で進み、表示された等式を帰納的述語とします。
<!--/-->

```agda
    correct-val : (F : S) → Correct F R → (a : Dom) (v : S)
                → Holds F (up a) v → fst v ≡ col a
    correct-val F hc = W.induction {P = λ a → (v : S) → Holds F (up a) v → fst v ≡ col a} go
      where
      go : (a : Dom) → ((b : Dom) → b ≺ a → (v : S) → Holds F (up b) v → fst v ≡ col b)
```

<!--en-->
The proof reduces to a pointwise equivalence: `w` belongs to the recorded value if and only if `w` belongs to the collapse. Two helper facts are extracted from the correctness hypothesis: completeness at `up a`, and the value clause.
<!--zh-->
证明化归为逐点等价：`w` 属于被记录取值当且仅当 `w` 属于塌缩。从正确性假设提取两个辅助事实：`up a` 处的完备性，以及取值子句。
<!--ja-->
証明は、各点の同値に帰着します。`w` が記録された値に属することと、`w` が崩壊に属することは同値です。正しさの仮定から、`up a` での完備さと、値の条項という二つの補助の事実が取り出されます。
<!--/-->

```agda
         → (v : S) → Holds F (up a) v → fst v ≡ col a
      go a IH v hv = extensionalV {a = fst v} {b = col a} (λ w → ⇔toPath (fwd w) (bwd w))
        where
        cmp : Complete F R (up a)
        cmp = hc (up a) v hv .fst
```

<!--en-->
The correctness of the entry at `a` has two complementary consequences. The preceding `cmp` supplies table entries for all predecessors, while `val` identifies membership in `v` with occurrence as a predecessor value. The two directions of the coming extensionality argument use these consequences in opposite orders.
<!--zh-->
`a` 处表项的正确性有两项互补后果。前面的 `cmp` 为所有前驱提供表项，而 `val` 把对 `v` 的隶属与作为某个前驱取值出现相互认同。接下来的外延性论证在两个方向中以相反次序使用这两项事实。
<!--ja-->
`a` での項目の正しさには、相補的な二つの帰結があります。先の `cmp` はすべての先行者に表の項目を与え、`val` は `v` への所属と先行者の値として現れることを同定します。続く外延性の議論の二方向では、この二つを逆の順で用います。
<!--/-->

```agda
        val : ValueIs F R (up a) v
        val = hc (up a) v hv .snd

```

<!--en-->
For the first inclusion, let `w` be a member of the recorded value `v`. Since `v` is constructible, membership makes `w` constructible as well, so it can be packaged as the carrier element `wS`. The forward half of `val` then gives, under propositional truncation, an `R`-predecessor `y` of `a` at which the table records `wS`.
<!--zh-->
为证第一向包含，取被记录取值 `v` 的成员 `w`。由于 `v` 可构造，成员关系也使 `w` 可构造，故可将其打包为载体元素 `wS`。随后，`val` 的正向一半在命题截断下给出 `a` 的某个 `R` 前驱 `y`，表在该处记录 `wS`。
<!--ja-->
第一の包含を示すため、記録された値 `v` の要素 `w` を取ります。`v` は構成可能であり、その要素 `w` も構成可能なので、台の要素 `wS` として組にできます。すると `val` の前向きの半分から、`a` のある `R`-先行者 `y` で表が `wS` を記録することが、命題的切り詰めのもとで得られます。
<!--/-->

```agda
        fwd : (w : V ℓ) → ⟨ w ∈ fst v ⟩ → ⟨ w ∈ col a ⟩
        fwd w w∈ = PT.rec (snd (w ∈ col a)) read (val wS .fst w∈)
          where
          wS : S
          wS = w , isL-trans {x = fst v} {y = w} w∈ (snd v)
```

<!--en-->
The source entry is converted into the two facts needed: the relation between the carried predecessor and the argument, and the table entry at the carried predecessor. The predecessor is then decoded to its internal index.
<!--zh-->
来源条目被转换为所需的两条事实：被载前驱与实参之间的关系，以及被载前驱处的表条目。前驱随后被解码为其内部索引。
<!--ja-->
出所の項目は、必要な二つの事実に変換されます。載せられた先行者と入力の間の関係と、載せられた先行者での表の項目です。先行者は、その内部の添字に復号されます。
<!--/-->

```agda
          read : Σ[ y ∈ S ] (Holds R y (up a) × Holds F y wS) → ⟨ w ∈ col a ⟩
          read (y , (ry , fy)) = subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b b≺a)
            where
            my : Mem y
            my = Rsub y (up a) ry .fst
```

<!--en-->
The internal index `b` is recovered by descending along the membership, and the relation entry is transported to the internal form `b ≺ a`. The equation `e` records the identification of `w` with the collapse of `b`, to be proved next.
<!--zh-->
内部索引 `b` 由隶属下降而恢复，关系条目被运输为内部形式 `b ≺ a`。等式 `e` 记录 `w` 与 `b` 的塌缩的认同，下一步证明。
<!--ja-->
内部の添字 `b` は所属を下降して復元され、関係の項目は内部の形 `b ≺ a` へ運ばれます。等式 `e` が、`w` と `b` の崩壊の同定を記録します。これは次に証明されます。
<!--/-->

```agda
            b : Dom
            b = toDom y my
            b≺a : b ≺ a
            b≺a = ≺-in b a (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val y my)) ry)
            e : w ≡ col b
```

<!--en-->
The equation is exactly the induction hypothesis applied to the decoded predecessor: the table's value at the carried predecessor equals the collapse of its internal index, which by transport equals `w`.
<!--zh-->
该等式恰是把归纳假设施于解码后的前驱：表在被载前驱处的取值等于其内部索引的塌缩，经运输即等于 `w`。
<!--ja-->
この等式は、復号された先行者に帰納の仮定を適用したものです。表の、載せられた先行者での値は、その内部の添字の崩壊に等しく、輸送によって `w` に等しくなります。
<!--/-->

```agda
            e = IH b b≺a wS (subst (λ t → ⟨ pr t w ∈ fst F ⟩) (sym (toDom-val y my)) fy)

```

<!--en-->
For the reverse inclusion, suppose `w ∈ col a`. The elimination rule for the collapse says, under propositional truncation, that `col r ≡ w` for some predecessor `r ≺ a`. Because the goal `w ∈ fst v` is a proposition, the proof may reason inside that truncation. The carried element `wS` is constructible because it belongs to the constructible set `col a`.
<!--zh-->
为证反向包含，设 `w ∈ col a`。塌缩的消去规则在命题截断下给出某个前驱 `r ≺ a`，并有 `col r ≡ w`。目标 `w ∈ fst v` 是命题，故可以在该截断内部推理。又因 `w` 属于可构造集合 `col a`，所以可把它连同可构造性证据打包为 `wS`。
<!--ja-->
逆向きの包含では `w ∈ col a` とします。崩壊の除去則から、ある先行者 `r ≺ a` について `col r ≡ w` であることが、命題的切り詰めのもとで得られます。目標 `w ∈ fst v` は命題なので、その切り詰めの内側で議論できます。また `w` は構成可能な集合 `col a` の要素なので、構成可能性の証拠と組にして `wS` とできます。
<!--/-->

```agda
        bwd : (w : V ℓ) → ⟨ w ∈ col a ⟩ → ⟨ w ∈ fst v ⟩
        bwd w w∈ = PT.rec (snd (w ∈ fst v)) read (col-out a w w∈)
          where
          wS : S
          wS = w , isL-trans {x = col a} {y = w} w∈ (col-isL a)
```

<!--en-->
For the predecessor `r` supplied by `col-out`, completeness of the entry at `a` gives merely some table value `u` at `up r`. The inner elimination is legitimate because membership of `w` in `v` is a proposition. It remains to use correctness at `r` to compare `u` with `col r`, and hence with `w`.
<!--zh-->
对 `col-out` 给出的前驱 `r`，`a` 处表项的完备性在命题截断下给出 `up r` 处的某个表值 `u`。由于目标 `w ∈ v` 是命题，可以合法地消去这个截断。接下来只须利用 `r` 处的正确性把 `u` 与 `col r` 比较，进而与 `w` 比较。
<!--ja-->
`col-out` が与える先行者 `r` について、`a` での項目の完全性から、`up r` におけるある表の値 `u` が単に存在することが得られます。目標である `w ∈ v` は命題なので、この切り詰めを除去できます。残る仕事は、`r` での正しさを用いて `u` を `col r` と比較し、したがって `w` と比較することです。
<!--/-->

```agda
          read : Σ[ r ∈ Dom ] ((r ≺ a) × (col r ≡ w)) → ⟨ w ∈ fst v ⟩
          read (r , (ra , e)) = PT.rec (snd (w ∈ fst v)) inner (cmp (up r) (≺-out r a ra))
            where
            inner : Σ[ u ∈ S ] Holds F (up r) u → ⟨ w ∈ fst v ⟩
            inner (u , fu) = val wS .snd
```

<!--en-->
The reverse half of the value equation turns a source witness into membership in `v`. Here that witness uses the predecessor `up r`, its relation to `up a`, and the table entry with value `u`; the induction hypothesis identifies `u` with `col r`, and the equation `col r ≡ w` transports the entry so that its value is `w`.
<!--zh-->
取值方程的反向一半把来源见证转换为对 `v` 的隶属。这里的来源见证由前驱 `up r`、它与 `up a` 的关系，以及取值为 `u` 的表项组成；归纳假设把 `u` 认同为 `col r`，再由等式 `col r ≡ w` 运输该表项，使其取值成为 `w`。
<!--ja-->
値の方程式の逆向きの半分は、出所の証人から `v` への所属を導きます。ここでの証人は、先行者 `up r`、それと `up a` の関係、および値 `u` をもつ表の項目からなります。帰納仮定が `u` を `col r` と同定し、さらに等式 `col r ≡ w` に沿って項目を輸送することで、その値を `w` にします。
<!--/-->

```agda
              ∣ up r , (≺-out r a ra , subst (λ t → ⟨ pr (↪ r) t ∈ fst F ⟩) (IH r ra u fu ∙ e) fu) ∣₁
```

<!--en-->
Now suppose `q` is genuinely a member of `D` and `v` satisfies the local collapse formula at `q`. The formula supplies only a propositionally truncated correct table containing `(q,v)`, but the desired set equality is a proposition, so the truncation can be eliminated. After transporting the entry from `q` to its decoded representative, `correct-val` identifies `fst v` with `col (toDom q mq)`.
<!--zh-->
现设 `q` 确为 `D` 的成员，且 `v` 在 `q` 处满足局部塌缩公式。该公式只在命题截断下给出一张含有 `(q,v)` 的正确表；但所求集合等式是命题，故可以消去此截断。把表项从 `q` 运输到其解码表示后，`correct-val` 便把 `fst v` 认同为 `col (toDom q mq)`。
<!--ja-->
ここで `q` が実際に `D` の要素であり、`v` が `q` で局所的な崩壊の論理式を満たすとします。論理式から得られるのは、`(q,v)` を含む正しい表が単に存在することだけですが、求める集合の等式は命題なので切り詰めを除去できます。項目を `q` から復号された表示へ輸送すると、`correct-val` によって `fst v` は `col (toDom q mq)` と同定されます。
<!--/-->

```agda
    colFo-val : (q : S) (mq : Mem q) (v : S) → ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩
              → fst v ≡ col (toDom q mq)
    colFo-val q mq v h = PT.rec (setIsSet (fst v) (col (toDom q mq)))
      (λ { (F , (hc , hv)) → correct-val F hc (toDom q mq) v
             (subst (λ t → ⟨ pr t (fst v) ∈ fst F ⟩) (sym (toDom-val q mq)) hv) })
```

<!--en-->
The outward reading of the collapse formula supplies the correct table and the table entry, which are the two inputs of the uniqueness lemma.
<!--zh-->
塌缩公式的向外读法供给正确表与表条目，即唯一性引理的两个输入。
<!--ja-->
崩壊の論理式の外向きの読み出しが、正しい表と表の項目を供給します。それらは、一意性の補題の二つの入力です。
<!--/-->

```agda
      (CF.colFo-out v q h)
```

<!--en-->
The local-table module is parameterized by an argument `a` of the domain and the induction hypothesis providing the collapse formula at every smaller argument. It will build, for `a`, a table whose entries at real predecessors record the collapse values and whose other entries record a default pair.
<!--zh-->
局部表模块以域的实参 `a` 与在每个更小实参处提供塌缩公式的归纳假设为参数。它将为 `a` 造一张表：其实真前驱处的条目记录塌缩值，其余条目记录默认对。
<!--ja-->
局所表のモジュールは、定義域の入力 `a` と、より小さい入力ごとに崩壊の論理式を供給する帰納の仮定によってパラメータづけられます。`a` のために、実際の先行者での項目が崩壊値を記録し、それ以外の項目が既定の対を記録する表を作ります。
<!--/-->

```agda
    module Approx (a : Dom)
                  (IH : (b : Dom) → b ≺ a → ⟨ (colʟ b ∷ up b ∷ []) ⊨ CF.colFo ⟩) where
```

<!--en-->
The default entry `ea` is the ordered pair of the carried argument with its own collapse, presented as a carrier element.
<!--zh-->
默认条目 `ea` 是被载实参与其自身塌缩组成的有序对，呈现为载体元素。
<!--ja-->
既定の項目 `ea` は、載せられた入力とその自身の崩壊の順序対で、台の要素として提示されます。
<!--/-->

```agda
      ea : S
      ea = prʟ (up a) (colʟ a)

```

<!--en-->
The body of the local formula has two disjuncts. The left disjunct says that `q` is a real predecessor of `a` and that `z` pairs `q` with a value satisfying the collapse formula. The right disjunct says that `q` is not a predecessor and `z` is the default entry. This case split is decided by excluded middle.
<!--zh-->
局部公式的体有两个析取支。左支说 `q` 是 `a` 的真前驱，且 `z` 把 `q` 与满足塌缩公式的取值配对。右支说 `q` 不是前驱，且 `z` 是默认条目。该情形分裂由排中律判定。
<!--ja-->
局所の論理式の本体は、二つの選言肢をもちます。左は、`q` が `a` の実際の先行者であり、`z` が `q` と、崩壊の論理式を満たす値とを対にすること。右は、`q` が先行者ではなく、`z` が既定の項目であること。この場合分けは排中律で決定されます。
<!--/-->

```agda
      Body : S → S → Type (ℓ-suc ℓ)
      Body z q =
          (Holds R q (up a)
             × ∥ Σ[ v ∈ S ] ((fst z ≡ pr (fst q) (fst v)) × ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩) ∥₁)
        ⊎ ((Holds R q (up a) → Empty.⊥) × (fst z ≡ fst ea))
```

<!--en-->
To distinguish the predecessor and default cases inside the object language, the relation test must mention the ordered pair formed from the varying argument `q` and the fixed point `a`. Pair expressions provide this term uniformly in the two free slots used by the local formula.
<!--zh-->
为了在对象语言中区分前驱情形与默认情形，关系检验必须提及由变化的实参 `q` 与固定点 `a` 组成的有序对。对表达式在局部公式使用的两个自由槽位中统一给出这个词项。
<!--ja-->
対象言語の中で先行者の場合と既定の場合を分けるには、変化する入力 `q` と固定された点 `a` からなる順序対を関係検査に使う必要があります。対の式は、局所的な論理式の二つの自由な枠において、この項を一様に与えます。
<!--/-->

```agda
      module PE = PairExpression

```

<!--en-->
The expression `image` denotes the pair `(q,up a)`: its first coordinate comes from the argument slot and its second is the literal carrier element representing `a`. Consequently, membership of `image` in `R` says exactly that `q` is an `R`-predecessor of `a`; it does not describe an entry of the local table.
<!--zh-->
表达式 `image` 表示有序对 `(q,up a)`：第一坐标取自实参槽，第二坐标是表示 `a` 的字面载体元素。因此，`image` 属于 `R` 恰好表示 `q` 是 `a` 的 `R` 前驱；它并不描述局部表的表项。
<!--ja-->
式 `image` は順序対 `(q,up a)` を表します。第一成分は入力の枠から取り、第二成分は `a` を表す台の要素をリテラルとして置きます。したがって `image` が `R` に属することは、ちょうど `q` が `a` の `R`-先行者であることを述べ、局所表の項目を記述するものではありません。
<!--/-->

```agda
      image : PE.Expr 2
      image = PE.pair (PE.slot (suc zero)) (PE.literal (up a))

```

<!--en-->
The formula `ψ` mirrors the two cases of `Body`. If `q R a`, the first branch requires the output `z` to pair `q` with some value satisfying `colFo` at `q`. If `q` is not a predecessor of `a`, the second branch requires `z` to equal the fixed default entry `ea`. The classical decision choosing between these branches is used later in the functionality proof, not built into the disjunction itself.
<!--zh-->
公式 `ψ` 对应 `Body` 的两种情形。若 `q R a`，第一支要求输出 `z` 把 `q` 与某个在 `q` 处满足 `colFo` 的取值配成有序对。若 `q` 不是 `a` 的前驱，第二支要求 `z` 等于固定的默认表项 `ea`。在两支之间作选择的经典判定稍后才用于函数性证明，并不是析取本身的一部分。
<!--ja-->
論理式 `ψ` は `Body` の二つの場合に対応します。`q R a` なら、第一の分岐は出力 `z` が `q` と、`q` で `colFo` を満たすある値との順序対であることを要求します。`q` が `a` の先行者でないなら、第二の分岐は `z` が固定された既定の項目 `ea` に等しいことを要求します。どちらの分岐を選ぶかという古典的な判定は後の関数性証明で使われるのであり、選言そのものに含まれるわけではありません。
<!--/-->

```agda
      opaque
        ψ : Formula S 2
        ψ = (PE.member image (con R) ∧̇ PF.pairFo)
          ∨̇ ((¬̇ PE.member image (con R)) ∧̇ (var zero ≐ con ea))

```

<!--en-->
Reading `ψ` outward preserves the truncation of its disjunction. In the predecessor branch, the pair-expression reader turns the first conjunct into `q R a`, while `PF.pair-out` says merely that `z` is `(q,v)` for some `v` satisfying `colFo` at `q`. In the default branch, the object-language negation must instead be converted into a host-level refutation of `q R a`.
<!--zh-->
向外读取 `ψ` 时，其析取外的命题截断仍被保留。在前驱分支中，对表达式的读式把第一合取项转换为 `q R a`，而 `PF.pair-out` 在命题截断下说明：对某个在 `q` 处满足 `colFo` 的 `v`，`z` 等于 `(q,v)`。在默认分支中，则须把对象语言否定转换为宿主级对 `q R a` 的反驳。
<!--ja-->
`ψ` を外向きに読むとき、選言を包む命題的切り詰めは保たれます。先行者の分岐では、対の式の読みが第一の連言肢を `q R a` へ変換し、`PF.pair-out` は、`q` で `colFo` を満たすある `v` について `z` が `(q,v)` であることを単に述べます。既定の分岐では、対象言語の否定をホストレベルでの `q R a` の反証へ変換する必要があります。
<!--/-->

```agda
        ψ-out : (z q : S) → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩ → ∥ Body z q ∥₁
        ψ-out z q = PT.map
          (λ { (inl (h1 , h2)) → inl (PE.member-out image (con R) (z ∷ q ∷ []) h1
                                         , PF.pair-out z q h2)
             ; (inr (h1 , h2)) → inr
```

<!--en-->
To obtain that host-level refutation, assume `q R a`. The inward reading of the pair expression turns this assumption into satisfaction of the membership atom, which the object-language negation rules out. The equality identifying `z` with the default entry already has the required host-level form and is retained unchanged.
<!--zh-->
为得到这份宿主级反驳，暂设 `q R a`。对表达式的向内读法把该假设转换为隶属原子式的满足，而对象语言否定排除了这种满足。把 `z` 认同为默认表项的等式已经具有所需的宿主级形式，故原样保留。
<!--ja-->
このホストレベルの反証を得るため、`q R a` と仮定します。対の式を内向きに読むと、この仮定は所属原子式の充足へ移りますが、対象言語の否定がそれを排除します。`z` を既定の項目と同定する等式はすでに必要なホストレベルの形なので、そのまま保たれます。
<!--/-->

```agda
                 ((λ k → lower (h1 (PE.member-in image (con R) (z ∷ q ∷ []) k))) , h2) })

```

<!--en-->
The inward reading injects the left branch through the pair-expression introduction and the pair-graph introduction, eliminating the truncated value into the proposition-valued satisfaction.
<!--zh-->
向内读法把左支经对表达式引入与对图引入注入，并把截断取值消去到命题值的满足之中。
<!--ja-->
内向きの読み出しは、左の分岐を、対の式の導入と対のグラフの導入を通して注入し、切り詰められた値を、命題値の充足の中へ消去します。
<!--/-->

```agda
        ψ-in : (z q : S) → Body z q → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
        ψ-in z q (inl (h1 , hv)) = PT.rec (snd ((z ∷ q ∷ []) ⊨ ψ))
          (λ { (v , (e , hc)) → ∣ inl (PE.member-in image (con R) (z ∷ q ∷ []) h1
                                     , PF.pair-in z q v e hc) ∣₁ }) hv
        ψ-in z q (inr (h1 , e)) =
```

<!--en-->
The right branch lifts the host-side refutation into the object language and carries the default equation. Both branches are injected into the truncated disjunction of the formula.
<!--zh-->
右支把宿主侧反驳提升进对象语言并携带默认等式。两支都被注入公式的截断析取。
<!--ja-->
右の分岐は、ホスト側の反駁を対象言語へ持ち上げ、既定の等式を運びます。どちらの分岐も、論理式の切り詰められた選言へ注入されます。
<!--/-->

```agda
          ∣ inr ((λ k → lift (h1 (PE.member-out image (con R) (z ∷ q ∷ []) k))) , e) ∣₁

```

<!--en-->
The helper `b≺a-of` decodes the host-side relation membership into the internal comparison: if `q` relates to `a`, then the internal index of `q` is below `a`. The decoding is by descending along the membership to recover the index.
<!--zh-->
辅助事实 `b≺a-of` 把宿主侧关系隶属解码为内部比较：若 `q` 与 `a` 有关系，则 `q` 的内部索引低于 `a`。解码方式是沿隶属下降以恢复索引。
<!--ja-->
補助の `b≺a-of` は、ホスト側の関係の所属を、内部の比較へ復号します。`q` が `a` と関係するなら、`q` の内部の添字は `a` より下です。復号は、所属を下降して添字を取り出すことによって行われます。
<!--/-->

```agda
      private
        b≺a-of : (q : S) (mq : Mem q) → Holds R q (up a) → toDom q mq ≺ a
        b≺a-of q mq h = ≺-in (toDom q mq) a
          (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val q mq)) h)

```

<!--en-->
The induction hypothesis is stated at the canonical representative `up (toDom q mq)`, whereas the local formula must be satisfied at the original carrier element `q`. The round-trip equality identifies these two presentations, and `colFo-at` transports the satisfaction proof from the canonical representative to `q`.
<!--zh-->
归纳假设陈述在典范表示 `up (toDom q mq)` 处，而局部公式必须在原载体元素 `q` 处得到满足。往返等式认同这两种呈现，`colFo-at` 随之把满足证明从典范表示运输到 `q`。
<!--ja-->
帰納仮定は正準な表示 `up (toDom q mq)` で述べられていますが、局所的な論理式は元の台の要素 `q` で満たされなければなりません。往復の等式が二つの表示を同定し、`colFo-at` が充足証明を正準な表示から `q` へ輸送します。
<!--/-->

```agda
        IHq : (q : S) (mq : Mem q) → toDom q mq ≺ a
            → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
        IHq q mq k = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (IH (toDom q mq) k)

```

<!--en-->
Replacement requires the values satisfying `ψ` at each `q ∈ D` to form a contractible fiber. The proof asks excluded middle whether `q R a`. In either case it will produce, under propositional truncation, a canonical satisfying output and a proof that every other satisfying output equals it; `mereFunct` converts this merely unique existence into contractibility.
<!--zh-->
替换要求：对每个 `q ∈ D`，满足 `ψ` 的取值构成可缩纤维。证明用排中律判定是否有 `q R a`。无论哪种情形，它都将在命题截断下给出一个满足公式的典范输出，并证明其他任何满足公式的输出都等于它；`mereFunct` 再把这种命题截断的唯一存在转换为可缩性。
<!--ja-->
置換が要求するのは、各 `q ∈ D` で `ψ` を満たす値が可縮なファイバーをなすことです。証明では排中律を用いて `q R a` かどうかを判定します。どちらの場合にも、論理式を満たす正準な出力と、それを満たすほかの出力がすべて正準な出力に等しいことの証明を、命題的切り詰めのもとで与えます。`mereFunct` は、この切り詰められた一意存在を可縮性へ変換します。
<!--/-->

```agda
        fc : (q : S) → ⟨ q ∈ˢ D ⟩ → isContr (Σ[ z ∈ S ] ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩)
        fc q mq = mereFunct ψ q (decide (lem (pr (fst q) (↪ a) ∈ fst R)))
          where
          b : Dom
          b = toDom q mq
```

<!--en-->
In the predecessor branch, the canonical output is `zb = prʟ q (colʟ b)`, whose underlying set codes `(q,col b)`; here `b` is the internal index decoded from `q`. The non-predecessor branch instead uses the default output `ea`. The local decision lemma will show, under propositional truncation, that whichever branch applies has one satisfying output and that every other satisfying output equals it.
<!--zh-->
在前驱分支中，典范输出为 `zb = prʟ q (colʟ b)`，其底层集合编码 `(q,col b)`；这里的 `b` 是从 `q` 解码出的内部索引。非前驱分支则使用默认输出 `ea`。局部判定引理将在命题截断下说明：无论哪一分支成立，都有一个满足公式的输出，且其他任何满足公式的输出都与它相等。
<!--ja-->
先行者の分岐における正準な出力は `zb = prʟ q (colʟ b)` であり、その基礎集合が `(q,col b)` を符号化します。ここで `b` は `q` から復号された内部の添字です。一方、先行者でない分岐では既定の出力 `ea` を使います。局所的な判定の補題は、どちらの場合にも論理式を満たす出力が一つあり、それを満たすほかの出力はすべてその出力に等しいことを、命題的切り詰めのもとで示します。
<!--/-->

```agda
          zb : S
          zb = prʟ q (colʟ b)
          decide : Holds R q (up a) ⊎ (Holds R q (up a) → Empty.⊥)
                 → ∥ Σ[ z ∈ S ] (⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
                                × ((z' : S) → ⟨ (z' ∷ q ∷ []) ⊨ ψ ⟩ → z' ≡ z)) ∥₁
```

<!--en-->
Assume `q R a`. The canonical output `zb` satisfies the left branch because the induction hypothesis supplies `colFo` for `col b` at `q`, while `prʟ-fst` supplies the required equality between `fst zb` and the ordered-pair code `pr (fst q) (col b)`. To prove uniqueness, an arbitrary satisfying output is read through the same two cases: a left-branch witness will be determined by `colFo-val`, while a right-branch witness contradicts the standing assumption `q R a`.
<!--zh-->
设 `q R a`。归纳假设说明 `col b` 在 `q` 处满足 `colFo`，而 `prʟ-fst` 给出 `fst zb` 与有序对编码 `pr (fst q) (col b)` 之间所需的等式，故典范输出 `zb` 满足左支。为证唯一性，把任意满足公式的输出仍按两种情形读取：左支见证将由 `colFo-val` 确定，右支见证则与既有假设 `q R a` 矛盾。
<!--ja-->
`q R a` と仮定します。帰納仮定は `col b` が `q` で `colFo` を満たすことを与え、`prʟ-fst` は `fst zb` と順序対の符号 `pr (fst q) (col b)` の間に必要な等式を与えるので、正準な出力 `zb` は左の分岐を満たします。一意性を示すため、任意の充足する出力を同じ二つの場合に分けて読みます。左の分岐の証人は `colFo-val` によって決まり、右の分岐の証人は仮定 `q R a` と矛盾します。
<!--/-->

```agda
          decide (inl h) = ∣ zb
            , ( ψ-in zb q (inl (h , ∣ colʟ b , (prʟ-fst q (colʟ b) , IHq q mq (b≺a-of q mq h)) ∣₁))
              , λ z' hz' → PT.rec (isSetS z' zb)
                  (λ { (inl (_ , hv)) → PT.rec (isSetS z' zb)
                         (λ { (v , (e , hcol)) → Σ≡Prop (λ w → snd (isL w))
```

<!--en-->
For a competing witness in the left branch, `colFo-val` identifies its second coordinate with `col b`; combining this with its pair equation proves that the whole output is `zb`. A competing right-branch witness is impossible because it contains a refutation of `q R a`. This finishes uniqueness in the predecessor case. The final line then opens the separate non-predecessor case by choosing the default output `ea`; its uniqueness proof continues in the next block.
<!--zh-->
对左支中的竞争见证，`colFo-val` 把其第二坐标认同为 `col b`；再与该见证的有序对等式合成，便证明整个输出等于 `zb`。右支中的竞争见证含有对 `q R a` 的否定，故不可能存在。至此，前驱情形的唯一性得证。末行另行开始非前驱情形并选择默认输出 `ea`；其唯一性证明将在下一代码块继续。
<!--ja-->
左の分岐にある別の証人について、`colFo-val` はその第二成分を `col b` と同定します。これを順序対の等式と合成すると、出力全体が `zb` に等しいことが従います。右の分岐にある別の証人は `q R a` の反証を含むので存在できません。これで先行者の場合の一意性が完了します。最後の行からは、既定の出力 `ea` を選ぶ、先行者でない場合が別に始まり、その一意性証明は次のコードブロックへ続きます。
<!--/-->

```agda
                                (e ∙ cong (pr (fst q)) (colFo-val q mq v hcol) ∙ sym (prʟ-fst q (colʟ b))) })
                         hv
                     ; (inr (nh , _)) → Empty.rec (nh h) })
                  (ψ-out z' q hz') ) ∣₁
          decide (inr nh) = ∣ ea
```

<!--en-->
The refuted-membership case closes the uniqueness argument. The default entry `ea` satisfies `ψ`. Reading any competing witness outward either produces a positive membership, contradicting `nh`, or gives the default-branch equality `fst z' ≡ fst ea`. In the latter case, propositionality of constructibility lifts this equality of underlying sets to the required equality `z' ≡ ea` in `S`.
<!--zh-->
否定隶属的情形闭合了唯一性论证。默认条目 `ea` 满足 `ψ`。向外读取任意竞争见证时，要么得到一条与 `nh` 矛盾的肯定隶属，要么由默认支得到 `fst z' ≡ fst ea`。在后一种情形中，可构造性证明的命题性把这条底层集合的等式提升为 `S` 中所需的等式 `z' ≡ ea`。
<!--ja-->
所属を否定する場合が一意性の議論を閉じます。既定の項目 `ea` は `ψ` を満たします。別の証人を外向きに読むと、`nh` と矛盾する肯定的な所属が得られるか、既定の分岐から `fst z' ≡ fst ea` が得られます。後者では、構成可能性の証明が命題であることにより、基礎集合のこの等式が `S` で必要な等式 `z' ≡ ea` へ持ち上がります。
<!--/-->

```agda
            , ( ψ-in ea q (inr (nh , refl))
              , λ z' hz' → PT.rec (isSetS z' ea)
                  (λ { (inl (h , _)) → Empty.rec (nh h)
                     ; (inr (_ , e)) → Σ≡Prop (λ w → snd (isL w)) e })
                  (ψ-out z' q hz') ) ∣₁
```

<!--en-->
The local recursion ranges over every `q ∈ D`. If `q R up a`, its unique value is the ordered pair of `q` with the collapse at the index presented by `q`; otherwise its value is the single default entry `ea`. Replacement applied to `ψ` and this uniqueness proof collects the resulting values into one constructible set.
<!--zh-->
这项局部递归的定义域是整个 `D`。若 `q R up a`，它的唯一取值是 `q` 与 `q` 所呈现索引的塌缩值组成的有序对；否则取同一个默认条目 `ea`。把替换应用于 `ψ` 及这份唯一性证明，便将所得取值收集为一个可构造集。
<!--ja-->
この局所再帰の定義域は `D` 全体です。`q R up a` なら、その一意な値は `q` と、`q` が表示する添字での崩壊値との順序対です。そうでなければ、値は共通の既定項 `ea` です。`ψ` とこの一意性証明に置換を適用すると、得られる値が一つの構成可能集合に集められます。
<!--/-->

```agda

        module T = Of (record { dom = D ; graph = ψ ; funct = fc }) using ( table; table-in; table-out )

```

<!--en-->
`Fa` names this replacement range. The following membership lemmas show that its elements are exactly the pairs `pr(↪ b,col b)` with `b ≺ a`, together with the top pair `pr(↪ a,col a)` contributed by the default branch.
<!--zh-->
`Fa` 表示这个由替换得到的值域。下述成员关系引理将证明，它的元素恰为满足 `b ≺ a` 的有序对 `pr(↪ b,col b)`，再加上默认分支给出的顶端有序对 `pr(↪ a,col a)`。
<!--ja-->
`Fa` は置換で得られたこの値域を表します。以下の所属補題により、その要素は `b ≺ a` を満たす順序対 `pr(↪ b,col b)` と、既定の分岐が与える最上部の順序対 `pr(↪ a,col a)` にちょうど限られることが分かります。
<!--/-->

```agda
      Fa : S
      Fa = T.table

```

<!--en-->
`Below b` states that the index `b` is at or below the current one: either strictly below, or equal. This two-case predicate drives both the introduction and the correctness of the local table.
<!--zh-->
`Below b` 陈述索引 `b` 至多等于当前索引：要么严格低于，要么相等。这个两分谓词驱动局部表的引入与正确性。
<!--ja-->
`Below b` は、添字 `b` が現在のもの以下であることを述べます。真に下か、等しいかのいずれかです。この二つの述語が、局所的な表の導入と正しさの両方を支えます。
<!--/-->

```agda
      Below : Dom → Type ℓ
      Below b = (b ≺ a) ⊎ (b ≡ a)

```

<!--en-->
For `b` at or below `a`, `Fa-in` inserts the graph entry with input `up b` and value `colʟ b`. A strict comparison uses the induction hypothesis to satisfy the first disjunct of `ψ`; an equality `b ≡ a` uses the default branch after identifying this pair with `ea`.
<!--zh-->
若 `b` 小于或等于 `a`，`Fa-in` 就把输入为 `up b`、取值为 `colʟ b` 的图条目放入 `Fa`。严格比较的情形用归纳假设满足 `ψ` 的第一个析取支；等式 `b ≡ a` 的情形则先把这个有序对等同于 `ea`，再使用默认分支。
<!--ja-->
`b` が `a` 以下なら、`Fa-in` は入力 `up b` と値 `colʟ b` からなるグラフの項を `Fa` に入れます。狭義の比較の場合は帰納仮定によって `ψ` の第一の選言肢を満たし、等式 `b ≡ a` の場合はこの順序対を `ea` と同一視して既定の分岐を使います。
<!--/-->

```agda
      Fa-in : (b : Dom) → Below b → Holds Fa (up b) (colʟ b)
      Fa-in b k = subst (λ w → ⟨ w ∈ fst Fa ⟩) (prʟ-fst (up b) (colʟ b))
        (T.table-in (up b) (prʟ (up b) (colʟ b)) (up-mem b) (ψ-in _ (up b) (bodyOf k)))
        where
        bodyOf : Below b → Body (prʟ (up b) (colʟ b)) (up b)
```

<!--en-->
In the strict case, the body contains the relation witness `b ≺ a` and the induction hypothesis saying that `colʟ b` satisfies the collapse formula at `up b`. In the equality case, irreflexivity rules out `up b R up a`, while transport along `b ≡ a` identifies the proposed pair with the default pair.
<!--zh-->
在严格情形中，公式体包含关系见证 `b ≺ a`，以及归纳假设所给出的 `colʟ b` 在 `up b` 处满足塌缩公式。在相等情形中，非自反性排除 `up b R up a`，而沿 `b ≡ a` 的传输把待证有序对等同于默认有序对。
<!--ja-->
狭義の場合、式の本体には関係の証拠 `b ≺ a` と、`colʟ b` が `up b` で崩壊の論理式を満たすという帰納仮定が入ります。等しい場合、非反射性が `up b R up a` を排除し、`b ≡ a` に沿う輸送が対象の順序対を既定の順序対と同一視します。
<!--/-->

```agda
        bodyOf (inl k) = inl (≺-out b a k , ∣ colʟ b , (prʟ-fst (up b) (colʟ b) , IH b k) ∣₁)
        bodyOf (inr e) = inr
          ( (λ h → ≺-irrefl a (≺-in a a (subst (λ t → Holds R (up t) (up a)) e h)))
          , prʟ-fst (up b) (colʟ b) ∙ cong (λ t → pr (↪ t) (col t)) e ∙ sym (prʟ-fst (up a) (colʟ a)) )

```

<!--en-->
Conversely, membership in `Fa` merely yields an index `b` with `b ≺ a` or `b ≡ a`, together with an equality identifying the member with `pr(↪ b,col b)`. The index remains under propositional truncation, so this result does not choose a representative.
<!--zh-->
反过来，属于 `Fa` 仅仅给出一个满足 `b ≺ a` 或 `b ≡ a` 的索引 `b`，以及把该成员等同于 `pr(↪ b,col b)` 的等式。索引仍处于命题截断之下，因此这个结论没有选定一个代表元。
<!--ja-->
逆に、`Fa` への所属からは、`b ≺ a` または `b ≡ a` を満たす添字 `b` と、その要素を `pr(↪ b,col b)` と同一視する等式が単に得られます。添字は命題的切り詰めの中にあるため、この結論は代表を選びません。
<!--/-->

```agda
      Fa-out : (y : S) → ⟨ y ∈ˢ Fa ⟩
             → ∥ Σ[ b ∈ Dom ] (Below b × (fst y ≡ pr (↪ b) (col b))) ∥₁
      Fa-out y hy = PT.rec squash₁
        (λ { (q , (mq , hψ)) → PT.rec squash₁
          (λ { (inl (h , hv)) → PT.map
```

<!--en-->
In the predecessor branch, `colFo-val` identifies the value supplied by the formula with the collapse at `toDom q mq`; the presentation equation for `q` then rewrites the pair into canonical form. In the default branch, the recorded pair is the one indexed by `a` itself.
<!--zh-->
在前驱分支中，`colFo-val` 把公式给出的取值等同于 `toDom q mq` 处的塌缩值，随后 `q` 的呈现等式把有序对改写为典范形式。在默认分支中，记录的有序对就是以 `a` 自身为索引的那一个。
<!--ja-->
先行者の分岐では、`colFo-val` が論理式から得た値を `toDom q mq` での崩壊値と同一視し、続いて `q` の表示等式が順序対を標準形へ書き換えます。既定の分岐で記録されるのは、`a` 自身を添字とする順序対です。
<!--/-->

```agda
                 (λ { (v , (e , hcol)) → toDom q mq
                    , (inl (b≺a-of q mq h)
                      , e ∙ cong₂ pr (sym (toDom-val q mq)) (colFo-val q mq v hcol)) })
                 hv
             ; (inr (_ , e)) → ∣ a , (inr refl , e ∙ prʟ-fst (up a) (colʟ a)) ∣₁ })
```

<!--en-->
Both the replacement reader and `ψ-out` return truncated witnesses. Since the desired conclusion is itself propositionally truncated, the proof may eliminate the outer truncation, then the inner one, without selecting either witness globally.
<!--zh-->
替换的读取引理与 `ψ-out` 都只返回经命题截断的见证。由于目标本身也经过命题截断，证明可以依次消去外层与内层截断，而无需在全局选定任何一个见证。
<!--ja-->
置換の読み出し補題と `ψ-out` は、どちらも命題的に切り詰められた証人だけを返します。目標も命題的に切り詰められているので、どちらの証人も大域的に選ぶことなく、外側、内側の順に切り詰めを除去できます。
<!--/-->

```agda
          (ψ-out y q hψ) })
        (T.table-out y hy)

```

<!--en-->
Specializing the preceding result to the ordered-pair code of `x` and `v` recovers its two coordinates. Thus a graph entry `Holds Fa x v` merely determines an index `b ≤ a` for which `fst x ≡ ↪ b` and `fst v ≡ col b`.
<!--zh-->
把上一结论用于 `x` 与 `v` 的有序对编码，便可恢复它的两个坐标。因此，图条目 `Holds Fa x v` 仅仅确定某个 `b ≤ a`，使 `fst x ≡ ↪ b` 且 `fst v ≡ col b`。
<!--ja-->
直前の結果を `x` と `v` の順序対符号に適用すると、その二つの座標を復元できます。したがってグラフの項 `Holds Fa x v` からは、`fst x ≡ ↪ b` かつ `fst v ≡ col b` を満たすある `b ≤ a` が単に得られます。
<!--/-->

```agda
      Fa-pair : (x v : S) → Holds Fa x v
              → ∥ Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v)) ∥₁
      Fa-pair x v h = PT.map step
        (Fa-out (prʟ x v) (subst (λ w → ⟨ w ∈ fst Fa ⟩) (sym (prʟ-fst x v)) h))
        where
```

<!--en-->
The transport re-points the equation at the internal pair, and the helper splits it through the injectivity of the ordered pair into the naming equation of the index and that of the collapse value.
<!--zh-->
传输把等式重新指向内部对；辅助引理经有序对的单射性把它拆成索引的命名等式与塌缩值的命名等式。
<!--ja-->
輸送は等式を内部の対に向け直し、補助が順序対の単射性を通してそれを、添字の名指しの等式と崩壊の値の名指しの等式に分けます。
<!--/-->

```agda
        step : Σ[ b ∈ Dom ] (Below b × (fst (prʟ x v) ≡ pr (↪ b) (col b)))
             → Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
        step (b , (k , e)) = b , (k , sym (fst q) , sym (snd q))
          where
          q : (fst x ≡ ↪ b) × (fst v ≡ col b)
```

<!--en-->
Applying `pr-inj` to the composite pair equality yields `fst x ≡ ↪ b` and `fst v ≡ col b`. The result expected by `Fa-pair` has the canonical coordinates first, so `step` reverses both component equalities before returning them.
<!--zh-->
把 `pr-inj` 应用于复合后的有序对等式，便得到 `fst x ≡ ↪ b` 与 `fst v ≡ col b`。`Fa-pair` 所需的结果把典范坐标置于等式左边，因此 `step` 返回前先反转这两条分量等式。
<!--ja-->
合成した順序対の等式に `pr-inj` を適用すると、`fst x ≡ ↪ b` と `fst v ≡ col b` が得られます。`Fa-pair` が要求する結果では正準な座標が等式の左辺にあるため、`step` は二つの成分の等式を反転してから返します。
<!--/-->

```agda
          q = pr-inj (sym (prʟ-fst x v) ∙ e)

```

<!--en-->
If `c ≺ b` and `b ≺ a`, transitivity gives `c ≺ a`. If instead `b ≡ a`, substituting this equality into `c ≺ b` gives the same conclusion. These are exactly the two cases of `Below b`.
<!--zh-->
若 `c ≺ b` 且 `b ≺ a`，传递性给出 `c ≺ a`。若改为 `b ≡ a`，把这个等式代入 `c ≺ b` 也得到同一结论。这正是 `Below b` 的两种情形。
<!--ja-->
`c ≺ b` かつ `b ≺ a` なら、推移性から `c ≺ a` が従います。一方 `b ≡ a` なら、この等式を `c ≺ b` に代入して同じ結論を得ます。これが `Below b` の二つの場合です。
<!--/-->

```agda
      below-trans : {c b : Dom} → c ≺ b → Below b → c ≺ a
      below-trans cb (inl k) = ≺-trans cb k
      below-trans {c} cb (inr e) = subst (c ≺_) e cb

```

<!--en-->
To prove `Correct Fa R`, fix an actual entry `(x,v)` of `Fa`. The paired reader gives only a truncated index representing this entry, but both `Complete Fa R x` and `ValueIs Fa R x v` are propositions. Their conjunction is therefore a valid target for eliminating that truncation.
<!--zh-->
为证明 `Correct Fa R`，先固定 `Fa` 中一个实际条目 `(x,v)`。配对读取引理只给出一个经命题截断的索引来表示该条目，但 `Complete Fa R x` 与 `ValueIs Fa R x v` 都是命题。因此，可以合法地向它们的合取消去这层截断。
<!--ja-->
`Correct Fa R` を示すため、`Fa` の実際の項 `(x,v)` を固定します。対の読み出しから得られる、この項を表示する添字は命題的に切り詰められています。しかし `Complete Fa R x` と `ValueIs Fa R x v` はともに命題なので、その連言へ切り詰めを除去できます。
<!--/-->

```agda
      Fa-correct : Correct Fa R
      Fa-correct x v hxv = PT.rec
        (isProp× (isPropΠ (λ _ → isPropΠ (λ _ → squash₁)))
                 (isPropΠ (λ w → isProp× (isPropΠ (λ _ → squash₁))
                                          (isPropΠ (λ _ → snd (fst w ∈ fst v))))))
```

<!--en-->
Suppose the chosen entry is represented by `b ≤ a`, so that `x` presents `b` and `v` has underlying set `col b`. Completeness must give every `R`-predecessor of `x` a value in `Fa`; the value condition must prove, for each `w`, that `w ∈ v` exactly when some such predecessor is paired with `w` in `Fa`.
<!--zh-->
设所选条目由某个 `b ≤ a` 表示，于是 `x` 呈现 `b`，而 `v` 的底层集合是 `col b`。完备性要求 `x` 的每个 `R` 前驱都在 `Fa` 中有取值；取值条件则要求对每个 `w` 证明：`w ∈ v` 当且仅当某个这样的前驱在 `Fa` 中与 `w` 配对。
<!--ja-->
選んだ項がある `b ≤ a` で表され、`x` が `b` を表示し、`v` の基礎集合が `col b` であるとします。完全性では、`x` の各 `R`-先行者が `Fa` で値をもつことを示します。値条件では各 `w` について、`w ∈ v` と、そのような先行者の一つが `Fa` で `w` と対になっていることとの同値を示します。
<!--/-->

```agda
        build (Fa-pair x v hxv)
        where
        build : Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
              → Complete Fa R x × ValueIs Fa R x v
        build (b , (k , ex , ev)) = cmp , (λ w → fwd w , bwd w)
```

<!--en-->
The central conversion takes a coded predecessor `y R x` to a strict comparison in `Dom`. The entry representation identifies `fst x` with the represented member `↪ b`, rather than identifying the carrier element `x` with the external index `b`. After `Rsub` places `y` in `D`, `toDom` recovers the index that can be compared with `b`.
<!--zh-->
这里的关键转换，是把编码关系中的前驱 `y R x` 化为 `Dom` 中的严格比较。条目的表示把 `fst x` 与被表示成员 `↪ b` 等同，并不把载体元素 `x` 与外围索引 `b` 等同。`Rsub` 先证明 `y` 属于 `D`，随后 `toDom` 才恢复出可与 `b` 比较的索引。
<!--ja-->
ここで中心となる変換は、符号化された先行者 `y R x` を `Dom` 上の狭義比較へ移すことです。項目の表示が同一視するのは `fst x` と表示された要素 `↪ b` であり、台の要素 `x` と外部の添字 `b` ではありません。`Rsub` がまず `y` を `D` に入れ、その後で `toDom` が `b` と比較できる添字を復元します。
<!--/-->

```agda
          where
```

<!--en-->
From `y R x`, the containment hypothesis supplies `y ∈ D`, so `toDom y my` defines an index `c`. Transporting the relation witness along the presentation equations for `y` and `x` proves `c ≺ b`; the second coordinate records that `↪ c` is the underlying set of `y`.
<!--zh-->
由 `y R x`，端点包含假设先给出 `y ∈ D`，故 `toDom y my` 定义了一个索引 `c`。沿 `y` 与 `x` 的呈现等式传输关系见证，即得 `c ≺ b`；第二个分量则记录 `↪ c` 是 `y` 的底层集合。
<!--ja-->
`y R x` から端点の包含仮定によって `y ∈ D` が得られるので、`toDom y my` は添字 `c` を定めます。`y` と `x` の表示等式に沿って関係の証拠を輸送すると `c ≺ b` が従い、第二成分には `↪ c` が `y` の基礎集合であることが記録されます。
<!--/-->

```agda
          pred : (y : S) → Holds R y x → Σ[ c ∈ Dom ] ((c ≺ b) × (↪ c ≡ fst y))
          pred y hy = c , (≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩)
                              (sym (toDom-val y my)) (sym ex) hy) , toDom-val y my)
            where
            my : Mem y
```

<!--en-->
The proof `my` is precisely the first endpoint membership supplied by `Rsub`; it is the evidence needed to form `toDom y my`. Since membership in `D` is a proposition, using this evidence does not add a choice of presentation.
<!--zh-->
证明 `my` 正是 `Rsub` 给出的第一个端点成员关系，也是构造 `toDom y my` 所需的证据。由于属于 `D` 是一个命题，使用这份证据不会额外选择一种呈现。
<!--ja-->
証明 `my` は `Rsub` が与える第一端点の所属そのものであり、`toDom y my` を作るために必要な根拠です。`D` への所属は命題なので、この根拠を使っても表示の選択が新たに加わることはありません。
<!--/-->

```agda
            my = Rsub y x hy .fst
            c : Dom
            c = toDom y my

```

<!--en-->
For a predecessor `y R x`, let `c` be the index just recovered. The witness for completeness is the value `colʟ c`; `Fa-in` supplies the canonical entry at `up c`, and transport along `↪ c ≡ fst y` turns it into the required entry at `y`. Transitivity through `b ≤ a` ensures that `c` lies below `a`.
<!--zh-->
对前驱 `y R x`，令 `c` 为刚恢复的索引。完备性的取值见证是 `colʟ c`；`Fa-in` 先给出输入为 `up c` 的典范条目，再沿 `↪ c ≡ fst y` 传输为输入在 `y` 处的所需条目。经由 `b ≤ a` 的传递性保证 `c` 严格低于 `a`。
<!--ja-->
先行者 `y R x` に対し、直前に復元した添字を `c` とします。完全性の値の証人は `colʟ c` です。`Fa-in` が入力 `up c` での標準的な項を与え、それを `↪ c ≡ fst y` に沿って輸送すると、入力 `y` で必要な項になります。`b ≤ a` を介する推移性により、`c` は `a` より真に下にあります。
<!--/-->

```agda
          cmp : Complete Fa R x
          cmp y hy = ∣ colʟ c , subst (λ t → ⟨ pr t (col c) ∈ fst Fa ⟩) ec
                                 (Fa-in c (inl (below-trans cb k))) ∣₁
            where
            c = pred y hy .fst
```

<!--en-->
The two projections of `pred y hy` are now named `cb` and `ec`: `cb` is the strict comparison `c ≺ b`, while `ec` identifies the canonical representative `↪ c` with the actual input `y`. They provide, respectively, the bound needed by `Fa-in` and the transport to `y`.
<!--zh-->
现在把 `pred y hy` 的两个投影记作 `cb` 与 `ec`：`cb` 是严格比较 `c ≺ b`，`ec` 则把典范代表 `↪ c` 等同于实际输入 `y`。前者提供 `Fa-in` 所需的界，后者负责把条目传输到 `y`。
<!--ja-->
ここで `pred y hy` の二つの射影を `cb` と `ec` と名づけます。`cb` は狭義比較 `c ≺ b` であり、`ec` は標準的な代表 `↪ c` を実際の入力 `y` と同一視します。前者は `Fa-in` に必要な境界を、後者は項を `y` へ運ぶ輸送を与えます。
<!--/-->

```agda
            cb = pred y hy .snd .fst
            ec = pred y hy .snd .snd

```

<!--en-->
For the forward half of `ValueIs`, rewrite `w ∈ v` as `fst w ∈ col b`. The outward collapse lemma merely gives `r ≺ b` and `col r ≡ fst w`; these data produce an `R`-edge from `up r` to `x` and a table entry pairing `up r` with `w`.
<!--zh-->
为证明 `ValueIs` 的正向一半，先把 `w ∈ v` 改写为 `fst w ∈ col b`。塌缩的向外引理仅仅给出 `r ≺ b` 与 `col r ≡ fst w`；这些数据构造出从 `up r` 到 `x` 的一条 `R` 边，以及在表中把 `up r` 与 `w` 配对的条目。
<!--ja-->
`ValueIs` の順方向では、`w ∈ v` を `fst w ∈ col b` と書き換えます。崩壊の外向き補題から単に得られる `r ≺ b` と `col r ≡ fst w` により、`up r` から `x` への `R`-辺と、`up r` を `w` に対応させる表の項が構成できます。
<!--/-->

```agda
          fwd : (w : S) → ⟨ fst w ∈ fst v ⟩ → Src Fa R x w
          fwd w w∈ = PT.map read (col-out b (fst w) (subst (λ t → ⟨ fst w ∈ t ⟩) (sym ev) w∈))
            where
            read : Σ[ r ∈ Dom ] ((r ≺ b) × (col r ≡ fst w)) → Σ[ y ∈ S ] (Holds R y x × Holds Fa y w)
            read (r , (rb , er)) = up r
```

<!--en-->
The two memberships are transported along the equation of the index and the strict comparison, placing both the relation and the table membership at the named predecessor.
<!--zh-->
两条隶属沿索引的等式与严格比较传输，把关系与表的隶属都落在被点名的前驱处。
<!--ja-->
二つの所属は添字の等式と狭義の比較に沿って輸送され、関係と表の所属の両方が名指された先行者のところに置かれます。
<!--/-->

```agda
              , ( subst (λ t → ⟨ pr (↪ r) t ∈ fst R ⟩) ex (≺-out r b rb)
                , subst (λ t → ⟨ pr (↪ r) t ∈ fst Fa ⟩) er (Fa-in r (inl (below-trans rb k))) )

```

<!--en-->
For the reverse half, a witness of `Src Fa R x w` merely supplies some `y` with `y R x` and a table entry from `y` to `w`. The target `fst w ∈ fst v` is a proposition, so the truncated source witness and then the truncated table reading may both be eliminated into it.
<!--zh-->
在反向一半中，`Src Fa R x w` 的见证仅仅给出某个 `y`，满足 `y R x`，并且表中有从 `y` 到 `w` 的条目。目标 `fst w ∈ fst v` 是命题，因此可以向它依次消去来源见证与表读取结果中的命题截断。
<!--ja-->
逆方向では、`Src Fa R x w` の証人から、`y R x` を満たし、表で `y` から `w` への項をもつような `y` が単に得られます。目標 `fst w ∈ fst v` は命題なので、出所の証人と表の読み出しに含まれる命題的切り詰めを順にそこへ除去できます。
<!--/-->

```agda
          bwd : (w : S) → Src Fa R x w → ⟨ fst w ∈ fst v ⟩
          bwd w = PT.rec (snd (fst w ∈ fst v)) (λ { (y , (hy , fy)) →
            PT.rec (snd (fst w ∈ fst v)) (read y hy) (Fa-pair y w fy) })
            where
            read : (y : S) → Holds R y x
```

<!--en-->
Reading the table entry gives an index `c`, an equation identifying `y` with `↪ c`, and an equation identifying `w` with `col c`. Combining the first equation with `y R x` and the representation of `x` by `b` yields `c ≺ b`; hence `col-in` places `col c` in `col b`, and the remaining equations transport this membership to `w ∈ v`.
<!--zh-->
读取表条目得到一个索引 `c`、把 `y` 等同于 `↪ c` 的等式，以及把 `w` 等同于 `col c` 的等式。把第一个等式、`y R x` 与 `x` 由 `b` 表示这一事实合并，便得到 `c ≺ b`；于是 `col-in` 给出 `col c ∈ col b`，其余等式再把这条成员关系传输为 `w ∈ v`。
<!--ja-->
表の項を読むと、添字 `c`、`y` を `↪ c` と同一視する等式、そして `w` を `col c` と同一視する等式が得られます。最初の等式を `y R x` および `x` が `b` で表示されることと合わせると `c ≺ b` が従います。そこで `col-in` が `col c ∈ col b` を与え、残りの等式がこの所属を `w ∈ v` へ輸送します。
<!--/-->

```agda
                 → Σ[ c ∈ Dom ] (Below c × (↪ c ≡ fst y) × (col c ≡ fst w))
                 → ⟨ fst w ∈ fst v ⟩
            read y hy (c , (_ , ey , ew)) =
              subst2 (λ s t → ⟨ s ∈ t ⟩) ew ev (col-in b c cb)
              where
```

<!--en-->
The strict comparison between `c` and `b` is filled from the two naming equations and the relation witness, completing the predecessor data.
<!--zh-->
`c` 与 `b` 之间的严格比较由两条命名等式与关系见证填充，前驱数据随之完备。
<!--ja-->
`c` と `b` の間の狭義の比較は、二つの名指しの等式と関係の証人から満たされ、先行者のデータがそろいます。
<!--/-->

```agda
              cb : c ≺ b
              cb = ≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩) (sym ey) (sym ex) hy)

```

<!--en-->
The local table satisfies the graph formula at the top element, with the default entry witnessing the value clause. This is the induction step of the whole section.
<!--zh-->
局部表在顶端元素处满足图公式，默认条目见证取值子句。这是本节的归纳步。
<!--ja-->
局所的な表は頂点の要素でグラフの論理式を満たし、既定の項目が値の節の証人になります。これがこの節の帰納の段階です。
<!--/-->

```agda
      approx-step : ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
      approx-step = CF.colFo-in (colʟ a) (up a) Fa Fa-correct (Fa-in a (inr refl))
```

<!--en-->
Well-founded induction now proves the collapse formula at every `a : Dom`. The induction hypothesis supplies the formula at each strict predecessor; `Approx.approx-step` uses those witnesses to build a correct local table at `a`. The conclusion concerns every index in `Dom`; it does not require `D` itself to have already been identified with an ordinal.
<!--zh-->
现在用良基归纳证明塌缩公式在每个 `a : Dom` 处成立。归纳假设为每个严格前驱给出该公式的满足见证，`Approx.approx-step` 再用这些见证在 `a` 处构造一张正确的局部表。结论遍及 `Dom` 中的每个索引，并不要求事先把 `D` 等同于某个序数。
<!--ja-->
ここで整礎帰納により、崩壊の論理式が各 `a : Dom` で成り立つことを示します。帰納仮定は各狭義先行者での充足証拠を与え、`Approx.approx-step` はそれらを用いて `a` で正しい局所表を構成します。結論は `Dom` のすべての添字に関するものであり、`D` 自体がすでに順序数と同一視されていることは必要ありません。
<!--/-->

```agda
    approx : (a : Dom) → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
    approx = W.induction {P = λ a → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩}
      (λ a IH → Approx.approx-step a IH)

```

<!--en-->
For `q : S` with `mq : Mem q`, the preceding induction gives the formula at the canonical representative `up (toDom q mq)`. The round-trip equality `up-toDom q mq` identifies that representative with `q`, and `colFo-at` transports satisfaction to the original member of `D`.
<!--zh-->
给定 `q : S` 与 `mq : Mem q`，前面的归纳先在典范表示 `up (toDom q mq)` 处给出公式。往返等式 `up-toDom q mq` 把该表示与 `q` 等同，`colFo-at` 再把满足证明运输到 `D` 的这个原成员处。
<!--ja-->
`q : S` と `mq : Mem q` に対して、直前の帰納はまず正準な表示 `up (toDom q mq)` で論理式を与えます。往復の等式 `up-toDom q mq` がその表示を `q` と同一視し、`colFo-at` が充足証明を `D` のもとの要素へ輸送します。
<!--/-->

```agda
    approx-at : (q : S) (mq : Mem q) → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
    approx-at q mq = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (approx (toDom q mq))
```

<!--en-->
The recursion `otR` uses `D` as its domain and `CF.colFo` as its value relation. At a member `q ∈ D`, its chosen value is the collapse at the small index `toDom q mq`; the preceding approximation proves that this value satisfies the formula at `q`.
<!--zh-->
递归 `otR` 以 `D` 为定义域，以 `CF.colFo` 为取值关系。对成员 `q ∈ D`，选定的取值是小索引 `toDom q mq` 处的塌缩值；前面的逼近结果证明这个取值在 `q` 处满足公式。
<!--ja-->
再帰 `otR` は `D` を定義域、`CF.colFo` を値関係とします。要素 `q ∈ D` で選ばれる値は、小さい添字 `toDom q mq` での崩壊値です。直前の近似により、この値が `q` で論理式を満たすことが示されます。
<!--/-->

```agda
    private
      otR : Recursion
      otR = record
        { dom   = D
        ; graph = CF.colFo
```

<!--en-->
The `funct` field must make the fiber of values satisfying `CF.colFo` at each `q ∈ D` contractible. Its center is `colʟ (toDom q mq)` together with `approx-at q mq`. For any competing `(v,hv)`, `colFo-val` identifies the underlying set of `v` with the same collapse value; propositionality of constructibility and of satisfaction then lifts that equality first to `v` and finally to the whole fiber element.
<!--zh-->
字段 `funct` 必须证明：对每个 `q ∈ D`，满足 `CF.colFo` 的取值所成纤维是可缩的。其中心由 `colʟ (toDom q mq)` 与 `approx-at q mq` 组成。对任意竞争元素 `(v,hv)`，`colFo-val` 把 `v` 的底层集合与同一个塌缩值等同；可构造性证明与满足证明的命题性再依次把这条等式提升到 `v`，最后提升到整个纤维元素。
<!--ja-->
フィールド `funct` は、各 `q ∈ D` で `CF.colFo` を満たす値のファイバーが可縮であることを示さなければなりません。その中心は `colʟ (toDom q mq)` と `approx-at q mq` です。別の要素 `(v,hv)` に対して、`colFo-val` は `v` の基礎集合を同じ崩壊値と同一視します。構成可能性の証明と充足の証明が命題であることにより、この等式はまず `v` の等式へ、最後にファイバーの要素全体の等式へ持ち上がります。
<!--/-->

```agda
        ; funct = λ q mq → (colʟ (toDom q mq) , approx-at q mq)
            , λ { (v , hv) → Σ≡Prop (λ w → snd ((w ∷ q ∷ []) ⊨ CF.colFo))
                (sym (Σ≡Prop (λ w → snd (isL w)) (colFo-val q mq v hv))) } }

```

<!--en-->
The generic replacement construction `Of` now turns this functional recursion into its value table. It provides both directions of the membership characterization: values satisfying the recursion enter the table, and every table member comes from some input in `D` with the required formula witness.
<!--zh-->
通用的替换构造 `Of` 现在把这项函数性递归变成它的取值表，并给出成员关系刻画的两个方向：满足递归关系的取值进入该表，而表的每个成员都来自 `D` 中某个输入，并带有所需的公式见证。
<!--ja-->
一般の置換構成 `Of` は、この関数的な再帰をその値の表へ変えます。また所属の特徴づけを両方向に与えます。再帰関係を満たす値は表に入り、表の各要素は、必要な論理式の証拠を伴う `D` のある入力から生じます。
<!--/-->

```agda
      module OT = Of otR using ( table; table-in; table-out )

```

<!--en-->
`otL` is the replacement range of `otR`, hence an element of `L`. Its underlying set collects all collapse values `col b` for `b : Dom`, without requiring those values to have distinct indices. At this point the construction uses only this exact-range description; ordinality of the whole range is a further conclusion.
<!--zh-->
`otL` 是 `otR` 经替换得到的值域，因此是 `L` 的一个元素。它的底层集合收集所有 `b : Dom` 的塌缩值 `col b`，无需这些取值来自互不相同的索引。这里的构造只使用这一精确值域刻画；整个值域的序数性是还需进一步推出的结论。
<!--ja-->
`otL` は `otR` の置換による値域であり、したがって `L` の要素です。その基礎集合はすべての `b : Dom` に対する崩壊値 `col b` を集めますが、それらの値が互いに異なる添字から来る必要はありません。ここではこの正確な値域の記述だけを用い、値域全体の順序数性はさらに導くべき結論として残します。
<!--/-->

```agda
    otL : S
    otL = OT.table

```

<!--en-->
For each `b : Dom`, the approximation proves that `colʟ b` is a value of `otR` at `up b`. The introduction half of replacement therefore gives `col b ∈ fst otL`.
<!--zh-->
对每个 `b : Dom`，逼近引理证明 `colʟ b` 是 `otR` 在 `up b` 处的取值。因此，替换的引入方向给出 `col b ∈ fst otL`。
<!--ja-->
各 `b : Dom` について、近似補題は `colʟ b` が `up b` における `otR` の値であることを示します。したがって置換の導入方向から `col b ∈ fst otL` が得られます。
<!--/-->

```agda
    otL-in : (b : Dom) → ⟨ col b ∈ fst otL ⟩
    otL-in b = OT.table-in (up b) (colʟ b) (up-mem b) (approx b)

```

<!--en-->
Conversely, every `y ∈ fst otL` merely has an index `b : Dom` with `col b ≡ y`. The result deliberately retains propositional truncation, so it describes the exact range without choosing a preimage for every member.
<!--zh-->
反过来，每个 `y ∈ fst otL` 仅仅具有某个索引 `b : Dom`，满足 `col b ≡ y`。结论特意保留命题截断，因此它刻画了精确值域，却没有为每个成员选定一个原像。
<!--ja-->
逆に、各 `y ∈ fst otL` について、`col b ≡ y` を満たす添字 `b : Dom` が単に存在します。結論には意図的に命題的切り詰めが残されているため、各要素の原像を選ぶことなく正確な値域を記述しています。
<!--/-->

```agda
    otL-out : (y : V ℓ) → ⟨ y ∈ fst otL ⟩ → ∥ Σ[ b ∈ Dom ] (col b ≡ y) ∥₁
    otL-out y hy = PT.map (λ { (q , (mq , h)) → toDom q mq , sym (colFo-val q mq yS h) })
      (OT.table-out yS hy)
      where
      yS : S
```

<!--en-->
To apply the replacement reader, the ambient set `y` must be regarded as an element of the constructible carrier. Downward closure of constructibility supplies this packaging from `y ∈ fst otL` and the fact that `otL` is constructible.
<!--zh-->
为了应用替换的读取引理，需要把外围集合 `y` 看作可构造论域中的元素。由 `y ∈ fst otL` 以及 `otL` 的可构造性，可构造性的向下封闭正好给出这一打包。
<!--ja-->
置換の読み出しを適用するには、周囲の集合 `y` を構成可能な領域の要素として扱う必要があります。`y ∈ fst otL` と `otL` の構成可能性から、構成可能性の下方閉性がこの組を与えます。
<!--/-->

```agda
      yS = y , isL-trans {x = fst otL} {y = y} hy (snd otL)

```

<!--en-->
Applying the recursion-graph construction to `otR` collects ordered pairs rather than bare values. For every input in `D` it records the input together with its uniquely determined collapse value, and it supplies the corresponding inward and outward readings, single-valuedness, and exact-domain statement.
<!--zh-->
把递归图构造应用于 `otR`，所收集的是有序对而非裸取值。它为 `D` 中每个输入记录该输入及其唯一确定的塌缩值，并给出相应的内向与外向读取、单值性以及精确定义域陈述。
<!--ja-->
再帰グラフの構成を `otR` に適用すると、裸の値ではなく順序対が集められます。`D` の各入力について、その入力と一意に定まる崩壊値を記録し、対応する内向きと外向きの読み、一価性、そして定義域が正確に `D` であることを与えます。
<!--/-->

```agda
    module CT = RecursionGraph otR using ( F; F-in; F-out; pair-out; sv; dm )

```

<!--en-->
`colTable` is the graph set constructed from `otR` inside `L`. Its canonical entry at `b : Dom` is `pr(↪ b,col b)`: the stored input is the represented member `↪ b` of `D`, while `b` itself remains an index in the external small presentation.
<!--zh-->
`colTable` 是在 `L` 内由 `otR` 构造出的函数图集合。对 `b : Dom`，其典范条目是 `pr(↪ b,col b)`：表中存储的输入是 `D` 的被表示成员 `↪ b`，而 `b` 本身仍是外围小表示中的索引。
<!--ja-->
`colTable` は、`L` の内部で `otR` から構成されたグラフの集合です。`b : Dom` における正準な項目は `pr(↪ b,col b)` です。表に保存される入力は `D` の表示された要素 `↪ b` であり、`b` 自体は外部の小さな表示に属する添字のままです。
<!--/-->

```agda
    colTable : S
    colTable = CT.F

```

<!--en-->
At the canonical representative `up b`, the recursion graph initially records the value `col (toDom (up b) (up-mem b))`. The presentation equation induces equality of this recovered index with `b`; transporting the second coordinate along its image under `col` yields the advertised pair `pr(↪ b,col b)`.
<!--zh-->
在典范代表 `up b` 处，递归图最初记录的取值是 `col (toDom (up b) (up-mem b))`。呈现等式诱导出这个恢复索引与 `b` 的相等；沿该等式在 `col` 下的像传输第二坐标，便得到所陈述的有序对 `pr(↪ b,col b)`。
<!--ja-->
標準的な代表 `up b` において、再帰グラフが最初に記録する値は `col (toDom (up b) (up-mem b))` です。表示等式から、この復元された添字と `b` との等式が得られます。その `col` による像に沿って第二座標を輸送すると、主張された順序対 `pr(↪ b,col b)` が得られます。
<!--/-->

```agda
    colTable-in : (b : Dom) → ⟨ pr (↪ b) (col b) ∈ fst colTable ⟩
    colTable-in b = subst (λ t → ⟨ pr (↪ b) t ∈ fst colTable ⟩)
      (cong col (Dom≡ (toDom-val (up b) (up-mem b)))) (CT.F-in (up b) (up-mem b))

```

<!--en-->
Conversely, `colTable-out` says that any member `y` of the graph is merely equal in its underlying set to `pr(↪ b,col b)` for some `b : Dom`. The index remains under propositional truncation, so this outward reading characterizes the graph without selecting a representing index for each member.
<!--zh-->
反过来，`colTable-out` 说明：对函数图的任意成员 `y`，仅仅存在某个 `b : Dom`，使 `fst y ≡ pr(↪ b,col b)`。该索引仍处于命题截断之下，因此这项向外读法只刻画函数图，并未为每个成员选定一个表示索引。
<!--ja-->
逆に `colTable-out` は、グラフの任意の要素 `y` について、ある `b : Dom` に対する `fst y ≡ pr(↪ b,col b)` が単に成り立つと述べます。その添字は命題的切り詰めの中にあるため、この外向きの読みはグラフを特徴づけますが、各要素を表示する添字を選びません。
<!--/-->

```agda
    colTable-out : (y : S) → ⟨ y ∈ˢ colTable ⟩
                 → ∥ Σ[ b ∈ Dom ] (fst y ≡ pr (↪ b) (col b)) ∥₁
    colTable-out y hy = PT.map (λ { (q , mq , e) → toDom q mq
      , e ∙ cong (λ t → pr t (col (toDom q mq))) (sym (toDom-val q mq)) }) (CT.F-out (fst y) hy)
```

<!--en-->
The fiber predicate says that a member `v` paired with `x` is the collapse value of the index that `x` presents, with the presentation membership as data.
<!--zh-->
纤维谓词说：与 `x` 配对的成员 `v` 是 `x` 所呈现索引的塌缩值，并以呈现隶属为数据。
<!--ja-->
ファイバーの述語は、`x` と対にされる要素 `v` が `x` の提示する添字の崩壊の値であることを述べ、提示の所属をデータとして伴います。
<!--/-->

```agda
    Fib : S → S → Type (ℓ-suc ℓ)
    Fib x v = Σ[ mx ∈ Mem x ] (fst v ≡ col (toDom x mx))

```

<!--en-->
For fixed `x` and `v`, `Fib x v` is a proposition. Membership `mx : Mem x` is proposition-valued, and for each such `mx` the equality `fst v ≡ col (toDom x mx)` is a proposition because `V` is a set. Thus the dependent sum carries no additional choice data.
<!--zh-->
固定 `x` 与 `v` 后，`Fib x v` 是命题。成员关系 `mx : Mem x` 取值于命题；对每个这样的 `mx`，由于 `V` 是集合，等式 `fst v ≡ col (toDom x mx)` 也是命题。因此，这个依值和不携带额外的选择数据。
<!--ja-->
`x` と `v` を固定すると、`Fib x v` は命題です。所属 `mx : Mem x` は命題値であり、各 `mx` に対する等式 `fst v ≡ col (toDom x mx)` も、`V` が集合であるため命題です。したがって、この依存和は追加の選択データをもちません。
<!--/-->

```agda
    isPropFib : (x v : S) → isProp (Fib x v)
    isPropFib x v = isPropΣ (isPropMem x) (λ mx → setIsSet (fst v) (col (toDom x mx)))

```

<!--en-->
Membership of the encoded pair of `x` and `v` in `colTable` therefore yields untruncated information: `x` belongs to `D`, and the underlying set of `v` equals the collapse at the index presented by `x`. Propositionality of `Fib x v` is what permits the graph reader's truncated witness to be eliminated.
<!--zh-->
因此，`x` 与 `v` 的编码有序对属于 `colTable` 时，可以得到不带截断的信息：`x` 属于 `D`，且 `v` 的底层集合等于 `x` 所呈现索引处的塌缩值。正是 `Fib x v` 的命题性允许消去图读取结果中的截断。
<!--ja-->
したがって、`x` と `v` の符号化された順序対が `colTable` に属すれば、切り詰められていない情報が得られます。すなわち `x` は `D` に属し、`v` の基礎集合は `x` が表示する添字での崩壊値に等しいという情報です。`Fib x v` が命題であるため、グラフの読み出しに含まれる切り詰めを除去できます。
<!--/-->

```agda
    colTable-pair : (x v : S) → Holds colTable x v → Fib x v
    colTable-pair = CT.pair-out
```

<!--en-->
## The graph as a coded injection
<!--zh-->
## 作为编码单射的图
<!--ja-->
## 符号化された単射としてのグラフ
<!--/-->

<!--en-->
To study when the collapse graph codes an injection, fix `D`, `R`, and the endpoint condition `Rsub`. This condition says only that both endpoints of every recorded `R`-edge lie in `D`; well-foundedness, transitivity, and trichotomy remain separate hypotheses.
<!--zh-->
为研究塌缩图何时编码一条单射，固定 `D`、`R` 以及端点条件 `Rsub`。这个条件只说明每条被 `R` 记录的边，其两个端点都属于 `D`；良基性、传递性与三歧性仍是彼此独立的假设。
<!--ja-->
崩壊グラフがいつ単射を符号化するかを調べるため、`D`、`R`、および端点条件 `Rsub` を固定します。この条件が述べるのは、`R` に記録された各辺の両端点が `D` に属することだけです。整礎性、推移性、三分法は別々の仮定として残ります。
<!--/-->

```agda
module Code (D R : S)
            (Rsub : (y x : S) → Holds R y x
                  → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

```

<!--en-->
The small presentation `Dom`, its coded relation `_≺_`, and the conversions between members of `D` and their indices are the same ones used above. The coding argument will build on that collapse construction rather than introduce a second relation.
<!--zh-->
这里沿用上文的小表示 `Dom`、其编码关系 `_≺_`，以及 `D` 的成员与索引之间的转换。接下来的编码论证建立在同一塌缩构造上，并不引入第二条关系。
<!--ja-->
ここでも、先に用いた小さい表示 `Dom`、その符号化された関係 `_≺_`、および `D` の要素と添字との間の変換を使います。以下の符号化の議論は同じ崩壊構成に基づき、別の関係を導入しません。
<!--/-->

```agda
  open Internal D R Rsub public

```

<!--en-->
The hypotheses play different roles. Well-foundedness defines `col` by recursion, while transitivity proves each collapse value is an ordinal and hence constructible; the local-table assembly also uses the chapter's classical parameter `lem`. Together these ingredients construct the exact range `otL` and the graph `colTable`, and yield single-valuedness, exact domain, and containment of all graph values in `otL`. Trichotomy is added only in the next module, where it proves injectivity.
<!--zh-->
这些假设各有不同作用。良基性通过递归定义 `col`，传递性证明每个塌缩值是序数，因而可构造；局部表的装配还使用本章的经典参数 `lem`。这些材料共同构造出精确值域 `otL` 与函数图 `colTable`，并给出单值性、精确定义域，以及所有函数图取值都属于 `otL`。三歧性只在下一个模块中加入，用于证明单射性。
<!--ja-->
仮定の役割はそれぞれ異なります。整礎性は再帰によって `col` を定義し、推移性は各崩壊値が順序数であり、したがって構成可能であることを示します。局所表の組み立てでは、この章の古典的な引数 `lem` も使います。これらを合わせて正確な値域 `otL` とグラフ `colTable` を構成し、一価性、正確な定義域、すべてのグラフ値が `otL` に属することを得ます。三分法は次のモジュールで初めて加えられ、単射性の証明に使われます。
<!--/-->

```agda
  module Conjuncts (wf : WellFounded _≺_)
                   (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

```

<!--en-->
With these two hypotheses fixed, the preceding graph construction supplies `col`, `otL`, and `colTable` together with their membership characterizations. At this stage equal inputs have equal recorded values, but equality of recorded values has not yet been shown to recover equal inputs.
<!--zh-->
固定这两个假设后，前面的图构造给出 `col`、`otL` 与 `colTable`，以及它们的成员关系刻画。在这一阶段，相同输入具有相同的记录取值，但尚未证明记录取值相等能够推出输入相等。
<!--ja-->
この二つの仮定を固定すると、先のグラフ構成から `col`、`otL`、`colTable` と、それぞれの所属の特徴づけが得られます。この段階では、同じ入力には同じ値が記録されますが、記録された値の等しさから入力の等しさを復元できることはまだ示されていません。
<!--/-->

```agda
    open Graph wf ≺-trans public

```

<!--en-->
In the two-slot environment `γ`, slot zero contains `colTable` and slot one contains `D`. The formulas for single-valuedness and exact domain can therefore refer to the graph and its intended domain by these fixed positions.
<!--zh-->
在二槽位环境 `γ` 中，零号槽放置 `colTable`，一号槽放置 `D`。单值性与精确定义域公式因而可以通过这两个固定位置引用函数图及其预定定义域。
<!--ja-->
二つのスロットをもつ環境 `γ` では、スロット 0 に `colTable`、スロット 1 に `D` が置かれます。したがって、一価性と正確な定義域の論理式は、これらの固定位置によってグラフとその意図された定義域を参照できます。
<!--/-->

```agda
    γ : S ^ 2
    γ = colTable ∷ D ∷ []

```

<!--en-->
The first condition is single-valuedness: if `colTable` contains pairs with the same input and values `y` and `y'`, then `fst y ≡ fst y'`. It follows from uniqueness of the recursion value and does not assert that every input has a value.
<!--zh-->
第一项条件是单值性：若 `colTable` 含有输入相同、取值分别为 `y` 与 `y'` 的两个有序对，则 `fst y ≡ fst y'`。这来自递归取值的唯一性，本身并不断言每个输入都有取值。
<!--ja-->
第一の条件は一価性です。`colTable` が同じ入力に対して値 `y` と `y'` をもつ二つの順序対を含むなら、`fst y ≡ fst y'` が成り立ちます。これは再帰値の一意性から従うものであり、各入力が値をもつこと自体は主張しません。
<!--/-->

```agda
    sv : ⟨ γ ⊨ svAt zero ⟩
    sv = CT.sv

```

<!--en-->
The domain condition is an equivalence: an input has some value in `colTable` exactly when it belongs to `D`. Thus it includes both exclusion of entries outside `D` and totality on every member of `D`; the existential value in the latter direction remains propositionally truncated.
<!--zh-->
定义域条件是一条等价：一个输入在 `colTable` 中具有某个取值，当且仅当它属于 `D`。因此，它既排除定义域外的条目，也断言 `D` 的每个成员都有取值；后一个方向中的存在取值仍保留命题截断。
<!--ja-->
定義域条件は同値です。ある入力が `colTable` で何らかの値をもつことと、その入力が `D` に属することとは同値です。したがって、この条件は `D` の外の項を排除すると同時に、`D` の各要素上での全域性も述べます。後者の方向での値の存在は命題的に切り詰められたままです。
<!--/-->

```agda
    dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
    dm = CT.dm

```

<!--en-->
The range condition follows from the paired graph reading: an entry from `x` to `y` gives a domain witness for `x` and identifies `fst y` with the corresponding collapse value, which `otL-in` places in `otL`. This establishes only that graph values lie in `otL`; injectivity of `colTable` still requires the trichotomy hypothesis introduced next.
<!--zh-->
值域条件来自函数图的配对读取：从 `x` 到 `y` 的条目给出 `x` 属于定义域的见证，并把 `fst y` 等同于相应的塌缩值，而 `otL-in` 证明该塌缩值属于 `otL`。这里仅证明函数图的取值都落在 `otL` 中；`colTable` 的单射性仍需下一步引入的三歧性假设。
<!--ja-->
値域条件はグラフの対の読み出しから従います。`x` から `y` への項は、`x` が定義域に属する証拠を与え、`fst y` を対応する崩壊値と同一視します。その崩壊値は `otL-in` によって `otL` に属します。ここで示したのはグラフの値が `otL` に入ることだけであり、`colTable` の単射性には次に導入する三分法の仮定がなお必要です。
<!--/-->

```agda
    ran : (x y : S) → Holds colTable x y → ⟨ fst y ∈ fst otL ⟩
    ran x y h = subst (λ t → ⟨ t ∈ fst otL ⟩) (sym (snd (colTable-pair x y h)))
      (otL-in (toDom x (fst (colTable-pair x y h))))
```

<!--en-->
The collapse table is already total and single-valued on `D`, and its values already lie in the exact range `otL`. The remaining condition for a coded injection is input uniqueness. Assume trichotomy on the small domain: for any `a` and `b`, either `a ≺ b`, `a ≡ b`, or `b ≺ a`. Together with the well-foundedness and transitivity fixed by the enclosing module, this comparison will make equal collapse values force equal indices.
<!--zh-->
塌缩表已经在 `D` 上全域且单值，其取值也已落在精确值域 `otL` 中。要得到编码单射，只余下输入唯一性这一项条件。现在假设小定义域上的三歧性：对任意 `a` 与 `b`，或者 `a ≺ b`，或者 `a ≡ b`，或者 `b ≺ a`。结合外层模块已经固定的良基性与传递性，这项比较将使相等的塌缩值迫使索引相等。
<!--ja-->
崩壊表はすでに `D` 上で全域的かつ一価であり、その値は正確な値域 `otL` に属しています。符号化された単射を得るために残る条件は、入力の一意性です。そこで小さな定義域上の三分法を仮定します。任意の `a` と `b` に対して、`a ≺ b`、`a ≡ b`、`b ≺ a` のいずれかが成り立つという仮定です。外側のモジュールですでに固定された整礎性と推移性にこの比較を合わせると、崩壊値の等しさから添字の等しさを導けます。
<!--/-->

```agda
    module Inj (tri : (a b : Dom) → (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a))) where

```

<!--en-->
To prove that `col` is injective, fix `a` and `b` with `col a ≡ col b` and split their trichotomy. The equality case is already the desired conclusion. Each strict case instead turns a genuine membership between the two collapse values into self-membership after transport along their equality, so it suffices to refute that impossible membership.
<!--zh-->
为证明 `col` 单射，固定满足 `col a ≡ col b` 的 `a` 与 `b`，并按二者的三歧性分类。相等情形已经给出所需结论。两个严格情形则各自把两个塌缩值之间真实成立的隶属关系沿该等式搬运成自隶属，故只需反驳这一不可能的隶属关系。
<!--ja-->
`col` の単射性を示すため、`col a ≡ col b` を満たす `a` と `b` を固定し、両者の三分法で場合分けします。等しい場合は、それ自体が求める結論です。二つの狭義の場合には、崩壊値の間に実際に成り立つ所属を、その等しさに沿って自己所属へ移せるので、この不可能な所属を反駁すれば十分です。
<!--/-->

```agda
      col-inj : (a b : Dom) → col a ≡ col b → a ≡ b
      col-inj a b e = go (tri a b)
        where
        go : (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a)) → a ≡ b
        go (inl k)       = Empty.rec (∈-irrefl (col b)
```

<!--en-->
In the left case, `a` precedes `b`, so `col a` is a member of `col b`; transporting along the value equality makes `col b` a member of itself, which irreflexivity refutes. The middle case returns the equality directly. The right case is symmetric: `col a` would be a member of itself.
<!--zh-->
左支中 `a` 先于 `b`，故 `col a` 属于 `col b`；沿取值等式运输使 `col b` 属于自身，被非自反性反驳。中支直接返回等式。右支对称：`col a` 将属于自身。
<!--ja-->
左の場合、`a` は `b` に先行するので `col a` は `col b` の要素です。値の等式に沿って輸送すると `col b` が自分自身の要素になり、非反射性で反駁されます。中間の場合は等式をそのまま返します。右の場合は対称的に、`col a` が自分自身の要素になります。
<!--/-->

```agda
          (subst (λ t → ⟨ t ∈ col b ⟩) e (col-in b a k)))
        go (inr (inl q)) = q
        go (inr (inr k)) = Empty.rec (∈-irrefl (col a)
          (subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b k)))

```

<!--en-->
The object-language clause `injAt` asks whether two graph entries with the same output have the same input. Reading `p` and `q` with `colTable-pair` produces membership proofs `m` and `m'` for the two inputs in `D`, together with equations identifying the common output `y` with both recovered collapse values. Composing those equations supplies the hypothesis needed by `col-inj`.
<!--zh-->
对象语言子句 `injAt` 要求：具有同一输出的两条图表项必须具有同一输入。用 `colTable-pair` 读取 `p` 与 `q`，便得到两个输入属于 `D` 的证明 `m` 与 `m'`，以及把共同输出 `y` 分别认同为两个恢复所得塌缩值的等式。复合这两条等式，就得到应用 `col-inj` 所需的前提。
<!--ja-->
対象言語の条項 `injAt` は、同じ出力をもつ二つのグラフ項目が同じ入力をもつことを要求します。`p` と `q` を `colTable-pair` で読むと、二つの入力が `D` に属することを示す `m` と `m'`、および共通の出力 `y` を、復元された二つの崩壊値のそれぞれと同一視する等式が得られます。その二つの等式を合成すれば、`col-inj` に必要な仮定になります。
<!--/-->

```agda
      ij : ⟨ γ ⊨ injAt zero ⟩
      ij = injAt-in zero γ (λ y x x' p q →
        let (m , e)   = colTable-pair x y p
            (m' , e') = colTable-pair x' y q
        in sym (toDom-val x m)
```

<!--en-->
The recovered indices are equal by `col-inj`, and the round-trip lemma transports that equality back to the underlying sets of the original carrier elements. The three equations compose into the required equality.
<!--zh-->
恢复的索引由 `col-inj` 相等，而往返引理把该等式搬回原载体元素的底层集合。三条等式复合成所需等式。
<!--ja-->
復元された添字は `col-inj` によって等しく、往復の補題がその等しさを、もとの台の要素の基礎の集合へ運び戻します。三つの等式が合成されて、必要な等しさになります。
<!--/-->

```agda
         ∙ cong ↪ (col-inj (toDom x m) (toDom x' m') (sym e ∙ e'))
         ∙ toDom-val x' m')

```

<!--en-->
The four fields now have distinct sources. The recursion graph supplies single-valuedness and the exact domain clause; `colTable-pair` and `otL-in` give the range bound; trichotomy supplied the missing injectivity clause. Packaging these proofs yields `InjCode colTable D otL`. Thus `colTable` is a coded injection only inside the module carrying `tri`; this record makes no separate claim that `otL` has been packaged here as an ordinal.
<!--zh-->
这四个字段来自不同的论证。递归图给出单值性与精确定义域子句；`colTable-pair` 和 `otL-in` 给出值域界；三歧性则补上缺少的单射性子句。把这些证明封装起来便得到 `InjCode colTable D otL`。因此，只有在携带 `tri` 的模块内部，`colTable` 才是编码单射；这份记录没有另行断言本章已经把 `otL` 封装为序数。
<!--ja-->
四つのフィールドは、それぞれ異なる議論から得られます。再帰グラフが一価性と正確な定義域の条項を与え、`colTable-pair` と `otL-in` が値域の上界を与え、三分法が残っていた単射性の条項を与えます。これらの証明をまとめると `InjCode colTable D otL` が得られます。したがって `colTable` が符号化された単射になるのは `tri` をもつモジュールの内部だけです。また、このレコードは `otL` の順序数性が本章で定理としてまとめられたとは主張しません。
<!--/-->

```agda
      code : InjCode colTable D otL
      code = sv , dm , ij , ran
```

<!--en-->
The converse construction is intentionally local to chosen source and target sets `X` and `Y`. For every `x ∈ X`, `pre` must choose an index `b : Dom` with `col b ≡ fst x`; this is a collapse preimage, and it need not be a predecessor of any fixed point of the relation. The second argument `bound` proves that the represented original input `↪ b` lies in `Y`. These data are extra obligations at each use of the inverse interface, rather than consequences of `otL-out` alone.
<!--zh-->
反向构造只针对选定的源集 `X` 与目标集 `Y`。对每个 `x ∈ X`，`pre` 必须选出索引 `b : Dom` 并满足 `col b ≡ fst x`；它是塌缩原像，不一定是这条关系中某个固定点的前驱。第二项参数 `bound` 证明所表示的原输入 `↪ b` 属于 `Y`。每次使用逆向接口时都必须另行提供这些数据，它们不能仅由 `otL-out` 自动得到。
<!--ja-->
逆向きの構成は、選んだ始域 `X` と終域 `Y` に限って行います。各 `x ∈ X` に対し、`pre` は `col b ≡ fst x` を満たす添字 `b : Dom` を選ばなければなりません。これは崩壊の原像であり、関係のある固定した点の先行者であるとは限りません。第二の引数 `bound` は、表示された元の入力 `↪ b` が `Y` に属することを証明します。逆向きのインターフェースを使うたびにこれらのデータを別途与える必要があり、`otL-out` だけから自動的に得られるものではありません。
<!--/-->

```agda
      module Inverse (X Y : S)
        (pre : (x : S) → ⟨ fst x ∈ fst X ⟩ → Σ[ b ∈ Dom ] (col b ≡ fst x))
        (bound : (x : S) (mx : ⟨ fst x ∈ fst X ⟩) → ⟨ ↪ (pre x mx .fst) ∈ fst Y ⟩) where

```

<!--en-->
Membership in the source set is recorded as a type, so that the argument can carry it alongside each element being mapped.
<!--zh-->
源集的隶属被记录为类型，使论证能把它与被映射的每个元素并肩携带。
<!--ja-->
源の集合への所属は型として記録され、議論が、写す各要素とともにそれを運べるようにします。
<!--/-->

```agda
        SourceMem : S → Type (ℓ-suc ℓ)
        SourceMem x = ⟨ fst x ∈ fst X ⟩

```

<!--en-->
For `x ∈ X`, let `b` be the collapse preimage selected by `pre`. The inverse function returns `up b`, the constructible carrier element whose underlying set is the represented member `↪ b` of the original domain. The proof argument `mx` is needed because the selected preimage may depend on the evidence that `x` lies in the chosen source.
<!--zh-->
对 `x ∈ X`，令 `b` 为 `pre` 选出的塌缩原像。逆函数返回 `up b`，即底层集合为原定义域中被表示成员 `↪ b` 的可构造载体元素。这里需要证明参数 `mx`，因为所选原像可以依赖于 `x` 属于指定源集的证据。
<!--ja-->
`x ∈ X` に対し、`b` を `pre` が選んだ崩壊の原像とします。逆関数は `up b`、すなわち元の定義域で表示された要素 `↪ b` を基礎集合にもつ構成可能な台の要素を返します。選ばれる原像は `x` が指定された始域に属する証拠に依存しうるため、証明引数 `mx` が必要です。
<!--/-->

```agda
        fn : (x : S) → SourceMem x → S
        fn x mx = up (pre x mx .fst)

```

<!--en-->
The defining formula reads the existing table in the converse direction. In the environment `y ∷ x ∷ []`, `y` is the proposed output of the inverse map and `x` is its input, while `appC colTable zero (suc zero)` asserts the original table entry `Holds colTable y x`. No new collapse table is assumed; the two coordinates of the old graph are simply assigned their inverse roles.
<!--zh-->
定义公式沿反方向读取已有的表。在环境 `y ∷ x ∷ []` 中，`y` 是逆映射的候选输出，`x` 是其输入，而 `appC colTable zero (suc zero)` 断言原表项 `Holds colTable y x`。这里没有假设一张新的塌缩表，只是让旧图的两个坐标承担逆向角色。
<!--ja-->
定義する論理式は、既存の表を逆向きに読みます。環境 `y ∷ x ∷ []` では、`y` が逆写像の候補となる出力、`x` がその入力であり、`appC colTable zero (suc zero)` は元の表項目 `Holds colTable y x` を主張します。新しい崩壊表を仮定するのではなく、古いグラフの二つの座標に逆向きの役割を与えています。
<!--/-->

```agda
        opaque
          graph : Formula S 2
          graph = appC colTable zero (suc zero)

```

<!--en-->
The adequacy equation identifies the satisfaction of the swapped graph formula with the membership of the pair in the collapse table, so both readings of the table can be used interchangeably.
<!--zh-->
充分性等式把交换后图公式的满足等同于该对在塌缩表中的隶属，使表的两种读法可互换。
<!--ja-->
妥当性の等式が、入れ替えたグラフの論理式の充足を、崩壊の表での対の所属と同一視します。だから表の二つの読み出しは相互に代用できます。
<!--/-->

```agda
          at : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ ≡ Holds colTable y x
          at y x = cong ⟨_⟩ (appC-adequate colTable zero (suc zero) (y ∷ x ∷ []))

```

<!--en-->
It remains to show that the converse formula has only the selected value. From `Holds colTable y x`, `colTable-pair` recovers an index presenting the candidate output `y` and an equation saying that this index collapses to the inverse input `x`. The selected index from `pre` also collapses to `x`; `col-inj` therefore identifies the two indices, and `up-toDom` transports that index equality back to `y ≡ fn x mx`.
<!--zh-->
还需证明反向公式只能取到所选的值。由 `Holds colTable y x`，`colTable-pair` 恢复一个表示候选输出 `y` 的索引，并给出该索引的塌缩值等于逆映射输入 `x` 的等式。`pre` 选出的索引也塌缩到 `x`；因此 `col-inj` 认同这两个索引，`up-toDom` 再把索引等式搬回 `y ≡ fn x mx`。
<!--ja-->
次に、逆向きの論理式が選ばれた値だけをもつことを示します。`Holds colTable y x` から、`colTable-pair` は候補出力 `y` を表示する添字と、その添字の崩壊値が逆写像の入力 `x` に等しいという等式を復元します。`pre` が選んだ添字も `x` へ崩壊します。したがって `col-inj` が二つの添字を同一視し、`up-toDom` がその添字の等しさを `y ≡ fn x mx` へ戻します。
<!--/-->

```agda
        only : (x : S) (mx : SourceMem x) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x mx
        only x mx y hy = sym (up-toDom y my)
          ∙ cong up (col-inj (toDom y my) (pre x mx .fst) (sym (f .snd) ∙ sym (pre x mx .snd)))
          where
          f = colTable-pair y x (transport (at y x) hy)
```

<!--en-->
The first projection of `f` is the membership proof `my : Mem y`. It is the evidence needed to form the recovered index `toDom y my` and to apply the round-trip lemma; it is not itself that index.
<!--zh-->
`f` 的第一投影是成员关系证明 `my : Mem y`。这份证据用于构造恢复所得的索引 `toDom y my` 并应用往返引理；它本身并不是该索引。
<!--ja-->
`f` の第一射影は所属の証明 `my : Mem y` です。この証拠によって、復元される添字 `toDom y my` を作り、往復の補題を適用できます。`my` 自体がその添字なのではありません。
<!--/-->

```agda
          my = f .fst

```

<!--en-->
These ingredients form a `DefinableMap` from `X` to `Y`. Its external function is `fn`, and `bound` supplies the codomain field. For the defining clause, start with `colTable-in b` for the selected preimage `b`; substitute `col b ≡ fst x` in the output coordinate, then use `at` in the reverse direction to turn the resulting table membership into satisfaction of the converse graph formula.
<!--zh-->
这些材料组成一项从 `X` 到 `Y` 的 `DefinableMap`。其外围函数是 `fn`，而 `bound` 提供陪域字段。为证明定义子句，先对所选原像 `b` 使用 `colTable-in b`；再沿 `col b ≡ fst x` 替换输出坐标，最后反向使用 `at`，把所得表隶属关系变成反向图公式的满足证明。
<!--ja-->
これらの材料から、`X` から `Y` への `DefinableMap` を作ります。その外部関数は `fn` であり、`bound` が終域のフィールドを与えます。定義の条項では、選んだ原像 `b` に対する `colTable-in b` から始めます。出力の座標を `col b ≡ fst x` に沿って置き換え、最後に `at` を逆向きに使って、得られた表への所属を逆向きのグラフ論理式の充足へ変えます。
<!--/-->

```agda
        M : DefinableMap
        M = record
          { dom = X ; cod = Y ; fn = fn ; into = bound ; graph = graph
          ; defines = λ x mx → transport (sym (at (fn x mx) x))
              (subst (λ w → ⟨ pr (↪ (pre x mx .fst)) w ∈ fst colTable ⟩)
```

<!--en-->
The `defines` field starts from the canonical entry `colTable-in b` and transports its output coordinate along the preimage equation `col b ≡ fst x`. The adequacy equality `at` then turns that table membership into satisfaction of the converse graph formula, while `only` supplies the required uniqueness of the value.
<!--zh-->
字段 `defines` 从典范条目 `colTable-in b` 出发，沿原像等式 `col b ≡ fst x` 运输其输出坐标。充分性等式 `at` 随后把这条表成员关系变成反向图公式的满足，而 `only` 则给出所需的取值唯一性。
<!--ja-->
フィールド `defines` は正準な項目 `colTable-in b` から始め、その出力座標を原像の等式 `col b ≡ fst x` に沿って輸送します。妥当性の等式 `at` がその表への所属を逆向きのグラフ論理式の充足へ変え、`only` が必要な値の一意性を与えます。
<!--/-->

```agda
                (pre x mx .snd)
                (colTable-in (pre x mx .fst)))
          ; only = only }

```

<!--en-->
The inverse function is injective for a direct reason. If `fn x mx` and `fn x' mx'` have equal underlying sets, then these sets are `↪ b` and `↪ b'` for the indices selected by `pre`; presentation injectivity `Dom≡` gives `b ≡ b'`. Applying `col` and composing with the two equations stored by `pre` yields `fst x ≡ fst x'`. This proof uses injectivity of the small presentation at `Dom≡`; `col-inj` was used earlier to prove uniqueness of the converse formula, not in this equality chain.
<!--zh-->
逆函数的单射性有一项直接理由。若 `fn x mx` 与 `fn x' mx'` 的底层集合相等，那么这两个集合分别是 `pre` 所选索引 `b` 与 `b'` 的 `↪ b` 和 `↪ b'`；表示的单射性 `Dom≡` 因而给出 `b ≡ b'`。对该等式应用 `col`，再与 `pre` 保存的两条等式复合，便得到 `fst x ≡ fst x'`。这段证明在 `Dom≡` 处使用小表示的单射性；`col-inj` 已在前文用于证明反向公式的取值唯一性，并未出现在这条等式链中。
<!--ja-->
逆関数の単射性には直接の理由があります。`fn x mx` と `fn x' mx'` の基礎集合が等しいなら、それらは `pre` が選んだ添字 `b` と `b'` に対する `↪ b` と `↪ b'` です。表示の単射性 `Dom≡` によって `b ≡ b'` が得られます。この等式に `col` を作用させ、`pre` が保持する二つの等式と合成すれば、`fst x ≡ fst x'` が従います。この証明が `Dom≡` で使うのは小さな表示の単射性です。`col-inj` は先に逆向きの論理式の値の一意性を示すために使われましたが、この等式の列には現れません。
<!--/-->

```agda
        inj : (x : S) (mx : SourceMem x) (x' : S) (mx' : SourceMem x')
            → fst (fn x mx) ≡ fst (fn x' mx') → fst x ≡ fst x'
        inj x mx x' mx' e = sym (pre x mx .snd) ∙ cong col (Dom≡ e) ∙ pre x' mx' .snd

```

<!--en-->
Applying the general definable-injection construction to `M` and `inj` packages the restricted converse as `InjL X Y`, a propositionally truncated existence claim for a coded injection. Its scope is exactly the supplied data: every member of `X` has a chosen collapse preimage, and the represented original input lies in `Y`. It supplies neither an unconditional inverse on all of `otL` nor a bijection record.
<!--zh-->
把一般的可定义单射构造应用于 `M` 与 `inj`，便把这项受限反向映射封装为 `InjL X Y`，即编码单射存在性的命题截断陈述。它的范围恰由所给数据限定：`X` 的每个成员都有一个选定的塌缩原像，并且所表示的原输入属于 `Y`。它既不提供整个 `otL` 上的无条件逆映射，也不提供双射记录。
<!--ja-->
一般の定義可能単射の構成を `M` と `inj` に適用すると、この制限された逆向きの写像が `InjL X Y`、すなわち符号化された単射の存在を命題的に切り詰めた主張としてまとめられます。その範囲は与えたデータによって正確に限られています。`X` の各要素には選ばれた崩壊の原像があり、表示された元の入力は `Y` に属します。これは `otL` 全体に対する無条件の逆写像も、全単射のレコードも与えません。
<!--/-->

```agda
        injL : InjL X Y
        injL = DefinableInj.injL M inj
```
