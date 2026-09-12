<!--en-->
# Formula expressions for coded recursion

The coded satisfaction recursion must decide, inside `L`, questions of the form: does the environment `γ` satisfy the coded formula `c`? To recognize a compound value such as a Kuratowski pair while keeping the description bounded, its witnesses must themselves be elements of the model. For a pair `q` with components `u` and `v`, a constructible set `s` is needed with `s` a member of `q` and `u`, `v` members of `s`, and the reading formula binds all three at once, evaluating the two component conditions in the assignment `v, u, s` followed by the old assignment, with the old slots preserved under the shift.

The chapter builds this once, as a structural reader on a small expression language of assignment slots, constructible literals, numerals, and Kuratowski pairs, and proves it adequate in both directions. The outward direction starts from a satisfaction judgment, eliminates its three truncated existentials into a path proposition, and composes the pairing equation with the recursive component paths. The inward direction chooses the explicit internal elements of the two subexpressions and obtains their common constructible container, without extracting any choice from a truncation.

The same reader then specializes in several directions. Membership of an expression's value in the denotation of a term uses transitivity of `L`: the ambient value's membership in the constructible interpretation of the term proves that value constructible, so it can serve as a model element; this is a genuine construction, distinct from the proposition-valued target restriction that licenses eliminating a truncation. Extensional set descriptions are an ordinary pair of universally quantified implications, with no outer truncation; they characterize a candidate set rather than construct one. The arity-tag recognizers read two nested pairing layers, the arity paired with a tag-and-payload code. Finally the successor and environment-extension formulas are lifted by bounded absoluteness, whose transfer rests on the established transitive-model setup together with the compatibility of lookups under projection. The environment-extension formula closes the chapter.
<!--zh-->
# 码化递归所用的公式表达式

码化的满足关系递归要在 `L` 内部判定形如「环境 `γ` 是否满足码 `c` 所示公式」的问题。要用有界公式识别 Kuratowski 对这样的复合取值，其见证本身必须是模型元素。对分量 `u`、`v` 的配对 `q`，需要一个可构造集合 `s`，使 `s` 属于 `q`，而 `u`、`v` 属于 `s`；读式一次性绑定这三者，并在「`v, u, s` 接原赋值」的扩展赋值中求取两个分量条件，原槽位在移位下保持不变。

本章把这件事一次做好：在由赋值槽位、可构造字面常元、数码与 Kuratowski 对组成的小表达式语言上建立一条结构读式，并证明其双向充分性。向外方向从满足判断出发，把三层截断存在消去到取值为命题的路径中，再将配对等式与递归的分量路径串联。向内方向为两个子表达式选定显式的内部元素，并取得它们共同的可构造容器，而不从任何截断中抽取选择。

同一读式随后沿几个方向特化。表达式取值属于词项所指的隶属关系使用 `L` 的传递性：该周遭取值属于词项的可构造解释这一事实证明了取值可构造，故它能充当模型元素；这是一次真正的构造，与「截断只能消去到取值为命题的目标」这一限制不同。外延集合描述是一对普通的全称蕴含，外层没有截断；它刻画一个候选集合，而不构造它。元数标签识别器读取两层嵌套的配对：元数与「标签加载荷」之对。最后，后继公式与环境扩展公式经有界绝对性抬升，其转换立足于既有的传递模型设置，以及查值在投影下的相容性。本章以环境扩展公式收尾。
<!--ja-->
# 符号化再帰のための論理式表現

符号化された充足関係の再帰は、`L` の内部で「環境 `γ` は符号 `c` の論理式を充足するか」という形の問いを判定しなければなりません。Kuratowski 対のような複合的な値を有界論理式で認識するには、証人自身が模型の要素でなければなりません。成分 `u` と `v` をもつ対 `q` に対しては、`s` が `q` に属し、`u` と `v` が `s` に属する構成可能集合 `s` が要ります。読みの論理式はこの三者を一度に束縛し、`v, u, s` に元の割り当てを続けた拡張割り当てのもとで二つの成分条件を評価します。元のスロットはずらしの下で保たれます。

本章はこれを一度だけ組み立てます。代入スロット、構成可能なリテラル、数項、Kuratowski 対からなる小さな式の言語上の構造的な読みを与え、その双方向の妥当性を証明します。外向きの方向は充足の判断から出発し、三つの命題的切り捨てを受けた存在を命題値のパスへ消去し、対の等式を帰納的な成分のパスと連結します。内向きの方向は二つの部分式の明示的な内部要素を選び、それらの共通の構成可能コンテナを取得します。截断から選択を取り出すことは一切ありません。

同じ読みはいくつもの方向に特殊化されます。式の値がある項の指示への所属は `L` の推移性を用います。周囲の値が項の構成可能な解釈に属するという事実がその値の構成可能性を証明し、それによって値は模型の要素として働けます。これは実際の構成であって、截断の消去を正当化する命題値の対象という制限とは別物です。外延的な集合の記述は普通の全称含意の対であり、外側に截断はなく、候補となる集合を構成するのではなく特徴づけます。アリティ付きタグの認識器は二層の入れ子の対、すなわちアリティと「タグとペイロードの対」を読みます。最後に、後者と環境拡張の論理式は有界絶対性によって持ち上げられます。その転送は確立された推移的モデルの設定と、射影の下での参照の相容性に依拠します。環境拡張の論理式が本章を閉じます。
<!--/-->

<!--en-->
To keep a first-order description of a compound value in the bounded fragment, fixed pieces are named by constants and each witness is bounded. Everything here takes place at one fixed level `ℓ`: the ambient hierarchy is `V ℓ`, and the model whose elements the bounded quantifiers range over is the constructible one sitting inside it. Since a satisfaction judgment compares truth values, the facts the formulas assert are propositions of the truth algebra at level `ℓ-suc ℓ`.
<!--zh-->
要让复合集合取值的一阶描述留在有界片段中，固定部件由常元命名，每个见证都受集合界定。这里的一切都固定在一个层 `ℓ` 上：周遭层级是 `V ℓ`，有界量词所遍历其元素的模型，是栖身于其中的可构造模型。由于满足判断比较的是真值，这些公式所断言的事实便是层 `ℓ-suc ℓ` 的真值代数中的命题。
<!--ja-->
複合的な集合の値を一階の有界論理式で記述するには、固定された部分を定数で名指し、各証人を集合で限界づけます。ここでのすべては、ひとつの固定されたレベル `ℓ` の上で行われます。周囲の階層は `V ℓ` であり、有界量化子がその要素を渡る模型は、その中に置かれた構成可能模型です。充足の判断は真理値を比較するものなので、これらの論理式が主張する事実は、レベル `ℓ-suc ℓ` の真理値代数の命題になります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Expressions {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
Two sides of one distinction run through the chapter. Out in the hierarchy, the structure `𝒮ᵥ` interprets the first-order language over `V ℓ`, and Kuratowski pairing there is the operation `pr`. Inside the model, the same language is reinterpreted over constructible sets. A clause that recognizes a compound value must therefore be readable in both places at once, and each adequacy statement below says exactly that: the truth value of the internal formula, read in the model, is identified, as a path, with the corresponding ambient statement about `pr` and the projected assignment.
<!--zh-->
一条区分的两面贯穿全章。在层级之外，结构 `𝒮ᵥ` 在 `V ℓ` 上解释一阶语言，那里的 Kuratowski 配对正是运算 `pr`。在模型之内，同一语言被重新解释于可构造集合之上。因此，识别复合取值的一条子句必须能同时在两处读出；而下面的每条充分性陈述说的恰是这件事：内部公式在模型中读出的真值，作为一条路径，被等同于关于 `pr` 与投影赋值的相应周遭陈述。
<!--ja-->
ひとつの区別の二つの側面が本章を貫きます。階層の外では、構造 `𝒮ᵥ` が `V ℓ` の上で一階の言語を解釈し、そこの Kuratowski 対が演算 `pr` です。模型の内側では、同じ言語が構成可能集合の上で改めて解釈されます。したがって複合的な値を認識する節は、両方の場所で同時に読めなければならず、以下の各妥当性の主張が述べるのはまさにそのことです。内部の論理式の模型での真理値が、経路として、`pr` と射影された割り当てについての対応する周囲の主張と同一視されるのです。
<!--/-->

```agda
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
```

<!--en-->
An element of the constructible model is an ambient set together with a proof that it is constructible. Transitivity of `L` is what lets bounded witnesses move between the two sides: a member of a constructible set is itself constructible, by `isL-trans`, and so becomes an element of the model in its own right. Bounded absoluteness does the corresponding work for formulas. A Δ₀ formula about the hierarchy, all of whose constants name constructible sets, means the same inside `L`; the constant bounding recorded by the `BoundedFo` data is precisely the hypothesis this transfer needs. The successor and environment-extension formulas are already proved on the hierarchy side, and lifting them into the model is a matter of applying this transfer.
<!--zh-->
可构造模型的一个元素是「周遭集合连同它可构造的证明」。`L` 的传递性使有界见证能在两侧之间移动：由 `isL-trans`，可构造集合的成员本身可构造，因而自己就能充当模型元素。有界绝对性则为公式做相应的工作：一条关于层级、且所有常元都命名可构造集合的 Δ₀ 公式，在 `L` 内意义不变；`BoundedFo` 数据记录的常元有界性正是这一转换所需的前提。后继公式与环境扩展公式已在层级一侧证得，把它们抬入模型只需施用这一转换。
<!--ja-->
構成可能模型の要素とは、周囲の集合に「それが構成可能である」という証明を添えたものです。`L` の推移性が、有界な証人が両側の間を移れるようにします。`isL-trans` により、構成可能集合の要素はそれ自身構成可能であり、したがってそれ自体が模型の要素になれます。有界絶対性は論理式について対応する仕事をします。階層についての、すべての定数が構成可能集合を名指す Δ₀ 論理式は、`L` の内部でも意味を変えません。`BoundedFo` データが記録する定数の有界性は、この転送が要る前提そのものです。後者と環境拡張の論理式はすでに階層の側で証明されており、模型への持ち上げはこの転送を適用することにほかなりません。
<!--/-->

```agda
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import FOL.Manipulation.ConstantBounding using ( BoundedFo )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo )
open import L.Coding.Environment {ℓ}
  using ( sucAt; Δ₀-sucAt; sucAt-adequate; consAt; Δ₀-consAt; consAt-adequate
```

<!--en-->
The numerals need one compatibility fact. The internal numeral `numeralL k` realizes the von Neumann natural `k` inside the model, and `numeralL-fst` identifies its projection with the ambient `# k`; both directions of the numeral clause lean on this. Because several clauses quantify over finitely many slots at once, environments are shifted along a reindexing of slots. One logical form recurs throughout: an adequacy statement is a path of truth values, obtained from the two implications of an equivalence of propositions, and the bounded quantifiers of the object language are read as truncated existence.
<!--zh-->
数码需要一条相容性事实。内部数码 `numeralL k` 在模型内实现冯·诺伊曼自然数 `k`，而 `numeralL-fst` 把它的投影与周遭的 `# k` 等同起来；数码子句的两个方向都依赖于此。由于若干子句要同时对有穷多个槽位量化，环境沿槽位的重标定而移动。一种逻辑形式贯穿全章：充分性陈述是由命题等价的两个蕴含得到的真值路径，而对象语言的有界量词被读作截断存在。
<!--ja-->
数項にはひとつの相容性の事実が必要です。内部の数項 `numeralL k` はフォン・ノイマンの自然数 `k` を模型の内部で実現し、`numeralL-fst` はその射影を周囲の `# k` と同一視します。数項の節の両方向はこれに依存します。いくつかの節は有限個のスロットについて同時に量化するので、環境はスロットの再索引付けに沿って移されます。ひとつの論理的な形式が全章を貫きます。妥当性の主張は命題の同値の二つの含意から得られる真理値の経路であり、対象言語の有界量化子は命題的切り捨てを受けた存在として読まれます。
<!--/-->

```agda
        ; env; cons; shiftPairAt; sgl0At; pair0At; tag0At )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
```

<!--en-->
The ambient hierarchy `V ℓ` is an h-set, so the equality of two of its sets is a proposition and can sit inside a truth value; this is what makes the packaged equations below legitimate. The natural numbers enter as sets: `# k` is the von Neumann numeral in the hierarchy and `sucV` its successor operation, a notion distinct from any universe level and from the arity indices the codes carry. Propositional truncation gives mere existence, and eliminating it is legitimate only into a proposition-valued target, a restriction the pair reader's outward proof honors explicitly.
<!--zh-->
周遭层级 `V ℓ` 是一个 h-集合，故其中两个集合的相等是命题，可以放进真值之内；这正是下文打包等式得以成立的原因。自然数以集合身份进入：`# k` 是层级中的冯·诺伊曼数码，`sucV` 是其后继运算，它既不同于任何宇宙层级，也不同于码所带的元数指标。命题截断给出单纯存在，其消去只在取值为命题的目标中合法；配对读式的向外证明将显式遵守这一限制。
<!--ja-->
周囲の階層 `V ℓ` は h-集合なので、その二つの集合の等しさは命題であり、真理値の中に置けます。これが後の梱包された等式を正当化するものです。自然数は集合として現れます。`# k` は階層におけるフォン・ノイマンの数項、`sucV` はその後者演算であり、宇宙レベルとも、符号が持つアリティの指標とも別の概念です。命題的切り捨ては単なる存在を与え、その消去が正当なのは命題値の対象に限られます。対の読みの外向きの証明はこの制限を明示的に守ります。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
```

<!--en-->
The truth values at work are the propositions of `hProp` at level `ℓ-suc ℓ`, each packaged with its own proof of propositionhood, and the connective and quantifier operations of the truth algebra act on these packages. The model's carrier `S` consists of the pairs of an ambient set and a constructibility certificate. The absoluteness machinery is set up once for this situation: the structure being relativized is the hierarchy `𝒮ᵥ`, the class selecting the submodel is `isL`, transitivity is what keeps Δ₀ formulas absolute, satisfaction is written `⊨`, term interpretation `⟦_⟧`, and an environment is a vector of model elements.
<!--zh-->
这里使用的真值是层 `ℓ-suc ℓ` 的 `hProp` 命题，每个都连同「它是命题」的证明打包，真值代数的联结与量化运算都作用在这些包裹上。模型的载体 `S` 由「周遭集合配可构造性证书」的对组成。绝对性机制针对这一情形一次性设立：被相对化的结构是层级 `𝒮ᵥ`，挑选子模型的类是 `isL`，传递性使 Δ₀ 公式保持绝对；满足记作 `⊨`，词项解释记作 `⟦_⟧`，环境是模型元素的向量。
<!--ja-->
ここで使う真理値はレベル `ℓ-suc ℓ` の `hProp` の命題であり、それぞれ「それが命題である証明」とともに梱包され、真理値代数の連言と量化の演算はこの梱包に作用します。模型の台 `S` は、周囲の集合と構成可能性の証明の対からなります。絶対性の仕組みはこの状況に対して一度だけ設けられます。相対化される構造は階層 `𝒮ᵥ`、部分模型を選ぶクラスは `isL`、Δ₀ 論理式を絶対的に保つのが推移性です。充足は `⊨`、項の解釈は `⟦_⟧` と書き、環境は模型の要素からなるベクトルです。
<!--/-->

```agda

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )

open import L.Coding.Model {ℓ}
```

<!--en-->
One piece of the model dictionary matters for the main construction: the pair-shaped fact. The model's pairing `prʟ` projects to the ambient pairing by `prʟ-fst`, and its bounded reading formula is `prAtL`; the record `Container` with `container` produces, for a value equal to a pair, a constructible set holding both components. Reading a pair by a bounded formula demands exactly such an intermediate set, and `lookup-fst` and `envOverAt`, used later, are the projection and environment facts of the same dictionary.
<!--zh-->
模型词典中有一件东西对主要构造至关重要：配对形状的事实。模型的配对 `prʟ` 经 `prʟ-fst` 投影为周遭配对，其有界读式是 `prAtL`；记录 `Container` 连同 `container` 为等于某个对的取值造出一个容纳两个分量的可构造集合。用有界公式读取一个对，需要的恰是这样的中间集合；而 `lookup-fst` 与 `envOverAt` 则是同一词典中稍后用到的投影与环境事实。
<!--ja-->
模型の辞書の中で、主な構成に決定的なのは対の形をした事実です。模型の対 `prʟ` は `prʟ-fst` によって周囲の対へ射影され、その有界な読みの論理式が `prAtL` です。レコード `Container` と `container` は、ある対に等しい値に対して、両方の成分を収める構成可能集合をひとつ作ります。有界な論理式で対を読むには、まさにそのような中間集合が必要であり、`lookup-fst` と `envOverAt` は、のちに使われる同じ辞書の射影と環境の事実です。
<!--/-->

```agda
  using ( lookup-fst; prʟ; prʟ-fst; prAtL; prAtL-adequate; envOverAt
        ; Container; container )
```

<!--en-->
A bounded quantifier in the model ranges over elements of `S`, so any compound value a formula must recognize has to be matched by bounded witnesses that are themselves elements of the model. This section builds the general tool: an inductive language `Expr` of values assembled from assignment slots, constructible literals, numerals, and Kuratowski pairs, together with one structural reader turning an expression into a formula, and a two-sided adequacy theorem identifying the formula's meaning with the value the expression denotes. Everything else in the chapter is a specialization of this reader.
<!--zh-->
模型中的有界量词遍历 `S` 的元素，因此公式要识别的任何复合取值，都必须能由本身是模型元素的有界见证来匹配。本节建立一般工具：一个归纳语言 `Expr`，其取值由赋值槽位、可构造字面常元、数码与 Kuratowski 对组装而成；连同一条把表达式变成公式的结构读式，以及一个双向的充分性定理，它把公式的含义与表达式所指的值等同起来。本章其余的一切都是这一读式的特例。
<!--ja-->
模型における有界量化子は `S` の要素を渡ります。したがって論理式に認識させたい複合的な値は、それ自身が模型の要素である有界な証人によって一致させられねばなりません。本節はその一般的な道具を組み立てます。代入スロット、構成可能なリテラル、数項、Kuratowski 対から値を組み立てる帰納的な言語 `Expr` と、表現を論理式へ変えるひとつの構造的な読み、そして論理式の意味を表現の指す値と同一視する両方向の妥当性定理です。本章の残りはすべて、この読みの特殊化です。
<!--/-->

<!--en-->
Two small preparations open the section. `PairIs a p` packages the statement that the ambient value `a` equals `p` as a truth value: since the hierarchy is an h-set, that equality type is a proposition, and the pairing with `setIsSet` makes it an inhabitant of `Ω`. Adequacy statements will compare satisfaction judgments with these packaged equalities along paths. The expression language itself is indexed by a natural number `n` that fixes how many free-variable slots are available; a slot may well go unused.
<!--zh-->
本节以两件小准备开篇。`PairIs a p` 把「周遭取值 `a` 等于 `p`」这一陈述打包成真值：由于层级是 h-集合，该相等类型是命题，与 `setIsSet` 配对后便是 `Ω` 的元素。此后充分性陈述都将沿路径把满足判断与这些打包的等式相比较。表达式语言本身以自然数 `n` 为指标，确定可用的自由变元槽位数；某个槽位完全可以不被使用。
<!--ja-->
本節は小さな二つの準備から始まります。`PairIs a p` は「周囲の値 `a` が `p` に等しい」という主張を真理値として梱包します。階層は h-集合なので、その等式の型は命題であり、`setIsSet` との対によって `Ω` の要素になります。以後の妥当性の主張は、充足の判断とこれらの梱包された等式をパスに沿って比較することになります。式の言語そのものは自然数 `n` を指標とし、利用できる自由変数スロットの数を確定します。ひとつのスロットが使われないままであっても構いません。
<!--/-->

```agda
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

module PairExpression where
  data Expr (n : ℕ) : Type (ℓ-suc ℓ) where
```

<!--en-->
The language of expressions is fixed by four constructors, and each names one way a compound value can present itself to a formula. A `slot`{.Agda} `i`{.Agda} refers to the `i`-th entry of an ambient assignment, the analogue of a variable; a `literal`{.Agda} `a`{.Agda} names a whole element of the model, constructibility certificate included, so it behaves like an object-language constant; a `numeral`{.Agda} `k`{.Agda} names the von Neumann natural `k`; and `pair`{.Agda} composes two subexpressions into a Kuratowski pair. An expression is a finite description of a value, not itself a set, so it admits two independent readings, and the goal is to prove that they agree.
<!--zh-->
表达式语言由四个构造子确定，每个构造子对应复合取值向公式呈现自身的一种方式。`slot`{.Agda} `i`{.Agda} 引用周遭赋值的第 `i` 项，相当于变元；`literal`{.Agda} `a`{.Agda} 一次性命名模型的一个完整元素，连同其可构造性证书，故其行为如对象语言常元；`numeral`{.Agda} `k`{.Agda} 命名冯·诺伊曼自然数 `k`；`pair`{.Agda} 把两个子表达式合成一个 Kuratowski 对。表达式是取值的有穷描述，本身不是集合，因此它容许两种独立的读法，而目标正是证明二者一致。
<!--ja-->
表現の言語は四つの構成子で確定し、それぞれが複合的な値が論理式に現れるひとつのしかたに対応します。`slot`{.Agda} `i`{.Agda} は周囲の割り当ての第 `i` 項を参照する、変数に相当するものです。`literal`{.Agda} `a`{.Agda} は模型の要素ひとつを、構成可能性の証明書ごとまとめて名指し、対象言語の定数のように振る舞います。`numeral`{.Agda} `k`{.Agda} はフォン・ノイマンの自然数 `k` を名指し、`pair`{.Agda} は二つの部分表現を Kuratowski 対へ合成します。表現は値の有限な記述であって、それ自身は集合ではないので、二つの独立した読み方が許され、目標はこの二つが一致することの証明です。
<!--/-->

```agda
    slot : Fin n → Expr n
    literal : S → Expr n
    numeral : ℕ → Expr n
    pair : Expr n → Expr n → Expr n

  value : ∀ {n} → Expr n → (Fin n → V ℓ) → V ℓ
```

<!--en-->
The first reading is ambient. Given an assignment of hierarchy sets to the slots, `value`{.Agda} computes the set an expression denotes: a slot is looked up, a literal projects away its certificate with `fst`{.Agda}, a numeral becomes `# k`{.Agda}, and a pair is the Kuratowski pair `pr`{.Agda} of the two denoted sets. This is the reading the adequacy theorem will recover on its right-hand side: the point of a bounded formula is to identify, from inside the model, a value that is naturally described out here.
<!--zh-->
第一种读法是周遭的。给定把层级集合指派给各槽位，`value`{.Agda} 计算表达式所指的集合：槽位按查值，字面常元经 `fst`{.Agda} 投影掉其证书，数码变为 `# k`{.Agda}，配对则是两个所指集合的 Kuratowski 对 `pr`{.Agda}。充分性定理将在右侧恢复的正是这种读法：一条有界公式的意义，就在于从模型内部识别出一个天然描述于外的取值。
<!--ja-->
第一の読みは周囲のものです。階層の集合を各スロットに割り当てると、`value`{.Agda} は表現の指す集合を計算します。スロットは参照され、リテラルは `fst`{.Agda} で証明書を射影して捨てられ、数項は `# k`{.Agda} になり、対は指された二つの集合の Kuratowski 対 `pr`{.Agda} です。妥当性定理が右辺として取り戻すのはこの読みです。有界な論理式の意義は、外で自然に記述される値を模型の内部から識別することにあります。
<!--/-->

```agda
  value (slot i) γ = γ i
  value (literal a) γ = fst a
  value (numeral k) γ = # k
  value (pair a b) γ = pr (value a γ) (value b γ)

  element : ∀ {n} → Expr n → (Fin n → S) → S
```

<!--en-->
The second reading stays inside the model. Given an assignment of elements of `S` to the slots, `element`{.Agda} computes an element of `S`: literals are already model elements carrying their certificates, numerals use the internal numerals `numeralL`{.Agda}, and pairs are formed by the model's own pairing `prʟ`{.Agda}. The two readings are parallel clause by clause, and this parallelism is what makes the bridge between them provable: to compare them one only ever compares corresponding cases.
<!--zh-->
第二种读法停留在模型内部。给定把 `S` 的元素指派给各槽位，`element`{.Agda} 计算出一个 `S` 的元素：字面常元本就是带证书的模型元素，数码用内部数码 `numeralL`{.Agda}，配对由模型自己的配对 `prʟ`{.Agda} 生成。两种读法逐条款平行，而这种平行性正是二者之间的桥梁可证的原因：比较它们时只需逐情形对应地比。
<!--ja-->
第二の読みは模型の内部にとどまります。`S` の要素を各スロットに割り当てると、`element`{.Agda} は `S` の要素をひとつ計算します。リテラルはもともと証明書を伴う模型の要素であり、数項は模型内部の数項 `numeralL`{.Agda} を使い、対は模型自身の対 `prʟ`{.Agda} で作られます。二つの読みは条項ごとに平行しており、この平行性こそ両者を結ぶ橋が証明できる理由です。比較はつねに対応する場合どうしの比較で済むからです。
<!--/-->

```agda
  element (slot i) γ = γ i
  element (literal a) γ = a
  element (numeral k) γ = numeralL k
  element (pair a b) γ = prʟ (element a γ) (element b γ)

  element-fst : ∀ {n} (e : Expr n) (γ : Fin n → S)
```

<!--en-->
The bridge is `element-fst`{.Agda}: projecting an internal element yields, as a path, exactly the ambient value at the projected assignment. For slots and literals the two readings coincide on the nose, so the proof is `refl`{.Agda}. A numeral is the first genuine case: its internal form projects to the ambient one by `numeralL-fst`{.Agda}, the compatibility fact between internal and ambient numerals that the numeral chapter supplies. Note the direction, since it recurs throughout: the path goes from the projection of the internal value to the ambient value.
<!--zh-->
桥梁是 `element-fst`{.Agda}：投影一个内部元素，作为一条路径，恰好等于在投影后赋值处的周遭取值。对槽位与字面常元，两种读法逐字重合，故证明即 `refl`{.Agda}。数码是第一个实质情形：其内部形式经 `numeralL-fst`{.Agda} 投影为周遭形式，这正是数码一章给出的内部数码与周遭数码之间的相容性事实。注意方向，它将贯穿全章：路径从内部取值的投影出发，指向周遭取值。
<!--ja-->
橋となるのが `element-fst`{.Agda} です。内部の要素を射影すると、その道はちょうど、射影された割り当てにおける周囲の値になります。スロットとリテラルでは二つの読みが文字どおり一致するので、証明は `refl`{.Agda} です。数項が最初の本格的な場合で、その内部の形は `numeralL-fst`{.Agda} によって周囲の形へ射影されます。これは数項の章が供給する、内部の数項と周囲の数項の間の相容性の事実です。方向に注意してください。これは後章でも繰り返されます。道は内部の値の射影から周囲の値へ向かいます。
<!--/-->

```agda
              → fst (element e γ) ≡ value e (λ i → fst (γ i))
  element-fst (slot i) γ = refl
  element-fst (literal a) γ = refl
  element-fst (numeral k) γ = numeralL-fst k
  element-fst (pair a b) γ = prʟ-fst (element a γ) (element b γ)
```

<!--en-->
The pair case composes two independent compatibilities: the model's pairing projects to the ambient pairing by `prʟ-fst`{.Agda}, and each component's projection law is the recursive fact. Congruence under `pr`{.Agda} assembles the two component paths into one, and the projection law for a nested expression follows by induction. On the syntactic side, `lift3`{.Agda} is the reindexing the pair reader will need: it shifts every old slot three places up, `lift3 ρ i = suc (suc (suc (ρ i)))`{.Agda}, preserving which old entry each slot refers to while making room for three fresh variables.
<!--zh-->
配对情形把两条独立的相容性串联起来：模型的配对经 `prʟ-fst`{.Agda} 投影为周遭配对，而每个分量的投影律正是递归的事实。在 `pr`{.Agda} 之下的同余把两条分量路径合成一条，嵌套表达式的投影律便由归纳成立。在语法一侧，`lift3`{.Agda} 是配对读式所需的重标定：它把每个旧槽位上移三位，即 `lift3 ρ i = suc (suc (suc (ρ i)))`{.Agda}，既保留每个槽位所指的旧条目，又为三个新变元腾出位置。
<!--ja-->
対の場合は独立した二つの相容性を連結します。模型の対は `prʟ-fst`{.Agda} によって周囲の対へ射影され、各成分の射影の法則は帰納的な事実です。`pr`{.Agda} の下での合同性が二つの成分の道をひとつにまとめ、入れ子になった表現の射影の法則は帰納法で従います。構文の側では、`lift3`{.Agda} が対の読み出しに要る再索引付けです。各スロットを三つ上げる、つまり `lift3 ρ i = suc (suc (suc (ρ i)))`{.Agda} とすることで、各スロットが指す旧来の項目を保ったまま、三つの新しい変数の分の空きができます。
<!--/-->

```agda
    ∙ cong₂ pr (element-fst a γ) (element-fst b γ)

  lift3 : ∀ {n m} → (Fin n → Fin m) → Fin n → Fin (3 + m)
  lift3 ρ i = suc (suc (suc (ρ i)))

  read : ∀ {n m} → Expr n → (Fin n → Fin m) → Fin m → Formula S m
  read (slot i) ρ q = var q ≐ var (ρ i)
```

<!--en-->
The reader `read`{.Agda} turns an expression at slot `q`{.Agda} into a bounded formula. A slot demands equality with the corresponding reindexed variable, a literal equality with its constant, a numeral equality with the constant naming its internal numeral. The pair case carries the mathematical content. It binds, by three bounded existentials, a set `s` in the set at `q` and elements `u`, `v` in `s`, so that `s` is a member of the entry at `q` and `u`, `v` are members of `s`; through the model's pair-reading formula `prAtL`{.Agda} it asserts that the entry at `q` equals the pair `pr u v`. The component conditions are then read recursively at the shifted slots, which is what `lift3`{.Agda} provides. Thus a compound value is recognized from inside the model through a constructible intermediate set holding both Kuratowski components.
<!--zh-->
读式 `read`{.Agda} 把槽位 `q`{.Agda} 处的表达式变成一条有界公式。槽位要求与相应的重标定变元相等，字面常元要求与其常元相等，数码要求与命名其内部数码的常元相等。配对情形才有数学内容：它用三条有界存在绑定 `q` 处集合中的集合 `s`，以及 `s` 中的元素 `u`、`v`，使 `s` 属于 `q` 处的条目，而 `u`、`v` 属于 `s`；再借模型的配对读式 `prAtL`{.Agda} 断言 `q` 处的条目等于对 `pr u v`。随后在移位槽位处递归读出两个分量条件，这正是 `lift3`{.Agda} 所提供的。于是，一个复合取值是从模型内部、经由一个容纳两个 Kuratowski 分量的可构造中间集合来识别的。
<!--ja-->
読み出し `read`{.Agda} は、スロット `q`{.Agda} の表現を有界な論理式へ変えます。スロットは対応する再索引付けされた変数との等しさを、リテラルはその定数との等しさを、数項は内部の数項を名指す定数との等しさを要求します。数学的な内容を担うのは対の場合です。三つの有界存在によって、`q` の集合の中の集合 `s` と、`s` の中の要素 `u`、`v` を結び、`s` が `q` の項目の要素であり、`u` と `v` が `s` の要素になるようにします。そして模型の対の読みの論理式 `prAtL`{.Agda} を通して、`q` の項目が対 `pr u v` に等しいと主張します。成分の条件はその後、ずらしたスロットで帰納的に読まれ、これを `lift3`{.Agda} が担います。こうして複合的な値は、模型の内部から、Kuratowski の二成分をともに収める構成可能な中間集合を経由して認識されます。
<!--/-->

```agda
  read (literal a) ρ q = var q ≐ con a
  read (numeral k) ρ q = var q ≐ con (numeralL k)
  read (pair a b) ρ q = ∃̇∈ (var q) (∃̇∈ (var zero) (∃̇∈ (var (suc zero))
    (prAtL (suc (suc (suc q))) (suc zero) zero
      ∧̇ (read a (lift3 ρ) (suc zero) ∧̇ read b (lift3 ρ) zero))))
```

<!--en-->
Adequacy has two directions, and `out`{.Agda} is the one a soundness proof consumes: from an inhabitant of the satisfaction judgment it produces the path saying that the entry at `q` projects to the denoted value. Slots and literals already are such paths by definition, and the numeral case composes the hypothesis with `numeralL-fst`{.Agda}, the same direction as in `element-fst`. The interesting work is the pair case, which occupies the next two steps.
<!--zh-->
充分性分为两个方向，`out`{.Agda} 是可靠性证明所用的方向：从满足判断的一个证明出发，产出「槽位 `q` 处的条目投影后等于所指的值」这条路径。槽位与字面常元按定义本就是这样的路径，数码情形则把前提与 `numeralL-fst`{.Agda} 复合，方向与 `element-fst` 相同。实质工作在配对情形，它占了接下来的两步。
<!--ja-->
妥当性には二つの方向があり、`out`{.Agda} は健全性の証明が消費する方向です。充足の判断の要素から、「スロット `q` の項目を射影すると指された値に等しい」という道を作ります。スロットとリテラルは定義どおりそのような道そのものであり、数項の場合は前提を `numeralL-fst`{.Agda} と合成します。方向は `element-fst` と同じです。本格的な仕事は対の場合にあり、次の二段がそれを扱います。
<!--/-->

```agda

  out : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
       → ⟨ γ ⊨ read e ρ q ⟩ → fst (lookup q γ) ≡ value e (λ i → fst (lookup (ρ i) γ))
  out (slot i) ρ q γ h = h
  out (literal a) ρ q γ h = h
  out (numeral k) ρ q γ h = h ∙ numeralL-fst k
```

<!--en-->
The hypothesis of the pair case is a truncated bounded existential with three layers, so the proof eliminates them one at a time, and each elimination needs a proposition-valued target. This is where `setIsSet`{.Agda} enters: the conclusion is a path in the hierarchy, which is an h-set, hence the target is a proposition and the eliminations are legitimate. What truncation gives and what it does not should be stated plainly. The witnesses `s`, `u`, `v` arrive as elements, so the mathematics can use them, but the hypothesis asserts only their mere existence: no uniqueness, and no chosen representatives.
<!--zh-->
配对情形的前提是一个具有三层的截断有界存在，故证明逐层消去它们，而每次消去都需要取值为命题的目标。这正是 `setIsSet`{.Agda} 进入之处：结论是层级 (一个 h-集合) 中的一条路径，因此目标是命题，消去合法。截断给了什么、没给什么，值得直说：见证 `s`、`u`、`v` 作为元素到达，数学可以继续使用它们，但前提断言的只是它们的单纯存在：没有唯一性，也没有被选出的代表。
<!--ja-->
対の場合の前提は三層に重なった截断された有界存在なので、証明はそれを一度にひとつずつ消去し、各消去には命題値の対象が必要です。ここで `setIsSet`{.Agda} が登場します。結論は階層 (h-集合) における道であり、したがって対象は命題なので、消去は正当です。截断が何を与え、何を与えないかは率直に述べるべきです。証人 `s`、`u`、`v` は要素として現れるので数学はそれを使えますが、前提が主張するのはそれらの単なる存在にすぎません。一意性も、選ばれた代表もありません。
<!--/-->

```agda
  out (pair a b) ρ q γ = PT.rec (setIsSet _ _) (λ { (s , s∈ , hs) →
    PT.rec (setIsSet _ _) (λ { (u , u∈ , hu) →
      PT.rec (setIsSet _ _) (λ { (v , v∈ , p , ha , hb) →
        subst ⟨_⟩ (prAtL-adequate (suc (suc (suc q))) (suc zero) zero (v ∷ u ∷ s ∷ γ)) p
        ∙ cong₂ pr (out a (lift3 ρ) (suc zero) (v ∷ u ∷ s ∷ γ) ha)
```

<!--en-->
With the three witnesses in hand, the innermost formula is unfolded by the pair reader's own adequacy: transporting `p` along `prAtL-adequate`{.Agda} turns the pairing assertion into the equation `fst (lookup q γ) ≡ pr (fst u) (fst v)`. The two recursive hypotheses then give the components' projections at slots one and zero, `fst u ≡ value a` and `fst v ≡ value b`, and congruence under `pr`{.Agda} rewrites the right-hand side into `pr (value a) (value b)`, which is exactly the value of the pair expression. The inner proof is thus one transport followed by one congruence.
<!--zh-->
拿到三个见证后，最内层公式由配对读式自身的充分性展开：把 `p` 沿 `prAtL-adequate`{.Agda} 传输，配对断言便变成等式 `fst (lookup q γ) ≡ pr (fst u) (fst v)`。两个递归前提随即给出分量在一号与零号槽位处的投影，即 `fst u ≡ value a` 与 `fst v ≡ value b`；再经 `pr`{.Agda} 之下的同余，右侧被改写为 `pr (value a) (value b)`，恰是该配对表达式的取值。内层证明因此是一次传输加一次同余。
<!--ja-->
三つの証人が手に入れば、最も内側の論理式は対の読み出し自身の妥当性によって展開されます。`p` を `prAtL-adequate`{.Agda} に沿って輸送すると、対の主張は等式 `fst (lookup q γ) ≡ pr (fst u) (fst v)` になります。続く二つの帰納的な前提が、スロット 0 と 1 での成分の射影、すなわち `fst u ≡ value a` と `fst v ≡ value b` を与え、`pr`{.Agda} の下での合同が右辺を `pr (value a) (value b)` へ書き換えます。これはまさにその対の表現の値です。内側の証明は、輸送ひとつと合同ひとつからなります。
<!--/-->

```agda
                   (out b (lift3 ρ) zero (v ∷ u ∷ s ∷ γ) hb) }) hu }) hs })

  into : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
        → fst (lookup q γ) ≡ value e (λ i → fst (lookup (ρ i) γ)) → ⟨ γ ⊨ read e ρ q ⟩
  into (slot i) ρ q γ h = h
  into (literal a) ρ q γ h = h
```

<!--en-->
The converse direction `into`{.Agda} builds an inhabitant of the satisfaction judgment from the bare equation. Slots and literals are immediate; the numeral case composes with the symmetry of `numeralL-fst`{.Agda}, reversing the direction of the earlier compatibility. In the pair case all three truncated layers must be supplied at once, and here nothing is extracted from a truncation: the witnesses are constructed outright. The internal elements `u` and `v` are chosen as `element a` and `element b` in the reindexed assignment, and `Container`{.Agda} and `container`{.Agda} use the adjusted path `e` to produce a constructible set `s` containing both, with all membership certificates. This is a use of transitivity of `L` in its own right, distinct from the proposition-valuedness that licensed the eliminations above: there truncation was consumed, here concrete elements are produced.
<!--zh-->
逆向的 `into`{.Agda} 从裸等式出发构造满足判断的一个证明。槽位与字面常元直接可得；数码情形与 `numeralL-fst`{.Agda} 的对称复合，调转了前述相容性的方向。配对情形须一次性给出全部三个截断层，而此处并非从截断中抽取任何东西：见证是直接构造的。内部元素 `u` 与 `v` 取为重标定赋值下的 `element a` 与 `element b`，而 `Container`{.Agda} 与 `container`{.Agda} 用调整后的路径 `e` 造出一个同时容纳两者的可构造集合 `s`，连同全部隶属证书。这是对 `L` 传递性的一次独立运用，与上文使消去得以合法的「取值为命题」是两回事：那里消去的是截断，这里产出的是具体的元素。
<!--ja-->
逆方向の `into`{.Agda} は、裸の等式から充足の判断の要素を構成します。スロットとリテラルは直接であり、数項の場合は `numeralL-fst`{.Agda} の対称と合成して、先の相容性の向きを逆にします。対の場合には三つの截断の層すべてを一度に供給しなければなりませんが、ここでは截断から何かを取り出すのではなく、証人をその場で構成します。内部の要素 `u` と `v` は再索引付けされた割り当てでの `element a` と `element b` として選ばれ、`Container`{.Agda} と `container`{.Agda} が調整済みの道 `e` を用いて、両方を収める構成可能な集合 `s` を、すべての所属の証明書とともに作ります。これは `L` の推移性の独立した使用であり、上で消去を正当化した命題値の確認とは別物です。あちらは截断を消費し、こちらは具体的な要素を作り出します。
<!--/-->

```agda
  into (numeral k) ρ q γ h = h ∙ sym (numeralL-fst k)
  into {n} {m} (pair a b) ρ q γ h = ∣ s , c .snd .fst , ∣ u , c .snd .snd .fst ,
    ∣ v , c .snd .snd .snd ,
      subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc q))) (suc zero) zero δ)) e
      , into a (lift3 ρ) (suc zero) δ (element-fst a η)
```

<!--en-->
The extended assignment `δ` is `v ∷ u ∷ s ∷ γ`, and its layout is the whole bookkeeping of the construction:

| slot | entry | role |
| --- | --- | --- |
| 0 | `v` | internal element of `b` |
| 1 | `u` | internal element of `a` |
| 2 | `s` | the intermediate set, a member of the entry at `q` |
| `i + 3` | old slot `i` | the original assignment, unchanged |

The pair formula asserts `s ∈ q`, `u ∈ s`, `v ∈ s`, and `q ≡ pr u v`; since `u` sits at slot one and `v` at slot zero, the recursive reads `read a` at slot one and `read b` at slot zero consult exactly the old slots, by `lift3`. Each subproof is assembled by `into` itself at the shifted slot, fed the projection path `element-fst` for the component being read, and the three nested truncated existentials are closed with one explicit `∣_∣₁` per layer.
<!--zh-->
扩展赋值 `δ` 就是 `v ∷ u ∷ s ∷ γ`，它的布局就是这一构造的全部簿记：

| 槽位 | 条目 | 角色 |
| --- | --- | --- |
| 0 | `v` | `b` 的内部元素 |
| 1 | `u` | `a` 的内部元素 |
| 2 | `s` | 中间集合，`q` 处条目的成员 |
| `i + 3` | 旧槽位 `i` | 原赋值，原样保留 |

配对公式断言 `s ∈ q`、`u ∈ s`、`v ∈ s`，以及 `q ≡ pr u v`；由于 `u` 位于一号槽位、`v` 位于零号槽位，经 `lift3` 后，在一号槽位处的 `read a` 与零号槽位处的 `read b` 所查询的恰是原来的槽位。每个子证明由 `into` 自身在移位槽位处组装，喂入被读分量的投影路径 `element-fst`；最后，三个嵌套的截断存在各以一个显式的 `∣_∣₁` 封口。
<!--ja-->
拡張された割り当て `δ` は `v ∷ u ∷ s ∷ γ` であり、その配置がこの構成のすべての簿記です。

| スロット | 項目 | 役割 |
| --- | --- | --- |
| 0 | `v` | `b` の内部要素 |
| 1 | `u` | `a` の内部要素 |
| 2 | `s` | 中間集合、`q` の項目の要素 |
| `i + 3` | 古いスロット `i` | 元の割り当て、そのまま |

対の論理式は `s ∈ q`、`u ∈ s`、`v ∈ s`、そして `q ≡ pr u v` を主張します。`u` がスロット 1 に、`v` がスロット 0 にあるので、`lift3` によって、スロット 1 での `read a` とスロット 0 での `read b` はちょうど古いスロットを参照します。各部分証明は `into` 自身がずらしたスロットで組み立て、読まれる成分の射影の経路 `element-fst` を与えられ、最後に三つの入れ子の截断された存在は、層ごとにひとつの明示的な `∣_∣₁` で閉じられます。
<!--/-->

```agda
      , into b (lift3 ρ) zero δ (element-fst b η) ∣₁ ∣₁ ∣₁
    where
    η : Fin n → S
    η i = lookup (ρ i) γ
    u v : S
```

<!--en-->
The remaining local definitions record the arithmetic of the construction. `η` restricts the old assignment to the reindexed slots, and `u` and `v` are the explicit internal elements of the two subexpressions under it; these are chosen outright, not extracted from any truncation. The path `e` then states that the entry at `q` equals the ambient pair `pr (fst u) (fst v)`. Its direction matters: the hypothesis `h` says the entry equals the denoted value of the whole pair, and composing with the symmetry of the components' projection congruence `element-fst` produces exactly the target the container construction expects.
<!--zh-->
其余的局部定义记录这一构造的算术。`η` 把旧赋值限制到重标定后的槽位，`u` 与 `v` 是两个子表达式在其下的显式内部元素；它们是直接选定的，并非从任何截断中提取。路径 `e` 随后陈述：`q` 处的条目等于周遭配对 `pr (fst u) (fst v)`。它的方向很重要：前提 `h` 说条目等于整个配对所指的值，与分量的投影同余 `element-fst` 的对称复合后，得到的恰是容器构造所预期的目标。
<!--ja-->
残りの局所的な定義は、この構成の算術を記録します。`η` は古い割り当てを再索引付けされたスロットに制限したものであり、`u` と `v` はそのもとでの二つの部分表現の明示的な内部的な要素です。これらは直接選ばれるのであって、截断から取り出されるのではありません。経路 `e` は、スロット `q` の項目が周囲の対 `pr (fst u) (fst v)` に等しいと述べます。その方向が重要です。前提 `h` は項目が対全体の指す値に等しいと言い、成分の射影の合同 `element-fst` の対称と合成することで、コンテナの構成が期待する対象がちょうど得られます。
<!--/-->

```agda
    u = element a η
    v = element b η
    e : fst (lookup q γ) ≡ pr (fst u) (fst v)
    e = h ∙ sym (cong₂ pr (element-fst a η) (element-fst b η))
    c : Container (lookup q γ) u v
```

<!--en-->
The container is produced from the path `e`, and its first component is the desired constructible set `s`, the common intermediate through which both Kuratowski components are reached: `s` is a member of the entry at `q`, and `u` and `v` are members of `s`. Prepending `v`, then `u`, then `s` to `γ` yields the extended assignment `δ` of arity three more than the original. Every remaining ingredient of the inward construction is now an entry of `δ` rather than a free-standing element.
<!--zh-->
容器由路径 `e` 造出，其第一个分量正是所需的可构造集合 `s`，它是到达两个 Kuratowski 分量的公共中间体：`s` 是 `q` 处条目的成员，而 `u` 与 `v` 是 `s` 的成员。把 `v`、`u`、`s` 依次推到 `γ` 的最前，便得到比原来多元数三的扩展赋值 `δ`。此后内向构造所需的每个材料都不再是游离的元素，而是 `δ` 的一个条目。
<!--ja-->
コンテナは経路 `e` から作られ、その最初の成分がまさに求める構成可能な集合 `s` です。これは二つの Kuratowski 成分のどちらにも到達する共通の中間体であり、`s` はスロット `q` の項目の要素であり、`u` と `v` は `s` の要素です。`v`、`u`、`s` の順に `γ` の先頭へ付け加えると、元よりアリティが三だけ大きい拡張された割り当て `δ` が得られます。以後、内向きの構成に要る材料はどれも、遊離した要素ではなく `δ` の項目になります。
<!--/-->

```agda
    c = container (lookup q γ) u v e
    s : S
    s = c .fst
    δ : S ^ (suc (suc (suc m)))
    δ = v ∷ u ∷ s ∷ γ
```

<!--en-->
The two directions assemble into the advertised form. `adequate` states that the satisfaction judgment at `γ` equals, as a truth value, the packaged equation between the projected entry at `q` and the ambient denotation; `⇔toPath` converts the pair of implications `out` and `into` into that path. As the first application, `member e C` says that the value of `e` belongs to the denotation of the term `C`: it boundedly quantifies over a member of `C`'s interpretation and demands the expression reader at that member's extended assignment, with the expression shifted into the leading slot.
<!--zh-->
两个方向组装成所宣称的形状。`adequate` 陈述：在 `γ` 处的满足判断，作为一个真值，等于「`q` 处条目的投影」与「周遭所指」之间打包后的等式；`⇔toPath` 把 `out` 与 `into` 这对蕴含变成这条路径。作为第一个应用，`member e C` 说表达式 `e` 的取值属于词项 `C` 的所指：它对 `C` 所指的成员作有界量化，并要求在该成员扩展后的赋值处成立表达式读式，其中表达式被移入首位槽位。
<!--ja-->
二つの方向が、述べられた形に組み上がります。`adequate` は、`γ` での充足の判断が、真理値として、「スロット `q` の項目の射影」と「周囲の指示値」との、梱包された等式に等しいと述べます。`⇔toPath` が `out` と `into` の組の含意をこの経路に変えます。最初の応用として、`member e C` は表現 `e` の値が項 `C` の指示に属すると述べます。`C` の解釈の要素について有界に量化し、その要素で拡張した割り当てのもとで、表現を先頭スロットへずらした読み出しを要求します。
<!--/-->

```agda

  adequate : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
            → (γ ⊨ read e ρ q) ≡ PairIs (fst (lookup q γ)) (value e (λ i → fst (lookup (ρ i) γ)))
  adequate e ρ q γ = ⇔toPath (out e ρ q γ) (into e ρ q γ)

  member : ∀ {n} → Expr n → Term S n → Formula S n
  member e C = ∃̇∈ C (read e suc zero)
```

<!--en-->
The outward reader of `member` eliminates the truncated bounded existential and receives a member `x`, its membership proof `h`, and the proof `p` that `x`'s extended assignment satisfies the expression reader. Applying adequacy outward converts `p` into the equation `fst x ≡ value e ...`; transporting `h` along that equation turns membership of `fst x` into membership of the denoted value. The target is the membership proposition `value e ... ∈ fst (⟦ C ⟧ γ)`, whose second component supplies exactly the propositionhood required by `PT.rec`.
<!--zh-->
`member` 的向外读式消去截断的有界存在，得到成员 `x`、其隶属证明 `h`，以及「`x` 的扩展赋值满足表达式读式」的证明 `p`。把充分性沿向外方向施于 `p`，得到等式 `fst x ≡ value e ...`；再沿这条等式搬运 `h`，便把 `fst x` 的隶属变成所指取值的隶属。目标正是隶属命题 `value e ... ∈ fst (⟦ C ⟧ γ)`，其第二分量给出 `PT.rec` 所需的命题性证明。
<!--ja-->
`member` の外向きの読みは、截断された有界存在を消去し、要素 `x`、その所属の証明 `h`、そして `x` で拡張した割り当てが表現の読みを満たす証明 `p` を受け取ります。妥当性を外向きに `p` に適用すると等式 `fst x ≡ value e ...` が得られ、その等式に沿って `h` を輸送すれば、`fst x` の所属が表現の値の所属へ移ります。対象は所属命題 `value e ... ∈ fst (⟦ C ⟧ γ)` であり、その第二成分が `PT.rec` に必要な命題性の証明を与えます。
<!--/-->

```agda

  member-out : ∀ {n} (e : Expr n) (C : Term S n) (γ : S ^ n)
              → ⟨ γ ⊨ member e C ⟩ → ⟨ value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ) ⟩
  member-out e C γ = PT.rec (snd (value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ)))
    (λ { (x , h , p) → subst (λ v → ⟨ v ∈ fst (⟦ C ⟧ γ) ⟩) (out e suc zero (x ∷ γ) p) h })

  member-in : ∀ {n} (e : Expr n) (C : Term S n) (γ : S ^ n)
```

<!--en-->
The inward reader must exhibit the member, and the value of `e` itself serves, once it is made an element of the model. It is a member of `fst (⟦ C ⟧ γ)` by hypothesis, and the interpretation of the term is constructible, so transitivity of `L` hands over the constructibility certificate for the value: that is exactly what `isL-trans` does here. This use of transitivity is different in kind from the proposition-valued target restriction on truncation elimination: no truncation is in play, and what is produced is the explicit data that makes the ambient value a pair of itself and its certificate. With that, `x` is exactly such a pair, and the entry at the extended assignment projects to the value definitionally, so the recursive `into` receives the path `refl`.
<!--zh-->
向内读式必须给出那个成员，而表达式 `e` 的取值本身即可充当，只需先把它变成模型的元素。由前提它是 `fst (⟦ C ⟧ γ)` 的成员，而该词项的解释可构造，于是 `L` 的传递性给出该取值的可构造性证书：这正是 `isL-trans` 在此处所做的事。这里没有消去截断；证书与周遭取值组成显式的模型元素 `x`，作为有界存在的见证。扩展赋值处的首项按定义投影为该取值，故递归的 `into` 收到路径 `refl`。
<!--ja-->
内向きの読みはその要素を示さねばなりませんが、表現 `e` の値そのものを模型の要素にすれば証人になります。前提によりそれは `fst (⟦ C ⟧ γ)` の要素であり、項の解釈は構成可能なので、`L` の推移性がその値の構成可能性の証明書を与えます。ここで `isL-trans` がしているのはまさにそれです。截断の消去は行われません。証明書と周囲の値を組にした明示的な模型要素 `x` が、有界存在の証人になります。拡張された割り当ての先頭は定義によりその値へ射影されるので、帰納的な `into` は経路 `refl` を受け取ります。
<!--/-->

```agda
             → ⟨ value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ) ⟩ → ⟨ γ ⊨ member e C ⟩
  member-in e C γ h = ∣ x , h , into e suc zero (x ∷ γ) refl ∣₁
    where
    x : S
    x = value e (λ i → fst (lookup i γ)) , isL-trans h (snd (⟦ C ⟧ γ))
```

<!--en-->
The first specialization turns the generic reader into a tag recognizer. `tagAtL s k x` reads, at slot `s`, the expression pairing the numeral `k` with the slot `x`; it is therefore the bounded formula asserting that the entry at `s` is the ordered pair of `# k` and the entry at `x`. Codes in the recursion carry a numeric tag paired with their payload, and this is exactly that shape.
<!--zh-->
第一个特化把一般读式变成标签识别器。`tagAtL s k x` 在槽位 `s` 处读取「数码 `k` 与槽位 `x` 配对」的表达式，因而是一条有界公式，断言 `s` 处的条目是 `# k` 与 `x` 处条目的有序对。递归中的码都带有一个与载荷配对的数字标签，而这正是那个形状。
<!--ja-->
最初の特殊化は、一般的な読み出しをタグの認識器に変えます。`tagAtL s k x` は、スロット `s` で「数項 `k` とスロット `x` の対」という表現を読むもので、したがって、スロット `s` の項目が `# k` とスロット `x` の項目の順序対であると主張する有界論理式です。再帰に現れる符号は、ペイロードと対になった数値のタグを帯びており、まさにこの形をしています。
<!--/-->

```agda

tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = PairExpression.read
  (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot x)) id s

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
```

<!--en-->
Its adequacy lemma needs no new proof: instantiating the generic adequacy at this expression with the identity relabelling already computes to the identification of the satisfaction judgment with `PairIs` of the projected entry and `pr (# k)` of the projected payload. This is the pattern of the whole section: choose an expression, cite `PairExpression.adequate`, and the meaning of the clause is read off.
<!--zh-->
它的充分性引理无需新证明：在这一表达式处以恒等改名实例化一般充分性，其计算结果已经是「满足判断等同于投影条目与 `pr (# k)` 投影载荷的 `PairIs`」。这是全节的模式：选定一个表达式，引用 `PairExpression.adequate`，子句的含义便被读出。
<!--ja-->
その妥当性の補題は新しい証明を要りません。この表現について恒等リラベルで一般的な妥当性を実体化すると、その計算結果はすでに、充足の判断が、射影された項目と `pr (# k)` されたペイロードの `PairIs` と同一視されるというものです。これが本節全体の型です。表現を選び、`PairExpression.adequate` を引用すれば、節の意味が読み取れます。
<!--/-->

```agda
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot x)) id s γ

tagPairAtL : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagPairAtL s k a b = PairExpression.read
```

<!--en-->
The second specialization handles payloads that are themselves pairs, and the two pairing layers are nested in the expression. `tagPairAtL s k a b` reads the numeral `k` paired with the pair of the two slots `a` and `b`, so it recognizes entries of the shape `pr (# k) (pr (entry a) (entry b))`: a tag over a two-component payload.
<!--zh-->
第二个特化处理本身是对形式的载荷，两层配对嵌套在表达式之内。`tagPairAtL s k a b` 读取「数码 `k` 与槽位 `a`、`b` 之对配对」的表达式，故识别形如 `pr (# k) (pr (entry a) (entry b))` 的条目：一个标签架在双分量载荷之上。
<!--ja-->
第二の特殊化は、それ自身が対であるようなペイロードを扱い、二層の対は表現の中に入れ子になっています。`tagPairAtL s k a b` は「数項 `k` と、スロット `a` と `b` の対との対」という表現を読むので、`pr (# k) (pr (entry a) (entry b))` の形の項目を認識します。タグが二成分のペイロードの上に載ったものです。
<!--/-->

```agda
  (PairExpression.pair (PairExpression.numeral k)
    (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b))) id s

tagPairAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ tagPairAtL s k a b)
  ≡ PairIs (fst (lookup s γ))
```

<!--en-->
The adequacy lemma again computes directly from the generic one, recovering all three components: the tag numeral, and both payload entries after projection. The nesting is handled entirely inside the expression reader; at the level of these clauses nothing but the expression shape is visible.
<!--zh-->
充分性引理再次由一般引理直接计算而得，恢复全部三个分量：标签数码，以及投影后的两个载荷条目。嵌套完全在表达式读式内部处理；在这一层子句上，除表达式形状外什么都看不见。
<!--ja-->
妥当性の補題はここでも一般的なものから直接計算され、三つの成分すべてを、タグの数項と、射影後の二つのペイロードの項目とを取り戻します。入れ子は完全に表現の読み出しの内部で処理されます。この層の節から見えるのは、表現の形だけです。
<!--/-->

```agda
      (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ))))
tagPairAtL-adequate s k a b γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.numeral k)
    (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b))) id s γ
```

<!--en-->
## Sets by extension

The reader of the previous section recognizes a value through its Kuratowski pairing layers; many recursion clauses instead need to say what the members of a set are. Both are statements of the same kind: a first-order formula in the model that, read back in the ambient hierarchy, identifies the value held in a slot. This section builds the extensional shape.

`extAt`{.Agda} y φ says of the set in slot `y`{.Agda} that it has exactly the members satisfying a unary condition `φ`{.Agda}. Its outer structure is two unbounded universal quantifiers joined by an ordinary conjunction: one implication from membership in the set to `φ`{.Agda}, and one back. `extAt`{.Agda} itself adds no new propositional truncation, though the parameter `φ`{.Agda} is an arbitrary formula and may internally contain quantifiers and truncated existentials of its own. Because the outer evidence is a plain conjunction, its two readings are simply the projections of that conjunction, and its introduction is simply their ordered pair. This is the right level of strength for a description: the formula characterizes a candidate set and says nothing about whether one exists, which is a matter for the construction that later supplies the value.
<!--zh-->
## 以外延给出集合

上一节的结构读式经由 Kuratowski 配对层识别取值；而许多递归子句要说的却是「一个集合的成员是什么」。二者是同类陈述：模型中的一条一阶公式，读回周遭层级后，恰能指认槽位中的取值。本节构造外延形状。

`extAt`{.Agda} y φ 对槽位 `y`{.Agda} 中的集合断言：其成员恰为满足一元条件 `φ`{.Agda} 的对象。它的外层结构是两条无界全称量词经普通合取相连：一条从属于该集合推出 `φ`{.Agda}，一条反向。`extAt`{.Agda} 自身不引入新的命题截断，但参数 `φ`{.Agda} 是任意公式，内部可以含有自己的量词与截断存在。由于外层的证据只是普通的合取，它的两种读法就是该合取的两个投影，而它的引入也就是二者的有序对。这正是一条描述所需的强度：该公式刻画一个候选集合，对这样的集合是否存在不置一词；存在与否，属于日后给出该取值的构造的事。
<!--ja-->
## 外延によって集合を定める

前節の構造的な読みは Kuratowski 対の層を通して値を認識しましたが、多くの再帰の節が語りたいのは、ある集合の要素が何であるかということです。両者は同じ種類の主張、すなわち模型の中の一階の論理式が、周囲の階層へ読み戻されたときにスロットの値をちょうど指し示す、という形をしています。本節ではその外延的な形を作ります。

`extAt`{.Agda} y φ は、スロット `y`{.Agda} の集合について、その要素が一変数の条件 `φ`{.Agda} を満たす対象とちょうど一致することを述べます。外側の構造は、普通の連言で結ばれた二つの非有界な全称量化です。一方は集合への所属から `φ`{.Agda} への含意、もう一方は逆向きの含意です。`extAt`{.Agda} 自体は新たな命題の切り捨てを導入しませんが、パラメータ `φ`{.Agda} は任意の論理式であり、その内部に量化子や切り捨てられた存在を含むことはあります。外側の証拠が素の連言であるため、二つの読みは連言の射影そのもの、導入もそれらの順序対そのものになります。これは記述としてちょうどよい強さです。この論理式は候補となる集合を特徴づけるだけで、そのような集合が存在するかどうかには何も言いません。存在は、後で値を供給する構成の仕事です。
<!--/-->

<!--en-->
The definition binds one fresh variable for the candidates and is the conjunction of two unbounded universal quantifiers: every member of the set in slot `y`{.Agda} satisfies `φ`{.Agda}, and every satisfier is a member. The outer connective is an ordinary conjunction and `extAt`{.Agda} wraps neither implication in truncation, but the condition `φ`{.Agda} is passed through as given and may be any formula, with quantifiers or truncated existentials inside. What `extAt`{.Agda} itself fixes is only the outer shape: a pair of implications under a quantifier, each side being a function on model elements and their satisfaction proofs. That is exactly why the formula can serve as a description: it constrains a value without ever asserting one.
<!--zh-->
该定义为候选者绑定一个新变元，整体是两条无界全称量词的合取：槽位 `y`{.Agda} 中集合的每个成员满足 `φ`{.Agda}，而每个满足者也属于该集合。外层的联结词是普通合取，`extAt`{.Agda} 不把任何一条蕴含包进截断，但条件 `φ`{.Agda} 按原样传入，可以是任何公式，内部含有量词或截断存在均可。`extAt`{.Agda} 自身固定的只是外层形状：量词之下的一对蕴含，每侧都是模型元素及其满足证明上的函数。这正是该公式得以充当描述的原因：它约束一个取值，却从不断言取值的存在。
<!--ja-->
この定義は候補のための新しい変数を一つ束縛し、全体として二つの非有界な全称量化の連言です。すなわち、スロット `y`{.Agda} の集合のすべての要素が `φ`{.Agda} を満たすこと、そして `φ`{.Agda} を満たすすべてのものが要素であること。外側の結合子は普通の連言であり、`extAt`{.Agda} はどちらの含意も切り捨てで包みませんが、条件 `φ`{.Agda} はそのまま渡され、量化子や切り捨てられた存在を内部に含む任意の論理式であって構いません。`extAt`{.Agda} 自体が確定するのは外側の形だけです。量化子の下にある二つの含意の対であり、各側は模型の要素とその充足の証明の上の関数です。これこそ、この論理式が記述として機能する理由です。値を束縛するだけで、値の存在を主張することはないのです。
<!--/-->

```agda
extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
```

<!--en-->
The two readers are the two projections of the outer conjunction. From an inhabitant of `extAt y φ`, `extAt-out`{.Agda} takes the first component, which assigns to every model element `z`{.Agda} the implication from membership of `fst z`{.Agda} in the set at `y`{.Agda} to satisfaction of `φ`{.Agda} in the extended environment; `extAt-in`{.Agda} takes the second component, which gives that implication in reverse. Neither reader eliminates a truncation, chooses a witness, or transports along a path; whatever `φ`{.Agda} may contain internally, at this outer level the evidence is an ordered pair and each reader is literally a projection of it.
<!--zh-->
两个读式就是外层合取的两个投影。由 `extAt y φ` 的一个证明出发，`extAt-out`{.Agda} 取第一分量：它对每个模型元素 `z`{.Agda} 给出一条蕴含，从 `fst z`{.Agda} 属于槽位 `y`{.Agda} 处集合，到扩展环境中 `φ`{.Agda} 成立；`extAt-in`{.Agda} 取第二分量，给出反方向的同一条蕴含。两个读式都不消去截断、不选取见证、也不沿路径搬运；无论 `φ`{.Agda} 内部含有什么，在这一外层上证据就是一个有序对，而每个读式恰是它的投影。
<!--ja-->
二つの読みは、外側の連言の二つの射影です。`extAt y φ` の要素から出発して、`extAt-out`{.Agda} は第一の成分を取ります。これはすべての模型の要素 `z`{.Agda} に対して、`fst z`{.Agda} がスロット `y`{.Agda} の集合に属することから、拡張された環境での `φ`{.Agda} の充足への含意を割り当てます。`extAt-in`{.Agda} は第二の成分を取り、同じ含意を逆向きに与えます。どちらの読みも切り捨ての除去も証人の選択も経路に沿う輸送も行いません。`φ`{.Agda} の内部に何があっても、この外側の層では証拠は順序対であり、各読みは文字どおりその射影です。
<!--/-->

```agda
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd
```

<!--en-->
Introduction runs the projections in reverse and is the ordered pair of the two implications, each supplied as a function. Hence `extAt-in-both`{.Agda}: a clause that can establish both directions of its condition satisfies the formula by pairing the two functions, with no further work at the outer level; any quantifier or truncation work happens inside `φ`{.Agda} and is discharged there. The statement is worth reading as it stands: it produces an inhabitant of a satisfaction judgment from two functions, and asserts nothing about the existence of a set whose members satisfy `φ`{.Agda}. Whether such a set is ever supplied is decided where the value is constructed, not here.
<!--zh-->
引入把两个投影反向运行，就是那两条蕴含的有序对，各以函数形式给出。于是有 `extAt-in-both`{.Agda}：一个能同时建立其条件两个方向的子句，只需把两个函数配成对，便满足这条公式，外层无须再做任何事；量词或截断的工作都发生在 `φ`{.Agda} 内部，并在那里完成。这条陈述本身值得细读：它从两个函数造出满足判断的一个证明，而对「成员满足 `φ`{.Agda} 的集合是否存在」不作任何断言。这样的集合是否真的被给出，由构造取值之处决定，与此处无关。
<!--ja-->
導入は射影を逆向きに走らせるもので、二つの含意をそれぞれ関数として与えたときの順序対です。そこで `extAt-in-both`{.Agda} が成り立ちます。条件の両方向をともに確立できる節は、二つの関数を対にするだけでこの論理式を充足し、外側の層ではそれ以上の仕事は要りません。量化子や切り捨てに伴う仕事はすべて `φ`{.Agda} の内部で起き、そこで片づけられます。この主張はそのまま読む価値があります。二つの関数から充足の判断の要素を作るのであって、`φ`{.Agda} を満たす要素をもつ集合の存在については何も主張しません。そのような集合が実際に供給されるかどうかは、値が構成される側で決まる事柄であり、ここではありません。
<!--/-->

```agda

  extAt-in-both : ((z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
                → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
                → ⟨ γ ⊨ extAt y φ ⟩
  extAt-in-both f g = f , g


```

<!--en-->
## Reading a key in two layers

A key of the satisfaction recursion is a set assembled by two nested pairings: an arity paired with a code, and the code itself a tag numeral paired with a payload. Recognizing such a key by a bounded formula therefore means checking both pairing layers, and the structural reader already does this, since it handles expressions of arbitrary nesting. Each formula below is thus the reader applied to a suitable expression, and each adequacy lemma is the corresponding specialization of `PairExpression.adequate`{.Agda}. The arity is deliberately kept as a variable slot rather than fixed at a numeral, because a clause for a constructor that produces a subformula of different arity needs to speak about the arity value itself.
<!--zh-->
## 分两层读一个键

满足关系递归的键是一个由两层嵌套配对组装而成的集合：元数与一个码配成对，而码本身又是标签数码与载荷之对。因此用有界公式识别一个键，就意味着检查这两层配对；而结构读式本就处理任意嵌套的表达式，恰好胜任。于是下面的每条公式都是把该读式用于相应的表达式，每条充分性引理也都是 `PairExpression.adequate`{.Agda} 的相应特例。元数被有意保留为变元槽位而非固定为某个数码，因为那些会产出不同元数子公式的构造子，其子句需要谈论元数值本身。
<!--ja-->
## 二層の鍵を読む

充足関係の再帰における鍵は、二層の入れ子になった対から組み上げられた集合です。アリティと符号との対であり、符号そのものはタグの数項とペイロードとの対です。したがって有界な論理式で鍵を認識するとは、この二層の対を検査することですが、構造的な読みは任意の入れ子の式をすでに扱えるので、その任に十分に応えます。そこで以下の各論理式は適切な式に読みを適用したものであり、各妥当性補題は `PairExpression.adequate`{.Agda} の対応する特殊化です。アリティが数項に固定されず変数スロットとして残されているのは意図的なことです。異なるアリティの部分論理式を生む構成子の節は、アリティの値そのものについて語る必要があるからです。
<!--/-->

<!--en-->
`arityTagPairAtL c ar k a b`{.Agda} says that the set in slot `c`{.Agda} is the ordered pair whose first component is the set in slot `ar`{.Agda} and whose second component is itself a pairing: the numeral `# k`{.Agda} paired with the pair of the sets in slots `a`{.Agda} and `b`{.Agda}. The defining expression is `pair (slot ar) (pair (numeral k) (pair (slot a) (slot b)))`{.Agda}, read at `c`{.Agda} under the identity relabelling, and this is the shape of a key whose payload is a two-slot code.
<!--zh-->
`arityTagPairAtL c ar k a b`{.Agda} 断言槽位 `c`{.Agda} 中的集合是一个有序对：第一分量是槽位 `ar`{.Agda} 中的集合，第二分量本身又是一个配对，即数码 `# k`{.Agda} 与槽位 `a`{.Agda}、`b`{.Agda} 中集合之对的配对。定义表达式为 `pair (slot ar) (pair (numeral k) (pair (slot a) (slot b)))`{.Agda}，在恒等改名下于 `c`{.Agda} 处读取；这正是载荷为双槽位码的键的形状。
<!--ja-->
`arityTagPairAtL c ar k a b`{.Agda} は、スロット `c`{.Agda} の集合が順序対であることを述べます。第一成分はスロット `ar`{.Agda} の集合であり、第二成分はさらに、`# k`{.Agda} という数項とスロット `a`{.Agda}、`b`{.Agda} の集合の対との対です。定義式は `pair (slot ar) (pair (numeral k) (pair (slot a) (slot b)))`{.Agda} という形で、恒等リラベルの下で `c`{.Agda} において読まれます。これはペイロードが二スロットの符号である鍵の形状です。
<!--/-->

```agda
arityTagPairAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula S n
arityTagPairAtL c ar k a b = PairExpression.read
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k)
      (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b)))) id c
```

<!--en-->
The adequacy statement identifies the truth value of this formula with the proposition `PairIs (fst (lookup c γ)) (...)`{.Agda}, a path in the ambient hierarchy asserting that the set at `c`{.Agda} equals the nested Kuratowski pair built from the slot projections. The components can then be read off the right-hand side: the tag numeral `# k`{.Agda} is fixed, while `ar`{.Agda}, `a`{.Agda} and `b`{.Agda} each contribute their looked-up value. Since the statement is a path of truth values rather than a one-way implication, a later proof may rewrite with it in either direction.
<!--zh-->
充分性陈述把该公式的真值等同于命题 `PairIs (fst (lookup c γ)) (...)`{.Agda}，这是周遭层级中的一条路径，断言 `c`{.Agda} 处的集合等于由各槽位投影构造的嵌套 Kuratowski 对。各分量便可从右边读出：标签数码 `# k`{.Agda} 是固定的，而 `ar`{.Agda}、`a`{.Agda} 与 `b`{.Agda} 各自贡献其查得的值。由于该陈述是真理值之间的路径而非单向蕴含，后续证明可以在任一方向上用它改写。
<!--ja-->
妥当性の主張は、この論理式の真理値を命題 `PairIs (fst (lookup c γ)) (...)`{.Agda}、すなわち周囲の階層におけるパスと同一視します。これは `c`{.Agda} の集合が各スロットの射影から組み上げられた入れ子の Kuratowski 対に等しいと述べるものです。各成分は右辺から読み取れます。タグの数項 `# k`{.Agda} は固定されており、`ar`{.Agda}、`a`{.Agda}、`b`{.Agda} はそれぞれ参照された値を寄与します。この主張は一方向の含意ではなく真理値の間のパスなので、後の証明ではどちらの方向にも書き換えに使えます。
<!--/-->

```agda

arityTagPairAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagPairAtL c ar k a b)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ))
        (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ)))))
```

<!--en-->
The proof is a one-line specialization of `PairExpression.adequate`{.Agda} to the same expression, relabelling, and slot. The bounded witnesses, the elimination and introduction of truncated existentials, and the transport along the adequacy of `prAtL`{.Agda} were all discharged once in the structural theorem, so no new semantic argument appears here. With the pair-payload case in place, the one-payload variant `arityTagAtL c ar k a`{.Agda} is defined the same way, except that the innermost expression is the single slot `a`{.Agda} rather than a pair of two slots.
<!--zh-->
证明是 `PairExpression.adequate`{.Agda} 对同一表达式、同一改名与同一槽位的一行特例。有界见证、截断存在的消去与引入、以及沿 `prAtL`{.Agda} 充分性的搬运，都已在结构定理中一次性完成，故这里不再出现新的语义论证。双槽位载荷的情形就绪之后，单载荷变体 `arityTagAtL c ar k a`{.Agda} 以同样方式定义，唯一差别是最内层表达式是单个槽位 `a`{.Agda}，而非两个槽位之对。
<!--ja-->
証明は `PairExpression.adequate`{.Agda} を同じ式、同じリラベル、同じスロットに適用する一行の特殊化です。有界な証人、截断された存在の除去と導入、`prAtL`{.Agda} の妥当性に沿う輸送はすべて構造定理で一度に片づけられているため、ここに新しい意味論的議論は現れません。対ペイロードの場合が整うと、一つのペイロードを持つ変種 `arityTagAtL c ar k a`{.Agda} が同じ仕方で定義されます。違いは最も内側の式が二つのスロットの対ではなく単一のスロット `a`{.Agda} である点だけです。
<!--/-->

```agda
arityTagPairAtL-adequate c ar k a b γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k)
      (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b)))) id c γ

arityTagAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Formula S n
```

<!--en-->
The body applies the structural reader at `c`{.Agda} under the identity relabelling, and the adequacy statement again takes the form of a `PairIs`{.Agda} path: the set at `c`{.Agda} equals the arity value paired with `# k`{.Agda} paired with the value at `a`{.Agda}. This is the shape needed when a code's payload is a single slot rather than two, for instance one variable index or one subformula slot.
<!--zh-->
主体是在恒等改名下于 `c`{.Agda} 处应用结构读式，充分性陈述同样取 `PairIs`{.Agda} 路径的形式：`c`{.Agda} 处的集合等于元数值与「`# k`{.Agda} 与 `a`{.Agda} 处的值之对」的配对。当码的载荷是单个槽位而非两个时，需要的正是这个形状，例如一个变元指标或一个子公式槽位。
<!--ja-->
本体は恒等リラベルの下で `c`{.Agda} において構造的な読みを適用するものであり、妥当性の主張もやはり `PairIs`{.Agda} のパスの形をとります。すなわち `c`{.Agda} の集合は、アリティの値と「`# k`{.Agda} と `a`{.Agda} の値の対」との対に等しいということです。符号のペイロードが二つではなく単一のスロットである場合、たとえば変数の番号一つや部分論理式のスロット一つである場合に、必要なのはまさにこの形です。
<!--/-->

```agda
arityTagAtL c ar k a = PairExpression.read
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot a))) id c

arityTagAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagAtL c ar k a)
```

<!--en-->
The adequacy proof again cites `PairExpression.adequate`{.Agda} at the same expression and slot, mirroring the pair case. Both arity-tag formulas and both adequacy lemmas therefore rest on the one structural theorem, which is the return on building the reader generically. What is done with the recovered arity value belongs to the clauses of the satisfaction recursion, which are stated in `L.Coding.SatisfactionClauses`{.Agda}; this chapter supplies the shapes those clauses read.
<!--zh-->
充分性证明再次在同样的表达式与槽位上引用 `PairExpression.adequate`{.Agda}，与配对情形如出一辙。因此两个元数标签公式与两个充分性引理都立足于那一个结构定理，这正是把读式写成通用形式所得到的回报。至于恢复出的元数值之后如何使用，属于满足关系递归的子句，它们陈述于 `L.Coding.SatisfactionClauses`{.Agda}；本章给出的正是那些子句所读取的形状。
<!--ja-->
妥当性の証明はここでも、同じ式とスロットに対して `PairExpression.adequate`{.Agda} を引用するもので、対の場合と同じ作法です。したがって二つのアリティ付きタグ論理式と二つの妥当性補題は、唯一の構造定理の上に立ちます。読みを汎用的に作ったことの見返りがこれです。復元されたアリティの値をその後どう扱うかは、充足関係の再帰の節に属する事柄であり、それらの節は `L.Coding.SatisfactionClauses`{.Agda} で述べられます。本章が供給するのは、それらの節が読む形状です。
<!--/-->

```agda
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ)) (pr (# k) (fst (lookup a γ))))
arityTagAtL-adequate c ar k a γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot a))) id c γ
```

<!--en-->
## Looking a subcode up in the table

A satisfaction-table entry records, for a key made of an arity and a code, the set of environments satisfying that formula. Reading a subformula's value therefore means forming that key inside the object language: pairing the arity with the subcode and asserting equality with a candidate set. At the subformula's own arity, the table is universally scanned and the key equality guards an implication selecting the matching entry; when the subformula binds a variable, the same lookup is performed at a next arity witnessed internally by the successor formula of the following section.

## The shape of a clause

A clause of the recursion binds a code, its arity, its payload components, and the value recorded at the code, then asserts the tagged shape of the code and states one constructor-specific condition between the recorded values. Reading such a clause back is a chain of rewrites along the adequacy lemmas established in this chapter, and assembling one is those rewrites run backwards.

## The positive connectives

For conjunction and disjunction the constructor-specific condition is small: the value at the code is the pointwise conjunction, respectively pointwise disjunction, of the two subvalues, all read from the table at the same arity. Everything the clause needs beyond that condition is the lookup machinery above.

## The ambient environment set

`envSetAt`{.Agda} describes, by the extension characterization, the set of environments at the arity held in one slot, relative to the carrier in another. It characterizes that set; it does not construct one.
<!--zh-->
## 在表中查一个子码

满足关系表的一个条目记录的是：对由元数与码组成的键，满足该公式的环境之集。因此读取一个子公式的取值，意味着在对象语言内部构造那个键：把元数与子码配成对，并断言其与一个候选集合相等。在子公式自身的元数处，公式全称遍历表中条目，并以键相等作为蕴含的前件来选出相符条目；当子公式绑定变元时，同样的查表发生在下一个元数处，该元数由下一节的后继公式在内部给出见证。

## 一条子句的形状

递归的一条子句绑定码、其元数、其载荷分量以及表在该码处记录的取值，然后断言码的带标签形状，并在被记录的取值之间陈述一条构造子特有的条件。把子句读回去，是沿本章建立的诸充分性引理作一串改写；而组装一条子句，就是把这些改写反向运行。

## 正的联结词

对合取与析取而言，那条构造子特有的条件很小：码处的取值是两个子取值的逐点合取，或逐点析取，都从同一元数处的表读出。该条件之外子句所需的一切，就是上面的查表机制。

## 周遭环境集

`envSetAt`{.Agda} 以外延刻画描述一个集合：以一个槽位所存元数为元数、相对于另一槽位中的载体的环境之集。它刻画这个集合，而不构造它。
<!--ja-->
## 表から部分符号を引く

充足関係表のエントリは、アリティと符号からなる鍵に対して、その論理式を充足する環境の集合を記録します。したがって部分論理式の値を読むとは、その鍵を対象言語の内部で作ること、すなわちアリティと部分符号の対を作り、候補となる集合との等しさを主張することを意味します。部分論理式自身のアリティでは表の項目を全称量化し、鍵の等式を含意の前件として一致する項目を選びます。部分論理式が変数を束縛するときには、同じ参照が次のアリティで行われ、そのアリティは次節の後者の論理式が内部で証人となります。

## 節の共通形

再帰の一つの節は、符号、そのアリティ、ペイロードの成分、そして符号の位置に記録された値を束縛し、符号のタグ付きの形を述べ、記録された値の間で構成子ごとの条件を一つ述べます。節を読み戻すことは、本章で確立した妥当性の補題に沿った書き換えの連鎖であり、節を組み立てることは、その書き換えを逆向きに走らせることです。

## 正の結合子

論理積と論理和にとって、構成子ごとの条件は小さなものです。符号の位置の値は二つの部分値の逐点連言、それぞれ逐点選言であり、いずれも同じアリティの表から読み出されます。この条件のほかに節が要るものは、上の参照の仕組みだけです。

## 周囲の環境集合

`envSetAt`{.Agda} は、外延による特徴づけによって、あるスロットにあるアリティの、別のスロットの台の上での環境の集合を記述します。これは集合を特徴づけるのであって、構成するのではありません。
<!--/-->

<!--en-->
The definition applies the extension characterization at slot `E`{.Agda}, with the environment predicate `envOverAt`{.Agda} as the condition. That predicate classifies a candidate environment relative to a domain and a range, so the freshly bound variable of `extAt`{.Agda}, at position zero of the extended environment, plays the role of the candidate. The domain and range arguments appear as `suc ar`{.Agda} and `suc B`{.Agda} because the condition is evaluated in the extended environment, one arity above the slots the formula itself binds. By the projections `extAt-out`{.Agda} and `extAt-in`{.Agda}, an inhabitant of `envSetAt E ar B`{.Agda} is exactly a pair of implications saying that the set at `E`{.Agda} contains precisely those candidate environments over the arity recorded at `ar`{.Agda} that the carrier at `B`{.Agda} admits. The formula describes the set; its construction happens where the satisfaction table is built.
<!--zh-->
该定义把外延刻画施于槽位 `E`{.Agda}，条件取为环境谓词 `envOverAt`{.Agda}。这个谓词相对于一个定义域与一个值域，对单个候选环境加以分类，因此 `extAt`{.Agda} 新绑定的变元 (位于扩展环境的零号位置) 就扮演候选者的角色。定义域与值域的参数写作 `suc ar`{.Agda} 与 `suc B`{.Agda}，因为条件是在扩展环境中求值的，比公式自身绑定的槽位高一个元数。由投影 `extAt-out`{.Agda} 与 `extAt-in`{.Agda}，`envSetAt E ar B`{.Agda} 的证明恰给出一对蕴含：`E`{.Agda} 处的集合恰含那些以 `ar`{.Agda} 处记录的元数为元数、且为 `B`{.Agda} 处载体所容纳的候选环境。这条公式只描述集合；其构造发生在构造满足关系表之处。
<!--ja-->
この定義は、外延による特徴づけをスロット `E`{.Agda} に適用し、条件として環境の述語 `envOverAt`{.Agda} をとります。この述語は定義域と値域に対して一つの候補環境を分類するものなので、`extAt`{.Agda} が新たに束縛する変数 (拡張された環境の位置 0) が候補の役割を果たします。定義域と値域の引数が `suc ar`{.Agda} と `suc B`{.Agda} と現れるのは、条件が拡張された環境で評価されるからであり、論理式自身が束縛するスロットより一つアリティが上です。射影 `extAt-out`{.Agda} と `extAt-in`{.Agda} により、`envSetAt E ar B`{.Agda} の証明はちょうど二つの含意を与えるもの、すなわち `E`{.Agda} の集合が、`ar`{.Agda} に記録されたアリティの上で `B`{.Agda} の台が受け入れる候補環境をちょうど含む、と言うものになります。この論理式は集合を記述するだけで、その構成は充足関係表が作られる場所で行われます。
<!--/-->

```agda
envSetAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envSetAt E ar B = extAt E (envOverAt zero (suc ar) (suc B))


```

<!--en-->
## Implication and bottom

Among the logical clauses, implication and bottom stand apart from the positive connectives in the shape of their values. Bottom has no subcodes and its condition inside the common extension frame is false, so its value is empty; it still uses the frame's ambient environment set. Implication is interpreted over the set of all environments at the code's arity, so its clause must name that ambient set and constrain it extensionally; this is why the environment set of the previous section exists. A clause stated as an implication, and not as the join of a complement with the consequent, matches the truth algebra's function-space arrow; the direct implication matches the constructive semantics without invoking excluded middle.

## The next arity

`sucAtL`{.Agda} is the internal formula saying that the set in slot `j` is the `sucV` of the set in slot `i`; its adequacy lemma applies to arbitrary sets, without assuming that either is a numeral or an ordinal.

A clause whose subformula sits one arity higher must consult the table at an arity constrained to be the successor of the current one. The hierarchy-side formula `sucAt`{.Agda} expresses this set equation and names no constants. Lifting it requires the `BoundedFo InL` argument expected by `liftFo`; the separate theorem `Δ₀-sucAt` is used later by `transferFo` to justify bounded absoluteness.
<!--zh-->
## 蕴含与底

在诸逻辑子句之中，蕴含与底在取值形状上不同于正的联结词。底没有子码，并在共同的外延框架中以假为条件，故其取值为空；它仍使用框架所绑定的周遭环境集。蕴含则在该码元数处的全体环境之集上解释，故其子句必须点名那个周遭集合，并以外延方式约束它；这也正是上一节的环境之集存在的原因。蕴含写成蕴含式，而非「前件之补与后件之并」，才与真值代数的函数空间箭头相合；直接使用蕴含正合构造性语义，并不调用排中律。

## 下一个元数

`sucAtL`{.Agda} 是断言槽位 `j` 中的集合等于槽位 `i` 中集合之 `sucV` 的内部公式；其充分性引理适用于任意集合，并不假定两者是数码或序数。

当子公式比原式高一个元数时，子句必须在受约束为当前元数后继的元数处查询表。层级一侧的公式 `sucAt`{.Agda} 表达这一集合等式，且不点名常元。抬升它需要 `liftFo` 所要求的 `BoundedFo InL` 参数；另一个独立定理 `Δ₀-sucAt` 则稍后交给 `transferFo`，用来证明有界绝对性。
<!--ja-->
## 含意と偽

論理の節のうち、含意と偽は、その値の形において正の結合子と一線を画します。偽には部分符号がなく、共通の外延の枠組みの中で条件が偽なので、その値は空です。ただし枠組みが束縛する周囲の環境集合は使います。含意は、符号のアリティにおけるすべての環境の集合の上で解釈されるため、その節はその周囲の集合を名指し、外延的に制約しなければなりません。前節の環境の集合が存在するのはまさにこのためです。含意は「補集合と後件の結び」ではなく含意として述べられるとき、真理値代数の関数空間の矢印と一致します。含意を直接用いれば、排中律を呼び出さずに構成的な意味論と一致します。

## 次のアリティ

`sucAtL`{.Agda} は、スロット `j` の集合がスロット `i` の集合の `sucV` であることを述べる内部論理式です。その妥当性補題は任意の集合に適用でき、数項や順序数であることを仮定しません。

部分論理式が一つ高いアリティにある節は、現在のアリティの後続であると制約されたアリティで表を参照します。階層側の論理式 `sucAt`{.Agda} はこの集合の等式を表し、定数を含みません。持ち上げには `liftFo` が要求する `BoundedFo InL` の引数が必要です。これとは別の定理 `Δ₀-sucAt` は、後で `transferFo` に渡され、有界絶対性を正当化します。
<!--/-->

<!--en-->
The definition is `sucAtL i j = liftFo (sucAt i j) _`{.Agda}. Because `sucAt` names no constants, its `BoundedFo InL` argument contains no nontrivial constructibility witnesses. In the adequacy proof, `transferFo` receives that argument and, separately, `Δ₀-sucAt i j`, the hierarchy-side Δ₀ certificate. The result identifies satisfaction with `PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))`: the proposition that the set at `j` is the successor set of the set at `i`.
<!--zh-->
定义为 `sucAtL i j = liftFo (sucAt i j) _`{.Agda}。由于 `sucAt` 不含常元，其 `BoundedFo InL` 参数没有非平凡的常元可构造性见证。在充分性证明中，`transferFo` 分别接收这个参数与 `Δ₀-sucAt i j`，后者才是层级一侧的 Δ₀ 证书。所得路径把满足等同于 `PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))`：即槽位 `j` 的集合是槽位 `i` 集合的后继集这一命题。
<!--ja-->
定義は `sucAtL i j = liftFo (sucAt i j) _`{.Agda} です。`sucAt` は定数を含まないため、その `BoundedFo InL` の引数には非自明な定数の構成可能性の証人はありません。妥当性の証明では、`transferFo` はこの引数と、階層側の Δ₀ 証明書である `Δ₀-sucAt i j` とを別々に受け取ります。得られるパスは充足を `PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))`、すなわちスロット `j` の集合がスロット `i` の集合の後続集合であるという命題と同一視します。
<!--/-->

```agda
sucAtL : ∀ {n} → Fin n → Fin n → Formula S n
sucAtL i j = liftFo (sucAt i j) _

sucAtL-adequate : ∀ {n} (i j : Fin n) (γ : S ^ n)
  → (γ ⊨ sucAtL i j) ≡ PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))
sucAtL-adequate i j γ =
```

<!--en-->
The proof composes three paths. The transfer lemma first equates satisfaction of the lifted formula in `L` with ambient satisfaction of `sucAt i j` at the projected assignment `map fst γ`{.Agda}, using the boundedness certificate; the transfer rests on the established transitive-model setup. The hierarchy-side adequacy theorem `sucAt-adequate`{.Agda} then rewrites that satisfaction as the equality of the interpreted values. Finally, the two lookups of the projected assignment are moved to projections of the lookups in `γ` by `lookup-fst`{.Agda}, `sucV`{.Agda} is moved inside by congruence, and the equation is reassembled under `PairIs`{.Agda} by `cong₂`{.Agda}. The result is the identification stated.
<!--zh-->
证明串联三条路径。转换引理先借有界性证书，把抬升公式在 `L` 中的满足等同于 `sucAt i j` 在投影赋值 `map fst γ`{.Agda} 处的周遭满足；该转换立足于既有的传递模型设置。层级一侧的充分性定理 `sucAt-adequate`{.Agda} 随后把那个满足改写为被解释取值之间的等式。最后，`lookup-fst`{.Agda} 把投影赋值处的两次查表换成 `γ` 中查表后的投影，同余把 `sucV`{.Agda} 移到内部，再由 `cong₂`{.Agda} 在 `PairIs`{.Agda} 之下重新组装等式。所得即所陈述的等同。
<!--ja-->
証明は三つのパスを連結します。まず転送の補題が有界性の証明書を使い、持ち上げられた論理式の `L` での充足を、射影された割り当て `map fst γ`{.Agda} での `sucAt i j` の周囲の充足と等しいとします。転送は確立された推移的モデルの設定に依拠します。次に階層側の妥当性定理 `sucAt-adequate`{.Agda} が、その充足を解釈された値の間の等式へ書き換えます。最後に `lookup-fst`{.Agda} が射影された割り当てでの二度の参照を `γ` での参照の射影へ移し、合同が `sucV`{.Agda} を内側へ移し、`cong₂`{.Agda} が等式を `PairIs`{.Agda} の下で組み立て直します。得られるのは述べられた同一視です。
<!--/-->

```agda
    transferFo (sucAt i j) _ (Δ₀-sucAt i j) γ
  ∙ sucAt-adequate i j (map fst γ)
  ∙ cong₂ PairIs (lookup-fst j γ) (cong sucV (lookup-fst i γ))

```

<!--en-->
## Extending an environment

`consAtL`{.Agda} describes extending an environment by a new leading value, and its adequacy lemma identifies the resulting coded environment exactly.

A quantified body is evaluated after adjoining a value at the front of the current environment. The hierarchy-side formula `consAt`{.Agda} already characterizes this operation, while `consAtL`{.Agda} will express the same characterization inside the constructible model. Its lift requires boundedness certificates for the singleton, pairing, tagging, and key-shifting relations from which the coded extension is assembled. These relations introduce no constant numeral: the distinguished tag is the empty set, and the new head value is read from slot `m`{.Agda}. The separate lemma `numL`{.Agda}, defined immediately below, records the constructibility of ambient numerals for later bounded formulas that do name them.
<!--zh-->
## 扩展一个环境

`consAtL`{.Agda} 描述以一个新的首值扩展环境，其充分性引理准确对应所得的码化环境。

量词主体在当前环境前添入一个取值后求值。层级一侧的公式 `consAt`{.Agda} 已刻画这一运算，`consAtL`{.Agda} 则要在可构造模型内部表达同一刻画。抬升所需的有界性证书分别对应组成码化扩展的单集、配对、标签和键移位关系。这些关系没有引入常元数码：指定标签是空集，而新的首值从槽位 `m`{.Agda} 读取。紧接着在此定义的独立引理 `numL`{.Agda} 记录周遭数码的可构造性，供确实点名数码的其他有界公式使用。
<!--ja-->
## 環境を拡張する

`consAtL`{.Agda} は新しい先頭値による環境の拡張を記述し、その妥当性補題が得られる符号化環境を正確に同一視します。

量化された本体は、現在の環境の先頭に値を一つ加えた環境で評価されます。階層側の論理式 `consAt`{.Agda} はこの操作をすでに特徴づけており、`consAtL`{.Agda} は同じ特徴づけを構成可能模型の内部で表します。持ち上げには、符号化された拡張を組み立てる単集合、対、タグ、鍵の移動の各関係について有界性の証明が必要です。これらの関係は定数の数項を導入しません。指定されたタグは空集合であり、新しい先頭値はスロット `m`{.Agda} から読まれます。直後にここで定義される独立の補題 `numL`{.Agda} は、数項を実際に名指す別の有界論理式のために、周囲の数項の構成可能性を記録します。
<!--/-->

<!--en-->
`numL k`{.Agda} is defined here and proves the ambient numeral `# k`{.Agda} constructible. The internal numeral `numeralL k`{.Agda} already carries constructibility of its projection, and `numeralL-fst k`{.Agda} identifies that projection with `# k`{.Agda}; transporting the certificate along this path gives `⟨ isL (# k) ⟩`{.Agda}. The following private definitions provide `BoundedFo InL` data for the formulas used to recognize the empty tag, combining bounded shape with constructibility witnesses for any constants they contain. In particular, `sgl0At k`{.Agda} characterizes the set in slot `k`{.Agda} as `{∅}`: it has an empty member and every one of its members is empty. `bddSgl0` supplies that combined data; it is not a separate Δ₀ theorem.
<!--zh-->
`numL k`{.Agda} 在此定义，并证明周遭数码 `# k`{.Agda} 可构造。内部数码 `numeralL k`{.Agda} 已带有其投影可构造的证明，`numeralL-fst k`{.Agda} 把该投影与 `# k`{.Agda} 等同；沿此路径搬运证书，便得到 `⟨ isL (# k) ⟩`{.Agda}。随后的私有定义为识别空标签的公式提供 `BoundedFo InL` 数据：既记录有界形状，也为其中出现的常元给出可构造性见证。其中 `sgl0At k`{.Agda} 把槽位 `k`{.Agda} 中的集合刻画为 `{∅}`：它有一个空成员，并且每个成员都是空的。`bddSgl0` 给出这种组合数据，而不是一条独立的 Δ₀ 定理。
<!--ja-->
`numL k`{.Agda} はここで定義され、周囲の数項 `# k`{.Agda} が構成可能であることを示します。内部数項 `numeralL k`{.Agda} はその射影の構成可能性をすでに備え、`numeralL-fst k`{.Agda} がその射影を `# k`{.Agda} と同一視します。このパスに沿って証明を輸送すると `⟨ isL (# k) ⟩`{.Agda} が得られます。続く非公開の定義は、空のタグを認識する論理式について `BoundedFo InL` のデータを与えます。これは有界な形と、現れる定数の構成可能性の証人を組み合わせたものです。特に `sgl0At k`{.Agda} はスロット `k`{.Agda} の集合を `{∅}` と特徴づけます。空の要素をもち、すべての要素が空であるという条件です。`bddSgl0` はこの組み合わせたデータを与えるもので、独立な Δ₀ 定理ではありません。
<!--/-->

```agda
numL : (k : ℕ) → InL (# k)
numL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

private
  bddSgl0 : ∀ {n} (k : Fin n) → BoundedFo InL (sgl0At k)
  bddSgl0 k = (_ , (_ , _)) , (_ , (_ , _))
```

<!--en-->
`pair0At k j`{.Agda} characterizes the set in slot `k`{.Agda} as the unordered pair `{∅, W}`, where `W` is the value of the original assignment at slot `j`{.Agda}; under its inner binder that same value is addressed by `suc j`{.Agda}. It is not a Kuratowski pair of the two slot values. The formula `tag0At s x`{.Agda} then combines `sgl0At`{.Agda} and `pair0At`{.Agda}: its two distinguished members are `{∅}` and `{∅, W}`, so the set at `s`{.Agda} is the Kuratowski pair `pr ∅ W`. The certificates `bddPair0`{.Agda} and `bddTag0`{.Agda} supply `BoundedFo InL` data for these descriptions, including the required constructibility witnesses for constants.
<!--zh-->
`pair0At k j`{.Agda} 把槽位 `k`{.Agda} 中的集合刻画为无序对 `{∅, W}`，其中 `W` 是原赋值槽位 `j`{.Agda} 的取值；进入内部量词后，同一取值由 `suc j`{.Agda} 指向。它并不是两个槽位取值的 Kuratowski 对。`tag0At s x`{.Agda} 再组合 `sgl0At`{.Agda} 与 `pair0At`{.Agda}：两个指定成员分别是 `{∅}` 与 `{∅, W}`，所以槽位 `s`{.Agda} 中的集合就是 Kuratowski 对 `pr ∅ W`。`bddPair0`{.Agda} 与 `bddTag0`{.Agda} 为这些描述给出 `BoundedFo InL` 数据，其中包括所需的常元可构造性见证。
<!--ja-->
`pair0At k j`{.Agda} は、スロット `k`{.Agda} の集合を非順序対 `{∅, W}` と特徴づけます。ここで `W` は元の割り当てのスロット `j`{.Agda} の値であり、内側の量化子に入ると同じ値を `suc j`{.Agda} が指します。二つのスロットの値からなる Kuratowski 対ではありません。`tag0At s x`{.Agda} は `sgl0At`{.Agda} と `pair0At`{.Agda} を組み合わせます。指定された二要素が `{∅}` と `{∅, W}` なので、スロット `s`{.Agda} の集合は Kuratowski 対 `pr ∅ W` です。`bddPair0`{.Agda} と `bddTag0`{.Agda} は、これらの記述の `BoundedFo InL` データを与え、必要な定数の構成可能性の証人も含みます。
<!--/-->

```agda

  bddPair0 : ∀ {n} (k j : Fin n) → BoundedFo InL (pair0At k j)
  bddPair0 k j = (_ , (_ , _)) , ((_ , _) , (_ , ((_ , _) , (_ , _))))

  bddTag0 : ∀ {n} (s x : Fin n) → BoundedFo InL (tag0At s x)
  bddTag0 {n} s x =
      (_ , bddSgl0 {suc n} zero)
```

<!--en-->
The remainder of `bddTag0`{.Agda} pairs the singleton certificate, used for the empty-set tag itself, with the pair certificates for the outer and inner pairing layers. After it, `bddShift`{.Agda} certifies `shiftPairAt p' p`{.Agda}, which recognizes the entry at `p'`{.Agda} as obtained from the entry at `p`{.Agda} by replacing its numeral key with its successor while keeping the paired value unchanged; the certificate is written as a single placeholder because the formula's bounded subformulas are again the leaves and bounded quantifiers already covered.
<!--zh-->
`bddTag0`{.Agda} 的其余部分把用于空集标签本身的单集证书，与外、内两层配对的证书配成对。其后 `bddShift`{.Agda} 为 `shiftPairAt p' p`{.Agda} 作证：`p'`{.Agda} 处的条目是由 `p`{.Agda} 处的条目把其数码键换成其后继、而配对的值保持不变所得；这里证书写成一个占位符，因为该公式的有界子公式仍是已被覆盖的叶子与有界量词。
<!--ja-->
`bddTag0`{.Agda} の残りの部分は、空集合タグ自体に使う単集合の証明書と、外側と内側の対の層のための証明書とを対にします。その後の `bddShift`{.Agda} は `shiftPairAt p' p`{.Agda} を証明します。すなわち `p'`{.Agda} の項目は、`p`{.Agda} の項目の数項の鍵をその後者に置き換え、対になった値はそのままにして得られるものとして認識されます。ここで証明書を単一のプレースホルダとして書けるのは、論理式の有界な部分論理式が、すでに扱った葉と有界量化子と同じだからです。
<!--/-->

```agda
    , ( (_ , bddPair0 {suc n} zero (suc x))
      , (_ , (bddSgl0 {suc n} zero , bddPair0 {suc n} zero (suc x))) )

  bddShift : ∀ {n} (p' p : Fin n) → BoundedFo InL (shiftPairAt p' p)
  bddShift p' p = _

  bddCons : ∀ {n} (e' m e : Fin n) → BoundedFo InL (consAt e' m e)
```

<!--en-->
`bddCons`{.Agda} assembles everything the extension formula needs. Reading its three conjuncts: the extended graph holds an entry that is the empty-set tag over the value at `m`{.Agda}, the new leading entry, certified by `bddTag0`{.Agda} at the shifted slot; every entry of the old graph reappears with its key shifted to the successor, certified by `bddShift`{.Agda} two arities up; and the remaining conjunct repeats the same two certificates for the membership direction that reads back out of the extension. Each conjunct's certificate lives at the depth its quantifiers create, which is why the arities in the annotations grow to `suc (suc n)`{.Agda}.
<!--zh-->
`bddCons`{.Agda} 装配扩展公式所需的一切。按其三个合取项来读：扩展后的图持有一个条目，即架在 `m`{.Agda} 处之值上的空集标签，也就是新的首条目，由移位槽位处的 `bddTag0`{.Agda} 作证；旧图的每个条目带其后移的键重现，由高两个元数处的 `bddShift`{.Agda} 作证；其余合取项为从扩展中向外读出的隶属方向重复这两个证书。每个合取项的证书位于其量词所创造的深度，这正说明注记中的元数增长到 `suc (suc n)`{.Agda}。
<!--ja-->
`bddCons`{.Agda} は拡張の論理式が必要とするすべてを組み立てます。三つの連言を読むと、拡張されたグラフは `m`{.Agda} の値の上に載った空集合タグである項目、すなわち新しい先頭の項目を保持し、ずらしたスロットでの `bddTag0`{.Agda} が証明します。旧グラフの各項目は鍵を後者へずらして現れ、二つアリティが上の `bddShift`{.Agda} が証明します。残りの連言は、拡張の外へ読み出す所属の方向について同じ二つの証明書を繰り返します。各連言の証明書はその量化子が作る深さに置かれるため、注釈のアリティが `suc (suc n)`{.Agda} まで増えるのです。
<!--/-->

```agda
  bddCons {n} e' m e =
      (_ , bddTag0 {suc n} zero (suc m))
    , ( (_ , (_ , bddShift {suc (suc n)} zero (suc zero)))
      , (_ , ( bddTag0 {suc n} zero (suc m)
             , (_ , bddShift {suc (suc n)} (suc zero) zero) )) )
```

<!--en-->
With the boundedness certificates assembled, `consAtL e' m e`{.Agda} is the lift of the hierarchy-side formula `consAt e' m e`{.Agda} through `liftFo`{.Agda}, supplied with `bddCons`{.Agda} as its certificate. Its adequacy statement is conditional where the successor's was not: it takes a family `g : Fin k → V ℓ`{.Agda} together with a proof `hE`{.Agda} that the set held in slot `e`{.Agda} is the coded environment `env g`{.Agda}. Under that hypothesis, satisfaction of `consAtL e' m e`{.Agda} is identified, as a truth value, with `PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))`{.Agda}: the set at `e'`{.Agda} is exactly the coded environment obtained by pushing the value at `m`{.Agda} onto the front of `g`. The formula classifies a candidate against an environment that is already coded; it does not construct one, and the hypothesis about the old environment is precisely what makes the classification well-defined.
<!--zh-->
有界性证书装配齐备之后，`consAtL e' m e`{.Agda} 就是层级一侧公式 `consAt e' m e`{.Agda} 经 `liftFo`{.Agda} 的抬升，其证书由 `bddCons`{.Agda} 提供。它的充分性陈述带有一个后继情形所没有的条件：给定一个族 `g : Fin k → V ℓ`{.Agda}，以及「槽位 `e`{.Agda} 中的集合是码化环境 `env g`{.Agda}」的证明 `hE`{.Agda}。在该假设下，`consAtL e' m e`{.Agda} 的满足作为一个真值被等同于 `PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))`{.Agda}：`e'`{.Agda} 处的集合恰是把 `m`{.Agda} 处的取值推到 `g` 前端所得的码化环境。这条公式是针对一个已被码化的环境作分类，而非构造环境；关于旧环境的那个假设，正是使这一分类适定的前提。
<!--ja-->
有界性の証明書がそろうと、`consAtL e' m e`{.Agda} は階層側の論理式 `consAt e' m e`{.Agda} を `liftFo`{.Agda} で持ち上げたものであり、その証明書として `bddCons`{.Agda} が与えられます。この妥当性の主張には、後者の場合にはなかった条件が付きます。族 `g : Fin k → V ℓ`{.Agda} と、スロット `e`{.Agda} に置かれた集合が符号化環境 `env g`{.Agda} であるという証明 `hE`{.Agda} を仮定するのです。その仮定の下で、`consAtL e' m e`{.Agda} の充足は、真理値として `PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))`{.Agda} と同一視されます。すなわち `e'`{.Agda} の集合は、`m`{.Agda} の値を `g` の先頭に付け加えて得られる符号化環境にほかなりません。この論理式は、すでに符号化された環境に対して候補を分類するものであって、環境を構成するものではありません。旧環境についての仮定こそ、この分類を意味の定まったものにする前提です。
<!--/-->

```agda

consAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
consAtL e' m e = liftFo (consAt e' m e) (bddCons e' m e)

consAtL-adequate : ∀ {n} (e' m e : Fin n) (γ : S ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → fst (lookup e γ) ≡ env g
```

<!--en-->
The proof opens with the transfer lemma, given all its inputs at once: the formula `consAt e' m e`{.Agda}, its boundedness certificate `bddCons`{.Agda}, and the Δ₀ certificate `Δ₀-consAt`{.Agda} recorded on the hierarchy side. The transfer is bounded absoluteness in action, and it depends on the established transitive-model setup: because `L` is transitive and every constant the formula names is constructible, satisfaction of the lifted formula in the carrier moves to satisfaction of the original formula at the projected assignment `map fst γ`{.Agda}, where ambient facts can be stated directly.
<!--zh-->
证明以转换引理开场，一次给足它的全部输入：公式 `consAt e' m e`{.Agda}、其有界性证书 `bddCons`{.Agda}、以及层级一侧记录的 Δ₀ 证书 `Δ₀-consAt`{.Agda}。这一步是有界绝对性的实际运用，并依赖于既已建立的传递模型设置：由于 `L` 传递、且公式点名的每个常元都可构造，抬升公式在载体中的满足，就移为原公式在投影赋值 `map fst γ`{.Agda} 处的满足，而在那里周遭的事实可以直接陈述。
<!--ja-->
証明は転送の補題から始まり、その入力は一度にすべて与えられます。論理式 `consAt e' m e`{.Agda}、その有界性の証明書 `bddCons`{.Agda}、そして階層側で記録された Δ₀ の証明書 `Δ₀-consAt`{.Agda} です。このステップは有界絶対性の実際の働きであり、確立された推移的モデルの設定に依存します。`L` が推移的であり、論理式が名指す定数がすべて構成可能であることから、持ち上げられた論理式の台での充足は、射影された割り当て `map fst γ`{.Agda} での元の論理式の充足へと移ります。そこでは周囲の事実を直接述べることができます。
<!--/-->

```agda
  → (γ ⊨ consAtL e' m e)
  ≡ PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))
consAtL-adequate e' m e γ g hE =
    transferFo (consAt e' m e) (bddCons e' m e) (Δ₀-consAt e' m e) γ
  ∙ consAt-adequate e' m e (map fst γ) g
```

<!--en-->
The hierarchy-side adequacy theorem `consAt-adequate`{.Agda} then rewrites ambient satisfaction as the identification of the new slot with the extended coded environment. It requires the hypothesis in projected form, which is why `lookup-fst e γ`{.Agda} is composed with `hE`{.Agda} on the way in: the projection of the entry at `e`{.Agda} equals `env g`{.Agda}. Congruence then moves the two remaining lookups, the value at `e'`{.Agda} by `lookup-fst`{.Agda}, and the value at `m`{.Agda} by `cong`{.Agda} under the function `λ w → env (cons w g)`{.Agda}. The chain of paths ends exactly at the promised `PairIs`{.Agda} identification, and this closes the chapter's own mathematics: every internal formula needed to recognize syntax shapes, arities, environments, and their extension is in place.
<!--zh-->
层级一侧的充分性定理 `consAt-adequate`{.Agda} 随后把周遭满足改写为新槽位与扩展后的码化环境的等同。它需要假设以投影形式给出，这正是入口处把 `lookup-fst e γ`{.Agda} 与 `hE`{.Agda} 串联的原因：`e`{.Agda} 处条目的投影等于 `env g`{.Agda}。接着，同余移走剩下的两次查表：`e'`{.Agda} 处的取值由 `lookup-fst`{.Agda} 处理，`m`{.Agda} 处的取值在函数 `λ w → env (cons w g)`{.Agda} 之下由 `cong`{.Agda} 处理。路径链条的终点恰是所允诺的 `PairIs`{.Agda} 等同。本章自身的数学至此收束：识别语法形状、元数、环境及其扩展所需的每条内部公式都已就位。
<!--ja-->
階層側の妥当性定理 `consAt-adequate`{.Agda} は次に、周囲の充足を、新しいスロットと拡張された符号化環境との同一視へ書き換えます。仮定は射影された形で必要なので、入り口で `lookup-fst e γ`{.Agda} が `hE`{.Agda} と連結されます。すなわち `e`{.Agda} の項目の射影は `env g`{.Agda} に等しいのです。続いて合同が残る二度の参照を移します。`e'`{.Agda} の値は `lookup-fst`{.Agda} で、`m`{.Agda} の値は関数 `λ w → env (cons w g)`{.Agda} の下で `cong`{.Agda} で処理されます。経路の連鎖は約束された `PairIs`{.Agda} の同一視でちょうど終わります。これで本章固有の数学は閉じます。構文の形、アリティ、環境、そしてその拡張を認識するのに必要な内部論理式は、すべてここに揃いました。
<!--/-->

```agda
      (lookup-fst e γ ∙ hE)
  ∙ cong₂ PairIs (lookup-fst e' γ)
      (cong (λ w → env (cons w g)) (lookup-fst m γ))

```

<!--en-->
## The unbounded quantifiers

The two unbounded-quantifier clauses use the common bounded frame `extB`, which binds the ambient environment set `F` and extension data before applying the quantifier-specific body. In `quBody q`, the parameter `q` is the outer quantifier over the carrier set `w`: it is bounded existential for `∃` and bounded universal for `∀`. The inner formula `∃̇∈ ya (consAtL ...)`, which says that the extended environment occurs in the body's recorded value, is unchanged in both cases. Thus the universal case changes only the outer quantifier to implication semantics; it does not replace an innermost conjunction.

## Evaluating a term, and the atoms

A term is a variable or a constant, so the clause evaluating a coded term has two cases: a variable's value is what the environment records at its key, while a constant's value is the constant itself, in any environment at all. The two atoms then evaluate both term codes and compare the resulting values, one asserting membership and the other equality; their payload is a pair of term codes, at which the satisfaction table has no entries, which is why the clause builds the lookups itself rather than taking them from a frame.

## The bounded quantifiers

A bounded quantifier's payload is a term code paired with a formula code. The bound is evaluated in the environment by the two-case reader, the body's value is read one arity higher, and the pushed values are restricted to elements of the evaluated bound as well as of the carrier. Ranging over the carrier as well as the bound is not redundant: the reference semantics quantifies over the carrier and guards by membership in the bound, and a bound may have members outside the carrier, so quantifying over the bound alone would demand entries the table does not have.

## Recap

This chapter built first-order formulas with which a satisfaction clause recognizes compound values inside `L`. Three kinds of statement carry it. The structural adequacy of the expression reader identifies, in both directions, the satisfaction of a formula about slots, literals, numerals, and Kuratowski pairs with the equality of the projected entry to the denoted ambient value, the pair case passing through a constructible intermediate set. The extensional characterization `extAt`{.Agda} is an ordinary conjunction of two universally quantified implications, whose readings and introduction are projections and pairing. And the internal successor and environment-extension formulas are lifted by bounded absoluteness over the transitive model, with the adequacy paths composed from the transferred satisfaction, the hierarchy-side theorems, and the compatibility of lookups under projection. On these the clause shapes of the coded satisfaction recursion rest.
<!--zh-->
## 无界量词

两条无界量词子句使用共同的有界框架 `extB`；它先绑定周遭环境集 `F` 与扩展数据，再应用量词专有的主体。在 `quBody q` 中，参数 `q` 是遍历载体集 `w` 的外层量词：存在情形取有界存在，全称情形取有界全称。内部公式 `∃̇∈ ya (consAtL ...)` 表示扩展环境出现在主体所记录的取值中，在两种情形下都不改变。因此，全称情形只把外层量词改成蕴含语义，并没有把某个最内层合取改成蕴含。

## 求一个词项的值，与两个原子

一个词项是变元或常元，故求值码化词项的子句有两种情形：变元的取值是环境在其键处记录的东西，而常元的取值就是那个常元，在任何环境中都一样。两个原子随后求出两个词项码的值并在模型中比较所得，其一断言隶属，另一断言相等；它们的载荷是一对词项码，满足关系表在该处没有条目，这正是该子句自行构造查表、而不由框架代劳的原因。

## 有界量词

有界量词的载荷是「词项码与公式码的对」。界由两情形的求值读式在环境中求值，主体的取值在高一个元数处读出，而被推入的取值同时限于载体与所得界中的元素。同时遍历载体与那个界并非冗余：参照语义是在载体上作量化、再以「属于那个界」设防，而一个界完全可以有落在载体之外的成员；只在那个界上作量化，就会索要表所没有的条目。

## 小结

本章建立了码化满足关系的子句在 `L` 内部识别复合取值所需的一阶公式。支撑它的是三类陈述。表达式读式的结构充分性在两个方向上把「关于槽位、字面常元、数码与 Kuratowski 对的公式」的满足，等同于「投影条目与所指周遭取值」的相等，配对情形经由一个可构造的中间集合完成。外延刻画 `extAt`{.Agda} 是两条全称蕴含的普通合取，其读法与引入就是投影与配对。内部的后继公式与环境扩展公式由传递模型上的有界绝对性抬升，其充分性路径由转换后的满足、层级一侧的定理、以及查值在投影下的相容性串联而成。码化满足关系递归的诸子句形状正立足于此。
<!--ja-->
## 非有界量化子

二つの非有界量化子の節は、共通の有界な枠 `extB` を使います。この枠は周囲の環境集合 `F` と拡張のデータを束縛してから、量化子固有の本体を適用します。`quBody q` では、引数 `q` は台の集合 `w` を走る外側の量化子であり、存在の場合は有界存在、全称の場合は有界全称です。拡張された環境が本体に記録された値に現れることを述べる内側の論理式 `∃̇∈ ya (consAtL ...)` は、どちらの場合にも変わりません。したがって全称の場合に変わるのは外側の量化子だけで、最も内側の連言を含意へ置き換えるのではありません。

## 項の評価と二つの原子論理式

項は変数か定数です。したがって符号化された項を評価する節には二つの場合があります。変数の値は環境がその鍵に記録するものであり、定数の値はその定数そのものであり、どの環境でも同じです。二つの原子論理式はその後、両方の項の符号を評価して、得られた値を模型の中で比較します。一方は所属を、他方は等式を主張します。そのペイロードは項の符号の対であり、充足関係表にはそこにエントリがないため、この節は枠組みに任せずに自分で参照を作るのです。

## 有界量化子

有界量化子のペイロードは、項の符号と論理式の符号の対です。境界は二つの場合をもつ評価の読みによって環境の中で評価され、本体の値はひとつアリティ上で読まれ、付け加えられる値は台と評価された境界の両方の要素に限られます。台と境界の両方を渡ることは冗長ではありません。参照意味論は台の上で量化し、境界への所属で防ぎます。境界は台の外に要素をもつことも十分にあり得るので、境界だけを渡る量化は、表がもたないエントリを要求することになります。

## まとめ

本章は、符号化された充足関係の節が `L` の内部で複合的な値を認識するための一階論理式を組み立てました。それを支えるのは三種類の主張です。表現の読みの構造的な妥当性は、スロット、リテラル、数項、Kuratowski 対についての論理式の充足を、両方向で、射影された項目と指示された周囲の値の等しさと同一視します。対の場合は構成可能な中間集合を通って行われます。外延的な特徴づけ `extAt`{.Agda} は二つの全称含意の普通の連言であり、その読みと導入は射影と対です。そして内部の後者の論理式と環境拡張の論理式は、推移的モデルの上の有界絶対性によって持ち上げられ、その妥当性の経路は転送された充足、階層側の定理、射影の下での参照の相容性から連結されます。符号化充足関係の再帰を成す節の形状は、この上に立ちます。
<!--/-->
