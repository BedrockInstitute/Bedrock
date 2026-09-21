<!--en-->
# The square law for infinite L-cardinals

For an infinite cardinal `κ` of `L`, the set of ordered pairs of members of `κ` injects into `κ` itself, by an internal coded injection. This chapter builds that injection. The route runs through the Gödel order on pairs: the order is written as a formula of the first-order object language, read off at the ordinal `κ` as the external Gödel order, and collapsed to an order type that the counting lemmas compare with `κ`. The chapter works at a fixed universe level `ℓ`, under excluded middle at the next level, the one classical assumption on which the ordinal comparisons below depend.
<!--zh-->
# L 中无穷基数的平方律

对 `L` 中的无穷基数 `κ`，其成员的有序对所成之集可经 `L` 内部的编码单射注入 `κ` 自身。本章构造这个单射。路线经由对上的 Gödel 序：把这条序写成第一阶对象语言的公式，在序数 `κ` 处读作外部的 Gödel 序，再塌缩到序型，由计数引理与 `κ` 比较。本章在固定的宇宙层级 `ℓ` 上工作，使用高一层的排中律，即下文所有序数比较所依赖的唯一经典假设。
<!--ja-->
# L の無限基数における平方律

`L` の無限基数 `κ` に対し、その要素の順序対からなる集合は、`L` の内部での符号化された単射によって `κ` 自身へ注入される。本章はこの単射を構成する。道筋は対の上の Gödel 順序を経由する。順序を一階の対象言語の論理式として書き下し、順序数 `κ` のところで外部の Gödel 順序として読み、崩壊によって順序型へ落とし、計数の補題によって `κ` と比較する。本章は固定された宇宙レベル `ℓ` の上で、一つ上のレベルの排中律、すなわち以下の順序数の比較が依存する唯一の古典的仮定のもとで進む。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The construction is not constructive throughout, and the reason lies in the mathematics rather than in the formalism. To order the pairs of an ordinal one must decide, for two ordinals `a` and `b`, whether `a` belongs to `b`; and every classical decision of this chapter is an instance of that single question. The module therefore receives excluded middle at level `ℓ-suc ℓ` as explicit data, the level of the membership propositions being decided.
<!--zh-->
这一构造并非处处构造性的，其原因在数学而不在形式化。要为序数的有序对排序，就必须对两个序数 `a` 与 `b` 判定 `a` 是否属于 `b`；本章的每个经典判定都是这同一个问题的实例。模块因此以显式数据接收层级 `ℓ-suc ℓ` 上的排中律，那正是被判定隶属命题所在的层级。
<!--ja-->
この構成がすべて構成的なわけではなく、その理由は形式化ではなく数学にある。順序数の対を順序づけるには、二つの順序数 `a` と `b` について `a` が `b` に属するかを判定しなければならない。本章の古典的な判定はどれもこの一つの問いの実例である。そこでモジュールは、レベル `ℓ-suc ℓ` の排中律を明示的なデータとして受け取る。判定される所属の命題の住むレベルである。
<!--/-->

```agda
open import Base.Prelude
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Base.Classical using ( LEM )

```

<!--en-->
The module parameter fixes that instance once, and every classical step of the chapter consumes precisely it.
<!--zh-->
模块参数一次性固定这个实例，本章的每个经典步骤消耗的恰是它。
<!--ja-->
モジュールパラメータはその実例を一度だけ固定し、本章の古典的な段階はどれも正確にこれを消費する。
<!--/-->

```agda
module L.GCH.CardinalSquareLaw {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The order to be internalized is written in the first-order object language: formulas built from membership and equality atoms by the connectives, negation and the unbounded existential, interpreted over the ambient hierarchy. Two facts of the hierarchy stand beside it, and both are used to end arguments: membership is well-founded, so ordinals admit induction along `∈`, and no set belongs to itself, so impossible comparisons can be refuted outright.
<!--zh-->
将被内在化的序用一阶对象语言写出：由隶属与相等两种原子经联结词、否定和无界存在量词生成的公式，在外围层级上解释。层级自身还有两条事实伴随其侧，二者都用于收束论证：隶属是良基的，故序数允许沿 `∈` 作归纳；并且没有集合属于自身，故不可能的比较可被直接反驳。
<!--ja-->
内在化される順序は、一階の対象言語で書かれる。所属と等しさ (等号) の原子式から、結合子、否定、非有界の存在量化子によって作られる論理式であり、周囲の階層の上で解釈される。階層の二つの事実がその傍らにあり、どちらも議論を閉じるために使われる。所属は整礎であり、順序数は `∈` に沿った帰納を許し、またどの集合も自分自身に属さないため、あり得ない比較はそのまま反証できる。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
```

<!--en-->
Reading the coordinates of a coded pair, and counting with them, rests on three facts. The successor operation on ordinals is injective, so equal successors have equal predecessors. Every member of an ordinal is named by an index of its small presentation, the naming is injective, and a member of a constructible set is itself constructible. And the ordered pair `pr` is injective in both coordinates, so a coded pair determines its two entries.
<!--zh-->
读取编码对的坐标并以其计数，依赖三个事实。序数的后继运算是单射的，故相等的后继有相同的前驱。序数的每个成员都由其小呈现的一个索引指名，该命名单射，且可构造集的成员自身可构造。有序对 `pr` 在两个坐标上都是单射的，故编码对确定其两个分量。
<!--ja-->
符号化された対の座標を読み、それで計数するには、三つの事実が要る。順序数の後続演算は単射であり、等しい後続は等しい先行者をもつ。順序数の各要素は小さな提示の添字によって名指され、その名指しは単射で、構成可能な集合の要素はそれ自身構成可能である。そして順序対 `pr` は両座標で単射であり、符号化された対はその二つの成分を確定する。
<!--/-->

```agda
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( ord-suc-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
```

<!--en-->
On the constructible side, the inner structure `𝒮ʟ` restricts the hierarchy to the transitive class of constructible sets. The ordinal facts used throughout are closure facts: members of ordinals are ordinals, successors of ordinals are ordinals, the members of `ω` are ordinals, and any two ordinals are comparable by trichotomy. Beside them stands the external Gödel order on pairs, the order this chapter internalizes.
<!--zh-->
在可构造一侧，内层结构 `𝒮ʟ` 把层级限制到可构造集这个传递类。全章使用的序数事实都是封闭性事实：序数的成员是序数，序数的后继是序数，`ω` 的成员是序数，且任意两个序数经三歧性可比。与它们并列的，是本章所要内在化的、对上的外部 Gödel 序。
<!--ja-->
構成可能な側では、内側の構造 `𝒮ʟ` が階層を構成可能な集合という推移的クラスに制限する。全体を通して使う順序数の事実は閉性の事実である。順序数の要素は順序数であり、順序数の後続は順序数であり、`ω` の要素は順序数であり、任意の二つの順序数は三分法によって比較できる。その傍らには、対の上の外部の Gödel 順序、すなわち本章が内在化する順序がある。
<!--/-->

```agda
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω; ω-mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
```

<!--en-->
The comparison of two ordinals is packaged as three-case data rather than as a truth value, because the proofs below must inspect which case occurred: strictly below, equal, or strictly above. The empty set and `ω` are available as elements of `L`, and the internal successor numerals come with the identification of their underlying sets, which lets a numeral slot be read as an ambient natural number.
<!--zh-->
两个序数的比较被打包成三歧数据而非真值，因为下文的证明必须检查出现了哪种情形：严格小于、相等、或严格大于。空集与 `ω` 都可作为 `L` 的元素使用，内部的后继数码则带有对其底层集合的等同，使数码槽位能读作外围自然数。
<!--ja-->
二つの順序数の比較は、真理値ではなく三つの場合のデータとしてまとめられる。下の証明は、どの場合が起こったかを検査しなければならないからである。狭義に下、等しい、狭義に上。空集合と `ω` は `L` の要素として使え、内部の後続数詞はその基底集合の同一視を伴い、数項のスロットを周囲の自然数として読めるようにする。
<!--/-->

```agda
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( lt; eq; gt ) renaming ( Tri to TriW )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
```

<!--en-->
Inside `L`, ordered pairs and graph conditions are expressed by first-order formulas with inner and ambient readings. Pairing adequacy identifies the coded pair with the ambient ordered pair of its two entries, while the graph readings express single-valuedness, domain, injectivity, and containment of values in the codomain. Together these conditions describe an internal coded injection.
<!--zh-->
在 `L` 内部，有序对与图条件由具有内外两种读法的一阶公式表达。配对充分性把编码对等同于其两个分量组成的外围有序对；图的读法则表达单值性、定义域、单射性及取值属于陪域。合在一起，这些条件刻画内部编码单射。
<!--ja-->
`L` の内部では、順序対とグラフの条件を、内側と外側の二つの読みをもつ一階論理式で表す。対の妥当性は符号化された対を二つの成分からなる周囲の順序対と同一視し、グラフの読みは単値性、定義域、単射性、値が終域に属することを表す。これらの条件が内部の符号化された単射を記述する。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-out; domAt )
open import L.Coding.Expressions {ℓ} using ( sucAtL; sucAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt; module Extract; module Small )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL; IsCardinalL; _↪_ )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
```

<!--en-->
Three mathematical transitions drive the construction. An ordinal is replaced by an internal cardinal representative contained in it and internally equipotent to it. A definable injective function yields a coded injection. Finally, a well-founded transitive relation is collapsed to an ordinal order type, while trichotomy makes the collapse map injective.
<!--zh-->
构造由三个数学转换推动。首先，以包含于原序数且在内部与之等势的内部基数代表替代该序数；其次，可定义单射函数给出编码单射；最后，把良基且传递的关系塌缩为序数序型，并由三歧性证明塌缩映射单射。
<!--ja-->
構成は三つの数学的な移行によって進む。まず順序数を、その中に含まれ、内部でそれと同じ濃度をもつ内部基数の代表に替える。次に、定義可能な単射関数から符号化された単射を得る。最後に、整礎で推移的な関係を順序数としての順序型へ崩壊し、三分法によって崩壊写像の単射性を示す。
<!--/-->

```agda
open import L.GCH.CardinalRepresentative {ℓ} lem using ( cardOf )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )
open import L.InjectionComposition {ℓ} lem
  using ( appC; appC-adequate; ω-limit; finite-excl-ω )
```

<!--en-->
A comparison of two coded pairs carries six dependent witnesses: four coordinates and their two maxima. Products retain the simultaneous equations and order conditions, while disjoint sums retain the alternative comparison cases. Since the proof components are propositions, they do not create additional choices in the resulting order data.
<!--zh-->
两个编码对的比较携带六个相互依赖的见证：四个坐标及其两个最大值。积保存同时成立的等式与次序条件，不交和保存不同的比较情形。由于证明分量都是命题，它们不会在所得序数据中引入额外选择。
<!--ja-->
二つの符号化された対の比較は、四つの座標と二つの最大値という六つの依存する証人を伴う。積は同時に成り立つ等式と順序条件を保ち、非交和は比較の場合分けを保つ。証明の成分は命題なので、得られる順序データに余分な選択を生じさせない。
<!--/-->

```agda
```

<!--en-->
The coordinates of a coded pair are members of the underlying set of `κ`, read through the small presentation of that set. Beside the presentation stand the ambient membership, the empty set with its emptiness proof, and `ω` with the successor operation, the notions in which the two coordinates are compared and counted.
<!--zh-->
编码对的坐标是 `κ` 底层集合的成员，须借助该集合的小呈现读取。与呈现并列的还有外围隶属、带空虚性证明的空集，以及 `ω` 与后继运算，坐标的比较与计数正是在这些概念中进行。
<!--ja-->
符号化された対の座標は、`κ` の基底集合の要素であり、その集合の小さな提示を通して読まれる。提示の傍らには、周囲の所属、空虚性の証明を伴う空集合、そして `ω` と後続の演算があり、座標の比較と計数はこれらの概念の中で行われる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
```

<!--en-->
Three logical forms recur. Well-foundedness appears as accessibility data for every element, which is what lets the collapse descend along the order. Refutations live in the empty type. And a condition that only asserts that witnesses exist is stated under truncation, which is enough because the goals that consume such conditions are themselves propositions or truncations.
<!--zh-->
三种逻辑形式反复出现。良基性表述为每个元素的可及性数据，正是它使塌缩能沿序下降。反驳居住在空类型中。而只断言见证存在的条件在截断之下陈述，这已经足够，因为消费这些条件的目标本身就是命题或截断。
<!--ja-->
三つの論理形式が繰り返し現れる。整礎性はすべての要素への到達可能性のデータとして現れ、これが崩壊を順序に沿って下降させる。反証は空の型に住み、証人の存在だけを主張する条件は切り詰めの下で述べられる。そのような条件を消費する目標がそれ自身命題や切り詰めであるため、それで十分なのである。
<!--/-->

```agda
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Induction.WellFounded as WF
```

<!--en-->
Two carriers are named and kept apart. The ambient carrier carries the hierarchy's own membership; the inner carrier `S` consists of the constructible sets, each an ambient set with its constructibility proof, and its membership is the ambient membership read on the underlying sets.
<!--zh-->
两个载体被命名并保持区分。外围载体承载层级自身的隶属；内层载体 `S` 由可构造集组成，每个元素是一个外围集合连同其可构造性证明，其隶属就是在外围集合上读取的外围隶属。
<!--ja-->
二つの台が名指され、区別して保たれる。周囲の台は階層本来の所属を運び、内側の台 `S` は構成可能な集合からなり、各要素は周囲の集合とその構成可能性の証明の対であり、その所属は基底の集合の上で読んだ周囲の所属である。
<!--/-->

```agda

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
module SV = hPropStructure 𝒮ᵥ using ()
module SL = hPropStructure 𝒮ʟ using (S; _∈ˢ_)
open SL using ( S )

```

<!--en-->
The absoluteness instance is fixed over the transitive class of constructible sets: bounded formulas mean the same inside `L` as outside, environments are read through the projection, and the inner satisfaction relation is renamed to plain `_⊨_`.
<!--zh-->
绝对性实例固定在可构造集这个传递类上：有界公式在 `L` 内外的含义相同，环境经投影读取，内层满足关系被改名为朴素的 `_⊨_`。
<!--ja-->
絶対性の実例は、構成可能な集合という推移的クラスの上で固定される。有界な論理式は `L` の内側でも外側でも同じ意味を持ち、環境は射影を通して読まれ、内側の充足関係は平易な `_⊨_` に改名される。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using (_^_; _⊨ᵐ_)
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
The inner carrier is an h-set, and this is what makes equality of its elements manageable. Its elements are pairs whose second components are propositions, so two elements are equal exactly when their underlying sets are, and the pair-path lemma builds the equality of two pairs from equalities of their components.
<!--zh-->
内层载体是 h-集合，这使其元素的相等易于处理。其元素是第二分量为命题的对，所以两个元素恰在其底层集合相等时相等；对路径引理则由各分量的等式构造两个对的等式。
<!--ja-->
内側の台は h-集合であり、そのため要素の等しさを扱える。要素は第二成分が命題である対なので、二つの要素が等しいのは基底集合が等しいときに限る。対のパスの補題は、各成分の等しさから二つの対の等しさを構成する。
<!--/-->

```agda
isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))
opaque
  pair≡ : {A : Type ℓ} {B : Type ℓ} {a a' : A} {b b' : B}
        → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
```

<!--en-->
The pair path is exactly that construction: from `a ≡ a'` and `b ≡ b'` it forms, pointwise, the path `(a , b) ≡ (a' , b')`. Ordinals are constructible, and for a direct reason: an ordinal `x` is a member of its own successor, whose stage is a set of `L`, and membership in a stage is constructibility. The statement is a proposition, so its proof carries no information beyond the fact.
<!--zh-->
对路径正是这一构造：由 `a ≡ a'` 与 `b ≡ b'` 逐点得到路径 `(a , b) ≡ (a' , b')`。序数是可构造的，理由直接：序数 `x` 属于它自己的后继，而那个层是 `L` 的集合，属于层即是可构造。该陈述是命题，故其证明在事实之外不携带任何信息。
<!--ja-->
対のパスはまさにこの構成である。`a ≡ a'` と `b ≡ b'` から、各点で `(a , b) ≡ (a' , b')` というパスを作る。順序数は構成可能である。その理由は直接である。順序数 `x` はみずからの後続に属し、その段階は `L` の集合であり、段階への所属が構成可能性だからである。この主張は命題なので、証明は事実の外には何も運ばない。
<!--/-->

```agda
  pair≡ e1 e2 = λ i → e1 i , e2 i
opaque
  isL-ord : (x : V ℓ) → IsOrd x → ⟨ isL x ⟩
  isL-ord x ox = Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)

```

<!--en-->
Thus an ordinal `x` can be regarded as the element `ordL x ox` of the constructible carrier. Applying definable separation to the relation saying that both coordinates belong to `K` then produces `prodL K`, the constructible set of their ordered pairs.
<!--zh-->
因此，序数 `x` 可连同其可构造性证明视为可构造载体的元素 `ordL x ox`。再对「两个坐标都属于 `K`」这一关系施行可定义分离，便得到由这些有序对组成的可构造集合 `prodL K`。
<!--ja-->
したがって順序数 `x` は、その構成可能性の証明とともに、構成可能な台の要素 `ordL x ox` とみなせる。二つの座標がともに `K` に属するという関係に定義可能分出を適用すると、それらの順序対からなる構成可能集合 `prodL K` が得られる。
<!--/-->

```agda
ordL : (x : V ℓ) → IsOrd x → S
ordL x ox = x , isL-ord x ox
open import L.InjectionComposition {ℓ} lem public using ( module Relation )
private
  module Product (K : S) = Relation K K
```

<!--en-->
The describing condition of the product says that both coordinates are members of `K`. Its host reading is the ambient membership of the two projections in the underlying set of `K`, and both directions of the reading are supplied.
<!--zh-->
乘积的描述条件说：两个坐标都是 `K` 的成员。其在宿主一侧的读法，是两个投影在 `K` 的底层集合中的外围隶属，且该读法的两个方向都已给出。
<!--ja-->
積の記述の条件は、二つの座標がともに `K` の要素であることを述べる。ホスト側の読みは、二つの射影の `K` の基底集合への周囲の所属であり、その読みの両方向が与えられる。
<!--/-->

```agda
    ((var (suc zero) ∈̇ con K) ∧̇ (var zero ∈̇ con K))
    (λ x y → (fst x ∈ˢ fst K) ⊓ (fst y ∈ˢ fst K))
    (λ x y e h → h) (λ x y e h → h)

```

<!--en-->
`prodL K` is therefore the set of the ordered pairs of two members of `K`, separated inside `L` from the stage that bounds them.
<!--zh-->
于是 `prodL K` 就是由 `K` 的两个成员组成的有序对之集，在 `L` 内部从约束它们的层中分离而来。
<!--ja-->
したがって `prodL K` は、`K` の二つの要素からなる順序対の集合であり、`L` の内部でそれらを抑える段階から分出されたものである。
<!--/-->

```agda
prodL : S → S
prodL = Product.rel

```

<!--en-->
Membership in the product is characterized by a truncated existence: some two members `a` and `b` of `K` with the member equal to their ordered pair. The truncation records exactly what the condition asserts, that witnesses exist, and at this point nothing distinguishes one pair of witnesses from another; removing it becomes possible only after the uniqueness of the witnesses has been proved.
<!--zh-->
乘积中的隶属由一条截断的存在陈述刻画：存在 `K` 的两个成员 `a` 与 `b`，使该成员等于它们的有序对。截断如实记录条件所断言的内容，即见证存在，而在此处没有任何东西能区分一对见证与另一对；只有先证明见证唯一，才谈得上消去截断。
<!--ja-->
積への所属は、切り詰められた存在によって特徴づけられる。`K` の二つの要素 `a` と `b` があって、その要素がそれらの順序対に等しい、と。切り詰めは、条件が証人の存在を主張する以上のことを記録しない。この段階では、ある証人の対を別の対と区別する何ものもなく、切り詰めを取り除くことは、証人の一意性が証明された後にはじめて可能になる。
<!--/-->

```agda
InProd : S → V ℓ → Type (ℓ-suc ℓ)
InProd K e = ∥ Σ[ a ∈ S ] Σ[ b ∈ S ]
               (⟨ fst a ∈ˢ fst K ⟩ × ⟨ fst b ∈ˢ fst K ⟩
                × (e ≡ pr (fst a) (fst b))) ∥₁

```

<!--en-->
Inward, the ordered pair of any two members of `K` belongs to `prodL K`; this is the separated relation's own introduction rule.
<!--zh-->
向内：`K` 的任意两个成员的有序对属于 `prodL K`；这正是那条被分离关系自身的引入规则。
<!--ja-->
内向きには、`K` の任意の二つの要素の順序対が `prodL K` に属する。これは分出された関係そのものの導入規則である。
<!--/-->

```agda
prodL-in : (K a b : S) → ⟨ fst a ∈ˢ fst K ⟩ → ⟨ fst b ∈ˢ fst K ⟩
         → ⟨ pr (fst a) (fst b) ∈ˢ fst (prodL K) ⟩
prodL-in K a b ma mb = Product.into K a b ma mb (ma , mb)

```

<!--en-->
Outward, a member of `prodL K` comes, in truncated form, from two members of `K` and the pair equation. Against the small presentation of `K` the stronger, untruncated statement is available: every member of the product is the ordered pair of the elements named by two indices of `K`.
<!--zh-->
向外：`prodL K` 的成员以截断的形式来自 `K` 的两个成员与那条对等式。对照 `K` 的小呈现，更强而不截断的陈述也可用：乘积的每个成员都是 `K` 的两个索引所指名元素组成的有序对。
<!--ja-->
外向きには、`prodL K` の要素は、切り詰められた形で `K` の二つの要素と対の等式から来る。`K` の小さな提示に対しては、切り詰めのないより強い主張も使える。積のすべての要素は、`K` の二つの添字が名指す要素の順序対なのである。
<!--/-->

```agda
prodL-out : (K e : S) → ⟨ fst e ∈ˢ fst (prodL K) ⟩ → InProd K (fst e)
prodL-out K e h = map₁ (λ { (a , b , q , ma , mb) → a , b , ma , mb , q }) (Product.out K e h)
prodL-fst : (K e : S) → ⟨ fst e ∈ˢ fst (prodL K) ⟩
          → Σ[ a ∈ ⟪ fst K ⟫ ] Σ[ b ∈ ⟪ fst K ⟫ ]
              (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b))
```

<!--en-->
The proof converts the truncated witnesses into the fibers of `K`'s indexing, and repairs the pair equation along the fibers' own identifications, which say that each member of `K` is exactly the set its index names.
<!--zh-->
证明把截断的见证转换为 `K` 的索引的纤维，并沿纤维自身的等同，即「`K` 的每个成员恰是其索引所指名的集合」，修复那条对等式。
<!--ja-->
証明は、切り詰められた証人を `K` の索引のファイバーへ変換し、対の等式をファイバー自身の同定に沿って修復する。その同定は、`K` の各要素がまさにその索引の名指す集合であることを述べる。
<!--/-->

```agda
prodL-fst K e h = rec₁ isPropFib
  (λ { (a , b , ma , mb , q) →
     fiber (fst K) ma .fst , fiber (fst K) mb .fst
     , q ∙ cong₂ pr (sym (fiber (fst K) ma .snd)) (sym (fiber (fst K) mb .snd)) })
  (prodL-out K e h)
```

<!--en-->
The second components are unique: the injectivity of the ordered pair extracts an equation of the named sets, and the injectivity of `K`'s indexing turns it into an equation of indices.
<!--zh-->
第二分量是唯一的：有序对的单射性提取出所指名集合的等式，而 `K` 的索引的单射性把它变成索引的等式。
<!--ja-->
第二成分は一意である。順序対の単射性が名指された集合の等式を取り出し、`K` の索引の単射性がそれを添字の等式へ変える。
<!--/-->

```agda
  where
  inner : (a : ⟪ fst K ⟫)
        → isProp (Σ[ b ∈ ⟪ fst K ⟫ ] (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b)))
  inner a (b , q) (b' , q') = Σ≡Prop (λ _ → setIsSet _ _)
    (↪-inj {a = fst K} (pr-inj (sym q ∙ q') .snd))
```

<!--en-->
The first components are unique for the same reason, so the whole fiber statement is a proposition: the untruncated reading does not depend on any choice.
<!--zh-->
第一分量基于同样的理由唯一，于是整条纤维陈述是一个命题：不截断的读法不依赖任何选取。
<!--ja-->
第一成分も同じ理由で一意であり、したがってファイバーの主張全体が命題になる。
<!--/-->

```agda
  isPropFib : isProp (Σ[ a ∈ ⟪ fst K ⟫ ] Σ[ b ∈ ⟪ fst K ⟫ ]
                        (fst e ≡ pr (⟪ fst K ⟫↪ a) (⟪ fst K ⟫↪ b)))
  isPropFib (a , b , q) (a' , b' , q') = Σ≡Prop inner
    (↪-inj {a = fst K} (pr-inj (sym q ∙ q') .fst))
```

<!--en-->
## The Gödel order, as a formula
<!--zh-->
## 作为公式的 Gödel 序
<!--ja-->
## 論理式としての Gödel 順序
<!--/-->

<!--en-->
With the product in hand, the order enters: `MaxIs` says that `m` is the maximum of `a` and `b` when these are ordinals.
<!--zh-->
乘积到手之后，序登场：当 `a` 与 `b` 为序数时，`MaxIs` 说 `m` 是它们的最大值。
<!--ja-->
切り詰めのない読みはどの選択にも依存しない。積を手にしたところで、順序が登場する。`MaxIs` は、`a` と `b` が順序数であるとき、`m` がそれらの最大値であることを述べる。
<!--/-->

```agda
MaxIs : S → S → S → Type (ℓ-suc ℓ)
```

<!--en-->
The definition offers two alternatives: either `a` belongs to `b` and `m` is `b`, or membership of `a` in `b` is refuted and `m` is `a`. Only the disjunction is truncated, because the definition asserts that one of the alternatives holds without deciding which; on ordinals, excluded middle selects the branch, and the selected `m` is then the maximum of `a` and `b`.
<!--zh-->
定义给出两个选项：要么 `a` 属于 `b` 且 `m` 是 `b`，要么「`a` 属于 `b`」被反驳且 `m` 是 `a`。被截断的只是这个析取，因为定义只断言两个选项之一成立而不判定是哪一个；在序数上，排中律将选出分支，被选出的 `m` 便是 `a` 与 `b` 的最大值。
<!--ja-->
定義は二つの選択肢を提示する。`a` が `b` に属し `m` が `b` であるか、`a` の `b` への所属が反証され `m` が `a` であるか。切り詰められるのはこの選言だけである。定義は、どちらかの選択肢が成り立つと主張するだけで、どちらかを判定しないからである。順序数の上では排中律が分枝を選び、選ばれた `m` が `a` と `b` の最大値になる。
<!--/-->

```agda
MaxIs m a b =
  ∥ (⟨ fst a ∈ˢ fst b ⟩ × (fst m ≡ fst b))
  ⊎ ((⟨ fst a ∈ˢ fst b ⟩ → ⊥₀) × (fst m ≡ fst a)) ∥₁

```

<!--en-->
The Gödel comparison of two pairs is likewise data under truncation: either the maximum `m` of the first pair belongs to the maximum `n` of the second, or the two maxima are equal and the pairs compare lexicographically, first coordinate against first coordinate, then second against second.
<!--zh-->
两个对的 Gödel 比较同样是截断之下的数据：要么第一对的最大值 `m` 属于第二对的最大值 `n`，要么两个最大值相等，此时按字典序比较，先比第一坐标，再比第二坐标。
<!--ja-->
二つの対の Gödel 比較も同じく切り詰めの下のデータである。第一の対の最大値 `m` が第二の対の最大値 `n` に属するか、二つの最大値が等しいときは辞書式に比較する。第一座標どうし、ついで第二座標どうしである。
<!--/-->

```agda
OrdIs : S → S → S → S → S → S → Type (ℓ-suc ℓ)
OrdIs m n a b c d =
  ∥ ⟨ fst m ∈ˢ fst n ⟩
  ⊎ ((fst m ≡ fst n)
     × ∥ ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩) ∥₁) ∥₁
```

<!--en-->
The maximum is expressible as a bounded formula: `m` equals `b` when `a` belongs to `b`, and equals `a` when membership of `a` in `b` is refuted, the negation making the second alternative a guarded branch. When `a` and `b` are ordinals, this formula says precisely that `m` is their maximum.
<!--zh-->
最大值可写成一条有界公式：当 `a` 属于 `b` 时 `m` 等于 `b`，当 `a` 属于 `b` 被反驳时等于 `a`；否定词使第二个选项成为受守卫的分支。当 `a` 与 `b` 为序数时，这条公式说的恰是 `m` 是它们的最大值。
<!--ja-->
最大値は有界な論理式として書ける。`a` が `b` に属するとき `m` は `b` に等しく、`a` の `b` への所属が反証されるとき `a` に等しい。否定が第二の選択肢を守られた分枝として立てる。`a` と `b` が順序数であるとき、この論理式が述べるのはまさに、`m` がそれらの最大値であることである。
<!--/-->

```agda

maxAt : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
maxAt m a b = ((var a ∈̇ var b) ∧̇ (var m ≐ var b))
            ∨̇ ((¬̇ (var a ∈̇ var b)) ∧̇ (var m ≐ var a))

```

<!--en-->
The Gödel comparison is expressible the same way, with its priorities made explicit: first the maxima are compared; when the maxima are equal, the first coordinates are compared; and when the first coordinates are equal as well, the second coordinates are compared.
<!--zh-->
Gödel 比较也可同样写出，且其优先级是显式的：先比较两个最大值；最大值相等时比较第一坐标；第一坐标也相等时再比较第二坐标。
<!--ja-->
Gödel の比較も同じやり方で書ける。その優先順位は明示的である。まず最大値を比較し、最大値が等しいときは第一座標を比較し、第一座標も等しいときには第二座標を比較する。
<!--/-->

```agda
ordAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
ordAt m n a b c d =
    (var m ∈̇ var n)
  ∨̇ ((var m ≐ var n)
     ∧̇ ((var a ∈̇ var c) ∨̇ ((var a ≐ var c) ∧̇ (var b ∈̇ var d))))
```

<!--en-->
Putting the pieces together, `Lt p q` says that `p` and `q` are coded pairs, of members `a`, `b` and of members `c`, `d`, whose maxima `m` and `n` satisfy the maximum conditions and whose comparison satisfies the Gödel condition. The six witnesses are recorded under truncation: the conditions assert that witnesses exist, and the classical case analysis selects among the alternatives only afterwards.
<!--zh-->
把各部分合起来，`Lt p q` 说：`p` 与 `q` 是编码对，分别由成员 `a`、`b` 与成员 `c`、`d` 组成，其最大值 `m` 与 `n` 满足最大值条件，其比较满足 Gödel 条件。六个见证在截断之下记录：这些条件只断言见证存在，而经典情形分析是随后才在诸选项间作出选择。
<!--ja-->
部品を合わせると、`Lt p q` は次のように述べる。`p` と `q` は符号化された対であり、それぞれ要素 `a`、`b` と要素 `c`、`d` からなり、その最大値 `m` と `n` は最大値の条件を満たし、その比較は Gödel の条件を満たす、と。六つの証人は切り詰めの下に記録される。条件が主張するのは証人の存在だけであり、古典的な場合分けが選択肢の中から選ぶのはその後である。
<!--/-->

```agda

Lt : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Lt p q = ∥ Σ[ a ∈ S ] Σ[ b ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ] Σ[ m ∈ S ] Σ[ n ∈ S ]
           ( (p ≡ pr (fst a) (fst b)) × (q ≡ pr (fst c) (fst d))
           × MaxIs m a b × MaxIs n c d × OrdIs m n a b c d ) ∥₁

```

<!--en-->
Six binders need six slots beyond the caller's environment, and `↑6` shifts an index by exactly that many positions.
<!--zh-->
六个约束子需要超出调用者环境的六个槽位，`↑6` 恰好把索引移动这么多位置。
<!--ja-->
六つの束縛子には、呼び出し側の環境を超える六つのスロットが要り、`↑6` は添字をちょうどその数だけずらす。
<!--/-->

```agda
private
  ↑6 : ∀ {k} → Fin k → Fin (suc (suc (suc (suc (suc (suc k))))))
  ↑6 i = suc (suc (suc (suc (suc (suc i)))))

```

<!--en-->
The six slots are named `i0` through `i5`, one per quantified witness. The first aliases bind positions zero, one and two, which will hold the maximum of the second pair, the maximum of the first pair, and the second coordinate of the second pair.
<!--zh-->
六个槽位被命名为 `i0` 到 `i5`，每个量化见证一个。前三条别名绑定第零、第一、第二位置，它们将容纳第二对的最大值、第一对的最大值、以及第二对的第二坐标。
<!--ja-->
六つのスロットには `i0` から `i5` までの名前が付き、量化された証人ごとに一つである。最初の三つの別名は位置 0、1、2 を束縛し、そこには第二の対の最大値、第一の対の最大値、第二の対の第二座標が入る。
<!--/-->

```agda
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc zero
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
```

<!--en-->
The aliases continue: position two is filled by the second coordinate of the second pair, position three by its first coordinate, position four by the second coordinate of the first pair.
<!--zh-->
别名继续：第二位由第二对的第二坐标填充，第三位由其第一坐标填充，第四位由第一对的第二坐标填充。
<!--ja-->
別名は続く。位置 2 には第二の対の第二座標が、位置 3 にはその第一座標が、位置 4 には第一の対の第二座標が入る。
<!--/-->

```agda
  i2 = suc (suc zero)
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc (suc (suc zero))
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
  i4 = suc (suc (suc (suc zero)))
```

<!--en-->
Position five is the first coordinate of the first pair, completing the six. The order formula itself then begins: it will bind the six witnesses in sequence and say of `p` and `q` exactly what the Gödel comparison requires.
<!--zh-->
第五位是第一对的第一坐标，六个至此齐备。序公式随之开始：它将依次绑定六个见证，并就 `p` 与 `q` 说出 Gödel 比较所要求的内容。
<!--ja-->
位置 5 は第一の対の第一座標であり、六つがそろう。ついで順序の論理式が始まる。六つの証人を順に束縛し、`p` と `q` について Gödel の比較の要求する内容を述べるのである。
<!--/-->

```agda
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc (suc (suc (suc (suc zero))))
opaque
  ltAt : ∀ {k} → Fin k → Fin k → Formula S k
  ltAt p q = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
```

<!--en-->
The body binds six witnesses in sequence and conjoins five atoms: `p` is the ordered pair of the fifth and fourth slots, `q` is the ordered pair of the third and second, the first maximum atom relates the coordinates of `p`, the second maximum atom those of `q`, and the order atom compares the two maxima and then the coordinates. Read in the six-slot context, this says exactly that `p` is below `q` in the Gödel order.
<!--zh-->
公式体依次绑定六个见证，并合取五个原子：`p` 是第五、第四槽位组成的有序对，`q` 是第三、第二槽位组成的有序对，第一个最大值原子约束 `p` 的两个坐标，第二个最大值原子约束 `q` 的两个坐标，序原子则先比较两个最大值、再比较坐标。在六槽位语境中读出，这恰好说：`p` 在 Gödel 序下低于 `q`。
<!--ja-->
本体は六つの証人を順に束縛し、五つの原子を連言する。`p` は第五と第四のスロットの順序対、`q` は第三と第二のスロットの順序対であり、第一の最大値の原子は `p` の座標を、第二の最大値の原子は `q` の座標を結び、順序の原子が二つの最大値を、ついで座標を比較する。六スロットの文脈で読めば、これはまさに、Gödel 順序において `p` が `q` より下であることを述べている。
<!--/-->

```agda
        prAtL (↑6 p) i5 i4
     ∧̇ (prAtL (↑6 q) i3 i2
     ∧̇ (maxAt i1 i5 i4
     ∧̇ (maxAt i0 i3 i2
     ∧̇ ordAt i1 i0 i5 i4 i3 i2)))))))))
```

<!--en-->
Adequacy is checked against a concrete six-entry context. The context extends the caller's environment by the six witnesses, newest first: `n`, `m`, `d`, `c`, `b`, `a`, so that slot zero is `n` and slot five is `a`, matching the aliases.
<!--zh-->
充分性对照一个具体的六条目语境检验。该语境把六个见证以最新在前的方式添加到调用者的环境：`n`、`m`、`d`、`c`、`b`、`a`，于是第零槽位是 `n`、第五槽位是 `a`，与那些别名一致。
<!--ja-->
妥当性は、具体的な六項目の文脈に対して確かめられる。この文脈は、呼び出し側の環境に六つの証人を新しいものから順に加えたもの、すなわち `n`、`m`、`d`、`c`、`b`、`a` であり、スロット 0 が `n`、スロット 5 が `a` となって別名と一致する。
<!--/-->

```agda

  private
    env : ∀ {k} → S ^ k → S → S → S → S → S → S
        → S ^ (suc (suc (suc (suc (suc (suc k))))))
    env γ a b c d m n = n ∷ m ∷ d ∷ c ∷ b ∷ a ∷ γ

```

<!--en-->
The first adequacy lemma reads the pair atom at that context: satisfaction of the pairing atom is the equation between the caller's `p` and the ordered pair of `a` and `b`.
<!--zh-->
第一条充分性引理在该语境读取配对原子：配对原子的满足，就是调用者的 `p` 与 `a`、`b` 的有序对之间的等式。
<!--ja-->
最初の妥当性の補題は、その文脈で対の原子を読む。対の原子の充足は、呼び出し側の `p` と `a`、`b` の順序対との間の等式である。
<!--/-->

```agda
    atP : ∀ {k} (p : Fin k) (γ : S ^ k) (a b c d m n : S)
        → ⟨ env γ a b c d m n ⊨ prAtL (↑6 p) i5 i4 ⟩
        ≡ (fst (lookup p γ) ≡ pr (fst a) (fst b))
    atP p γ a b c d m n = cong ⟨_⟩ (prAtL-adequate (↑6 p) i5 i4 (env γ a b c d m n))

```

<!--en-->
The second does the same for `q` and the pair of `c` and `d`. With these two identifications, the satisfaction of the formula is interchangeable with the six-witness data of `Lt`.
<!--zh-->
第二条对 `q` 与 `c`、`d` 的有序对做同样的事。有了这两条等同，公式的满足与 `Lt` 的六见证数据便可互换。
<!--ja-->
第二は `q` と `c`、`d` の順序対について同じことをする。この二つの同定により、論理式の充足と `Lt` の六証人のデータは互いに取り替えられる。
<!--/-->

```agda
    atQ : ∀ {k} (q : Fin k) (γ : S ^ k) (a b c d m n : S)
        → ⟨ env γ a b c d m n ⊨ prAtL (↑6 q) i3 i2 ⟩
        ≡ (fst (lookup q γ) ≡ pr (fst c) (fst d))
    atQ q γ a b c d m n = cong ⟨_⟩ (prAtL-adequate (↑6 q) i3 i2 (env γ a b c d m n))

```

<!--en-->
The outward direction consumes the six nested truncations in turn: satisfaction of `ltAt p q` at `γ` yields witnesses `a` through `n` together with the pair equations, the two maximum data, and the order data.
<!--zh-->
向外方向依次消耗六层嵌套的截断：`ltAt p q` 在 `γ` 处的满足给出见证 `a` 至 `n`，连同两条对等式、两份最大值数据与一份序数据。
<!--ja-->
外向きの方向は、六重に入れ子になった切り詰めを順に消費する。`γ` での `ltAt p q` の充足から、証人 `a` から `n` までと、対の等式、二つの最大値のデータ、そして順序のデータが得られる。
<!--/-->

```agda
  lt-out : ∀ {k} (p q : Fin k) (γ : S ^ k) → ⟨ γ ⊨ ltAt p q ⟩
         → Lt (fst (lookup p γ)) (fst (lookup q γ))
  lt-out p q γ = rec₁ squash₁ (λ { (a , ha) → rec₁ squash₁ (λ { (b , hb) →
    rec₁ squash₁ (λ { (c , hc) → rec₁ squash₁ (λ { (d , hd) →
    rec₁ squash₁ (λ { (m , hm) → rec₁ squash₁ (λ { (n , (hp , (hq , (hM , (hN , hO))))) →
```

<!--en-->
The two pair equations are transported along the adequacy paths, and the first maximum datum is carried to the ambient level. The six existential witnesses live at the lifted semantic level, so the affirmation case passes unchanged while the refutation case is lowered out of the lifting.
<!--zh-->
两条对等式沿充分性路径传输；第一份最大值数据被搬运到外围层级。六个存在见证处于被提升的语义层，因此肯定的情形原样保留，反驳的情形则被从提升中降出。
<!--ja-->
二つの対の等式は妥当性のパスに沿って輸送され、第一の最大値のデータは周囲のレベルへ運ばれる。六つの存在の証人は持ち上げられた意味の水準に住むので、肯定の場合はそのまま残り、反証の場合は持ち上げの外へ降ろされる。
<!--/-->

```agda
      ∣ a , b , c , d , m , n
      , ( transport (atP p γ a b c d m n) hp
        , transport (atQ q γ a b c d m n) hq
        , map₁ (λ { (inl h) → inl h
                    ; (inr (n , e)) → inr ((λ k → lower (n k)) , e) }) hM
```

<!--en-->
The second maximum datum is mapped identically, completing the witness of `Lt` at the caller's `p` and `q`.
<!--zh-->
第二份最大值数据以同样方式映射，从而在调用者的 `p` 与 `q` 处补全 `Lt` 的见证。
<!--ja-->
第二の最大値のデータも同じやり方で写され、呼び出し側の `p` と `q` における `Lt` の証人がそろう。
<!--/-->

```agda
        , map₁ (λ { (inl h) → inl h
                    ; (inr (n , e)) → inr ((λ k → lower (n k)) , e) }) hN
        , hO ) ∣₁ }) hm }) hd }) hc }) hb }) ha })

```

<!--en-->
The inward direction turns `Lt` into the satisfaction statement, which is a proposition.
<!--zh-->
向内方向把 `Lt` 转为满足陈述，而后者是命题。
<!--ja-->
内向きの方向は、`Lt` を充足の主張へ変える。主張は命題である。
<!--/-->

```agda
  lt-in : ∀ {k} (p q : Fin k) (γ : S ^ k)
        → Lt (fst (lookup p γ)) (fst (lookup q γ)) → ⟨ γ ⊨ ltAt p q ⟩
  lt-in p q γ = rec₁ (snd (γ ⊨ ltAt p q))
    (λ { (a , b , c , d , m , n , (ep , eq' , hM , hN , hO)) →
      ∣ a , ∣ b , ∣ c , ∣ d , ∣ m , ∣ n
```

<!--en-->
The six witnesses are re-entered as the nested existential witnesses, with the pair equations transported along the adequacy paths in the reverse direction.
<!--zh-->
六个见证作为嵌套的存在见证被重新填入，两条对等式则沿充分性路径反方向传输。
<!--ja-->
六つの証人は入れ子の存在証人として再び入れられ、対の等式は妥当性のパスに沿って逆向きに輸送される。
<!--/-->

```agda
      , ( transport (sym (atP p γ a b c d m n)) ep
        , ( transport (sym (atQ q γ a b c d m n)) eq'
        , ( map₁ (λ { (inl h) → inl h
                      ; (inr (n , e)) → inr ((λ k → lift (n k)) , e) }) hM
          , ( map₁ (λ { (inl h) → inl h
```

<!--en-->
The two maximum data are mapped back, this time lifted into the object level's guarded atoms, and the order datum closes the formula. The Gödel module then packages the order for a set `P`: its describing condition requires both coordinates to be members of `P` and relates them by the order formula.
<!--zh-->
两份最大值数据被映射回去，这次提升为对象层带守卫的原子，序数据随之封闭整条公式。Gödel 模块随后为集合 `P` 打包这条序：其描述条件要求两个坐标都是 `P` 的成员，并以序公式关联它们。
<!--ja-->
二つの最大値のデータは今度は対象レベルの守られた原子へ持ち上げて写され、順序のデータが論理式を閉じる。Gödel のモジュールはついで、集合 `P` のためのこの順序をまとめる。その記述の条件は、二つの座標がともに `P` の要素であることを要求し、順序の論理式で両者を結ぶ。
<!--/-->

```agda
                        ; (inr (n , e)) → inr ((λ k → lift (n k)) , e) }) hN
            , hO )))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ })
private
  module Godel (P : S) = Relation P P
    ((var (suc zero) ∈̇ con P) ∧̇ ((var zero ∈̇ con P) ∧̇ ltAt (suc zero) zero))
```

<!--en-->
The host reading adds membership in `P` on both sides, conjoined with the order relation, and the two directions quote the outward and inward lemmas at the slots the two binders occupy: the first coordinate in the outer slot, the second in the inner one.
<!--zh-->
宿主读法在两侧加上对 `P` 的隶属，与序关系合取；两个方向在两个约束子所占的槽位处引用向外与向内引理：第一坐标在外层槽位，第二坐标在内层槽位。
<!--ja-->
ホスト側の読みは、両側に `P` への所属を加え、順序の関係と連言する。二つの方向は、二つの束縛子の占めるスロットで、外向きと内向きの補題を引用する。第一座標が外側のスロット、第二座標が内側のスロットである。
<!--/-->

```agda
    (λ p q → (fst p ∈ˢ fst P) ⊓ ((fst q ∈ˢ fst P) ⊓ (Lt (fst p) (fst q) , squash₁)))
    (λ p q e h → h .fst , h .snd .fst , lt-out (suc zero) zero (q ∷ p ∷ e ∷ []) (h .snd .snd))
    (λ p q e h → h .fst , h .snd .fst , lt-in (suc zero) zero (q ∷ p ∷ e ∷ []) (h .snd .snd))

```

<!--en-->
`godel P` is that separated relation: inside `L`, the set of the ordered pairs of members of `P` that compare below one another in the Gödel order.
<!--zh-->
`godel P` 就是那条被分离的关系：在 `L` 内部，由 `P` 的成员组成的、在 Gödel 序下相互低于的有序对之集。
<!--ja-->
`godel P` がその分出された関係である。`L` の内部における、`P` の要素からなる順序対のうち、Gödel 順序で互いに下にあるものの集合である。
<!--/-->

```agda
godel : S → S
godel = Godel.rel

```

<!--en-->
Inward: for two members `p` and `q` of `P` with `p` below `q`, their ordered pair belongs to `godel P`.
<!--zh-->
向内：对 `P` 的两个成员 `p`、`q`，若 `p` 低于 `q`，则它们的有序对属于 `godel P`。
<!--ja-->
内向きには、`P` の二つの要素 `p` と `q` について、`p` が `q` より下なら、その順序対は `godel P` に属する。
<!--/-->

```agda
godel-in : (P p q : S) → ⟨ fst p ∈ˢ fst P ⟩ → ⟨ fst q ∈ˢ fst P ⟩
         → Lt (fst p) (fst q) → ⟨ pr (fst p) (fst q) ∈ˢ fst (godel P) ⟩
godel-in P p q mp mq l = Godel.into P p q mp mq (mp , mq , l)

```

<!--en-->
Outward: a member of `godel P` comes with both members and the order data between them.
<!--zh-->
向外：`godel P` 的成员带有两个成员及其间的序数据。
<!--ja-->
外向きには、`godel P` の要素には二つの要素とその間の順序のデータが伴う。
<!--/-->

```agda
godel-out : (P p q : S) → ⟨ pr (fst p) (fst q) ∈ˢ fst (godel P) ⟩
          → ⟨ fst p ∈ˢ fst P ⟩ × ⟨ fst q ∈ˢ fst P ⟩ × Lt (fst p) (fst q)
godel-out = Godel.pair-out
```

<!--en-->
## The transfer to the host order
<!--zh-->
## 到宿主序的搬运
<!--ja-->
## ホスト側の順序への移送
<!--/-->

<!--en-->
The order module then fixes an ordinal `κ`, the case at which the square law is stated.
<!--zh-->
序模块随后固定一个序数 `κ`，即平方律所陈述的情形。
<!--ja-->
順序のモジュールはついで、平方律が述べられる場合である順序数 `κ` を固定する。
<!--/-->

```agda
module Order (κ : S) (oκ : IsOrd (fst κ)) where

```

<!--en-->
`K` is the underlying set of the ordinal `κ`; the carrier on which the square law unfolds is precisely this set of ordinals below `κ`.
<!--zh-->
`K` 是序数 `κ` 的底层集合；平方律所展开的载体正是这个由 `κ` 以下序数组成的集合。
<!--ja-->
`K` は順序数 `κ` の基底集合である。平方律が展開される台は、まさに `κ` 以下の順序数からなるこの集合である。
<!--/-->

```agda
  K : V ℓ
  K = fst κ

```

<!--en-->
`↑` names the members of `K` ambiently, through the small presentation's embedding: each index denotes the ordinal it presents.
<!--zh-->
`↑` 借助小呈现的嵌入，在外围点名 `K` 的成员：每个索引指称它所呈现的那个序数。
<!--ja-->
`↑` は、小さな提示の埋め込みを通して、`K` の要素を周囲で名指す。各添字はそれが提示する順序数を指すのである。
<!--/-->

```agda
  ↑ : ⟪ K ⟫ → V ℓ
  ↑ = ⟪ K ⟫↪

```

<!--en-->
An index `m : ⟪ K ⟫` names the ambient set `↑ m`, together with a proof that it belongs to `κ`. Since constructibility is inherited by members, `upK m` packages that named ordinal as an element of `L`.
<!--zh-->
索引 `m : ⟪ K ⟫` 指名外围集合 `↑ m`，并带有它属于 `κ` 的证明。可构造性向成员传递，因此 `upK m` 把这个被指名的序数打包为 `L` 的元素。
<!--ja-->
添字 `m : ⟪ K ⟫` は周囲の集合 `↑ m` を名指し、それが `κ` に属する証明を伴う。構成可能性は要素へ受け継がれるので、`upK m` はこの名指された順序数を `L` の要素としてまとめる。
<!--/-->

```agda
  upK : ⟪ K ⟫ → S
  upK m = ↑ m , isL-trans {x = K} {y = ↑ m} (member K m) (snd κ)

```

<!--en-->
The carrier of the order to be compared is `Pair`, the type of two indices of `κ`: an ordered pair in the host, each coordinate naming an ordinal below `κ`.
<!--zh-->
待比较的序的载体是 `Pair`，即 `κ` 的两个索引组成的类型：宿主一侧的有序对，每个坐标都指名一个低于 `κ` 的序数。
<!--ja-->
比較される順序の台は `Pair`、すなわち `κ` の二つの添字の型である。ホスト側の順序対であり、各座標は `κ` より下の順序数を名指す。
<!--/-->

```agda
  Pair : Type ℓ
  Pair = ⟪ K ⟫ × ⟪ K ⟫

```

<!--en-->
On the coordinates themselves stands the coordinate order `≺₁`, quoted from the external square-law development: ordinals below `κ` compare strictly by membership of the ambient sets they name.
<!--zh-->
坐标自身之上立着坐标序 `≺₁`，引自外部的平方律构造：低于 `κ` 的序数按其所指名外围集合之间的隶属作严格比较。
<!--ja-->
座標そのものの上には座標の順序 `≺₁` が立っている。外部の平方律の構成から引用されたもので、`κ` より下の順序数を、それらが名指す周囲の集合どうしの所属によって狭義に比較する。
<!--/-->

```agda
  _≺₁_ : ⟪ K ⟫ → ⟪ K ⟫ → Type (ℓ-suc ℓ)
  _≺₁_ = SQ._≺₁_ K oκ

```

<!--en-->
On pairs stands the Gödel order `≺ₚ`: compare maxima first, then the first coordinates, then the second. This is the external order that the internal formula must reproduce.
<!--zh-->
有序对之上立着 Gödel 序 `≺ₚ`：先比最大值，再比第一坐标，最后比第二坐标。这正是内部公式必须复现的那条外部序。
<!--ja-->
順序対の上には Gödel 順序 `≺ₚ` が立つ。まず最大値を比べ、ついで第一座標、最後に第二座標を比べるものである。内部の論理式が再現すべき外部の順序はこれである。
<!--/-->

```agda
  _≺ₚ_ : Pair → Pair → Type (ℓ-suc ℓ)
  _≺ₚ_ = SQ._≺_ K oκ

```

<!--en-->
The maximum operation `maxOrd` returns, for two ordinals below `κ`, the larger of the two, again quoted from the external development and again reading as a maximum only because the entries are ordinals.
<!--zh-->
最大值运算 `maxOrd` 对低于 `κ` 的两个序数返回其中较大者，同样引自外部构造，也同样只因条目是序数才读作最大值。
<!--ja-->
最大値の演算 `maxOrd` は、`κ` より下の二つの順序数に対して大きい方を返す。これも外部の構成からの引用であり、やはり要素が順序数であるからこそ最大値として読めるのである。
<!--/-->

```agda
  maxOrd : ⟪ K ⟫ → ⟪ K ⟫ → ⟪ K ⟫
  maxOrd = SQ.maxOrd K oκ

```

<!--en-->
Two small facts prepare the comparison between the two sides. First, every member of the ordinal `κ` is itself an ordinal, so the named ordinals carry ordinality certificates. Second, `max-out` states that the internal maximum condition, read at elements whose underlying sets name `a'` and `b'`, forces the internal maximum to be exactly the host maximum of `a'` and `b'`; the proof proceeds by the trichotomy data of the host order.
<!--zh-->
两个小事实为两侧的比较做准备。其一，序数 `κ` 的每个成员自身也是序数，故被点名的序数携带序数性证书。其二，`max-out` 陈述：在底层集合指名 `a'` 与 `b'` 的元素处读取的内部最大值条件，迫使内部最大值恰为 `a'` 与 `b'` 的宿主最大值；证明按宿主序的三歧数据展开。
<!--ja-->
二つの小さな事実が、両側の比較の準備をする。第一に、順序数 `κ` の各要素はそれ自身順序数であり、名指された順序数は順序数性の証明を帯ぶ。第二に、`max-out` は、基底の集合が `a'` と `b'` を名指す要素の上で読んだ内部の最大値の条件が、内部の最大値をちょうど `a'` と `b'` のホストの最大値に強いることを述べる。証明はホストの順序の三分法のデータに沿って進む。
<!--/-->

```agda
  ord↑ : (m : ⟪ K ⟫) → IsOrd (↑ m)
  ord↑ m = mem-ord {A = K} oκ (↑ m) (member K m)
  max-out : (a b m : S) (a' b' : ⟪ K ⟫) → fst a ≡ ↑ a' → fst b ≡ ↑ b'
          → MaxIs m a b → fst m ≡ ↑ (maxOrd a' b')
  max-out a b m a' b' ea eb = rec₁ (setIsSet _ _) (go (SQ.tri₁ K oκ a' b'))
```

<!--en-->
The case function fixes the shape of that argument: the host trichotomy splits into below, equal, and above; the internal datum splits into the affirmation, where `m` is `b`, and the refutation, where `m` is `a`. Matching the two splits term by term is the whole content.
<!--zh-->
情形函数固定了该论证的形状：宿主三歧分成低于、相等、高于；内部数据分成肯定分支 (`m` 即 `b`) 与反驳分支 (`m` 即 `a`)。把两种分裂逐项配上，就是全部内容。
<!--ja-->
場合分けの関数が、この議論の形を固定する。ホストの三分法は下・等しい・上に分かれ、内部のデータは肯定の場合 (`m` が `b`) と反証の場合 (`m` が `a`) に分かれる。二つの場合分けを項ごとに合わせることが内容のすべてである。
<!--/-->

```agda
    where
    go : (t : TriW (a' ≺₁ b') (a' ≡ b') (b' ≺₁ a'))
       → (⟨ fst a ∈ˢ fst b ⟩ × (fst m ≡ fst b))
         ⊎ ((⟨ fst a ∈ˢ fst b ⟩ → ⊥₀) × (fst m ≡ fst a))
       → fst m ≡ ↑ (SQ.maxGo K oκ a' b' t)
```

<!--en-->
In the below case the affirmation composes the equation of `m` with `b` and the naming of `b`, giving the host maximum. Its refutation branch is impossible: the membership it refutes is exactly the trichotomy's witness, transported through the two namings.
<!--zh-->
低于情形中，肯定分支把 `m` 与 `b` 的等式同 `b` 的命名复合，给出宿主最大值。其反驳分支不可能：它所反驳的隶属恰是三歧的见证，只须经两次命名传输即得。
<!--ja-->
下の場合、肯定の分枝は `m` と `b` の等式に `b` の名指しを合成してホストの最大値を与える。その反証の分枝は不可能である。反証されている所属は、まさに三分法の証人であり、二つの名指しを通して輸送されるだけだからである。
<!--/-->

```agda
    go (lt h) (inl (_ , e))   = e ∙ eb
    go (lt h) (inr (na , _))  =
      ⊥₀-rec (na (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) (sym ea) (sym eb) h))
    go (eq p) (inl (a∈b , _)) =
      ⊥₀-rec (∈-irrefl (↑ b')
```

<!--en-->
In the equal case an affirmation would place `a` inside `b` while the host declares them equal, contradicting the irreflexivity of membership at the named ordinal `b`; the refutation branch then names the maximum as `a`, transported along the naming of `a`.
<!--zh-->
相等情形中，肯定分支会断言 `a` 属于 `b`，而宿主宣布二者相等，这与被点名序数 `b` 处隶属的非自反性矛盾；反驳分支随即把最大值命名为 `a`，并沿 `a` 的命名传输。
<!--ja-->
等しい場合、肯定の分枝は `a` が `b` の内側にあると置くが、ホストは両者を等しいと宣言しており、名指された順序数 `b` における所属の非反射性と矛盾する。反証の分枝は、最大値を `a` と名指し、`a` の名指しに沿って輸送する。
<!--/-->

```agda
        (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) (ea ∙ cong ↑ p) eb a∈b))
    go (eq p) (inr (_ , e))   = e ∙ ea
    go (gt h) (inl (a∈b , _)) =
      ⊥₀-rec (∈-irrefl (↑ a')
        (ord↑ a' .fst {x = ↑ b'} {y = ↑ a'}
```

<!--en-->
In the above case the host witness puts `b` inside `a`; an affirmative internal branch would also put `a` inside `b`, and transitivity would contradict irreflexivity at `a`.
<!--zh-->
高于情形中，宿主见证给出 `b ∈ a`；若内部仍取肯定分支，还会有 `a ∈ b`，传递性便在 `a` 处违背非自反性。
<!--ja-->
上の場合、ホストの証人は `b ∈ a` を与える。内部でも肯定の枝を取ると `a ∈ b` も得られ、推移性によって `a` での非反射性に反する。
<!--/-->

```agda
          (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) ea eb a∈b) h))
    go (gt h) (inr (_ , e))   = e ∙ ea

```

<!--en-->
The converse `max-in` writes the host maximum into the internal predicate: for every pair of indices, the lifted element named by `maxOrd` satisfies `MaxIs` at the two lifted coordinates.
<!--zh-->
逆向的 `max-in` 把宿主最大值写进内部谓词：对每一对索引，由 `maxOrd` 指名的被提升元素在两个被提升坐标处满足 `MaxIs`。
<!--ja-->
逆の `max-in` は、ホストの最大値を内部の述語の中に書き込む。添字の各対に対して、`maxOrd` が名指す持ち上げられた要素が、持ち上げられた二つの座標で `MaxIs` を満たす。
<!--/-->

```agda
  max-in : (a' b' : ⟪ K ⟫) → MaxIs (upK (maxOrd a' b')) (upK a') (upK b')
  max-in a' b' = go (SQ.tri₁ K oκ a' b')
    where
    go : (t : TriW (a' ≺₁ b') (a' ≡ b') (b' ≺₁ a'))
       → MaxIs (upK (SQ.maxGo K oκ a' b' t)) (upK a') (upK b')
```

<!--en-->
Its three cases are immediate from the host comparison: below gives the affirmation with the equation definitional, equality refutes membership by irreflexivity, and above refutes it through the coordinate's own ordinality. The same block defines `code`, the ambient ordered pair of the two named ordinals of a host pair.
<!--zh-->
其三种情形由宿主比较直接得出：低于给出肯定分支且等式定义性成立；相等以非自反性反驳隶属；高于则借该坐标自身的序数性反驳。同一块中还定义了 `code`，即宿主对的两个被点名序数的外围有序对。
<!--ja-->
その三つの場合はホストの比較から直ちに従う。下では肯定の分枝に等式が定義的に付随し、等しい場合は非反射性によって所属が退けられ、上ではその座標自身の順序数性を通して退けられる。同じブロックでは `code`、すなわちホストの対の二つの名指された順序数の周囲の順序対が定義される。
<!--/-->

```agda
    go (lt h) = ∣ inl (h , refl) ∣₁
    go (eq p) = ∣ inr ((λ h → ∈-irrefl (↑ b') (subst (λ w → ⟨ ↑ w ∈ˢ ↑ b' ⟩) p h)) , refl) ∣₁
    go (gt h) = ∣ inr ((λ h' → ∈-irrefl (↑ a') (ord↑ a' .fst {x = ↑ b'} {y = ↑ a'} h' h)) , refl) ∣₁
  code : Pair → V ℓ
  code p = pr (↑ (fst p)) (↑ (snd p))
```

<!--en-->
The heart of the transfer is the refutation lemma. It assumes a contradiction-shaped pair of data: `Lt` holds of the coded pairs of `p` and `q`, while the host order refuses to compare them. The six witnesses of such an assumed `Lt` are collected into a single statement of absurdity.
<!--zh-->
搬运的核心是一条反驳引理。它假设一对形状即矛盾的数据：`Lt` 在 `p` 与 `q` 的编码对上成立，而宿主序却拒绝比较它们。这种假设下的 `Lt` 的六个见证被收拢为一条荒谬性陈述。
<!--ja-->
移送の核心は反証の補題である。ここでは矛盾の形をしたデータの対を仮定する。`p` と `q` の符号化された対の上で `Lt` が成り立ちながら、ホストの順序はその比較を拒むのである。こうして仮定された `Lt` の六つの証人が、一つの矛盾の主張にまとめられる。
<!--/-->

```agda
  private
    refute : (p q : Pair) → (p ≺ₚ q → ⊥₀)
           → Σ[ a ∈ S ] Σ[ b ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ] Σ[ m ∈ S ] Σ[ n ∈ S ]
               ( (code p ≡ pr (fst a) (fst b)) × (code q ≡ pr (fst c) (fst d))
               × MaxIs m a b × MaxIs n c d × OrdIs m n a b c d )
```

<!--en-->
The conclusion is the empty type: the assumed order data and the refused comparison cannot coexist. The proof destructures the six witnesses and works on the underlying sets they name.
<!--zh-->
结论是空类型：被假设的序数据与被拒绝的比较不能并存。证明拆开六个见证，在其所指名的底层集合上工作。
<!--ja-->
結論は空の型である。仮定された順序のデータと拒まれた比較は共存できない。証明は六つの証人を分解し、それらの名指す基底の集合の上で作業する。
<!--/-->

```agda
           → ⊥₀
    refute (a' , b') (c' , d') nk (a , b , c , d , m , n , (ep , eq' , hM , hN , hO)) =
      rec₁ isProp⊥ outer hO
      where
      ea : fst a ≡ ↑ a'
```

<!--en-->
The injectivity of the ordered pair extracts, from each coding equation, the identification of the underlying set of each witness with the corresponding named ordinal. These four equations anchor every later comparison.
<!--zh-->
有序对的单射性从每条编码等式中提取出：每个见证的底层集合与相应被点名序数的等同。这四条等式为后文所有比较提供了锚点。
<!--ja-->
順序対の単射性が、各符号化の等式から、証人の基底集合と対応する名指された順序数の同定を取り出す。この四つの等式が、後のすべての比較の錨となる。
<!--/-->

```agda
      ea = sym (pr-inj ep .fst)
      eb : fst b ≡ ↑ b'
      eb = sym (pr-inj ep .snd)
      ec : fst c ≡ ↑ c'
      ec = sym (pr-inj eq' .fst)
```

<!--en-->
The two maxima are then identified with the host maxima, by `max-out` applied to the two maximum data. At this point the internal and external readings of the whole configuration coincide on all six coordinates.
<!--zh-->
两个最大值再经 `max-out` 施于两份最大值数据，而与宿主最大值等同。至此整个构形的内部读法与外部读法在全部六个坐标上一致。
<!--ja-->
二つの最大値は、二つの最大値のデータに `max-out` を適用して、ホストの最大値と同一視される。ここで構成全体の内部の読みと外部の読みは、六つの座標のすべてで一致する。
<!--/-->

```agda
      ed : fst d ≡ ↑ d'
      ed = sym (pr-inj eq' .snd)
      em : fst m ≡ ↑ (maxOrd a' b')
      em = max-out a b m a' b' ea eb hM
      en : fst n ≡ ↑ (maxOrd c' d')
```

<!--en-->
The equation `en` supplies the same identification for the second pair, so `OrdIs` can now be transported entirely to the host maxima and coordinates.
<!--zh-->
等式 `en` 为第二个对给出同样的等同，于是现在可把 `OrdIs` 完整传输到宿主最大值与坐标上。
<!--ja-->
等式 `en` は第二の対にも同じ同定を与えるので、`OrdIs` をホストの最大値と座標へすべて輸送できるようになる。
<!--/-->

```agda
      en = max-out c d n c' d' ec ed hN

```

<!--en-->
The inner lemma transfers the coordinate comparison. An ambient membership between the named first coordinates becomes membership in the host order, transported along the identifications of the two namings.
<!--zh-->
内层引理传递坐标比较：被点名第一坐标之间的外围隶属，沿两次命名的等同传输后，变成宿主序中的低于关系。
<!--ja-->
内側の補題は座標の比較を移送する。名指された第一座標の間の周囲の所属は、二つの名指しの同定に沿って輸送されると、ホストの順序での下関係になる。
<!--/-->

```agda
      inner : ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩)
            → (a' ≺₁ c') ⊎ ((a' ≡ c') × (b' ≺₁ d'))
      inner (inl h)       = inl (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) ea ec h)
      inner (inr (e , h)) =
        inr ( ↪-inj {a = K} (sym ea ∙ e ∙ ec)
```

<!--en-->
The equality case transfers as well: an equality of the named sets, cycled through the two namings, becomes an equality of indices by the injectivity of `K`'s naming, and the second coordinates compare as before.
<!--zh-->
相等情形同样传递：被点名集合的等式经两次命名的循环改写后，由 `K` 的命名的单射性变成索引的等式，而第二坐标照旧比较。
<!--ja-->
相等の場合も同じく伝わる。名指された集合の等式を二つの名指しの間で巡らせると、`K` の名指しの単射性によって添字の等式になり、第二座標は従来どおり比較される。
<!--/-->

```agda
            , subst2 (λ x y → ⟨ x ∈ˢ y ⟩) eb ed h )

```

<!--en-->
If the first maximum belongs to the second, transporting this membership along `em` and `en` gives the first, strict-maximum branch of `p ≺ₚ q`, contradicting `nk`.
<!--zh-->
若第一个最大值属于第二个，沿 `em` 与 `en` 传输这份隶属，便得到 `p ≺ₚ q` 的严格最大值分支，与 `nk` 矛盾。
<!--ja-->
第一の最大値が第二の最大値に属するなら、この所属を `em` と `en` に沿って輸送すると `p ≺ₚ q` の最大値が真に小さい枝が得られ、`nk` と矛盾する。
<!--/-->

```agda
      outer : ⟨ fst m ∈ˢ fst n ⟩
            ⊎ ((fst m ≡ fst n)
               × ∥ ⟨ fst a ∈ˢ fst c ⟩ ⊎ ((fst a ≡ fst c) × ⟨ fst b ∈ˢ fst d ⟩) ∥₁)
            → ⊥₀
      outer (inl h)       = nk (inl (subst2 (λ x y → ⟨ x ∈ˢ y ⟩) em en h))
```

<!--en-->
If the two maxima are equal, the equality of the underlying sets becomes an equality of indices by the naming injectivity, and the inner lemma then compares the pairs inside the host order, refuting the refusal once more.
<!--zh-->
若两个最大值相等，底层集合的等式经命名单射性变成索引的等式，内层引理随后在宿主序内比较两对，再次反驳拒绝。
<!--ja-->
二つの最大値が等しいなら、基底集合の等式が名指しの単射性によって添字の等式になり、内側の補題がホストの順序の中で二つの対を比較して、再び拒否を退ける。
<!--/-->

```agda
      outer (inr (e , h)) = rec₁ isProp⊥
        (λ w → nk (inr (↪-inj {a = K} (sym em ∙ e ∙ en) , inner w))) h

```

<!--en-->
To prove `lt→≺`, trichotomy leaves three possibilities for the host pairs. The desired strict case is immediate. Equality and the reverse strict case would each make any refusal of `p ≺ₚ q` incompatible with the assumed `Lt`, by `refute`; hence both also yield the desired comparison.
<!--zh-->
证明 `lt→≺` 时，宿主对的三歧性给出三种可能。所需的严格分支可直接返回；在相等或反向严格的分支中，若拒绝 `p ≺ₚ q`，`refute` 会使之与已假设的 `Lt` 矛盾，因而仍得到所需比较。
<!--ja-->
`lt→≺` の証明では、ホストの対の三分法から三つの場合が生じる。求める狭義の枝はそのまま返せる。相等または逆向きの狭義の枝では、`p ≺ₚ q` を否定すると `refute` により仮定した `Lt` と矛盾するので、やはり求める比較が得られる。
<!--/-->

```agda
  lt→≺ : (p q : Pair) → Lt (code p) (code q) → p ≺ₚ q
  lt→≺ p q l = go (SQ.tri≺ K oκ p q)
    where
    refuted : ((p ≺ₚ q) → ⊥₀) → p ≺ₚ q
    refuted nk = ⊥₀-rec (rec₁ isProp⊥ (refute p q nk) l)
```

<!--en-->
In the equality case, a putative `p ≺ₚ q` transports to `q ≺ₚ q` and violates irreflexivity. In the reverse strict case, composing that putative comparison with `q ≺ₚ p` gives `p ≺ₚ p`, again impossible.
<!--zh-->
相等情形中，假设的 `p ≺ₚ q` 可传输为 `q ≺ₚ q`，违背非自反性；反向严格情形中，把这份假设比较与 `q ≺ₚ p` 复合会得到 `p ≺ₚ p`，同样不可能。
<!--ja-->
相等の場合、仮定した `p ≺ₚ q` は `q ≺ₚ q` へ輸送され、非反射性に反する。逆向きの狭義の場合、その仮定した比較を `q ≺ₚ p` と合成すると `p ≺ₚ p` が得られ、やはり不可能である。
<!--/-->

```agda

    go : TriW (p ≺ₚ q) (p ≡ q) (q ≺ₚ p) → p ≺ₚ q
    go (lt k) = k
    go (eq e) = refuted (λ k → SQ.irr≺ K oκ q (subst (λ w → w ≺ₚ q) e k))
    go (gt h) = refuted (λ k → SQ.irr≺ K oκ p (SQ.trans≺ K oκ p q p k h))

```

<!--en-->
The converse `≺→lt` writes the host comparison into the object language. Its six witnesses are the lifted coordinates and the two lifted maxima, the pair equations are definitional, the maximum data come from `max-in`, and the order data from the host comparison itself.
<!--zh-->
逆向的 `≺→lt` 把宿主比较写进对象语言。其六个见证是被提升的坐标与两个被提升的最大值，两条对等式定义性成立，最大值数据来自 `max-in`，序数据来自宿主比较本身。
<!--ja-->
逆の `≺→lt` は、ホストの比較を対象言語の中に書き込む。六つの証人は持ち上げられた座標と二つの持ち上げられた最大値であり、対の等式は定義的に成り立ち、最大値のデータは `max-in` が、順序のデータはホストの比較そのものが供給する。
<!--/-->

```agda
  ≺→lt : (p q : Pair) → p ≺ₚ q → Lt (code p) (code q)
  ≺→lt (a' , b') (c' , d') k =
    ∣ upK a' , upK b' , upK c' , upK d' , upK (maxOrd a' b') , upK (maxOrd c' d')
    , ( refl , refl , max-in a' b' , max-in c' d' , ord k ) ∣₁
    where
```

<!--en-->
The order datum is read case by case: strict membership passes through untouched, and the two equality cases are transported along the naming of the maxima and the naming of the coordinates respectively.
<!--zh-->
序数据按情形逐条读取：严格隶属原样通过；两种相等情形分别沿最大值的命名与坐标的命名传输。
<!--ja-->
順序のデータは場合ごとに読まれる。狭義の所属はそのまま通り、相等の二つの場合は、最大値の名指しおよび座標の名指しに沿ってそれぞれ輸送される。
<!--/-->

```agda
    ord : (a' , b') ≺ₚ (c' , d')
        → OrdIs (upK (maxOrd a' b')) (upK (maxOrd c' d')) (upK a') (upK b') (upK c') (upK d')
    ord (inl h)                 = ∣ inl h ∣₁
    ord (inr (e , inl h))       = ∣ inr (cong ↑ e , ∣ inl h ∣₁) ∣₁
    ord (inr (e , inr (f , h))) = ∣ inr (cong ↑ e , ∣ inr (cong ↑ f , h) ∣₁) ∣₁
```

<!--en-->
If `x < y`, transitivity with `y < z` gives `x < z`; if `x = y`, the given comparison `y < z` is transported along that equality.
<!--zh-->
若 `x < y`，与 `y < z` 传递即得 `x < z`；若 `x = y`，则沿该等式传输已有的 `y < z`。
<!--ja-->
`x < y` なら `y < z` との推移性から `x < z` を得る。`x = y` なら、与えられた `y < z` をその等式に沿って輸送する。
<!--/-->

```agda
  private
    ≤→≺ : (x y z : ⟪ K ⟫) → SQ._≤₁_ K oκ x y → y ≺₁ z → x ≺₁ z
    ≤→≺ x y z (inl h) h' = SQ.trans₁ K oκ x y z h h'
    ≤→≺ x y z (inr e) h' = subst (λ w → w ≺₁ z) (sym e) h'

```

<!--en-->
The companion lemma turns `x ≤ y` and `y = y'` into membership of `x` in the successor of `y'`. In the strict case, `x ∈ y'` gives successor membership directly; in the equality case, identifying `x` with `y'` reduces the claim to `y'` belonging to its own successor.
<!--zh-->
配套引理由 `x ≤ y` 与 `y = y'` 得出 `x` 属于 `y'` 的后继。严格情形中，`x ∈ y'` 直接给出后继隶属；相等情形中，把 `x` 与 `y'` 等同后，目标化为 `y'` 属于自身后继。
<!--ja-->
対になる補題は、`x ≤ y` と `y = y'` から、`x` が `y'` の後続に属することを導く。狭義の場合は `x ∈ y'` から後続への所属が直接従う。等しい場合は `x` を `y'` と同一視すると、主張は `y'` が自身の後続に属することへ帰着する。
<!--/-->

```agda
    ≤→∈suc : (x y y' : ⟪ K ⟫) → SQ._≤₁_ K oκ x y → y ≡ y'
           → ⟨ ↑ x ∈ˢ sucV (↑ y') ⟩
    ≤→∈suc x y y' (inl h) e = ∈sucV-inl (subst (λ w → x ≺₁ w) e h)
    ≤→∈suc x y y' (inr q) e =
      subst (λ w → ⟨ ↑ w ∈ˢ sucV (↑ y') ⟩) (sym (q ∙ e)) (self∈sucV (↑ y'))
```

<!--en-->
The segment lemmas now read off the order. If a pair `r` is below a pair `p`, the first coordinate of `r` is a member of the successor of the maximum of `p`: in the strict-max case this is at-most followed by strict comparison.
<!--zh-->
节段引理现在从序中读出：若对 `r` 低于对 `p`，则 `r` 的第一坐标属于 `p` 的最大值的后继；在最大值严格比较的情形，这是先「至多」再严格比较。
<!--ja-->
節の補題がここで順序から読み取られる。対 `r` が対 `p` より下なら、`r` の第一座標は `p` の最大値の後続の要素である。最大値が真に比較される場合は、たかだかの関係に続いて狭義の比較が行われる。
<!--/-->

```agda

  fst∈suc : (r p : Pair) → r ≺ₚ p
          → ⟨ ↑ (fst r) ∈ˢ sucV (↑ (maxOrd (fst p) (snd p))) ⟩
  fst∈suc (a , b) (c , d) (inl h) =
    ∈sucV-inl (≤→≺ a (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .fst) h)
  fst∈suc (a , b) (c , d) (inr (e , _)) =
```

<!--en-->
In the equal-max case the first coordinate is at most the shared maximum and the two maxima are identified, so membership in the successor follows from the self-membership of the maximum in its own successor.
<!--zh-->
最大值相等的情形中，第一坐标至多为共同的最大值，而两个最大值被等同，故隶属由「最大值属于自身后继」得出。
<!--ja-->
最大値が等しい場合は、第一座標は共有された最大値を超えず、二つの最大値は同一視されるので、所属は最大値がみずからの後続に属することから従う。
<!--/-->

```agda
    ≤→∈suc a (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .fst) e

```

<!--en-->
The same argument, applied to the second coordinates, gives `snd∈suc`: the second coordinate of `r` also lands in the successor of `p`'s maximum, whether the maxima compare strictly or are equal.
<!--zh-->
把同一论证施于第二坐标，即得 `snd∈suc`：`r` 的第二坐标同样落入 `p` 的最大值的后继，无论两个最大值严格比较还是相等。
<!--ja-->
同じ議論を第二座標に適用すると `snd∈suc` が得られる。`r` の第二座標もまた、二つの最大値が狭義に比較される場合にも、等しい場合にも、`p` の最大値の後続に収まる。
<!--/-->

```agda
  snd∈suc : (r p : Pair) → r ≺ₚ p
          → ⟨ ↑ (snd r) ∈ˢ sucV (↑ (maxOrd (fst p) (snd p))) ⟩
  snd∈suc (a , b) (c , d) (inl h) =
    ∈sucV-inl (≤→≺ b (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .snd) h)
  snd∈suc (a , b) (c , d) (inr (e , _)) =
```

<!--en-->
These two bounds show that every predecessor of a pair `(c, d)` has both coordinates in `suc(max(c, d))`.
<!--zh-->
这两个界说明，对 `(c, d)` 的每个前驱，其两个坐标都属于 `suc(max(c, d))`。
<!--ja-->
この二つの評価から、`(c, d)` の任意の先行者の両座標が `suc(max(c, d))` に属することが分かる。
<!--/-->

```agda
    ≤→∈suc b (maxOrd a b) (maxOrd c d) (SQ.max-spec K oκ a b .snd) e
module Coll (κ : S) (oκ : IsOrd (fst κ)) where

```

<!--en-->
These bounds control every predecessor segment of the Gödel order. Together with well-foundedness and transitivity, they place the relation on `prodL κ` in the setting where it can be collapsed to its ordinal order type.
<!--zh-->
这些界控制 Gödel 序的每个前驱节段。结合良基性与传递性，它们使 `prodL κ` 上的关系处于可塌缩为序数序型的情形。
<!--ja-->
これらの評価は Gödel 順序の各先行者切片を制御する。整礎性と推移性を合わせると、`prodL κ` 上の関係を順序数としての順序型へ崩壊できる状況が得られる。
<!--/-->

```agda
  open Order κ oκ

```

<!--en-->
The set to be collapsed onto an order type is `P`, the product: the ordered pairs of members of the ordinal `κ`, already separated inside `L`.
<!--zh-->
将要被塌缩成序型的集合是 `P`，即乘积：序数 `κ` 的成员的有序对之集，已在 `L` 内部分离而来。
<!--ja-->
順序型へ崩壊される集合は `P`、すなわち積である。順序数 `κ` の要素の順序対の集合であり、すでに `L` の内部で分出されている。
<!--/-->

```agda
  P : S
  P = prodL κ

```

<!--en-->
The relation of the collapse is `R`, the Gödel order on that product: two members of `P` stand related exactly when the first compares below the second.
<!--zh-->
塌缩所用关系是 `R`，即该乘积上的 Gödel 序：`P` 的两个成员恰好在其一低于另一个时相关。
<!--ja-->
崩壊に用いられる関係は `R`、つまりその積の上の Gödel 順序である。`P` の二つの要素は、一方が他方より下で比較されるときに限り関係づけられる。
<!--/-->

```agda
  R : S
  R = godel P

```

<!--en-->
For the Gödel relation this follows directly: whenever `y R x`, both `y` and `x` are members of the product.
<!--zh-->
对 Gödel 关系这可直接读出：只要 `y R x`，`y` 与 `x` 都是该乘积的成员。
<!--ja-->
Gödel 関係では直接従う。`y R x` なら、`y` と `x` はともにその積の要素である。
<!--/-->

```agda
  Rsub : (y x : S) → Holds R y x → ⟨ fst y ∈ fst P ⟩ × ⟨ fst x ∈ fst P ⟩
  Rsub y x h = godel-out P y x h .fst , godel-out P y x h .snd .fst

```

<!--en-->
The order-type machinery is instantiated once and for this product. Its domain is an index set for the collapse, and `φ` reads off, for each index, the host pair that the corresponding member of the product presents: the two coordinates are recovered untruncated by the presentation reader of the product.
<!--zh-->
序型机制针对这个乘积一次性实例化。其定义域是塌缩的一个索引集，而 `φ` 为每个索引读出乘积中相应成员所呈现的宿主对：两个坐标由乘积的呈现读式无截断地恢复。
<!--ja-->
順序型の仕組みはこの積のために一度実例化される。その定義域は崩壊の添字集合であり、`φ` は各添字に対して、積の対応する要素が提示するホストの対を読み取る。二つの座標は積の提示の読みによって切り詰めなしで回収される。
<!--/-->

```agda
  module OT = Code P R Rsub using (Dom; Dom≡; isProp≺; toDom; up; up-mem; up-toDom; ↪; _≺_; ≺-in; ≺-out; module Conjuncts)
  φ : OT.Dom → Pair
  φ m = prodL-fst κ (OT.up m) (OT.up-mem m) .fst
      , prodL-fst κ (OT.up m) (OT.up-mem m) .snd .fst

```

<!--en-->
The reading comes with its equation: the internal coding of the index equals the ambient ordered pair of the two coordinates. This equation is the hinge on which every comparison between the internal and external orders turns.
<!--zh-->
该读式随附一条等式：索引的内部编码等于两个坐标的外围有序对。这条等式是内部序与外部序之间每一次比较所依赖的枢纽。
<!--ja-->
この読みには等式が伴う。添字の内部の符号化は、二つの座標の周囲の順序対に等しいのである。この等式が、内部の順序と外部の順序の間のすべての比較の継ぎ目である。
<!--/-->

```agda
  φ-eq : (m : OT.Dom) → OT.↪ m ≡ code (φ m)
  φ-eq m = prodL-fst κ (OT.up m) (OT.up-mem m) .snd .snd

```

<!--en-->
`φ` is injective: if two indices name the same host pair, their codings agree, and the domain's own criterion, equality of codings, returns equality of indices. Thus no two product indices can be sent to the same host pair.
<!--zh-->
`φ` 是单射的：若两个索引指名同一宿主对，则它们的编码一致，而定义域自身的判据「编码相等」即返回索引相等。因此两个不同的乘积索引不可能被送到同一个宿主对。
<!--ja-->
`φ` は単射である。二つの添字が同じホストの対を名指すなら、それらの符号化は一致し、定義域みずからの基準、すなわち符号化の相等が添字の相等を返す。したがって、異なる二つの積の添字が同じホストの対へ送られることはない。
<!--/-->

```agda
  φ-inj : (m n : OT.Dom) → φ m ≡ φ n → m ≡ n
  φ-inj m n e = OT.Dom≡ (φ-eq m ∙ cong code e ∙ sym (φ-eq n))

```

<!--en-->
The forward transfer reads the internal order outward: if two indices compare inside `L`, their host pairs compare in the Gödel order. The proof quotes the defining equation and the outward reading of the formula, then applies the transfer `lt→≺` at the two host pairs.
<!--zh-->
向前传递把内部序向外读：若两个索引在 `L` 内部可比较，则它们的宿主对在 Gödel 序下可比较。证明引用定义等式与公式的外向读式，然后在两个宿主对上施用传递 `lt→≺`。
<!--ja-->
順方向の移送は、内部の順序を外向きに読む。二つの添字が `L` の内部で比較されれば、それらのホストの対は Gödel 順序で比較される。証明は定義の等式と論理式の外向きの読みを引用し、二つのホストの対の上で移送 `lt→≺` を適用する。
<!--/-->

```agda
  ≺-fwd : (m n : OT.Dom) → m OT.≺ n → φ m ≺ₚ φ n
  ≺-fwd m n k = lt→≺ (φ m) (φ n)
    (subst2 Lt (φ-eq m) (φ-eq n) (godel-out P (OT.up m) (OT.up n) (OT.≺-out m n k) .snd .snd))

```

<!--en-->
The backward transfer reads the host order inward, quoting the inward reading of the formula and the transfer `≺→lt` at the same two pairs. Together the two directions say: the internal relation on the collapse's indices is exactly the host Gödel order, read through `φ`.
<!--zh-->
向后传递把宿主序向内读，引用公式的向内读式与同一对上的传递 `≺→lt`。两个方向合起来说：塌缩索引上的内部关系，恰是经 `φ` 读出的宿主 Gödel 序。
<!--ja-->
逆方向の移送は、ホストの順序を内向きに読み、論理式の内向きの読みと、同じ二つの対の上の移送 `≺→lt` を引用する。二つの方向を合わせると、崩壊の添字の上の内部の関係は、`φ` を通して読んだホストの Gödel 順序にほかならないと言える。
<!--/-->

```agda
  ≺-bwd : (m n : OT.Dom) → φ m ≺ₚ φ n → m OT.≺ n
  ≺-bwd m n k = OT.≺-in m n
    (godel-in P (OT.up m) (OT.up n) (OT.up-mem m) (OT.up-mem n)
      (subst2 Lt (sym (φ-eq m)) (sym (φ-eq n)) (≺→lt (φ m) (φ n) k)))

```

<!--en-->
Well-foundedness transfers with the indices. The accessibility of a host pair supplies the accessibility of the corresponding index, whose predecessors map forward to host pairs of strictly smaller pairs. Induction along the external order thus becomes induction along the internal one.
<!--zh-->
良基性随索引传递。宿主对的可及性给出相应索引的可及性，其前驱向前映到严格更小的对所对应的宿主对。于是沿外部序的归纳成为沿内部序的归纳。
<!--ja-->
整礎性は添字とともに伝わる。ホストの対の到達可能性は、対応する添字の到達可能性を供給し、その先行者は前方へ、真に小さい対のホストの対へ写される。こうして外部の順序に沿う帰納が、内部の順序に沿う帰納になる。
<!--/-->

```agda
  wf : WellFounded OT._≺_
  wf m = go (SQ.wf≺ K oκ (φ m))
    where
    go : {n : OT.Dom} → Acc _≺ₚ_ (φ n) → Acc OT._≺_ n
    go {n} (acc r) = acc (λ n' k → go (r (φ n') (≺-fwd n' n k)))
```

<!--en-->
Transitivity transfers the same way: two internal steps are read outward, composed by the host order's transitivity, and read back inward as one internal step from `a` to `c`.
<!--zh-->
传递性同样传递：内部的两步先向外读出，由宿主序的传递性复合，再向内读回为从 `a` 直达 `c` 的一步。
<!--ja-->
推移性も同じように伝わる。内部の二段階を外向きに読み、ホストの順序の推移性で合成し、`a` から `c` への一段階として内向きに読み戻す。
<!--/-->

```agda

  ≺-trans : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
  ≺-trans {a} {b} {c} k k' =
    ≺-bwd a c (SQ.trans≺ K oκ (φ a) (φ b) (φ c) (≺-fwd a b k) (≺-fwd b c k'))

```

<!--en-->
Trichotomy completes the transferred package. For any two indices, the host trichotomy compares their pairs; the statement is a three-way sum of internal comparisons.
<!--zh-->
三歧性补全所传递的整套结构。对任意两个索引，宿主三歧比较它们的对；该陈述是内部比较的三向和。
<!--ja-->
三分法が移送された一式を完成させる。任意の二つの添字に対して、ホストの三分法がそれらの対を比較する。主張は内部の比較の三方向の和として述べられる。
<!--/-->

```agda
  tri : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  tri a b = go (SQ.tri≺ K oκ (φ a) (φ b))
    where
    go : TriW (φ a ≺ₚ φ b) (φ a ≡ φ b) (φ b ≺ₚ φ a)
       → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
```

<!--en-->
The three cases are read back through the backward transfer for the two strict cases, and through the injectivity of `φ` for the equality case: equal pairs name equal indices.
<!--zh-->
三种情形分别读回：两个严格情形经向后传递，相等情形经 `φ` 的单射性，指名同一宿主对的索引相等。
<!--ja-->
三つの場合はそれぞれ読み戻される。二つの狭義の場合は逆方向の移送を通り、相等の場合は `φ` の単射性を通って、同じホストの対を名指す添字は等しくなる。
<!--/-->

```agda
    go (lt h) = inl (≺-bwd a b h)
    go (eq e) = inr (inl (φ-inj a b e))
    go (gt h) = inr (inr (≺-bwd b a h))

```

<!--en-->
Well-foundedness and transitivity construct the collapse and its order type.
<!--zh-->
良基性与传递性构造出塌缩及其序型；
<!--ja-->
整礎性と推移性から崩壊とその順序型を構成する。
<!--/-->

```agda
  module C = OT.Conjuncts wf ≺-trans using (module Inj; col; col-ord; col-out; colTable; colTable-in; colTable-pair; colʟ; otL; otL-out)
  module I = C.Inj tri using (code; col-inj; module Inverse)
  injL-ot : InjL P C.otL
  injL-ot = ∣ C.colTable , I.code ∣₁
```

<!--en-->
## Three counting facts
<!--zh-->
## 三条计数事实
<!--ja-->
## 三つの計数事実
<!--/-->

<!--en-->
Trichotomy then makes the collapse map injective, so its graph witnesses an internal injection `P ↪ C.otL`.
<!--zh-->
三歧性随后证明塌缩映射单射，因此其图见证内部单射 `P ↪ C.otL`。
<!--ja-->
続いて三分法が崩壊写像の単射性を与えるので、そのグラフが内部単射 `P ↪ C.otL` を証する。
<!--/-->

```agda
incl : (a b : V ℓ) → ((z : V ℓ) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ b ⟩) → ⟪ a ⟫ ↪ ⟪ b ⟫
```

<!--en-->
The counting lemmas begin on the ambient side. An inclusion of two ambient sets acts on the small presentations: each index of the subset names a member of the larger set, and the member's own fiber in the larger presentation names the corresponding index.
<!--zh-->
计数引理从外围一侧开始。两个外围集合之间的包含作用于小呈现：子集的每个索引指名较大集合的一个成员，而该成员在较大呈现中的纤维则指名相应的索引。
<!--ja-->
計数の補題は周囲の側から始まる。二つの周囲の集合の間の包含は小さな提示の上で働く。部分集合の各添字は大きい集合の要素を名指し、その要素の大きい提示におけるファイバーが対応する添字を名指す。
<!--/-->

```agda
incl a b sub = ι , ι-inj
  where
  ι : ⟪ a ⟫ → ⟪ b ⟫
  ι m = fiber b (sub (⟪ a ⟫↪ m) (member a m)) .fst
  ι-inj : (m n : ⟪ a ⟫) → ι m ≡ ι n → m ≡ n
```

<!--en-->
The induced map on indices is injective: if two indices of the subset name members that the larger presentation indexes identically, the equality of the namings forces an equality of the named members, and the subset's own injectivity returns the equality of indices.
<!--zh-->
诱导出的索引映射是单射的：若子集的两个索引所指名的成员在较大呈现中被同一索引指名，则命名的等式迫使被指名成员相等，而子集自身的单射性返回索引的相等。
<!--ja-->
誘導された添字の写しは単射である。部分集合の二つの添字が名指す要素が大きい提示で同じ添字によって名指されるなら、名指しの等式が名指された要素の等式を強制し、部分集合みずからの単射性が添字の等式を返す。
<!--/-->

```agda
  ι-inj m n e = ↪-inj {a = a}
    (sym (fiber b (sub (⟪ a ⟫↪ m) (member a m)) .snd)
     ∙ cong ⟪ b ⟫↪ e
     ∙ fiber b (sub (⟪ a ⟫↪ n) (member a n)) .snd)
opaque
```

<!--en-->
A coded injection in `L` can be read externally: its graph conditions determine an injective map between the small presentations of its domain and codomain. Together with `ω ⊆ a` for every infinite ordinal `a`, this connects internal injections with ordinary cardinal comparisons.
<!--zh-->
`L` 中的编码单射可在外围读出：图的各项条件确定其定义域与值域的小呈现之间的单射。再结合每个无穷序数 `a` 都满足 `ω ⊆ a`，便把内部单射同通常的基数比较连接起来。
<!--ja-->
`L` 内の符号化された単射は外側で読み取れる。そのグラフ条件から、定義域と終域の小さな提示の間の単射が定まる。さらに任意の無限順序数 `a` に対する `ω ⊆ a` と合わせることで、内部単射を通常の基数比較へ結びつける。
<!--/-->

```agda
  coded→ambient : (a b : S) → Σ[ F ∈ S ] InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  coded→ambient a b (F , sv , dm , ij , ran) = Sm.small , Sm.small-inj
    where module Sm = Small F a b sv dm ij ran
ω⊆ : (a : V ℓ) → IsOrd a → (⟨ a ∈ˢ ω ⟩ → ⊥₀)
   → (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ a ⟩
```

<!--en-->
Containment of `ω` follows from trichotomy at the ordinal `a`: `a` cannot belong to `ω` by the infinity hypothesis; `a` equal to `ω` transports the membership; and `ω` inside `a` transfers every membership by transitivity.
<!--zh-->
`ω` 的包含由序数 `a` 处的三歧性得出：由无穷性假设 `a` 不属于 `ω`；`a` 等于 `ω` 时传输该隶属；`ω` 在 `a` 之内时由传递性转发每一份隶属。
<!--ja-->
`ω` の包含は、順序数 `a` での三分法から従う。無限性の仮定により `a` は `ω` に属せず、`a` が `ω` に等しいときは所属が輸送され、`ω` が `a` の内側にあるときは推移性がすべての所属を中継する。
<!--/-->

```agda
ω⊆ a oa a∉ω z z∈ω = go (ord-tri a oa ω ω-ord)
  where
  go : ⟨ a ∈ˢ ω ⟩ ⊎ ((a ≡ ω) ⊎ ⟨ ω ∈ˢ a ⟩) → ⟨ z ∈ˢ a ⟩
  go (inl h)         = ⊥₀-rec (a∉ω h)
  go (inr (inl e))   = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω
```

<!--en-->
Its last case is transitivity applied to `z ∈ ω` and `ω ∈ a`. With containment in hand, the second counting fact is the exclusion: an infinite ordinal admits no internal injection into a member of `ω`, that is, into a finite ordinal.
<!--zh-->
其最后一种情形是把传递性施于 `z ∈ ω` 与 `ω ∈ a`。包含到手之后，第二条计数事实是排除：无穷序数不容许到 `ω` 之成员 (即有限序数) 的内部单射。
<!--ja-->
その最後の場合は、`z ∈ ω` と `ω ∈ a` に推移性を適用するものである。包含を手にすると、第二の計数の事実は排除となる。無限の順序数は、`ω` の要素、すなわち有限の順序数への内部の単射を許さない。
<!--/-->

```agda
  go (inr (inr ω∈a)) = oa .fst z∈ω ω∈a
no-fin : (a b : S) → IsOrd (fst a) → (⟨ fst a ∈ˢ ω ⟩ → ⊥₀)
       → IsOrd (fst b) → ⟨ fst b ∈ˢ ω ⟩ → InjL a b → ⊥₀
no-fin a b oa a∉ω ob b∈ω = rec₁ isProp⊥ (λ c →
  finite-excl-ω (fst b) ob b∈ω (λ x → h c x , h c x)
```

<!--en-->
The final piece of the refutation quotes the containment of `ω` in `a`: since `ω ⊆ a`, the two lemmas compose, and an injection of `ω` into `b` would inject `ω` into the finite set `b` after passing through `a`. The inclusion map `ι` is fixed once in the where-clause.
<!--zh-->
反驳的最后一步引用 `ω` 含于 `a` 的事实：由于 `ω ⊆ a`，两条引理得以复合，于是「`ω` 单射入 `b`」经过 `a` 中转就成了「`ω` 单射入有限集 `b`」。包含映射 `ι` 在 where 子句中一次性确定。
<!--ja-->
反証の最後の部分は、`ω` が `a` に含まれるという事実を引用する。`ω ⊆ a` なので二つの補題が合成され、`ω` から `b` への単射は `a` を経由すると `ω` から有限集合 `b` への単射になる。包含写像 `ι` は where 節で一度定められる。
<!--/-->

```agda
    (λ x y e → ι .snd x y
       (coded→ambient a b c .snd (ι .fst x) (ι .fst y) (cong fst e))))
  where
  ι : ⟪ ω ⟫ ↪ ⟪ fst a ⟫
  ι = incl ω (fst a) (ω⊆ (fst a) oa a∉ω)
```

<!--en-->
The map `h` evaluates the coded injection after the inclusion `ω ↪ a`.
<!--zh-->
映射 `h` 在包含 `ω ↪ a` 之后求值编码单射。
<!--ja-->
写像 `h` は包含 `ω ↪ a` の後で符号化された単射を評価する。
<!--/-->

```agda
  h : Σ[ F ∈ S ] InjCode F a b → ⟪ ω ⟫ → ⟪ fst b ⟫
  h c x = coded→ambient a b c .fst (ι .fst x)
```

<!--en-->
## A coded injection lifts to the products
<!--zh-->
## 编码单射提升到乘积
<!--ja-->
## 符号化された単射を直積へ持ち上げる
<!--/-->

<!--en-->
For the product construction, fix a graph `F` that is single-valued on `a`, has domain `a`, is injective, and takes its values in `b`; these are the four conditions of a coded injection `a ↪ b`.
<!--zh-->
为构造乘积上的映射，固定一个图 `F`：它在 `a` 上单值、定义域为 `a`、具有单射性，且取值落在 `b` 中；这四项正是编码单射 `a ↪ b` 的条件。
<!--ja-->
積上の写像を構成するため、`a` 上で単値であり、定義域が `a`、単射的で、値が `b` に入るグラフ `F` を固定する。これらが符号化された単射 `a ↪ b` の四条件である。
<!--/-->

```agda
module ProdMap (a b F : S)
               (sv : ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩)
```

<!--en-->
The map `h` evaluates the coded injection after the inclusion `ω ↪ a`. For the product construction, fix a graph `F` that is single-valued on `a`, has domain `a`, is injective, and takes its values in `b`; these are the four conditions of a coded injection `a ↪ b`.
<!--zh-->
映射 `h` 在包含 `ω ↪ a` 之后求值编码单射。为构造乘积上的映射，固定一个图 `F`：它在 `a` 上单值、定义域为 `a`、具有单射性，且取值落在 `b` 中；这四项正是编码单射 `a ↪ b` 的条件。
<!--ja-->
写像 `h` は包含 `ω ↪ a` の後で符号化された単射を評価する。積上の写像を構成するため、`a` 上で単値であり、定義域が `a`、単射的で、値が `b` に入るグラフ `F` を固定する。これらが符号化された単射 `a ↪ b` の四条件である。
<!--/-->

```agda
               (ij : ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩)
               (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                    → ⟨ fst y ∈ fst b ⟩) where

```

<!--en-->
The extraction module reads the actual function out of the graph: `toFun` computes the value at each domain element, `toFun-graph` certifies that the pair belongs to the graph, and `toFun-inj` transfers the graph's injectivity to the function.
<!--zh-->
提取模块从图中读出真正的函数：`toFun` 在每个定义域元素处计算取值，`toFun-graph` 证明相应的对属于图，`toFun-inj` 把图的单射性转移到函数上。
<!--ja-->
抽出のモジュールは、グラフから実際の関数を読み取る。`toFun` が定義域の各要素での値を計算し、`toFun-graph` がその対がグラフに属することを証明し、`toFun-inj` がグラフの単射性を関数へ移す。
<!--/-->

```agda
  module E = Extract F a sv dm using (toFun; toFun-graph; toFun-inj)

```

<!--en-->
Two predicates describe the objects in play. `Mem p` says that `p` is a member of the product `prodL a`; `Comp p` says that `p` decomposes into two members `x` and `y` of `a` whose ordered pair is exactly the underlying set of `p`.
<!--zh-->
两个谓词刻画所涉对象。`Mem p` 说 `p` 是乘积 `prodL a` 的成员；`Comp p` 说 `p` 可分解为 `a` 的两个成员 `x` 与 `y`，且其有序对恰是 `p` 的底层集合。
<!--ja-->
二つの述語が対象を記述する。`Mem p` は `p` が積 `prodL a` の要素であることを、`Comp p` は `p` が `a` の二つの要素 `x` と `y` に分解され、その順序対が `p` の基底集合に等しいことを述べる。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem p = ⟨ fst p ∈ˢ fst (prodL a) ⟩
  Comp : S → Type (ℓ-suc ℓ)
  Comp p = Σ[ x ∈ S ] Σ[ y ∈ S ]
             (⟨ fst x ∈ˢ fst a ⟩ × ⟨ fst y ∈ˢ fst a ⟩ × (fst p ≡ pr (fst x) (fst y)))
```

<!--en-->
The components of a product member are unique, and `isPropComp` proves it. The first projections are identified by the injectivity of the ordered pair; the second projections are then compared in the inner lemma.
<!--zh-->
乘积成员的分量唯一，`isPropComp` 证明这一点。第一投影由有序对的单射性等同；第二投影随后在内层引理中比较。
<!--ja-->
積の要素の成分は一意であり、`isPropComp` がそれを証明する。第一射影は順序対の単射性によって同一視され、第二射影は内側の補題で比較される。
<!--/-->

```agda

  isPropComp : (p : S) → isProp (Comp p)
  isPropComp p (x , y , _ , _ , e) (x' , y' , _ , _ , e') =
    Σ≡Prop inner (Σ≡Prop (λ v → snd (isL v)) (pr-inj (sym e ∙ e') .fst))
    where
    inner : (x : S)
```

<!--en-->
The inner lemma compares the second components: two candidates `y` and `y'` paired with the same first coordinate are equal, because the pair equation identifies their underlying sets with the same set, and the constructibility and membership components are propositions.
<!--zh-->
内层引理比较第二分量：与同一第一坐标配对的两个候选 `y` 与 `y'` 相等，因为对等式把它们的底层集合与同一个集合等同，而可构造性与隶属分量都是命题。
<!--ja-->
内側の補題は第二成分を比較する。同じ第一座標と対にされた候補 `y` と `y'` は等しくなる。対の等式がそれらの基底集合を同じ集合と同一視し、構成可能性と所属の成分は命題だからである。
<!--/-->

```agda
          → isProp (Σ[ y ∈ S ] (⟨ fst x ∈ˢ fst a ⟩ × ⟨ fst y ∈ˢ fst a ⟩
                                × (fst p ≡ pr (fst x) (fst y))))
    inner x (y , _ , _ , e) (y' , _ , _ , e') =
      Σ≡Prop (λ w → isProp× (snd (fst x ∈ˢ fst a))
                      (isProp× (snd (fst w ∈ˢ fst a)) (setIsSet _ _)))
```

<!--en-->
The last component is discharged by the equality of underlying sets, and the uniqueness is complete: `Comp p` is a proposition, so its truncated existence can be eliminated into an honest decomposition.
<!--zh-->
最后一个分量由底层集合的相等消解，唯一性随之完成：`Comp p` 是命题，故其截断的存在可以消去为一份真实的分解。
<!--ja-->
最後の成分は基底集合の相等によって処理され、一意性が完成する。`Comp p` は命題なので、切り詰められた存在は実際の分解へ消去できる。
<!--/-->

```agda
        (Σ≡Prop (λ v → snd (isL v)) (pr-inj (sym e ∙ e') .snd))

```

<!--en-->
The reader `comp` turns the truncated membership of the product into an honest decomposition, and the uniqueness just proved is what licenses the elimination. The value map `val` then computes, at each member `x` of `a`, the element that the coded injection `F` assigns to it.
<!--zh-->
读式 `comp` 把乘积的截断隶属变成真实的分解，而刚刚证明的唯一性正是这一消去的许可。取值映射 `val` 随后在 `a` 的每个成员 `x` 处计算编码单射 `F` 指派给它的元素。
<!--ja-->
読み `comp` は、積の切り詰められた所属を実際の分解へ変える。その消去を許すのは、証明されたばかりの一意性である。そして値の写像 `val` が、`a` の各要素 `x` に対して、符号化された単射 `F` が割り当てる要素を計算する。
<!--/-->

```agda
  comp : (p : S) → Mem p → Comp p
  comp p mp = rec₁ (isPropComp p) (λ z → z) (prodL-out a p mp)
  opaque
    val : (x : S) → ⟨ fst x ∈ˢ fst a ⟩ → S
    val x mx = E.toFun (x , mx)
```

<!--en-->
The graph lemma certifies that the computed value is paired with its input inside the graph: the ordered pair of `x` and `val x` belongs to `F`. This is the record of the assignment, kept for every member of `a`.
<!--zh-->
图引理证明：计算出的取值与其输入在图中配对，即 `x` 与 `val x` 的有序对属于 `F`。这就是赋值的记录，对 `a` 的每个成员都予保留。
<!--ja-->
グラフの補題は、計算された値が入力とともにグラフの内部で対にされることを証明する。すなわち `x` と `val x` の順序対が `F` に属するのである。この割り当ての記録は `a` のすべての要素について保たれる。
<!--/-->

```agda

    val-graph : (x : S) (mx : ⟨ fst x ∈ˢ fst a ⟩)
              → ⟨ pr (fst x) (fst (val x mx)) ∈ fst F ⟩
    val-graph x mx = E.toFun-graph (x , mx)

```

<!--en-->
The injectivity lemma transfers the graph's injectivity to the computed values: if two members of `a` receive values with equal underlying sets, the members themselves are equal. This is what will make the lifted map on pairs injective.
<!--zh-->
单射性引理把图的单射性转移到计算出的取值上：若 `a` 的两个成员被指派的取值有相同的底层集合，则这两个成员本身相等。这正是使对上的提升映射成为单射的关键。
<!--ja-->
単射性の補題は、グラフの単射性を計算された値へ移す。`a` の二つの要素に割り当てられた値の基底集合が等しければ、要素そのものも等しいのである。これが、対の上の持ち上げられた写像を単射にする鍵である。
<!--/-->

```agda
    val-inj : (x : S) (mx : ⟨ fst x ∈ˢ fst a ⟩) (x' : S) (mx' : ⟨ fst x' ∈ˢ fst a ⟩)
            → fst (val x mx) ≡ fst (val x' mx') → fst x ≡ fst x'
    val-inj x mx x' mx' = E.toFun-inj ij (x , mx) (x' , mx')

```

<!--en-->
The lifted map `fn` acts on a member of the product by applying `F` coordinatewise: the internal ordered pair of the image of the first coordinate and the image of the second.
<!--zh-->
提升映射 `fn` 作用于乘积成员的方式是按坐标施用 `F`：即第一坐标的像与第二坐标的像组成的内部有序对。
<!--ja-->
持ち上げられた写像 `fn` は、積の要素に座標ごとに `F` を適用する。第一座標の像と第二座標の像の内部の順序対である。
<!--/-->

```agda
  fn : (p : S) → Mem p → S
  fn p mp = prʟ (val (comp p mp .fst) (comp p mp .snd .snd .fst))
                (val (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst))

```

<!--en-->
The image lands in the product over `b`: both component values are members of `b` by the range clause, so their internal pair belongs to `prodL b`. The identification of the internal and ambient pairs is transported along its own first-projection lemma.
<!--zh-->
像落入 `b` 之上的乘积：由值域子句，两个分量取值都是 `b` 的成员，故其内部对属于 `prodL b`。内部对与外围对的等同则沿其第一投影引理传输。
<!--ja-->
像は `b` の上の積の中に収まる。値域の節により二つの成分の値はともに `b` の要素であり、したがってその内部の対は `prodL b` に属する。内部の対と周囲の対の同一視は、みずからの第一射影の補題に沿って輸送される。
<!--/-->

```agda
  into : (p : S) (mp : Mem p) → ⟨ fst (fn p mp) ∈ˢ fst (prodL b) ⟩
  into p mp =
    subst (λ w → ⟨ w ∈ˢ fst (prodL b) ⟩) (sym (prʟ-fst (val x mx) (val y my)))
      (prodL-in b (val x mx) (val y my)
        (ran x (val x mx) (val-graph x mx)) (ran y (val y my) (val-graph y my)))
```

<!--en-->
A decomposition of `p` supplies coordinates `x,y` together with proofs `x ∈ a` and `y ∈ a`. These membership proofs are part of the data because `val` is defined only on members of `a`.
<!--zh-->
`p` 的分解给出坐标 `x,y`，并同时给出 `x ∈ a` 与 `y ∈ a` 的证明。这些隶属证明是数据的一部分，因为 `val` 只在 `a` 的成员上定义。
<!--ja-->
`p` の分解は座標 `x,y` と、`x ∈ a` および `y ∈ a` の証明を同時に与える。`val` は `a` の要素についてのみ定義されるため、これらの所属証明もデータの一部である。
<!--/-->

```agda
    where
    x = comp p mp .fst
    y = comp p mp .snd .fst
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst
```

<!--en-->
The chain type assembles what the graph formula must witness: `p` is the pair of `x` and `y`, `q` is the pair of `x'` and `y'`, and the graph of `F` contains the pairs of the two first coordinates and of the two second coordinates.
<!--zh-->
链类型汇集图公式须见证的全部内容：`p` 是 `x` 与 `y` 的对，`q` 是 `x'` 与 `y'` 的对，且 `F` 的图包含两个第一坐标的对与两个第二坐标的对。
<!--ja-->
連鎖の型は、グラフの論理式が証明すべき内容をまとめる。`p` は `x` と `y` の対、`q` は `x'` と `y'` の対であり、`F` のグラフには二つの第一座標の対と二つの第二座標の対が含まれるのである。
<!--/-->

```agda

  Chain : S → S → S → S → S → S → Type (ℓ-suc ℓ)
  Chain q p x y x' y' =
      (fst p ≡ pr (fst x) (fst y)) × (fst q ≡ pr (fst x') (fst y'))
    × ⟨ pr (fst x) (fst x') ∈ fst F ⟩ × ⟨ pr (fst y) (fst y') ∈ fst F ⟩

```

<!--en-->
The graph formula `mapFo` existentially chooses `x,y,x',y'` and conjoins four assertions: `p=(x,y)`, `q=(x',y')`, and the two applications of `F`.
<!--zh-->
图公式 `mapFo` 以存在量词选取 `x,y,x',y'`，并合取四项断言：`p=(x,y)`、`q=(x',y')`，以及 `F` 的两次应用。
<!--ja-->
グラフの論理式 `mapFo` は `x,y,x',y'` を存在量化し、`p=(x,y)`、`q=(x',y')`、および `F` の二つの適用という四つの主張を連言する。
<!--/-->

```agda
  opaque
    mapFo : Formula S 2
    mapFo = ∃̇ (∃̇ (∃̇ (∃̇ (
          prAtL i5 i3 i2
       ∧̇ (prAtL i4 i1 i0
```

<!--en-->
The last two atoms are the application clauses: the graph of `F` contains the pairs of the first coordinates and of the second coordinates, which is precisely the statement that `F` maps `x` to `x'` and `y` to `y'`.
<!--zh-->
最后两个原子是应用子句：`F` 的图包含两个第一坐标的对与两个第二坐标的对，这恰是「`F` 把 `x` 映到 `x'`、把 `y` 映到 `y'`」的陈述。
<!--ja-->
最後の二つの原子は適用の節である。`F` のグラフには第一座標どうしの対と第二座標どうしの対が含まれ、これはまさに、`F` が `x` を `x'` へ、`y` を `y'` へ写すということである。
<!--/-->

```agda
       ∧̇ (appC F i3 i1
       ∧̇ appC F i2 i0))))))

```

<!--en-->
Adequacy is checked against the six-entry context that adds the four witnesses, newest first, followed by the pair `q` and the pair `p`: slot zero is `y'`, slot five is `p`, matching the indices of the four atoms.
<!--zh-->
充分性对照一个具体的六条目语境检验：该语境先加入四个见证 (最新在前)，再接对 `q` 与对 `p`，于是第零槽位是 `y'`、第五槽位是 `p`，与四个原子的索引一致。
<!--ja-->
妥当性は、具体的な六項目の文脈に対して確かめられる。四つの証人を新しいものから順に加え、対 `q` と対 `p` を続けた文脈であり、スロット 0 が `y'`、スロット 5 が `p` となって四つの原子の添字と一致する。
<!--/-->

```agda
    private
      env₄ : S → S → S → S → S → S → S ^ 6
      env₄ q p x y x' y' = y' ∷ x' ∷ y ∷ x ∷ q ∷ p ∷ []

```

<!--en-->
The first adequacy lemma reads the pair atom for `p`: satisfaction of the pairing atom at the context is the equation between the underlying set of `p` and the ordered pair of `x` and `y`.
<!--zh-->
第一条充分性引理读取 `p` 的配对原子：该原子在语境中的满足，就是 `p` 的底层集合与 `x`、`y` 的有序对之间的等式。
<!--ja-->
最初の妥当性の補題は `p` の対の原子を読む。文脈における対の原子の充足は、`p` の基底集合と `x`、`y` の順序対との間の等式である。
<!--/-->

```agda
      at1 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ prAtL i5 i3 i2 ⟩ ≡ (fst p ≡ pr (fst x) (fst y))
      at1 q p x y x' y' = cong ⟨_⟩ (prAtL-adequate i5 i3 i2 (env₄ q p x y x' y'))

```

<!--en-->
The second adequacy lemma does the same for `q`, against the witnesses `x'` and `y'`. The two equations anchor the pair part of the chain.
<!--zh-->
第二条充分性引理对 `q` 与见证 `x'`、`y'` 做同样的事。这两条等式为链的对部分提供了锚点。
<!--ja-->
第二の妥当性の補題は、証人 `x'` と `y'` に対して `q` について同じことをする。この二つの等式が、連鎖の対の部分の錨である。
<!--/-->

```agda
      at2 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ prAtL i4 i1 i0 ⟩ ≡ (fst q ≡ pr (fst x') (fst y'))
      at2 q p x y x' y' = cong ⟨_⟩ (prAtL-adequate i4 i1 i0 (env₄ q p x y x' y'))

```

<!--en-->
The third adequacy lemma reads the first application atom: satisfaction in `L` is identified with the ambient membership of the pair of the two first coordinates in the graph of `F`.
<!--zh-->
第三条充分性引理读取第一个应用原子：其在 `L` 中的满足，被等同于两个第一坐标组成的对在 `F` 图中的外围隶属。
<!--ja-->
三つ目の妥当性の補題は第一の適用の原子を読む。`L` での充足は、二つの第一座標の対の `F` のグラフへの周囲の所属と同一視される。
<!--/-->

```agda
      at3 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ appC F i3 i1 ⟩ ≡ ⟨ pr (fst x) (fst x') ∈ fst F ⟩
      at3 q p x y x' y' = cong ⟨_⟩ (appC-adequate F i3 i1 (env₄ q p x y x' y'))

```

<!--en-->
The fourth does the same for the second coordinates, completing the translation of all four atoms into ordinary statements about members of sets.
<!--zh-->
第四条对第二坐标做同样的事，四个原子由此全部翻译为关于集合成员的普通陈述。
<!--ja-->
四つ目は第二座標に対して同じことをし、四つの原子のすべてが、集合の要素についての通常の主張へ翻訳される。
<!--/-->

```agda
      at4 : (q p x y x' y' : S)
          → ⟨ env₄ q p x y x' y' ⊨ appC F i2 i0 ⟩ ≡ ⟨ pr (fst y) (fst y') ∈ fst F ⟩
      at4 q p x y x' y' = cong ⟨_⟩ (appC-adequate F i2 i0 (env₄ q p x y x' y'))

```

<!--en-->
The outward direction consumes the four nested existentials in turn and assembles the truncated chain: four witnesses with all four atoms transported to their ambient readings.
<!--zh-->
向外方向依次消耗四层嵌套的存在量词，组装出截断的链：四个见证连同全部四个原子都传输到其外围读法。
<!--ja-->
外向きの方向は、四重に入れ子になった存在量化を順に消費し、切り詰められた連鎖を組み立てる。四つの証人と、周囲の読みへ輸送された四つの原子である。
<!--/-->

```agda
    mapFo-out : (q p : S) → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩
              → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] Σ[ x' ∈ S ] Σ[ y' ∈ S ] Chain q p x y x' y' ∥₁
    mapFo-out q p = rec₁ squash₁ (λ { (x , hx) → rec₁ squash₁ (λ { (y , hy) →
      rec₁ squash₁ (λ { (x' , hx') → map₁ (λ { (y' , (h1 , (h2 , (h3 , h4)))) →
        x , y , x' , y'
```

<!--en-->
Each atom is transported along its own adequacy path, so the chain records ordinary equations and ordinary memberships rather than satisfaction judgments.
<!--zh-->
每个原子都沿其自身的充分性路径传输，因此链所记录的是普通的等式与普通的隶属，而非满足判断。
<!--ja-->
各原子はみずからの妥当性のパスに沿って輸送されるため、連鎖が記録するのは充足の判断ではなく、通常の等式と通常の所属である。
<!--/-->

```agda
        , ( transport (at1 q p x y x' y') h1 , transport (at2 q p x y x' y') h2
          , transport (at3 q p x y x' y') h3 , transport (at4 q p x y x' y') h4 ) })
        hx' }) hy }) hx })

```

<!--en-->
The inward direction rebuilds the formula from the chain. The four witnesses are entered as the nested existentials, and the four atoms are transported along the adequacy paths in the reverse direction.
<!--zh-->
向内方向从链重建公式：四个见证作为嵌套存在量词的见证填入，四个原子沿充分性路径反方向传输。
<!--ja-->
内向きの方向は、連鎖から論理式を組み立て直す。四つの証人を入れ子の存在量化の証人として入れ、四つの原子を妥当性のパスに沿って逆向きに輸送する。
<!--/-->

```agda
    mapFo-in : (q p x y x' y' : S) → Chain q p x y x' y' → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩
    mapFo-in q p x y x' y' (h1 , h2 , h3 , h4) =
      ∣ x , ∣ y , ∣ x' , ∣ y'
      , ( transport (sym (at1 q p x y x' y')) h1
        , ( transport (sym (at2 q p x y x' y')) h2
```

<!--en-->
The last two application atoms complete the nested conjunction of the four assertions, and hence complete the witness for `mapFo`.
<!--zh-->
最后两个应用原子补全由四项断言组成的嵌套合取，从而完成 `mapFo` 的见证。
<!--ja-->
最後の二つの適用原子が四つの主張からなる入れ子の連言を完成させ、`mapFo` の証人が得られる。
<!--/-->

```agda
        , ( transport (sym (at3 q p x y x' y')) h3
          , transport (sym (at4 q p x y x' y')) h4 ))) ∣₁ ∣₁ ∣₁ ∣₁

```

<!--en-->
Uniqueness says that the graph formula determines the value: any `q` paired with `p` in the graph equals the canonical image `fn p mp`. The proof consumes the truncated chain into the pair equation, the goal being an equation in an h-set.
<!--zh-->
唯一性说图公式确定取值：任何在图中与 `p` 配对的 `q` 都等于典范像 `fn p mp`。证明把截断的链消耗进对等式，而目标正是 h-集合中的等式。
<!--ja-->
一意性は、グラフの論理式が値を定めることを述べる。グラフの中で `p` と対にされる任意の `q` は、正準な像 `fn p mp` に等しくなる。証明は切り詰められた連鎖を対の等式の中で消費し、目標は h-集合における等式である。
<!--/-->

```agda
  only : (p : S) (mp : Mem p) (q : S) → ⟨ (q ∷ p ∷ []) ⊨ mapFo ⟩ → q ≡ fn p mp
  only p mp q h = rec₁ (isSetS q (fn p mp)) step (mapFo-out q p h)
    where
    x = comp p mp .fst
    y = comp p mp .snd .fst
```

<!--en-->
The four components of the member `p` are named once, as in the image lemma, so the uniqueness computation can refer to them directly.
<!--zh-->
成员 `p` 的四个分量像在像引理中那样一次性命名，使唯一性的计算可以直接引用它们。
<!--ja-->
要素 `p` の四つの成分には、像の補題と同じように一度名前が与えられ、一意性の計算がそれらを直接参照できる。
<!--/-->

```agda
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst
    e = comp p mp .snd .snd .snd .snd

```

<!--en-->
The chain equation writes `q` as `(x₁',y₁')`, while the fixed decomposition writes `p` as `(x,y)`. Single-valuedness identifies `x₁'` with `val x` and `y₁'` with `val y`, so `q` is the canonical image `(val x,val y)`.
<!--zh-->
链中的等式把 `q` 写成 `(x₁',y₁')`，而固定的分解把 `p` 写成 `(x,y)`。单值性分别把 `x₁'`、`y₁'` 认同为 `val x`、`val y`，故 `q` 就是典范像 `(val x,val y)`。
<!--ja-->
連鎖の等式は `q` を `(x₁',y₁')` と書き、固定した分解は `p` を `(x,y)` と書く。単値性により `x₁'` は `val x` と、`y₁'` は `val y` と同一視されるので、`q` は正準な像 `(val x,val y)` である。
<!--/-->

```agda
    step : Σ[ x₁ ∈ S ] Σ[ y₁ ∈ S ] Σ[ x₁' ∈ S ] Σ[ y₁' ∈ S ] Chain q p x₁ y₁ x₁' y₁'
         → q ≡ fn p mp
    step (x₁ , y₁ , x₁' , y₁' , (e₁ , e₂ , h3 , h4)) =
      Σ≡Prop (λ v → snd (isL v))
        (e₂ ∙ cong₂ pr ex ey ∙ sym (prʟ-fst (val x mx) (val y my)))
```

<!--en-->
The injectivity of the ordered pair splits the pair equation into two: the underlying set of `x₁` equals that of `x`, and the underlying set of `y₁` equals that of `y`.
<!--zh-->
有序对的单射性把对等式拆成两条：`x₁` 的底层集合等于 `x` 的，`y₁` 的底层集合等于 `y` 的。
<!--ja-->
順序対の単射性が対の等式を二つに分ける。`x₁` の基底集合は `x` のそれに等しく、`y₁` の基底集合は `y` のそれに等しいのである。
<!--/-->

```agda
      where
      x₁≡x : fst x₁ ≡ fst x
      x₁≡x = pr-inj (sym e₁ ∙ e) .fst
      y₁≡y : fst y₁ ≡ fst y
      y₁≡y = pr-inj (sym e₁ ∙ e) .snd
```

<!--en-->
The two graph memberships are then read through the single-valuedness of `F`: an entry paired with `x₁`, once `x₁` is known to name `x`, must agree with the recorded value `val x mx` on its first projection.
<!--zh-->
两条图隶属随后经 `F` 的单值性读出：一旦知道 `x₁` 指名 `x`，与 `x₁` 配对的条目在其第一投影上必与已记录的取值 `val x mx` 一致。
<!--ja-->
二つのグラフへの所属は、`F` の単値性を通して読まれる。`x₁` が `x` を名指すことが分かれば、`x₁` と対にされた項目の第一射影は、記録された値 `val x mx` と一致せざるを得ない。
<!--/-->

```agda
      ex : fst x₁' ≡ fst (val x mx)
      ex = svAt-out zero (F ∷ a ∷ []) sv x x₁' (val x mx)
             (subst (λ w → ⟨ pr w (fst x₁') ∈ fst F ⟩) x₁≡x h3) (val-graph x mx)
      ey : fst y₁' ≡ fst (val y my)
      ey = svAt-out zero (F ∷ a ∷ []) sv y y₁' (val y my)
```

<!--en-->
The second coordinate is treated identically, with its own membership and its own recorded value.
<!--zh-->
第二坐标以完全相同的方式处理，使用它自己的隶属与它自己被记录的取值。
<!--ja-->
第二座標もまったく同じように扱われ、みずからの所属と、みずからに記録された値が用いられる。
<!--/-->

```agda
             (subst (λ w → ⟨ pr w (fst y₁') ∈ fst F ⟩) y₁≡y h4) (val-graph y my)

```

<!--en-->
Thus `mapFo` defines the coordinatewise image `fn`: every product member has that graph value, and `into` places the value in `prodL b`.
<!--zh-->
因此 `mapFo` 定义逐坐标像 `fn`：每个乘积成员都具有这一图取值，而 `into` 把该取值置于 `prodL b` 中。
<!--ja-->
したがって `mapFo` は座標ごとの像 `fn` を定義する。各積要素はこのグラフ値をもち、`into` がその値を `prodL b` に入れる。
<!--/-->

```agda
  M : DefinableMap
  M = record
    { dom = prodL a ; cod = prodL b ; fn = fn ; into = into ; graph = mapFo
    ; defines = λ p mp →
        mapFo-in (fn p mp) p (comp p mp .fst) (comp p mp .snd .fst)
```

<!--en-->
The defining clause is the chain, instantiated at the canonical image of `p`: the two values, the pair equation of the product member, and the two graph lemmas certify that the graph holds of the image and its input.
<!--zh-->
定义子句就是那条链，在 `p` 的典范像处实例化：两个取值、乘积成员的对等式，以及两条图引理，共同证明图对像及其输入成立。
<!--ja-->
定義の節は連鎖であり、`p` の正準な像のところで実例化される。二つの値、積の要素の対の等式、そして二つのグラフの補題が、グラフが像とその入力について成り立つことを証明する。
<!--/-->

```agda
          (val (comp p mp .fst) (comp p mp .snd .snd .fst))
          (val (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst))
          ( comp p mp .snd .snd .snd .snd
          , prʟ-fst _ _
          , val-graph (comp p mp .fst) (comp p mp .snd .snd .fst)
```

<!--en-->
The uniqueness theorem shows that no second graph value is possible, so the formula represents an actual function on `prodL a`.
<!--zh-->
唯一性定理排除了第二个图取值，因此该公式确实表示 `prodL a` 上的函数。
<!--ja-->
一意性定理により別のグラフ値はありえないため、この論理式は `prodL a` 上の実際の関数を表す。
<!--/-->

```agda
          , val-graph (comp p mp .snd .fst) (comp p mp .snd .snd .snd .fst) )
    ; only = only }

```

<!--en-->
Injectivity of the lifted map is proved directly. Two product members whose images agree as underlying sets must themselves agree, and the proof reassembles each member from its components.
<!--zh-->
提升映射的单射性被直接证明：若两个乘积成员的像作为底层集合相等，则这两个成员本身相等。证明把每个成员从其分量重新组装。
<!--ja-->
持ち上げられた写像の単射性は直接証明される。像が基底集合として等しい二つの積の要素は、それ自身も等しくなければならない。証明は各要素をその成分から組み立て直す。
<!--/-->

```agda
  inj : (p : S) (mp : Mem p) (p' : S) (mp' : Mem p')
      → fst (fn p mp) ≡ fst (fn p' mp') → fst p ≡ fst p'
  inj p mp p' mp' e = e₀ ∙ cong₂ pr ex ey ∙ sym e₀'
    where
    x = comp p mp .fst
```

<!--en-->
The components of both members are named once, so the two decompositions can be compared coordinate by coordinate.
<!--zh-->
两个成员的分量各一次性命名，使两份分解可以逐坐标比较。
<!--ja-->
二つの要素の成分にはそれぞれ一度名前が与えられ、二つの分解を座標ごとに比較できる。
<!--/-->

```agda
    y = comp p mp .snd .fst
    mx = comp p mp .snd .snd .fst
    my = comp p mp .snd .snd .snd .fst
    e₀ = comp p mp .snd .snd .snd .snd
    x' = comp p' mp' .fst
```

<!--en-->
The assumed equality of images is an equality of internal pairs; its injectivity splits it into the equality of the two first images and the equality of the two second images.
<!--zh-->
所假设的像相等是内部对的相等；其单射性把它拆成两个第一像的相等与两个第二像的相等。
<!--ja-->
仮定された像の相等は内部の対の相等であり、その単射性がそれを、第一の像どうしの相等と第二の像どうしの相等に分ける。
<!--/-->

```agda
    y' = comp p' mp' .snd .fst
    mx' = comp p' mp' .snd .snd .fst
    my' = comp p' mp' .snd .snd .snd .fst
    e₀' = comp p' mp' .snd .snd .snd .snd
    q : (fst (val x mx) ≡ fst (val x' mx')) × (fst (val y my) ≡ fst (val y' my'))
```

<!--en-->
Each component equality is fed to the injectivity of the value map, yielding first coordinates equal and second coordinates equal; the two coordinates of the pair equation are then transported along these.
<!--zh-->
每个分量的等式都被喂给取值映射的单射性，得到第一坐标相等与第二坐标相等；对等式的两个坐标再沿它们传输。
<!--ja-->
各成分の等式は値の写像の単射性に渡され、第一座標の相等と第二座標の相等が得られる。対の等式の二つの座標はこれらに沿って輸送される。
<!--/-->

```agda
    q = pr-inj (sym (prʟ-fst (val x mx) (val y my)) ∙ e ∙ prʟ-fst (val x' mx') (val y' my'))
    ex : fst x ≡ fst x'
    ex = val-inj x mx x' mx' (fst q)
    ey : fst y ≡ fst y'
    ey = val-inj y my y' my' (snd q)
```

<!--en-->
The definable map and its injectivity assemble into the internal injection: `prodL a` injects into `prodL b` inside `L`.
<!--zh-->
可定义映射与其单射性装配成内部单射：在 `L` 内部，`prodL a` 单射入 `prodL b`。
<!--ja-->
定義可能な写像とその単射性が内部の単射として組み上がる。`L` の内部で `prodL a` は `prodL b` へ単射する。
<!--/-->

```agda

  injL : InjL (prodL a) (prodL b)
  injL = Inj.injL M inj

```

<!--en-->
Because `InjL` is propositionally truncated, a coded injection `a ↪ b` may be lifted without choosing its graph globally.
<!--zh-->
由于 `InjL` 是命题截断的，提升编码单射 `a ↪ b` 无须全局选定其图。
<!--ja-->
`InjL` は命題的に切り詰められているため、グラフを大域的に選ばずに符号化された単射 `a ↪ b` を持ち上げられる。
<!--/-->

```agda
prod-inj : (a b : S) → InjL a b → InjL (prodL a) (prodL b)
prod-inj a b = rec₁ squash₁
  (λ { (F , sv , dm , ij , ran) → ProdMap.injL a b F sv dm ij ran })
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--ja-->
## 無限基数の平方律
<!--/-->

<!--en-->
To absorb the extra top element of an infinite ordinal, it remains to inject its successor back into the ordinal.
<!--zh-->
为吸收无穷序数新增的顶端元素，还须把该序数的后继单射回序数本身。
<!--ja-->
無限順序数に加わる頂点を吸収するには、その後続をもとの順序数へ単射すれば十分である。
<!--/-->

```agda
module Shift (mL : S) (om : IsOrd (fst mL)) (m∉ω : ⟨ fst mL ∈ˢ ω ⟩ → ⊥₀) where

```

<!--en-->
Write `m` for the underlying ordinal of `mL`. Membership and finiteness decisions concern this set, while `mL` retains the evidence that it is an element of `L`.
<!--zh-->
记 `mL` 的底层序数为 `m`。隶属与有限性判定针对这个集合，而 `mL` 保留它属于 `L` 的证据。
<!--ja-->
`mL` の基底にある順序数を `m` と書く。所属と有限性の判定はこの集合について行い、`mL` はそれが `L` の要素である証拠を保持する。
<!--/-->

```agda
  private
    m : V ℓ
    m = fst mL

```

<!--en-->
The domain of the shift is the internal successor `D = sucʟ mL`: the successor of the ordinal inside `L`, which contains both the members of `m` and `m` itself.
<!--zh-->
移位的定义域是内部后继 `D = sucʟ mL`：即 `L` 内该序数的后继，它既包含 `m` 的成员，也包含 `m` 自身。
<!--ja-->
移し変えの定義域は内部の後続 `D = sucʟ mL` である。`L` の内部での順序数の後続であり、`m` の要素と `m` 自身の両方を含む。
<!--/-->

```agda
    D : S
    D = sucʟ mL

```

<!--en-->
Equality of two elements of `L` is equality of their underlying sets, since the constructibility components are propositions. This small equation is used at every identification inside the shift.
<!--zh-->
`L` 中两个元素的相等就是其底层集合的相等，因为可构造性分量是命题。这条小等式在移位内部的每一处等同都要用到。
<!--ja-->
`L` の二つの要素の相等は、その基底集合の相等である。構成可能性の成分は命題だからである。この小さな等式は、移し変えの内部のあらゆる同一視で使われる。
<!--/-->

```agda
    S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
    S≡ = Σ≡Prop (λ v → snd (isL v))

```

<!--en-->
Since `m` is infinite, every member of `ω` belongs to `m`; the containment is quoted from the counting facts and is the reason the successor of a finite member stays inside `m`.
<!--zh-->
由于 `m` 无穷，`ω` 的每个成员都属于 `m`；这一包含引自计数事实，也正是有限成员的后继得以留在 `m` 内的原因。
<!--ja-->
`m` は無限なので、`ω` のすべての要素は `m` に属する。この包含は計数の事実から引用されたもので、有限の要素の後続が `m` の内側にとどまる理由でもある。
<!--/-->

```agda
    ω⊆m : (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ m ⟩
    ω⊆m = ω⊆ m om m∉ω

```

<!--en-->
Membership in the shift's domain is stated, and the first decision is defined: an element is either a member of `ω` or the membership is refuted. This is an explicit decision delivered by excluded middle.
<!--zh-->
先陈述移位定义域中的隶属，并定义第一个判定：元素要么属于 `ω`，要么该隶属被反驳。这是由排中律给出的显式判定。
<!--ja-->
移し変えの定義域への所属を述べ、最初の判定を定義する。要素は `ω` に属するか、その所属が反証されるかのいずれかである。これは排中律が与える明示的な判定である。
<!--/-->

```agda
    Mem : S → Type (ℓ-suc ℓ)
    Mem x = ⟨ fst x ∈ˢ fst D ⟩
    Fin? : S → Type (ℓ-suc ℓ)
    Fin? x = Dec ⟨ fst x ∈ˢ ω ⟩

```

<!--en-->
The second decision separates the members of the successor: an element of `sucʟ mL` is either a member of `m` or equal to `m`, which is exactly what membership in a successor means.
<!--zh-->
第二个判定区分后继的成员：`sucʟ mL` 的元素要么属于 `m`，要么等于 `m`，这正是「属于后继」的含义。
<!--ja-->
第二の判定は後続の要素を分ける。`sucʟ mL` の要素は `m` に属するか `m` と等しいかであり、これが後続への所属の意味そのものである。
<!--/-->

```agda
    Top? : S → Type (ℓ-suc ℓ)
    Top? x = ⟨ fst x ∈ˢ m ⟩ ⊎ (fst x ≡ m)

```

<!--en-->
The first decision is an instance of excluded middle, applied to the membership proposition of `x` in `ω`.
<!--zh-->
第一个判定是排中律的一个实例，施用于 `x` 属于 `ω` 这条隶属命题。
<!--ja-->
最初の判定は排中律の一つの実例であり、`x` の `ω` への所属の命題に適用される。
<!--/-->

```agda
    fin? : (x : S) → Fin? x
    fin? x = lem (fst x ∈ˢ ω)

```

<!--en-->
The second decision is also an instance of excluded middle, refined by the successor's elimination: a member of `sucʟ mL` is either a member of `m` or equal to `m`, so a refuted membership leaves only equality.
<!--zh-->
第二个判定同样是排中律的实例，并经后继的消去细化：`sucʟ mL` 的成员要么属于 `m`、要么等于 `m`，于是隶属被反驳后就只剩相等。
<!--ja-->
第二の判定も排中律の実例であり、後続の消去によって洗練される。`sucʟ mL` の要素は `m` に属するか `m` と等しいかであり、所属が反証されれば等しいことだけが残る。
<!--/-->

```agda
    top? : (x : S) → Mem x → Top? x
    top? x h = go (lem (fst x ∈ˢ m))
      where
      go : Dec ⟨ fst x ∈ˢ m ⟩ → Top? x
      go (yes k) = inl k
```

<!--en-->
In the refuted case the elimination consumes the truncated membership in the successor, and the two outcomes are exclusive: an element cannot both belong to `m` and equal `m`, since that would make `m` a member of itself, refuted by the irreflexivity of membership.
<!--zh-->
在被反驳的情形中，消去消耗后继中的截断隶属；而两种结果互斥：一个元素不能既属于 `m` 又等于 `m`，否则 `m` 将属于自身，这被隶属的非自反性所反驳。
<!--ja-->
反証された場合では、消去が後続の切り詰められた所属を消費する。二つの結果は排他的である。ある要素が `m` に属し、かつ `m` に等しいことはあり得ない。それは `m` がみずからに属することになり、所属の非反射性によって退けられるからである。
<!--/-->

```agda
      go (no nk) = inr (∈sucV-elim {A = m} {x = fst x} (setIsSet (fst x) m)
        (subst (λ w → ⟨ fst x ∈ˢ w ⟩) (sucʟ-fst mL) h) (λ k → ⊥₀-rec (nk k)) (λ q → q))
    not-both : (x : S) → ⟨ fst x ∈ˢ m ⟩ → fst x ≡ m → ⊥₀
    not-both x k q = ∈-irrefl m (subst (λ w → ⟨ w ∈ˢ m ⟩) q k)

```

<!--en-->
The finite and top cases cannot overlap. If `x` belongs to `ω` and equals `m`, transporting its membership along that equality would put `m` in `ω`, contrary to the hypothesis that `m` is infinite.
<!--zh-->
有限情形与顶端情形不能重合。若 `x` 属于 `ω` 且等于 `m`，沿该等式搬运其隶属关系便会得到 `m ∈ ω`，与 `m` 无穷的假设矛盾。
<!--ja-->
有限の場合と頂点の場合は重ならない。`x` が `ω` に属し、しかも `m` に等しいなら、その等しさに沿って所属を移送することで `m ∈ ω` が得られ、`m` が無限であるという仮定に反する。
<!--/-->

```agda
    ω-fin : (x : S) → ⟨ fst x ∈ˢ ω ⟩ → fst x ≡ m → ⊥₀
    ω-fin x k q = m∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) q k)

```

<!--en-->
A successor can never be empty. Indeed, `a` belongs to `sucV a`; if `sucV a = ∅`, transporting this membership would produce an element of the empty set.
<!--zh-->
后继绝不可能是空集。事实上，`a` 属于 `sucV a`；若 `sucV a = ∅`，沿该等式搬运这一隶属关系便会得到空集的一个元素。
<!--ja-->
後続が空集合になることはない。実際、`a` は `sucV a` に属する。もし `sucV a = ∅` なら、この所属を等しさに沿って移送することで、空集合の要素が得られてしまう。
<!--/-->

```agda
    suc≢∅ : (a : V ℓ) → sucV a ≡ ∅ → ⊥₀
    suc≢∅ a e = ∅-empty a
      (∈∈ₛ {a = a} {b = ∅} .fst (subst (λ w → ⟨ a ∈ˢ w ⟩) e (self∈sucV a)))

```

<!--en-->
The three cases now define the value of the shift. A finite member is sent to its internal successor; a non-finite member of `m` is sent to itself; and the top element `m` is sent to the empty set of `L`. These are precisely the three alternatives the decisions distinguish.
<!--zh-->
三种情形现在定义移位的取值。有限成员被送到其内部后继；`m` 的非有限成员被送到自身；而顶端元素 `m` 被送到 `L` 的空集。这正是两个判定所区分的三种选择。
<!--ja-->
三つの場合が、移し変えの値を定義する。有限の要素はみずからの内部の後続へ送られ、`m` の非有限の要素はみずからへ送られ、頂点の要素 `m` は `L` の空集合へ送られる。これらは、二つの判定が区別する三つの選択肢にほかならない。
<!--/-->

```agda
    value : (x : S) → Fin? x → Top? x → S
    value x (yes _) _       = sucʟ x
    value x (no _) (inl _) = x
    value x (no _) (inr _) = ∅ʟ

```

<!--en-->
The value is guaranteed to lie in `m`. For a finite member, its successor is a member of `ω` by the limit property, and `ω` is contained in `m`; for a member of `m` the membership is the decision itself; and the empty set is a member of `ω`, hence of `m`.
<!--zh-->
取值保证落在 `m` 中。对有限成员，其后继由 `ω` 的极限性质成为 `ω` 的成员，而 `ω` 包含于 `m`；对 `m` 的成员，隶属就是那个判定本身；空集则是 `ω` 的成员，因而也是 `m` 的成员。
<!--ja-->
値は `m` の中に収まることが保証される。有限の要素については、その後続が極限の性質によって `ω` の要素となり、`ω` は `m` に含まれる。`m` の要素については、所属がその判定そのものであり、空集合は `ω` の、したがって `m` の要素である。
<!--/-->

```agda
    value-in : (x : S) (f : Fin? x) (t : Top? x) → ⟨ fst (value x f t) ∈ˢ m ⟩
    value-in x (yes k) _ =
      subst (λ w → ⟨ w ∈ˢ m ⟩) (sym (sucʟ-fst x)) (ω⊆m (sucV (fst x)) (ω-limit (fst x) k))
    value-in x (no _) (inl k) = k
    value-in x (no _) (inr _) = ω⊆m ∅ (#∈ω zero)
```

<!--en-->
The witness type for the graph formula is declared: either `x` is finite and `y` is its successor, or `x` is not finite, lies in `m`, and `y` equals `x`, or `x` equals the top `m` and `y` is empty. The three alternatives are truncated, and each carries its own memberships and equations.
<!--zh-->
图公式的见证类型在此声明：要么 `x` 有限且 `y` 是其后继；要么 `x` 非有限、属于 `m` 且 `y` 等于 `x`；要么 `x` 等于顶端 `m` 且 `y` 为空。三种选择被截断，各自携带自己的隶属与等式。
<!--ja-->
グラフの論理式の証人の型が宣言される。`x` が有限で `y` はその後続、`x` が非有限で `m` に属し `y` は `x` に等しい、あるいは `x` が頂点 `m` に等しく `y` は空である、の三つの選択肢である。三つは切り詰めの下にあり、それぞれがみずからの所属と等式を運ぶ。
<!--/-->

```agda

    Wit : (y x : S) → Type (ℓ-suc ℓ)
    Wit y x = ∥ (⟨ fst x ∈ˢ ω ⟩ × (fst y ≡ sucV (fst x)))
              ⊎ ( ((⟨ fst x ∈ˢ ω ⟩ → ⊥₀) × ⟨ fst x ∈ˢ m ⟩ × (fst y ≡ fst x))
                ⊎ ((fst x ≡ m) × (fst y ≡ ∅)) ) ∥₁

```

<!--en-->
The graph formula is stated in the object language, and its first disjunct says that `x` is a member of the internal `ω` and `y` is its successor, read by the successor clause. The second disjunct begins by denying that `x` is finite.
<!--zh-->
图公式在对象语言中陈述，其第一个析取支说：`x` 属于内部 `ω` 且 `y` 是其后继，由后继子句读出。第二个析取支首先否认 `x` 有限。
<!--ja-->
グラフの論理式は対象言語で述べられる。その第一の選言肢は、`x` が内部の `ω` に属し `y` がその後続であることを、後続の節によって読み取る。第二の選言肢はまず、`x` が有限であることを否定する。
<!--/-->

```agda
  opaque
    graph : Formula S 2
    graph = ((var (suc zero) ∈̇ con ωʟ) ∧̇ sucAtL (suc zero) zero)
          ∨̇ ( ( (¬̇ (var (suc zero) ∈̇ con ωʟ))
              ∧̇ ((var (suc zero) ∈̇ con mL) ∧̇ (var zero ≐ var (suc zero))) )
```

<!--en-->
The two guarded alternatives inside complete the second and third disjuncts: a non-finite member of `m` is paired with itself, and the top element is paired with the empty set of `L`.
<!--zh-->
其内两条受守卫的选项补全第二、第三析取支：`m` 的非有限成员与自身配对，顶端元素与 `L` 的空集配对。
<!--ja-->
その内側の二つの守られた選択肢が第二と第三の選言肢を完成させる。`m` の非有限の要素はみずからと対にされ、頂点の要素は `L` の空集合と対にされる。
<!--/-->

```agda
            ∨̇ ((var (suc zero) ≐ con mL) ∧̇ (var zero ≐ con ∅ʟ)) )

```

<!--en-->
The adequacy of the successor clause is recorded once: satisfaction of the successor atom at the two-entry context is the equation between `y` and the ambient successor of `x`.
<!--zh-->
后继子句的充分性记录一次：后继原子在二元组语境中的满足，就是 `y` 与外围后继 `sucV x` 之间的等式。
<!--ja-->
後続の節の妥当性が一度記録される。二項目の文脈での後続の原子の充足は、`y` と周囲の後続 `sucV x` との間の等式である。
<!--/-->

```agda
    private
      sa : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ sucAtL (suc zero) zero ⟩ ≡ (fst y ≡ sucV (fst x))
      sa y x = cong ⟨_⟩ (sucAtL-adequate (suc zero) zero (y ∷ x ∷ []))

```

<!--en-->
Reading the formula outward eliminates the truncated disjunction into the propositional witness type. The successor clause is converted by adequacy, while propositional resizing lowers the refutation in the middle clause from its lifted universe; the top clause already has the required form.
<!--zh-->
向外读取公式时，将命题截断下的析取消去到同为命题的见证类型中。后继子句由充分性转换；中间子句中的反驳则通过命题换级从提升后的宇宙降回所需层级；顶端子句已经具有所需形式。
<!--ja-->
論理式を外向きに読むと、命題的切り詰めの下の論理和を、やはり命題である証人型へ除去する。後続の節は妥当性によって変換し、中間の節の反証は命題リサイズによって持ち上げられた宇宙から必要なレベルへ戻す。頂点の節はすでに必要な形である。
<!--/-->

```agda
    graph-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → Wit y x
    graph-out y x = rec₁ squash₁
      (λ { (inl (k , e)) → ∣ inl (k , transport (sa y x) e) ∣₁
         ; (inr h) → map₁ (λ { (inl (n , (k , e))) →
                                  inr (inl ((λ hx → lower (n hx)) , k , e))
```

<!--en-->
The third disjunct carries only the two equations of the top case, so its translation is direct.
<!--zh-->
第三个析取支只携带顶端情形的两条等式，故其翻译是直接的。
<!--ja-->
第三の選言肢は頂点の場合の二つの等式だけを運ぶので、その翻訳は直接である。
<!--/-->

```agda
                              ; (inr (q , e)) → inr (inr (q , e)) }) h })

```

<!--en-->
The three inward lemmas rebuild the formula from each kind of witness. For a finite member, the successor equation is transported back along the adequacy into the first disjunct.
<!--zh-->
三条向内引理从每种见证重建公式。对有限成员，后继等式沿充分性反方向传输，进入第一个析取支。
<!--ja-->
三つの内向きの補題が、それぞれの証人から論理式を組み立て直す。有限の要素では、後続の等式が妥当性に沿って逆向きに輸送され、第一の選言肢に入る。
<!--/-->

```agda
    in-fin : (y x : S) → ⟨ fst x ∈ˢ ω ⟩ → fst y ≡ sucV (fst x) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-fin y x k e = ∣ inl (k , transport (sym (sa y x)) e) ∣₁

```

<!--en-->
For a non-finite member of `m`, the refutation of `x ∈ ω` is lifted into the object-level negation. Together with `x ∈ m` and `y = x`, it supplies the middle disjunct.
<!--zh-->
对 `m` 的非有限成员，`x ∈ ω` 的反驳被提升为对象层的否定；它与 `x ∈ m` 和 `y = x` 一起构成中间析取支。
<!--ja-->
`m` の非有限な要素については、`x ∈ ω` の反証を対象レベルの否定へ持ち上げる。これを `x ∈ m` および `y = x` と合わせると、中間の選言肢が得られる。
<!--/-->

```agda
    in-mid : (y x : S) → (⟨ fst x ∈ˢ ω ⟩ → ⊥₀) → ⟨ fst x ∈ˢ m ⟩ → fst y ≡ fst x
           → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-mid y x n k e = ∣ inr ∣ inl ((λ hx → lift (n hx)) , (k , e)) ∣₁ ∣₁

```

<!--en-->
For the top element, the two equations of the top case are assembled directly into the third disjunct.
<!--zh-->
对顶端元素，顶端情形的两条等式被直接组装进第三个析取支。
<!--ja-->
頂点の要素では、頂点の場合の二つの等式が第三の選言肢に直接組み立てられる。
<!--/-->

```agda
    in-top : (y x : S) → fst x ≡ m → fst y ≡ ∅ → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
    in-top y x q e = ∣ inr ∣ inr (q , e) ∣₁ ∣₁

```

<!--en-->
The shift function is now defined through the two decisions: the value is the successor, the element itself, or the empty set, according to how the decisions classify the input.
<!--zh-->
移位函数现在经由两个判定定义：按判定对输入的分类，取值分别是后继、元素自身或空集。
<!--ja-->
移し変えの関数は、二つの判定を通して定義される。判定が入力を分類する仕方に応じて、値は後続、要素そのもの、あるいは空集合である。
<!--/-->

```agda
  private
    fn : (x : S) → Mem x → S
    fn x h = value x (fin? x) (top? x h)

```

<!--en-->
The defining clause is verified in all three cases: the finite case quotes the successor equation, the middle case is definitional, and the top case pairs the empty set with the top element.
<!--zh-->
定义子句在三种情形下都得到验证：有限情形引用后继等式，中间情形是定义性的，顶端情形把空集与顶端元素配对。
<!--ja-->
定義の節は三つの場合すべてで確かめられる。有限の場合は後続の等式を引用し、中間の場合は定義的であり、頂点の場合は空集合と頂点の要素を対にする。
<!--/-->

```agda
    defines' : (x : S) (f : Fin? x) (t : Top? x) → ⟨ (value x f t ∷ x ∷ []) ⊨ graph ⟩
    defines' x (yes k) _       = in-fin (sucʟ x) x k (sucʟ-fst x)
    defines' x (no n) (inl k) = in-mid x x n k refl
    defines' x (no n) (inr q) = in-top ∅ʟ x q refl

```

<!--en-->
Uniqueness reads the graph backwards: any `y` paired with `x` in the graph equals the chosen value. The proof consumes the truncated disjunction into the equality goal, which is an equation in an h-set.
<!--zh-->
唯一性把图反向读出：图中与 `x` 配对的任何 `y` 都等于所选的取值。证明把截断的析取消耗进等式目标，而后者是 h-集合中的等式。
<!--ja-->
一意性はグラフを逆向きに読む。グラフの中で `x` と対にされる任意の `y` は、選ばれた値に等しくなる。証明は切り詰められた選言を、h-集合における等式という目標の中へ消費する。
<!--/-->

```agda
    only' : (x : S) (f : Fin? x) (t : Top? x) (y : S)
          → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ value x f t
    only' x f t y hy = rec₁ (isSetS y (value x f t)) (go f t) (graph-out y x hy)
      where
      go : (f : Fin? x) (t : Top? x)
```

<!--en-->
The case function receives the unpacked alternatives together with the chosen decisions. In the finite case with the finite affirmation, the successor equation and the internal pairing equation agree after transporting along the successor's first-projection identification.
<!--zh-->
情形函数接收展开后的选项与已选定的判定。有限情形配有限肯定时，后继等式与内部配对等式沿后继的第一投影等同传输后彼此一致。
<!--ja-->
場合分けの関数は、展開された選択肢と選ばれた判定を受け取る。有限の場合に有限の肯定が組になるとき、後続の等式と内部の対の等式は、後続の第一射影の同定に沿って輸送されれば一致する。
<!--/-->

```agda
         → (⟨ fst x ∈ˢ ω ⟩ × (fst y ≡ sucV (fst x)))
           ⊎ ( ((⟨ fst x ∈ˢ ω ⟩ → ⊥₀) × ⟨ fst x ∈ˢ m ⟩ × (fst y ≡ fst x))
             ⊎ ((fst x ≡ m) × (fst y ≡ ∅)) )
         → y ≡ value x f t
      go (yes k) _       (inl (_ , e))             = S≡ (e ∙ sym (sucʟ-fst x))
```

<!--en-->
The next five clauses compare the chosen finite or non-finite member case with a graph witness. A finite choice contradicts either the middle witness's refutation or the top equation; a non-finite member choice contradicts a finite witness, agrees with a middle witness by its equation, and excludes a top witness because a member of `m` cannot equal `m`.
<!--zh-->
接下来的五个子句把已选定的有限情形或非有限成员情形与图见证比较。有限选择分别与中间见证中的反驳或顶端等式矛盾；非有限成员选择与有限见证矛盾，凭中间见证的等式与其中间值一致，并由 `m` 的成员不可能等于 `m` 排除顶端见证。
<!--ja-->
続く五つの節では、選ばれた有限の場合または非有限な要素の場合を、グラフの証人と照合する。有限という選択は、中間の証人に含まれる反証とも頂点の等式とも矛盾する。非有限な要素という選択は、有限の証人とは矛盾し、中間の証人とはその等式によって一致し、`m` の要素は `m` 自身に等しくなれないことから頂点の証人を排除する。
<!--/-->

```agda
      go (yes k) _       (inr (inl (n , _ , _)))   = ⊥₀-rec (n k)
      go (yes k) _       (inr (inr (q , _)))       = ⊥₀-rec (ω-fin x k q)
      go (no n) (inl k) (inl (k' , _))            = ⊥₀-rec (n k')
      go (no n) (inl k) (inr (inl (_ , _ , e)))   = S≡ e
      go (no n) (inl k) (inr (inr (q , _)))       = ⊥₀-rec (not-both x k q)
```

<!--en-->
If the chosen input is the top element, a finite witness contradicts its non-finiteness, and a middle witness contradicts the fact that an element of `m` cannot equal `m`. A top witness gives the required equality directly from its empty-value equation.
<!--zh-->
若选定的输入是顶端元素，则有限见证与其非有限性矛盾，中间见证则与 `m` 的成员不可能等于 `m` 相矛盾。顶端见证由其空值等式直接给出所需相等。
<!--ja-->
選ばれた入力が頂点なら、有限の証人はその非有限性と矛盾し、中間の証人は `m` の要素が `m` 自身に等しくなれないことと矛盾する。頂点の証人からは、空集合を値とする等式によって必要な等しさが直接得られる。
<!--/-->

```agda
      go (no n) (inr q) (inl (k' , _))            = ⊥₀-rec (n k')
      go (no n) (inr q) (inr (inl (_ , k , _)))   = ⊥₀-rec (not-both x k q)
      go (no n) (inr q) (inr (inr (_ , e)))       = S≡ e

```

<!--en-->
These data determine a definable function from `sucʟ mL` to `mL`: every input receives the chosen shift value in `m`, and the displayed formula is its graph.
<!--zh-->
这些数据确定了从 `sucʟ mL` 到 `mL` 的可定义函数：每个输入都取得位于 `m` 中的选定移位值，而上面的公式正是其图。
<!--ja-->
以上のデータにより、`sucʟ mL` から `mL` への定義可能な関数が定まる。各入力には `m` に属するシフト値が割り当てられ、上の論理式がそのグラフになる。
<!--/-->

```agda
    M : DefinableMap
    M = record
      { dom = D ; cod = mL ; fn = fn
      ; into = λ x h → value-in x (fin? x) (top? x h)
      ; graph = graph
```

<!--en-->
Excluded middle supplies the two decisions for each input. The preceding existence and uniqueness arguments then show that the graph holds exactly at the selected value.
<!--zh-->
排中律为每个输入给出这两个判定。前面的存在性与唯一性论证随即表明，该图恰在选定的值处成立。
<!--ja-->
排中律は各入力について二つの判定を与える。先の存在性と一意性の議論により、このグラフがちょうど選ばれた値について成り立つことが分かる。
<!--/-->

```agda
      ; defines = λ x h → defines' x (fin? x) (top? x h)
      ; only = λ x h → only' x (fin? x) (top? x h) }

```

<!--en-->
Injectivity is proved by comparing the cases for two inputs. If both are finite, equality of their shifted values is equality of their successors, so injectivity of ordinal successor identifies the original ordinals.
<!--zh-->
单射性通过比较两个输入各自所属的情形来证明。若二者都有限，则移位值相等就是其后继相等，因而序数后继的单射性认同原来的两个序数。
<!--ja-->
単射性は、二つの入力について場合を比較して証明する。両方が有限なら、シフト後の値の等しさはそれぞれの後続の等しさなので、順序数の後続の単射性から元の二つの順序数が等しいと分かる。
<!--/-->

```agda
    inj' : (x : S) (f : Fin? x) (t : Top? x) (x' : S) (f' : Fin? x') (t' : Top? x')
         → fst (value x f t) ≡ fst (value x' f' t') → fst x ≡ fst x'
    inj' x (yes k) _ x' (yes k') _ e =
      ord-suc-inj (fst x) (fst x') (mem-ord {A = ω} ω-ord (fst x) k)
        (sym (sucʟ-fst x) ∙ e ∙ sucʟ-fst x')
```

<!--en-->
A finite input cannot share its shifted value with a non-finite member: that equality would put the latter's value, and hence the latter itself, in `ω`. Nor can it share its value with the top input, because that would equate a successor with the empty set.
<!--zh-->
有限输入不可能与非有限成员取得相同的移位值：该等式会使后者的值、也就是后者本身属于 `ω`。它也不可能与顶端输入取得相同的值，因为这会令一个后继等于空集。
<!--ja-->
有限な入力が非有限な要素と同じシフト値をもつことはない。その等しさから、後者の値、したがって後者自身が `ω` に属することになるからである。頂点の入力とも値を共有できない。そうすると後続が空集合に等しくなってしまう。
<!--/-->

```agda
    inj' x (yes k) _ x' (no n') (inl _) e =
      ⊥₀-rec (n' (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (sucʟ-fst x) ∙ e) (ω-limit (fst x) k)))
    inj' x (yes k) _ x' (no n') (inr _) e =
      ⊥₀-rec (suc≢∅ (fst x) (sym (sucʟ-fst x) ∙ e))
    inj' x (no n) (inl _) x' (yes k') _ e =
```

<!--en-->
The reverse finite/non-finite case gives the same contradiction. Two non-finite members with equal values are equal immediately, while a non-finite member cannot share the top value: equality with the empty set would make it a member of `ω`.
<!--zh-->
有限与非有限次序相反的情形给出同样的矛盾。两个非有限成员若取值相等，便立即相等；非有限成员则不可能与顶端取得同一个值，因为等于空集会使它属于 `ω`。
<!--ja-->
有限と非有限の順序を逆にした場合も、同じ矛盾になる。二つの非有限な要素は、値が等しければ直ちに等しくなる。一方、非有限な要素は頂点と同じ値をもてない。空集合に等しければ `ω` に属することになるからである。
<!--/-->

```agda
      ⊥₀-rec (n (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (sucʟ-fst x') ∙ sym e) (ω-limit (fst x') k')))
    inj' x (no n) (inl _) x' (no n') (inl _) e = e
    inj' x (no n) (inl _) x' (no n') (inr _) e =
      ⊥₀-rec (n (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym e) (#∈ω zero)))
    inj' x (no n) (inr _) x' (yes k') _ e =
```

<!--en-->
For a top input, equality with a finite value would again make a successor empty, and equality with a non-finite member's value would make that member equal to the empty set and hence finite. If both inputs are top, their equations with `m` identify them. Thus the shift is internally injective.
<!--zh-->
对顶端输入而言，与有限输入的值相等会再次令后继成为空集；与非有限成员的值相等则会令该成员等于空集，因而成为有限序数。若两个输入都是顶端，它们各自与 `m` 的等式便认同二者。因此该移位在 `L` 内部是单射。
<!--ja-->
頂点の入力について、有限な入力の値と等しければ後続が空集合になり、非有限な要素の値と等しければその要素が空集合、したがって有限な順序数になってしまう。両方の入力が頂点なら、それぞれを `m` と結ぶ等式から両者が等しいと分かる。したがって、このシフトは `L` の内部で単射である。
<!--/-->

```agda
      ⊥₀-rec (suc≢∅ (fst x') (sym (sucʟ-fst x') ∙ sym e))
    inj' x (no n) (inr _) x' (no n') (inl _) e =
      ⊥₀-rec (n' (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (#∈ω zero)))
    inj' x (no n) (inr q) x' (no n') (inr q') e = q ∙ sym q'
  injL : InjL (sucʟ mL) mL
```

<!--en-->
The definable shift and the preceding case analysis give the coded injection `sucʟ mL ↪ mL`. We will also use the elementary fact that two members of a set represented by the same fiber index are equal: applying the presentation map to the index equality recovers equality of the represented members.
<!--zh-->
可定义移位与前面的分类讨论共同给出编码单射 `sucʟ mL ↪ mL`。还要用到一个基本事实：若一个集合的两个成员由同一个纤维索引表示，则它们相等；将呈现映射作用于索引等式，便恢复出所表示成员的相等。
<!--ja-->
定義可能なシフトと先の分類により、符号化された単射 `sucʟ mL ↪ mL` が得られる。さらに、ある集合の二つの要素が同じファイバー添字で表されるなら両者は等しい、という基本的な事実を用いる。添字の等しさに提示写像を作用させると、表された要素の等しさが復元される。
<!--/-->

```agda
  injL = Inj.injL M (λ x h x' h' → inj' x (fin? x) (top? x h) x' (fin? x') (top? x' h'))
opaque
  fiber-inj : (g : V ℓ) {x y : V ℓ} (mx : ⟨ x ∈ˢ g ⟩) (my : ⟨ y ∈ˢ g ⟩)
            → fiber g mx .fst ≡ fiber g my .fst → x ≡ y
  fiber-inj g mx my e = sym (fiber g mx .snd) ∙ cong ⟪ g ⟫↪ e ∙ fiber g my .snd
```

<!--en-->
For each constructible infinite ordinal `a` that is an internal cardinal, the induction goal is a coded injection from its Cartesian square `a × a` back into `a`. Packaging the statement as `Goal a` lets membership induction apply it uniformly below `a`.
<!--zh-->
对每个可构造的无穷序数 `a`，若它还是内部基数，归纳目标便是从其笛卡尔平方 `a × a` 回到 `a` 的编码单射。将该命题包装为 `Goal a`，即可在隶属归纳中对 `a` 以下的对象统一使用它。
<!--ja-->
構成可能な無限順序数 `a` が内部の基数でもあるとき、帰納目標はその直積平方 `a × a` から `a` への符号化された単射である。この主張を `Goal a` としてまとめることで、所属に関する帰納法を `a` より下の対象へ一様に適用できる。
<!--/-->

```agda

Goal : V ℓ → Type (ℓ-suc ℓ)
Goal a = (la : ⟨ isL a ⟩) → IsOrd a → IsCardinalL (a , la)
       → (⟨ a ∈ˢ ω ⟩ → ⊥₀) → InjL (prodL (a , la)) (a , la)

```

<!--en-->
The induction step receives the set `a`, the induction hypothesis for every member of `a`, and the four hypotheses: constructibility, ordinality, internal cardinality, and infinity. The cardinality hypothesis is the exclusion of internal injections of `κ` into its own members, the form in which the collapse counting will be used.
<!--zh-->
归纳步接收集合 `a`、对 `a` 每个成员的归纳假设，以及四条假设：可构造性、序数性、内部基数性与无穷性。基数性假设排除「`κ` 内部单射入其自身成员」，这正是塌缩计数所要使用的形式。
<!--ja-->
帰納の段階は、集合 `a`、`a` の各要素に対する帰納仮定、そして四つの仮定を受け取る。構成可能性、順序数性、内部の基数性、無限性である。基数性の仮定は、`κ` がみずからの要素へ内部的に単射することを排除するもので、崩壊の計数が用いる形そのものである。
<!--/-->

```agda
module Step (a : V ℓ) (ih : (a' : V ℓ) → ⟨ a' ∈ˢ a ⟩ → Goal a')
            (la : ⟨ isL a ⟩) (oa : IsOrd a) (carda : IsCardinalL (a , la))
            (a∉ω : ⟨ a ∈ˢ ω ⟩ → ⊥₀) where

```

<!--en-->
Write `κ` for the constructible set whose underlying ordinal is `a`. This keeps the ambient ordinal data and the proof that it belongs to `L` together whenever an internal construction is formed.
<!--zh-->
以 `κ` 表示底层序数为 `a` 的可构造集合。这样，在形成内部构造时，外围序数数据与其属于 `L` 的证明始终成对出现。
<!--ja-->
台となる順序数が `a` である構成可能集合を `κ` と書く。これにより、内部の構成を行うたびに、周囲の順序数のデータとそれが `L` に属することの証明を一緒に扱える。
<!--/-->

```agda
  κ : S
  κ = a , la

```

<!--en-->
We now consider `κ × κ` with its Gödel order and the ordinal obtained by collapsing that well-order. The task is to show that every initial segment of this collapse is still bounded below `κ`.
<!--zh-->
现在考察带有 Gödel 序的 `κ × κ`，以及将该良序塌缩所得的序数。目标是证明这一塌缩的每个初始段仍在 `κ` 以下有界。
<!--ja-->
ここから、Gödel 順序を備えた `κ × κ` と、その整列順序を崩壊して得られる順序数を考える。目標は、この崩壊の各始切片がなお `κ` より下に抑えられることを示すことである。
<!--/-->

```agda
  open Order κ oa
  open Coll κ oa

```

<!--en-->
Since the ordinal `a` is not finite, it contains every finite ordinal. We also need closure under successor: for `m ∈ a`, trichotomy places `sucV m` below, equal to, or above `a`; the next cases rule out the latter two possibilities.
<!--zh-->
由于序数 `a` 不是有限序数，它包含每个有限序数。还需证明它对后继封闭：给定 `m ∈ a`，三歧性将 `sucV m` 置于 `a` 以下、等于 `a` 或高于 `a`；接下来的分类将排除后两种可能。
<!--ja-->
順序数 `a` は有限順序数ではないので、すべての有限順序数を含む。さらに後続について閉じていることが必要である。`m ∈ a` に対し、三分法は `sucV m` が `a` より下、`a` と等しい、または `a` より上のいずれかであるとする。続く場合分けで後二者を排除する。
<!--/-->

```agda
  ω⊆a : (z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ a ⟩
  ω⊆a = ω⊆ a oa a∉ω
  suc∈ : (m : V ℓ) → ⟨ m ∈ˢ a ⟩ → ⟨ sucV m ∈ˢ a ⟩
  suc∈ m m∈a = go (ord-tri (sucV m) (suc-ord om) a oa)
    where
```

<!--en-->
Because `m` is a member of the ordinal `a`, it is itself an ordinal. Its constructibility follows from membership in the constructible set `a`, so `m` determines an element `mL` of the internal universe.
<!--zh-->
由于 `m` 是序数 `a` 的成员，`m` 本身也是序数。又因 `m` 属于可构造集合 `a`，它也是可构造的，因而确定内部论域中的元素 `mL`。
<!--ja-->
`m` は順序数 `a` の要素なので、それ自身も順序数である。また、構成可能集合 `a` に属することから `m` も構成可能であり、内部の論域の要素 `mL` を定める。
<!--/-->

```agda
    om : IsOrd m
    om = mem-ord {A = a} oa m m∈a
    mL : S
    mL = ordL m om

```

<!--en-->
Apply trichotomy to `sucV m` and `a`. The first case is exactly the desired membership. If `sucV m = a`, comparing `m` with `ω` splits the contradiction into the finite case and the two infinite cases handled next.
<!--zh-->
对 `sucV m` 与 `a` 应用三歧性。第一种情形正是所需的隶属关系。若 `sucV m = a`，再比较 `m` 与 `ω`，便把矛盾分成有限情形和接下来处理的两种无穷情形。
<!--ja-->
`sucV m` と `a` に三分法を適用する。第一の場合は、求める所属そのものである。`sucV m = a` なら、さらに `m` と `ω` を比較することで、矛盾を有限の場合と、続いて扱う二つの無限の場合に分ける。
<!--/-->

```agda
    go : ⟨ sucV m ∈ˢ a ⟩ ⊎ ((sucV m ≡ a) ⊎ ⟨ a ∈ˢ sucV m ⟩) → ⟨ sucV m ∈ˢ a ⟩
    go (inl h) = h
    go (inr (inl e)) = ⊥₀-rec (fin (ord-tri m om ω ω-ord))
      where
      fin : ⟨ m ∈ˢ ω ⟩ ⊎ ((m ≡ ω) ⊎ ⟨ ω ∈ˢ m ⟩) → ⊥₀
```

<!--en-->
If `m` were a member of `ω`, its successor would also be a member of `ω`, putting the cardinal `a` inside `ω` against the infinity hypothesis. If instead `m` equals `ω` or contains it, the internal cardinality of `a`, applied at the member `m`, would refute the shift injection `sucʟ mL ↪ mL`, an internal injection into a member of the cardinal.
<!--zh-->
若 `m` 属于 `ω`，则其后继也属于 `ω`，从而把基数 `a` 放进 `ω`，与无穷性假设矛盾。若 `m` 等于 `ω` 或包含 `ω`，则在成员 `m` 处施用 `a` 的内部基数性，便会反驳移位单射 `sucʟ mL ↪ mL`，后者是到该基数某个成员的内部单射。
<!--ja-->
`m` が `ω` の要素なら、その後続も `ω` の要素となり、基数 `a` が `ω` の内側に入って無限性の仮定と矛盾する。`m` が `ω` に等しいか `ω` を含む場合は、要素 `m` のところで `a` の内部の基数性を適用すると、移し変えの単射 `sucʟ mL ↪ mL`、すなわち基数のある要素への内部の単射が退けられる。
<!--/-->

```agda
      fin (inl m∈ω) = a∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (ω-limit m m∈ω))
      fin (inr r) =
        carda mL m∈a (subst (λ w → InjL w mL) sucL≡κ (Shift.injL mL om m∉ω))
        where
        m∉ω : ⟨ m ∈ˢ ω ⟩ → ⊥₀
```

<!--en-->
The local non-finiteness is read off the same trichotomy: if `m` equalled `ω`, the assumed membership would place `ω` inside itself; if `ω` belonged to `m`, transitivity would again place `ω` inside itself. Both contradict the irreflexivity of membership.
<!--zh-->
局部非有限性由同一三歧性读出：若 `m` 等于 `ω`，所假设的隶属会把 `ω` 放进其自身；若 `ω` 属于 `m`，传递性同样会把 `ω` 放进其自身。两者都与隶属的非自反性矛盾。
<!--ja-->
局所的な非有限性は、同じ三分法から読み取られる。`m` が `ω` に等しいなら、仮定された所属が `ω` をみずからの内側に置き、`ω` が `m` に属するなら、推移性が再び `ω` をみずからの内側に置く。どちらも所属の非反射性と矛盾する。
<!--/-->

```agda
        m∉ω h = rr r
          where
          rr : (m ≡ ω) ⊎ ⟨ ω ∈ˢ m ⟩ → ⊥₀
          rr (inl e') = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e' h)
          rr (inr ω∈m) = ∈-irrefl ω (ω-ord .fst ω∈m h)
```

<!--en-->
The equality `sucV m = a` identifies the internal successor `sucʟ mL` with `κ`, so the shift would give the injection into `m` forbidden by cardinality. In the remaining trichotomy case, `a ∈ sucV m` means either `a ∈ m` or `a = m`; each alternative yields self-membership of an ordinal and is therefore impossible.
<!--zh-->
等式 `sucV m = a` 将内部后继 `sucʟ mL` 与 `κ` 认同，于是移位会给出基数性所禁止的、从 `κ` 到 `m` 的单射。在三歧性的余下情形中，`a ∈ sucV m` 意味着 `a ∈ m` 或 `a = m`；两种选择都会导出某个序数属于自身，因而都不可能。
<!--ja-->
等式 `sucV m = a` は内部の後続 `sucʟ mL` を `κ` と同一視するので、シフトから、基数性に反する `κ` から `m` への単射が得られる。三分法の残る場合では、`a ∈ sucV m` は `a ∈ m` または `a = m` を意味する。どちらからも順序数の自己所属が導かれるため、不可能である。
<!--/-->

```agda
        sucL≡κ : sucʟ mL ≡ κ
        sucL≡κ = Σ≡Prop (λ v → snd (isL v)) (sucʟ-fst mL ∙ e)
    go (inr (inr h)) = ⊥*-rec
      (∈sucV-elim {A = m} {x = a} {P = ⊥* {ℓ-suc ℓ}} isProp⊥* h
        (λ a∈m → lift (∈-irrefl a (oa .fst a∈m m∈a)))
```

<!--en-->
Successor closure now makes the induction hypothesis available at the smaller ordinals needed below. More generally, if an infinite ordinal `γ` lies below `a`, choose an internal cardinal representative of `γ`; the induction hypothesis at that representative will yield an injection `prodL γ ↪ γ`.
<!--zh-->
有了后继封闭性，便可在下文所需的较小序数处使用归纳假设。更一般地，若无穷序数 `γ` 位于 `a` 以下，就为 `γ` 选取一个内部基数代表；在该代表处使用归纳假设，将得到单射 `prodL γ ↪ γ`。
<!--ja-->
後続についての閉性が得られたので、以下で必要となるより小さい順序数に帰納仮定を適用できる。より一般に、無限順序数 `γ` が `a` より下にあるなら、`γ` の内部基数代表を選び、その代表に帰納仮定を適用して `prodL γ ↪ γ` を得る。
<!--/-->

```agda
        (λ a≡m → lift (∈-irrefl m (subst (λ w → ⟨ m ∈ˢ w ⟩) a≡m m∈a))))
  prod-into : (γ : S) → IsOrd (fst γ) → ⟨ fst γ ∈ˢ a ⟩
            → (⟨ fst γ ∈ˢ ω ⟩ → ⊥₀) → InjL (prodL γ) γ
  prod-into γ oγ γ∈a γ∉ω = rec₁ squash₁ build (cardOf γ oγ)
    where
```

<!--en-->
The cardinal representative delivers its data in truncated form: an ordinal `μ` that is an internal cardinal, contained in `γ`, with `γ` injecting into it and it into `γ`. The build function turns this data into the product injection.
<!--zh-->
基数代表以截断形式交付其数据：序数 `μ` 是内部基数、包含于 `γ`，且 `γ` 单射入它、它单射入 `γ`。函数 `build` 把这些数据变成乘积单射。
<!--ja-->
基数の代表は、切り詰められた形でデータを渡す。順序数 `μ` は内部の基数であり `γ` に含まれ、`γ` から `μ` へ、`μ` から `γ` への単射が伴う。関数 `build` はこのデータを積の単射へ変える。
<!--/-->

```agda
    build : Σ[ μ ∈ S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst γ ⟩)
              × InjL γ μ × InjL μ γ )
          → InjL (prodL γ) γ
```

<!--en-->
The injection composes three injections. The product injection lifts `γ ↪ μ` coordinatewise; the induction hypothesis applies at the internal cardinal `μ`, giving `prodL μ ↪ μ`; and `μ ↪ γ` composes the result down into `γ`.
<!--zh-->
该单射复合三条单射。乘积单射把 `γ ↪ μ` 逐坐标提升；归纳假设施用于内部基数 `μ`，给出 `prodL μ ↪ μ`；再经 `μ ↪ γ` 把结果复合回 `γ`。
<!--ja-->
単射は三つの単射を合成する。積の単射が `γ ↪ μ` を座標ごとに持ち上げ、帰納仮定が内部の基数 `μ` において適用されて `prodL μ ↪ μ` を与え、さらに `μ ↪ γ` によって結果が `γ` の中へ合成される。
<!--/-->

```agda
    build (μ , oμ , cardμ , μ⊆γ , γ↪μ , μ↪γ) =
      injl-trans (prodL γ) (prodL μ) γ (prod-inj γ μ γ↪μ)
        (injl-trans (prodL μ) μ γ (ih (fst μ) μ∈a (snd μ) oμ cardμ μ∉ω) μ↪γ)
      where
      μ∈a : ⟨ fst μ ∈ˢ a ⟩
```

<!--en-->
The representative `μ` also lies below `a`. If `μ ∈ γ`, transitivity carries it through `γ ∈ a`; if `μ = γ`, membership transports directly. The remaining comparison `γ ∈ μ` is impossible, because the inclusion `μ ⊆ γ` would then give `γ ∈ γ`.
<!--zh-->
代表 `μ` 同样位于 `a` 以下。若 `μ ∈ γ`，传递性结合 `γ ∈ a` 即得 `μ ∈ a`；若 `μ = γ`，直接搬运隶属关系即可。余下的比较 `γ ∈ μ` 不可能成立，因为包含关系 `μ ⊆ γ` 会由此给出 `γ ∈ γ`。
<!--ja-->
代表 `μ` も `a` より下にある。`μ ∈ γ` なら、`γ ∈ a` と推移性から `μ ∈ a` が従う。`μ = γ` なら、所属をその等しさに沿って移送する。残る `γ ∈ μ` は不可能である。包含 `μ ⊆ γ` によって `γ ∈ γ` が導かれるからである。
<!--/-->

```agda
      μ∈a = go (ord-tri (fst μ) oμ (fst γ) oγ)
        where
        go : ⟨ fst μ ∈ˢ fst γ ⟩ ⊎ ((fst μ ≡ fst γ) ⊎ ⟨ fst γ ∈ˢ fst μ ⟩) → ⟨ fst μ ∈ˢ a ⟩
        go (inl h)       = oa .fst h γ∈a
        go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ a ⟩) (sym e) γ∈a
```

<!--en-->
The representative `μ` must also be infinite. If `μ ∈ ω`, the inclusion `ω ↪ γ` for infinite `γ`, followed by `γ ↪ μ`, would inject `ω` into the finite ordinal `μ`, which is impossible. For later use, `Seg p b` records a predecessor `r ≺ p` whose collapse value is `b`.
<!--zh-->
代表 `μ` 也必须是无穷的。若 `μ ∈ ω`，先用无穷序数 `γ` 所给出的 `ω ↪ γ`，再复合 `γ ↪ μ`，便会将 `ω` 单射入有限序数 `μ`，这是不可能的。为后文使用，`Seg p b` 记录一个满足 `r ≺ p` 且塌缩值为 `b` 的前驱 `r`。
<!--ja-->
代表 `μ` も無限でなければならない。もし `μ ∈ ω` なら、無限順序数 `γ` に対する `ω ↪ γ` と `γ ↪ μ` を合成して、`ω` を有限順序数 `μ` へ単射できてしまう。これは不可能である。後で用いるため、`Seg p b` は `r ≺ p` であり崩壊値が `b` である先行者 `r` を記録する。
<!--/-->

```agda
        go (inr (inr h)) = ⊥₀-rec (∈-irrefl (fst γ) (μ⊆γ (fst γ) h))
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → ⊥₀
      μ∉ω h = no-fin γ μ oγ γ∉ω oμ h γ↪μ
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))
```

<!--en-->
Segments are unique: two predecessors of `p` with equal collapse values are equal, since the collapse map is injective on indices, a proposition recorded once for later eliminations.
<!--zh-->
节段唯一：塌缩值相等的 `p` 的两个前驱相等，因为塌缩映射在索引上是单射的；这一命题被一次性记录，供后续消去使用。
<!--ja-->
節は一意である。崩壊の値が等しい `p` の二つの先行者は等しくなる。崩壊の写しは添字の上で単射であり、この命題が以降の消去のために一度記録される。
<!--/-->

```agda

  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ r → isProp× (OT.isProp≺ r p) (setIsSet _ _)) (I.col-inj r r' (e ∙ sym e'))

```

<!--en-->
Every member of a collapse value determines its segment, by the outward reading of the collapse and the uniqueness just proved. The maximum of a pair is then named: the larger of its two coordinates in the host order.
<!--zh-->
塌缩值的每个成员都由塌缩的外向读法与刚证明的唯一性确定其节段。随后给出对的 maximum：其两个坐标在宿主序中的较大者。
<!--ja-->
崩壊の値のすべての要素は、崩壊の外向きの読みと証明されたばかりの一意性によって、その節を確定する。ついで対の最大値が名指される。その二つの座標のホストの順序における大きい方である。
<!--/-->

```agda
  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = rec₁ (isPropSeg p b) (λ z → z) (C.col-out p b h)
  mx : OT.Dom → ⟪ K ⟫
  mx p = maxOrd (φ p .fst) (φ p .snd)

```

<!--en-->
Let `mV p` be the ambient ordinal represented by the maximum of the two coordinates of `p`. If `r ≺ p` in the collapsed Gödel order, the first coordinate of `r` lies below the successor of this maximum; this is the first coordinate bound for the Gödel order.
<!--zh-->
令 `mV p` 为 `p` 的两个坐标之最大值所表示的外围序数。若在塌缩后的 Gödel 序中 `r ≺ p`，则 `r` 的第一坐标位于该最大值的后继之下；这正是 Gödel 序对第一坐标给出的界。
<!--ja-->
`p` の二つの座標の最大値が表す周囲の順序数を `mV p` とする。崩壊された Gödel 順序で `r ≺ p` なら、`r` の第一座標はこの最大値の後続より下にある。これは Gödel 順序が与える第一座標の上界である。
<!--/-->

```agda
  mV : OT.Dom → V ℓ
  mV p = ↑ (mx p)
  opaque
    seg-fst : (p r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .fst) ∈ˢ sucV (mV p) ⟩
    seg-fst p r k = fst∈suc (φ r) (φ p) (≺-fwd r p k)
```

<!--en-->
The second coordinate of every `r ≺ p` obeys the same bound. We therefore use `gfin p = sucV (mV p)` as a common carrier for both coordinates; under the finite-case hypothesis `mV p ∈ ω`, this carrier is itself a finite ordinal.
<!--zh-->
每个 `r ≺ p` 的第二坐标也满足同一上界。因此取 `gfin p = sucV (mV p)` 作为两个坐标的共同载体；在有限情形的假设 `mV p ∈ ω` 下，该载体本身也是有限序数。
<!--ja-->
すべての `r ≺ p` について、第二座標も同じ上界を満たす。そこで `gfin p = sucV (mV p)` を両座標に共通の台として用いる。有限の場合の仮定 `mV p ∈ ω` のもとでは、この台自身も有限順序数である。
<!--/-->

```agda

    seg-snd : (p r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .snd) ∈ˢ sucV (mV p) ⟩
    seg-snd p r k = snd∈suc (φ r) (φ p) (≺-fwd r p k)
  gfin : OT.Dom → V ℓ
  gfin p = sucV (mV p)
  opaque
```

<!--en-->
For each predecessor `r ≺ p`, the two coordinate bounds select two indices in the presentation of `gfin p`; `h p r` is their ordered pair. When `mV p` is finite, this pair codes `r` inside the square of a finite ordinal.
<!--zh-->
对每个前驱 `r ≺ p`，两个坐标界分别在 `gfin p` 的呈现中选出一个索引；`h p r` 就是这两个索引组成的有序对。当 `mV p` 有限时，该有序对把 `r` 编码到一个有限序数的平方中。
<!--ja-->
各先行者 `r ≺ p` について、二つの座標の上界から `gfin p` の提示における二つの添字が選ばれ、`h p r` はその順序対である。`mV p` が有限なら、この対は `r` を有限順序数の平方の中に符号化する。
<!--/-->

```agda
    h : (p r : OT.Dom) (k : r OT.≺ p) → ⟪ gfin p ⟫ × ⟪ gfin p ⟫
    h p r k = fiber (gfin p) (seg-fst p r k) .fst , fiber (gfin p) (seg-snd p r k) .fst

```

<!--en-->
Equality of two codes `h p r` and `h p r'` forces equality of their first indices by applying the first projection. This is the first half of recovering the coordinates of `r` from its code.
<!--zh-->
若两个编码 `h p r` 与 `h p r'` 相等，对该等式应用第一投影便得到第一索引相等。这是从编码恢复 `r` 的两个坐标的第一步。
<!--ja-->
二つの符号 `h p r` と `h p r'` が等しければ、その等しさに第一射影を作用させることで、第一の添字が等しいと分かる。これは符号から `r` の座標を復元する前半である。
<!--/-->

```agda
    h-fst : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k'
          → fiber (gfin p) (seg-fst p r k) .fst
          ≡ fiber (gfin p) (seg-fst p r' k') .fst
    h-fst p r r' k k' e = cong fst e
```

<!--en-->
Applying the second projection to the same code equality likewise identifies the second indices. Thus equality of the fiber pairs controls both components separately.
<!--zh-->
对同一个编码等式应用第二投影，同样得到第二索引相等。因此，纤维对的相等分别控制了两个分量。
<!--ja-->
同じ符号の等しさに第二射影を作用させると、第二の添字も等しいと分かる。したがって、ファイバー対の等しさは二つの成分をそれぞれ決定する。
<!--/-->

```agda

    h-snd : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k'
          → fiber (gfin p) (seg-snd p r k) .fst
          ≡ fiber (gfin p) (seg-snd p r' k') .fst
    h-snd p r r' k k' e = cong snd e
```

<!--en-->
Equality of the first fiber indices implies equality of the ambient ordinals named by those fibers. Since the presentation map of `K` is injective, the first coordinates `φ r .fst` and `φ r' .fst` are equal.
<!--zh-->
第一纤维索引相等蕴含这些纤维所表示的外围序数相等。由于 `K` 的呈现映射是单射，第一坐标 `φ r .fst` 与 `φ r' .fst` 因而相等。
<!--ja-->
第一のファイバー添字が等しければ、それらのファイバーが表す周囲の順序数も等しくなる。`K` の提示写像は単射なので、第一座標 `φ r .fst` と `φ r' .fst` が等しいと従う。
<!--/-->

```agda
  step-e1 : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k' → φ r .fst ≡ φ r' .fst
  step-e1 p r r' k k' e =
    ↪-inj {a = K} (fiber-inj (gfin p) (seg-fst p r k) (seg-fst p r' k') (h-fst p r r' k k' e))

```

<!--en-->
The second transfer lemma does the same for the second coordinates, so an equality of fiber pairs determines both coordinates of the underlying pair, which is what the finite case of the collapse will need.
<!--zh-->
第二条传递引理对第二坐标做同样的事，于是纤维对的相等同时确定底层对的两个坐标，这正是塌缩的有限情形所需要的。
<!--ja-->
第二の移送の補題は第二の座標についても同じことをし、ファイバーの対の相等がもとの対の両座標を確定する。崩壊の有限の場合に必要なのはまさにこれである。
<!--/-->

```agda
  step-e2 : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
          → h p r k ≡ h p r' k' → φ r .snd ≡ φ r' .snd
  step-e2 p r r' k k' e =
    ↪-inj {a = K} (fiber-inj (gfin p) (seg-snd p r k) (seg-snd p r' k') (h-snd p r r' k k' e))

```

<!--en-->
Equality of two fiber-pair codes gives equality of both coordinates of `φ r` and `φ r'`. Pair extensionality combines these coordinate equalities, and injectivity of `φ` then gives `r = r'`. Thus the coding of predecessors of `p` is injective. The finite case to be proved says that if the maximum coordinate of `p` belongs to `ω`, then so does `C.col p`.
<!--zh-->
两个纤维对编码相等，就会使 `φ r` 与 `φ r'` 的两个坐标分别相等。对的外延性把两条坐标等式合成起来，再由 `φ` 的单射性得到 `r = r'`。因此，对 `p` 的前驱所作的编码是单射。待证的有限情形是：若 `p` 的最大坐标属于 `ω`，则 `C.col p` 也属于 `ω`。
<!--ja-->
二つのファイバー対の符号が等しければ、`φ r` と `φ r'` の二つの座標はそれぞれ等しくなる。対の外延性でこれらの座標の等しさをまとめ、さらに `φ` の単射性を用いると `r = r'` が得られる。したがって、`p` の先行者の符号化は単射である。示すべき有限の場合は、`p` の最大座標が `ω` に属するなら `C.col p` も `ω` に属する、という主張である。
<!--/-->

```agda
  step-inj : (p r r' : OT.Dom) (k : r OT.≺ p) (k' : r' OT.≺ p)
           → h p r k ≡ h p r' k' → r ≡ r'
  step-inj p r r' k k' e =
    φ-inj r r' (pair≡ (step-e1 p r r' k k' e) (step-e2 p r r' k k' e))
  col-fin : (p : OT.Dom) → ⟨ mV p ∈ˢ ω ⟩ → ⟨ C.col p ∈ˢ ω ⟩
```

<!--en-->
The proof compares the collapse value with `ω` by trichotomy, and names its finite carrier first: `g` is the successor of the ambient maximum of `p`, the set into which both coordinates of every predecessor were shown to fall.
<!--zh-->
证明用三歧性比较塌缩值与 `ω`，并先点名其有限载体：`g` 是 `p` 的外围最大值的后继，即已证明容纳每个前驱两个坐标的那个集合。
<!--ja-->
証明は三分法によって崩壊の値と `ω` を比較し、まず有限の台に名前を与える。`g` は `p` の周囲の最大値の後続であり、すべての先行者の二つの座標が収まると示された集合である。
<!--/-->

```agda
  col-fin p m∈ω = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
    where
    g : V ℓ
    g = sucV (mV p)
    og : IsOrd g
```

<!--en-->
Because `mV p ∈ ω`, the maximum is an ordinal, and its successor `g` is an ordinal as well. The limit property of `ω` gives `g ∈ ω`, so `g` is a finite ordinal. These are precisely the hypotheses needed to rule out an injection of `ω` into `g × g`.
<!--zh-->
由 `mV p ∈ ω` 可知这个最大值是序数，其后继 `g` 也仍是序数。`ω` 的极限性质给出 `g ∈ ω`，所以 `g` 是有限序数。这些条件恰好可以用来排除从 `ω` 到 `g × g` 的单射。
<!--ja-->
`mV p ∈ ω` なので、この最大値は順序数であり、その後続 `g` も順序数である。`ω` の極限性から `g ∈ ω` が従うため、`g` は有限順序数である。これらは、`ω` から `g × g` への単射を排除するために必要な仮定である。
<!--/-->

```agda
    og = suc-ord (ω-mem-ord (mV p) m∈ω)
    g∈ω : ⟨ g ∈ˢ ω ⟩
    g∈ω = ω-limit (mV p) m∈ω

```

<!--en-->
The refutation assumes that `ω` is contained in the collapse value. Then every index of `ω` names a segment of `col p`: the containment places the named member inside the collapse, and the segment lemma recovers the predecessor.
<!--zh-->
反驳假设 `ω` 包含于塌缩值。于是 `ω` 的每个索引都指名 `col p` 的一个节段：包含关系把被指名的成员放进塌缩之内，而节段引理恢复出相应的前驱。
<!--ja-->
反証は、`ω` が崩壊の値に含まれると仮定する。すると `ω` のすべての添字が `col p` の節を名指す。包含が名指された要素を崩壊の内側に置き、節の補題が先行者を復元するのである。
<!--/-->

```agda
    refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → ⊥₀
    refute sub = finite-excl-ω g og g∈ω f f-inj
      where
      s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
      s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
```

<!--en-->
For each `x ∈ ω`, let `s x` be the unique predecessor of `p` whose collapse value is `x`. The map `f` sends `x` to the two fiber indices coding the coordinates of this predecessor, hence to an element of the finite square `g × g`. It remains to show that equal such codes come from equal elements of `ω`.
<!--zh-->
对每个 `x ∈ ω`，令 `s x` 为 `p` 的唯一前驱，并使其塌缩值等于 `x`。映射 `f` 把 `x` 送到编码该前驱两个坐标的纤维索引对，因而送到有限平方 `g × g` 的一个元素。还需证明这样的编码若相等，原来的两个 `ω` 中元素也相等。
<!--ja-->
各 `x ∈ ω` に対し、崩壊値が `x` である `p` の一意な先行者を `s x` とする。写像 `f` は `x` を、その先行者の二つの座標を符号化するファイバー添字の対、したがって有限な平方 `g × g` の要素へ送る。このような符号が等しければ、もとの `ω` の要素も等しいことを示せばよいのである。
<!--/-->

```agda
      f : ⟪ ω ⟫ → ⟪ g ⟫ × ⟪ g ⟫
      f x = h p (s x .fst) (s x .snd .fst)
      f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
      f-inj x y e = ↪-inj {a = ω}
        (sym (s x .snd .snd)
```

<!--en-->
Injectivity is proved by composing three equations: the collapse value of the segment of `x` equals `x`, the segments agree as predecessors by the finite-case injection just proved, and the collapse value of the segment of `y` equals `y`. The composite forces `x` and `y` to agree.
<!--zh-->
单射性由三条等式复合而成：`x` 的节段的塌缩值等于 `x`，两个节段作为前驱由刚证明的有限情形单射相等，`y` 的节段的塌缩值等于 `y`。复合起来便迫使 `x` 与 `y` 一致。
<!--ja-->
単射性は三つの等式の合成として証明される。`x` の節の崩壊の値は `x` に等しく、二つの節は証明されたばかりの有限の場合の単射によって先行者として一致し、`y` の節の崩壊の値は `y` に等しい。合成すると、`x` と `y` が一致することが迫られる。
<!--/-->

```agda
         ∙ cong C.col (step-inj p (s x .fst) (s y .fst) (s x .snd .fst) (s y .snd .fst) e)
         ∙ s y .snd .snd)

```

<!--en-->
Trichotomy now proves `C.col p ∈ ω`. Equality `C.col p = ω` would give the forbidden inclusion `ω ⊆ C.col p`; if `ω ∈ C.col p`, transitivity of the ordinal `C.col p` gives the same inclusion. For the general inverse-collapse construction, fix a predecessor bound `p` and a constructible carrier `g`.
<!--zh-->
三歧性现在给出 `C.col p ∈ ω`。若 `C.col p = ω`，便会得到已被排除的包含 `ω ⊆ C.col p`；若 `ω ∈ C.col p`，序数 `C.col p` 的传递性也会给出同一包含。为构造一般的逆塌缩，固定一个前驱上界 `p` 和一个可构造载体 `g`。
<!--ja-->
これで三分法から `C.col p ∈ ω` が従う。`C.col p = ω` なら、すでに排除した包含 `ω ⊆ C.col p` が得られる。`ω ∈ C.col p` の場合も、順序数 `C.col p` の推移性から同じ包含が得られる。一般の逆崩壊を構成するため、先行者の上界 `p` と構成可能な台 `g` を固定する。
<!--/-->

```agda
    go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
    go (inl k)         = k
    go (inr (inl e))   = ⊥₀-rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
    go (inr (inr ω∈c)) = ⊥₀-rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))
  module Inv (p : OT.Dom) (g : S)
```

<!--en-->
Assume that, for every `r ≺ p`, both coordinates represented by `φ r` belong to the carrier of `g`. These two bounds ensure that the pair represented by `r` belongs to the internal product `prodL g`, the codomain of the inverse collapse.
<!--zh-->
假设对每个 `r ≺ p`，`φ r` 所表示的两个坐标都属于 `g` 的载体。这两条界保证 `r` 所表示的对属于内部乘积 `prodL g`，而该乘积正是逆塌缩的陪域。
<!--ja-->
各 `r ≺ p` について、`φ r` が表す二つの座標がとも `g` の台に属すると仮定する。この二つの上界により、`r` が表す対は内部の積 `prodL g` に属する。この積が逆崩壊の終域になる。
<!--/-->

```agda
             (bfst : (r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .fst) ∈ˢ fst g ⟩)
             (bsnd : (r : OT.Dom) → r OT.≺ p → ⟨ ↑ (φ r .snd) ∈ˢ fst g ⟩) where

```

<!--en-->
Every member `x` of the collapse value determines its segment: the truncated membership is eliminated, since segments are unique, and yields a predecessor `r` whose collapse value is the underlying set of `x`.
<!--zh-->
塌缩值的每个成员 `x` 都确定其节段：由于节段唯一，截断的隶属被消去，给出一个前驱 `r`，其塌缩值正是 `x` 的底层集合。
<!--ja-->
崩壊の値のすべての要素 `x` はみずからの節を確定する。節は一意なので、切り詰められた所属は消去され、崩壊の値が `x` の基底集合である先行者 `r` が得られる。
<!--/-->

```agda
    private
      pre : (x : S) → ⟨ fst x ∈ˢ C.col p ⟩ → Σ[ r ∈ OT.Dom ] (C.col r ≡ fst x)
      pre x mx = seg p (fst x) mx .fst , seg p (fst x) mx .snd .snd

```

<!--en-->
For the predecessor selected from `x ∈ C.col p`, the presentation equation identifies `OT.↪ r` with the ordered pair of the two coordinates represented by `φ r`. Membership in `prodL g` is therefore reduced to the two coordinate bounds; `bfst` supplies the first one.
<!--zh-->
对由 `x ∈ C.col p` 选出的前驱 `r`，呈现等式把 `OT.↪ r` 认同为 `φ r` 所表示的两个坐标组成的有序对。因此，证明它属于 `prodL g` 归结为两条坐标界；`bfst` 给出第一条。
<!--ja-->
`x ∈ C.col p` から選ばれた先行者 `r` について、提示の等式は `OT.↪ r` を、`φ r` が表す二つの座標の順序対と同一視する。したがって `prodL g` への所属は二つの座標の上界に帰着し、`bfst` が第一の上界を与える。
<!--/-->

```agda
      bound : (x : S) (mx : ⟨ fst x ∈ˢ C.col p ⟩) → ⟨ OT.↪ (pre x mx .fst) ∈ˢ fst (prodL g) ⟩
      bound x mx = subst (λ w → ⟨ w ∈ˢ fst (prodL g) ⟩) (sym (φ-eq (seg p (fst x) mx .fst)))
        (prodL-in g (upK (φ (seg p (fst x) mx .fst) .fst))
                    (upK (φ (seg p (fst x) mx .fst) .snd))
                    (bfst _ (seg p (fst x) mx .snd .fst))
```

<!--en-->
The bound `bsnd` supplies the second coordinate membership. Together the two bounds place the represented ordered pair in `g × g`, completing the required codomain proof.
<!--zh-->
`bsnd` 给出第二坐标的隶属关系。两条界合在一起，把所表示的有序对放入 `g × g`，从而完成所需的陪域证明。
<!--ja-->
`bsnd` が第二座標の所属を与える。二つの上界を合わせると、表された順序対が `g × g` に属することが分かり、必要な終域の証明が完成する。
<!--/-->

```agda
                    (bsnd _ (seg p (fst x) mx .snd .fst)))

```

<!--en-->
Consequently, collapse on the initial segment below `p` has a definable inverse into `prodL g`: each member of `C.col p` returns to its unique predecessor, and distinct collapse values return to distinct pairs. This gives an internal injection `C.colʟ p ↪ prodL g`. The main induction now aims to prove `C.col p ∈ a` for every `p`, beginning with trichotomy for its maximum coordinate.
<!--zh-->
因此，`p` 以下初始段上的塌缩具有一个到 `prodL g` 的可定义逆映射：`C.col p` 的每个成员都回到其唯一前驱，不同的塌缩值则回到不同的对。由此得到内部单射 `C.colʟ p ↪ prodL g`。主归纳现在要对每个 `p` 证明 `C.col p ∈ a`，首先对它的最大坐标应用三歧性。
<!--ja-->
したがって、`p` より下の始切片上の崩壊には `prodL g` への定義可能な逆写像がある。`C.col p` の各要素は一意な先行者へ戻り、異なる崩壊値は異なる対へ戻る。これにより、内部の単射 `C.colʟ p ↪ prodL g` が得られる。主帰納では、各 `p` について `C.col p ∈ a` を示す。まず、その最大座標に三分法を適用する。
<!--/-->

```agda
    open I.Inverse (C.colʟ p) (prodL g) pre bound public
      using ( fn; graph; at; only; M; inj; injL ) renaming ( SourceMem to Mem )
  colIn : (p : OT.Dom) → ⟨ C.col p ∈ˢ a ⟩
  colIn p = go (ord-tri (mV p) (ord↑ (mx p)) ω ω-ord)
    where
```

<!--en-->
If the maximum of the pair is finite, the collapse value is finite by the finite case, and the containment of `ω` in `a` places it inside `a`. Otherwise the maximum is infinite, and the trichotomy between the collapse value and `a` is examined.
<!--zh-->
若该对的最大值有限，则由有限情形塌缩值有限，而 `ω` 含于 `a` 使其落入 `a`。否则最大值无穷，转而检查塌缩值与 `a` 之间的三歧性。
<!--ja-->
対の最大値が有限なら、有限の場合によって崩壊の値も有限であり、`ω` が `a` に含まれることで `a` の中に入る。そうでなければ最大値は無限で、崩壊の値と `a` の三分法が検討される。
<!--/-->

```agda
    go : ⟨ mV p ∈ˢ ω ⟩ ⊎ ((mV p ≡ ω) ⊎ ⟨ ω ∈ˢ mV p ⟩) → ⟨ C.col p ∈ˢ a ⟩
    go (inl m∈ω) = ω⊆a (C.col p) (col-fin p m∈ω)
    go (inr inf) = go' (ord-tri (C.col p) (C.col-ord p) a oa)
      where
      m∉ω : ⟨ mV p ∈ˢ ω ⟩ → ⊥₀
```

<!--en-->
In the infinite branch, suppose for contradiction that `mV p ∈ ω`. If `mV p = ω`, transporting this membership gives `ω ∈ ω`. If instead `ω ∈ mV p`, transitivity of `ω` combines the two memberships to give `ω ∈ ω` again. Irreflexivity rules out both alternatives, so `mV p` is not finite.
<!--zh-->
在无穷分支中，反设 `mV p ∈ ω`。若 `mV p = ω`，沿该等式搬运此隶属关系便得到 `ω ∈ ω`；若 `ω ∈ mV p`，则 `ω` 的传递性把这两条隶属关系合成，再次得到 `ω ∈ ω`。非自反性排除两种选择，故 `mV p` 不是有限序数。
<!--ja-->
無限の場合に `mV p ∈ ω` と仮定して矛盾を導く。`mV p = ω` なら、この所属を等しさに沿って移送すると `ω ∈ ω` が得られる。一方 `ω ∈ mV p` なら、`ω` の推移性で二つの所属を合成すると、やはり `ω ∈ ω` が得られる。非反射性が両方を排除するので、`mV p` は有限順序数ではない。
<!--/-->

```agda
      m∉ω h = rr inf
        where
        rr : (mV p ≡ ω) ⊎ ⟨ ω ∈ˢ mV p ⟩ → ⊥₀
        rr (inl e)   = ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e h)
        rr (inr ω∈m) = ∈-irrefl ω (ω-ord .fst ω∈m h)
```

<!--en-->
The carrier `g` is the successor of the maximum, and is an ordinal because the maximum is a member of the ordinal `κ`; the ordinal is then packaged as an element `gL` of `L`.
<!--zh-->
载体 `g` 是最大值的后继，由于最大值是序数 `κ` 的成员，故 `g` 是序数；随后该序数被打包为 `L` 的元素 `gL`。
<!--ja-->
台 `g` は最大値の後続であり、最大値が順序数 `κ` の要素であるため `g` も順序数である。ついでこの順序数は `L` の要素 `gL` としてまとめられる。
<!--/-->

```agda

      g : V ℓ
      g = sucV (mV p)
      og : IsOrd g
      og = suc-ord (ord↑ (mx p))
      gL : S
```

<!--en-->
The carrier belongs to `a` by the successor closure proved above, and it is infinite: if `g` belonged to `ω`, then the maximum, being a member of `g`, would belong to `ω` by transitivity, contradicting the infiniteness just established.
<!--zh-->
载体由前证的后继封闭性属于 `a`，且它是无穷的：若 `g` 属于 `ω`，则作为 `g` 成员的最大值经传递性也属于 `ω`，与刚才确立的无穷性矛盾。
<!--ja-->
台は、上で証明した後続の閉性によって `a` に属し、さらに無限である。`g` が `ω` に属すれば、`g` の要素である最大値も推移性によって `ω` に属することになり、確立されたばかりの無限性と矛盾する。
<!--/-->

```agda
      gL = ordL g og
      g∈a : ⟨ g ∈ˢ a ⟩
      g∈a = suc∈ (mV p) (member K (mx p))
      g∉ω : ⟨ g ∈ˢ ω ⟩ → ⊥₀
      g∉ω h = m∉ω (ω-ord .fst (self∈sucV (mV p)) h)
```

<!--en-->
For every `r ≺ p`, the bounds `seg-fst` and `seg-snd` place both coordinates of `r` in `g = sucV (mV p)`. The inverse-collapse construction therefore gives an internal injection from `C.colʟ p` into `prodL gL`.
<!--zh-->
对每个 `r ≺ p`，界 `seg-fst` 与 `seg-snd` 都把 `r` 的两个坐标放入 `g = sucV (mV p)`。因此，逆塌缩构造给出从 `C.colʟ p` 到 `prodL gL` 的内部单射。
<!--ja-->
各 `r ≺ p` について、上界 `seg-fst` と `seg-snd` は `r` の二つの座標をとも `g = sucV (mV p)` に入れる。したがって逆崩壊の構成により、`C.colʟ p` から `prodL gL` への内部の単射が得られる。
<!--/-->

```agda

      module IV = Inv p gL (seg-fst p) (seg-snd p) using (injL)

```

<!--en-->
Compose the inverse-collapse injection with `prod-into gL` to obtain `C.colʟ p ↪ gL`. To construct the latter injection, `prod-into` first chooses an internal cardinal representative `μ` of `gL`, applies the induction hypothesis at `μ`, and transports the resulting square injection along the injections between `μ` and `gL`.
<!--zh-->
把逆塌缩单射与 `prod-into gL` 复合，便得到 `C.colʟ p ↪ gL`。后一个单射并非直接在 `gL` 处使用归纳假设：`prod-into` 先为 `gL` 选取内部基数代表 `μ`，在 `μ` 处应用归纳假设，再沿 `μ` 与 `gL` 之间的单射搬运所得的平方单射。
<!--ja-->
逆崩壊の単射と `prod-into gL` を合成すると、`C.colʟ p ↪ gL` が得られる。後者は `gL` に帰納仮定を直接適用したものではない。`prod-into` はまず `gL` の内部基数代表 `μ` を選び、`μ` で帰納仮定を適用し、`μ` と `gL` の間の単射に沿って、得られた平方の単射を移す。
<!--/-->

```agda
      col↪g : InjL (C.colʟ p) gL
      col↪g = injl-trans (C.colʟ p) (prodL gL) gL IV.injL (prod-into gL og g∈a g∉ω)
      absurd : ((z : V ℓ) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ C.col p ⟩) → ⊥₀
      absurd sub = carda gL g∈a
        (injl-trans κ (C.colʟ p) gL (inclusion-coded κ (C.colʟ p) sub) col↪g)
```

<!--en-->
If the cardinal were contained in the collapse value, composing that inclusion with the injection into `gL` would inject `κ` into its own member `gL`, contradicting the internal cardinality of `κ`. The trichotomy between the collapse value and `a` therefore leaves only direct membership.
<!--zh-->
若基数包含于塌缩值，则把该包含与到 `gL` 的单射复合，将使 `κ` 单射入其自身成员 `gL`，与 `κ` 的内部基数性矛盾。于是塌缩值与 `a` 的三歧性只剩直接隶属一种情形。
<!--ja-->
基数が崩壊の値に含まれるなら、その包含と `gL` への単射を合成することで、`κ` がみずからの要素 `gL` へ単射することになり、`κ` の内部の基数性と矛盾する。したがって崩壊の値と `a` の三分法に残るのは直接の所属だけである。
<!--/-->

```agda

      go' : ⟨ C.col p ∈ˢ a ⟩ ⊎ ((C.col p ≡ a) ⊎ ⟨ a ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ a ⟩
      go' (inl h)       = h
      go' (inr (inl e)) = ⊥₀-rec (absurd (λ z z∈a → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈a))
      go' (inr (inr h)) = ⊥₀-rec (absurd (λ z z∈a → C.col-ord p .fst z∈a h))
  result : InjL (prodL κ) κ
```

<!--en-->
The product first injects into the collapse order type `C.otL`. Every member `z` of this order type is equal to `C.col b` for some `b : OT.Dom`, and `colIn b` places that collapse value in `a`; hence `C.otL ⊆ κ`. Composing the first injection with the coded inclusion gives the required internal injection `prodL κ ↪ κ`.
<!--zh-->
乘积先单射入塌缩序型 `C.otL`。该序型的每个成员 `z` 都等于某个 `b : OT.Dom` 的 `C.col b`，而 `colIn b` 把这个塌缩值放入 `a`；因此 `C.otL ⊆ κ`。把第一个单射与这一编码包含复合，便得到所需的内部单射 `prodL κ ↪ κ`。
<!--ja-->
まず積を崩壊の順序型 `C.otL` へ単射する。この順序型の各要素 `z` は、ある `b : OT.Dom` に対する `C.col b` と等しく、`colIn b` によってその崩壊値は `a` に属する。したがって `C.otL ⊆ κ` である。最初の単射と、この符号化された包含を合成すると、必要な内部の単射 `prodL κ ↪ κ` が得られる。
<!--/-->

```agda
  result = injl-trans P C.otL κ injL-ot (inclusion-coded C.otL κ ot⊆a)
    where
    ot⊆a : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ a ⟩
    ot⊆a z hz = rec₁ (snd (z ∈ˢ a))
      (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ a ⟩) e (colIn b) }) (C.otL-out z hz)
```

<!--en-->
Membership well-founded induction now proves the square law. Given an ordinal `κ` that is an internal cardinal and satisfies `ω ∈ κ`, the induction step constructed above yields an internal injection `prodL κ ↪ κ` once the required proof that `κ` is not finite is supplied.
<!--zh-->
现在由隶属关系上的良基归纳证明平方律。给定一个作为内部基数并满足 `ω ∈ κ` 的序数 `κ`，只要补上 `κ` 不是有限序数的证明，上面构造的归纳步骤就给出内部单射 `prodL κ ↪ κ`。
<!--ja-->
これで所属関係に関する整礎帰納法から平方則が得られる。内部の基数であり `ω ∈ κ` を満たす順序数 `κ` に対し、`κ` が有限順序数ではないことを示せば、上で構成した帰納段階から内部の単射 `prodL κ ↪ κ` が得られる。
<!--/-->

```agda
square-law-L :
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩
  → InjL (prodL κ) κ
square-law-L κ oκ cκ ω∈κ =
  WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ
```

<!--en-->
Finally, `κ` cannot belong to `ω`. If it did, transitivity of the ordinal `ω` would combine `ω ∈ κ` with `κ ∈ ω` to give `ω ∈ ω`, contradicting irreflexivity. This discharges the infinitude hypothesis required by the induction step.
<!--zh-->
最后，`κ` 不可能属于 `ω`。否则，序数 `ω` 的传递性会把 `ω ∈ κ` 与 `κ ∈ ω` 合成，得到 `ω ∈ ω`，与非自反性矛盾。这就满足了归纳步骤所需的无穷性假设。
<!--ja-->
最後に、`κ` が `ω` に属することはない。もし属するなら、順序数 `ω` の推移性により `ω ∈ κ` と `κ ∈ ω` から `ω ∈ ω` が従い、非反射性に反する。これで帰納段階に必要な無限性の仮定が得られる。
<!--/-->

```agda
    (λ κ∈ω → ∈-irrefl ω (ω-ord .fst ω∈κ κ∈ω))
```
