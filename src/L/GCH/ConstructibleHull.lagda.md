```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Locating the hull and its collapse inside L
<!--zh-->
# 在 L 中定位 Skolem 壳及其塌缩
<!--ja-->
# 包とその崩壊を L の内部に置く
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ`{.Agda} and assume `lem : LEM (ℓ-suc ℓ)`{.Agda}. This hypothesis supplies a decision for each proposition at that level; it remains an explicit parameter of the constructions below.
<!--zh-->
固定宇宙层级 `ℓ`{.Agda}，并假设 `lem : LEM (ℓ-suc ℓ)`{.Agda}。这个假设为相应层级的每个命题提供判定，并始终作为下文构造的显式参数。
<!--ja-->
宇宙レベル `ℓ`{.Agda} を固定し、`lem : LEM (ℓ-suc ℓ)`{.Agda} を仮定する。この仮定は該当するレベルの各命題に判定を与え、以下の構成の明示的なパラメータとして保たれる。
<!--/-->

```agda
module L.GCH.ConstructibleHull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ⊥̇ )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Collapse {ℓ} using ( module Collapse )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-out; Lset→isL; 𝒟ₒ; 𝒟ₒ∋⊆
        ; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ; extensionalL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Recursion.Graph {ℓ} lem using () renaming ( module Graph to RecursionGraph )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; envOverAt; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( numL; sucAtL; sucAtL-adequate; consAtL; consAtL-adequate )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envS; Ix; envOver; module Recover )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( graph; envFor; envFor-graph )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; keyS; key∈AllCodes )
open import L.Coding.CodeConstructibility {ℓ} using ( cupʟ; cupʟ-inl; cupʟ-inr )
open import L.Coding.UniformSatisfaction {ℓ} lem using ( val-sat )
open import L.Choice.CanonicalNames {ℓ} lem using ( limitCode; numeral∈limit; pr∈limit )
open import L.Choice.NameComparison {ℓ} lem using ( freeCode-in; freeCode-out )
open import L.Choice.InternalWellOrder {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.Choice.StageOrders {ℓ} lem using ( orderAt; relOf )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOfFormula; isPropLeastOf )
  renaming ( Tri to Tri∙; lt to tri-lt; eq to tri-eq; gt to tri-gt )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( module Relation; isL-ord )
open import L.GCH.OrderType {ℓ} lem
  using ( Holds; Complete; Src; ValueIs; Correct
        ; completeAt; complete-in; complete-out
        ; valueAt; value-in; value-out
        ; correctAt; correct-in; correct-out )
open import L.GCH.OmegaRecursion {ℓ} lem using ( module Iterate )
open import L.GCH.SkolemHull {ℓ} lem using ( module HullStage; module Frame )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )
open import L.GCH.AdequateStages {ℓ} lem using ( Superadequate )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
open import L.GCH.CondensationTransfer {ℓ} lem using ( module Condense )
open import V.Model {ℓ} using ( pair-spec )
```

<!--en-->

The condensation argument needs more than an external hull: the hull itself and every value of its collapse must belong to L. This chapter proves these membership facts by coding the collapse and expressing the hull as an ω-iteration.
<!--zh-->

凝聚论证需要的不只是外部的 Skolem 壳：壳本身与其塌缩的每个值都必须属于 L。本章通过编码塌缩、把壳写成 ω 迭代来证明这些成员关系。
<!--ja-->

凝縮の議論には、外の包だけでは足りない。包そのものと、崩壊の各値が `L` に属する必要がある。本章は、崩壊を符号化し、包を ω 反復として表すことで、これらの所属の事実を証明する。
<!--/-->

<!--en-->
The chapter runs under classical logic: an excluded-middle instance at the successor of the model's own level. This is the same hypothesis the choice construction carries, and it is the only classical assumption made here.
<!--zh-->
本章在经典逻辑下运行：取模型自身层级后继处的排中律实例。这与选择构造所携带的假设相同，也是本章唯一的经典假设。
<!--ja-->
本章は古典論理のもとで進む。モデル自身のレベルの後続での排中律の実例を使う。これは選択の構成が帯びるのと同じ仮定であり、ここで仮定される古典的な事実はこれだけである。
<!--/-->

```agda
open import Cubical.Relation.Nullary using ( decRec )
open import Cubical.HITs.PropositionalTruncation using ( rec2 )
open import Cubical.Foundations.Prelude using ( J )
open import Cubical.Foundations.HLevels using ( isPropΠ2 )
```

<!--en-->
The module is parameterized by that hypothesis, so every statement below is relative to it rather than to an ambient principle of excluded middle.
<!--zh-->
模块以该假设为参数，因此下文每条陈述都是相对于它而言的，而不诉诸任何笼统的排中律原理。
<!--ja-->
モジュールはこの仮定をパラメータとする。したがって以下の主張はすべてそれに相対的であり、漠然とした排中律の原理に訴えるものではない。
<!--/-->

<!--en-->
The chapter speaks the first-order language of set theory: formulas are built over the carrier of the constructible structure, their constants name elements of `L`, and constants can be relabeled along any map, with satisfaction invariant under such relabeling. This is the vocabulary in which the collapse and the hull will be described.
<!--zh-->
本章使用集合论的一阶语言：公式构筑于可构造结构的载体之上，其常元指名 `L` 的元素，且常元可沿任意映射改名，满足关系在改名下不变。这正是描述塌缩与壳所用的词汇。
<!--ja-->
本章は集合論の一階言語で語る。論理式は構成可能な構造の台の上で組み立てられ、その定数は `L` の要素を名指す。定数は任意の対応に沿って改名でき、充足は改名で変わる。これが、崩壊と包を記述するための語彙である。
<!--/-->

<!--en-->
Formula readings move between environments by renaming, and renaming is harmless for satisfaction. The ambient hierarchy contributes the background facts: induction along membership, extensionality of sets, and the presentation of an element as an index together with its membership proof.
<!--zh-->
公式的读法经改名在环境间移动，而改名对满足无害。环境层级提供背景事实：沿隶属的归纳、集合的外延性，以及「元素=索引连同其隶属证明」的呈现方式。
<!--ja-->
論理式の読みは、改名によって環境の間を移動する。改名は充足にとって無害である。周囲の階層は、所属に沿う帰納、集合の外延性、そして「要素＝添字とその所属の証明」という提示の仕方という、背景の事実を供給する。
<!--/-->

<!--en-->
The argument begins where every set of `L` lives: in the tower of stages indexed by ordinals. The collapse of a set is computed from its members alone, and constructibility travels along membership; what must be shown is that this local computation never leaves `L`. Since a hull is not transitive, the argument cannot invoke global facts about the collapse; it re-derives, stage by stage, that the values stay inside.
<!--zh-->
论证从 `L` 中每个集合的居所开始：以序数为索引的层之塔。一个集合的塌缩只由其成员算出，而可构造性沿隶属传递；有待证明的是这场局部计算从不离开 `L`。由于壳不传递，论证无法援引关于塌缩的全局事实，而必须逐层重新推得取值留在内部。
<!--ja-->
議論は、`L` のすべての集合の住む場所からはじまる。順序数で添字づけられた段階の塔である。集合の崩壊はその要素だけから計算され、構成可能性は所属に沿って伝わる。示すべきは、この局所的な計算が `L` の外に出ないことである。包は推移的ではないので、議論は崩壊についての大域的な事実を使えず、段階ごとに、値が内側にとどまることを改めて導く。
<!--/-->

<!--en-->
The constructible set `ωʟ` represents the ambient `ω`, and its specification identifies its members with the internal numerals. Separation will carve the bounded slices and one-step closures used later. In both operations the result is an element of `L` again, which is what keeps the whole construction inside the universe it describes.
<!--zh-->
可构造集合 `ωʟ` 表示周遭的 `ω`，其规格把它的成员认作内部数码。后文用分离刻出有界切片与单步闭包。这两种运算的结果都仍是 `L` 的元素，这正是使整个构造留在它所描述的宇宙之内的原因。
<!--ja-->
構成可能集合 `ωʟ` は周囲の `ω` を表し、その仕様は要素を内部の数項と同定する。後では分出によって有界な切片と一段階の閉包を切り出す。どちらの演算も、結果が再び `L` の要素である。それが、構成全体を、その記述対象の宇宙の内側に保つのである。
<!--/-->

<!--en-->
Replacement assembles values into tables: a recursion whose graph is definable becomes an element of `L`, and it suffices that a unique value merely exists at each argument. Definability interprets the constants of formulas, and the model-side coding of pairs and numerals provides the entries and their names.
<!--zh-->
替换把取值装配成表：图可定义的递归成为 `L` 的元素，而只须每个实参处「仅仅存在」唯一取值。可定义性解释公式的常元；模型内侧的对与数码编码供给条目及其名字。
<!--ja-->
置換が値を表へ集める。グラフが定義可能な再帰は `L` の要素となり、各入力で一意な値が「単に存在する」だけで十分である。定義可能性が論理式の定数を解釈し、モデル側の対と数項の符号化が、項目とその名前を供給する。
<!--/-->

<!--en-->
Environments code parameter vectors as single sets, from which the vectors are recovered; the satisfaction bridge reads internal satisfaction externally; the code set gathers all codes into one element of `L`; and constructible unions combine the pieces that the construction collects along the way.
<!--zh-->
环境把参数向量编码为单个集合，向量又可从中恢复；满足桥把内部满足向外部读取；码集把所有码收集为 `L` 的一个元素；可构造并则把构造沿途收集的各部分合并起来。
<!--ja-->
環境はパラメータのベクトルを一つの集合として符号化し、ベクトルはそこから復元される。充足の橋は内部の充足を外側で読み、符号の集合がすべての符号を `L` の一つの要素に集め、構成可能な合併が、構成が途中で集めた部分を結合する。
<!--/-->

<!--en-->
The uniform satisfaction table assigns to every code its satisfaction set, read externally; the canonical-names construction places numerals and the codes of parameter-free formulas, which may still have free-variable slots, in `Lset ω`; the internal well-order of a stage compares its members, first by birth stage and then by name.
<!--zh-->
一致满足表为每条码指派其满足集，并向外部读取；典范名构造把数码以及无常元公式的码放入 `Lset ω`，无常元公式仍可带有自由变元槽；某层的内部良序比较其成员，先按诞生层、再按名字。
<!--ja-->
一様な充足の表は、すべての符号にその充足集合を割り当て、外側で読める。正準名の構成は、数項と、定数を持たない論理式のコードを `Lset ω` に置く。そのような論理式にも自由変数の枠は残りえる。段階の内部の整列順序は要素を、まず誕生の段階、つぎに名前で比較する。
<!--/-->

<!--en-->
Least-element search over a strict well-order returns, from an inhabited family, the least element; relations themselves become sets of pairs with two readings, and the order-type chapter states the three predicates describing a collapse table.
<!--zh-->
严格良序上的最小元搜索，从有居留者的族返回最小元；关系自身成为带有两条读式的对之集，而序型章陈述描述塌缩表的三条谓词。
<!--ja-->
狭義の整列順序の上の最小元の探索は、住民のある族から最小元を返す。関係そのものも、二つの読みをもつ対の集合になり、順序型の章が、崩壊の表を記述する三つの述語を述べる。
<!--/-->

<!--en-->
Correctness, completeness at an argument, and the value clause are each a formula with its two satisfaction readings; internal ω-recursion iterates a definable two-place step along the model's own `ω`. The hull's members are named by codes of arbitrary nesting depth, so no single separation can produce the hull; it is reached by iterating a definable one-step closure along `ω`, and this is why the closure must be built ω times.
<!--zh-->
正确性、在实参处的完备性、以及取值子句，各自都是带两条满足读式的公式；内部 ω 递归沿模型自身的 `ω` 迭代一个可定义的二元步进。壳的成员由任意嵌套深度的码名指，因此任何一次分离都造不出壳；只能沿 `ω` 迭代一个可定义的单步闭包抵达它，这正是闭包必须构建 ω 次的原因。
<!--ja-->
正しさ、入力での完備さ、値の条項は、それぞれ二つの充足の読みをもつ論理式である。内部 ω 再帰は、モデル自身の `ω` に沿って、定義可能な二項のステップを反復する。包の要素は、任意の入れ子の深さの符号に名指されるので、一度の分離で包を作ることはできない。`ω` に沿って、定義可能な一段階の閉包を反復することではじめて届く。閉包を ω 回作らねばならない理由はこれである。
<!--/-->

<!--en-->
The proof has two connected parts. First, a local collapse table shows that each collapse value of a constructible carrier is constructible. Second, the Skolem hull is realized as the union of its finite closure stages, making the carrier itself constructible and allowing the first argument to apply to it.
<!--zh-->
证明分为彼此衔接的两部分。首先，局部塌缩表证明可构造载体的每个塌缩值仍可构造。其次，把 Skolem 壳实现为各有限闭包层的并，从而证明载体本身可构造，并可对它应用第一部分。
<!--ja-->
証明は結びついた二つの部分からなる。まず局所的な崩壊表により、構成可能な台の各崩壊値が構成可能であることを示す。次に Skolem 包を有限閉包段階の合併として実現し、台自身の構成可能性を得て、第一の議論を適用する。
<!--/-->

<!--en-->
A nested hull code has a finite depth, computed by taking maxima over the depths of its parameter codes. This depth bounds the closure stage at which its value appears.
<!--zh-->
嵌套壳码具有有限深度，其深度由各参数码深度的最大值计算。这个深度给出该码取值出现时所需闭包层的上界。
<!--ja-->
入れ子になった包の符号には有限の深さがあり、パラメータ符号の深さの最大値から計算される。この深さが、その値の現れる閉包段階を上から評価する。
<!--/-->

```agda
open import Cubical.Data.Nat.Properties using ( max )
open import Cubical.Data.Nat.Order using ( _≤_; left-≤-max; right-≤-max )
```

<!--en-->
Finite parameter vectors let one witness code depend on finitely many earlier values. Empty sets, singletons and unordered pairs provide the set codes needed to represent those parameters and their ordered pairs inside the hierarchy.
<!--zh-->
有限参数向量使一个见证码能够依赖有限多个较早取值。空集、单点集与无序二元集提供集合编码，使这些参数及其有序对可在层级内部表示。
<!--ja-->
有限パラメータベクトルにより、一つの証人符号は有限個の先行する値に依存できる。空集合、単集合、非順序対から、これらのパラメータとその順序対を階層内で表す集合符号を作れる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
```

<!--en-->
The von Neumann successor and numerals organize the finite closure stages inside `ω`. Unordered pairs also supply the ingredients from which the ordered pairs used in graphs and environments are encoded.
<!--zh-->
冯·诺伊曼后继与数码把有限闭包层组织在 `ω` 内。无序对还提供构造有序对的原料，而图与环境正以这些有序对编码。
<!--ja-->
フォン・ノイマンの後者と数項により、有限閉包段階を `ω` の内部で整理する。非順序対は、グラフと環境に使う順序対を符号化する材料にもなる。
<!--/-->

```agda
open InfinitySet {ℓ} using ( ω; sucV; #_ )
```

<!--en-->
Existence statements are kept propositionally truncated until their witnesses are needed only to prove another proposition. Equalities in the cumulative hierarchy are propositions, so the collapse argument can eliminate such truncated data when proving its set equalities.
<!--zh-->
存在陈述保持命题截断，直到其见证只用于证明另一命题时才予消去。累积层级中的等式是命题，因此塌缩论证在证明集合等式时可以消去这类截断数据。
<!--ja-->
存在の主張は、その証人を別の命題の証明にだけ使う段階まで命題的切断のまま保つ。累積階層の等式は命題なので、崩壊の議論では集合の等式を示す際にこの切断されたデータを除去できる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
```

<!--en-->
Two levels of membership must be distinguished. Ambient membership belongs to the cumulative hierarchy, whereas an element of the constructible carrier packages an ambient set together with a proof of constructibility; carrier membership is read through those underlying sets.
<!--zh-->
这里须区分两层隶属。外围隶属属于累积层级；可构造载体的元素则把外围集合与其可构造性证明打包，而载体上的隶属通过底层集合读取。
<!--ja-->
二つの所属を区別する必要がある。外側の所属は累積階層の関係である。一方、構成可能な台の要素は外側の集合とその構成可能性の証明を組にし、台上の所属はその基底集合を通して読まれる。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
```

<!--en-->
For formulas whose constants are elements of `L`, `⊨` denotes satisfaction in the class model of `L`. Relabeling constants by the identity map leaves both the environment and satisfaction unchanged.
<!--zh-->
对于常元为 `L` 元素的公式，`⊨` 表示在 `L` 的类模型中的满足。沿恒等映射重标常元既不改变环境，也不改变满足关系。
<!--ja-->
定数が `L` の要素である論理式について、`⊨` は `L` のクラスモデルでの充足を表す。恒等写像による定数の付け替えは、環境も充足も変えない。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
module Ren = Sat 𝒮ʟ id using ( Agrees; ⊨-rename )
```

<!--en-->
Seven names, `i0` through `i6`, abbreviate the first seven de Bruijn indices, one per slot of a long environment.
<!--zh-->
`i0` 至 `i6` 共七个名字，缩写前七个 de Bruijn 索引，长环境的每个槽位一个。
<!--ja-->
`i0` から `i6` までの七つの名前が、最初の七つの de Bruijn 添字を略記する。長い環境の枠ごとに一つである。
<!--/-->

```agda
private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
```

<!--en-->
Each successor shifts the preceding index into a larger finite type; the names continue slot by slot.
<!--zh-->
每个后继索引把前一个索引移入更大的有限类型；这些名字逐槽延续。
<!--ja-->
各後続添字は直前の添字をより大きな有限型へ移す。名前は枠ごとに続く。
<!--/-->

```agda
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
```

<!--en-->
These are free-variable positions, whose interpretation changes as later binders extend the environment.
<!--zh-->
它们表示自由变元位置，后续约束子扩张环境时，其读法随之移动。
<!--ja-->
これらは自由変数の位置であり、後の束縛子が環境を拡張すると読み方が移動する。
<!--/-->

```agda
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5
```

<!--en-->
An element of the carrier is determined by its underlying set, because constructibility is a proposition: two carrier elements with equal underlying sets are equal, and the helper `S≡`{.Agda} makes that identification wherever a carrier element is rebuilt from the same underlying set.
<!--zh-->
载体的元素由其底层集合决定，因为可构造性是命题：底层集合相等的两个载体元素相等。凡从同一底层集合重建载体元素之处，辅助 `S≡`{.Agda} 都作出这一认同。
<!--ja-->
台の要素はその基礎の集合で決まる。構成可能性が命題だからである。基礎の集合が等しい台の要素は等しく、補助 `S≡`{.Agda} が、同じ基礎の集合から台の要素を組み立て直す場所で、その同定を行う。
<!--/-->

```agda
  S≡ : {x y : CS.S} → fst x ≡ fst y → x ≡ y
  S≡ = Σ≡Prop (λ v → snd (isL v))
```

<!--en-->
The renaming `ρs` swaps the two slots: a formula about a pair in the swapped order is read in the original order. It is used when the step formula is proved in one slot order and consumed in the other.
<!--zh-->
改名 `ρs` 交换两个槽位：以交换次序书写的关于某对的公式，可在原次序下读取。当步进公式按一种槽序证明、按另一种槽序使用时，就用到它。
<!--ja-->
改名 `ρs` は二つの枠を入れ替える。入れ替えた順で書かれた、ある対についての論理式を、元の順で読むためのものである。ステップの論理式を一方の枠の順で証明し、別の順で使うときに使われる。
<!--/-->

```agda
  ρs : Fin 2 → Fin 2
  ρs zero = suc zero
  ρs (suc zero) = zero
```

<!--en-->
The renaming `ρf` keeps `w` in slot zero and sends `Z` from slot one to slot two, skipping the middle slot occupied by the candidate next stage `Z'`.
<!--zh-->
改名 `ρf` 保持 `w` 位于第零槽，并把 `Z` 从第一槽移到第二槽，越过由候选下一阶段 `Z'` 占据的中间槽。
<!--ja-->
改名 `ρf` は `w` を第零スロットに保ち、`Z` を第一スロットから第二スロットへ送り、次段階の候補 `Z'` が占める中央のスロットを飛ばす。
<!--/-->

```agda
  ρf : Fin 2 → Fin 3
  ρf zero = zero
  ρf (suc zero) = suc (suc zero)
```

<!--en-->
An agreement for `ρs` says that the swapped environment carries the same elements as the original at the moved slots. Both cases are proved by reflexivity, since each slot is sent to the position of the very same element.
<!--zh-->
`ρs` 的相合说：交换后的环境在被移动的槽处载有与原环境相同的元素。两个情形都可由自反性证明，因为每个槽都被送到同一元素所在的位置。
<!--ja-->
`ρs` の一致は、入れ替えた環境が、動いた枠で元の環境と同じ要素を載せていると言う。どちらの場合も反射性で証明できる。各枠が、同じ要素のある位置へ送られるからである。
<!--/-->

```agda
  ags : (Z'' w : CS.S) → Ren.Agrees ρs (Z'' ∷ w ∷ []) (w ∷ Z'' ∷ [])
  ags Z'' w zero = refl
  ags Z'' w (suc zero) = refl
```

<!--en-->
Fix an arbitrary constructible carrier `M`.
<!--zh-->
固定任意可构造载体 `M`。
<!--ja-->
任意の構成可能な台 `M` を固定する。
<!--/-->

```agda
  agf : (w Z' Z : CS.S) → Ren.Agrees ρf (w ∷ Z' ∷ Z ∷ []) (w ∷ Z ∷ [])
  agf w Z' Z zero = refl
  agf w Z' Z (suc zero) = refl
```

<!--en-->
## The collapse of a constructible carrier stays in L
<!--zh-->
## 可构造载体的塌缩仍在 L 中
<!--ja-->
## 構成可能な台の崩壊は L にとどまる
<!--/-->

<!--en-->
The collapse argument uses only the constructibility of `M` and the predecessors that remain inside it; no transitivity assumption is imposed.
<!--zh-->
塌缩论证只使用 `M` 的可构造性以及仍位于其中的前驱，不要求 `M` 传递。
<!--ja-->
崩壊の議論が使うのは `M` の構成可能性と、その内部に残る先行者だけであり、推移性は仮定しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module PiIn (Mʟ : CS.S) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Let `M` be the underlying set of the chosen constructible carrier. Its accompanying certificate ensures that every member later lifted from `M` is constructible.
<!--zh-->
令 `M` 为所选可构造载体的底层集合。随附的证书保证，此后从 `M` 提升出的每个成员都是可构造的。
<!--ja-->
選んだ構成可能な台の基底集合を `M` とする。付随する証明により、後に `M` から持ち上げる各要素が構成可能であることが保証される。
<!--/-->

```agda
  M : S
  M = fst Mʟ
```

<!--en-->
The collapse `π x` is formed from the collapse values of those members of `x` that also lie in `M`; `πX` collects the values `π x` for `x ∈ M`. This restricted predecessor relation makes the definition meaningful without assuming that `M` is transitive.
<!--zh-->
`π x` 由 `x` 的成员中同时属于 `M` 者的塌缩值组成；`πX` 收集所有 `x ∈ M` 的取值 `π x`。这种受限的前驱关系使定义无须假设 `M` 传递。
<!--ja-->
`π x` は、`x` の要素のうち `M` にも属するものの崩壊値から作られ、`πX` は `x ∈ M` に対する値 `π x` を集める。この制限された先行者関係により、`M` の推移性を仮定せずに定義できる。
<!--/-->

```agda
  module C = Collapse M using ( Fiber; π; π-compute; πX; πX-member; π∈-fwd )
```

<!--en-->
Since constructibility is inherited by members, every `y ∈ M` is constructible. Hence such a `y` can be paired with that proof and treated as an element of the constructible carrier.
<!--zh-->
可构造性向成员传递，所以每个 `y ∈ M` 都可构造。因此可把 `y` 与该证明配对，视为可构造载体的元素。
<!--ja-->
構成可能性は要素へ受け継がれるので、各 `y ∈ M` は構成可能である。したがって `y` をその証明と組にし、構成可能な台の要素として扱える。
<!--/-->

```agda
  memL : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL y ⟩
  memL y y∈M = isL-trans {x = M} {y = y} y∈M (snd Mʟ)
```

<!--en-->
The lifting `up` packages a member as a carrier element. The first lemma reads the collapse value outward: every member of `π x` is the collapse of a member of `x` that lies in `M`, which follows from the computation clause of the collapse, the identity `π x` equals the image of the collapse over the members of `x` inside `M`.
<!--zh-->
提升 `up` 把成员打包为载体元素。第一条引理向外读取塌缩值：`π x` 的每个成员都是 `x` 的某个属于 `M` 的成员的塌缩，其依据是塌缩的计算子句，即恒等式「`π x` 等于 `x` 在 `M` 内成员上的塌缩像」。
<!--ja-->
持ち上げ `up` は、要素を台の要素としてまとめる。最初の補題は、崩壊値を外向きに読む。`π x` の要素はどれも、`x` の、`M` に属する要素の崩壊である。これは崩壊の計算の条項、すなわち「`π x` は `x` の `M` の中の要素の上の崩壊の像に等しい」という恒等式から従う。
<!--/-->

```agda
  up : (y : S) → ⟨ y ∈ˢ M ⟩ → CS.S
  up y y∈M = y , memL y y∈M
  π-mem-out : (x w : S) → ⟨ w ∈ˢ C.π x ⟩
            → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) ∥₁
  π-mem-out x w w∈ = map₁ mk (subst (λ u → ⟨ w ∈ˢ u ⟩) (C.π-compute x) w∈)
```

<!--en-->
The conversion turns the collapse's own fibre witness into the member statement: the fibre pairs a presented index with the proof that the collapse of the presented element equals `w`, and the presented element is a member of `x` whose collapse is taken.
<!--zh-->
该转换把塌缩自身的纤维见证变成成员陈述：纤维把被呈现的索引与「被呈现元素的塌缩等于 `w`」的证明配对，而被呈现的元素正是被取塌缩的 `x` 的成员。
<!--ja-->
この変換は、崩壊自身のファイバーの証人を、要素についての主張へ変える。ファイバーは、提示された添字と、「提示された要素の崩壊が `w` に等しい」証明を組にする。提示された要素は、崩壊が取られる `x` の要素である。
<!--/-->

```agda
    where
    mk : Σ[ p ∈ C.Fiber x ] (C.π (⟪ x ⟫↪ (p .fst)) ≡ w)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( member x (p .fst)
```

<!--en-->
The membership relation of `M` is expressed using three free-variable slots, read by `Relation` at the environment `y ∷ x ∷ e ∷ []`; the third slot carries the coded pair, while the formula asserts `y ∈ M`, `x ∈ M`, and `y ∈ x`.
<!--zh-->
`M` 的隶属关系使用三个自由变元槽，并由 `Relation` 在环境 `y ∷ x ∷ e ∷ []` 下读取；第三槽携带编码对，而公式断言 `y ∈ M`、`x ∈ M` 与 `y ∈ x`。
<!--ja-->
`M` の所属関係は三つの自由変数スロットで表され、`Relation` により環境 `y ∷ x ∷ e ∷ []` で読まれる。第三スロットは符号化された対を載せ、論理式は `y ∈ M`、`x ∈ M`、`y ∈ x` を主張する。
<!--/-->

```agda
                 , ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = M} .snd (p .snd)
                 , q )
  private module Membership = Relation Mʟ Mʟ
            ((var i1 ∈̇ con Mʟ) ∧̇ ((var i0 ∈̇ con Mʟ) ∧̇ (var i1 ∈̇ var i0)))
```

<!--en-->
The host-side reading of the relation is exactly the three memberships, conjoined; this is the adequacy that lets the object-language formula and the external statement stand for each other.
<!--zh-->
关系的宿主侧读法恰是三条隶属的合取；正是这种充分性使对象语言公式与外部陈述可以互相代表。
<!--ja-->
関係のホスト側の読みは、三つの所属の連言そのものである。この妥当性があるから、対象言語の論理式と外側の主張は互いに代わり合える。
<!--/-->

```agda
            (λ y x → (fst y ∈ˢ M) ⊓ ((fst x ∈ˢ M) ⊓ (fst y ∈ˢ fst x)))
            (λ y x z h → h) (λ y x z h → h)
```

<!--en-->
The relation becomes an element of the model: a set of pairs of carrier elements, introduced and eliminated by the two readings. Because the relation is bounded by the carrier, the pair set is small enough to be carved out by separation.
<!--zh-->
关系成为模型的元素：一个由载体元素之对组成的集合，由两条读式引入与消去。由于关系以载体为界，这个对集足够小，可用分离切出。
<!--ja-->
関係はモデルの要素になる。台の要素の対からなる集合で、二つの読み出しによって導入と消去ができる。関係が台で界されているので、対の集合は分離で切り出せるほど小さいのである。
<!--/-->

```agda
  R : CS.S
  R = Membership.rel
```

<!--en-->
The introduction reading exhibits both endpoint memberships and the membership between them, which is the content of the relation at the pair.
<!--zh-->
引入读式出示两端点的隶属及二者之间的隶属，这正是该关系在此对上的内容。
<!--ja-->
導入の読み出しは、両端の所属と、その間の所属を示す。それがこの対での関係の内容である。
<!--/-->

```agda
  R-in : (y x : CS.S) → ⟨ fst y ∈ˢ M ⟩ → ⟨ fst x ∈ˢ M ⟩ → ⟨ fst y ∈ˢ fst x ⟩
       → Holds R y x
  R-in y x my mx yx = Membership.into y x my mx (my , mx , yx)
```

<!--en-->
The elimination reading returns the same three memberships; the two directions together say the relation is adequate, neither stronger nor weaker than the host-side statement.
<!--zh-->
消去读式返回同样的三个隶属；两个方向合起来说明该关系是充分的，既不强于也不弱于宿主侧陈述。
<!--ja-->
消去の読み出しは、同じ三つの所属を返す。二方向合わせて、この関係が妥当であること、ホスト側の主張よりも強くも弱くもないことが分かる。
<!--/-->

```agda
  R-out : (y x : CS.S) → Holds R y x
        → ⟨ fst y ∈ˢ M ⟩ × ⟨ fst x ∈ˢ M ⟩ × ⟨ fst y ∈ˢ fst x ⟩
  R-out = Membership.pair-out
```

<!--en-->
The collapse formula is local, not global. At slots for a value and an argument it says: there merely exists a table `F` correct for the relation `R`, complete at the argument, whose value at the argument is the given value. No single global function graph is claimed; at each argument only the existence of such a table is asserted, which is what lets the formula hold over a non-transitive carrier.
<!--zh-->
塌缩公式作用于一个取值与一个实参，它是局部的而非全局的。它说：仅存在一张对关系 `R` 正确、在该实参处完备、且在该实参处取给定值的表 `F`。它不声称任何全局的函数图；在每个实参处只断言这样的表存在，这正是该公式能在非传递载体上成立的原因。
<!--ja-->
崩壊の論理式は、値と実引数の枠の上に立ち、大域的ではなく局所的である。こう言う。関係 `R` に対して正しく、実引数で完備であり、そこでの値が与えられた値であるような表 `F` が、単に存在する、と。一つの大域的な関数のグラフを主張するのではなく、各実引数でそのような表の存在だけを述べるのである。だからこの論理式は、推移的でない台の上でも成立する。
<!--/-->

```agda
  opaque
    piFo : Formula CS.S 2
    piFo = ∃̇ ( correctAt i0 R
             ∧̇ ( completeAt i0 R i2 ∧̇ valueAt i0 R i2 i1 ) )
```

<!--en-->
The outward reading of the formula unpacks the satisfaction into the three components: the correct table, its completeness at the argument, and the value clause, each transported out of its binder by the order-type chapter's own projections.
<!--zh-->
公式的向外读法把满足拆成三个分量：正确的表、它在实参处的完备性、以及取值子句；每个合取项都由序型章自身的投影从约束子中运出。
<!--ja-->
論理式の外向きの読み出しは、充足を三つの成分にほどく。正しい表、実引数での完備さ、値の条項である。それぞれの連言項が、順序型の章自身の射影によって束縛子の外へ運ばれる。
<!--/-->

```agda
    piFo-out : (v p : CS.S) → ⟨ (v ∷ p ∷ []) ⊨ piFo ⟩
             → ∥ Σ[ F ∈ CS.S ] (Correct F R × (Complete F R p × ValueIs F R p v)) ∥₁
    piFo-out v p = map₁ (λ { (F , (hc , (hm , hv))) → F
      , ( correct-out i0 R (F ∷ v ∷ p ∷ []) hc
        , ( complete-out i0 R i2 (F ∷ v ∷ p ∷ []) hm
```

<!--en-->
The innermost projection finishes the unpacking: the value clause arrives as an ordinary statement about the table's entry at the argument.
<!--zh-->
最内层的投影完成拆包：取值子句作为关于「表在实参处的条目」的普通陈述抵达。
<!--ja-->
最も内側の射影がほどきを終える。値の条項は、実引数での表の項目についての通常の主張として届く。
<!--/-->

```agda
          , value-out i0 R i2 i1 (F ∷ v ∷ p ∷ []) hv ) ) })
```

<!--en-->
The inward reading chooses the table `F` for the existential quantifier and supplies proofs of its correctness, completeness at the argument, and value clause. Together with the outward reading, this identifies the formula exactly with its intended content.
<!--zh-->
向内读法为存在量词选取表 `F`，并给出其正确性、在实参处的完备性及取值子句的证明。结合向外读法，该公式便与其预期内容精确对应。
<!--ja-->
内向きの読みでは、存在量化の証人として表 `F` を選び、その正しさ、入力での完全性、値の条項の証明を与える。外向きの読みと合わせると、この論理式は意図した内容と正確に対応する。
<!--/-->

```agda
    piFo-in : (v p F : CS.S) → Correct F R → Complete F R p → ValueIs F R p v
            → ⟨ (v ∷ p ∷ []) ⊨ piFo ⟩
    piFo-in v p F hc hm hv = ∣ F
      , ( correct-in i0 R (F ∷ v ∷ p ∷ []) hc
        , ( complete-in i0 R i2 (F ∷ v ∷ p ∷ []) hm
```

<!--en-->
Uniqueness is proved by one membership induction. The motive says: at every constructible member `x` of the carrier, any table correct for the relation and complete at `x` assigns the collapse of `x` as its value. Both the constructibility and the membership travel with the motive, because the table's entries are pairs of carrier elements.
<!--zh-->
唯一性由一次隶属归纳证明。动机说：对载体的每个可构造成员 `x`，凡对该关系正确、且在 `x` 处完备的表，其取值必是 `x` 的塌缩。可构造性与隶属都随动机同行，因为表的条目是载体元素组成的对。
<!--ja-->
一意性は、所属に沿う帰納が一回で証明する。動機はこう言う。台の構成可能な要素 `x` のそれぞれで、その関係に対して正しく `x` で完備な表は、`x` の崩壊を値として割り当てる、と。構成可能性も所属も、表の項目が台の要素の対であるために、動機とともに運ばれる。
<!--/-->

```agda
          , value-in i0 R i2 i1 (F ∷ v ∷ p ∷ []) hv ) ) ∣₁
  private
    Pv : CS.S → S → Type (ℓ-suc ℓ)
    Pv F x = (xL : ⟨ isL x ⟩) → ⟨ x ∈ˢ M ⟩ → (v : CS.S)
           → Complete F R (x , xL) → ValueIs F R (x , xL) v → fst v ≡ C.π x
```

<!--en-->
The induction runs along membership in the ambient hierarchy, exactly as the collapse itself is defined along it: to prove the motive at `x`, prove it at every member of `x`.
<!--zh-->
归纳沿环境层级的隶属运行，与塌缩自身的定义方式一致：要证 `x` 处的动机，就证 `x` 的每个成员处的动机。
<!--ja-->
帰納は、周囲の階層の所属に沿って走る。崩壊そのものがそうやって定義されているからである。`x` での動機を証明するには、`x` のすべての要素での動機を証明する。
<!--/-->

```agda
  value-val′ : (F : CS.S) → Correct F R → (x : S) → Pv F x
  value-val′ F hc = ∈-induction {P = Pv F} go
    where
    go : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → Pv F y) → Pv F x
    go x IH xL x∈M v cmp val =
```

<!--en-->
The step compares members: the recorded value and the collapse have the same members, and extensionality of the ambient hierarchy turns that into equality. The argument is presented as a carrier element, so its entries may be typed over the carrier.
<!--zh-->
步进比较成员：被记录取值与塌缩有相同的成员，而环境层级的外延性把这一点变成相等。实参被呈现为载体元素，故其条目可以载体为类型。
<!--ja-->
ステップは要素を比較する。記録された値と崩壊は同じ要素をもち、周囲の階層の外延性がそれを等しさへ変える。入力は台の要素として提示されるので、その項目は台の上で型づけられる。
<!--/-->

```agda
      extensionalV {a = fst v} {b = C.π x} (λ w → ⇔toPath (fwd w) (bwd w))
      where
      xS : CS.S
      xS = x , xL
```

<!--en-->
Forward: a member `w` of the recorded value is carried, and the value clause produces a relation entry together with a table entry at it. The carrying packages `w` with the constructibility inherited from the recorded value.
<!--zh-->
向前：被记录取值的成员 `w` 被载入，取值子句产出一条关系条目及其处的表条目。载入时把从被记录取值承袭来的可构造性与 `w` 打包。
<!--ja-->
前向き：記録された値の要素 `w` を台に載せ、値の条項が、関係の項目と、そこの表の項目を作る。載せるとき、記録された値から受け継いだ構成可能性を `w` とともに包む。
<!--/-->

```agda
      fwd : (w : S) → ⟨ w ∈ˢ fst v ⟩ → ⟨ w ∈ˢ C.π x ⟩
      fwd w w∈ = rec₁ (snd (w ∈ˢ C.π x)) read (val wS .fst w∈)
        where
        wS : CS.S
        wS = w , isL-trans {x = fst v} {y = w} w∈ (snd v)
```

<!--en-->
The source witness separates into a relation fact `ry` and a table entry `fy`. Reading `ry` yields `y ∈ M` and `y ∈ x`; the induction hypothesis applied to `fy` identifies `w` with `π y`, and `π∈-fwd` then places `w` in `π x`.
<!--zh-->
来源见证分成关系事实 `ry` 与表项 `fy`。读取 `ry` 得到 `y ∈ M` 与 `y ∈ x`；把归纳假设用于 `fy`，便把 `w` 认同为 `π y`，而 `π∈-fwd` 随后把 `w` 放入 `π x`。
<!--ja-->
源の証人は関係の事実 `ry` と表の項目 `fy` に分かれる。`ry` から `y ∈ M` と `y ∈ x` を読み、`fy` に帰納法の仮定を適用して `w` を `π y` と同定し、`π∈-fwd` によって `w` を `π x` に入れる。
<!--/-->

```agda
        read : Σ[ y ∈ CS.S ] (Holds R y xS × Holds F y wS) → ⟨ w ∈ˢ C.π x ⟩
        read (y , (ry , fy)) =
          subst (λ t → ⟨ t ∈ˢ C.π x ⟩) e (C.π∈-fwd x (fst y) y∈x y∈M)
          where
          y∈M : ⟨ fst y ∈ˢ M ⟩
```

<!--en-->
The relation entry also says the component lies in the argument, which unlocks the induction hypothesis: the table's value at that component equals the collapse of the component. This equation, composed with the collapse reading, is the identification of `w`.
<!--zh-->
关系条目还说该分量低于实参，这就解锁了归纳假设：表在该分量处的取值等于该分量的塌缩。把这条等式与塌缩读法复合，即完成对 `w` 的认同。
<!--ja-->
関係の項目はさらに、その成分が入力の下にあるとも言い、これが帰納の仮定を解き放つ。その成分での表の値は成分の崩壊に等しい、と。この等式を崩壊の読み出しと合成すれば、`w` の同定が終わる。
<!--/-->

```agda
          y∈M = R-out y xS ry .fst
          y∈x : ⟨ fst y ∈ˢ x ⟩
          y∈x = R-out y xS ry .snd .snd
          e : C.π (fst y) ≡ w
          e = sym (IH (fst y) y∈x (snd y) y∈M wS (hc y wS fy .fst) (hc y wS fy .snd))
```

<!--en-->
Backward: a member `w` of the collapse decomposes, by the outward reading already proved, into a component of the argument inside the carrier whose collapse is `w`. Completeness at the original argument `x`, applied to the predecessor `y`, supplies an entry `(y,u)`.
<!--zh-->
向后：塌缩的成员 `w` 由已证的向外读法分解为载体中实参的某分量，其塌缩为 `w`。把表在原实参 `x` 处的完备性用于前驱 `y`，得到表项 `(y,u)`。
<!--ja-->
後ろ向き：崩壊の要素 `w` は、すでに証明した外向きの読みによって、台の中の入力の成分へと分解され、その成分の崩壊が `w` になる。元の実引数 `x` における表の完備さを前者 `y` に適用すると、項目 `(y,u)` が得られる。
<!--/-->

```agda
      bwd : (w : S) → ⟨ w ∈ˢ C.π x ⟩ → ⟨ w ∈ˢ fst v ⟩
      bwd w w∈ = rec₁ (snd (w ∈ˢ fst v)) read (π-mem-out x w w∈)
        where
        read : Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) → ⟨ w ∈ˢ fst v ⟩
        read (y , (y∈x , y∈M , e)) = rec₁ (snd (w ∈ˢ fst v)) inner (cmp yS ry)
```

<!--en-->
The component is carried as a carrier element, and the relation entry at the pair is reintroduced from the two memberships and the membership between them.
<!--zh-->
该分量被载为载体元素，而该对处的关系条目由两个隶属与二者之间的隶属重新引入。
<!--ja-->
その成分は台の要素として載せられ、対での関係の項目が、二つの所属とその間の所属から改めて導入される。
<!--/-->

```agda
          where
          yS : CS.S
          yS = up y y∈M
          ry : Holds R yS xS
          ry = R-in yS xS y∈M x∈M y∈x
```

<!--en-->
The induction hypothesis identifies `u` with `π y`, and `π y = w` transports membership in the recorded value to `w`. This is what the backward direction claims.
<!--zh-->
归纳假设把 `u` 认同为 `π y`，再沿 `π y = w` 搬移，即得 `w` 属于被记录的取值。这正是向后方向所主张的。
<!--ja-->
帰納法の仮定が `u` を `π y` と同定し、`π y = w` に沿って輸送すると、`w` が記録された値に属することが従う。後ろ向きの方向が主張するのはこれである。
<!--/-->

```agda
          inner : Σ[ u ∈ CS.S ] Holds F yS u → ⟨ w ∈ˢ fst v ⟩
          inner (u , fu) =
            subst (λ t → ⟨ t ∈ˢ fst v ⟩) (eu ∙ e) (val u .snd ∣ yS , (ry , fu) ∣₁)
            where
            eu : fst u ≡ C.π y
```

<!--en-->
The equation `eu` is the induction hypothesis at the component: the table's value at `y` equals the collapse of `y`. Composed with the equation carried by the decomposition, it identifies the entry's value with `w`, which is exactly what the backward direction had to place.
<!--zh-->
等式 `eu` 是归纳假设在分量 `y` 处的应用：表在 `y` 处的取值等于 `y` 的塌缩。把它与分解所携带的等式复合，条目的取值便被认同于 `w`，这正是向后方向所要安放的。
<!--ja-->
等式 `eu` は、成分 `y` での帰納の仮定である。表の `y` での値は `y` の崩壊に等しい、というものである。分解が携える等式と合成すれば、項目の値は `w` と同一視され、後ろ向きの方向が置こうとしていたのはまさにこれである。
<!--/-->

```agda
            eu = IH y y∈x (snd yS) y∈M u (hc yS u fu .fst) (hc yS u fu .snd)
```

<!--en-->
Applying the induction to the underlying set of a carrier element gives the same uniqueness statement in the restricted structure. The resulting determination lemma says that whenever the collapse formula is satisfied at a member of `M`, its value must equal that member's collapse.
<!--zh-->
把归纳施于载体元素的底层集合，便在受限结构中得到同一唯一性陈述。所得确定性引理说明：塌缩公式若在 `M` 的成员处成立，其取值必等于该成员的塌缩。
<!--ja-->
台の要素の基礎集合に帰納を適用すると、制限された構造で同じ一意性の主張が得られる。得られる決定補題は、崩壊の論理式が `M` の要素で成立するなら、その値はその要素の崩壊に等しいことを述べる。
<!--/-->

```agda
  value-val : (F : CS.S) → Correct F R → (x : CS.S) → ⟨ fst x ∈ˢ M ⟩ → (v : CS.S)
            → Complete F R x → ValueIs F R x v → fst v ≡ C.π (fst x)
  value-val F hc x = value-val′ F hc (fst x) (snd x)
  piFo-val : (q : CS.S) → ⟨ fst q ∈ˢ M ⟩ → (v : CS.S) → ⟨ (v ∷ q ∷ []) ⊨ piFo ⟩
           → fst v ≡ C.π (fst q)
```

<!--en-->
The proof eliminates the truncated existence into the equality of two h-sets, which is a proposition, and applies the uniqueness just proved to the correct table handed over by the outward reading. The next construction cuts from the carrier the elements lying inside a given element of `L`.
<!--zh-->
证明把截断存在消去到两个 h-集合的相等之中，后者是命题，并对向外读法交出的正确表应用刚证的唯一性。下一个构造从载体中切出落在 `L` 的某个给定元素之内的元素。
<!--ja-->
証明は、切り詰められた存在を二つの h-集合の等しさという命題へ消去し、外向きの読み出しが手渡す正しい表に、今証明した一意性を適用する。次の構成では、`L` の与えられた要素の内側にある要素を台から切り出す。
<!--/-->

```agda
  piFo-val q mq v h = rec₁ (setIsSet (fst v) (C.π (fst q)))
    (λ { (F , (hc , (hm , hv))) → value-val F hc q mq v hm hv })
    (piFo-out v q h)
```

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Cut (K : CS.S) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The cutting formula is the single atomic formula: the free slot is a member of the constant `K`. Everything the slice contains is what satisfies it.
<!--zh-->
切割公式只有一条原子公式：自由槽位属于常元 `K`。切片所容纳的，恰是满足它的那些元素。
<!--ja-->
切り出しの論理式はただ一つの原子論理式である。自由な枠が定数 `K` の要素であることを表す。スライスが収めるのは、これを満たす要素だけである。
<!--/-->

```agda
    cutFo : Formula CS.S 1
    cutFo = var i0 ∈̇ con K
```

<!--en-->
Separation applied at `Mʟ` yields the slice as an element of `L`, so the slice is more than a mere class of members. This is what lets the slice serve as the domain of an internal recursion.
<!--zh-->
把分离施于 `Mʟ`，切片便作为 `L` 的元素而得，而不只是成员的类。因此切片可以作为内部递归的定义域使用。
<!--ja-->
分離を `Mʟ` に適用することで、スライスも `L` の要素として得られ、単なる要素の類では終わらない。このため、スライスを内部再帰の定義域として使える。
<!--/-->

```agda
    opaque
      cut : CS.S
      cut = hasSeparationL Mʟ cutFo .fst .fst
```

<!--en-->
The membership specification identifies membership in the slice with membership in the carrier together with satisfaction of the cutting formula, which unpacks to lying in the underlying set of `K`.
<!--zh-->
隶属规格把「属于切片」等同于「属于载体且满足切割公式」，后者展开即落在 `K` 的底层集合之中。
<!--ja-->
所属の仕様は、スライスへの所属を、台への所属と切り出しの論理式の充足とを合わせたものとして同定する。後者はほどけば、`K` の基礎の集合の中にあることにほかならない。
<!--/-->

```agda
      cut-mem : (y : CS.S) → (y CS.∈ˢ cut) ≡ ((y CS.∈ˢ Mʟ) ⊓ ((y ∷ []) ⊨ cutFo))
      cut-mem = hasSeparationL Mʟ cutFo .fst .snd
```

<!--en-->
The inward direction combines membership in `M` with membership in the underlying set of `K` to place the carried element in the slice.
<!--zh-->
向内方向把属于 `M` 与属于 `K` 的底层集合这两个事实合并，从而把载入后的元素放进切片。
<!--ja-->
内向きの方向は、`M` への所属と `K` の基礎集合への所属を組み合わせ、載せた要素をスライスに入れる。
<!--/-->

```agda
      cut-in : (y : CS.S) → ⟨ fst y ∈ˢ M ⟩ → ⟨ fst y ∈ˢ fst K ⟩ → ⟨ y CS.∈ˢ cut ⟩
      cut-in y my yK = subst ⟨_⟩ (sym (cut-mem y)) (my , yK)
```

<!--en-->
The outward direction reads the same specification back into its two components. A member `q` of the carrier is good at a stage `δ` when membership in that stage yields both a constructible presentation of its collapse and the collapse formula at `q`.
<!--zh-->
向外方向把同一规格读回其两个分量。载体成员 `q` 在层 `δ` 处称为「好」，若它属于该层时，既能得到其塌缩的可构造呈现，也能得到 `q` 处的塌缩公式。
<!--ja-->
外向きの方向は、同じ仕様を二つの成分へ読み戻す。台の要素 `q` が段階 `δ` で「良い」とは、その段階に属するとき、崩壊の構成可能な表示と `q` における崩壊の論理式の両方が得られることである。
<!--/-->

```agda
      cut-out : (y : CS.S) → ⟨ y CS.∈ˢ cut ⟩ → ⟨ fst y ∈ˢ M ⟩ × ⟨ fst y ∈ˢ fst K ⟩
      cut-out y h = subst ⟨_⟩ (cut-mem y) h
```
</div>
</details>
```agda
  Good : S → S → Type (ℓ-suc ℓ)
  Good δ q = ⟨ q ∈ˢ M ⟩ → ⟨ q ∈ˢ Lset δ ⟩
           → Σ[ qL ∈ ⟨ isL (C.π q) ⟩ ] ((mq : ⟨ q ∈ˢ M ⟩)
```

<!--en-->
The second component of goodness packages the collapse as an element of `𝒮ʟ` using its constructibility proof, and states that the collapse formula holds of this value and the chosen presentation of the member of `M`.
<!--zh-->
「好」的第二分量利用可构造性证明把塌缩包装成 `𝒮ʟ` 的元素，并断言塌缩公式在该取值与所选的 `M` 成员呈现上成立。
<!--ja-->
「良いこと」の第二成分は、構成可能性の証明によって崩壊を `𝒮ʟ` の要素として包み、その値と選んだ `M` の要素の表示について崩壊の論理式が成立することを述べる。
<!--/-->

```agda
                → ⟨ ((C.π q , qL) ∷ up q mq ∷ []) ⊨ piFo ⟩)
```

<!--en-->
Goodness is a proposition: membership in the carrier, in the stage, constructibility, and satisfaction are each one. This matters because the stage decomposition returns a merely-existing witness, and a merely-existing goodness can be consumed without choosing among witnesses.
<!--zh-->
「好」是命题：对载体的隶属、对层的隶属、可构造性与满足各自为命题。这一点至关重要，因为层的分解只返回仅仅存在的见证，而仅仅存在的「好」可以被消费，无须在见证之间挑选。
<!--ja-->
「良いこと」は命題である。台への所属も、段階への所属も、構成可能性も充足も、それぞれ命題だからである。ここが大切である。段階の分解が返すのは、単に存在するだけの証人であるが、命題である「良いこと」なら、証人を選ぶことなく消費できるのである。
<!--/-->

```agda
  isPropGood : (δ q : S) → isProp (Good δ q)
  isPropGood δ q = isPropΠ2 λ _ _ → isPropΣ (snd (isL (C.π q)))
    λ qL → isPropΠ λ mq → snd (((C.π q , qL) ∷ up q mq ∷ []) ⊨ piFo)
```

<!--en-->
Fix an ordinal stage `δ'` and assume goodness for every `q` that lies both in `M` and in `Lset δ'`. These earlier collapse values will be assembled into the value at the next argument.
<!--zh-->
固定序数层 `δ'`，并假设每个同时属于 `M` 与 `Lset δ'` 的 `q` 都是「好」的。这些较早的塌缩值将被组装成下一实参处的取值。
<!--ja-->
順序数段階 `δ'` を固定し、`M` と `Lset δ'` の両方に属する各 `q` が「良い」と仮定する。これら先行する崩壊値を組み合わせて、次の入力での値を作る。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Step (δ' : S) (oδ' : IsOrd δ')
              (IH : (q : S) → Good δ' q) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The slice is cut at the stage `Lset δ'`: the members of the carrier that the stage already contains. Because the stage is a set of `L`, the slice is an element of `L` by separation, and it is exactly the domain the induction hypothesis speaks about.
<!--zh-->
切片在层 `Lset δ'` 处切出：该层已容纳的载体成员。由于该层是 `L` 的集合，切片由分离成为 `L` 的元素，而它恰是归纳假设所谈论的定义域。
<!--ja-->
スライスは、段階 `Lset δ'` で切り出される。その段階がすでに収めている台の要素である。段階は `L` の集合なので、スライスは分離によって `L` の要素になり、これこそ帰納の仮定が語る定義域である。
<!--/-->

```agda
    module Sl = Cut (LsetS δ' oδ') using ( cut; cut-in; cut-out )
```

<!--en-->
Stages are transitive, so a member of a member of the stage is still inside the stage; this is the fact that later restricts the table's conditions to smaller arguments. By the induction hypothesis, the collapse of a slice member is available as an element of `𝒮ʟ`; its constructibility proof is the first component of goodness.
<!--zh-->
层是传递的，因此层的成员的成员仍在层内；这条事实稍后会把表的条件限制到更小的实参。由归纳假设，切片成员的塌缩可作为 `𝒮ʟ` 的元素使用；其可构造性证明正是「好」的第一分量。
<!--ja-->
段階は推移的である。したがって、段階の要素の要素も段階の内側にあり、この事実が後で表の条件をより小さい入力へ制限する。帰納の仮定により、スライスの要素の崩壊は `𝒮ʟ` の要素として得られ、その構成可能性の証明が「良いこと」の第一成分である。
<!--/-->

```agda
    Lδ'-trans : {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ Lset δ' ⟩ → ⟨ y ∈ˢ Lset δ' ⟩
    Lδ'-trans {x} {y} = layer-trans (Lset-layer δ') {x = x} {y = y}
    πʟ : (y : CS.S) → ⟨ y CS.∈ˢ Sl.cut ⟩ → CS.S
    πʟ y hy = C.π (fst y) , IH (fst y) (Sl.cut-out y hy .fst) (Sl.cut-out y hy .snd) .fst
```

<!--en-->
The collapse formula holds at the pair of that collapse and the member, by the same induction hypothesis: the second component of goodness is exactly a satisfaction of the formula at the pair, transported along the identification of the element with its underlying set.
<!--zh-->
塌缩公式在该塌缩与成员组成的对上成立，同样由归纳假设给出：「好」的第二分量恰是该公式在此对上的一个满足，沿「元素与其底层集合的认同」运输而来。
<!--ja-->
崩壊の論理式が、その崩壊と要素の対の上で成立するのも、同じ帰納の仮定による。「良いこと」の第二成分はちょうど、この対での論理式の充足であり、要素とその基礎の集合の同定に沿って運ばれる。
<!--/-->

```agda
    πʟ-graph : (y : CS.S) (hy : ⟨ y CS.∈ˢ Sl.cut ⟩)
             → ⟨ (πʟ y hy ∷ y ∷ []) ⊨ piFo ⟩
    πʟ-graph y hy =
      subst (λ y' → ⟨ (πʟ y hy ∷ y' ∷ []) ⊨ piFo ⟩) (S≡ refl)
        (IH (fst y) my (Sl.cut-out y hy .snd) .snd my)
```

<!--en-->
The identification uses the membership of the member in the carrier, read out of the slice specification; the underlying set has not changed, so the transport is determined by the propositionality of constructibility.
<!--zh-->
该认同使用从切片规格读出的「成员属于载体」；底层集合未曾改变，而由于可构造性的证明是命题，该同一视足以确定所需的运输。
<!--ja-->
この同定には、スライスの仕様から読み出した要素の台への所属を使う。基礎集合は変わっておらず、構成可能性の証明は命題なので、この同一視に沿った輸送は一意に定まる。
<!--/-->

```agda
      where
      my : ⟨ fst y ∈ˢ M ⟩
      my = Sl.cut-out y hy .fst
```

<!--en-->
Over the slice, these collapse values form an internal recursion with domain the slice and graph `piFo`. Constructibility supplies each value as an element of `𝒮ʟ`, so the graph entries are pairs of `𝒮ʟ`-elements.
<!--zh-->
在切片上，这些塌缩取值组成以切片为定义域、以 `piFo` 为图公式的内部递归。可构造性把每个取值给成 `𝒮ʟ` 的元素，因此图条目是 `𝒮ʟ` 元素组成的有序对。
<!--ja-->
スライス上の崩壊値は、スライスを定義域、`piFo` をグラフの論理式とする内部再帰をなす。構成可能性によって各値は `𝒮ʟ` の要素となるので、グラフの項目は `𝒮ʟ` の要素の対である。
<!--/-->

```agda
    private
      Rπ : Recursion
      Rπ = record
        { dom = Sl.cut ; graph = piFo
        ; funct = λ y hy → (πʟ y hy , πʟ-graph y hy)
```

<!--en-->
Functionality holds because the collapse formula determines its value at every member of the carrier: any other value satisfying the formula at the same pair is equal to it, which the determination lemma reads out. The equality of the corresponding `𝒮ʟ`-elements then follows because their constructibility proofs are proposition-valued.
<!--zh-->
函数性成立，因为塌缩公式在载体的每个成员处都确定其取值：在同一对处满足公式的任何其他取值都等于它，确定性引理读出这一点。随后，由于其中的可构造性证明是命题值的，便得到相应 `𝒮ʟ` 元素的相等。
<!--ja-->
関数性が成立するのは、崩壊の論理式が台のすべての要素でその値を決めるからである。同じ対で論理式を満たすほかの値はどれもそれと等しく、決定の補題がそれを読み出す。対応する `𝒮ʟ` の要素の等しさは、構成可能性の証明が命題値であることから従う。
<!--/-->

```agda
            , λ { (v , h) → Σ≡Prop (λ w → snd ((w ∷ y ∷ []) ⊨ piFo))
                (sym (S≡ (piFo-val y (Sl.cut-out y hy .fst) v h))) } }
```

<!--en-->
The graph recursion of `L` collects the table: a set of pairs of carrier elements whose entries are exactly the collapse records over the slice.
<!--zh-->
`L` 的图递归收集这张表：一个由载体元素之对组成的集合，其条目恰是切片上的塌缩记录。
<!--ja-->
`L` のグラフの再帰が表を集める。台の要素の対からなる集合で、その項目はスライス上の崩壊の記録にほかならない。
<!--/-->

```agda
      module T = RecursionGraph Rπ using ( F; F-in; pair-out )
```

<!--en-->
The collected set is the table at the stage: an element of `L` that pairs each slice member with its constructible collapse.
<!--zh-->
收集所得的集合就是该层处的表：一个 `L` 的元素，把每个切片成员与其可构造的塌缩配成对。
<!--ja-->
集められた集合が、この段階での表である。`L` の要素であり、スライスの各要素と、その構成可能な崩壊とを対にする。
<!--/-->

```agda
    Tab : CS.S
    Tab = T.F
```

<!--en-->
The inward reading of the table exhibits its entries: at every slice member, the pair of the member with its collapse is recorded.
<!--zh-->
表的向内读式出示其条目：在每个切片成员处，成员与其塌缩组成的对都被记录。
<!--ja-->
表の内向きの読み出しは、その項目を示す。スライスの各要素で、要素とその崩壊の対が記録される。
<!--/-->

```agda
    Tab-in : (y : CS.S) (hy : ⟨ y CS.∈ˢ Sl.cut ⟩) → Holds Tab y (πʟ y hy)
    Tab-in = T.F-in
```

<!--en-->
The outward reading decomposes an entry into a slice member and a value equal to the collapse of its underlying set. Together with the inward reading this says the table records exactly the collapses, nothing distorted.
<!--zh-->
向外读式把一条条目分解为切片成员与其底层集合的塌缩相等的取值。与向内读式合起来，这说明表记录的恰是诸塌缩，毫无走样。
<!--ja-->
外向きの読み出しは、項目をスライスの要素と、その基礎集合の崩壊に等しい値へ分解する。内向きの読み出しと合わせて、表が記録するのは崩壊そのものであり、歪みがないことが分かる。
<!--/-->

```agda
    Tab-pair : (x v : CS.S) → Holds Tab x v
             → ⟨ x CS.∈ˢ Sl.cut ⟩ × (fst v ≡ C.π (fst x))
    Tab-pair = T.pair-out
```

<!--en-->
An argument `x` is closed when every member of `x` that also belongs to `M` lies in the stage slice. This condition is imposed on each argument separately, because no transitivity assumption is made on `M`.
<!--zh-->
实参 `x` 称为封闭，若 `x` 的每个同时属于 `M` 的成员都落在层切片中。这个条件须逐实参给出，因为这里并未假定 `M` 传递。
<!--ja-->
引数 `x` が閉じているとは、`x` の要素であり、かつ `M` に属するものがすべて段階スライスに入ることである。この条件は引数ごとに課される。ここでは `M` の推移性を仮定していない。
<!--/-->

```agda
    Closed : CS.S → Type (ℓ-suc ℓ)
    Closed x = (y : S) (y∈x : ⟨ y ∈ˢ fst x ⟩) (y∈M : ⟨ y ∈ˢ M ⟩)
             → ⟨ up y y∈M CS.∈ˢ Sl.cut ⟩
```

<!--en-->
A slice member is closed by transitivity of the stage: any member of it that lies in `M` remains in the stage and therefore belongs to the slice.
<!--zh-->
切片成员因层的传递性而封闭：它的任何同时属于 `M` 的成员仍在该层内，因而属于切片。
<!--ja-->
スライスの要素は段階の推移性によって閉じている。その要素であり、かつ `M` に属するものは段階内にとどまるので、スライスに属する。
<!--/-->

```agda
    slice-closed : (x : CS.S) → ⟨ x CS.∈ˢ Sl.cut ⟩ → Closed x
    slice-closed x hx y y∈x y∈M =
      Sl.cut-in (up y y∈M) y∈M (Lδ'-trans {x = fst x} {y = y} y∈x (Sl.cut-out x hx .snd))
```

<!--en-->
For a closed argument, completeness of the table is the truncated existence of the table's own entry at each related member: closedness places that member inside the slice, where the table records its collapse. The relation entry is decomposed to name the member.
<!--zh-->
对封闭的实参，表的完备性就是「表在相关成员处有自己的条目」的截断存在：封闭性把该成员放进切片，表在那里记录其塌缩。关系条目被分解以指名该成员。
<!--ja-->
閉じた入力に対する表の完備さとは、関係する各要素での表自身の項目の切り詰められた存在である。閉じていることがその要素をスライスの中へ置き、表がそこに崩壊を記録する。関係の項目は分解されて、その要素を名指す。
<!--/-->

```agda
    complete-of : (x : CS.S) → Closed x → Complete Tab R x
    complete-of x cl y ry = ∣ πʟ y' hy' , subst (λ w → ⟨ pr w (C.π (fst y)) ∈ˢ fst Tab ⟩) refl (Tab-in y' hy') ∣₁
      where
      ro = R-out y x ry
      y' : CS.S
```

<!--en-->
The member is carried as a carrier element, and closedness places the carried element inside the slice, which is exactly the hypothesis under which the table recorded the collapse.
<!--zh-->
该成员被载为载体元素，而封闭性把载入后的元素放进切片，这正是表记录其塌缩时所用的假设。
<!--ja-->
その要素は台の要素として載せられ、閉じていることが、載せられた要素をスライスの中へ置く。これは、表が崩壊を記録したときの仮定そのものである。
<!--/-->

```agda
      y' = up (fst y) (ro .fst)
      hy' : ⟨ y' CS.∈ˢ Sl.cut ⟩
      hy' = cl (fst y) (ro .snd .snd) (ro .fst)
```

<!--en-->
For a closed argument, the value clause holds of the collapse itself. The proof has two directions: every member of the collapse value comes from a related member, and every member related to the argument is carried into the collapse value by the table.
<!--zh-->
对封闭的实参，取值子句对塌缩自身成立。证明有两个方向：塌缩值的每个成员都来自某个相关成员，而与实参有关系的每个成员都被表载入塌缩值。
<!--ja-->
閉じた入力に対して、値の条項は崩壊そのものについて成立する。証明には二方向ある。崩壊値の要素はどれも関係する要素から来ており、入力と関係する要素はどれも、表によって崩壊値の中へ運ばれる。
<!--/-->

```agda
    valueIs-of : (x : CS.S) → ⟨ fst x ∈ˢ M ⟩ → Closed x → (v : CS.S) → fst v ≡ C.π (fst x)
               → ValueIs Tab R x v
    valueIs-of x mx cl v ev w = fwd , bwd
      where
      fwd : ⟨ fst w ∈ˢ fst v ⟩ → Src Tab R x w
```

<!--en-->
Forward: a member `w` of the candidate value `v` is decomposed by the collapse reading into a component of the argument inside the carrier, whose collapse equals `w`. The decomposition is a truncated existence, and the elimination targets a proposition.
<!--zh-->
向前：候选取值 `v` 的成员 `w` 经塌缩读法分解为载体中实参的分量，其塌缩等于 `w`。该分解是截断的存在，而消去的目标是一条命题。
<!--ja-->
前向きでは、候補の値 `v` の要素 `w` を、崩壊の読み出しによって台の中の入力の成分へ分解する。その成分の崩壊は `w` に等しくなる。分解は切り詰められた存在であり、消去の対象は命題である。
<!--/-->

```agda
      fwd w∈ = map₁ read (π-mem-out (fst x) (fst w) (subst (λ t → ⟨ fst w ∈ˢ t ⟩) ev w∈))
        where
        read : Σ[ y ∈ S ] (⟨ y ∈ˢ fst x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ fst w))
             → Σ[ y ∈ CS.S ] (Holds R y x × Holds Tab y w)
        read (y , (y∈x , y∈M , e)) = up y y∈M
```

<!--en-->
The component is lifted to the carrier. Its membership in the argument yields the relation entry, while the table entry is transported along the equality between its collapse and `w`. Together these two entries form the required witness of `Src Tab R x w`.
<!--zh-->
该分量先提升为载体元素。它属于实参这一事实给出关系条目，而表条目沿其塌缩与 `w` 的等式搬运。两条条目合在一起，构成所需的 `Src Tab R x w` 见证。
<!--ja-->
その成分を台の要素へ持ち上げる。入力への所属から関係の項目が得られ、表の項目はその崩壊と `w` の等式に沿って輸送される。この二つを合わせると、必要な `Src Tab R x w` の証人になる。
<!--/-->

```agda
          , ( R-in (up y y∈M) x y∈M mx y∈x
            , subst (λ t → ⟨ pr y t ∈ˢ fst Tab ⟩) e (Tab-in (up y y∈M) (cl y y∈x y∈M)) )
```

<!--en-->
Backward: a source entry for `w` names a related member whose table value is `w`. The pair reading splits the entry into memberships and an equality; the collapse reading places `w` in the collapse of the first component, and the two equations transport it back into the recorded value.
<!--zh-->
向后：`w` 的一条源条目名指一个表取值为 `w` 的相关成员。对读法把条目拆成隶属与等式；塌缩读法把 `w` 放进第一分量的塌缩，而两条等式再把它运回被记录取值。
<!--ja-->
後ろ向き：`w` のソースの項目は、表の値が `w` であるような関係する要素を名指す。対の読み出しが項目を所属と等式に分け、崩壊の読み出しが `w` を第一成分の崩壊の中に置き、二つの等式がそれを記録された値へ運び戻す。
<!--/-->

```agda
      bwd : Src Tab R x w → ⟨ fst w ∈ˢ fst v ⟩
      bwd = rec₁ (snd (fst w ∈ˢ fst v)) (λ { (y , (ry , ty)) →
        subst2 (λ s t → ⟨ s ∈ˢ t ⟩) (sym (Tab-pair y w ty .snd)) (sym ev)
          (C.π∈-fwd (fst x) (fst y) (R-out y x ry .snd .snd) (R-out y x ry .fst)) })
```

<!--en-->
The correctness of the table at each entry is assembled from the two clauses at the slice member that the entry names. The pair reading contributes the slice membership and the carrier membership.
<!--zh-->
表在每条条目处的正确性，由该条目所指名的切片成员处的两个子句装配而成。对读法贡献切片隶属与载体隶属。
<!--ja-->
それぞれの項目での表の正しさは、その項目が名指すスライスの要素での二つの条項から組み立てられる。対の読み出しが、スライスへの所属と台への所属を与える。
<!--/-->

```agda
    Tab-correct : Correct Tab R
    Tab-correct x v hxv = complete-of x cl , valueIs-of x mx cl v (Tab-pair x v hxv .snd)
      where
      hx : ⟨ x CS.∈ˢ Sl.cut ⟩
      hx = Tab-pair x v hxv .fst
```

<!--en-->
The carrier membership and closedness complete the hypotheses, and the step module is parameterized by an argument `q` of the carrier all of whose members lie below the earlier stage. This is the situation needed for an element of the definable powerset of `Lset δ'`; here closedness follows from `q⊆`.
<!--zh-->
载体隶属与封闭性补全诸假设；步进模块由载体的实参 `q` 参数化，其所有成员都低于更早层。这是 `Lset δ'` 的可定义幂集中的元素所需的情形；此时封闭性由 `q⊆` 得出。
<!--ja-->
台への所属と閉じていることが仮定を完成させ、ステップのモジュールは、その要素がすべてより前の段階の下にあるような台の入力 `q` でパラメータづけられる。これは `Lset δ'` の定義可能冪集合の要素に必要な状況であり、ここでは閉じていることが `q⊆` から従う。
<!--/-->

```agda
      mx : ⟨ fst x ∈ˢ M ⟩
      mx = Sl.cut-out x hx .fst
      cl : Closed x
      cl = slice-closed x hx
    module At (q : S) (mq : ⟨ q ∈ˢ M ⟩) (q⊆ : (y : S) → ⟨ y ∈ˢ q ⟩ → ⟨ y ∈ˢ Lset δ' ⟩) where
```

<!--en-->
The argument is carried as a carrier element, so that it can serve as an environment slot and as the second component of pairs.
<!--zh-->
实参被载为载体元素，从而可以充当环境槽位以及有序对的第二分量。
<!--ja-->
入力は台の要素として載せられ、環境の枠としても、対の第二成分としても働けるようになる。
<!--/-->

```agda
      qS : CS.S
      qS = up q mq
```

<!--en-->
Closedness of the carried argument holds by the hypothesis: each member inside the carrier lies below the earlier stage, and the slice admits it. The members of the argument inside the carrier are then cut out as their own slice, the domain on which the collapse value will be computed.
<!--zh-->
载入后实参的封闭性由假设成立：其在载体内的每个成员都低于更早层，切片接纳它们。实参在载体内的成员随后被切出为它们自己的切片，塌缩取值将在这个定义域上计算。
<!--ja-->
載せた入力の閉じていることは仮定から成立する。台の中のその要素はすべてより前の段階の下にあり、スライスが受け入れる。そして台の中の入力の要素が、それ自身のスライスとして切り出される。崩壊の値はこの定義域の上で計算される。
<!--/-->

```agda
      cl : Closed qS
      cl y y∈q y∈M = Sl.cut-in (up y y∈M) y∈M (q⊆ y y∈q)
      module Mq = Cut qS using ( cut; cut-in; cut-out )
```

<!--en-->
The collapse value of `q` is built as an internal recursion: domain the slice of members of `q` in the carrier, graph the collapse formula. This functional graph therefore meets the hypotheses of replacement in `L`.
<!--zh-->
`q` 的塌缩取值被构造为一个内部递归：定义域是 `q` 在载体内的成员切片，图是塌缩公式。因此，这个函数图满足 `L` 中替换原理的假设。
<!--ja-->
`q` の崩壊値は、内部の再帰として作られる。定義域は台の中の `q` の要素のスライス、グラフは崩壊の論理式である。したがって、この関数的グラフは `L` における置換の仮定を満たす。
<!--/-->

```agda
      private
        valR : Recursion
        valR = record
          { dom   = Mq.cut
          ; graph = piFo
```

<!--en-->
Functionality is assembled through `mereFunct`, from a merely-existing unique value at each argument. The witness `wit` produces such a value together with its satisfaction and uniqueness, all inside the truncation, because uniqueness of the collapse formula at a member of the carrier is a proposition.
<!--zh-->
函数性经由 `mereFunct` 装配，所需输入是在每个实参处截断存在的唯一取值。见证 `wit` 在截断内部产出这样的取值连同其满足与唯一性，因为塌缩公式在载体成员处的唯一性是命题。
<!--ja-->
関数性は `mereFunct` を通して組み立てられる。各入力で、一意な値が「単に存在する」ことからである。証人 `wit` は、そのような値と、その充足と一意性とを、切り詰めの内側で産出する。台の要素での崩壊の論理式の一意性が命題だからである。
<!--/-->

```agda
          ; funct = λ y hy → mereFunct piFo y (wit y hy) }
          where
          wit : (y : CS.S) (hy : ⟨ y CS.∈ˢ Mq.cut ⟩)
              → ∥ Σ[ v ∈ CS.S ] (⟨ (v ∷ y ∷ []) ⊨ piFo ⟩
                                × ((v' : CS.S) → ⟨ (v' ∷ y ∷ []) ⊨ piFo ⟩ → v' ≡ v)) ∥₁
```

<!--en-->
The witness is the global collapse value `C.π (fst y)`, presented as constructible by the induction hypothesis. The stage-slice table supplies its `piFo` proof, and `piFo-val` supplies uniqueness.
<!--zh-->
见证是全局塌缩值 `C.π (fst y)`，由归纳假设给出其可构造呈现。层切片上的表供给它的 `piFo` 证明，`piFo-val` 供给唯一性。
<!--ja-->
証人は大域的な崩壊値 `C.π (fst y)` であり、帰納の仮定によって構成可能なものとして表示される。段階スライス上の表が `piFo` の証明を与え、`piFo-val` が一意性を与える。
<!--/-->

```agda
          wit y hy = ∣ πʟ y hy'
            , ( πʟ-graph y hy'
              , λ v' hv' → S≡ (piFo-val y my v' hv') ) ∣₁
            where
            my : ⟨ fst y ∈ˢ M ⟩
```

<!--en-->
The membership of `y` in the carrier comes from the slice of `q`. The hypothesis puts every member of `q` in `Lset δ'`, so every such carrier element is admitted by the stage slice.
<!--zh-->
`y` 在载体中的隶属来自 `q` 的切片。假设把 `q` 的每个成员放入 `Lset δ'`，所以其中每个属于载体的元素都被层切片接纳。
<!--ja-->
`y` の台への所属は `q` のスライスから来る。仮定により `q` の各要素は `Lset δ'` に入るので、そのうち台に属する要素はすべて段階スライスに入る。
<!--/-->

```agda
            my = Mq.cut-out y hy .fst
            hy' : ⟨ y CS.∈ˢ Sl.cut ⟩
            hy' = Sl.cut-in y my (q⊆ (fst y) (Mq.cut-out y hy .snd))
```

<!--en-->
Replacement now collects the values of this recursion into an element of `L`: its members are exactly the constructible collapse values of members of `q` that lie in `M`.
<!--zh-->
替换把该递归的取值收集成 `L` 的一个元素：其成员恰是 `q` 中同时属于 `M` 的成员之可构造塌缩值。
<!--ja-->
置換はこの再帰の値を `L` の要素として集める。その要素はちょうど、`q` の要素であり、かつ `M` に属するものの構成可能な崩壊値である。
<!--/-->

```agda
        module Vq = Of valR using ( table; table-in; table-out )
```

<!--en-->
The underlying set of the table agrees with the collapse of `q`, proved by extensionality through a member-by-member equivalence. Forward: a member of the table is a value at some member `y` of `q` inside the carrier, and the elimination targets the proposition that `w` lies in the collapse of `q`.
<!--zh-->
表的底层集合与 `q` 的塌缩一致，由逐成员等价经外延性证明。向前：表的成员是载体中某个成员 `y` 处的取值，而消去的目标是命题「`w` 属于 `q` 的塌缩」。
<!--ja-->
表の基礎の集合は、`q` の崩壊と一致する。要素ごとの同値を通して外延性で証明される。前向き：表の要素は、台の中の `q` のある要素 `y` での値であり、消去の対象は「`w` が `q` の崩壊に属する」という命題である。
<!--/-->

```agda
      val≡π : fst Vq.table ≡ C.π q
      val≡π = extensionalV {a = fst Vq.table} {b = C.π q} (λ w → ⇔toPath (fwd w) (bwd w))
        where
        fwd : (w : S) → ⟨ w ∈ˢ fst Vq.table ⟩ → ⟨ w ∈ˢ C.π q ⟩
        fwd w hw = rec₁ (snd (w ∈ˢ C.π q))
```

<!--en-->
The outward reading names the member `y` and its value; the determination lemma identifies the value with the collapse of `y`, and the collapse reading places the collapse of `y` inside the collapse of `q`, which the transport composes.
<!--zh-->
向外读法名指成员 `y` 及其取值；确定性引理把该取值同认于 `y` 的塌缩，而塌缩读法把 `y` 的塌缩放进 `q` 的塌缩，运输把两者复合。
<!--ja-->
外向きの読み出しが要素 `y` とその値を名指し、決定の補題がその値を `y` の崩壊と同一視し、崩壊の読み出しが `y` の崩壊を `q` の崩壊の中へ置く。輸送がこの二つを合成する。
<!--/-->

```agda
          (λ { (y , (hy , h)) →
             subst (λ t → ⟨ t ∈ˢ C.π q ⟩)
               (sym (piFo-val y (Mq.cut-out y hy .fst) wS h))
               (C.π∈-fwd q (fst y) (Mq.cut-out y hy .snd) (Mq.cut-out y hy .fst)) })
          (Vq.table-out wS hw)
```

<!--en-->
Since `w` belongs to the constructible value set `Vq.table`, transitivity of `L` supplies its constructibility and hence its presentation as an element of `𝒮ʟ`.
<!--zh-->
由于 `w` 属于可构造的取值集合 `Vq.table`，`L` 的传递性给出 `w` 的可构造性，从而把它呈现为 `𝒮ʟ` 的元素。
<!--ja-->
`w` は構成可能な値集合 `Vq.table` に属するので、`L` の推移性から `w` の構成可能性が得られ、`𝒮ʟ` の要素として表示できる。
<!--/-->

```agda
          where
          wS : CS.S
          wS = w , isL-trans {x = fst Vq.table} {y = w} hw (snd Vq.table)
```

<!--en-->
Backward: a member of the collapse of `q` decomposes into a component of `q` inside the carrier whose collapse equals it, which is precisely the form in which the table records entries.
<!--zh-->
向后：`q` 的塌缩的成员分解为载体中 `q` 的某分量，其塌缩等于该成员；这恰是表记录条目的形式。
<!--ja-->
後ろ向き：`q` の崩壊の要素は、台の中の `q` の成分へと分解され、その成分の崩壊がそれと等しくなる。これは、表が項目を記録する形そのものである。
<!--/-->

```agda
        bwd : (w : S) → ⟨ w ∈ˢ C.π q ⟩ → ⟨ w ∈ˢ fst Vq.table ⟩
        bwd w hw = rec₁ (snd (w ∈ˢ fst Vq.table)) read (π-mem-out q w hw)
          where
          read : Σ[ y ∈ S ] (⟨ y ∈ˢ q ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) → ⟨ w ∈ˢ fst Vq.table ⟩
          read (y , (y∈q , y∈M , e)) =
```

<!--en-->
The equation transports `w` to the collapse of the component, and the table's inward reading produces the entry at the carried component, which records exactly that collapse.
<!--zh-->
等式把 `w` 运到分量的塌缩，而表的向内读式在载入后的分量处产出条目，其记录的恰是该塌缩。
<!--ja-->
等式が `w` を成分の崩壊へ運び、表の内向きの読み出しが、載せた成分での項目を作る。そこに記録されるのはまさにその崩壊である。
<!--/-->

```agda
            subst (λ t → ⟨ t ∈ˢ fst Vq.table ⟩) e
              (Vq.table-in yS (πʟ yS hy') hy (πʟ-graph yS hy'))
            where
            yS : CS.S
            yS = up y y∈M
```

<!--en-->
The carried component lies in the slice of `q` by its carrier membership, and in the stage slice by the hypothesis that members of `q` lie below the earlier stage.
<!--zh-->
载入后的分量因其在载体中的隶属而属于 `q` 的切片，又因「`q` 的成员低于更早层」的假设而属于层切片。
<!--ja-->
載せた成分は、台への所属によって `q` のスライスの中にあり、また「`q` の要素はより前の段階の下にある」という仮定によって、段階のスライスの中にもある。
<!--/-->

```agda
            hy : ⟨ yS CS.∈ˢ Mq.cut ⟩
            hy = Mq.cut-in yS y∈M y∈q
            hy' : ⟨ yS CS.∈ˢ Sl.cut ⟩
            hy' = Sl.cut-in yS y∈M (q⊆ y y∈q)
```

<!--en-->
The collapse of `q` is constructible: it equals the underlying set of the table, and the table is an element of `L`, so constructibility is transported along the equality. This is the first clause of goodness at `q`.
<!--zh-->
`q` 的塌缩可构造：它等于表的底层集合，而表是 `L` 的元素，故可构造性沿该等式运输而来。这是 `q` 处「好」的第一个子句。
<!--ja-->
`q` の崩壊は構成可能である。それは表の基礎の集合に等しく、表は `L` の要素なので、構成可能性がこの等式に沿って運ばれる。これが `q` での「良いこと」の最初の条項である。
<!--/-->

```agda
      πq-isL : ⟨ isL (C.π q) ⟩
      πq-isL = subst (λ t → ⟨ isL t ⟩) val≡π (snd Vq.table)
```

<!--en-->
The second clause of goodness is the collapse formula satisfied at the pair of the collapse with the member: correctness of the table, completeness at the closed argument, and the value clause identifying the value with the collapse. With both clauses, the stage induction can be stated: goodness at every ordinal.

The induction runs along membership in the hierarchy, consuming at each step the decomposition of membership in the stage.
<!--zh-->
「好」的第二个子句是塌缩公式在该塌缩与成员组成的对上成立：表的正确性、封闭实参处的完备性、以及认同取值与塌缩的取值子句。有了两个子句，层归纳即可陈述：在每个序数处的「好」。

归纳沿层级的隶属运行，每步消耗「属于层」的分解。
<!--ja-->
「良いこと」の第二の条項は、崩壊と要素の対の上で崩壊の論理式が成立することである。表の正しさ、閉じた入力での完備さ、そして値を崩壊と同定する値の条項である。二つの条項がそろえば、段階の帰納を述べられる。すべての順序数での「良いこと」である。

帰納は、階層の所属に沿って走り、各ステップで、段階への所属の分解を消費する。
<!--/-->

```agda
      good : (mq' : ⟨ q ∈ˢ M ⟩) → ⟨ ((C.π q , πq-isL) ∷ up q mq' ∷ []) ⊨ piFo ⟩
      good mq' = subst (λ q' → ⟨ ((C.π q , πq-isL) ∷ q' ∷ []) ⊨ piFo ⟩) (S≡ refl)
        (piFo-in (C.π q , πq-isL) qS Tab Tab-correct (complete-of qS cl)
          (valueIs-of qS mq cl (C.π q , πq-isL) refl))
```
</div>
</details>
```agda
  good-at : (δ : S) → IsOrd δ → (q : S) → Good δ q
```

<!--en-->
To prove goodness at `δ`, the membership of `q` in the stage `Lset δ` is decomposed: `q` lies in the definable powerset of an earlier stage `δ'`. The decomposition is eliminated into goodness, because goodness is a proposition.
<!--zh-->
要证 `δ` 处的「好」，先把 `q` 对层 `Lset δ` 的隶属分解：`q` 落在更早层 `δ'` 的可定义幂集内。该分解被消去到「好」之中，因为「好」是命题。
<!--ja-->
`δ` での「良いこと」を証明するには、段階 `Lset δ` への `q` の所属を分解する。`q` は、より前の段階 `δ'` の定義可能冪集合の中にある、と。分解は「良いこと」へ消去される。「良いこと」が命題だからである。
<!--/-->

```agda
  good-at = ∈-induction {P = λ δ → IsOrd δ → (q : S) → Good δ q} go
    where
    go : (δ : S) → ((δ' : S) → ⟨ δ' ∈ˢ δ ⟩ → IsOrd δ' → (q : S) → Good δ' q)
       → IsOrd δ → (q : S) → Good δ q
    go δ IH oδ q mq q∈Lδ = rec₁ (isPropGood δ q) read (Lset-out δ q q∈Lδ) mq q∈Lδ
```

<!--en-->
The decomposition names the earlier stage `δ'` below `δ` and the membership of `q` in its definable powerset. Using goodness below `δ'`, the step construction yields goodness at `q`. The definable powerset clause then says every member of `q` lies in the stage `Lset δ'`, which is the closedness hypothesis the step consumes.
<!--zh-->
分解给出低于 `δ` 的更早层 `δ'`，以及 `q` 属于其可定义幂集。利用 `δ'` 以下的「好」，步进构造得到 `q` 处的「好」。可定义幂集子句进而说 `q` 的每个成员都落在层 `Lset δ'` 内，这正是步进所消费的封闭性假设。
<!--ja-->
分解は、`δ` の下のより前の段階 `δ'` と、その定義可能冪集合への `q` の所属を名指す。`δ'` より下での「良いこと」を使うと、ステップの構成から `q` での「良いこと」が得られる。定義可能冪集合の条項はさらに、`q` のすべての要素が段階 `Lset δ'` の中にあると言う。これが、ステップが消費する閉じていることの仮定である。
<!--/-->

```agda
      where
      read : Σ[ δ' ∈ S ] (⟨ δ' ∈ˢ δ ⟩ × ⟨ q ∈ˢ 𝒟ₒ (Lset δ') ⟩) → Good δ q
      read (δ' , (δ'∈δ , q∈𝒟)) _ _ = A.πq-isL , A.good
        where
        oδ' : IsOrd δ'
```

<!--en-->
Ordinality of `δ'` follows from `δ' ∈ δ`. Applying the induction hypothesis below `δ'`, together with the definable-powerset fact that every member of `q` lies in `Lset δ'`, yields goodness at `q`. Thus the membership induction proves `good-at`. Since `M` itself belongs to `L`, its constructibility certificate supplies a stage containing `M`; transitivity of that stage then places every member of `M` inside it.
<!--zh-->
由 `δ' ∈ δ` 得到 `δ'` 的序数性。把归纳假设用于 `δ'` 以下，并结合可定义幂集所给出的「`q` 的每个成员都属于 `Lset δ'`」，即可得到 `q` 处的「好」，从而闭合 `good-at` 的隶属归纳。又因 `M` 本身属于 `L`，其可构造性证书给出一个包含 `M` 的层；该层的传递性于是把 `M` 的每个成员也放入其中。
<!--ja-->
`δ' ∈ δ` から `δ'` の順序数性が得られる。`δ'` より下で帰納の仮定を使い、`q` のすべての要素が `Lset δ'` に属するという定義可能冪集合の事実を合わせると、`q` での「良いこと」が得られ、`good-at` の所属帰納が閉じる。また `M` 自身が `L` に属するので、その構成可能性の証明から `M` を含む段階が得られ、その段階の推移性によって `M` の各要素も段階内に入る。
<!--/-->

```agda
        oδ' = mem-ord {A = δ} oδ δ' δ'∈δ
        module A = Step.At δ' oδ' (IH δ' δ'∈δ oδ') q mq (λ y y∈q → 𝒟ₒ∋⊆ (Lset δ') q q∈𝒟 y y∈q)
          using ( πq-isL; good )
  π-isL : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL (C.π y) ⟩
  π-isL y y∈M = rec₁ (snd (isL (C.π y)))
```

<!--en-->
A stage containing the constructible carrier `M` is obtained from the proof `Mʟ`, and goodness at that stage yields constructibility of the collapse of every member of `M`. The following claim begins the corresponding argument for members of the whole collapse image `C.πX`, again eliminating a truncated presentation into constructibility.
<!--zh-->
由证明 `Mʟ` 取得一个包含可构造载体 `M` 的层，而该层处的「好」给出 `M` 每个成员之塌缩的可构造性。下一条结论开始对整个塌缩像 `C.πX` 的成员作相应论证，同样把截断呈现消去到可构造性。
<!--ja-->
証明 `Mʟ` から構成可能な台 `M` を含む段階を取り、その段階での「良いこと」から `M` の各要素の崩壊が構成可能であることを得る。続く主張は、崩壊像全体 `C.πX` の要素について同じ議論を始め、やはり切り詰められた表示を構成可能性へ消去する。
<!--/-->

```agda
    (λ { (α , (oα , M∈Lα)) →
       good-at α oα y y∈M (layer-trans (Lset-layer α) {x = M} {y = y} y∈M M∈Lα) .fst })
    (snd Mʟ)
  πX-isL : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ isL x ⟩
  πX-isL x x∈πX = rec₁ (snd (isL x))
```

<!--en-->
The statement of `πX-isL` is about members: each member of the collapse image is the collapse of some member of the carrier, hence constructible.
<!--zh-->
`πX-isL` 的陈述是关于成员的：塌缩像的每个成员都是载体某个成员的塌缩，故可构造。
<!--ja-->
`πX-isL` の主張は要素についてのものである。
<!--/-->

```agda
    (λ { (y , (y∈M , e)) → subst (λ w → ⟨ isL w ⟩) e (π-isL y y∈M) })
    (C.πX-member x x∈πX)
```
</div>
</details>

<!--en-->
## The Skolem hull as an ω-iteration
<!--zh-->
## 把 Skolem 壳写成 ω 迭代
<!--ja-->
## Skolem 包を ω 反復として表す
<!--/-->

<!--en-->
This says exactly that the collapse image is contained in `L`; it is a statement about members, and no claim is made that the image itself is an element of `L`. With the first half finished, the second half opens under new parameters: a stage `lam` closed under successors of its members, and a start `X` whose members all lie in the stage.
<!--zh-->
这恰是说塌缩像包含于 `L`；它是关于成员的陈述，并不主张像本身是 `L` 的元素。前半完成后，后半在新参数下开启：一个对其成员的后继封闭的层 `lam`，以及成员全部落在该层内的起点 `X`。
<!--ja-->
崩壊像の各要素は台のどこかの要素の崩壊であり、だから構成可能である。これは、崩壊像が `L` に含まれると言っているだけである。像そのものが `L` の要素であるとは主張していない。前半が終わり、後半は新しいパラメータで始まる。要素の後者で閉じた段階 `lam` と、その要素がすべて段階の中にある始点 `X` である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Telescope (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The empty set lies in the stage as well, and the hull machinery is opened on these data: the hull carrier `M`, the fact that the hull is contained in the stage, and that every member of the start is a member of the hull.
<!--zh-->
空集也落在该层中；壳机制在这些数据上打开：壳载体 `M`、「壳包含于该层」以及「起点的每个成员都是壳的成员」。
<!--ja-->
空集合も段階の中にあり、包の機構がこれらのデータの上で開かれる。包の台 `M`、包が段階に含まれること、そして始点のすべての要素が包の要素であることである。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ
    using ( ∅∈Lsetα; hull-member; X⊆M; Hull⊆L )
  open HullStage.H.T lam ordλ succλ X X⊆L ∅∈λ public
```

<!--en-->
A hull code is either a base name for a member of `X`, or `wit k ψ cs`, which stores a constant-free formula and codes for its parameters. Its value is obtained by evaluating the subcodes and then, according as a witness exists, choosing the least witness or the junk value.
<!--zh-->
壳码或是起点成员的基础名，或是 `wit k ψ cs`，其中保存一条无常元公式及其参数的子码。先求出子码的值，再依是否存在见证，取最小见证或废弃值作为该码的值。
<!--ja-->
包の符号は、`X` の要素に対する基底名か、無定数公式とそのパラメータの符号を保存する `wit k ψ cs` である。部分符号を評価した後、証人が存在するかどうかに応じて、最小の証人または廃棄値をその値とする。
<!--/-->

```agda
    using ( Code; base; wit; val; vals; search; searchPredicate; Sat; Hull; val-wit
          ; satDecision )
  open HullStage.H.T lam ordλ succλ X X⊆L ∅∈λ using ( inHull; _⊨₀_ )
```

<!--en-->
The small carrier `SL` collects the members of the stage over which everything is typed. A parameter vector is drawn from a set `Z` when each of its components belongs to the underlying set of `Z`; the searches of the step range only over such vectors.
<!--zh-->
小载体 `SL` 收集所有命名与搜索所涉的层内成员。参数向量取自集合 `Z`，指每个分量都属于 `Z` 的底层集合；步进的搜索只在这样的向量上进行。
<!--ja-->
小さな台 `SL` は、すべてが型づけられる、段階の要素を集める。集合 `Z` から取ったパラメータのベクトルとは、各成分が `Z` の基礎の集合に属することである。ステップの探索はそのようなベクトルだけにわたる。
<!--/-->

```agda
  SL : Type (ℓ-suc ℓ)
  SL = HullStage.ASt.SL lam ordλ succλ X X⊆L ∅∈λ
  From : {k : ℕ} → CS.S → Vec SL k → Type (ℓ-suc ℓ)
  From {k} Z vs = (i : Fin k) → ⟨ fst (lookup i vs) ∈ˢ fst Z ⟩
  Searched : CS.S → S → Type (ℓ-suc ℓ)
```

<!--en-->
A search uses a constant-free formula of arity `k+1`. The vector from `Z` assigns its `k` parameter variables, while the remaining variable is assigned the candidate witness; `Sat` asserts that such a witness exists.
<!--zh-->
一次搜索使用元数为 `k+1` 的无常元公式。取自 `Z` 的向量给其中 `k` 个参数变元赋值，余下的变元由候选见证赋值；`Sat` 断言这样的见证存在。
<!--ja-->
探索にはアリティ `k+1` の無定数公式を使う。`Z` から取ったベクトルが `k` 個のパラメータ変数に値を与え、残る変数には候補となる証人を割り当てる。`Sat` はそのような証人の存在を表す。
<!--/-->

```agda
  Searched Z z = Σ[ k ∈ ℕ ] Σ[ ψ ∈ Formula (⊥* {ℓ}) (suc k) ] Σ[ vs ∈ Vec SL k ]
                 Σ[ w ∈ Sat k ψ vs ] (From Z vs × (z ≡ fst (search k ψ vs w)))
  Reads : CS.S → S → Type (ℓ-suc ℓ)
  Reads Z z = ⟨ z ∈ˢ fst Z ⟩ ⊎ ((z ≡ ∅) ⊎ Searched Z z)
```

<!--en-->
The package contains the operation `Φ`, a two-variable formula `ΦFo`, and a proof that for every `Z` the environment assigning `Φ Z` and `Z` to its two variables satisfies that formula.
<!--zh-->
该包包含运算 `Φ`、二变元公式 `ΦFo`，以及证明：对每个 `Z`，把两个变元分别赋值为 `Φ Z` 与 `Z` 的环境满足该公式。
<!--ja-->
この構造は、演算 `Φ`、二変数公式 `ΦFo`、そして任意の `Z` について二つの変数に `Φ Z` と `Z` を割り当てた環境がその公式を満たすという証明を含む。
<!--/-->

```agda
  record StepPack : Type (ℓ-suc (ℓ-suc ℓ)) where
    field
      Φ       : CS.S → CS.S
      ΦFo     : Formula CS.S 2
      defines : (Z : CS.S) → ⟨ (Φ Z ∷ Z ∷ []) ⊨ ΦFo ⟩
```

<!--en-->
The remaining fields pin the step down: any set satisfying the formula is the step's, members grow, the junk value is always present, and for every search at parameters from the current set the least witness is adjoined.
<!--zh-->
其余字段把步进钉死：任何满足该公式的集合都是步进之集；成员递增；废弃值总在；而对取自当前集合参数的每一次搜索，最小见证都被补入。
<!--ja-->
残りのフィールドがステップを確定させる。論理式を満たす集合はどれもステップの集合であり、要素は増え、廃棄値はつねにあり、現在の集合から取ったパラメータでのすべての探索に、最小の証人が加わる。
<!--/-->

```agda
      only    : (Z Z' : CS.S) → ⟨ (Z' ∷ Z ∷ []) ⊨ ΦFo ⟩ → Z' ≡ Φ Z
      grows   : (Z : CS.S) (z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ fst (Φ Z) ⟩
      junk    : (Z : CS.S) → ⟨ ∅ ∈ˢ fst (Φ Z) ⟩
      least   : (Z : CS.S) (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec SL k)
              → From Z vs → (w : Sat k ψ vs) → ⟨ fst (search k ψ vs w) ∈ˢ fst (Φ Z) ⟩
```

<!--en-->
The outward field reads a member of the step host-side, provided the current set lies below the stage: every member of the step is an old member, the junk value, or the value of a search. This reading is what the exhaustion proof will spend.
<!--zh-->
向外的字段在「当前集合低于该层」的前提下，从宿主一侧读取步进的成员：步进的每个成员都是旧成员、废弃值、或某次搜索的取值。穷尽性证明所要消耗的正是这条读法。
<!--ja-->
外向きのフィールドは、現在の集合が段階の下にあるとき、ステップの要素をホスト側で読む。ステップの要素は、古い要素、廃棄値、探索の値のいずれかである。使い尽くしの証明が使うのはこの読み出しである。
<!--/-->

```agda
      out     : (Z : CS.S) → ((z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              → (z : S) → ⟨ z ∈ˢ fst (Φ Z) ⟩ → ∥ Reads Z z ∥₁
```

<!--en-->
The iteration module takes the constructibility of the start together with the packaged step. Both are needed: the internal recursion begins at an element of `L`, and the step supplies the formula and its clauses.
<!--zh-->
迭代模块以「起点的可构造性」与打包好的步进为参数。两者缺一不可：内部递归从 `L` 的一个元素出发，而步进供给公式及其各子句。
<!--ja-->
反復のモジュールは、始点の構成可能性と、まとめられたステップを受け取る。どちらも必要である。内部の再帰は `L` の要素からはじまり、ステップが論理式とその条項を供給するからである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module HullIter (X-isL : ⟨ isL X ⟩) (P : StepPack) where
```
</summary>
<div class="submodule-fold-content">

```agda
    open StepPack P
```

<!--en-->
The start is presented as a carrier element, pairing the set with its constructibility; this is the form the internal recursion consumes.
<!--zh-->
起点被呈现为载体元素，即集合连同其可构造性；这正是内部递归所消费的形式。
<!--ja-->
始点は台の要素として提示される。集合とその構成可能性の組であり、内部の再帰が消費するのはこの形である。
<!--/-->

```agda
    Xʟ : CS.S
    Xʟ = X , X-isL
```

<!--en-->
The internal ω-recursion produces the iterates, and its closure machinery carries the growth field along: each iterate contains the previous one. The iterates are sets of the model, which is what will make their union an element of `L`.
<!--zh-->
内部 ω 递归产出诸迭代，其闭包机制把增长字段随身携带：每个迭代包含前一个。诸迭代是模型的集合，而这正是使诸迭代之并成为 `L` 元素的原因。
<!--ja-->
内部の ω 再帰が反復を作り、その閉包の機構が成長のフィールドを持ち運ぶ。それぞれの反復は前のものを含む。反復はモデルの集合であり、反復の合併が `L` の要素になるのはこのためである。
<!--/-->

```agda
    module It = Iterate Xʟ ΦFo Φ defines only
      using ( it; module Closure; iterUnion; iterUnion-in; iterUnion-out; iter; iter-in; iter-out; ω-num; Num )
    module Cl = It.Closure (λ Z z → grows Z (fst z)) using ( it-up )
```

<!--en-->
The stages of the iteration are named `hullStep n`, the `n`-th application of the step to the start.
<!--zh-->
迭代的各阶段被命名为 `hullStep n`，即步进对起点的第 `n` 次应用。
<!--ja-->
反復の各段階は `hullStep n` と名づけられる。始点に対するステップの `n` 回目の適用である。
<!--/-->

```agda
    hullStep : ℕ → CS.S
    hullStep = It.it
```

<!--en-->
The iteration is governed by its defining equation: applying the step `n+1` times produces exactly the one-step closure `Φ` applied to the `n`-th iterate. The equation holds by `refl`, because internal ω-recursion computes its successor stage by calling the step operation directly, and nothing needs to be transported. This is the arithmetic of the construction in its barest form: each layer of the telescope is the closure of the previous layer under the single definable step.
<!--zh-->
迭代由其定义等式支配：把步进应用 `n+1` 次，所得恰是把单步闭包 `Φ` 施于第 `n` 次迭代的结果。该等式由 `refl` 成立，因为内部 ω 递归在计算后继阶段时直接调用步进运算，无须任何搬运。这正是该构造最赤裸的算术：这一构造的每一层，就是前一层在单一可定义步进之下的闭包。
<!--ja-->
反復はその定義の等式に支配される。ステップを `n+1` 回適用して得られるものは、`n` 番目の反復に一段階の閉包 `Φ` を適用したものちょうどである。この等式は `refl` で成立する。内部の ω 再帰は、後者の段階を計算するときにステップの演算を直接呼ぶので、輸送は何も要らない。これが、この構成のもっとも裸の算術である。この構成のそれぞれの層は、前の層の、ただ一つの定義可能なステップの下での閉包である。
<!--/-->

```agda
    hullStep-suc : (n : ℕ) → hullStep (suc n) ≡ Φ (hullStep n)
    hullStep-suc n = refl
```

<!--en-->
The iterates grow with their index: if `n` does not exceed `n'`, then everything collected by the `n`-th iterate is still collected by the `n'`-th. The growth field of the step is applied once for each step of the difference, keeping the old members every time; the numeric equation carries the count, and the constructibility of the member travels with it, since it belongs to a constructible iterate. This monotonicity is what makes collection in an earlier iterate permanent.
<!--zh-->
迭代随其指标增长：若 `n` 不超过 `n'`，则第 `n` 个迭代所收集的一切仍被第 `n'` 个迭代收集。步进的增长字段沿差值逐次施加，每次都保留旧成员；数值等式搬运计数，而成员的可构造性随行，因为它属于某个可构造的迭代。这一单调性使「较早迭代中的收集」成为永久的性质。
<!--ja-->
反復はその添字とともに増える。`n` が `n'` を超えなければ、`n` 番目の反復が集めたものはすべて、`n'` 番目の反復も集める。ステップの成長のフィールドを差のぶんだけ繰り返し適用し、そのたびに古い要素は保たれる。数の等式が計数を運び、要素の構成可能性もそれとともに運ばれる。その要素は構成可能な反復に属するからである。この単調性により、早い段階で集められたものは、その後も収められたままになる。
<!--/-->

```agda
    hullStep-≤ : (n n' : ℕ) → n ≤ n' → (z : S)
               → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ fst (hullStep n') ⟩
    hullStep-≤ n n' (k , e) z h =
      subst (λ m → ⟨ z ∈ˢ fst (hullStep m) ⟩) e (Cl.it-up n k (z , zL) h)
      where
```

<!--en-->
Monotonicity of the iterates follows from the growth field: a member of an earlier iterate remains a member of every later one, and constructibility is carried along. Depth is assigned to hull codes by recursion: a base code has depth zero.

The witness code is one deeper than its code vector, because its value is computed one step after the values of the parameters.
<!--zh-->
迭代的单调性由增长字段而来：早前迭代的成员在之后每个迭代中仍是成员，且可构造性随行。壳码的深度由递归指定：基础码深度为零。

见证码比其码向量深一层，因为其取值在诸参数取值之后的下一步才计算。
<!--ja-->
反復の単調性は成長のフィールドから従う。前の反復の要素は、それ以降のすべての反復の要素であり、構成可能性も運ばれる。包の符号の深さは再帰で割り当てられる。base の符号の深さは零である。

証人の符号は、その符号のベクトルより一つ深い。その値は、パラメータの値の一歩あとの段階で計算されるからである。
<!--/-->

```agda
      zL : ⟨ isL z ⟩
      zL = isL-trans {x = fst (hullStep n)} {y = z} h (snd (hullStep n))
    mutual
      depth : Code → ℕ
      depth (base m) = 0
```

<!--en-->
The witness constructor adds one to the depth of its vector of subcodes.
<!--zh-->
见证构造子在其子码向量的深度上加一。
<!--ja-->
証人の構成子は、その子の符号のベクトルの深さに一を加える。
<!--/-->

```agda
      depth (wit k ψ cs) = suc (depths cs)
```

<!--en-->
The depth of a code vector is the maximum of the depths of its entries: a vector is available once all of its entries are.
<!--zh-->
码向量的深度是其各项深度的最大值：向量在其所有各项可得时即可用。
<!--ja-->
符号のベクトルの深さは、項目の深さの最大値である。ベクトルは、すべての項目が手に入れば使える。
<!--/-->

```agda
      depths : {m : ℕ} → Vec Code m → ℕ
      depths [] = 0
      depths (c ∷ cs) = max (depth c) (depths cs)
```

<!--en-->
A helper records how a case split on a decidable disjunction behaves when one disjunct is impossible: if satisfaction is empty, the computed value is the junk branch, whatever the other branch would have said.
<!--zh-->
一个辅助事实记录了「可判定析取的一支不可能时」情形分裂的行为：若满足为空，则计算出的取值是废弃分支，无论另一支本会说什么。
<!--ja-->
補助は、決定可能な選言の一方が不可能なときの、場合分けの振る舞いを記録する。充足が空なら、計算された値は廃棄の分岐であり、もう一方の分岐が何と言おうと変わらない。
<!--/-->

```agda
    private
      stuck-r : {A : Type (ℓ-suc ℓ)} (na : A → ⊥₀)
                (f : A → SL) (g : (A → ⊥₀) → SL) (s : Dec A)
              → decRec f g s ≡ g na
      stuck-r na f g (yes a) = ⊥₀-rec (na a)
```

<!--en-->
The refutation branch is proved by the function extensionality of the impossible function: no member exists to distinguish.
<!--zh-->
反驳分支由不可能函数的函数外延性证明：不存在任何成员可以区分二者。
<!--ja-->
反駁の分岐は、不可能な関数の関数外延性で証明される。区別するような要素は存在しないからである。
<!--/-->

```agda
      stuck-r na f g (no h) = cong g (funExt (λ a → ⊥₀-rec (na a)))
```

<!--en-->
Hull into union, first half: every hull code has its value staged at the iterate indexed by its depth. A base code names a member of the start, present at the zeroth iterate.
<!--zh-->
壳入并，前半：每个壳码的取值都安排在以其深度为索引的迭代处。基础码名指起点的成员，它在第零个迭代处已在。
<!--ja-->
包から合併へ、前半：すべての包の符号の値は、その深さで添字づけられた反復に用意される。base の符号は始点の要素を名指し、それは零番目の反復にある。
<!--/-->

```agda
    mutual
      hullStep-in : (c : Code) → ⟨ fst (val c) ∈ˢ fst (hullStep (depth c)) ⟩
      hullStep-in (base m) = member X m
      hullStep-in (wit k ψ cs) = go (satDecision k ψ (vals cs))
        where
```

<!--en-->
A witness code is split according to whether its search is satisfiable. Its depth is one more than the depth of its parameter-code vector, and the successor equation identifies that depth with the iterate obtained by applying `Φ` once more.
<!--zh-->
见证码按其搜索是否可满足分情况。它的深度比参数码向量的深度大一，而相继等式把这一深度处的迭代认作再施行一次 `Φ` 所得的迭代。
<!--ja-->
証人符号について、その探索が充足可能かどうかで場合分けする。その深さはパラメータ符号ベクトルの深さより一つ大きく、後続段階の等式により、その深さの反復は `Φ` をもう一度適用した反復と同一視される。
<!--/-->

```agda
        n : ℕ
        n = depths cs
        go : (s : Dec (Sat k ψ (vals cs)))
           → ⟨ fst (decRec (search k ψ (vals cs)) (λ _ → (∅ , HSH.∅∈Lsetα)) s)
                ∈ˢ fst (hullStep (suc n)) ⟩
```

<!--en-->
If the search is satisfied, the least-witness clause of the step adjoins the searched value at the next iterate, whose parameters are available by the vector depths. If the search is unsatisfiable, there is no witness to adjoin, and the step keeps the junk value instead.
<!--zh-->
若搜索被满足，步进的最小见证子句在下一个迭代处补入被搜索的值，其参数由向量深度可得。若搜索不可满足，则无见证可补，步进转而保留废弃值。
<!--ja-->
探索が充足されていれば、ステップの最小の証人の条項が、次の反復で探索された値を加える。そのパラメータはベクトルの深さによって手に入る。探索が充足されなければ、加える証人はなく、ステップは代わりに廃棄値を保つ。
<!--/-->

```agda
        go (yes w) = least (hullStep n) k ψ (vals cs) (vals-in cs) w
        go (no h) = junk (hullStep n)
```

<!--en-->
The parameters of a code vector are available at the maximum of the entry depths: each entry's value appeared at its own depth, and monotonicity carries it to the later iterate where the vector is consumed.
<!--zh-->
码向量的参数在各条目深度的最大值处可得：每项取值都在其自身深度处出现，单调性把它运到消耗该向量的更晚迭代。
<!--ja-->
符号のベクトルのパラメータは、項目の深さの最大値で手に入る。各項目の値はそれぞれの深さで現れ、単調性がそれを、ベクトルを消費するより後の反復へ運ぶ。
<!--/-->

```agda
      vals-in : {m : ℕ} (cs : Vec Code m) → From (hullStep (depths cs)) (vals cs)
      vals-in (c ∷ cs) zero =
        hullStep-≤ (depth c) (max (depth c) (depths cs)) left-≤-max (fst (val c)) (hullStep-in c)
      vals-in (c ∷ cs) (suc i) =
        hullStep-≤ (depths cs) (max (depth c) (depths cs)) right-≤-max
```

<!--en-->
The choice proceeds recursively over the parameter vector. For the empty vector, the empty code vector has the required value vector; at a nonempty vector, hull membership supplies a code for the head and recursion supplies codes for the tail.
<!--zh-->
该选取沿参数向量递归进行。对空向量，空码向量的值向量正合要求；对非空向量，头项的壳成员资格给出它的码，递归则给出尾部各项的码。
<!--ja-->
この選択はパラメータベクトルについて再帰する。空ベクトルでは空の符号ベクトルの値ベクトルが条件を満たす。空でない場合は、先頭の包への所属からその符号を得て、尾部の符号を再帰的に得る。
<!--/-->

```agda
          (fst (lookup i (vals cs))) (vals-in cs i)
    private
      choose : {k : ℕ} (vs : Vec SL k)
             → ((i : Fin k) → ⟨ fst (lookup i vs) ∈ˢ Hull ⟩)
             → ∥ Σ[ cs ∈ Vec Code k ] (vals cs ≡ vs) ∥₁
```

<!--en-->
The recursive step codes the head by hull membership and the tail recursively; the value equation is assembled componentwise, with the carrier equality reduced to the underlying sets.
<!--zh-->
递归步进为头部按壳成员资格取码、为尾部递归取码；取值方程按分量装配，其中载体的相等化归为底层集合的相等。
<!--ja-->
帰納のステップは、先頭を包の要素として符号化し、尾を帰納的に符号化する。値の等式は成分ごとに組み立てられ、台の等しさは基礎の集合の等しさへ帰着する。
<!--/-->

```agda
      choose [] h = ∣ [] , refl ∣₁
      choose (v ∷ vs) h = rec₁ squash₁ (λ { (c , ec) → map₁
        (λ { (cs , ecs) → (c ∷ cs)
           , cong₂ _∷_ (Σ≡Prop (λ z → snd (z ∈ˢ Lset lam)) ec) ecs })
        (choose vs (λ i → h (suc i))) })
```

<!--en-->
For a code vector `cs`, `val-wit` identifies the value of `wit k ψ cs` with the least witness returned by the search. Since every code value belongs to the hull, the searched value belongs to the hull.
<!--zh-->
对码向量 `cs`，`val-wit` 把 `wit k ψ cs` 的值与搜索返回的最小见证等同。由于每个码的值都属于壳，该搜索值也属于壳。
<!--ja-->
符号ベクトル `cs` に対し、`val-wit` は `wit k ψ cs` の値を探索が返す最小の証人と同一視する。すべての符号の値は包に属するので、探索値も包に属する。
<!--/-->

```agda
        (HSH.hull-member (fst v) (h zero))
      search-val : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k) (vs : Vec SL k)
                 → vals cs ≡ vs → (w : Sat k ψ vs) → ⟨ fst (search k ψ vs w) ∈ˢ Hull ⟩
      search-val k ψ cs vs e w =
        J (λ vs' e' → (w' : Sat k ψ vs') → ⟨ fst (search k ψ vs' w') ∈ˢ Hull ⟩)
```

<!--en-->
The path induction transports the statement along the identification of the parameter vectors, and the witness code is judged inside the hull.
<!--zh-->
路径归纳沿参数向量之间的同定搬运该陈述，而见证码在壳内受判。
<!--ja-->
パスの帰納が、パラメータのベクトルの同定に沿って主張を運び、証人の符号は包の内側で判定される。
<!--/-->

```agda
          (λ w' → subst (λ z → ⟨ fst z ∈ˢ Hull ⟩) (val-wit k ψ cs w') (inHull (wit k ψ cs)))
          e w
```

<!--en-->
The code `wit 0 ⊥̇ []` has no satisfying witness, so its value follows the failure branch and is `∅`. As every code value lies in the hull, the junk value lies there as well.
<!--zh-->
码 `wit 0 ⊥̇ []` 没有满足见证，因此其值走失败分支并等于 `∅`。每个码的值都在壳中，所以废弃值也在壳中。
<!--ja-->
符号 `wit 0 ⊥̇ []` には充足する証人がないため、その値は失敗側の分岐を通って `∅` になる。すべての符号の値は包に属するので、廃棄値も包に属する。
<!--/-->

```agda
      junk∈Hull : ⟨ ∅ ∈ˢ Hull ⟩
      junk∈Hull = subst (λ z → ⟨ fst z ∈ˢ Hull ⟩)
        (stuck-r unsat (search 0 ⊥̇ []) (λ _ → (∅ , HSH.∅∈Lsetα))
          (satDecision 0 ⊥̇ []))
        (inHull (wit 0 ⊥̇ []))
        where
```

<!--en-->
No environment satisfies falsity: unpacking such a satisfaction proof would produce an element of the empty type.
<!--zh-->
没有环境满足假式：展开这样的满足证明会得到空类型的元素。
<!--ja-->
偽を満たす環境はない。そのような充足の証明を展開すると、空型の要素が得られてしまう。
<!--/-->

```agda
        unsat : Sat 0 ⊥̇ [] → ⊥₀
        unsat = rec₁ isProp⊥ (λ { (a , h) → ⊥*-rec h })
```

<!--en-->
Union into hull, second half: every member of every iterate lies in the hull, by induction on the iterate index. The base case is the start, whose members are hull members by the hull chapter.
<!--zh-->
并入壳，后半：每个迭代的每个成员都在壳内，对迭代指标归纳。基础情形是起点，其成员由壳章即是壳成员。
<!--ja-->
合併から包へ、後半：すべての反復のすべての要素が包の中にある。反復の添字についての帰納である。基底の場合は始点であり、その要素は包の章によって包の要素である。
<!--/-->

```agda
    hullStep⊆Hull : (n : ℕ) (z : S) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ Hull ⟩
    hullStep⊆Hull zero z h = HSH.X⊆M z h
    hullStep⊆Hull (suc n) z h = rec₁ (snd (z ∈ˢ Hull)) read
      (out (hullStep n) (λ z' hz' → HSH.Hull⊆L z' (hullStep⊆Hull n z' hz')) z h)
      where
```

<!--en-->
The step case reads a member of the successor iterate through the outward clause: it is an old member, already in the hull by the induction hypothesis; it is the junk value, already in the hull; or it is a searched value, handled next.
<!--zh-->
步进情形经向外子句读取后继迭代的成员：它是旧成员，由归纳假设已在壳内；是废弃值，已在壳内；或是被搜索的值，交由下一步处理。
<!--ja-->
ステップの場合は、外向きの条項を通して、後者の反復の要素を読む。それは古い要素であり、帰納の仮定によってすでに包の中にある。廃棄値でもあり、すでに包の中にある。あるいは探索された値で、つぎに扱われる。
<!--/-->

```agda
      read : Reads (hullStep n) z → ⟨ z ∈ˢ Hull ⟩
      read (inl h') = hullStep⊆Hull n z h'
      read (inr (inl e)) = subst (λ t → ⟨ t ∈ˢ Hull ⟩) (sym e) junk∈Hull
      read (inr (inr (k , ψ , vs , w , from , e))) =
        subst (λ t → ⟨ t ∈ˢ Hull ⟩) (sym e)
```

<!--en-->
A searched value is matched with the code vector of its parameters, each parameter being a hull member by the induction hypothesis; the search then lies in the hull by `search-val`, and the equation transports that membership to `z`. The union of the iterates is named as the element of `L` presenting the hull.
<!--zh-->
被搜索的值与其参数的码向量相匹配，每个参数由归纳假设是壳成员；于是该搜索经 `search-val` 落在壳内，等式再把这一成员资格运给 `z`。诸迭代的并被命名为呈现壳的 `L` 元素。
<!--ja-->
探索された値は、そのパラメータの符号のベクトルと対応づけられ、各パラメータは帰納の仮定によって包の要素である。だから探索は `search-val` によって包の中にあり、等式がその所属を `z` へ運ぶ。反復の合併が、包を提示する `L` の要素として名づけられる。
<!--/-->

```agda
          (rec₁ (snd (fst (search k ψ vs w) ∈ˢ Hull))
            (λ { (cs , ecs) → search-val k ψ cs vs ecs w })
            (choose vs (λ i → hullStep⊆Hull n (fst (lookup i vs)) (from i))))
    hullL : CS.S
    hullL = It.iterUnion
```

<!--en-->
The hull as an element of `L` is the union of the iterates, and its membership description says its members are exactly the hull members. Forward: a member of the union lies at some iterate, hence in the hull.
<!--zh-->
作为 `L` 元素的壳是诸迭代的并，其隶属描述说它的成员恰是壳的成员。向前：并的成员落在某个迭代处，故在壳内。
<!--ja-->
`L` の要素としての包は、反復の合併であり、その所属の記述は、要素がちょうど包の要素であると言う。前向き：合併の要素はある反復に属し、だから包の中にある。
<!--/-->

```agda
    hullL-spec : fst hullL ≡ Hull
    hullL-spec = extensionalV {a = fst hullL} {b = Hull} (λ z → ⇔toPath (fwd z) (bwd z))
      where
      fwd : (z : S) → ⟨ z ∈ˢ fst hullL ⟩ → ⟨ z ∈ˢ Hull ⟩
      fwd z h = rec₁ (snd (z ∈ˢ Hull))
```

<!--en-->
The iterate index is consumed by the outward reading of the union, and the constructibility of the member is carried from the union, itself constructible by construction.
<!--zh-->
迭代指标由并的向外读法消去，成员的可构造性则由这个并继承；该并依构造即为可构造集合。
<!--ja-->
反復の添字は、合併の外向きの読み出しに消費され、要素の構成可能性は合併から運ばれる。合併そのものが、構成によって構成可能なのである。
<!--/-->

```agda
        (λ { (n , hn) → hullStep⊆Hull n z hn })
        (It.iterUnion-out (z , isL-trans {x = fst hullL} {y = z} h (snd hullL)) h)
```

<!--en-->
Backward: a hull member is named by a code, whose value appears at the iterate indexed by the code's depth; the inward reading of the union admits it.
<!--zh-->
向后：壳成员由某个码名指，其取值出现在以该码深度为索引的迭代处；并的向内读式接纳它。
<!--ja-->
後ろ向き：包の要素はある符号に名指され、その値は、符号の深さで添字づけられた反復に現れる。合併の内向きの読み出しがそれを受け入れる。
<!--/-->

```agda
      bwd : (z : S) → ⟨ z ∈ˢ Hull ⟩ → ⟨ z ∈ˢ fst hullL ⟩
      bwd z h = rec₁ (snd (z ∈ˢ fst hullL))
        (λ { (c , ec) → It.iterUnion-in (depth c) zS
               (subst (λ t → ⟨ t ∈ˢ fst (hullStep (depth c)) ⟩) ec (hullStep-in c)) })
        (HSH.hull-member z h)
```

<!--en-->
The named member is carried into the carrier: its constructibility follows from the hull being contained in the stage, whose element presentation supplies the certificate.
<!--zh-->
被名指的成员被载入载体：其可构造性由「壳包含于该层」而来，而该层的元素呈现供给了证书。
<!--ja-->
名指された要素は台の中へ載せられる。その構成可能性は、包が段階に含まれることから従い、段階の要素としての提示が証明書を供給する。
<!--/-->

```agda
        where
        zS : CS.S
        zS = z , Lset→isL lam ordλ z (HSH.Hull⊆L z h)
```

<!--en-->
The equality of underlying sets transports the union's constructibility onto the hull: the hull is an element of `L`. The first half of the chapter is now discharged in full, and the second module builds the definable step whose iteration was just consumed.

The step is built inside the stage, and its constants name objects of the stage: ordinality of `lam` comes from being an ordinal.
<!--zh-->
底层集合的相等把并的可构造性传递给壳：壳是 `L` 的元素。本章前半至此全部清偿，第二个模块则建造刚才被迭代所消费的可定义步进。

步进在该层内部建造，其常元名指该层的对象：`lam` 的可构造性由「`lam` 是序数」而来。
<!--ja-->
基礎の集合の等しさが、合併の構成可能性を包の上へ運ぶ。包は `L` の要素である。本章の前半はこれで完全に清算され、第二のモジュールは、今消費された定義可能なステップを作る。

ステップは段階の内側で作られ、その定数は段階の対象を名指す。`lam` の構成可能性は、`lam` が順序数であることから来る。
<!--/-->

```agda
    M-isL : ⟨ isL HS.M ⟩
    M-isL = subst (λ t → ⟨ isL t ⟩) hullL-spec (snd hullL)
```
</div>
</details>

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Build where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
An ordinal of the hierarchy is constructible, which anchors the stage inside `L`.
<!--zh-->
层级的序数可构造，这把该层锚定在 `L` 之内。
<!--ja-->
階層の順序数は構成可能であり、これが段階を `L` の内側に固定する。
<!--/-->

```agda
    λ-isL : ⟨ isL lam ⟩
    λ-isL = isL-ord lam ordλ
```

<!--en-->
`A` presents `Lset lam` together with its constructibility proof. It is the stage parameter used by the satisfaction graph and the coding of formulas over the stage.
<!--zh-->
`A` 把 `Lset lam` 连同其可构造性证明呈现为模型元素；满足图以及该层上的公式编码都以它为层参数。
<!--ja-->
`A` は `Lset lam` をその構成可能性の証明とともにモデルの要素として表す。充足グラフと段階上の公式の符号化は、これを段階のパラメータとして用いる。
<!--/-->

```agda
    A : CS.S
    A = LsetS lam ordλ
```

<!--en-->
The satisfaction graph over the stage supplies the satisfaction sets of all codes at once, with both readings; and definability over the stage interprets the constants of formulas as elements of the stage.
<!--zh-->
该层上的满足图一次性供给所有码的满足集，连同两条读式；层上的可定义性把公式的常元解释为层的元素。
<!--ja-->
段階の上の充足のグラフは、すべての符号の充足集合を、二つの読み出しとともに一度に供給する。そして段階の上の定義可能性が、論理式の定数を段階の要素として解釈する。
<!--/-->

```agda
    module SM = SatGraph A using ( pairs; pairs-in; pairs-out; valOf; valOf≡ )
    module DA = DefOf (Lset lam) using ( ι; _⊨ᵐ_; 𝒮M )
```

<!--en-->
The code set at the empty alphabet collects the codes of the parameter-free formulas. Such formulas may have free variables; what they lack is constants, and the free variables will be assigned by the parameter environments of the searches.
<!--zh-->
空字母表处的码集收集无常元公式的码。这些公式可以带有自由变量；它们缺少的是常元，而自由变量将由搜索的参数环境赋值。
<!--ja-->
空のアルファベットでの符号の集合は、無定数の論理式の符号を集める。そのような論理式は自由変数をもつことがある。欠けているのは定数であり、自由変数に値を与えるのは、探索のパラメータ環境である。
<!--/-->

```agda
    C₀ : CS.S
    C₀ = AllCodes ∅ʟ
```

<!--en-->
The stage's internal well-order is presented as an element of the model, the relation by which least witnesses will be compared.
<!--zh-->
该层的内部良序被呈现为模型的元素，即比较最小见证所用的关系。
<!--ja-->
段階の内部の整列順序は、モデルの要素として提示される。最小の証人を比較するための関係である。
<!--/-->

```agda
    Rel : CS.S
    Rel = relL lam λ-isL ordλ
```

<!--en-->
The strict well-order on the small carrier is read from that relation; its comparison is stated on carrier elements. The second component of a constructible ordered pair is again constructible, which the parameters of names will need.
<!--zh-->
小载体上的严格良序由该关系读取；其比较在载体元素上陈述。可构造有序对的第二分量也可构造，这正是一会儿名字的参数所需要的。
<!--ja-->
小さな台の上の狭義の整列順序は、その関係から読まれ、比較は台の要素の上で述べられる。構成可能な順序対の第二成分もまた構成可能であり、これが、のちの名前のパラメータに必要になる。
<!--/-->

```agda
    wL : SWO SL
    wL = orderAt lam ordλ
    relOf-at : SL → SL → Type (ℓ-suc ℓ)
    relOf-at = relOf wL
    pr-snd-isL : (a b : V ℓ) → ⟨ isL (pr a b) ⟩ → ⟨ isL b ⟩
```

<!--en-->
The proof peels the ordered pair twice through singletons: membership in a pair puts the second component inside a singleton-pair nesting, and each peeling keeps constructibility by transitivity.
<!--zh-->
证明经由单点集把有序对剥开两次：属于一对把第二分量放进「单点集-对」的嵌套中，而每次剥开都由传递性保持可构造性。
<!--ja-->
証明は、順序対を一元集合を通して二度剥がす。対への所属は第二成分を「一元集合と対」の入れ子の中に置き、それぞれの剥離が、推移性によって構成可能性を保つ。
<!--/-->

```agda
    pr-snd-isL a b h =
      isL-trans {x = ⁅ a , b ⁆} {y = b} (subst ⟨_⟩ (sym (pair-spec a b b)) ∣ inr refl ∣₁)
        (isL-trans {x = pr a b} {y = ⁅ a , b ⁆}
          (subst ⟨_⟩ (sym (pair-spec ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆)) ∣ inr refl ∣₁) h)
```

<!--en-->
Numerals are presented as carrier elements: the finite ordinal together with its constructibility, which the key clause of the witness formula will quantify over.
<!--zh-->
数码被呈现为载体元素：有限序数连同其可构造性，见证公式的键子句将对它们量化。
<!--ja-->
数項は台の要素として提示される。有限の順序数とその構成可能性であり、証人の論理式のキーの条項がこれを量化する。
<!--/-->

```agda
    nn : ℕ → CS.S
    nn k = # k , numL k
```

<!--en-->
Because the constant alphabet is empty, there is a unique interpretation `ε′` into the stage carrier. It allows a constant-free formula to be relabeled into the stage language without making any choices.
<!--zh-->
由于常元字母表为空，存在唯一的解释 `ε′` 映入该层载体。借此可把无常元公式改名到该层语言中，而无须作任何选择。
<!--ja-->
定数のアルファベットは空なので、段階の台への解釈 `ε′` は一意である。これにより、何も選択せずに無定数公式を段階の言語へ付け替えられる。
<!--/-->

```agda
    ε′ : ⊥* {ℓ} → ⟪ Lset lam ⟫
    ε′ = ⊥*-rec
    sat-bridge : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) (δ : SL ^ k)
               → (δ ⊨₀ χ) ≡ (δ DA.⊨ᵐ mapFo ε′ χ)
    sat-bridge k χ δ =
```

<!--en-->
The bridge is a composition: the environments of the empty alphabet agree trivially because there is nothing to interpret, and the relabeling theorem identifies the external satisfaction of the relabeled formula with the stage's internal satisfaction.
<!--zh-->
这座桥是一个复合：空字母表的环境平凡地相合，因为并无常元需要解释；而改名定理把「改名后公式的外部满足」与「层内部满足」等同。
<!--ja-->
この橋は合成である。空のアルファベットの環境は、解釈すべきものがないため、自明に一致する。そして改名の定理が、改名された論理式の外側の充足と、段階の内側の充足とを同一視する。
<!--/-->

```agda
        cong (λ κ → FOL.Semantics.At._⊨_ DA.𝒮M (⊥* {ℓ}) κ δ χ)
          (funExt (λ b → ⊥*-rec b))
      ∙ sym (⊨-map DA.𝒮M ε′ DA.ι χ δ)
    opaque
      keyOf : (k : ℕ) → Formula (⊥* {ℓ}) k → CS.S
```

<!--en-->
The key of a parameter-free formula at the stage is the key of its relabeled form in the stage's code set. It is named once, so that later statements can mention it without reopening its construction.
<!--zh-->
一条无常元公式在该层的键，是其改名后的形在该层码集中的键。它只命名一次，使后文各陈述可以提到它而不重新打开其构造。
<!--ja-->
無定数の論理式の、段階でのキーとは、改名された形の、段階の符号の集合でのキーである。一度だけ名づけられ、以後の主張はその構成を開かずに参照できる。
<!--/-->

```agda
      keyOf k χ = keyS A (mapFo ε′ χ)
```

<!--en-->
The key belongs to the code set at the stage: a code of the relabeled formula is a code over the stage's alphabet, and the code set contains all of them.
<!--zh-->
该键属于该层处的码集：改名后公式的码是该层字母表上的码，而码集把它们尽数包含。
<!--ja-->
そのキーは、段階での符号の集合に属する。改名された論理式の符号は、段階のアルファベットの上の符号であり、符号の集合はそれらをすべて含む。
<!--/-->

```agda
      keyOf∈ : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) → ⟨ keyOf k χ CS.∈ˢ AllCodes A ⟩
      keyOf∈ k χ = key∈AllCodes A (mapFo ε′ χ)
```

<!--en-->
Although `keyOf` is opaque, the lemma `keyOf≡` exposes the exact equation with `keyS A (mapFo ε′ χ)`. Later proofs use this equation without unfolding the sealed definition.
<!--zh-->
虽然 `keyOf` 是不透明定义，引理 `keyOf≡` 明确给出它与 `keyS A (mapFo ε′ χ)` 的等式。后续证明可使用该等式，而不展开封存的定义。
<!--ja-->
`keyOf` は不透明であるが、補題 `keyOf≡` が `keyS A (mapFo ε′ χ)` との正確な等式を公開する。以後の証明は、封印された定義を展開せずにこの等式を使える。
<!--/-->

```agda
      keyOf≡ : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) → keyOf k χ ≡ keyS A (mapFo ε′ χ)
      keyOf≡ k χ = refl
```

<!--en-->
The underlying set of the sealed key is computed: it is the ordered pair of the numeral of the arity with the code of the relabeled formula. The proof composes the two relabelings of the formula, the empty alphabet followed by the stage's embedding, and the relabeling theorem identifies the result with the code the limit level records.
<!--zh-->
封存键的底层集合被算出：它是「元数的数码与改名后公式的码」组成的有序对。证明复合了公式的两次改名，先经空字母表、再经该层的嵌入，而改名定理把结果与极限层所记录的码等同。
<!--ja-->
封印されたキーの基礎の集合が計算される。それは、アリティの数項と、改名された論理式の符号との順序対である。証明は、論理式の二つの改名を合成する。空のアルファベットを経て、段階の埋め込みへ続くものである。改名の定理が、結果を極限段階が記録する符号と同一視する。
<!--/-->

```agda
      keyOf-fst : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
                → fst (keyOf k χ) ≡ pr (# k) (fst (limitCode χ))
      keyOf-fst k χ = cong (pr (# k)) (cong VCode.⌜_⌝
        ( mapFo-comp ε′ ⟪ Lset lam ⟫↪ χ
        ∙ cong (λ f → mapFo f χ) (funExt (λ b → ⊥*-rec b)) ))
```

<!--en-->
For each parameter-free formula, `Tof` is the satisfaction set selected by the satisfaction graph at the formula's sealed key. This fixed set represents satisfaction of that formula throughout the stage.
<!--zh-->
对每条无参公式，`Tof` 是满足图在该公式封存键处选出的满足集。这个固定集合在整个层中表示该公式的满足关系。
<!--ja-->
各無パラメータ論理式に対し、`Tof` は充足のグラフがその論理式の封印されたキーで選ぶ充足集合である。この固定した集合が、段階全体でその論理式の充足関係を表す。
<!--/-->

```agda
    Tof : (k : ℕ) → Formula (⊥* {ℓ}) k → CS.S
    Tof k χ = SM.valOf (keyOf k χ) (keyOf∈ k χ)
```

<!--en-->
The ordered pair of the key and its satisfaction set belongs to the satisfaction graph. Moreover, any carrier element with the same underlying set as the key selects the same satisfaction set: their constructibility witnesses are propositions, so equality of the underlying sets lifts to equality in the carrier and hence to equality of the selected values.
<!--zh-->
键与其满足集组成的有序对属于满足图。此外，任何与该键具有相同底层集合的载体元素都会选出同一满足集：其可构造性见证都是命题，所以底层集合的相等可提升为载体中的相等，继而得到所选取值的相等。
<!--ja-->
キーとその充足集合との順序対は、充足のグラフに属する。さらに、キーと同じ基礎集合をもつ台の要素は同じ充足集合を選ぶ。構成可能性の証明は命題なので、基礎集合の等しさが台での等しさへ持ち上がり、したがって選ばれた値も等しくなる。
<!--/-->

```agda
    Tof-pair : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
             → ⟨ pr (fst (keyOf k χ)) (fst (Tof k χ)) ∈ˢ fst SM.pairs ⟩
    Tof-pair k χ = SM.pairs-in (keyOf k χ) (keyOf∈ k χ)
    valOf-same : (x : CS.S) (m : ⟨ x CS.∈ˢ AllCodes A ⟩) (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
               → fst x ≡ fst (keyOf k χ) → SM.valOf x m ≡ Tof k χ
```

<!--en-->
The proof runs by path induction on the equation of underlying sets, with the propositionality of code-set membership absorbing the difference of membership proofs. Only the underlying sets matter, so the transport is silent about everything else.
<!--zh-->
证明沿底层集合等式作路径归纳，而码集隶属的命题性吸收了隶属证明之间的差异。起作用的只有底层集合，因此运输对其余一切保持沉默。
<!--ja-->
証明は、基礎の集合の等式の上のパス帰納で進む。符号集合への所属の命題性が、所属の証明の違いを吸収する。大切なのは基礎の集合だけなので、輸送はそのほかの何ものにも触れない。
<!--/-->

```agda
    valOf-same x m k χ e =
      J (λ x' e' → (m' : ⟨ x' CS.∈ˢ AllCodes A ⟩) → SM.valOf x m ≡ SM.valOf x' m')
        (λ m' → cong (SM.valOf x) (snd (x CS.∈ˢ AllCodes A) m m'))
        (S≡ {x = x} {y = keyOf k χ} e) (keyOf∈ k χ)
    sat-at : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) (δ : SL ^ k) (z : CS.S)
```

<!--en-->
Membership in a satisfaction set is now computed as the stage's own satisfaction. The bridge composes three identifications: the sealed name agrees with the key it was built from; the value at the key is read externally by the uniform satisfaction theorem; and the external satisfaction of the relabeled formula is the stage's internal satisfaction by the relabeling bridge.
<!--zh-->
「属于一个满足集」此刻被算成层自身的满足。这座桥复合三个同认：封存的名字与其所自的键一致；键处的取值由一致满足定理向外部读取；而改名后公式的外部满足，经改名桥即层内部满足。
<!--ja-->
充足集合への所属が、ここで段階自身の充足として計算される。この橋は三つの同定を合成する。封印された名前は、その作られたキーと一致すること。キーでの値は、一様な充足の定理によって外側の充足として読めること。そして改名された論理式の外側の充足が、改名の橋によって段階の内側の充足に等しいことである。
<!--/-->

```agda
           → fst z ≡ graph A δ → (z CS.∈ˢ Tof k χ) ≡ (δ ⊨₀ χ)
    sat-at k χ δ z qz =
        cong (z CS.∈ˢ_) (SM.valOf≡ (keyOf k χ) (keyOf∈ k χ))
      ∙ val-sat A (mapFo ε′ χ) (keyOf k χ) (keyOf∈ k χ) (cong fst (keyOf≡ k χ)) δ z qz
      ∙ sym (sat-bridge k χ δ)
```

<!--en-->
The key recognizer is a formula. It says that the value in slot `s` belongs to the stage's code set and is the ordered pair of the successor of the numeral in slot `a` with some code. Thus, when slot `a` contains `# k`, it recognizes a key of arity `k+1` for a parameter-free formula. Parameter-free here means that the constant domain is empty; the formula may still have free variables.
<!--zh-->
键识别式是一条公式。它断言槽位 `s` 的值属于该层的码集，并且对某个码，它是槽位 `a` 中数码的后继与该码组成的有序对。因此，当槽位 `a` 含有 `# k` 时，它识别一条元数为 `k+1` 的无参公式之键。这里「无参」表示常元域为空；公式仍可有自由变元。
<!--ja-->
キーの認識式は、枠 `s` の値がこの段階の符号集合に属し、ある符号との間で、枠 `a` にある数項の後者とその符号との順序対になっている、と述べる。したがって、枠 `a` が `# k` を含むとき、これはアリティ `k+1` の無パラメータ論理式のキーを認識する。ここで無パラメータとは定数域が空であるという意味で、論理式は自由変数をもちえる。
<!--/-->

```agda
    opaque
      keyIn : ∀ {n} → Fin n → Fin n → Formula CS.S n
      keyIn s a = (var s ∈̇ con C₀)
                ∧̇ ∃̇ ( sucAtL (suc a) zero
                     ∧̇ ∃̇ (prAtL (suc (suc s)) (suc zero) zero) )
```

<!--en-->
The readings are stated at a variable environment, for a fixed arity `k` whose numeral is named at slot `a`. Fixing the arity in advance is what makes the two readings equations about codes rather than searches through them.
<!--zh-->
两条读式在变元环境处陈述，针对固定的元数 `k`，其数码已被记在槽位 `a` 处。预先固定元数，正是使两条读式成为关于码的等式、而非在码中搜寻的原因。
<!--ja-->
読み出しは、変数の環境の上で、固定したアリティ `k` に対して述べられる。その数項は枠 `a` に名指されている。アリティをはじめに固定するからこそ、二つの読み出しは、符号の中を探すのではなく、符号についての等式になるのである。
<!--/-->

```agda
    module KeyIn {n : ℕ} (s a : Fin n) (γ : CS.S ^ n) (k : ℕ)
                 (qa : fst (lookup a γ) ≡ # k) where
```

<!--en-->
The formula is opened for computation at its own slots, since the readings must compute through the conjunctions and existentials of the definition.
<!--zh-->
该公式在其自身槽位处被开启以供计算，因为两条读式必须穿过定义中的合取与存在量词。
<!--ja-->
論理式は、その自分の枠の上で計算のために開かれる。読み出しが、定義の連言と存在量化子を通り抜けなければならないからである。
<!--/-->

```agda
      opaque
        unfolding keyIn
```

<!--en-->
The introduction builds the satisfaction from three data: the code-set membership of `s`, an element `c` of the hierarchy, and the equation identifying `s` with the pair of the successor numeral and `c`. The numeral, the successor clause and the pair clause are filled in order.
<!--zh-->
引入由三个数据建成满足：`s` 的码集隶属、层级的一个元素 `c`，以及把 `s` 同认于「后继数码与 `c` 之对」的等式。数码、后继子句与对子句依次填入。
<!--ja-->
導入は、三つのデータから充足を作る。`s` の符号集合への所属、階層の要素 `c`、そして `s` を「後者の数項と `c` の対」と同定する等式である。数項、後者の条項、対の条項が、この順で満たされる。
<!--/-->

```agda
        keyIn-in : ⟨ fst (lookup s γ) ∈ˢ fst C₀ ⟩ → (c : V ℓ)
                 → fst (lookup s γ) ≡ pr (# (suc k)) c → ⟨ γ ⊨ keyIn s a ⟩
        keyIn-in h c q = h , ∣ numAt , ( hsuc , ∣ cS , hpr ∣₁ ) ∣₁
          where
          numAt : CS.S
```

<!--en-->
The numeral is presented as a carrier element, and the code `c` is lifted to one as well. From the equation identifying `s` with the ordered pair and from the constructibility of `s`, `pr-snd-isL` extracts the constructibility of the pair's second component `c`.
<!--zh-->
数码被呈现为载体元素，码 `c` 也被提升为载体元素。由把 `s` 同认于该有序对的等式以及 `s` 的可构造性，`pr-snd-isL` 推出有序对第二分量 `c` 的可构造性。
<!--ja-->
数項は台の要素として提示され、符号 `c` も台の要素へ持ち上げられる。`s` をその順序対と同定する等式と `s` の構成可能性から、`pr-snd-isL` は順序対の第二成分 `c` の構成可能性を取り出す。
<!--/-->

```agda
          numAt = nn (suc k)
          cS : CS.S
          cS = c , pr-snd-isL (# (suc k)) c
                     (subst (λ u → ⟨ isL u ⟩) q (isL-trans h (snd C₀)))
          hsuc : ⟨ (numAt ∷ γ) ⊨ sucAtL (suc a) zero ⟩
```

<!--en-->
The successor clause is transported from the equation of the numeral at slot `a`, and the pair clause from the equation of `s`, each through the adequacy of its coding operator. Both transports are exactly what converts host equations into satisfaction.
<!--zh-->
后继子句由槽位 `a` 处数码的等式运输而来，对子句由 `s` 的等式运输而来，各经其编码算子的充分性。这两次运输恰是把宿主等式转成满足的过程。
<!--ja-->
後者の条項は、枠 `a` の数項の等式から、対の条項は `s` の等式から、それぞれその符号化の演算子の妥当性を通して運ばれる。この二つの輸送こそ、ホストの等式を充足へ変えるものである。
<!--/-->

```agda
          hsuc = subst ⟨_⟩ (sym (sucAtL-adequate (suc a) zero (numAt ∷ γ)))
            (cong sucV (sym qa))
          hpr : ⟨ (cS ∷ numAt ∷ γ) ⊨ prAtL (suc (suc s)) (suc zero) zero ⟩
          hpr = subst ⟨_⟩
            (sym (prAtL-adequate (suc (suc s)) (suc zero) zero (cS ∷ numAt ∷ γ))) q
```

<!--en-->
The elimination recovers the two data: the code-set membership of `s`, and the truncated statement that `s` is the pair of the successor numeral with some code. The existential chain of the formula is unpacked step by step.
<!--zh-->
消去收回两条数据：`s` 的码集隶属，以及「`s` 是后继数码与某个码之对」的截断陈述。公式的存在链被逐步拆开。
<!--ja-->
消去は、二つのデータを取り戻す。`s` の符号集合への所属と、「`s` は後者の数項とある符号の対である」という切り詰められた主張である。論理式の存在の連鎖が、一歩ずつほどかれる。
<!--/-->

```agda
        keyIn-out : ⟨ γ ⊨ keyIn s a ⟩
                  → ⟨ fst (lookup s γ) ∈ˢ fst C₀ ⟩
                  × ∥ Σ[ c ∈ V ℓ ] (fst (lookup s γ) ≡ pr (# (suc k)) c) ∥₁
        keyIn-out (h , hk) = h , rec₁ squash₁ atNum hk
          where
```

<!--en-->
The intermediate binder names the numeral at the successor slot, and the adequacy of the successor coding converts its satisfaction into the equation of the underlying sets.
<!--zh-->
中间约束子名指后继槽位处的数码，而后继编码的充分性把其满足转换成底层集合的等式。
<!--ja-->
中間の束縛子は、後者の枠の数項を名指し、後者の符号化の妥当性が、その充足を基礎の集合の等式へ変換する。
<!--/-->

```agda
          atNum : Σ[ z ∈ CS.S ] ( ⟨ (z ∷ γ) ⊨ sucAtL (suc a) zero ⟩
                                × ⟨ (z ∷ γ) ⊨ ∃̇ (prAtL (suc (suc s)) (suc zero) zero) ⟩ )
                → ∥ Σ[ c ∈ V ℓ ] (fst (lookup s γ) ≡ pr (# (suc k)) c) ∥₁
          atNum (z , (hs , hc)) = map₁
            (λ { (c , hp) → fst c
```

<!--en-->
The inner existential then yields the code `c` with a satisfaction of the pair clause; the adequacy transports it to the equation of pairs, composed with the identifications of the numeral and its successor. The equation recovered is exactly the truncated statement sought.
<!--zh-->
内层存在量词随之给出码 `c` 及对子句的一个满足；充分性把它运成有序对的等式，再与数码及其后继的认同复合。收回的等式正是所要的截断陈述。
<!--ja-->
内側の存在量化子が、対の条項の充足をもつ符号 `c` を与える。妥当性がそれを順序対の等式へ運び、数項とその後者の同定と合成する。取り戻された等式は、求めていた切り詰められた主張そのものである。
<!--/-->

```agda
               , ( subst ⟨_⟩ (prAtL-adequate (suc (suc s)) (suc zero) zero (c ∷ z ∷ γ)) hp
                 ∙ cong (λ u → pr u (fst c)) (qz ∙ cong sucV qa) ) })
            hc
            where
            qz : fst z ≡ sucV (fst (lookup a γ))
```

<!--en-->
The seven-slot environment is now assembled: the satisfaction table, the extended environment, the parameter environment, the key, the numeral, the witness and the current set, in the order the body will read them.
<!--zh-->
七槽环境在此装配：满足表、扩展环境、参数环境、键、数码、见证与当前集合，次序即体所要读取的次序。
<!--ja-->
七つの枠の環境がここで組み立てられる。充足の表、拡張された環境、パラメータの環境、キー、数項、証人、そして現在の集合。本体が読む順のままである。
<!--/-->

```agda
            qz = subst ⟨_⟩ (sucAtL-adequate (suc a) zero (z ∷ γ)) hs
    Env : CS.S → CS.S → CS.S → CS.S → CS.S → CS.S → CS.S → CS.S ^ 7
    Env T e' e s k w Z = T ∷ e' ∷ e ∷ s ∷ k ∷ w ∷ Z ∷ []
```

<!--en-->
The minimality subformula quantifies over the stage's alphabet. It says: if some extension of the parameter environment by a stage element satisfies the coded formula, then no such element stands before the witness in the stage's well-order. It is bounded by the constant `A`, so the quantifier runs over the stage and not over the universe.
<!--zh-->
极小性子公式对层的字母表量化。它说：若参数环境被某个层元素扩展后满足被编码公式，则该元素在层良序中不排在见证之前。它以常元 `A` 为界，故量词遍历的是该层而非整个宇宙。
<!--ja-->
極小性の部分の論理式は、段階のアルファベットの上で量化する。こう言う。パラメータの環境がある段階の要素で拡張され、符号化された論理式を満たすなら、そのような要素で、段階の整列順序において証人の前に立つものはない。定数 `A` で界されているので、量化は宇宙ではなく段階の上を走る。
<!--/-->

```agda
    opaque
      minFo : Formula CS.S 7
      minFo = ∀̇∈ (con A)
        ( (∃̇ ( consAtL i0 i1 i4 ∧̇ (var i0 ∈̇ var i2) )) ⇒̇ ¬̇ (appC Rel i0 i6) )
```

<!--en-->
The body conjuncts now say, in order: the numeral lies in the internal `ωʟ`; `s` is a key of arity one more; the parameter environment codes a vector over the current set; the extended environment extends it by the witness.
<!--zh-->
体的各合取项依次说：数码落在内部 `ωʟ` 中；`s` 是元数加一的键；参数环境把当前集合上的一个向量编码；扩展环境由见证扩展该环境。
<!--ja-->
本体の連言項は、順にこう言う。数項は内部の `ωʟ` の中にある。`s` はアリティが一つ大きいキーである。パラメータの環境が、現在の集合の上のベクトルを符号化する。拡張された環境が、それを証人で拡張する、と。
<!--/-->

```agda
      bodyFo : Formula CS.S 7
      bodyFo = (var i4 ∈̇ con ωʟ)
            ∧̇ ( keyIn i3 i4
            ∧̇ ( envOverAt i2 i4 i6
            ∧̇ ( consAtL i1 i5 i2
```

<!--en-->
The remaining conjuncts say: the pair of the key and the table lies in the satisfaction graph; the extended environment lies in the table; the witness lies in the stage; and minimality holds. There are eight conjuncts in all. The stage bounds the witness and the candidates used by minimality, while the coding conjuncts supply the auxiliary objects that connect the record to the satisfaction table.
<!--zh-->
其余合取项说：键与表组成的对落在满足图中；扩展环境属于表；见证属于该层；且极小性成立。合计八个合取项。层约束见证以及极小性所比较的候选，而各编码合取项提供把这份记录接到满足表所需的辅助对象。
<!--ja-->
残りの連言項はこう言う。キーと表の対が充足のグラフの中にある。拡張された環境が表の中にある。証人が段階の中にある。そして極小性が成立する。連言項は全部で八つである。段階は証人と極小性で比較する候補を制限し、符号化の連言項は、この記録を充足表へ結びつける補助対象を与える。
<!--/-->

```agda
            ∧̇ ( appC SM.pairs i3 i0
            ∧̇ ( (var i1 ∈̇ var i0)
            ∧̇ ( (var i5 ∈̇ con A)
            ∧̇ minFo ))))))
```

<!--en-->
Fix the seven objects `T,e',e,s,k,w,Z`. At their joint environment, the body is a concrete proposition whose eight conjuncts can be projected and assembled in both directions.
<!--zh-->
固定七个对象 `T,e',e,s,k,w,Z`。在它们组成的环境处，体成为一个具体命题，其八个合取项既可逐项投影，也可反向装配。
<!--ja-->
七つの対象 `T,e',e,s,k,w,Z` を固定する。それらからなる環境では、本体は具体的な命題となり、八つの連言項を個別に取り出すことも、逆に組み立てることもできる。
<!--/-->

```agda
    module BodyRd (T e' e s k w Z : CS.S) where
```

<!--en-->
The seven-slot environment is recorded, and the host-side minimality is stated relative to a family presenting the parameter environment: no extension by a smaller stage element lands in the satisfaction table while ranking before the witness.
<!--zh-->
七槽环境被记录；宿主侧极小性相对于呈现参数环境的族陈述：不存在用更小的层元素所作的扩展落入满足表、同时在层序中排在见证之前。
<!--ja-->
七つの枠の環境が記録され、ホスト側の極小性は、パラメータの環境を提示する族に相対的に述べられる。より小さい段階の要素による拡張が、充足の表の中に落ち、かつ整列順序で証人の前に立つ、ということはない。
<!--/-->

```agda
      γ₇ : CS.S ^ 7
      γ₇ = Env T e' e s k w Z
      Min : {m : ℕ} (g : Fin m → V ℓ) → Type (ℓ-suc ℓ)
      Min g = (w' : CS.S) → ⟨ fst w' ∈ˢ fst A ⟩ → (e'' : CS.S)
            → fst e'' ≡ env (cons (fst w') g) → ⟨ fst e'' ∈ˢ fst T ⟩
```

<!--en-->
The clause ends in the empty type: minimality is refutation, and the data of a counterexample, a smaller extension with the pair membership, is exactly what must be impossible.
<!--zh-->
该子句终止于空类型：极小性表现为排除反例，也就是排除一个更小的扩展及其相应的对隶属。
<!--ja-->
この条項は空型で終わる。極小性は反駁であり、反例のデータ、つまりより小さい拡張とその対への所属が、ちょうど不可能でなければならないのである。
<!--/-->

```agda
            → ⟨ pr (fst w') (fst w) ∈ˢ fst Rel ⟩ → ⊥₀
```

<!--en-->
Because the body is a nested conjunction, each of its eight conditions can be read by projection, while a proof of all eight conditions can be assembled back into satisfaction of the body.
<!--zh-->
由于体是嵌套的合取，其八项条件都可由投影读出；反过来，八项条件的证明又可装配成对该体的满足。
<!--ja-->
本体は入れ子の連言なので、八つの条件はそれぞれ射影によって読み出せる。逆に、八条件の証明を組み合わせれば、本体の充足を得られる。
<!--/-->

```agda
      opaque
        unfolding bodyFo
```

<!--en-->
The first reading projects the numeral clause. Membership in the internal `ωʟ` lets us recover a natural number `n`; together with the key clause, this identifies `s` as a key of arity `n+1`, with one slot reserved for the witness.
<!--zh-->
第一条读法投影数码子句。属于内部 `ωʟ` 使我们能恢复自然数 `n`；再结合键子句，便知 `s` 是元数为 `n+1` 的键，其中一个槽位留给见证。
<!--ja-->
最初の読み出しは数項の条項を射影する。内部の `ωʟ` への所属から自然数 `n` を復元でき、キーの条項と合わせると、`s` がアリティ `n+1` のキーであり、その一枠が証人に割り当てられていると分かる。
<!--/-->

```agda
        b-num : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst k ∈ˢ fst ωʟ ⟩
        b-num h = h .fst
```

<!--en-->
The second projection is the key clause: at slots `s` and `k`, the formula asserts that `s` is a recognized key whose arity is one more than the numeral `k`.
<!--zh-->
第二项投影是键子句：公式在 `s` 与 `k` 槽处断言，`s` 是一个被识别的键，其元数比数码 `k` 大一。
<!--ja-->
第二の射影はキーの条項である。論理式は `s` と `k` の枠で、`s` が認識されたキーであり、そのアリティが数項 `k` より一つ大きいことを述べる。
<!--/-->

```agda
        b-key : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ γ₇ ⊨ keyIn i3 i4 ⟩
        b-key h = h .snd .fst
```

<!--en-->
The third reading projects the environment clause: the parameter environment codes a vector over the current set at the recorded slots.
<!--zh-->
第三条读法投影环境子句：参数环境在所记录的槽位处把当前集合上的一个向量编码。
<!--ja-->
第三の読み出しは、環境の条項を射影する。パラメータの環境が、記録された枠で、現在の集合の上のベクトルを符号化する。
<!--/-->

```agda
        b-env : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
        b-env h = h .snd .snd .fst
```

<!--en-->
The fourth reading states the extension equation, transported along the adequacy of the cons coding: the extended environment is the parameter environment extended by the witness.
<!--zh-->
第四条读法给出扩展等式，沿 cons 编码的充分性运输：扩展环境是参数环境由见证扩展而成。
<!--ja-->
第四の読み出しは拡張の等式を述べる。cons の符号化の妥当性に沿って運ばれたもので、拡張された環境は、パラメータの環境を証人で拡張したものである。
<!--/-->

```agda
        b-cons : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g
               → ⟨ γ₇ ⊨ bodyFo ⟩ → fst e' ≡ env (cons (fst w) g)
        b-cons g hE h =
          subst ⟨_⟩ (consAtL-adequate i1 i5 i2 γ₇ g hE) (h .snd .snd .snd .fst)
```

<!--en-->
The fifth reading states the graph membership of the pair of the key and the table, transported along the adequacy of the application coding.
<!--zh-->
第五条读法给出「键与表之对」的图隶属，沿应用编码的充分性运输。
<!--ja-->
第五の読み出しは、キーと表の対のグラフへの所属を述べる。適用の符号化の妥当性に沿って運ばれたものである。
<!--/-->

```agda
        b-tab : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ pr (fst s) (fst T) ∈ˢ fst SM.pairs ⟩
        b-tab h = subst ⟨_⟩ (appC-adequate SM.pairs i3 i0 γ₇) (h .snd .snd .snd .snd .fst)
```

<!--en-->
The sixth reading is the membership of the extended environment in the satisfaction table, the fact that says the witness satisfies the coded formula at the parameters.
<!--zh-->
第六条读法是扩展环境对满足表的隶属，即「见证在参数处满足被编码公式」这一事实。
<!--ja-->
第六の読み出しは、拡張された環境の充足の表への所属である。証人がパラメータで符号化された論理式を満たす、という事実である。
<!--/-->

```agda
        b-mem : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst e' ∈ˢ fst T ⟩
        b-mem h = h .snd .snd .snd .snd .snd .fst
```

<!--en-->
The seventh projection states that the witness belongs to the stage `A`, so the witness and all candidates compared with it range over the same stage.
<!--zh-->
第七项投影说明见证属于层 `A`，因而该见证与所有同它比较的候选都取自同一个层。
<!--ja-->
第七の射影は、証人が段階 `A` に属することを述べる。したがって、証人と、それと比較される候補はすべて同じ段階を動く。
<!--/-->

```agda
        b-stage : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst w ∈ˢ fst A ⟩
        b-stage h = h .snd .snd .snd .snd .snd .snd .fst
```

<!--en-->
The eighth reading is the minimality clause, read refutationally: a smaller candidate with a satisfying extension would contradict the bounded quantifier, after the relation entry is transported through the application's adequacy.
<!--zh-->
第八条读法是以反驳形式读取的极小性子句：一个更小的候选若带有满足扩展，便与有界量词矛盾，其间关系条目要经应用的充分性运输。
<!--ja-->
第八の読み出しは、反駁の形で読まれる極小性の条項である。より小さい候補が充足する拡張をもてば、有界の量化子と矛盾する。関係の項目は、適用の妥当性を通して輸送されたうえでである。
<!--/-->

```agda
        b-min : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g → ⟨ γ₇ ⊨ bodyFo ⟩ → Min g
        b-min g hE h w' hw' e'' qe hm hr =
          lower (h .snd .snd .snd .snd .snd .snd .snd w' hw' ∣ e'' , (hc , hm) ∣₁
            (subst ⟨_⟩ (sym (appC-adequate Rel i0 i6 (w' ∷ γ₇))) hr))
          where
```

<!--en-->
The cons clause of the candidate extension is transported from its host equation, exactly mirroring the coding of the extension in the inner existential.
<!--zh-->
候选扩展的 cons 子句由其宿主等式运输而来，恰与内层存在量词中扩展的编码互为镜像。
<!--ja-->
候補の拡張の cons の条項は、そのホストの等式から運ばれる。内側の存在量化子での拡張の符号化と、ちょうど鏡の関係である。
<!--/-->

```agda
          hc : ⟨ (e'' ∷ w' ∷ γ₇) ⊨ consAtL i0 i1 i4 ⟩
          hc = subst ⟨_⟩ (sym (consAtL-adequate i0 i1 i4 (e'' ∷ w' ∷ γ₇) g hE)) qe
```

<!--en-->
The filling reading assembles a satisfaction of the body from its eight components: the numeral clause, the key clause, the environment clause, the extension equation, the graph membership, the table membership, the stage membership, and minimality.
<!--zh-->
填充读法由八个分量装配出体的满足：数码子句、键子句、环境子句、扩展等式、图隶属、表隶属、层隶属，以及极小性。
<!--ja-->
充填の読み出しは、八つの成分から本体の充足を組み立てる。数項の条項、キーの条項、環境の条項、拡張の等式、グラフへの所属、表への所属、段階への所属、そして極小性である。
<!--/-->

```agda
        b-fill : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g
               → ⟨ fst k ∈ˢ fst ωʟ ⟩ → ⟨ γ₇ ⊨ keyIn i3 i4 ⟩ → ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
               → fst e' ≡ env (cons (fst w) g) → ⟨ pr (fst s) (fst T) ∈ˢ fst SM.pairs ⟩
               → ⟨ fst e' ∈ˢ fst T ⟩ → ⟨ fst w ∈ˢ fst A ⟩ → Min g
               → ⟨ γ₇ ⊨ bodyFo ⟩
```

<!--en-->
Five conjuncts are inserted directly. The extension equation and the graph entry are converted back into satisfactions by the reversed adequacy equations for `consAtL` and `appC`; minimality is supplied in the final clause.
<!--zh-->
五个合取项被直接放入。扩展等式与图条目分别沿 `consAtL` 和 `appC` 的充分性等式反向转换为满足；极小性则由最后一项给出。
<!--ja-->
五つの連言項はそのまま挿入される。拡張の等式とグラフの項目は、`consAtL` と `appC` の妥当性の等式を逆向きに用いて充足へ戻され、極小性は最後の条項で与えられる。
<!--/-->

```agda
        b-fill g hE c1 c2 c3 c4 c5 c6 c7 mn =
          c1 , c2 , c3
          , subst ⟨_⟩ (sym (consAtL-adequate i1 i5 i2 γ₇ g hE)) c4
          , subst ⟨_⟩ (sym (appC-adequate SM.pairs i3 i0 γ₇)) c5
          , c6 , c7
```

<!--en-->
Minimality is filled by eliminating its truncated counterexample into the empty type: the counterexample is transported through both adequacy equations and handed to the refutation, so the filler needs only the contradiction, not a construction.
<!--zh-->
极小性的填充靠把其截断的反例消去到空类型完成：反例先穿过两条充分性等式再交予反驳，因此填充者只需要矛盾本身，而不需要任何构造。
<!--ja-->
極小性の充填は、切り詰められた反例を空型へ消去することで行われる。反例は二つの妥当性の等式を通して運ばれ、反駁に手渡される。だから充填に要るのは矛盾だけで、構成ではない。
<!--/-->

```agda
          , λ w' hw' hex hr → lift (rec₁ isProp⊥
              (λ { (e'' , (hc , hm)) → mn w' hw' e''
                     (subst ⟨_⟩ (consAtL-adequate i0 i1 i4 (e'' ∷ w' ∷ γ₇) g hE) hc) hm
                     (subst ⟨_⟩ (appC-adequate Rel i0 i6 (w' ∷ γ₇)) hr) })
              hex)
```

<!--en-->
The witness formula wraps the body in five nested existentials, one per object: the satisfaction table, the extended environment, the parameter environment, the key, and the numeral. Satisfaction of the formula at `w` and `Z` says exactly that a complete record for a least witness at `w` over `Z` exists.
<!--zh-->
见证公式用五层嵌套存在量词包裹体，每个对象一个：满足表、扩展环境、参数环境、键、数码。该公式在 `w` 与 `Z` 处的满足，恰是说：`Z` 上 `w` 处的最小见证的完整记录存在。
<!--ja-->
証人の論理式は、本体を五重の存在量化で包む。対象ごとに一つである。充足の表、拡張された環境、パラメータの環境、キー、そして数項。この論理式の `w` と `Z` での充足が言うのは、`Z` の上の `w` での最小の証人の完全な記録が存在するということである。
<!--/-->

```agda
    opaque
      witFo : Formula CS.S 2
      witFo = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ bodyFo))))
```

<!--en-->
The inward reading injects the five objects and the body satisfaction through the five binders, each injection carrying one object into its slot.
<!--zh-->
向内读法把五个对象与体的满足沿五层约束子逐一注入，每次注入把一个对象送入其槽位。
<!--ja-->
内向きの読み出しは、五つの対象と本体の充足を、五つの束縛子を通して注入する。一回の注入が一つの対象を、その枠へ運ぶ。
<!--/-->

```agda
      witFo-in : (w Z T e' e s k : CS.S) → ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩
               → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
      witFo-in w Z T e' e s k h = ∣ k , ∣ s , ∣ e , ∣ e' , ∣ T , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
```

<!--en-->
The outward reading eliminates the five truncated existentials in binder order. At the innermost layer, `map₁` merely rearranges the recovered objects into the displayed dependent tuple, leaving the body satisfaction unchanged.
<!--zh-->
向外读法按约束次序消去五层截断存在。在最内层，`map₁` 只把恢复出的对象重排为所展示的依赖元组，体的满足本身不作运输。
<!--ja-->
外向きの読み出しは、束縛の順に五つの切り詰められた存在を消去する。最内層では `map₁` が、復元した対象を表示された依存対へ並べ替えるだけで、本体の充足そのものは輸送しない。
<!--/-->

```agda
      witFo-out : (w Z : CS.S) → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
                → ∥ Σ[ T ∈ CS.S ] Σ[ e' ∈ CS.S ] Σ[ e ∈ CS.S ] Σ[ s ∈ CS.S ] Σ[ k ∈ CS.S ]
                     ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩ ∥₁
      witFo-out w Z = rec₁ squash₁ (λ { (k , hk) → rec₁ squash₁ (λ { (s , hs) →
        rec₁ squash₁ (λ { (e , he) → rec₁ squash₁ (λ { (e' , he') → map₁
```

<!--en-->
Unwrapping `witFo` yields a table, an extended environment, a parameter environment, a key, and a numeral whose joint environment satisfies the body.
<!--zh-->
拆开 `witFo` 得到满足表、扩展环境、参数环境、键与数码；
<!--ja-->
`witFo` をほどくと、充足表・拡張環境・パラメータ環境・キー・数項が得られ、それらからなる環境が本体を満たす。
<!--/-->

```agda
          (λ { (T , hT) → T , e' , e , s , k , hT }) he' }) he }) hs }) hk })
```

<!--en-->
## The least-witness relation at a fixed key and environment
<!--zh-->
## 固定键与环境处的最小见证关系
<!--ja-->
## 固定したキーと環境における最小の証人の関係
<!--/-->

<!--en-->
When `e` and `s` are fixed, `LeastWitness Z e s z` retains the truncated existence of the remaining table, extended environment, and numeral.
<!--zh-->
它们组成的环境满足体。固定 `e` 与 `s` 后，`LeastWitness Z e s z` 保留其余满足表、扩展环境与数码的截断存在。
<!--ja-->
`e` と `s` を固定すると、`LeastWitness Z e s z` は残る充足表・拡張環境・数項の切り詰められた存在を保持する。
<!--/-->

```agda
    LeastWitness : CS.S → CS.S → CS.S → CS.S → Type (ℓ-suc ℓ)
    LeastWitness Z e s z =
      ∥ Σ[ T ∈ CS.S ] Σ[ e' ∈ CS.S ] Σ[ k ∈ CS.S ]
          ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩ ∥₁
```

<!--en-->
To bind the table, extended environment, and numeral while retaining six ambient variables, the body is renamed from seven slots to nine. The map places its seven meaningful entries at `T,e',e,s,k,z,Z`.
<!--zh-->
为了在保留六个周围变元的同时约束满足表、扩展环境与数码，体从七槽改名到九槽。槽位映射把七个有效条目放在 `T,e',e,s,k,z,Z` 处。
<!--ja-->
六つの周囲の変数を保ったまま充足表・拡張環境・数項を束縛するため、本体を七枠から九枠へ改名する。写像は七つの実質的な成分を `T,e',e,s,k,z,Z` の位置へ置く。
<!--/-->

```agda
    private
      ρ₉ : Fin 7 → Fin 9
      ρ₉ zero = i0
      ρ₉ (suc zero) = i1
      ρ₉ (suc (suc zero)) = i4
```

<!--en-->
The remaining four cases place the key `s`, the numeral `k`, the candidate `z`, and the current set `Z`. The final slots `p` and `q` are unused, so satisfaction is independent of their values.
<!--zh-->
余下四种情形依次安置键 `s`、数码 `k`、候选 `z` 与当前集合 `Z`。末尾的 `p,q` 不被读取，因此满足与它们的取值无关。
<!--ja-->
残る四つの場合は、キー `s`、数項 `k`、候補 `z`、現在の集合 `Z` を配置する。末尾の `p,q` は読まれないので、充足はその値に依存しない。
<!--/-->

```agda
      ρ₉ (suc (suc (suc zero))) = i5
      ρ₉ (suc (suc (suc (suc zero)))) = i2
      ρ₉ (suc (suc (suc (suc (suc zero))))) = i6
      ρ₉ (suc (suc (suc (suc (suc (suc zero)))))) = i3
```

<!--en-->
`Γ₉` displays this placement, and each agreement with the original seven-slot environment is judgmental reflexivity.
<!--zh-->
`Γ₉` 展示这一安置，而每条与原七槽环境的相合都由定义上的自反性成立。
<!--ja-->
`Γ₉` がこの配置を示し、元の七つの枠の環境との各一致は、定義上の反射性で成り立つ。
<!--/-->

```agda
      Γ₉ : (T e' k Z e s z p q : CS.S) → CS.S ^ 9
      Γ₉ T e' k Z e s z p q = T ∷ e' ∷ k ∷ Z ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []
```

<!--en-->
The agreements say that, at each renamed slot, the two environments carry the same carrier element. The first three are proved by reflexivity, one per renamed position.
<!--zh-->
相合说：在每个被改名的槽处，两个环境载有相同的载体元素。前三条由自反性证明，每个被改名的位置一条。
<!--ja-->
一致はこう言う。改名されたそれぞれの枠で、二つの環境は同じ台の要素を載せている、と。最初の三つは反射性で証明され、改名された位置ごとに一つである。
<!--/-->

```agda
      ag₉ : (T e' k Z e s z p q : CS.S)
          → Ren.Agrees ρ₉ (Γ₉ T e' k Z e s z p q) (Env T e' e s k z Z)
      ag₉ T e' k Z e s z p q zero = refl
      ag₉ T e' k Z e s z p q (suc zero) = refl
      ag₉ T e' k Z e s z p q (suc (suc zero)) = refl
```

<!--en-->
The remaining four agreements are again reflexivity, one per slot; every agreement is a computation, which is what makes the renaming usable inside a satisfaction.
<!--zh-->
其余四条相合同样是自反性，每槽一条；每条相合都是一次计算，这正是改名能在满足内部使用的原因。
<!--ja-->
残りの四つの一致も同じく反射性で、枠ごとに一つである。どの一致も計算であり、これが、改名を充足の内側で使える理由である。
<!--/-->

```agda
      ag₉ T e' k Z e s z p q (suc (suc (suc zero))) = refl
      ag₉ T e' k Z e s z p q (suc (suc (suc (suc zero)))) = refl
      ag₉ T e' k Z e s z p q (suc (suc (suc (suc (suc zero))))) = refl
      ag₉ T e' k Z e s z p q (suc (suc (suc (suc (suc (suc zero)))))) = refl
```

<!--en-->
The renamed body is the body formula pushed through the slot map, living over nine slots while saying the same thing as before.
<!--zh-->
改名后的体是沿槽位表推送的体公式，居于九槽之上，所说却与从前相同。
<!--ja-->
改名された本体は、本体の論理式を枠の対応に沿って押し出したもので、九つの枠の上にありながら、言うことは以前と同じである。
<!--/-->

```agda
      body₉ : Formula CS.S 9
      body₉ = renameFo ρ₉ bodyFo
```

<!--en-->
The reading equation says that satisfying the renamed body over the nine-slot environment is the same proposition as satisfying the body over the seven-slot environment.
<!--zh-->
读取等式说：在九槽环境上满足改名后的体，与在七槽环境上满足体，是同一命题。
<!--ja-->
読みの等式はこう言う。九つの枠の環境で改名された本体を充足することは、七つの枠の環境で本体を充足することと、同じ命題である。
<!--/-->

```agda
      body₉-read : (T e' k Z e s z p q : CS.S)
                 → ⟨ Γ₉ T e' k Z e s z p q ⊨ body₉ ⟩
                 ≡ ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩
      body₉-read T e' k Z e s z p q =
        cong ⟨_⟩ (Ren.⊨-rename ρ₉ bodyFo (Γ₉ T e' k Z e s z p q)
```

<!--en-->
The proof is the renaming theorem applied with the slot agreement, transported under the bracket of satisfaction.
<!--zh-->
证明是把改名定理施于槽位相合，再在满足的括号下运输。
<!--ja-->
証明は、枠の一致を引数に改名の定理を適用し、充足の括弧の下で輸送するものである。
<!--/-->

```agda
                    (Env T e' e s k z Z) (ag₉ T e' k Z e s z p q))
```

<!--en-->
The least-witness formula wraps the renamed body in three more existentials: the numeral, the extended environment, and the table. Satisfaction at the six-slot environment says that a least-witness record exists for the candidate at the current set, key and parameter environment.
<!--zh-->
最小见证公式在改名后的体上再包三层存在量词：数码、扩展环境、满足表。其在六槽环境处的满足说：对该候选，在当前集合、键与参数环境处，存在一份最小见证记录。
<!--ja-->
最小の証人の論理式は、改名された本体の上に、さらに三つの存在量化を包む。数項、拡張された環境、充足の表である。六つの枠の環境での充足が言うのは、候補の、現在の集合・キー・パラメータの環境における最小の証人の記録が存在するということである。
<!--/-->

```agda
    opaque
      leastWitnessFo : Formula CS.S 6
      leastWitnessFo = ∃̇ (∃̇ (∃̇ body₉))
```

<!--en-->
The inward reading eliminates the truncated least-witness data and injects the three objects, transporting the body satisfaction along the reading equation of the renamed body.
<!--zh-->
向内读法消去截断的最小见证数据并注入三个对象，且把体的满足沿改名体的读取等式运输。
<!--ja-->
内向きの読み出しは、切り詰められた最小の証人のデータを消去して三つの対象を注入し、本体の充足を、改名された本体の読みの等式に沿って運ぶ。
<!--/-->

```agda
      leastWitness-in : (Z e s z p q : CS.S) → LeastWitness Z e s z
                      → ⟨ (Z ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ leastWitnessFo ⟩
      leastWitness-in Z e s z p q = rec₁ (snd ((Z ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ leastWitnessFo))
        (λ { (T , e' , k , h) →
          ∣ k , ∣ e' , ∣ T , transport (sym (body₉-read T e' k Z e s z p q)) h ∣₁ ∣₁ ∣₁ })
```

<!--en-->
The outward reading eliminates the three nested existentials in order, each into the truncated continuation, so the formula satisfaction becomes a least-witness record again.
<!--zh-->
向外读法依次消去三层嵌套存在量词，每次都消到截断的后续之中，于是公式满足重新变回一份最小见证记录。
<!--ja-->
外向きの読み出しは、三重の入れ子の存在量化を順に消去し、そのつど切り詰められた続きの中へ消去する。だから論理式の充足は、再び最小の証人の記録になる。
<!--/-->

```agda
      leastWitness-out : (Z e s z p q : CS.S)
                       → ⟨ (Z ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ leastWitnessFo ⟩
                       → LeastWitness Z e s z
      leastWitness-out Z e s z p q = rec₁ squash₁ at₁
        where
```

<!--en-->
The innermost elimination rebuilds the least-witness data from the named table, extended environment and numeral, transporting the body satisfaction along the reading equation. The two outer eliminations supply the bound objects required by this construction.
<!--zh-->
最内层消去由被名指的满足表、扩展环境与数码重建最小见证数据，并把体的满足沿读取等式运输。两个外层消去则提供该构造所需的约束对象。
<!--ja-->
最も内側の消去は、名指された充足表・拡張環境・数項から最小の証人のデータを組み立て直し、本体の充足を読み出しの等式に沿って輸送する。外側の二つの消去は、この構成に必要な束縛された対象を与える。
<!--/-->

```agda
        at₃ : (k e' : CS.S) → Σ[ T ∈ CS.S ] ⟨ Γ₉ T e' k Z e s z p q ⊨ body₉ ⟩
            → LeastWitness Z e s z
        at₃ k e' (T , h) = ∣ T , e' , k , transport (body₉-read T e' k Z e s z p q) h ∣₁
        at₂ : (k : CS.S) → Σ[ e' ∈ CS.S ] ∥ Σ[ T ∈ CS.S ] ⟨ Γ₉ T e' k Z e s z p q ⊨ body₉ ⟩ ∥₁
            → LeastWitness Z e s z
```

<!--en-->
At this point two nested truncations remain: the outer one hides the extension environment `e'`, and the inner one hides the table `T`. The two eliminations expose them in turn, after which `at₃` transports the renamed body proof back to a `LeastWitness`.
<!--zh-->
此处还剩两层截断：外层隐藏延拓环境 `e'`，内层隐藏表 `T`。两次消去依次取出它们，随后 `at₃` 把改名后的体证明搬回一份 `LeastWitness`。
<!--ja-->
ここには二重の切り詰めが残っている。外側は延長された環境 `e'` を、内側は表 `T` を隠している。二回の除去でそれらを順に取り出すと、`at₃` が改名された本体の証明を `LeastWitness` へ戻す。
<!--/-->

```agda
        at₂ k (e' , h) = rec₁ squash₁ (at₃ k e') h
        at₁ : Σ[ k ∈ CS.S ] ∥ Σ[ e' ∈ CS.S ] ∥ Σ[ T ∈ CS.S ]
                ⟨ Γ₉ T e' k Z e s z p q ⊨ body₉ ⟩ ∥₁ ∥₁
            → LeastWitness Z e s z
        at₁ (k , h) = rec₁ squash₁ (at₂ k) h
```

<!--en-->
The numeral slot carries a member of the internal `ω`, and `decode-num` decodes it: a truncated natural number `n` together with the equation identifying the entry with the ambient numeral `# n`. Decoding is the bridge between the internal numbering and the natural-number bookkeeping of the witness data.
<!--zh-->
数码槽位装着内部 `ω` 的一个成员，`decode-num` 将其解码：得到截断的自然数 `n`，以及把该条目与外围数码 `# n` 等同的等式。解码是内部编号与见证数据的自然数记账之间的桥梁。
<!--ja-->
数項のスロットには内部の `ω` の要素が収められており、`decode-num` がそれを解読する。切り詰められた自然数 `n` と、その項目を周囲の数項 `# n` と同一視する等式が得られるのである。解読は、内部の付番と証人のデータの自然数の管理とを結ぶ橋である。
<!--/-->

```agda
    private
      decode-num : (q : CS.S) → ⟨ fst q ∈ˢ fst ωʟ ⟩ → ∥ Σ[ n ∈ ℕ ] (fst q ≡ # n) ∥₁
      decode-num q h = map₁ (λ { (n , e) → lower n , (e ∙ numeralL-fst (lower n)) })
        (subst ⟨_⟩ (ω-specL q) h)
```

<!--en-->
`LeastWitnessData` is the honest data behind a least witness: a natural number `n`, an assignment `g` of `n` indices into the presentation of `Z`, the equation saying that `e` is the environment naming those values, and the stage membership placing `s` in `Lset ω`.
<!--zh-->
`LeastWitnessData` 是最小见证背后的真实数据：自然数 `n`、把 `n` 个索引指派到 `Z` 呈现中的赋值 `g`、说明 `e` 正是命名这些取值的环境的等式，以及把 `s` 放入 `Lset ω` 的层隶属。
<!--ja-->
`LeastWitnessData` は最小証人の背後にある実際のデータである。自然数 `n`、`Z` の提示への `n` 個の添字の割り当て `g`、`e` がそれらの値を名指す環境であることの等式、そして `s` を `Lset ω` に置く段階の所属である。
<!--/-->

```agda
    LeastWitnessData : CS.S → CS.S → CS.S → Type (ℓ-suc ℓ)
    LeastWitnessData Z e s =
      Σ[ n ∈ ℕ ] Σ[ g ∈ (Fin n → ⟪ fst Z ⟫) ]
        ((fst e ≡ env (λ i → ⟪ fst Z ⟫↪ (g i))) × (⟨ fst s ∈ Lset ω ⟩))
```

<!--en-->
The theorem `leastWitness-data` says that a formula-level least witness determines, up to propositional truncation, a natural arity, an indexed parameter environment over `Z`, and a proof that the key lies in `Lset ω`.
<!--zh-->
定理 `leastWitness-data` 说明：公式层的最小见证在命题截断意义下决定一个自然数元数、`Z` 上的索引参数环境，以及键属于 `Lset ω` 的证明。
<!--ja-->
定理 `leastWitness-data` は、論理式の水準の最小証人から、命題的切り詰めのもとで、自然数のアリティ、`Z` 上で添字付けられたパラメータ環境、そしてキーが `Lset ω` に属する証明が得られることを述べる。
<!--/-->

```agda
    opaque
      leastWitness-data : (Z e s z : CS.S) → LeastWitness Z e s z
                        → ∥ LeastWitnessData Z e s ∥₁
      leastWitness-data Z e s z = rec₁ squash₁ body
        where
```

<!--en-->
The body of the conversion consumes the body satisfaction: it unpacks into the table `T`, the extension `e'`, the key `k`, and the body proof, and the numeral entry of the key is decoded first.
<!--zh-->
转换的主体消耗体的满足：将其拆开为表 `T`、扩展 `e'`、键 `k` 与体证明，而键的数码条目最先被解码。
<!--ja-->
変換の本体は、体の充足を消費する。それを表 `T`、拡張 `e'`、鍵 `k`、そして体の証明へ分解し、鍵の数項の項目がまず解読される。
<!--/-->

```agda
        body : Σ[ T ∈ CS.S ] Σ[ e' ∈ CS.S ] Σ[ k ∈ CS.S ]
                 ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩
             → ∥ LeastWitnessData Z e s ∥₁
        body (T , e' , k , hb) = map₁ at (decode-num k (BodyRd.b-num T e' e s k z Z hb))
          where
```

<!--en-->
With the numeral `n` and the equation naming the key, the data assembles: the length `n`, the recovered assignment `g`, the recovery equation for the environment, and the stage membership of `s`. The seven-entry context is named once so the recovery can address its slots.
<!--zh-->
有了数码 `n` 与点名键的等式，数据即可组装：长度 `n`、恢复出的赋值 `g`、环境的恢复等式，以及 `s` 的层隶属。七条目语境被一次性命名，使恢复过程能够寻址各个槽位。
<!--ja-->
数項 `n` と鍵を名指す等式が揃うと、データが組み上がる。長さ `n`、復元された割り当て `g`、環境の復元の等式、そして `s` の段階の所属である。七項目の文脈には一度名前が与えられ、復元が各スロットを参照できるようにする。
<!--/-->

```agda
          at : Σ[ n ∈ ℕ ] (fst k ≡ # n) → LeastWitnessData Z e s
          at (n , qk) = n , R.g , R.recovers , s∈Lω
            where
            γ : CS.S ^ 7
            γ = Env T e' e s k z Z
```

<!--en-->
The environment clause recovers an assignment `g` of indices in `Z` and proves that `e` is the graph of their values. Independently, the key clause says that `s` is a code and is an ordered pair of the successor arity numeral with a formula code.
<!--zh-->
环境子句恢复出 `Z` 中索引的赋值 `g`，并证明 `e` 是这些索引之取值的图。另一方面，键子句说明 `s` 是一个码，而且是后继元数的数码与某个公式码组成的有序对。
<!--ja-->
環境の節は `Z` の添字の割り当て `g` を復元し、`e` がそれらの値のグラフであることを示す。一方、キーの節は `s` がコードであり、後続アリティの数項と論理式コードとの順序対であることを述べる。
<!--/-->

```agda
            module R = Recover Z n γ i2 i4 i6 qk refl (BodyRd.b-env T e' e s k z Z hb)
              using ( g; recovers )
            kr : ⟨ fst s ∈ fst C₀ ⟩ × ∥ Σ[ c ∈ V ℓ ] (fst s ≡ pr (# (suc n)) c) ∥₁
            kr = KeyIn.keyIn-out i3 i4 γ n qk (BodyRd.b-key T e' e s k z Z hb)
            s∈Lω : ⟨ fst s ∈ Lset ω ⟩
```

<!--en-->
The stage membership of the key's value is the last piece of the data. It is proved from the pair equation: the second component `c` of the key is a code, and codes are constructible by the limit stage.
<!--zh-->
键的取值的层隶属是数据的最后一块。它由对等式证明：键的第二分量 `c` 是一个码，而码在极限层处就可构造。
<!--ja-->
鍵の値の段階の所属がデータの最後の部分である。これは対の等式から証明される。鍵の第二成分 `c` はコードであり、コードは極限の段階で既に構成可能である。
<!--/-->

```agda
            s∈Lω = rec₁ (snd (fst s ∈ Lset ω)) read (kr .snd)
              where
              read : Σ[ c ∈ V ℓ ] (fst s ≡ pr (# (suc n)) c) → ⟨ fst s ∈ Lset ω ⟩
              read (c , qs) = rec₁ (snd (fst s ∈ Lset ω))
                (λ { (χ , qc) → subst (λ w → ⟨ w ∈ Lset ω ⟩) (sym qs)
```

<!--en-->
Both components of the key therefore live in `Lset ω`: the successor numeral belongs to the limit by the numerals' membership, and pairs of members of a limit stage stay in the limit. Transporting along the pair equation places `s` in `Lset ω`, completing `LeastWitnessData`.
<!--zh-->
于是键的两个分量都住在 `Lset ω` 中：后继数码凭数码的隶属属于极限层，而极限层成员的有序对仍留在极限层。沿对等式传输后，`s` 便落入 `Lset ω`，`LeastWitnessData` 随之完成。
<!--ja-->
したがって鍵の二つの成分はどちらも `Lset ω` に住む。後続の数項は数項の所属によって極限に属し、極限の段階の要素の順序対はやはり極限にとどまる。対の等式に沿って輸送すれば `s` は `Lset ω` に入り、`LeastWitnessData` が完成する。
<!--/-->

```agda
                       (pr∈limit (# (suc n)) c (numeral∈limit (suc n))
                         (subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym qc) (snd (limitCode χ)))) })
                (freeCode-out (suc n) c (subst (λ u → ⟨ u ∈ fst C₀ ⟩) qs (kr .fst)))
```

<!--en-->
The outward reading of the witness formula now assembles: satisfaction of `witFo` at `(z, Z)` unpacks into a table, an extension, a key, and the body proof, and the body proof converts into a truncated `LeastWitness`. This is the form in which the satisfaction of the Skolem clause is consumed.
<!--zh-->
见证公式的外向读法在此组装：`witFo` 在 `(z, Z)` 处的满足拆开为表、扩展、键与体证明，而体证明转换为截断的 `LeastWitness`。这正是消费 Skolem 子句之满足的形式。
<!--ja-->
証人の論理式の外向きの読みがここで組み上がる。`(z, Z)` での `witFo` の充足は、表、拡張、鍵、そして体の証明へ展開され、体の証明は切り詰められた `LeastWitness` へ変換される。Skolem の節の充足を消費するのはこの形である。
<!--/-->

```agda
      witFo-leastWitness : (z Z : CS.S) → ⟨ (z ∷ Z ∷ []) ⊨ witFo ⟩
                         → ∥ Σ[ e ∈ CS.S ] Σ[ s ∈ CS.S ] LeastWitness Z e s z ∥₁
      witFo-leastWitness z Z h = map₁
        (λ { (T , e' , e , s , k , hb) → e , s , ∣ T , e' , k , hb ∣₁ })
        (witFo-out z Z h)
```

<!--en-->
For comparing two witnesses, we retain seven of the eight body clauses: the numeral, environment, extension, table, membership, stage, and minimality clauses. The key clause is not needed here, because the two witnesses already share `s`, and uniqueness of the value associated with that key identifies their tables.
<!--zh-->
为比较两个见证，这里保留体的八条子句中的七条：数码、环境、延拓、表、隶属、层与最小性子句。这里不需要键子句，因为两份见证已经共享 `s`，而该键所对应之值的唯一性会把两张表同一视。
<!--ja-->
二つの証人を比較するため、本体の八つの節のうち、数項、環境、延長、表、所属、段階、最小性の七つを保持する。ここではキーの節は必要ない。二つの証人はすでに `s` を共有しており、そのキーに対応する値の一意性によって二つの表が同定されるからである。
<!--/-->

```agda
    private module WitnessBody (z T e' e s k Z : CS.S) (hb : ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩) where
      module Rd = BodyRd T e' e s k z Z
        using ( b-num; b-env; b-cons; b-tab; b-mem; b-stage; b-min )
```

<!--en-->
Two retained clauses immediately give that the extended environment lies in the table and that the witness lies in `Lset lam`. Once the key numeral is identified with `# n`, the environment clause also recovers an `n`-tuple of indices from `Z`.
<!--zh-->
其中两条子句立即给出延拓环境属于表，以及见证属于 `Lset lam`。一旦把键的数码认同为 `# n`，环境子句还会恢复出 `Z` 中索引组成的 `n` 元组。
<!--ja-->
保持した二つの節から、延長された環境が表に属することと、証人が `Lset lam` に属することが直ちに得られる。キーの数項を `# n` と同定すると、環境の節はさらに `Z` の添字からなる `n` 組を復元する。
<!--/-->

```agda
      h6 = Rd.b-mem hb
      h7 = Rd.b-stage hb
      module AtNum (n : ℕ) (qk : fst k ≡ # n) where
        module R = Recover Z n (Env T e' e s k z Z) i2 i4 i6 qk refl (Rd.b-env hb)
          using ( g; recovers )
```

<!--en-->
The recovered indices name their ambient values through the presentation of `Z`, and the recovery equation says that the extension environment names exactly these ambient values, in the order the indices list them.
<!--zh-->
恢复出的索引借助 `Z` 的指名其外围取值，而恢复等式说：扩展环境所命名的恰是这些外围取值，顺序即索引排列的顺序。
<!--ja-->
復元された添字は `Z` の提示を通して周囲の値を名指し、復元の等式は、拡張環境が名指すのはまさにこれらの周囲の値であり、その順序は添字の並びどおりであることを言う。
<!--/-->

```agda
        g′ : Fin n → V ℓ
        g′ i = ⟪ fst Z ⟫↪ (R.g i)
        hE : fst e ≡ env g′
        hE = R.recovers
```

<!--en-->
To prove uniqueness, take two body witnesses with the same `Z`, parameter environment `e`, and formula key `s`. Decoding the first arity numeral fixes a common length `n` for the recovered parameter sequence.
<!--zh-->
为证明唯一性，取两份具有相同 `Z`、参数环境 `e` 与公式键 `s` 的体见证。解码第一份见证的元数数码，便固定恢复参数序列的共同长度 `n`。
<!--ja-->
一意性を示すため、同じ `Z`、パラメータ環境 `e`、論理式のキー `s` をもつ二つの本体の証人を取る。最初の証人のアリティの数項を解読すると、復元されるパラメータ列の共通の長さ `n` が定まる。
<!--/-->

```agda
    private module WitnessUnique (Z e s z T e' k : CS.S) (hb : ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩) (z' T₂ e'₂ k₂ : CS.S) (hb₂ : ⟨ Env T₂ e'₂ e s k₂ z' Z ⊨ bodyFo ⟩) (n : ℕ) (qk : fst k ≡ # n) where
```

<!--en-->
The stage clauses turn `z` and `z'` into elements of `Lset lam`. They can therefore be compared by the well-order of that stage, while the decoded first witness supplies the common parameter sequence used for both bodies.
<!--zh-->
层子句把 `z` 与 `z'` 化为 `Lset lam` 的元素，因而可用该层的良序比较它们；第一份见证的解码则给出两个体共同使用的参数序列。
<!--ja-->
段階の節によって `z` と `z'` は `Lset lam` の要素となるので、その段階の整列順序で比較できる。また、最初の証人の解読から、二つの本体が共有するパラメータ列が得られる。
<!--/-->

```agda
      module A₁ = WitnessBody z T e' e s k Z hb
      module A₂ = WitnessBody z' T₂ e'₂ e s k₂ Z hb₂
      module N = A₁.AtNum n qk
      zS : SL
      zS = fst z , A₁.h7
```

<!--en-->
The second element is packaged likewise. The extension equations say that each body's environment is the parameter environment extended by its own witnessed element: `e'` names `z` consed onto the recovered values, and `e'₂` names `z'` the same way.
<!--zh-->
第二个元素同样打包。两条扩展等式说：每个体的环境都是参数环境添加自己的被见证元素后的扩展，`e'` 命名「把 `z` 添加到恢复值之前」，`e'₂` 以同样方式命名 `z'`。
<!--ja-->
二番目の要素も同様にまとめられる。拡張の等式は、それぞれの体の環境が、みずからの証明された要素を加えた拡張であることを言う。`e'` は復元された値の前に `z` を加えたものを名指し、`e'₂` も同じ仕方で `z'` を名指す。
<!--/-->

```agda
      z'S : SL
      z'S = fst z' , A₂.h7
      e'≡ : fst e' ≡ env (cons (fst z) N.g′)
      e'≡ = A₁.Rd.b-cons N.g′ N.hE hb
      e'₂≡ : fst e'₂ ≡ env (cons (fst z') N.g′)
```

<!--en-->
The two table slots are then shown to agree. Both bodies assert that the pair of the key `s` and their table belongs to the table family's pairs, and the injectivity of the code naming forces two tables paired with the same key to be equal.
<!--zh-->
随后证明两个表槽位一致。两个体都断言「键 `s` 与自己的表组成的对」属于表族的诸对，而码命名的单射性迫使与同一键配对的两个表相等。
<!--ja-->
ついで、二つの表のスロットが一致することが示される。どちらの体も、鍵 `s` とみずからの表の対が表の族の対に属すると主張し、コードの名指しの単射性が、同じ鍵と対にされた二つの表を等しく強制する。
<!--/-->

```agda
      e'₂≡ = A₂.Rd.b-cons N.g′ N.hE hb₂
      T≡ : fst T ≡ fst T₂
      T≡ =
        let p = SM.pairs-out s T (A₁.Rd.b-tab hb)
            q = SM.pairs-out s T₂ (A₂.Rd.b-tab hb₂)
```

<!--en-->
The table equality is assembled from the outward readings of the two table clauses: each table is the value named by the key, and the injectivity of code naming identifies the two keys' code indices. The statement `not-below` is then prepared: a strictly smaller constructible element with its own body witness cannot have its extension inside the other's table.
<!--zh-->
表等式由两条表子句的外向读法组装：每个表都是键所指名的取值，而码命名的单射性认同两把键的码索引。随后准备陈述 `not-below`：严格更小的可构造元素若带有自己的体见证、且其扩展落在对方的表中，则不可能。
<!--ja-->
表の等式は、二つの表の節の外向きの読みから組み立てられる。各表は鍵が名指す値であり、コードの名指しの単射性が二つの鍵のコードの添字を同一視する。ついで `not-below` が準備される。より真に小さい構成可能な要素がみずからの体の証人をもち、その拡張が相手の表の内側にあることはあり得ない。
<!--/-->

```agda
        in snd p ∙ cong (λ m → fst (SM.valOf s m))
          (snd (fst s ∈ fst (AllCodes A)) (fst p) (fst q)) ∙ sym (snd q)
      not-below : (a b : CS.S) (ha : ⟨ fst a ∈ fst A ⟩) (hb' : ⟨ fst b ∈ fst A ⟩)
                  (Ta e'a ka : CS.S) (hba : ⟨ Env Ta e'a e s ka a Z ⊨ bodyFo ⟩)
                  (e'b : CS.S) → fst e'b ≡ env (cons (fst b) N.g′) → ⟨ fst e'b ∈ fst Ta ⟩
```

<!--en-->
If a constructible candidate lies below one witness and its extended environment belongs to the same table, the minimality clause gives a contradiction. The stage well-order supplies the internal comparison relation needed by that clause.
<!--zh-->
若一个可构造候选严格低于某见证，且其延拓环境属于同一张表，最小性子句便给出矛盾。层上的良序提供该子句所需的内部比较关系。
<!--ja-->
構成可能な候補が一方の証人より真に下にあり、その延長された環境が同じ表に属するなら、最小性の節から矛盾が得られる。段階の整列順序が、その節に必要な内部の比較関係を与える。
<!--/-->

```agda
                → relOf wL (fst b , hb') (fst a , ha) → ⊥₀
      not-below a b ha hb' Ta e'a ka hba e'b qe hm b<a =
        BodyRd.b-min Ta e'a e s ka a Z N.g′ N.hE hba b hb' e'b qe hm
          (relL-fill lam λ-isL ordλ (fst b , hb') (fst a , ha) b<a)
      result : fst z ≡ fst z'
```

<!--en-->
The result follows by the trichotomy of the internal well-order on the two packaged witnesses. If `z` were below `z'`, the smaller element `z` would contradict the minimality recorded by `z'`'s body, the shared table supplied through the table equality.
<!--zh-->
结果由内部良序在两个打包见证上的三歧性得出。若 `z` 低于 `z'`，则更小的 `z` 将与 `z'` 的体所记录的最小性矛盾，此时共享的表经由表等式供给。
<!--ja-->
結果は、まとめられた二つの証人の上の内部の整列順序の三分法から従う。`z` が `z'` より下なら、より小さい `z` が `z'` の体の記録する最小性と矛盾する。共有された表は表の等式を通して供給される。
<!--/-->

```agda
      result = go (SWO.tri∙ wL zS z'S)
        where
        go : Tri∙ (relOf wL zS z'S) (zS ≡ z'S) (relOf wL z'S zS) → fst z ≡ fst z'
        go (tri-lt h) = ⊥₀-rec (not-below z' z A₂.h7 A₁.h7 T₂ e'₂ k₂ hb₂ e' e'≡
                      (subst (λ t → ⟨ fst e' ∈ t ⟩) T≡ A₁.h6) h)
```

<!--en-->
If the two packaged witnesses are equal, their underlying sets are equal. The remaining strict case is symmetric: if `z'` lies below `z`, the minimality of `z` gives a contradiction.
<!--zh-->
若两个打包见证相等，则其底层集合相等。余下的严格次序情形与前者对称：若 `z'` 低于 `z`，便与 `z` 的最小性矛盾。
<!--ja-->
まとめられた二つの証人が等しければ、その基礎にある集合も等しい。残る狭義順序の場合は対称であり、`z'` が `z` より下なら `z` の最小性に矛盾する。
<!--/-->

```agda
        go (tri-eq q) = cong fst q
        go (tri-gt h) = ⊥₀-rec (not-below z z' A₁.h7 A₂.h7 T e' k hb e'₂ e'₂≡
                      (subst (λ t → ⟨ fst e'₂ ∈ t ⟩) (sym T≡) A₂.h6) h)
```

<!--en-->
Uniqueness of least witnesses is assembled: two witnesses for the same `Z`, `e` and `s` have equal underlying elements. The two truncations are consumed together, the goal being an equality in an h-set.
<!--zh-->
最小见证的唯一性由此组装：同一 `Z`、`e`、`s` 的两个见证具有相等的底层元素。两层截断被一起消耗，目标是 h-集合中的等式。
<!--ja-->
最小証人の一意性が組み上がる。同じ `Z`、`e`、`s` に対する二つの証人は、等しい基底要素をもつ。二つの切り詰めは一緒に消費され、目標は h-集合における等式である。
<!--/-->

```agda
    opaque
      leastWitness-unique : (Z e s z z' : CS.S) → LeastWitness Z e s z
                          → LeastWitness Z e s z' → fst z ≡ fst z'
      leastWitness-unique Z e s z z' = rec2 (setIsSet (fst z) (fst z')) inner
        where
```

<!--en-->
The inner lemma receives both unpacked body witnesses: tables, extensions, keys, and body satisfactions for the two candidate elements `z` and `z'`.
<!--zh-->
内层引理接收两份拆开的体见证：候选元素 `z` 与 `z'` 各自的表、扩展、键与体满足。
<!--ja-->
内側の補題は、展開された二つの体の証人を受け取る。候補の要素 `z` と `z'` のそれぞれに対する表、拡張、鍵、そして体の充足である。
<!--/-->

```agda
        inner : (Σ[ T ∈ CS.S ] Σ[ e' ∈ CS.S ] Σ[ k ∈ CS.S ]
                   ⟨ Env T e' e s k z Z ⊨ bodyFo ⟩)
              → (Σ[ T₂ ∈ CS.S ] Σ[ e'₂ ∈ CS.S ] Σ[ k₂ ∈ CS.S ]
                   ⟨ Env T₂ e'₂ e s k₂ z' Z ⊨ bodyFo ⟩)
              → fst z ≡ fst z'
```

<!--en-->
The first key is decoded to a numeral, allowing the preceding uniqueness argument to run at that arity. The same decoding principle is recorded as `ω-num`: every member of the internal `ω` is, up to truncation, an ambient numeral `# n`.
<!--zh-->
第一条键被解码为一个数码，使前述唯一性论证可在该元数处进行。同一解码原理写成 `ω-num`：内部 `ω` 的每个成员在命题截断意义下都是某个外围数码 `# n`。
<!--ja-->
最初のキーを数項へ解読すると、先の一意性の議論をそのアリティで行える。同じ解読原理を `ω-num` として記録する。内部の `ω` の各要素は、命題的切り詰めのもとで、ある周囲の数項 `# n` である。
<!--/-->

```agda
        inner (T , e' , k , hb) (T₂ , e'₂ , k₂ , hb₂) =
          rec₁ (setIsSet (fst z) (fst z'))
            (λ { (n , qk) → WitnessUnique.result Z e s z T e' k hb z' T₂ e'₂ k₂ hb₂ n qk })
            (decode-num k (BodyRd.b-num T e' e s k z Z hb))
    ω-num : (q : CS.S) → ⟨ fst q ∈ˢ fst ωʟ ⟩ → ∥ Σ[ n ∈ ℕ ] (fst q ≡ # n) ∥₁
```

<!--en-->
The decoding maps a member of the internal `ω` to a natural number with the numeral equation, and `vecOf` turns a function on `Fin k` into a length-`k` vector of constructible elements, the form the satisfaction clauses consume.
<!--zh-->
解码把内部 `ω` 的成员映射为自然数并附数码等式；`vecOf` 把 `Fin k` 上的函数变成长度 `k` 的可构造元素向量，即满足子句所消耗的形态。
<!--ja-->
解読は、内部の `ω` の要素を数項の等式とともに自然数へ写す。そして `vecOf` は `Fin k` の上の関数を、構成可能な要素の長さ `k` のベクトル、すなわち充足の節が消費する形へ変える。
<!--/-->

```agda
    ω-num q h = map₁ (λ { (n , e) → lower n , (e ∙ numeralL-fst (lower n)) })
      (subst ⟨_⟩ (ω-specL q) h)
    vecOf : {k : ℕ} → (Fin k → SL) → Vec SL k
    vecOf {zero} f = []
    vecOf {suc k} f = f zero ∷ vecOf (λ i → f (suc i))
```

<!--en-->
Lookups in `vecOf f` recover `f` entry by entry. Now fix a set `Z`, an arity `k`, a formula `χ` with one witness variable and `k` parameter variables, a parameter vector `vs` drawn from `Z`, and evidence that `χ` has a witness at `vs`.
<!--zh-->
在 `vecOf f` 中逐项查找会恢复 `f`。现固定集合 `Z`、元数 `k`、含一个见证变量与 `k` 个参数变量的公式 `χ`、取自 `Z` 的参数向量 `vs`，以及 `χ` 在 `vs` 处有见证的证据。
<!--ja-->
`vecOf f` の各成分を参照すると `f` が復元される。ここで、集合 `Z`、アリティ `k`、一つの証人変数と `k` 個のパラメータ変数をもつ論理式 `χ`、`Z` から取ったパラメータベクトル `vs`、そして `χ` が `vs` で証人をもつことの証拠を固定する。
<!--/-->

```agda
    lookup-vecOf : {k : ℕ} (f : Fin k → SL) (i : Fin k) → lookup i (vecOf f) ≡ f i
    lookup-vecOf {suc k} f zero = refl
    lookup-vecOf {suc k} f (suc i) = lookup-vecOf (λ j → f (suc j)) i
    module Least (Z : CS.S) (k : ℕ) (χ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec SL k)
                 (from : From Z vs) (w₀ : Sat k χ vs) where
```

<!--en-->
The predicate to be minimized says of an element `a` that the extended environment `(a ∷ vs)` satisfies `χ`. It is packaged as a proposition, so it can serve as the leastness predicate of a well-order.
<!--zh-->
被最小化的谓词说：元素 `a` 使扩展环境 `(a ∷ vs)` 满足 `χ`。它被打包为命题，故可充当良序的最小性谓词。
<!--ja-->
最小化される述語は、要素 `a` について、拡張された環境 `(a ∷ vs)` が `χ` を充足することを述べる。これは命題としてまとめられるため、整列順序の最小性の述語として働ける。
<!--/-->

```agda
      P : SL → hProp (ℓ-suc ℓ)
      P a = (a ∷ vs) ⊨₀ χ
```

<!--en-->
This predicate has no hidden host-only component. The object-language formula is `χ`, a candidate `a` determines the extended environment `a ∷ vs`, and the reusable package `searchPredicate k χ vs` has semantic reading judgmentally equal to `P`.
<!--zh-->
这个谓词不含隐藏的纯宿主成分。对象语言公式就是 `χ`，候选 `a` 决定扩展环境 `a ∷ vs`，而可复用的包 `searchPredicate k χ vs` 之语义读取在定义上就是 `P`。
<!--ja-->
この述語には、隠れたホストだけの成分はない。対象言語の論理式は `χ` であり、候補 `a` が拡張環境 `a ∷ vs` を決め、再利用できるパッケージ `searchPredicate k χ vs` の意味論的な読みは定義上 `P` そのものである。
<!--/-->

<!--en-->
The least witness `a` is selected by the least-element search along the internal well-order of `L`, applied to this predicate and the nonemptiness record.
<!--zh-->
最小见证 `a` 由 `L` 的内部良序上的最小元搜索选取，施用于该谓词与非空记录。
<!--ja-->
最小証人 `a` は、この述語と非空の記録に対して、`L` の内部の整列順序に沿う最小要素の探索によって選ばれる。
<!--/-->

```agda
      a : SL
      a = leastOfFormula wL (searchPredicate k χ vs) lem w₀ .fst
```

<!--en-->
Its leastness data is kept in full: `a` satisfies the predicate, and no smaller element of the well-order satisfies it.
<!--zh-->
其最小性数据被完整保留：`a` 满足该谓词，而良序中没有更小的元素满足它。
<!--ja-->
その最小性のデータは丸ごと保持される。`a` は述語を満たし、整列順序のより小さい要素は述語を満たさない。
<!--/-->

```agda
      a-least : IsLeast wL P a
      a-least = leastOfFormula wL (searchPredicate k χ vs) lem w₀ .snd
```

<!--en-->
Because the chosen witness `a` belongs to `Lset lam`, it is constructible and can be viewed as an element `aS` of the constructible carrier. For each parameter position, `g` chooses an index in the presentation of `Z` naming that parameter.
<!--zh-->
所选见证 `a` 属于 `Lset lam`，因此可构造，可视为可构造载体中的元素 `aS`。对每个参数位置，`g` 在 `Z` 的呈现中选择一个指名该参数的索引。
<!--ja-->
選ばれた証人 `a` は `Lset lam` に属するので構成可能であり、構成可能な台の要素 `aS` とみなせる。各パラメータ位置について、`g` はそのパラメータを名指す添字を `Z` の表示から選ぶ。
<!--/-->

```agda
      aS : CS.S
      aS = fst a , Lset→isL lam ordλ (fst a) (snd a)
      g : Ix Z k
      g i = fiber (fst Z) (from i) .fst
```

<!--en-->
The naming equation says that each parameter's index presents exactly that parameter: the embedded index equals the parameter as an element of `L`.
<!--zh-->
命名等式说：每个参数的索引所呈现的恰是该参数；被嵌入的索引作为 `L` 的元素等于该参数。
<!--ja-->
名指しの等式は、各パラメータの添字が提示するのはまさにそのパラメータであることを言う。埋め込まれた添字は、`L` の要素としてそのパラメータに等しいのである。
<!--/-->

```agda
      g-val : (i : Fin k) → ⟪ fst Z ⟫↪ (g i) ≡ fst (lookup i vs)
      g-val i = fiber (fst Z) (from i) .snd
```

<!--en-->
The ambient values of the parameters are collected in `g′`, one per slot, so that the parameter environment can be described both internally and ambiently.
<!--zh-->
参数的外围取值收于 `g′`，每槽一个，使参数环境既能在内部、也能在外围被描述。
<!--ja-->
パラメータの周囲の値は `g′` に集められ、スロットごとに一つである。これによりパラメータの環境は、内部と周囲の両方で記述できる。
<!--/-->

```agda
      g′ : Fin k → V ℓ
      g′ i = ⟪ fst Z ⟫↪ (g i)
```

<!--en-->
The parameter environment `e` is the internal graph of these values over `Z`, and `ext b` is the extension environment for a candidate `b`: the parameters with `b` consed in front.
<!--zh-->
参数环境 `e` 是这些取值在 `Z` 之上的内部图；`ext b` 是候选 `b` 的扩展环境：即把 `b` 添到参数之前的那个环境。
<!--ja-->
パラメータの環境 `e` は、これらの値の `Z` の上の内部のグラフであり、`ext b` は候補 `b` の拡張環境である。パラメータの前に `b` を加えたものである。
<!--/-->

```agda
      e : CS.S
      e = envS Z g
      ext : SL → CS.S
      ext b = envFor A (b ∷ vs)
```

<!--en-->
The extension's graph equation says that its underlying set is the graph of the candidate consed onto the ambient parameter values, the two readings of the extension being identified entry by entry.
<!--zh-->
扩展的图等式说：其底层集合是「候选 `b` 添加到外围参数值之前」的图；扩展的两种读法逐条目被等同。
<!--ja-->
拡張のグラフの等式は、その基底集合が、候補 `b` を周囲のパラメータの値の前に加えたグラフであることを言う。拡張の二つの読みは項目ごとに同一視される。
<!--/-->

```agda
      ext-graph : (b : SL) → fst (ext b) ≡ env (cons (fst b) g′)
      ext-graph b = envFor-graph A (b ∷ vs)
        ∙ cong env (funExt (λ { zero → refl ; (suc i) → sym (g-val i) }))
```

<!--en-->
The extension belongs to the satisfaction table of `χ` at arity `suc k` exactly when the extended environment satisfies `χ`. The table here is the one for this formula alone, and the equation is what lets membership in the table be traded for satisfaction.
<!--zh-->
扩展属于 `χ` 在元数 `suc k` 处的满足表，恰当扩展环境满足 `χ`。这里的表是仅属于这条公式的表，而这条等式使「属于表」可以换读为「满足」。
<!--ja-->
拡張は、アリティ `suc k` における `χ` の充足の表に属するのは、拡張された環境が `χ` を充足するとき、かつそのときに限る。ここでの表はこの論理式だけのための表であり、この等式によって、表への所属を充足と読み替えられるのである。
<!--/-->

```agda
      ext-sat : (b : SL) → (ext b CS.∈ˢ Tof (suc k) χ) ≡ ((b ∷ vs) ⊨₀ χ)
      ext-sat b = sat-at (suc k) χ (b ∷ vs) (ext b) (envFor-graph A (b ∷ vs))
```

<!--en-->
The key `sS` names the formula and its arity: it is the pair by which the table family indexes the table of `χ`.
<!--zh-->
键 `sS` 点名公式及其元数：它正是表族用以索引 `χ` 之表的那个对。
<!--ja-->
鍵 `sS` は論理式とそのアリティを名指す。表の族が `χ` の表を索引するための対である。
<!--/-->

```agda
      sS : CS.S
      sS = keyOf (suc k) χ
```

<!--en-->
The table `T` is the satisfaction table of `χ` at arity `suc k`, the set in which satisfying extensions are collected.
<!--zh-->
表 `T` 是 `χ` 在元数 `suc k` 处的满足表，即收集满足扩展的那个集合。
<!--ja-->
表 `T` はアリティ `suc k` における `χ` の充足の表であり、充足する拡張が集められる集合である。
<!--/-->

```agda
      T : CS.S
      T = Tof (suc k) χ
```

<!--en-->
The seven-entry environment `γ₇` assembles the whole picture: the table, the extension by the least witness, the parameter environment, the key, the numeral of the arity, the packaged witness, and the base set `Z`.
<!--zh-->
七条目环境 `γ₇` 把整个图景装配起来：表、由最小见证扩展的环境、参数环境、键、元数的数码、打包后的见证，以及基集合 `Z`。
<!--ja-->
七項目の環境 `γ₇` が全体の絵を組み上げる。表、最小証人による拡張、パラメータの環境、鍵、アリティの数項、まとめられた証人、そして基礎集合 `Z` である。
<!--/-->

```agda
      γ₇ : CS.S ^ 7
      γ₇ = Env T (ext a) e sS (nn k) aS Z
```

<!--en-->
The first clause records that the numeral of the arity belongs to the internal `ω`, the length of an environment being a natural number.
<!--zh-->
第一条子句记录：元数的数码属于内部 `ω`，因为环境的长度是自然数。
<!--ja-->
第一の節は、アリティの数項が内部の `ω` に属することを記録する。環境の長さは自然数だからである。
<!--/-->

```agda
      c1 : ⟨ γ₇ ⊨ (var i4 ∈̇ con ωʟ) ⟩
      c1 = #∈ω k
```

<!--en-->
The key clause says that the key belongs to the code set and pairs the successor numeral with the code of `χ`; the code is a free code, and free codes live in the limit stage of `ω`.
<!--zh-->
键子句说：键属于码集，并且是「后继数码与 `χ` 的码」组成的对；该码是自由码，而自由码住在 `ω` 的极限层中。
<!--ja-->
鍵の節は、鍵がコードの集合に属し、後続の数項と `χ` のコードの対であることを述べる。このコードは自由コードであり、自由コードは `ω` の極限の段階に住む。
<!--/-->

```agda
      c2 : ⟨ γ₇ ⊨ keyIn i3 i4 ⟩
      c2 = KeyIn.keyIn-in i3 i4 γ₇ k refl
        (subst (λ u → ⟨ u ∈ˢ fst C₀ ⟩) (sym (keyOf-fst (suc k) χ)) (freeCode-in (suc k) χ))
        (fst (limitCode χ)) (keyOf-fst (suc k) χ)
```

<!--en-->
The environment clause says that the parameter environment is an environment of length `nn k` over `Z`, with the values `g′`; it is transported from the environment lemma of `e` to the seven-entry context.
<!--zh-->
环境子句说：参数环境是 `Z` 上长度 `nn k`、取值 `g′` 的环境；它从 `e` 的环境引理被传输到七条目语境。
<!--ja-->
環境の節は、パラメータの環境が `Z` の上の長さ `nn k`、値 `g′` の環境であることを述べる。これは `e` の環境の補題から七項目の文脈へ輸送される。
<!--/-->

```agda
      c3 : ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
      c3 = envOverAt-transport (Z ∷ nn k ∷ e ∷ []) γ₇ i2 i1 i0 i2 i4 i6 refl refl refl
             (envOver Z g)
```

<!--en-->
The extension equation repeats that the extension by the least witness is the graph of the witness consed onto the parameter values.
<!--zh-->
扩展等式重复：由最小见证扩展的环境，是把见证添加到参数值之前所得的图。
<!--ja-->
拡張の等式は、最小証人による拡張が、パラメータの値の前に証人を加えたグラフであることを繰り返す。
<!--/-->

```agda
      c4 : fst (ext a) ≡ env (cons (fst a) g′)
      c4 = ext-graph a
```

<!--en-->
The pair of the key and the table belongs to the pairs of the table family, which is how the table is indexed by its key.
<!--zh-->
键与表组成的对属于表族的诸对；表正是以这样的对被其键索引。
<!--ja-->
鍵と表の対は、表の族の対に属する。表がみずからの鍵によって索引されるのはこの仕組みである。
<!--/-->

```agda
      c5 : ⟨ pr (fst sS) (fst T) ∈ˢ fst SM.pairs ⟩
      c5 = Tof-pair (suc k) χ
```

<!--en-->
The extension by the least witness belongs to the table: the table's membership equation reads it as satisfaction of `χ`, and the leastness data supplies exactly that satisfaction.
<!--zh-->
由最小见证得到的扩展属于表：表的隶属等式把它读作对 `χ` 的满足，而最小性数据恰供给了这份满足。
<!--ja-->
最小証人による拡張は表に属する。表の所属の等式がそれを `χ` の充足として読み、最小性のデータがまさにその充足を供給するのである。
<!--/-->

```agda
      c6 : ⟨ fst (ext a) ∈ˢ fst T ⟩
      c6 = transport (sym (cong ⟨_⟩ (ext-sat a))) (a-least .fst)
```

<!--en-->
The least witness belongs to the stage `Lset lam`; in the internal presentation `A = LsetS lam ordλ`, this is exactly the membership proof carried by `a`.
<!--zh-->
最小见证属于层 `Lset lam`；在内部表示 `A = LsetS lam ordλ` 中，这正是 `a` 所携带的隶属证明。
<!--ja-->
最小証人は段階 `Lset lam` に属する。内部表示 `A = LsetS lam ordλ` では、これはまさに `a` がもつ所属の証明である。
<!--/-->

```agda
      c7 : ⟨ fst aS ∈ˢ fst A ⟩
      c7 = snd a
```

<!--en-->
The minimality clause excludes every candidate `w'` in `Lset lam` whose extended environment belongs to the table: its packaged form cannot lie strictly below the chosen witness. This is precisely the leastness property of `a`.
<!--zh-->
最小性子句排除 `Lset lam` 中每个满足如下条件的候选 `w'`：若其延拓环境属于该表，则其打包形式不可能严格低于所选见证。这正是 `a` 的最小性。
<!--ja-->
最小性の節は、延長された環境が表に属するような `Lset lam` の各候補 `w'` を排除する。そのまとめられた形が選ばれた証人より真に下にあることはできない。これはまさに `a` の最小性である。
<!--/-->

```agda
      c8 : BodyRd.Min T (ext a) e sS (nn k) aS Z g′
      c8 w' w'∈ e'' q hm hr = a-least .snd w'S sat lt'
        where
        w'S : SL
        w'S = fst w' , w'∈
```

<!--en-->
The internal relation between the smaller candidate and `a` is filled from the ambient well-order restricted to constructible elements, and the candidate satisfies `χ`: its extension belongs to the table, read as satisfaction through the extension equation.
<!--zh-->
较小候选与 `a` 之间的内部关系，由限制在可构造元素上的外围良序填充；而该候选满足 `χ`：其扩展属于表，经扩展等式读作满足。
<!--ja-->
より小さい候補と `a` の間の内部の関係は、構成可能な要素に制限した周囲の整列順序から満たされ、候補は `χ` を充足する。その拡張が表に属することを、拡張の等式を通して充足として読むのである。
<!--/-->

```agda
        lt' : relOf-at w'S a
        lt' = relL-rep lam λ-isL ordλ w'S a hr
        sat : ⟨ (w'S ∷ vs) ⊨₀ χ ⟩
        sat = transport (cong ⟨_⟩ (ext-sat w'S))
                (subst (λ t → ⟨ t ∈ˢ fst T ⟩) (q ∙ sym (ext-graph w'S)) hm)
```

<!--en-->
The eight clauses together show that `witFo` holds at `(aS, Z)`: `a` is the least witness of `χ` over the chosen parameters, expressed entirely inside the constructible structure. We next read the same body data outward under the assumption that every member of `Z` lies in `Lset lam`.
<!--zh-->
八条子句合起来证明 `witFo` 在 `(aS, Z)` 处成立：`a` 是 `χ` 在所选参数上的最小见证，而且这一事实完全在可构造结构内部表达。接下来假设 `Z` 的每个成员都属于 `Lset lam`，并把同一份体数据读到外围。
<!--ja-->
八つの節を合わせると、`witFo` が `(aS, Z)` で成り立つ。すなわち `a` は、選んだパラメータにおける `χ` の最小証人であり、この事実は構成可能な構造の内部だけで表されている。次に、`Z` の各要素が `Lset lam` に属すると仮定し、同じ本体のデータを周囲で読む。
<!--/-->

```agda
      least : ⟨ (aS ∷ Z ∷ []) ⊨ witFo ⟩
      least = witFo-in aS Z T (ext a) e sS (nn k)
        (BodyRd.b-fill T (ext a) e sS (nn k) aS Z g′ refl c1 c2 c3 c4 c5 c6 c7 c8)
    module Out (Z : CS.S) (Z⊆ : (z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (w T e' e s k : CS.S) (h : ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩) where
```

<!--en-->
A body witness provides eight facts: the arity numeral, key shape, recovered parameter environment, extension equation, indexed table, table membership, stage membership, and minimality. Their outward readings reconstruct the semantic search represented by the code.
<!--zh-->
一份体见证提供八项事实：元数数码、键的形状、恢复出的参数环境、延拓等式、带索引的表、表隶属、层隶属与最小性。把这些事实读到外围，便可重建该码所表示的语义搜索。
<!--ja-->
本体の証人は八つの事実を与える。アリティの数項、キーの形、復元されたパラメータ環境、延長の等式、添字付けられた表、表への所属、段階への所属、そして最小性である。これらを周囲で読むと、コードが表す意味論的な探索を復元できる。
<!--/-->

```agda
      module Rd = BodyRd T e' e s k w Z
        using ( b-num; b-key; b-env; b-cons; b-tab; b-mem; b-stage; b-min )
```

<!--en-->
The stage clause proves that the witnessed set `w` belongs to `Lset lam`. Pairing `w` with this proof gives `wS`, the corresponding element of the stage carrier.
<!--zh-->
层子句证明被见证集合 `w` 属于 `Lset lam`。把 `w` 与这份证明配对，得到层载体中的相应元素 `wS`。
<!--ja-->
段階の節は、証人となる集合 `w` が `Lset lam` に属することを示す。`w` とこの証明を組にすると、段階の台の対応する要素 `wS` が得られる。
<!--/-->

```agda
      wS : SL
      wS = fst w , Rd.b-stage h
```

<!--en-->
The arity component of a decoded key belongs to the internal `ω`. Thus, up to propositional truncation, it is some numeral `# n`; fixing such an `n` lets us analyze the key at an ordinary natural-number arity.
<!--zh-->
已解码键的元数分量属于内部 `ω`，因此在命题截断意义下等于某个数码 `# n`。固定这样的 `n` 后，便可在通常的自然数元数处分析该键。
<!--ja-->
解読されたキーのアリティ成分は内部の `ω` に属する。したがって命題的切り詰めのもとで、ある数項 `# n` に等しい。この `n` を固定すれば、通常の自然数のアリティでキーを分析できる。
<!--/-->

```agda
      module AtNum (n : ℕ) (qk : fst k ≡ # n) where
```

<!--en-->
Inside this case, the first fact says that the slot component `s` of the key is itself a code, that is, a member of `C₀`. This follows from the key inversion: a key is the ordered pair of an arity numeral and a code, and reading the pair apart exhibits the code.
<!--zh-->
在此情形中，第一条事实说：键的槽位分量 `s` 本身就是一个码，即 `C₀` 的成员。这由键的求逆得出：键是有序对「元数数码与码」，把对拆开便显现出码。
<!--ja-->
この場合の最初の事実は、鍵のスロット成分 `s` がそれ自体コード、すなわち `C₀` の要素であることを言う。これは鍵の逆読みから従う。鍵はアリティの数項とコードの順序対であり、対を分解すればコードが現れる。
<!--/-->

```agda
        s∈ : ⟨ fst s ∈ˢ fst C₀ ⟩
        s∈ = KeyIn.keyIn-out i3 i4 (Env T e' e s k w Z) n qk (Rd.b-key h) .fst
```

<!--en-->
With the arity identified as `n`, the environment clause recovers a function `g : Fin n → ⟪ fst Z ⟫` and proves that the coded parameter environment is the graph of the values named by those indices.
<!--zh-->
把元数认同为 `n` 后，环境子句恢复出函数 `g : Fin n → ⟪ fst Z ⟫`，并证明编码的参数环境正是这些索引所指名之值的图。
<!--ja-->
アリティを `n` と同定すると、環境の節から関数 `g : Fin n → ⟪ fst Z ⟫` が復元され、符号化されたパラメータ環境が、それらの添字の名指す値のグラフであることが示される。
<!--/-->

```agda
        module R = Recover Z n (Env T e' e s k w Z) i2 i4 i6 qk refl (Rd.b-env h) using ( g; recovers )
```

<!--en-->
The recovered environment lists indices into the starting set. Each index is presented as an ambient element by the embedding of its presentation, giving the vector `g′` of underlying sets.
<!--zh-->
恢复出的环境列出起始集合的索引。每个索引经由其呈现的嵌入被实现为外围元素，得到底层集构成的向量 `g′`。
<!--ja-->
復元された環境は、始集合の索引の列である。各索引はその提示の埋め込みによって周囲の要素として実現され、底の集合のベクトル `g′` が得られる。
<!--/-->

```agda
        g′ : Fin n → V ℓ
        g′ i = ⟪ fst Z ⟫↪ (R.g i)
```

<!--en-->
The vector `vs` collects the same elements as entries of the constructible carrier, pairing each with the proof that it is constructible.
<!--zh-->
向量 `vs` 把同样的元素收集为可构造载体的条目，并为每个条目配上其可构造性的证明。
<!--ja-->
ベクトル `vs` は、同じ要素を構成可能な台の項目として集め、それぞれに構成可能性の証明を対にする。
<!--/-->

```agda
        vs : Vec SL n
        vs = vecOf (λ i → g′ i , Z⊆ (g′ i) (member (fst Z) (R.g i)))
```

<!--en-->
For every position `i`, the first component of `lookup i vs` is `g′ i`. Thus `vs` and `g′` describe the same parameter sequence, once as elements of the stage carrier and once as ambient sets.
<!--zh-->
对每个位置 `i`，`lookup i vs` 的第一分量都是 `g′ i`。因此 `vs` 与 `g′` 描述同一参数序列，前者把它写成层载体的元素，后者把它写成外围集合。
<!--ja-->
各位置 `i` について、`lookup i vs` の第一成分は `g′ i` である。したがって `vs` と `g′` は同じパラメータ列を、一方は段階の台の要素として、他方は周囲の集合として表す。
<!--/-->

```agda
        vs-val : (i : Fin n) → fst (lookup i vs) ≡ g′ i
        vs-val i = cong fst (lookup-vecOf (λ i → g′ i , Z⊆ (g′ i) (member (fst Z) (R.g i))) i)
```

<!--en-->
The recovered environment genuinely comes from the starting set: each entry of `vs`, read as a set, is a member of `Z`. This is the `From Z vs` record.
<!--zh-->
恢复出的环境确实来自起始集合：`vs` 的每个条目作为集合都是 `Z` 的成员。这正是 `From Z vs` 记录。
<!--ja-->
復元された環境は、実際に始集合から来ている。`vs` の各項目は、集合として読めば `Z` の要素である。これが `From Z vs` の記録である。
<!--/-->

```agda
        from : From Z vs
        from i = subst (λ u → ⟨ u ∈ˢ fst Z ⟩) (sym (vs-val i)) (member (fst Z) (R.g i))
```

<!--en-->
The recovery equation identifies the original environment component `e` with `env g′`, the graph formed from the recovered ambient values.
<!--zh-->
恢复等式把原环境分量 `e` 与 `env g′` 同一视；后者是由恢复出的外围取值形成的图。
<!--ja-->
復元の等式は、元の環境成分 `e` を `env g′`、すなわち復元された周囲の値から作られるグラフと同定する。
<!--/-->

```agda
        hE : fst e ≡ env g′
        hE = R.recovers
```

<!--en-->
The witness slot is compared with other candidates by extending the recovered environment by one entry: `ext b` is the environment with `b` prepended to `vs`.
<!--zh-->
见证槽位与其他候选的比较，通过把恢复的环境延长一个条目来进行：`ext b` 即把 `b` 前置到 `vs` 之前的环境。
<!--ja-->
証人のスロットは、復元された環境を一項目だけ延ばすことで他の候補と比較される。`ext b` は `b` を `vs` の前に置いた環境である。
<!--/-->

```agda
        ext : SL → CS.S
        ext b = envFor A (b ∷ vs)
```

<!--en-->
The underlying environment of this extension computes to the cons of the underlying set of `b` with `g′`: the graph description of the extended environment matches entry by entry.
<!--zh-->
这一延拓的底层环境计算为 `b` 的底层集与 `g′` 的 cons：延拓环境的图描述逐条目吻合。
<!--ja-->
この延長の底の環境は、`b` の底の集合と `g′` の cons として計算され、延長された環境のグラフの記述は項目ごとに一致する。
<!--/-->

```agda
        ext-graph : (b : SL) → fst (ext b) ≡ env (cons (fst b) g′)
        ext-graph b = envFor-graph A (b ∷ vs)
          ∙ cong env (funExt (λ { zero → refl ; (suc i) → vs-val i }))
```

<!--en-->
The key's own environment component is identified with `ext wS`: extending the recovered environment by the witness slot is exactly what the key recorded.
<!--zh-->
键自身的环境分量被认同为 `ext wS`：把恢复的环境以见证槽延拓，正是键所记录的内容。
<!--ja-->
鍵自身の環境成分は `ext wS` と同一視される。復元された環境を証人のスロットで延ばしたものが、まさに鍵が記録していたものである。
<!--/-->

```agda
        e'≡ : fst e' ≡ fst (ext wS)
        e'≡ = Rd.b-cons g′ hE h ∙ sym (ext-graph wS)
```

<!--en-->
Now choose the formula `χ` decoded from the code component and identify `s` with its canonical key `keyOf (suc n) χ`. The environment, formula, and key then all describe the same satisfaction query.
<!--zh-->
现取从码分量解出的公式 `χ`，并把 `s` 与其典范键 `keyOf (suc n) χ` 同一视。于是环境、公式与键都描述同一个满足查询。
<!--ja-->
ここでコード成分から解読された論理式 `χ` を取り、`s` をその正準なキー `keyOf (suc n) χ` と同定する。これで環境、論理式、キーはすべて同じ充足の問いを表す。
<!--/-->

```agda
        module AtCode (χ : Formula (⊥* {ℓ}) (suc n)) (qs : fst s ≡ fst (keyOf (suc n) χ)) where
```

<!--en-->
The predicate `P b` says that `b`, prepended to the recovered environment, satisfies `χ`. It is the property that the least-witness search minimizes over.
<!--zh-->
谓词 `P b` 说：把 `b` 前置到恢复的环境后满足 `χ`。这正是最小见证搜索所最小化的性质。
<!--ja-->
述語 `P b` は、`b` を復元された環境の前に置けば `χ` を充足することを言う。これが、最小の証人の探索が最小化する性質である。
<!--/-->

```agda
          P : SL → hProp (ℓ-suc ℓ)
          P b = (b ∷ vs) ⊨₀ χ
```

<!--en-->
Membership in the satisfaction table of `χ` agrees with `P b`, because the environment of `ext b` computes to the graph of `b ∷ vs`. This converts between the coded and the semantic readings of satisfaction.
<!--zh-->
在 `χ` 的满足表中的隶属与 `P b` 一致，因为 `ext b` 的环境计算为 `b ∷ vs` 的图。这在满足的编码读法与语义读法之间转换。
<!--ja-->
`χ` の充足表への所属は `P b` と一致する。`ext b` の環境が `b ∷ vs` のグラフとして計算されるからである。これが、充足の符号化された読みと意味論的な読みを切り替える。
<!--/-->

```agda
          ext-sat : (b : SL) → ⟨ ext b CS.∈ˢ Tof (suc n) χ ⟩ ≡ ⟨ P b ⟩
          ext-sat b = cong ⟨_⟩ (sat-at (suc n) χ (b ∷ vs) (ext b) (envFor-graph A (b ∷ vs)))
```

<!--en-->
The table component of the key is next identified with the satisfaction table of `χ` at the raised arity; with both components decoded, the key's member can be read semantically.
<!--zh-->
键的表分量随后被认同为 `χ` 在提升元数处的满足表；两个分量都解码后，键的成员便可按语义读取。
<!--ja-->
鍵の表の成分は、アリティを上げた `χ` の充足表と同一視される。両成分が解読されれば、鍵の要素を意味論的に読める。
<!--/-->

```agda
          module AtTable (qT : fst T ≡ fst (Tof (suc n) χ)) where
```

<!--en-->
The witness slot satisfies the recovered formula: the membership recorded in the key is transported along the environment and table identifications into satisfaction of `χ` at the extended environment.
<!--zh-->
见证槽位满足恢复出的公式：键中记录的隶属沿环境与表的同一视搬运，成为 `χ` 在延拓环境处的满足。
<!--ja-->
証人のスロットは、復元された論理式を充足する。鍵に記録された所属が、環境と表の同一視に沿って運ばれ、延長された環境のもとでの `χ` の充足になる。
<!--/-->

```agda
            sat : ⟨ P wS ⟩
            sat = transport (ext-sat wS)
              (subst2 (λ u t → ⟨ u ∈ˢ t ⟩) e'≡ qT (Rd.b-mem h))
```

<!--en-->
Leastness says that no stage element `b` satisfying `χ` lies below `wS`. Satisfaction of `χ` is converted into membership of `ext b` in the recovered table, and the stage well-order is converted into the internal relation required by the body's minimality clause.
<!--zh-->
最小性断言：不存在满足 `χ` 且严格低于 `wS` 的层元素 `b`。`χ` 的满足被换读为 `ext b` 属于恢复出的表，而层上的良序则被换成体的最小性子句所需的内部关系。
<!--ja-->
最小性は、`χ` を充足して `wS` より真に下にある段階の要素 `b` が存在しないことを述べる。`χ` の充足は `ext b` が復元された表に属することへ読み替えられ、段階の整列順序は本体の最小性の節が要求する内部関係へ変換される。
<!--/-->

```agda
            min : (b : SL) → ⟨ P b ⟩ → relOf-at b wS → ⊥₀
            min b pb lt = Rd.b-min g′ hE h bS (snd b) (ext b) (ext-graph b) hm
              (relL-fill lam λ-isL ordλ b wS lt)
              where
              bS : CS.S
```

<!--en-->
The smaller candidate is packaged as a constructible element `bS`, and its extended environment is shown to lie in the table, which is exactly the membership the minimality of the key refutes.
<!--zh-->
更小的候选被打包为可构造元素 `bS`，其延拓环境被证明落在表中，而这正是键的最小性所反驳的隶属。
<!--ja-->
より小さい候補は構成可能な要素 `bS` として包まれ、その延長された環境が表の中にあることが示される。これこそ、鍵の最小性が反証する所属である。
<!--/-->

```agda
              bS = fst b , Lset→isL lam ordλ (fst b) (snd b)
              hm : ⟨ fst (ext b) ∈ˢ fst T ⟩
              hm = subst (λ t → ⟨ fst (ext b) ∈ˢ t ⟩) (sym qT) (transport (sym (ext-sat b)) pb)
```

<!--en-->
The two facts combine into a satisfiability witness for `χ` at the recovered environment: the witness slot, together with its satisfaction, is truncated into `Sat`.
<!--zh-->
两条事实合成为「`χ` 在恢复环境处可满足」的见证：见证槽位连同其满足被截断为 `Sat`。
<!--ja-->
二つの事実は、復元された環境のもとでの `χ` の充足可能性の証人へと合成される。証人のスロットとその充足が、`Sat` へと切り詰められるのである。
<!--/-->

```agda
            w₀ : Sat n χ vs
            w₀ = ∣ wS , sat ∣₁
```

<!--en-->
The recovered arity `n`, formula `χ`, parameter vector `vs`, and witness `w₀` form a semantic search. Uniqueness of least elements identifies its result `search n χ vs w₀` with the original witnessed set `w`; separately, the table clause begins the proof that the recovered table is the satisfaction table of `χ`.
<!--zh-->
恢复出的元数 `n`、公式 `χ`、参数向量 `vs` 与见证 `w₀` 组成一次语义搜索。最小元的唯一性把搜索结果 `search n χ vs w₀` 与原被见证集合 `w` 同一视；另一方面，表子句开始证明恢复出的表正是 `χ` 的满足表。
<!--ja-->
復元されたアリティ `n`、論理式 `χ`、パラメータベクトル `vs`、証人 `w₀` が意味論的な探索をなす。最小要素の一意性により、その結果 `search n χ vs w₀` は元の証人集合 `w` と同定される。一方、表の節から、復元された表が `χ` の充足表であることの証明が始まる。
<!--/-->

```agda
            searched : Searched Z (fst w)
            searched = n , χ , vs , w₀ , (from , sym (cong (λ q → fst (fst q))
              (isPropLeastOf wL P (leastOfFormula wL (searchPredicate n χ vs) lem w₀)
                (wS , (sat , min)))))
          table : ∥ Searched Z (fst w) ∥₁
          table = ∣ AtTable.searched
```

<!--en-->
The table clause presents the underlying set of `T` as the value associated with the key `s`. Since `s` has already been identified with the canonical key of `χ` at arity `suc n`, uniqueness of the value at that key yields `fst T ≡ fst (Tof (suc n) χ)`.
<!--zh-->
表子句把 `T` 的底层集合表示为键 `s` 所对应的值。由于 `s` 已与 `χ` 在元数 `suc n` 处的典范键同一视，该键之值的唯一性给出 `fst T ≡ fst (Tof (suc n) χ)`。
<!--ja-->
表の節は `T` の基礎にある集合を、キー `s` に対応する値として表す。`s` はすでに、アリティ `suc n` における `χ` の正準なキーと同定されているので、そのキーにおける値の一意性から `fst T ≡ fst (Tof (suc n) χ)` が得られる。
<!--/-->

```agda
            (snd p ∙ cong fst (valOf-same s (fst p) (suc n) χ qs)) ∣₁
            where
            p : Σ[ m ∈ ⟨ s CS.∈ˢ AllCodes A ⟩ ] (fst T ≡ fst (SM.valOf s m))
            p = SM.pairs-out s T (Rd.b-tab h)
```

<!--en-->
To decode the code component `s`, `freeCode-out` supplies a formula `χ` whose free code is that component. The equation for the slot, the decoded code equation, and the computation of `keyOf` then identify `s` with the canonical key of `χ`.
<!--zh-->
为解码码分量 `s`，`freeCode-out` 给出一条公式 `χ`，其自由码正是该分量。随后依次复合槽位等式、解码所得的码等式与 `keyOf` 的计算等式，便把 `s` 与 `χ` 的典范键同一视。
<!--ja-->
コード成分 `s` を解読するため、`freeCode-out` は、その自由コードがこの成分である論理式 `χ` を与える。スロットの等式、解読されたコードの等式、`keyOf` の計算の等式を順に合成すると、`s` は `χ` の正準なキーと同定される。
<!--/-->

```agda
        code : ∥ Searched Z (fst w) ∥₁
        code = rec₁ squash₁
          (λ { (c , qc) → rec₁ squash₁
            (λ { (χ , ec) → AtCode.table χ
                   (qc ∙ cong (pr (# (suc n))) ec ∙ sym (keyOf-fst (suc n) χ)) })
```

<!--en-->
The key equation supplies the final link between the coded slot and the decoded formula. Consequently this numeral case yields a truncated `Searched Z (fst w)`: the witnessed set is exactly the least-witness search result for parameters recovered from `Z`.
<!--zh-->
键等式给出编码槽位与解码公式之间的最后联系。因此在这个数码情形中得到截断的 `Searched Z (fst w)`：被见证集合正是以从 `Z` 恢复的参数进行最小见证搜索所得的结果。
<!--ja-->
キーの等式が、符号化されたスロットと解読された論理式を結ぶ最後の関係を与える。したがってこの数項の場合には、切り詰められた `Searched Z (fst w)` が得られる。証人集合は、`Z` から復元したパラメータによる最小証人探索の結果にほかならない。
<!--/-->

```agda
            (freeCode-out (suc n) c (subst (λ u → ⟨ u ∈ˢ fst C₀ ⟩) qc s∈)) })
          (KeyIn.keyIn-out i3 i4 (Env T e' e s k w Z) n qk (Rd.b-key h) .snd)
```

<!--en-->
Since the arity recorded in every body witness belongs to the internal `ω`, numeral decoding turns the preceding analysis into a truncated semantic search for every such witness. For separation, choose the bound `Bnd Z = Z ∪ A`, where `A` is the internal presentation of `Lset lam`.
<!--zh-->
每份体见证所记录的元数都属于内部 `ω`，因此数码解码把前述分析推广为每份见证的一次截断语义搜索。作分离时取界 `Bnd Z = Z ∪ A`，其中 `A` 是 `Lset lam` 的内部表示。
<!--ja-->
各本体の証人に記録されたアリティは内部の `ω` に属するので、数項の解読により、先の分析から各証人について切り詰められた意味論的探索が得られる。分出の上界には `Bnd Z = Z ∪ A` を取り、`A` は `Lset lam` の内部表示である。
<!--/-->

```agda
      searched : ∥ Searched Z (fst w) ∥₁
      searched = rec₁ squash₁ (λ { (n , qk) → AtNum.code n qk }) (ω-num k (Rd.b-num h))
    Bnd : CS.S → CS.S
    Bnd Z = cupʟ Z A
```

<!--en-->
Members of `Z` lie in the bound by the left inclusion of the union.
<!--zh-->
`Z` 的成员由并的左包含落入界内。
<!--ja-->
`Z` の要素は、和の左の包含によって上界の中に入る。
<!--/-->

```agda
    bnd-Z : (Z z : CS.S) → ⟨ fst z ∈ˢ fst Z ⟩ → ⟨ z CS.∈ˢ Bnd Z ⟩
    bnd-Z Z z = cupʟ-inl Z A (fst z)
```

<!--en-->
Every member of `Lset lam` lies in `Bnd Z` through the right inclusion. The one-step closure condition then has three cases: an old member of `Z`, the empty set used when no witness exists, or a set `w` satisfying `witFo` with base `Z`.
<!--zh-->
`Lset lam` 的每个成员都由右包含进入 `Bnd Z`。一步闭包条件于是有三种情形：`Z` 的旧成员、无见证时使用的空集，或与基 `Z` 一起满足 `witFo` 的集合 `w`。
<!--ja-->
`Lset lam` の各要素は右側の包含によって `Bnd Z` に入る。一段階の閉包条件には三つの場合がある。`Z` の既存の要素、証人がないときに使う空集合、または基礎 `Z` とともに `witFo` を充足する集合 `w` である。
<!--/-->

```agda
    bnd-L : (Z z : CS.S) → ⟨ fst z ∈ˢ Lset lam ⟩ → ⟨ z CS.∈ˢ Bnd Z ⟩
    bnd-L Z z = cupʟ-inr Z A (fst z)
    Body : CS.S → CS.S → Type (ℓ-suc ℓ)
    Body Z w = ⟨ fst w ∈ˢ fst Z ⟩ ⊎ ((fst w ≡ ∅) ⊎ ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩)
```

<!--en-->
In the third case, the stage clause encoded by `witFo` proves directly that `w ∈ Lset lam`. Thus every newly adjoined least witness lies inside the fixed stage.
<!--zh-->
在第三种情形中，`witFo` 所编码的层子句直接证明 `w ∈ Lset lam`。因此每个新加入的最小见证都留在固定层内。
<!--ja-->
第三の場合、`witFo` に符号化された段階の節が `w ∈ Lset lam` を直接示す。したがって新たに加えられる最小証人はすべて固定した段階の内部にとどまる。
<!--/-->

```agda
    wit-L : (Z w : CS.S) → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩ → ⟨ fst w ∈ˢ Lset lam ⟩
    wit-L Z w hw = rec₁ (snd (fst w ∈ˢ Lset lam))
      (λ { (T , e' , e , s , k , h) → BodyRd.b-stage T e' e s k w Z h })
      (witFo-out w Z hw)
    opaque
```

<!--en-->
The separation formula expresses these three cases inside the constructible structure: membership in `Z`, equality with the empty set, or the renamed formula `witFo`. The renaming places its two free variables in the slots created by the existential wrapper.
<!--zh-->
分离公式在可构造结构内部表达这三种情形：属于 `Z`、等于空集，或满足改名后的 `witFo`。改名把它的两个自由变量放入存在包所形成的槽位。
<!--ja-->
分出の論理式は、構成可能な構造の内部で三つの場合を表す。`Z` への所属、空集合との等しさ、または改名された `witFo` の充足である。改名は、その二つの自由変数を存在量化で作られた位置に配置する。
<!--/-->

```agda
      sepFo : CS.S → Formula CS.S 1
      sepFo Z = (var i0 ∈̇ con Z)
              ∨̇ ( (var i0 ≐ con ∅ʟ)
                ∨̇ ∃̇ ( (var i0 ≐ con Z) ∧̇ renameFo ρs witFo ) )
```

<!--en-->
The renaming merely exchanges the two environment entries. Hence evaluating the renamed `witFo` at `(Z'', w)` has the same truth value as evaluating the original `witFo` at `(w, Z'')`.
<!--zh-->
这次改名只交换环境中的两个条目。因此，改名后的 `witFo` 在 `(Z'', w)` 处的真值，等于原 `witFo` 在 `(w, Z'')` 处的真值。
<!--ja-->
この改名は環境の二つの成分を交換するだけである。したがって、改名された `witFo` を `(Z'', w)` で評価した真理値は、元の `witFo` を `(w, Z'')` で評価した真理値に等しい。
<!--/-->

```agda
      private
        rs : (Z'' w : CS.S)
           → ⟨ (Z'' ∷ w ∷ []) ⊨ renameFo ρs witFo ⟩ ≡ ⟨ (w ∷ Z'' ∷ []) ⊨ witFo ⟩
        rs Z'' w = cong ⟨_⟩ (Ren.⊨-rename ρs witFo (Z'' ∷ w ∷ []) (w ∷ Z'' ∷ []) (ags Z'' w))
```

<!--en-->
Satisfaction of the separation formula decomposes into the three truncated cases of the body: membership in `Z`, equality with the empty set, or an existential whose witness identifies the domain.
<!--zh-->
分离公式的满足分解为体的三个截断情形：属于 `Z`、与空集相等，或一个其见证指认定义域的存在情形。
<!--ja-->
分出の論理式の充足は、本体の三つの切り詰められた場合に分解される。`Z` への所属、空集合との等号、あるいは、その証人が定義域を指認する存在の場合である。
<!--/-->

```agda
      sep-out : (Z w : CS.S) → ⟨ (w ∷ []) ⊨ sepFo Z ⟩ → ∥ Body Z w ∥₁
      sep-out Z w = rec₁ squash₁ (λ
        { (inl hz) → ∣ inl hz ∣₁
        ; (inr h') → rec₁ squash₁ (λ
          { (inl e) → ∣ inr (inl e) ∣₁
```

<!--en-->
In the existential case, its witness `Z''` is equal to the fixed parameter `Z`. Transporting along this equality and then along the renaming path yields `witFo` at `(w, Z)`.
<!--zh-->
在存在情形中，其见证 `Z''` 等于固定参数 `Z`。先沿这条等式、再沿改名路径搬运，便得到 `witFo` 在 `(w, Z)` 处成立。
<!--ja-->
存在の場合、その証人 `Z''` は固定したパラメータ `Z` に等しい。この等しさに沿って移送し、さらに改名のパスに沿って移送すると、`witFo` が `(w, Z)` で成り立つことが得られる。
<!--/-->

```agda
          ; (inr hw) → map₁ (λ { (Z'' , (eZ , hr)) → inr (inr
              (subst (λ u → ⟨ (w ∷ u ∷ []) ⊨ witFo ⟩) (S≡ {x = Z''} {y = Z} eZ)
                (transport (rs Z'' w) hr))) }) hw }) h' })
```

<!--en-->
Conversely, each of the three cases of the body produces the corresponding satisfaction of the separation formula, re-wrapping the renaming where needed.
<!--zh-->
反过来，体的三种情形各自产生分离公式相应的满足，并在需要处重新包上改名。
<!--ja-->
逆に、本体の三つの場合はそれぞれ、分出の論理式の対応する充足を産み、必要なところで名前の付け替えを包み直す。
<!--/-->

```agda
      sep-in : (Z w : CS.S) → Body Z w → ⟨ (w ∷ []) ⊨ sepFo Z ⟩
      sep-in Z w (inl hz) = ∣ inl hz ∣₁
      sep-in Z w (inr (inl e)) = ∣ inr ∣ inl e ∣₁ ∣₁
      sep-in Z w (inr (inr hw)) = ∣ inr ∣ inr ∣ Z , (refl , transport (sym (rs Z w)) hw) ∣₁ ∣₁ ∣₁
```

<!--en-->
Separation inside `L` selects from `Bnd Z` exactly the sets satisfying `sepFo Z`; call the resulting constructible set `Φ Z`. Its membership path identifies membership in `Φ Z` with membership in the bound together with satisfaction of the formula.
<!--zh-->
在 `L` 内作分离，从 `Bnd Z` 中恰好选出满足 `sepFo Z` 的集合；所得可构造集记为 `Φ Z`。其隶属路径把「属于 `Φ Z`」同一视为「属于该界并满足公式」。
<!--ja-->
`L` の内部で分出を行い、`Bnd Z` から `sepFo Z` を充足する集合だけを選ぶ。その構成可能集合を `Φ Z` とする。その所属のパスは、`Φ Z` への所属を、上界への所属と論理式の充足との組に同定する。
<!--/-->

```agda
    opaque
      Φ : CS.S → CS.S
      Φ Z = hasSeparationL (Bnd Z) (sepFo Z) .fst .fst
```

<!--en-->
The membership specification reads: `w` belongs to `Φ Z` exactly when `w` belongs to the bound and satisfies the separation formula.
<!--zh-->
隶属规格读作：`w` 属于 `Φ Z`，当且仅当 `w` 属于界 `Bnd Z` 且满足分离公式。
<!--ja-->
所属の仕様は次のように読める。`w` が `Φ Z` に属するのは、`w` が上界 `Bnd Z` に属し、分出の論理式を満たすとき、そのときに限る。
<!--/-->

```agda
      Φ-mem : (Z w : CS.S) → (w CS.∈ˢ Φ Z) ≡ ((w CS.∈ˢ Bnd Z) ⊓ ((w ∷ []) ⊨ sepFo Z))
      Φ-mem Z = hasSeparationL (Bnd Z) (sepFo Z) .fst .snd
```

<!--en-->
Every body case lands in `Φ Z`. The membership case enters through the bound; the proof packages the bound membership produced from each disjunct together with its separation satisfaction.
<!--zh-->
体的每种情形都落入 `Φ Z`。隶属情形经界进入；证明把每个析取支产生的界隶属与其分离满足打包。
<!--ja-->
本体のどの場合も `Φ Z` に着地する。所属の場合は上界を通って入り、証明は、各選言支から産み出される上界への所属を、分出の充足とともに包む。
<!--/-->

```agda
    Φ-in : (Z w : CS.S) → Body Z w → ⟨ fst w ∈ˢ fst (Φ Z) ⟩
    Φ-in Z w b = subst ⟨_⟩ (sym (Φ-mem Z w)) (bnd b , sep-in Z w b)
      where
      bnd : Body Z w → ⟨ w CS.∈ˢ Bnd Z ⟩
      bnd (inl hz) = bnd-Z Z w hz
```

<!--en-->
The empty-set case lies in the bound because `∅ ∈ Lset lam`. The witness case lies there because the stage clause of `witFo` proves its value belongs to `Lset lam`.
<!--zh-->
空集情形属于该界，因为 `∅ ∈ Lset lam`。见证情形也属于该界，因为 `witFo` 的层子句证明其取值属于 `Lset lam`。
<!--ja-->
空集合の場合は `∅ ∈ Lset lam` によって上界に属する。証人の場合も、`witFo` の段階の節がその値の `Lset lam` への所属を示すので、上界に属する。
<!--/-->

```agda
      bnd (inr (inl e)) = bnd-L Z w (subst (λ u → ⟨ u ∈ˢ Lset lam ⟩) (sym e) HSH.∅∈Lsetα)
      bnd (inr (inr hw)) = bnd-L Z w (wit-L Z w hw)
```

<!--en-->
Conversely, membership in `Φ Z` yields a truncated body case, by the membership specification and the separation reading. For the biconditional formula, the body is then rewritten in a three-slot arrangement.
<!--zh-->
反过来，`Φ Z` 中的隶属由隶属规格与分离读法给出截断的体情形。为写双条件公式，体随后改写为三空位排列。
<!--ja-->
逆に、`Φ Z` への所属からは、所属の仕様と分出の読みを通して、切り詰められた本体の場合が得られる。同値の論理式のために、本体は三つの枠の並びへ書き直される。
<!--/-->

```agda
    Φ-out : (Z w : CS.S) → ⟨ fst w ∈ˢ fst (Φ Z) ⟩ → ∥ Body Z w ∥₁
    Φ-out Z w h = sep-out Z w (subst ⟨_⟩ (Φ-mem Z w) h .snd)
    opaque
      bodyF : Formula CS.S 3
      bodyF = (var i0 ∈̇ var i2) ∨̇ ((var i0 ≐ con ∅ʟ) ∨̇ renameFo ρf witFo)
```

<!--en-->
The graph formula `ΦFo` quantifies over a fresh set `w` and states both implications between `w ∈ Z'` and the three-case condition `Body Z w`. Thus `(Z', Z)` satisfies `ΦFo` exactly when `Z'` has the same members as `Φ Z`.
<!--zh-->
图公式 `ΦFo` 对新集合 `w` 作全称量化，并陈述 `w ∈ Z'` 与三种情形组成的条件 `Body Z w` 之间的两个蕴涵。因此 `(Z', Z)` 满足 `ΦFo`，恰当 `Z'` 与 `Φ Z` 具有相同成员。
<!--ja-->
グラフの論理式 `ΦFo` は新しい集合 `w` を全称量化し、`w ∈ Z'` と三つの場合からなる条件 `Body Z w` の間の二つの含意を述べる。したがって `(Z', Z)` が `ΦFo` を充足するのは、`Z'` と `Φ Z` が同じ要素をもつとき、かつそのときに限る。
<!--/-->

```agda
      ΦFo : Formula CS.S 2
      ΦFo = ∀̇ ( ((var i0 ∈̇ var i1) ⇒̇ bodyF) ∧̇ (bodyF ⇒̇ (var i0 ∈̇ var i1)) )
```

<!--en-->
The renaming equivalence for the graph is proved like the earlier one: the renaming permutes the environment, and satisfaction transfers along the permutation.
<!--zh-->
图的改名等式与之前的同名引理一样证明：改名置换环境，满足沿置换搬运。
<!--ja-->
グラフのための改名の同値は、前のものと同じように証明される。改名は環境を入れ替え、充足はその入れ替えに沿って運ばれる。
<!--/-->

```agda
      private
        rf : (w Z' Z : CS.S)
           → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ renameFo ρf witFo ⟩ ≡ ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
        rf w Z' Z = cong ⟨_⟩ (Ren.⊨-rename ρf witFo (w ∷ Z' ∷ Z ∷ []) (w ∷ Z ∷ []) (agf w Z' Z))
```

<!--en-->
The body transfers across the three-slot arrangement in both directions: membership in `Z` is direct, and the remaining disjuncts are mapped through the truncation.
<!--zh-->
体在三空位排列下双向转移：属于 `Z` 是直接的，其余析取支经截断映射。
<!--ja-->
本体は、三つの枠の並びの下で双方向に移る。`Z` への所属は直接であり、残りの選言支は切り詰めの上で写される。
<!--/-->

```agda
        bodyF-out : (w Z' Z : CS.S) → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ bodyF ⟩ → ∥ Body Z w ∥₁
        bodyF-out w Z' Z = rec₁ squash₁ (λ
          { (inl hz) → ∣ inl hz ∣₁
          ; (inr h') → map₁ (λ
            { (inl e) → inr (inl e)
```

<!--en-->
In the witness case, the renaming path converts satisfaction of the three-slot formula back to `witFo` at `(w, Z)`, completing the forward implication from the graph body to `Body Z w`.
<!--zh-->
在见证情形中，改名路径把三槽公式的满足换回 `witFo` 在 `(w, Z)` 处的满足，从而完成由图公式体到 `Body Z w` 的正向蕴涵。
<!--ja-->
証人の場合、改名のパスは三変数の論理式の充足を `(w, Z)` における `witFo` の充足へ戻し、グラフの本体から `Body Z w` への順方向の含意を完成させる。
<!--/-->

```agda
            ; (inr hw) → inr (inr (transport (rf w Z' Z) hw)) }) h' })
```

<!--en-->
The converse assembles the three cases into the three-slot reading, transporting the witness disjunct against the renaming.
<!--zh-->
逆向把三种情形组装成三空位读法，并逆着改名搬运见证析取支。
<!--ja-->
逆方向は、三つの場合を三つの枠の読みに組み立て、Witnessの選言支を改名に対して運ぶ。
<!--/-->

```agda
        bodyF-in : (w Z' Z : CS.S) → Body Z w → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ bodyF ⟩
        bodyF-in w Z' Z (inl hz) = ∣ inl hz ∣₁
        bodyF-in w Z' Z (inr (inl e)) = ∣ inr ∣ inl e ∣₁ ∣₁
        bodyF-in w Z' Z (inr (inr hw)) = ∣ inr ∣ inr (transport (sym (rf w Z' Z)) hw) ∣₁ ∣₁
```

<!--en-->
The definability clause is then proved: the pair `(Φ Z, Z)` satisfies the graph formula. Each direction of the biconditional is the corresponding membership direction composed with the body transfer.
<!--zh-->
随后证明可定义性条款：对 `(Φ Z, Z)` 满足图公式。双条件的每个方向都是相应隶属方向与体转移的复合。
<!--ja-->
続いて、定義可能性の条項が証明される。対 `(Φ Z, Z)` はグラフの論理式を充足する。同値のそれぞれの向きは、対応する所属の向きと本体の転送の合成である。
<!--/-->

```agda
      Φ-defines : (Z : CS.S) → ⟨ (Φ Z ∷ Z ∷ []) ⊨ ΦFo ⟩
      Φ-defines Z w =
          (λ h → rec₁ (snd ((w ∷ Φ Z ∷ Z ∷ []) ⊨ bodyF)) (bodyF-in w (Φ Z) Z) (Φ-out Z w h))
        , (λ h → rec₁ (snd (fst w ∈ˢ fst (Φ Z))) (Φ-in Z w) (bodyF-out w (Φ Z) Z h))
```

<!--en-->
Uniqueness of the graph is proved by extensionality of the constructible structure: for any `Z'` whose pair with `Z` satisfies the graph formula, every member of `Z'` satisfies the body, and `Φ-in` places it in `Φ Z`.
<!--zh-->
图的唯一性由可构造结构的外延性证明：对任何「其与 `Z` 的对满足图公式」的 `Z'`，`Z'` 的每个成员都满足体，而 `Φ-in` 把它放入 `Φ Z`。
<!--ja-->
グラフの一意性は、構成可能な構造の外延性によって証明される。`Z` との対がグラフの論理式を充足する任意の `Z'` のすべての要素は本体を満たし、`Φ-in` がそれを `Φ Z` の中に置く。
<!--/-->

```agda
      Φ-only : (Z Z' : CS.S) → ⟨ (Z' ∷ Z ∷ []) ⊨ ΦFo ⟩ → Z' ≡ Φ Z
      Φ-only Z Z' h = extensionalL (λ v → ⇔toPath (fwd v) (bwd v))
        where
        fwd : (v : CS.S) → ⟨ fst v ∈ˢ fst Z' ⟩ → ⟨ fst v ∈ˢ fst (Φ Z) ⟩
        fwd v hv = rec₁ (snd (fst v ∈ˢ fst (Φ Z))) (Φ-in Z v) (bodyF-out v Z' Z (h v .fst hv))
```

<!--en-->
The backward direction of the extensionality argument reads each member of `Φ Z` as a truncated body case and applies the graph formula at that member.
<!--zh-->
外延性论证的反向把 `Φ Z` 的每个成员读作截断的体情形，并在该成员处应用图公式。
<!--ja-->
外延性の議論の逆方向は、`Φ Z` の各要素を切り詰められた本体の場合として読み、その要素のもとでグラフの論理式を適用する。
<!--/-->

```agda
        bwd : (v : CS.S) → ⟨ fst v ∈ˢ fst (Φ Z) ⟩ → ⟨ fst v ∈ˢ fst Z' ⟩
        bwd v hv = h v .snd
          (rec₁ (snd ((v ∷ Z' ∷ Z ∷ []) ⊨ bodyF)) (bodyF-in v Z' Z) (Φ-out Z v hv))
```

<!--en-->
We have therefore obtained a definable one-step operation `Φ`: the formula `ΦFo` characterizes its graph, and extensionality proves that any set satisfying that graph condition is equal to `Φ Z`.
<!--zh-->
由此得到可定义的一步运算 `Φ`：公式 `ΦFo` 刻画其图，而外延性证明任何满足该图条件的集合都等于 `Φ Z`。
<!--ja-->
これで定義可能な一段階の演算 `Φ` が得られた。論理式 `ΦFo` がそのグラフを特徴づけ、外延性により、そのグラフ条件を満たす任意の集合は `Φ Z` に等しい。
<!--/-->

```agda
    pack : StepPack
    pack = record
      { Φ       = Φ
      ; ΦFo     = ΦFo
      ; defines = Φ-defines
```

<!--en-->
This step contains every old member of `Z`, always contains the empty set, and contains the least witness for every satisfiable formula with parameters from `Z`. Conversely, its members arise only from these three cases, so `Φ` is exactly the desired one-step closure.
<!--zh-->
这一步包含 `Z` 的每个旧成员，始终包含空集，并对每条以 `Z` 中元素为参数且可满足的公式包含其最小见证。反过来，它的成员只来自这三种情形，因此 `Φ` 恰是所需的一步闭包。
<!--ja-->
この一段階は `Z` の既存の各要素を含み、常に空集合を含み、さらに `Z` の要素をパラメータとする充足可能な各論理式の最小証人を含む。逆に、その要素はこの三つの場合からしか生じないので、`Φ` は求める一段階の閉包にほかならない。
<!--/-->

```agda
      ; only    = Φ-only
      ; grows   = λ Z z hz → Φ-in Z (z , isL-trans {x = fst Z} {y = z} hz (snd Z)) (inl hz)
      ; junk    = λ Z → Φ-in Z ∅ʟ (inr (inl refl))
      ; least   = λ Z k χ vs from w₀ →
                    Φ-in Z (Least.aS Z k χ vs from w₀) (inr (inr (Least.least Z k χ vs from w₀)))
```

<!--en-->
Assume every member of `Z` lies in `Lset lam`. If `z ∈ Φ Z`, the membership characterization gives three possibilities: `z` was already in `Z`, `z = ∅`, or `witFo` holds at `(z, Z)`. In the third case, decoding the body reconstructs a semantic search from parameters in `Z` whose result is `z`.
<!--zh-->
假设 `Z` 的每个成员都属于 `Lset lam`。若 `z ∈ Φ Z`，隶属刻画给出三种可能：`z` 原已属于 `Z`，`z = ∅`，或 `witFo` 在 `(z, Z)` 处成立。在第三种情形中，解码公式体会重建一次以 `Z` 中元素为参数、结果为 `z` 的语义搜索。
<!--ja-->
`Z` の各要素が `Lset lam` に属すると仮定する。`z ∈ Φ Z` なら、所属の特徴づけから三つの可能性が得られる。`z` がすでに `Z` に属する場合、`z = ∅` の場合、または `witFo` が `(z, Z)` で成り立つ場合である。第三の場合、本体を解読すると、`Z` の要素をパラメータとし、結果が `z` である意味論的探索が復元される。
<!--/-->

```agda
      ; out     = λ Z Z⊆ z hz → rec₁ squash₁ (λ
          { (inl h') → ∣ inl h' ∣₁
          ; (inr (inl e)) → ∣ inr (inl e) ∣₁
          ; (inr (inr hw)) → rec₁ squash₁
              (λ { (T , e' , e , s , k , hb) →
```

<!--en-->
In the witness case, `z ∈ Φ Z` first makes `z` constructible, so it can be read as an element of the constructible carrier. The decoded body then proves `Searched Z z`, identifying `z` with the least-witness search determined by the recovered formula and parameters.
<!--zh-->
在见证情形中，`z ∈ Φ Z` 先给出 `z` 的可构造性，使它可被读作可构造载体的元素。解码后的公式体再证明 `Searched Z z`，把 `z` 与恢复出的公式和参数所决定的最小见证搜索同一视。
<!--ja-->
証人の場合、`z ∈ Φ Z` からまず `z` の構成可能性が得られ、`z` を構成可能な台の要素として読める。解読された本体はさらに `Searched Z z` を示し、`z` を復元された論理式とパラメータが定める最小証人探索と同定する。
<!--/-->

```agda
                 map₁ (λ sr → inr (inr sr)) (Out.searched Z Z⊆ (zS Z z hz) T e' e s k hb) })
              (witFo-out (zS Z z hz) Z hw) })
          (Φ-out Z (zS Z z hz) hz) }
      where
      zS : (Z : CS.S) (z : S) → ⟨ z ∈ˢ fst (Φ Z) ⟩ → CS.S
```

<!--en-->
Since `Φ Z` is constructible and constructibility is transitive, every member `z` of `Φ Z` is constructible.
<!--zh-->
由于 `Φ Z` 可构造且可构造性具有传递性，`Φ Z` 的每个成员 `z` 都可构造。
<!--ja-->
`Φ Z` は構成可能であり、構成可能性は推移的なので、`Φ Z` の各要素 `z` も構成可能である。
<!--/-->

```agda
      zS Z z hz = z , isL-trans {x = fst (Φ Z)} {y = z} hz (snd (Φ Z))
```
</div>
</details>

</div>
</details>

<!--en-->
## Supplying the constructibility premise for condensation
<!--zh-->
## 为凝聚提供可构造性前提
<!--ja-->
## 凝縮に必要な構成可能性の前提を与える
<!--/-->

<!--en-->
This supplies the carrier element needed in the preceding decoding and completes the construction of the definable one-step closure.
<!--zh-->
这给出前述解码所需的载体元素，并完成可定义一步闭包的构造。
<!--ja-->
これにより先の解読に必要な台の要素が得られ、定義可能な一段階の閉包の構成が完成する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Discharge (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (M-isL : ⟨ isL (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Assume that the hull `M` is itself constructible. This turns `M` into a constructible carrier, so the preceding collapse argument applies without requiring the hull to be transitive.
<!--zh-->
假设壳 `M` 本身可构造。这样便可把 `M` 视为可构造载体，从而应用前面的塌缩论证，而无须假设该壳是传递的。
<!--ja-->
包 `M` 自身が構成可能であると仮定する。これにより `M` を構成可能な台として扱えるので、包が推移的であると仮定せずに、先の崩壊の議論を適用できる。
<!--/-->

<!--en-->
Regarded as a constructible carrier, `M` has a collapse image `πX`. Every member of this image is the collapse value of some member of `M`, and the constructible-carrier theorem proves that such values belong to `L`.
<!--zh-->
把 `M` 视为可构造载体后，可得到其塌缩像 `πX`。该像的每个成员都是 `M` 某个成员的塌缩值，而可构造载体定理证明这些值都属于 `L`。
<!--ja-->
`M` を構成可能な台とみなすと、その崩壊像 `πX` が得られる。この像の各要素は `M` のある要素の崩壊値であり、構成可能な台についての定理から、そのような値は `L` に属する。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
  module HSC = HullStage.C lam ordλ succλ X X⊆L ∅∈λ using ( πX )
  module P = PiIn (HS.M , M-isL) using ( πX-isL )
```

<!--en-->
Consequently, every `x ∈ πX` is constructible. We now return to the hull generated from `X` inside `Lset λ`, assuming that `λ` is an ordinal closed under successors and that every member of `X` lies in this stage.
<!--zh-->
因此，每个 `x ∈ πX` 都可构造。现在回到由 `X` 在 `Lset λ` 内生成的壳，并假设 `λ` 是对后继封闭的序数，且 `X` 的每个成员都属于这一层。
<!--ja-->
したがって、すべての `x ∈ πX` は構成可能である。ここで、`X` から `Lset λ` の内部で生成される包に戻る。`λ` は後続について閉じた順序数であり、`X` の各要素はこの段階に属すると仮定する。
<!--/-->

```agda
  pixL : (x : S) → ⟨ x ∈ˢ HSC.πX ⟩ → ⟨ isL x ⟩
  pixL = P.πX-isL
```
</div>
</details>

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Condense′ (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩)
  where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
We also assume that `∅ ∈ λ`, that the hull frame generated by `X` is elementary, that `λ` is superadequate, and that `X` itself is constructible. The last assumption supplies the base of the internal finite iteration; elementarity and superadequacy supply the hypotheses needed for condensation.
<!--zh-->
还假设 `∅ ∈ λ`，由 `X` 生成的壳框架是初等的，`λ` 是超充分的，并且 `X` 本身可构造。最后一条假设为内部有限迭代提供起点；初等性与超充分性则提供凝聚论证所需的假设。
<!--ja-->
さらに、`∅ ∈ λ`、`X` から生成される包の枠組みの初等性、`λ` が強化された十分な段階であること、および `X` 自身の構成可能性を仮定する。最後の仮定は内部の有限反復の始点を与え、初等性と強化された十分性は凝縮の議論に必要な仮定を与える。
<!--/-->

<!--en-->
The construction has three connected parts. Codes name the initial elements and the values selected by later searches, using the empty set when a search has no witness; one definable operation `Φ` performs a closure step; and finite iteration of `Φ`, followed by union, builds a constructible set that will be identified with the Skolem hull.
<!--zh-->
这一构造由三个相连的部分组成。码指称初始元素和后续搜索所选取的值；搜索没有见证时则以空集为值。一个可定义运算 `Φ` 完成一步闭包；对 `Φ` 作有限迭代再取并，便构造出一个随后将与 Skolem 壳认同的可构造集合。
<!--ja-->
この構成は三つの部分からなる。コードが初期要素と後の探索で選ばれる値を指し、探索に証人がない場合は空集合を値とする。一つの定義可能な演算 `Φ` が一段の閉包を行い、`Φ` を有限回反復して合併を取ることで、後に Skolem 包と同一視される構成可能集合を作る。
<!--/-->

```agda
  module T = Telescope lam ordλ succλ X X⊆L ∅∈λ using ( Code; val; Reads; module StepPack )
  module TB = Telescope.Build lam ordλ succλ X X⊆L ∅∈λ using ( pack; Φ )
  module HI = Telescope.HullIter lam ordλ succλ X X⊆L ∅∈λ X-isL TB.pack
    using ( hullL; hullL-spec; hullStep; hullStep-suc; hullStep-in; hullStep⊆Hull; depth; M-isL )
  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
```

<!--en-->
The union of the finite closure stages is already an element `hullL` of the constructible universe. The next equality shows that its underlying set is precisely the externally defined hull `M`; this will supply the constructibility premise used above for the collapse image.
<!--zh-->
有限闭包层之并已经构成可构造宇宙中的元素 `hullL`。接下来的等式将证明其底层集合恰是外围定义的壳 `M`；这便会给出上文处理塌缩像时所用的整体可构造性前提。
<!--ja-->
有限な閉包段階の合併は、すでに構成可能宇宙の要素 `hullL` になっている。次の等式により、その台集合が周囲で定義された包 `M` にほかならないことを示す。これが、先に崩壊像を扱う際に仮定した包全体の構成可能性を与える。
<!--/-->

```agda
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ using ( Hull⊆L )
  module HSC = HullStage.C lam ordλ succλ X X⊆L ∅∈λ using ( πX )
  module D = Discharge lam ordλ succλ X X⊆L ∅∈λ HI.M-isL using ( pixL )
  hullL : CS.S
  hullL = HI.hullL
```

<!--en-->
The underlying set of `hullL` is exactly `M`. Hence the external characterization of the Skolem hull and the constructible set obtained by iteration describe the same members, while `hullL` additionally carries a proof of constructibility.
<!--zh-->
`hullL` 的底层集合恰是 `M`。因此，Skolem 壳的外围刻画与迭代所得的可构造集合描述了同样的成员，而 `hullL` 还携带其可构造性的证明。
<!--ja-->
`hullL` の台集合はちょうど `M` である。したがって、Skolem 包の周囲での特徴づけと、反復から得た構成可能集合は同じ要素を記述し、`hullL` はさらに構成可能性の証明も備えている。
<!--/-->

```agda
  hullL-spec : fst hullL ≡ HS.M
  hullL-spec = HI.hullL-spec
```

<!--en-->
The closure stages of the hull are indexed by natural numbers: `hullStep n` is the stage reached after `n` applications of the closure step.
<!--zh-->
壳的闭包层以自然数为索引：`hullStep n` 是闭包步骤施用 `n` 次后到达的层。
<!--ja-->
殻の閉包の段階は自然数で添字づけられる。`hullStep n` は閉包の段階を `n` 回適用して到達する層である。
<!--/-->

```agda
  hullStep : ℕ → CS.S
  hullStep = HI.hullStep
```

<!--en-->
At a successor index, the next stage is `Φ` applied to the current one. This operation retains the current members, includes the empty set, and adjoins the least witness for each coded search whose parameters are already present.
<!--zh-->
在后继索引处，下一层就是把 `Φ` 作用于当前层所得的结果。该运算保留当前成员，加入空集，并为每个参数已经出现的编码搜索加入其最小见证。
<!--ja-->
後続の添字では、次の段階は現在の段階に `Φ` を作用させたものである。この演算は現在の要素を保ち、空集合を加え、さらにパラメータがすでに現れている各符号化された探索について最小証人を加える。
<!--/-->

```agda
  hullStep-suc : (n : ℕ) → hullStep (suc n) ≡ TB.Φ (hullStep n)
  hullStep-suc = HI.hullStep-suc
```

<!--en-->
Each code has a finite depth, and the value it denotes belongs to the closure stage at that depth. Since every hull member is represented by a code, this gives a finite stage containing it, without choosing a canonical code for the member.
<!--zh-->
每个码都有一个有限深度，而它所指称的值属于以该深度为索引的闭包层。由于每个壳成员都由某个码表示，这便为它给出一个包含它的有限层，但并不为该成员选定典范码。
<!--ja-->
各コードには有限の深さがあり、それが指す値はその深さの閉包段階に属する。包の各要素は何らかのコードで表されるので、その要素を含む有限段階が得られるが、要素ごとに正準的なコードを選ぶわけではない。
<!--/-->

```agda
  hullStep-in : (c : T.Code) → ⟨ fst (T.val c) ∈ˢ fst (hullStep (HI.depth c)) ⟩
  hullStep-in = HI.hullStep-in
```

<!--en-->
Conversely, every member of every finite closure stage belongs to `M`. Together with the coded description of hull members, this proves that the union of the stages and the Skolem hull have exactly the same elements.
<!--zh-->
反过来，每个有限闭包层的每个成员都属于 `M`。结合壳成员的编码刻画，这便证明诸层之并与 Skolem 壳恰有相同的元素。
<!--ja-->
逆に、各有限閉包段階のすべての要素は `M` に属する。包の要素の符号による特徴づけと合わせると、これにより段階の合併と Skolem 包がまったく同じ要素をもつことが分かる。
<!--/-->

```agda
  hullStep⊆Hull : (n : ℕ) (z : S) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ HS.M ⟩
  hullStep⊆Hull = HI.hullStep⊆Hull
```

<!--en-->
The union of the stages is constructible: the hull stage `M` is an element of `L`. This is the first of the two membership facts the chapter set out to prove.
<!--zh-->
诸层之并可构造：壳层 `M` 是 `L` 的元素。这是本章要证明的两条隶属事实中的第一条。
<!--ja-->
段階の合併は構成可能である。殻の段階 `M` は `L` の要素である。これが本章が証明を目指した二つの所属の事実のうちの一つである。
<!--/-->

```agda
  M-isL : ⟨ isL HS.M ⟩
  M-isL = HI.M-isL
```

<!--en-->
The second follows through the discharge: every value of the collapse `πX` of the hull stage is constructible, because the carrier `M` is.
<!--zh-->
第二条经兑现而来：壳层 `M` 的塌缩 `πX` 的每个值都可构造，因为载体 `M` 可构造。
<!--ja-->
第二の事実は処理を通して従う。殻の段階 `M` の崩壊 `πX` のすべての値が構成可能なのは、台 `M` が構成可能だからである。
<!--/-->

```agda
  pixL : (x : S) → ⟨ x ∈ˢ HSC.πX ⟩ → ⟨ isL x ⟩
  pixL = D.pixL
```

<!--en-->
Condensation now yields an ordinal `β` for which the collapse image is exactly `Lset β`. The earlier memberwise constructibility statement is thereby strengthened to an identification of the whole image with one stage of the constructible hierarchy. The conclusion asserts this equality and the ordinality of `β`; it makes no further comparison between `β` and `λ`.
<!--zh-->
凝聚现在给出一个序数 `β`，使塌缩像恰等于 `Lset β`。由此，先前逐个成员的可构造性陈述加强为把整个像认同为可构造层级中的一个层。结论只断言这一等式与 `β` 的序数性，并未进一步比较 `β` 与 `λ`。
<!--ja-->
凝縮により、崩壊像がちょうど `Lset β` となる順序数 `β` が得られる。これにより、先の要素ごとの構成可能性は、像全体を構成可能階層の一つの段階と同一視する主張へ強められる。結論が主張するのはこの等式と `β` の順序数性であり、`β` と `λ` の間の比較までは含まない。
<!--/-->

```agda
  condenses′ : Σ[ β ∈ S ] (IsOrd β × (HSC.πX ≡ Lset β))
  condenses′ = Condense.condenses lam ordλ succλ X X⊆L ∅∈λ elem sup D.pixL
```
</div>
</details>
