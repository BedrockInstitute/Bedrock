<!--en-->
# Formulas for name comparison
<!--zh-->
# 名字比较的公式
<!--ja-->
# 名前の比較を表す論理式
<!--/-->

<!--en-->
A definable subset can have many names. At the meta-level, a name consists of an arity `k`, a parameter-free formula with `suc k` variable slots, and a vector of `k` parameters from the carrier. Its denotation is then derived from these three pieces: the extra variable ranges over the candidate member, and the remaining variables receive the parameter vector. The denotation is therefore not a fourth component of the name.

To express this data inside `L`, the chapter represents the parameter vector by a finite environment graph and represents evaluation by the satisfaction graph. At a genuine formula key, `satGraphAt` relates that key to the set of environments satisfying the formula. Its output is exactly this satisfaction-environment set. `NameAt` combines the arity, parameter-free formula code, and parameter environment with the derived denotation that will later be shared by all competing names.

Names are compared lexicographically: first by the formula code under the limit-stage order, then by arity, and finally by the parameter vectors under the given order on the carrier. The formula `≺At` expresses these three cases. `LeastNameAt` only states that the displayed name has no smaller name with the same denotation; the actual choice of a least name is the earlier construction `CanonicalNames.leastName`. `StepAt` locally quantifies two least names and compares them. The adequacy proved in this chapter reaches exactly `≺At` versus the meta-level relation `_≺ₙ_`; the full adequacy of `NameAt`, `LeastNameAt`, and `StepAt` is established in the following development.
<!--zh-->
同一个可定义子集可能有许多名字。在元语言中，一个名字由三份数据组成：元数 `k`、具有 `suc k` 个变元位的无参公式，以及取自载体的 `k` 个参数所成的向量。名字的指称由这三份数据派生：多出的那个变元表示待判断的元素，其余变元接收参数向量。因此，指称不是名字的第四个分量。

为了在 `L` 内表达这些数据，本章把参数向量表示为有穷环境图，并用满足关系图表示公式的读取。在真实的公式键处，`satGraphAt` 把该键关联到所有满足该公式的环境所成的集合。因此，它的输出恰是这个满足环境集。`NameAt` 把元数、无参公式码和参数环境与派生的指称联系起来；后文量化竞争名字时，它们都要具有同一个指称。

名字按字典序比较：先由极限层上的序比较公式码，再比较元数，最后依载体上给定的序比较参数向量。公式 `≺At` 表达这三种情形。`LeastNameAt` 只陈述当前名字没有同指称而更小的名字；真正选出最小名字的是前文的 `CanonicalNames.leastName`。`StepAt` 在局部量化两条最小名字并比较它们。本章完成的充分性恰好止于 `≺At` 与元语言关系 `_≺ₙ_` 的对应；`NameAt`、`LeastNameAt` 与 `StepAt` 的完整充分性由后续发展给出。
<!--ja-->
同じ定義可能な部分集合が複数の名前をもつことがあります。メタ言語における名前は、アリティ `k`、`suc k` 個の変数位置をもつ無パラメータ論理式、そして台から取った `k` 個のパラメータのベクトルから成ります。名前の指示対象は、この三つのデータから導かれます。余分な一つの変数が候補となる要素を表し、残りの変数がパラメータベクトルを受け取ります。したがって、指示対象は名前の第四の成分ではありません。

このデータを `L` の内部で表すために、本章はパラメータベクトルを有限な環境グラフで表し、論理式の評価を充足関係グラフで表します。正しい論理式キーにおいて、`satGraphAt` はそのキーを、論理式を満たす環境全体の集合に関係づけます。その出力は、まさにこの充足環境の集合です。`NameAt` はアリティ、無パラメータ論理式の符号、パラメータ環境を、それらから導かれる指示対象に結び付けます。後で競合する名前を量化するとき、それらは同じ指示対象をもたなければなりません。

名前は辞書式に比較されます。まず極限段階の順序で論理式の符号を比較し、次にアリティを比較し、最後に台上の与えられた順序でパラメータベクトルを比較します。論理式 `≺At` はこの三つの場合を表します。`LeastNameAt` は、同じ指示対象をもち、現在の名前より小さい名前がないことを述べるだけです。最小名を実際に選ぶのは、先に構成された `CanonicalNames.leastName` です。`StepAt` は二つの最小名を局所的に量化して比較します。本章で証明する妥当性は、ちょうど `≺At` とメタ言語の関係 `_≺ₙ_` との対応までです。`NameAt`、`LeastNameAt`、`StepAt` の完全な妥当性は後続の展開で証明されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The underlying language supplies universe levels, finite indices, vectors, and proposition-valued statements. Classical reasoning enters through one explicit hypothesis, `LEM (ℓ-suc ℓ)`, whose level is large enough for the satisfaction constructions and well-orders used below. Keeping that hypothesis visible will let us distinguish descriptions that merely state a property from earlier constructions that actually choose a witness.
<!--zh-->
底层语言供给宇宙层级、有穷指标、向量与取值为命题的陈述。经典推理只经一个显式假设 `LEM (ℓ-suc ℓ)` 进入；它的层级足以承载下文使用的满足关系构造与良序。保留这个显式假设，有助于区分「只陈述一项性质」与「真正选出一个见证」这两类步骤。
<!--ja-->
基礎となる言語は、宇宙レベル、有限添字、ベクトル、命題値の主張を与えます。古典的推論は、明示された一つの仮定 `LEM (ℓ-suc ℓ)` を通して入ります。そのレベルは、以下で使う充足関係の構成と整列順序を扱うのに十分です。この仮定を明示しておくことで、性質を述べるだけの記述と、証人を実際に選ぶ先行の構成とを区別できます。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and a law of excluded middle at the required higher level. This is the classical interface carried by the chapter. The formula constructors below only assemble syntax, but the natural-number object, satisfaction graph, limit-stage code order, and canonical-name theory that they use were constructed under the same hypothesis. The module therefore records these semantic dependencies without performing another choice. `LeastNameAt` expresses minimality; `CanonicalNames.leastName` remains the construction that selects a least name.
<!--zh-->
现在固定宇宙层级 `ℓ`，并在所需的更高层级上假设排中律。这是本章沿用的经典逻辑接口。下面的公式构造器只组合语法，但它们使用的自然数对象、满足关系图、极限层码序和典范名字理论都在同一假设下构造。因此，本模块如实记录这些语义依赖，而不再次作选择。`LeastNameAt` 表达最小性；实际选出最小名字的构造仍是 `CanonicalNames.leastName`。
<!--ja-->
宇宙レベル `ℓ` と、必要な一段高いレベルでの排中律を固定します。これは本章が引き継ぐ古典論理のインターフェースです。以下の論理式構成子は構文を組み立てるだけですが、そこで用いる自然数対象、充足関係グラフ、極限段階の符号順序、正準名の理論は、いずれも同じ仮定のもとで構成されています。したがって、このモジュールはこれらの意味論的依存関係を記録しますが、改めて選択を行うことはありません。`LeastNameAt` は最小性を表し、最小名を選ぶ構成は引き続き `CanonicalNames.leastName` です。
<!--/-->

```agda
module L.Choice.NameComparison {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The object language can speak about membership and equality, combine propositions, and quantify both over the whole carrier and over a set. Its semantics is read in a proposition-valued structure. Constant mappings connect three presentations needed later: genuinely parameter-free formulas, formulas over the empty alphabet, and the same syntax interpreted over a constructible carrier. Because these mappings preserve the formula, they will allow the code of a parameter-free skeleton to be recognized internally.
<!--zh-->
对象语言能够陈述隶属与相等，组合命题，并在整个载体或某个集合上量化；它的语义在取值为命题的结构中读取。常元映射连接后文所需的三种呈现：真正的无参公式、空字母表上的公式，以及在可构造载体上解释的同一语法。这些映射保持公式结构，因此后文可以在内部辨认一个无参骨架的码。
<!--ja-->
対象言語は所属と等号を述べ、命題を組み合わせ、台全体または一つの集合の上で量化できます。その意味論は命題値の構造で読み取られます。定数の写像は、後で必要となる三つの表示を結び付けます。すなわち、本当にパラメータをもたない論理式、空のアルファベット上の論理式、構成可能な台上で解釈された同じ構文です。これらの写像は論理式の構造を保つので、無パラメータ骨格の符号を内部で認識できるようになります。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp; embed )
```

<!--en-->
Formula codes, ordered pairs, and numerals are themselves sets in the cumulative hierarchy. The constructible substructure supplies the carrier in which the formulas are read, while transitivity lets membership in a constructible code set provide the constructibility facts needed for its components. Injectivity of pair and numeral coding later recovers arities and skeleton codes from equal keys. The stages `Lset` provide the setting for the limit-stage code order.
<!--zh-->
公式码、有序对与数码本身都是累积层级中的集合。可构造子结构提供读取这些公式的载体；传递性则使码集中的隶属事实能够供给其分量所需的可构造性。配对编码与数码编码的单射性将在后文从相等的键中恢复元数与骨架码。诸 `Lset` 层为极限层码序提供背景。
<!--ja-->
論理式の符号、順序対、数項は、それ自身が累積階層の集合です。構成可能部分構造は論理式を読む台を与え、推移性は構成可能な符号集合への所属から、その成分に必要な構成可能性を与えます。対の符号化と数項の符号化の単射性によって、後に等しいキーからアリティと骨格符号を復元できます。各 `Lset` 段階は極限段階の符号順序の舞台となります。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Ordinal {ℓ} using ( ∈#-elim; #∈#-elim )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; extensionalL )
```

<!--en-->
An arity is represented by a numeral in the internal natural-number set, and a parameter vector is represented by the graph of a finite environment. The object-language formulas can inspect ordered pairs, applications, and domains, extend an environment by a candidate element, and define a subset extensionally. For a formula over a carrier, `Sat` is the set of environments satisfying that formula. This set-valued reading is the semantic value later recovered from the satisfaction graph.
<!--zh-->
元数由内部自然数集中的数码表示，参数向量则由有穷环境的图表示。对象语言公式能够检查有序对、应用与定义域，把一个待判断的元素加入环境，并以外延方式定义子集。对于载体上的一条公式，`Sat` 是所有满足该公式的环境所成的集合。后文从满足关系图恢复的正是这个集合值。
<!--ja-->
アリティは内部の自然数集合に属する数項で表し、パラメータベクトルは有限環境のグラフで表します。対象言語の論理式は、順序対、適用、定義域を調べ、候補となる要素を環境に追加し、外延的に部分集合を定義できます。ある台上の論理式に対して、`Sat` はその論理式を満たす環境全体の集合です。後で充足関係グラフから復元する意味論的な値は、この集合です。
<!--/-->

```agda
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; appAt; appAt-adequate; domAt; domAt-in; domAt-out; domAt-intro; envOverAt )
open import L.Coding.Expressions {ℓ} using ( extAt; extAt-in-both; numL; sucAtL; sucAtL-adequate; consAtL )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
```

<!--en-->
Satisfaction has already been organized into a table whose entries pair each subformula key with its recursively determined set of satisfying environments. Slot closure and totality ensure that every genuine key needed in the recursion receives an entry, and the satisfaction bridge identifies its constants with elements of the chosen carrier. The present chapter can therefore read a stored value at a key without running the satisfaction recursion again.
<!--zh-->
满足关系已经被组织成一张表，其中每个条目把子公式键与递归确定的满足环境集配成一对。槽位闭包与全性保证递归所需的每个真实键都有条目，满足关系桥则把公式中的常元认作所选载体的元素。因此，本章可以读取某个键处已经存下的集合值，而无须重新运行满足关系递归。
<!--ja-->
充足関係はすでに表として構成されており、各項目は部分式のキーと、再帰的に定まる充足環境の集合を対にしています。スロットの閉性と全性により、再帰で必要となるすべての正しいキーに項目が与えられ、充足関係の橋渡しが論理式の定数を選ばれた台の要素として同定します。したがって本章では、充足関係の再帰を再実行せずに、キーに保存された集合値を読み取れます。
<!--/-->

```agda
open import L.Coding.SatisfactionTable {ℓ} lem
  using ( slot; satTable; total; inSlot; entry-in )
open import L.Coding.SlotClosure {ℓ} lem using ( slotClosed )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst )
open import L.Coding.CodeSet {ℓ} lem
```

<!--en-->
For each carrier, `AllCodes` collects exactly the genuine formula keys over that carrier, and its two directions connect membership with an underlying formula. The uniform bridge then supports the relational formula `satGraphAt B x y`: when `x` is a genuine key over the carrier in slot `B`, `y` is the corresponding set of satisfying environments. `GraphWitAt` and the two graph readings expose this set-valued relation without starting a fresh recursion.
<!--zh-->
对每个载体，`AllCodes` 恰好收集该载体上所有真实的公式键；它的两个方向把成员关系与相应公式联系起来。统一满足关系桥由此支持关系公式 `satGraphAt B x y`：当 `x` 是槽位 `B` 所持载体上的真实键时，`y` 就是相应的满足环境集。`GraphWitAt` 与两条图读式揭示这项集合值关系，而无须启动新的递归。
<!--ja-->
各台について、`AllCodes` はその台上の正しい論理式キーをちょうど集め、その二方向の読みは所属と元の論理式を結び付けます。統一充足関係の橋渡しは、関係を表す論理式 `satGraphAt B x y` を支えます。`x` がスロット `B` の台上の正しいキーであるとき、`y` は対応する充足環境の集合です。`GraphWitAt` と二つのグラフの読みは、この集合値の関係を新しい再帰なしに示します。
<!--/-->

```agda
  using ( keyS; AllCodes; AllCodes-out; key∈AllCodes )
open import L.Coding.UniformSatisfaction {ℓ} lem using ( keyBridge )
open import L.Coding.SatisfactionGraph {ℓ} lem using
  ( satGraphAt; GraphWitAt; graphAt-in; graphAt-out
  ; Bi; Ti; Ci; Ei; NN; ev; numν; numTags )
```

<!--en-->
The environment tower and the tagged recursion data justify the satisfaction-graph reading at every syntactic constructor. Against this internal machinery, the canonical-name theory supplies the meta-level standard used for comparison. A meta-level `Name` stores an arity, a parameter-free formula, and a parameter vector; `limitCode` derives the first comparison key from the formula, while the denotation is separately derived by satisfaction. This distinction is what the later slot formula must preserve.
<!--zh-->
环境塔与带标签的递归数据证明满足关系图的读法对每种语法构造都成立。与这套内部机制相对照，典范名字理论供给名字比较所遵循的元语言标准。元语言的 `Name` 存储元数、无参公式与参数向量；`limitCode` 从公式派生第一个比较键，而指称则另由满足关系派生。后文的槽位公式必须保持这一区分。
<!--ja-->
環境の塔とタグ付き再帰データは、充足関係グラフの読みが各構文要素について成り立つことを保証します。この内部の仕組みに対し、正準名の理論は名前比較の基準となるメタ言語の対象を与えます。メタ言語の `Name` が保存するのは、アリティ、無パラメータ論理式、パラメータベクトルです。`limitCode` は論理式から第一の比較キーを導き、指示対象は充足関係から別に導かれます。後のスロット論理式も、この区別を保たなければなりません。
<!--/-->

```agda
open import L.Coding.EnvironmentTower {ℓ} lem using ( towerAt; module Tower; module TowerHolds )
open import L.Coding.Quantification {ℓ} using ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9 )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.PinnedRecursion {ℓ} lem using ( module SatSoundC; module SlotHolds )
open import L.Choice.CanonicalNames {ℓ} lem using ( module Naming; limitCode )
```

<!--en-->
The code of a name is a member of the limit stage and is compared by `limitOrder`. The third key comes from an arbitrary strict well-order on the carrier. Canonical naming has already combined these with natural-number arity into `_≺ₙ_`, proved that relation well-founded, and used it in `leastName`. Here the two non-numerical orders appear through relation slots with representation laws, so the chapter describes their comparison rather than reconstructing either order.
<!--zh-->
名字的码是极限层的成员，并由 `limitOrder` 比较。第三个键来自载体上任意给定的严格良序。典范命名理论已经把这两项与自然数元数组合成 `_≺ₙ_`，证明该关系良基，并在 `leastName` 中使用它。本章让两个非数值的序经带有表示律的关系槽位出现，因而只描述它们所决定的比较，而不重新构造其中任何一个序。
<!--ja-->
名前の符号は極限段階の要素であり、`limitOrder` によって比較されます。第三のキーは、台上に与えられた任意の狭義整列順序から来ます。正準名の理論は、これらと自然数のアリティをすでに `_≺ₙ_` にまとめ、その関係の整礎性を証明し、`leastName` で用いています。本章では二つの非数値的な順序を、表示法則を伴う関係スロットによって受け取ります。したがって、どちらの順序も再構成せず、それらによる比較を記述します。
<!--/-->

```agda
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Limit; limitOrder )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )

```

<!--en-->
Natural-number order supplies the second comparison key: for numeral arities, membership of one numeral in another expresses strict inequality. Finite indices locate entries of parameter vectors and the earliest position at which two vectors differ. The adequacy argument later proves, by induction on their common length, that this first-difference description agrees with the recursive vector order used in `_≺ₙ_`.
<!--zh-->
自然数序供给第二个比较键：当元数表示为数码时，一个数码隶属于另一个数码正好表达严格小于。有穷指标用于定位参数向量的分量，以及两个向量最早出现差异的位置。后文的充分性论证对共同长度作归纳，证明这种「首次相异」描述与 `_≺ₙ_` 所用的递归向量序一致。
<!--ja-->
自然数の順序が第二の比較キーを与えます。アリティが数項で表されるとき、一方の数項が他方に所属することは狭義の不等号を表します。有限添字は、パラメータベクトルの成分と、二つのベクトルが最初に異なる位置を指定します。後の妥当性の議論では、共通の長さに関する帰納法により、この最初の相違による記述が `_≺ₙ_` で使われる再帰的なベクトル順序と一致することを証明します。
<!--/-->

```agda
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Order
  using ( _<_; zero-≤; suc-≤-suc; pred-≤-pred; ¬-<-zero; <-trans )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
```

<!--en-->
The proof data follow the lexicographic shape. Dependent pairs carry a position together with its evidence, while coproducts separate the code, arity, and parameter cases. Equalities of earlier keys permit dependent formulas and vectors to be transported to a common arity before the next key is compared. The empty type supplies the unique interpretation of constants for a formula that has no constants.
<!--zh-->
证明数据遵循字典序的形状。依值对携带某个位置及其证据，余积则区分码、元数与参数三种情形。前面诸键的相等性允许把依值公式与向量运输到共同元数，再比较下一个键。空类型给出无常元公式所需的唯一常元解释。
<!--ja-->
証明データは辞書式順序の形に従います。依存対は位置とその証拠を運び、直和は符号、アリティ、パラメータの三つの場合を分けます。先行するキーの等しさにより、依存する論理式とベクトルを共通のアリティへ輸送してから、次のキーを比較できます。空の型は、定数をもたない論理式に必要な定数解釈を一意に与えます。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
```

<!--en-->
Existential and disjunctive satisfaction is propositionally truncated: it preserves that a witness exists while forgetting which witness was supplied. Consequently, outward readings such as those for formula codes and name comparison return truncated existence, and elimination is used only into propositions. This is propositional truncation; propositional resizing does not occur here. The cumulative hierarchy supplies set-valued membership and the extensional equality principles needed after such readings.
<!--zh-->
存在式与析取式的满足语义带有命题截断：它保留「见证存在」，却忘掉给出的是哪个见证。因此，从公式码或名字比较向外读取时，结论仍是经过命题截断的存在性，而消去也只进入命题。这里发生的是命题截断；命题降级并未在此出现。累积层级则供给集合值的隶属关系，以及这些读式之后所需的外延相等原则。
<!--ja-->
存在式と選言式の充足意味論は命題的に切り詰められています。証人が存在することは保ちますが、どの証人が与えられたかは忘れます。そのため、論理式の符号や名前比較を外向きに読むと、結論にも切り詰められた存在が残り、消去先は命題に限られます。ここで使われるのは命題的切り詰めであり、命題のリサイズではありません。累積階層は集合値の所属関係と、その読みの後で必要となる外延的な等しさの原理を与えます。
<!--/-->

```agda
open import Cubical.Foundations.Transport using ( constSubstCommSlice )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
```

<!--en-->
Small members of a hierarchy set embed into the ambient hierarchy, and injectivity of that embedding later turns equality of represented parameters back into equality in the carrier. The empty set serves as the empty alphabet: it has no constants, so every map out of it is uniquely determined and a parameter-free formula keeps the same code under the required relabellings. The von Neumann numerals `# k`, their successor, and `ω` provide the internal arities used by environment domains and name comparison.
<!--zh-->
层级集合的小成员能够嵌入外围层级；该嵌入的单射性将在后文把已表示参数的相等恢复为载体中的相等。空集充当空字母表：它没有常元，因此从它出发的映射唯一确定，无参公式在所需的重标记下保持同一个码。冯·诺伊曼数码 `# k`、它们的后继与 `ω` 则提供环境定义域和名字比较所用的内部元数。
<!--ja-->
階層集合の小さな要素は周囲の階層へ埋め込まれ、その埋め込みの単射性によって、後に表現されたパラメータの等しさから台の中での等しさを復元できます。空集合は空のアルファベットとして働きます。定数がないので、そこから出る写像は一意に定まり、無パラメータ論理式は必要な付け替えの下で同じ符号を保ちます。フォン・ノイマン数項 `# k`、その後者、そして `ω` が、環境の定義域と名前比較に使う内部のアリティを与えます。
<!--/-->

```agda
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_; ω; sucV )
```

<!--en-->
The formulas ahead are interpreted in the constructible universe. Opening
`hPropStructure 𝒮ʟ` fixes their carrier `S`: an element is an ambient set
together with evidence that it is constructible. It also brings the
proposition-valued equality and membership relations of this structure into
scope. Thus a free variable or constant ranges over constructible sets, while
`⟨_⟩` exposes the type of evidence carried by an equality or membership
proposition when a proof uses it.
<!--zh-->
下文的公式都解释在可构造宇宙中。打开 `hPropStructure 𝒮ʟ` 便固定了它们的载体 `S`：载体的一个元素是环境宇宙中的一个集合，连同它可构造的证据。这个操作也把该结构中取命题值的等词与隶属关系带入作用域。因此，自由变元与常元都在可构造集合中取值；证明需要使用某条等词或隶属命题的证据时，`⟨_⟩` 则取出该命题的底层类型。
<!--ja-->
以下の論理式は構成可能宇宙で解釈されます。`hPropStructure 𝒮ʟ` を開くことで、その台 `S` が定まります。台の要素は、周囲の宇宙にある集合と、それが構成可能であるという証拠の組です。また、この構造の命題値をとる等号関係と所属関係もスコープに入ります。したがって自由変数と定数は構成可能集合の中を動き、証明で等号や所属の証拠が必要なときには、`⟨_⟩` がその命題の基礎型を取り出します。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

```

<!--en-->
There are two compatible readings of the same syntax. The absoluteness
instance starts with the ambient universe structure `𝒮ᵥ` and restricts it to
the transitive class `isL`. In the outer reading, a constructible set is
viewed through its underlying ambient set; in the inner reading, a constant
denotes the constructible set that names it and the restricted structure
supplies equality and membership. This chapter renames the inner satisfaction
relation to `⊨`. Consequently, for `γ : S ^ n`, the judgement `γ ⊨ F` says
that `F` holds inside `L` under the finite environment `γ`. This is the
reading needed for formulas that `L` itself will use to recognize and compare
names.
<!--zh-->
同一套句法有两种彼此相容的读法。这个绝对性实例从环境宇宙结构 `𝒮ᵥ` 出发，把它限制到传递类 `isL`。在外层读法中，一个可构造集合经其底层的环境集合来读取；在内层读法中，常元指称为它命名的那个可构造集合，而等词与隶属由限制后的结构解释。本章把内层满足关系改名为 `⊨`。因此，对 `γ : S ^ n`，判断 `γ ⊨ F` 表示公式 `F` 在 `L` 内部、有限环境 `γ` 下成立。这正是 `L` 自身识别并比较名字时所需的读法。
<!--ja-->
同じ構文には、互いに両立する二つの読み方があります。この絶対性の実例は、周囲の宇宙の構造 `𝒮ᵥ` から出発し、それを推移的クラス `isL` に制限します。外側の読みでは構成可能集合をその基礎にある周囲の集合として扱い、内側の読みでは定数がそれを名指す構成可能集合を表し、制限された構造が等号と所属を解釈します。本章では内側の充足関係を `⊨` と書きます。したがって `γ : S ^ n` に対する判断 `γ ⊨ F` は、有限環境 `γ` のもとで `F` が `L` の内部に成り立つことを意味します。これは、`L` 自身が名前を識別して比較する論理式に必要な読み方です。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
The formulas refer to earlier data by positions in an environment. Under a
new binder, every such position must move past the newly bound value; after
two binders, position `i` therefore becomes `suc (suc i)`. The abbreviation
`sh2` records this move. It is used when `FreeAt` has bound the successor
arity and its code key before consulting the skeleton and empty-alphabet code
set, and when the denotation condition has bound a candidate element and its
extended environment before consulting the original parameter environment.
<!--zh-->
这些公式用环境中的位置指向先前给定的数据。每进入一层新的约束，原有位置都必须越过新绑定的取值；经过两层约束后，位置 `i` 因而变成 `suc (suc i)`。缩写 `sh2` 记录的正是这次移动。`FreeAt` 先绑定后继元数及其码键，再读取骨架与空字母表码集时会用到它；指称条件先绑定候选元素及其扩展环境，再读取原参数环境时也会用到它。
<!--ja-->
これらの論理式は、環境内の位置によって先に与えられたデータを参照します。新しい束縛子の下では、もとの位置は新たに束縛された値を越えなければなりません。二つの束縛子の下では、位置 `i` は `suc (suc i)` になります。`sh2` はこの移動を表す略記です。`FreeAt` が後続のアリティとその符号鍵を束縛してから骨格と空のアルファベットの符号集合を参照するとき、また表示の条件が候補要素と拡張環境を束縛してからもとのパラメータ環境を参照するときに使われます。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

```

<!--en-->
Inside the denotation condition, the skeleton and the carrier's code set are
consulted only after four values have entered the environment: the candidate
element `z`, the extended environment `c`, its domain `k`, and the key under
consideration. Their original positions must therefore be raised four times.
`sh4` performs exactly that shift, so the key can be required both to belong
to the carrier's code set and to equal the pair formed from `k` and the
skeleton.
<!--zh-->
在指称条件内部，须等四个取值进入环境之后，才会读取骨架与载体的码集。这四个取值依次是候选元素 `z`、扩展环境 `c`、它的定义域 `k`，以及正在考察的键。因此，原来的位置必须连续提升四次。`sh4` 恰好执行这次移位，使公式既能要求该键属于载体的码集，也能要求它等于由 `k` 与骨架组成的对。
<!--ja-->
表示の条件の内部では、四つの値が環境に加わった後で初めて、骨格と台の符号集合を参照します。その四つは、候補要素 `z`、拡張環境 `c`、その定義域 `k`、そして考察中の鍵です。したがって、もとの位置を四回持ち上げる必要があります。`sh4` はまさにこの移動を行い、その鍵が台の符号集合に属することと、`k` と骨格から作られる対に等しいことの両方を述べられるようにします。
<!--/-->

```agda
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

```

<!--en-->
One more existential binds the value `v` associated with the key, so the
carrier is five places away when `satGraphAt` is invoked. Here `v` is the set
of environments satisfying the encoded formula, rather than a truth value;
the following membership atom asks whether the extended environment belongs
to that set. The same shift reappears in `LexAt`: after binding an index, the
two values at that index, an earlier index, and their proposed common value,
the original parameter environments are again five places away. `sh5`
records the common index calculation for both formulas.
<!--zh-->
再有一层存在量词绑定与该键相配的取值 `v`，所以调用 `satGraphAt` 时，载体的位置已隔着五个新取值。这里的 `v` 是满足被编码公式的诸环境所成的集合，并不是真值；紧接着的隶属原子询问扩展环境是否属于这个集合。同一档移位还出现在 `LexAt` 中：依次绑定一个序号、两个环境在该处的取值、一个更早的序号，以及见证两边相符的共同取值后，原参数环境也恰好隔着五个位置。`sh5` 统一记录了两处的下标计算。
<!--ja-->
さらに一つの存在量化子が鍵に対応する値 `v` を束縛するため、`satGraphAt` を用いる時点では台が五つ先の位置にあります。ここで `v` は符号化された論理式を充足する環境全体の集合であり、真理値ではありません。続く所属原子は、拡張環境がその集合に属するかを問います。同じ移動は `LexAt` にも現れます。一つの添字、その位置で二つの環境から得られる値、より前の添字、そして両者の一致を証す共通の値を順に束縛すると、もとのパラメータ環境はやはり五つ先にあります。`sh5` は両方の論理式に共通する添字計算を記録します。
<!--/-->

```agda
  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 i = suc (suc (suc (suc (suc i))))
```

<!--en-->
## The same code at the empty alphabet
<!--zh-->
## 同一个码，落在空字母表上
<!--ja-->
## 空のアルファベットでも同じ符号
<!--/-->

<!--en-->
The empty alphabet is the small presentation `⟪ ∅ ⟫` of members of the empty
set. If `m` were one of its symbols, the embedding `⟪ ∅ ⟫↪` would produce an
ambient set, while the presentation law would say that this set belongs to
`∅`. The theorem `∅-empty` rules out precisely such evidence, giving
`noAlpha m`. Thus formulas over this alphabet cannot contain a constant node.
They form one syntactic presentation of parameter-free formulas. Comparing it
with the empty constant domain `⊥*` used by meta-level names amounts to
relating two empty types.
<!--zh-->
空字母表是空集成员的小表示 `⟪ ∅ ⟫`。如果 `m` 是其中一个符号，那么嵌入 `⟪ ∅ ⟫↪` 会给出一个环境集合，而表示定律会断言这个集合属于 `∅`。定理 `∅-empty` 恰好排除了这种证据，由此得到 `noAlpha m`。所以，这个字母表上的公式不可能含有常元节点。它们给出了无参公式的一种句法呈现；要把它与元层面名字所用的空常元域 `⊥*` 联系起来，只须关联这两个空类型。
<!--ja-->
空のアルファベットは、空集合の要素の小さな表示 `⟪ ∅ ⟫` です。もし `m` がその記号の一つなら、埋め込み `⟪ ∅ ⟫↪` によって周囲の集合が得られ、表示の法則はそれが `∅` に属すると述べます。定理 `∅-empty` はまさにそのような証拠を否定するので、`noAlpha m` が従います。したがって、このアルファベット上の論理式は定数の節を含めません。これは無パラメータ論理式の一つの構文的表示です。メタ言語の名前が用いる空の定数域 `⊥*` と比較するには、この二つの空型を結び付ければ十分です。
<!--/-->

```agda
private
  noAlpha : ⟪ ∅ {ℓ} ⟫ → Empty.⊥
  noAlpha m = ∅-empty (⟪ ∅ ⟫↪ m) (∈ₛ⟪ ∅ ⟫↪ m)

```

<!--en-->
`Fo∅ n` names the family `Formula ⟪ ∅ ⟫ n`: formulas over the empty alphabet
with `n` available variable positions. Their lack of constants follows from
the type of their constant symbols, rather than from an extra predicate on a
formula. Meta-level names use the parallel family `Formula ⊥* n`. More
precisely, a `Name` stores an arity, a formula from that family with one extra
variable position, and a parameter vector of the stated arity; its denotation
is derived from those three pieces and is not another stored component.
<!--zh-->
`Fo∅ n` 是公式族 `Formula ⟪ ∅ ⟫ n` 的简称，也就是空字母表上具有 `n` 个可用变元位置的公式。它们不含常元，这是由常元符号的类型保证的，并非另有一个作用于公式的谓词。元层面名字使用与之平行的公式族 `Formula ⊥* n`。更确切地说，一个 `Name` 存储元数、在这个公式族中多出一个变元位置的无参公式，以及具有该元数的参数向量；指称由这三份数据派生，并不是另一个存储分量。
<!--ja-->
`Fo∅ n` は、`n` 個の変数位置を使える空のアルファベット上の論理式の族 `Formula ⟪ ∅ ⟫ n` を表す略記です。定数を含まないことは、論理式に別の述語を課すのではなく、定数記号の型そのものから従います。メタ言語の名前は、これに対応する族 `Formula ⊥* n` を使います。より正確には、`Name` が格納するのはアリティ、この族に属して変数位置を一つ余分にもつ無パラメータ論理式、そしてそのアリティのパラメータ列です。表示はこの三つから導かれるものであり、別の格納成分ではありません。
<!--/-->

```agda
  Fo∅ : ℕ → Type ℓ
  Fo∅ = Formula ⟪ ∅ {ℓ} ⟫

```

<!--en-->
The map `ε` changes from the empty alphabet `⟪ ∅ ⟫` to the empty constant
domain `⊥*`. Given a supposed source symbol `m`, `noAlpha m` yields a
contradiction, and empty elimination supplies the requested target. Hence
`mapFo ε` relabels a formula over `⟪ ∅ ⟫` as a formula over `⊥*`; in the other
direction, `embed` may be specialized to relabel from `⊥*` into `⟪ ∅ ⟫`.
Neither operation changes a constant occurrence, since there is none. The
composition law for relabelling then yields the precise equalities of formula
codes needed for the empty-alphabet characterization.
<!--zh-->
映射 `ε` 把空字母表 `⟪ ∅ ⟫` 送到空常元域 `⊥*`。给定一个假想的源符号 `m`，`noAlpha m` 导出矛盾，再由空型消去得到所需的目标。因此，`mapFo ε` 把 `⟪ ∅ ⟫` 上的公式改名为 `⊥*` 上的公式；反方向则可把 `embed` 特化为从 `⊥*` 到 `⟪ ∅ ⟫` 的改名。两种操作都不会改变任何常元出现，因为本来就没有常元。改名的复合法则因而给出空字母表刻画所需的精确公式码等式。
<!--ja-->
写像 `ε` は、空のアルファベット `⟪ ∅ ⟫` から空の定数域 `⊥*` への移行を与えます。仮に始域の記号 `m` が与えられれば、`noAlpha m` が矛盾を導き、空型の消去によって必要な終域の値が得られます。したがって `mapFo ε` は `⟪ ∅ ⟫` 上の論理式を `⊥*` 上の論理式へ改名します。逆向きには、`embed` を `⊥*` から `⟪ ∅ ⟫` への改名として特殊化できます。もともと定数の出現がないので、どちらの操作も定数の出現を変えません。そこで改名の合成則から、空のアルファベットによる特徴付けに必要な論理式の符号の等式が得られます。
<!--/-->

```agda
  ε : ⟪ ∅ {ℓ} ⟫ → ⊥* {ℓ}
  ε m = Empty.rec (noAlpha m)

```

<!--en-->
To recognize parameter-free formula codes inside the model, we must first relate
two presentations of having no constants. A formula `ψ` over `⟪ ∅ ⟫` uses as its
constant domain the members of the empty set, while `mapFo ε ψ` presents the same
syntax over the empty type `⊥*`. The map `ε` exists because an alleged member of
the empty set yields a contradiction. Reading `ψ` directly into the universe and
first relabelling it by `ε` and then embedding it therefore differ only by maps
out of an empty type. Function extensionality identifies those maps, and
`mapFo-comp` identifies the composite relabelling. Thus `sameCode` proves an
equality of the resulting universe-formulas themselves; applying the coding map
to this equality will later give equality of their codes.
<!--zh-->
要在模型内部识别无参公式的码，首先必须联系「没有常元」的两种表示。以`⟪ ∅ ⟫` 为常元域的公式 `ψ`，其常元来自空集的成员；而 `mapFo ε ψ` 把同一份语法表示在空类型 `⊥*` 上。若假定空集有一个成员便会得到矛盾，所以映射 `ε`得以定义。于是，直接把 `ψ` 读入宇宙，与先沿 `ε` 改名再嵌入宇宙，两者的差别只在于从空类型出发的映射。函数外延性判定这些映射相等，`mapFo-comp` 再判定复合改名相等。因此，`sameCode` 首先证明所得宇宙公式本身相等；稍后对这条等式施用编码映射，便得到相应码的等式。
<!--ja-->
モデルの内部で無パラメータ論理式のコードを認識するには、まず「定数を持たない」ことの二つの表し方を結び付ける必要があります。`⟪ ∅ ⟫` 上の論理式`ψ` では、定数域は空集合の要素の型です。一方、`mapFo ε ψ` は同じ構文を空型`⊥*` の上で表します。空集合の要素を仮定すれば矛盾が得られるため、写像 `ε`を定義できます。したがって、`ψ` を直接宇宙へ読む経路と、`ε` に沿って改名してから宇宙へ埋め込む経路の違いは、空型から出る写像の違いだけです。関数外延性がそれらの写像を同一視し、`mapFo-comp` が改名の合成を同一視します。このように `sameCode` は、まず得られる宇宙上の論理式そのものの等式を証明します。後でこの等式にコード化写像を適用すれば、対応するコードの等式が得られます。
<!--/-->

```agda
  sameCode : ∀ {n} (ψ : Fo∅ n) → mapFo ⟪ ∅ ⟫↪ ψ ≡ embed (mapFo ε ψ)
  sameCode ψ = cong (λ f → mapFo f ψ) (funExt (λ m → Empty.rec (noAlpha m)))
             ∙ sym (mapFo-comp ε Empty.rec* ψ)

```

<!--en-->
The converse comparison begins with a parameter-free formula
`χ : Formula ⊥* n`. It may be embedded first into formulas over `⟪ ∅ ⟫` and
then relabelled by the inclusion of that alphabet into the universe, or embedded
directly into formulas over the universe. By `mapFo-comp`, the first route is a
single relabelling from `⊥*`; since every two functions from `⊥*` agree, that
relabelling is the one used by the direct embedding. The equality `sameCode'`
is exactly the orientation needed to pass from the key that `AllCodes ∅ʟ`
assigns to the embedded formula to the usual universe-code of `χ`.
<!--zh-->
反向的比较从无参公式 `χ : Formula ⊥* n` 出发。可以先把它嵌入以 `⟪ ∅ ⟫`为常元域的公式，再沿该字母表到宇宙的包含映射改名；也可以把它直接嵌入宇宙上的公式。由 `mapFo-comp`，第一条路线就是一次从 `⊥*` 出发的改名；而从 `⊥*`出发的任意两个函数都相等，所以这次改名正是直接嵌入所用的改名。`sameCode'`给出的等式方向，恰好能把 `AllCodes ∅ʟ` 赋予嵌入公式的键，转换成 `χ` 通常的宇宙公式码所组成的键。
<!--ja-->
逆向きの比較は、無パラメータ論理式 `χ : Formula ⊥* n` から始まります。まず `χ` を `⟪ ∅ ⟫` 上の論理式へ埋め込み、そのアルファベットから宇宙への包含写像に沿って改名することも、初めから宇宙上の論理式へ埋め込むこともできます。`mapFo-comp` によれば、前者は `⊥*` からの一回の改名です。`⊥*`からの任意の二つの関数は等しいので、この改名は直接の埋め込みで使われるものと一致します。`sameCode'` の等式は、`AllCodes ∅ʟ` が埋め込まれた論理式に与えるキーを、`χ` の通常の宇宙上の論理式コードからなるキーへ移すのに必要な向きを持っています。
<!--/-->

```agda
  sameCode' : ∀ {n} (χ : Formula (⊥* {ℓ}) n)
            → mapFo ⟪ ∅ {ℓ} ⟫↪ (embed χ) ≡ embed χ
  sameCode' χ = mapFo-comp Empty.rec* ⟪ ∅ ⟫↪ χ
              ∙ cong (λ f → mapFo f χ) (funExt (λ b → Empty.rec* b))

```

<!--en-->
There is one further dependent-type issue. The arity is part of the type of a
formula, so an equality `e : i ≡ j` moves `ψ : Fo∅ i` to
`subst Fo∅ e ψ : Fo∅ j`. The key, however, should retain the same formula code
after this move. The codomain of the function that reads and codes a formula is
the fixed universe `V ℓ`, independent of the arity index. The general
substitution computation `constSubstCommSlice` therefore says that transporting
the formula does not change its code. `codeShift` records the equality in the
direction from the transported formula's code back to the original one, ready
for the arity adjustment in the decoding argument.
<!--zh-->
这里还有一个依值类型问题。元数属于公式类型的一部分，所以等式 `e : i ≡ j`会把 `ψ : Fo∅ i` 移到 `subst Fo∅ e ψ : Fo∅ j`。然而完成这次迁移后，键中的公式码应当保持不变。读取并编码公式的函数以固定的宇宙 `V ℓ` 为值域，而该值域不依赖元数索引。因此，一般的替换计算 `constSubstCommSlice` 表明，沿元数等式迁移公式不会改变其码。`codeShift` 把这条等式排成从迁移后公式的码指回原公式之码的方向，以便解码论证随后调整元数。
<!--ja-->
もう一つ、依存型に由来する問題があります。アリティは論理式の型の一部なので、等式 `e : i ≡ j` は `ψ : Fo∅ i` を `subst Fo∅ e ψ : Fo∅ j` へ移します。しかし、この移動の後もキーに入る論理式コードは同じでなければなりません。論理式を読み、コード化する関数の終域は固定された宇宙 `V ℓ` であり、アリティの添字には依存しません。したがって、一般の置換計算 `constSubstCommSlice` により、論理式を輸送してもコードは変わりません。`codeShift` はこの等式を、輸送後の論理式のコードから元のコードへ向かう形で記録し、復号の議論で行うアリティの調整に備えます。
<!--/-->

```agda
  codeShift : {i j : ℕ} (e : i ≡ j) (ψ : Fo∅ i)
            → VCode.⌜ mapFo ⟪ ∅ ⟫↪ (subst Fo∅ e ψ) ⌝
            ≡ VCode.⌜ mapFo ⟪ ∅ ⟫↪ ψ ⌝
  codeShift e ψ = sym (constSubstCommSlice
    Fo∅ (V ℓ) (λ _ u → VCode.⌜ mapFo ⟪ ∅ ⟫↪ u ⌝) e ψ)
```

<!--en-->
We can now prove the easy direction of the code-set bridge. For a
parameter-free `k`-ary formula `χ`, embedding it over `⟪ ∅ ⟫` produces a
formula whose key belongs to `AllCodes ∅ʟ` by `key∈AllCodes`. That key consists
of the numeral `# k` and the code obtained by reading the embedded formula
through the empty alphabet. The equality `sameCode'` identifies this formula
with the direct universe embedding of `χ`; the latter code is precisely
`fst (limitCode χ)`. Transporting membership along that equality proves
`freeCode-in`: the code set contains the arity-and-code key of every
parameter-free formula.
<!--zh-->
现在可以证明码集桥接中较直接的一向。对任意无参 `k` 元公式 `χ`，先把它嵌入 `⟪ ∅ ⟫` 上，所得公式的键由 `key∈AllCodes` 属于 `AllCodes ∅ʟ`。这个键由数码 `# k` 与「经空字母表读入所得的嵌入公式之码」组成。等式 `sameCode'` 把该公式等同于 `χ` 直接嵌入宇宙所得的公式，而后者的码正是 `fst (limitCode χ)`。沿这条等式迁移隶属证明，便得到 `freeCode-in`：码集包含每条无参公式的「元数与码」之键。
<!--ja-->
これで、コード集合との橋の直接な向きを証明できます。無パラメータな `k` 項論理式 `χ` を `⟪ ∅ ⟫` 上へ埋め込むと、その論理式のキーは`key∈AllCodes` により `AllCodes ∅ʟ` に属します。このキーは、数項 `# k` と、埋め込まれた論理式を空のアルファベットを通して読んだコードとの対です。`sameCode'` はその論理式を `χ` の宇宙への直接の埋め込みと同一視し、後者のコードはちょうど `fst (limitCode χ)` です。この等式に沿って所属の証明を輸送すると `freeCode-in` が得られます。すなわち、コード集合はすべての無パラメータ論理式について、アリティとコードからなるキーを含みます。
<!--/-->

```agda

freeCode-in : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
            → ⟨ pr (# k) (fst (limitCode χ)) ∈ fst (AllCodes ∅ʟ) ⟩
freeCode-in k χ =
  subst (λ u → ⟨ pr (# k) VCode.⌜ u ⌝ ∈ fst (AllCodes ∅ʟ) ⟩) (sameCode' χ)
    (key∈AllCodes ∅ʟ (embed χ))
```

<!--en-->
For the reverse direction, suppose `pr (# k) c` belongs to `AllCodes ∅ʟ`.
The elimination theorem `AllCodes-out` decodes a member only under
propositional truncation, and it takes an element of `S`, namely a set together
with a proof that it is constructible. The underlying set of the desired input
is already `pr (# k) c`; it remains to supply that constructibility proof. Once
this is done, `PT.map read` transforms each possible decoded payload into the
desired `k`-ary parameter-free payload without ever removing the truncation.
<!--zh-->
反向则设 `pr (# k) c` 属于 `AllCodes ∅ʟ`。消去定理 `AllCodes-out` 只在命题截断下解码一个成员，而且它接收的是 `S` 的元素，也就是一个集合连同其可构造性证明。所需输入的底层集合已经是 `pr (# k) c`，还须补上它的可构造性证明。完成这一步以后，`PT.map read` 会把命题截断中的每一份可能解码载荷变成所需的 `k` 元无参载荷，始终不消去命题截断。
<!--ja-->
逆向きでは、`pr (# k) c` が `AllCodes ∅ʟ` に属すると仮定します。除去定理`AllCodes-out` は、要素を命題的切り詰めの下でのみ復号し、入力には `S` の要素、すなわち集合とその構成可能性の証明を要求します。必要な入力の台集合はすでに `pr (# k) c` なので、残るのはその構成可能性の証明です。それが得られれば、`PT.map read` は切り詰められた各復号データを、求める `k` 項の無パラメータなデータへ変換します。この操作が命題的切り詰めを取り除くことはありません。
<!--/-->

```agda

freeCode-out : (k : ℕ) (c : V ℓ) → ⟨ pr (# k) c ∈ fst (AllCodes ∅ʟ) ⟩
             → ∥ Σ[ χ ∈ Formula (⊥* {ℓ}) k ] (c ≡ fst (limitCode χ)) ∥₁
freeCode-out k c h = PT.map read (AllCodes-out ∅ʟ (pr (# k) c , cL) h)
  where
  cL : ⟨ isL (pr (# k) c) ⟩
```

<!--en-->
That missing certificate follows from transitivity of constructibility.
`AllCodes ∅ʟ .snd` says that the code set is constructible, while `h` says that
the key belongs to it. Hence `isL-trans h (AllCodes ∅ʟ .snd)` proves that the
key itself is constructible. Pairing this certificate with `pr (# k) c` gives
the element of `S` required by `AllCodes-out`; no additional decoding or choice
occurs here.
<!--zh-->
这张缺少的证书来自可构造性的传递性。`AllCodes ∅ʟ .snd` 说明码集可构造，`h`则说明该键属于码集，故 `isL-trans h (AllCodes ∅ʟ .snd)` 证明键本身可构造。把这张证书与 `pr (# k) c` 配对，就得到 `AllCodes-out` 所要求的 `S` 元素；此处没有额外的解码，也没有发生选择。
<!--ja-->
不足していた証明書は、構成可能性の推移性から得られます。`AllCodes ∅ʟ .snd` はコード集合が構成可能であることを述べ、`h` はキーがその集合に属することを述べます。したがって`isL-trans h (AllCodes ∅ʟ .snd)` により、キー自身の構成可能性が証明されます。この証明書を `pr (# k) c` と組にすれば、`AllCodes-out` が要求する `S` の要素が得られます。ここでは新たな復号も選択も行われません。
<!--/-->

```agda
  cL = isL-trans h (AllCodes ∅ʟ .snd)

```

<!--en-->
Inside the truncation, `AllCodes-out` supplies an arity `n`, a formula
`ψ : Fo∅ n`, and an equality saying that the given key is the key of `ψ`.
The local function `read` turns each such payload into a parameter-free formula
of the requested arity `k` together with an equality between `c` and its code.
It does so by first transporting `ψ` to a formula `ψ' : Fo∅ k` and then
relabelling its impossible constants along `ε`. Thus the proposed witness is
`mapFo ε ψ'`. The pair equality provides both the arity equality needed for the
transport and the code equality used in the returned dependent pair.
<!--zh-->
在命题截断内部，`AllCodes-out` 给出一个元数 `n`、一条公式 `ψ : Fo∅ n`，以及一条说明「给定的键就是 `ψ` 的键」的等式。局部函数 `read` 把每份这样的载荷变成所需元数 `k` 处的一条无参公式，并附上 `c` 等于其码的证明。它先把 `ψ` 迁移为 `ψ' : Fo∅ k`，再沿 `ε` 改名其不可能出现的常元。因此，所构造的见证是 `mapFo ε ψ'`。有序对的等式同时给出迁移所需的元数等式，以及返回依值对时所需的码等式。
<!--ja-->
命題的切り詰めの内部で、`AllCodes-out` はアリティ `n`、論理式`ψ : Fo∅ n`、そして与えられたキーが `ψ` のキーであることを示す等式を与えます。局所関数 `read` は、そのような各データを、要求されたアリティ`k` の無パラメータ論理式と、`c` がそのコードに等しいことの証明へ変換します。まず `ψ` を `ψ' : Fo∅ k` へ輸送し、次に、現れ得ない定数を `ε` に沿って改名します。したがって構成される証人は `mapFo ε ψ'` です。対の等式は、輸送に必要なアリティの等式と、返される依存対に必要なコードの等式をともに与えます。
<!--/-->

```agda
  read : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Fo∅ n ] (pr (# k) c ≡ fst (keyS ∅ʟ ψ))
       → Σ[ χ ∈ Formula (⊥* {ℓ}) k ] (c ≡ fst (limitCode χ))
  read (n , (ψ , q)) = mapFo ε ψ' , (pr-inj q .snd ∙ step)
    where
    e : n ≡ k
```

<!--en-->
The two components of the key equality finish the construction. Its first
component has type `# k ≡ # n`; injectivity of numerals and symmetry yield
`e : n ≡ k`, along which `ψ` is transported to `ψ'`. Its second component says
that `c` is the universe-code obtained from the original `ψ`. By `codeShift`,
that code agrees with the code of the transported `ψ'`; by `sameCode`, the
latter agrees with the code of `embed (mapFo ε ψ')`. Composing these equalities
gives exactly the certificate paired with the witness. Since `read` is applied
only through `PT.map`, `freeCode-out` concludes merely that such a
parameter-free formula exists under propositional truncation. It does not
select a formula from the code set.
<!--zh-->
键等式的两个分量完成这一构造。第一分量的类型是 `# k ≡ # n`；数码的单射性再配合对称性，给出 `e : n ≡ k`，公式 `ψ` 沿它迁移为 `ψ'`。第二分量说明 `c`等于从原公式 `ψ` 得到的宇宙公式码。由 `codeShift`，该码等于迁移后 `ψ'` 的码；再由 `sameCode`，后者等于 `embed (mapFo ε ψ')` 的码。复合这些等式，恰好得到与见证配对的证明。由于 `read` 只通过 `PT.map` 使用，`freeCode-out` 的结论只是在命题截断下存在这样一条无参公式，并未从码集中选择出一条公式。
<!--ja-->
キーの等式の二つの成分が構成を完成させます。第一成分の型は `# k ≡ # n`です。数項の単射性と対称性から `e : n ≡ k` が得られ、`ψ` はそれに沿って`ψ'` へ輸送されます。第二成分は、`c` が元の `ψ` から得られる宇宙上の論理式コードに等しいことを述べます。`codeShift` により、そのコードは輸送後の `ψ'` のコードと一致します。さらに `sameCode` により、後者は`embed (mapFo ε ψ')` のコードと一致します。これらの等式を合成すると、証人と組にすべき証明がちょうど得られます。`read` は `PT.map` を通してのみ使われるため、`freeCode-out` の結論は、そのような無パラメータ論理式が命題的切り詰めの下で存在するということだけです。コード集合から論理式を選び出してはいません。
<!--/-->

```agda
    e = sym (#-inj′ (pr-inj q .fst))
    ψ' : Fo∅ k
    ψ' = subst Fo∅ e ψ
    step : VCode.⌜ mapFo ⟪ ∅ ⟫↪ ψ ⌝ ≡ VCode.⌜ embed (mapFo ε ψ') ⌝
    step = sym (codeShift e ψ) ∙ cong VCode.⌜_⌝ (sameCode ψ')
```

<!--en-->
## Constant-freeness, said as one atom
<!--zh-->
## 无参性，说成一个原子
<!--ja-->
## 無パラメータ性を一つの原子で述べる
<!--/-->

<!--en-->
The code set stores a formula under a key made from its arity and its skeleton.
To express this with one membership atom, `FreeAt` first binds the successor of
the value in the arity slot, then binds its pair with the skeleton, and finally
asks whether that pair belongs to the code-set slot. Thus, in meta-level
notation, its shape is `∃[ z ] ∃[ y ]`: `z` is the successor arity, while `y`
is the key. The shifts record exactly which earlier slot remains visible beneath
one or two binders. At this stage the formula only describes membership in the
set supplied at `C₀`; its parameter-free meaning will follow when that slot is
identified with the code set for the empty alphabet.
<!--zh-->
码集把一条公式存放在由其元数与骨架组成的键之下。为了用一个隶属原子表达此事，`FreeAt` 先绑定元数位置之取值的后继，再绑定这个后继与骨架组成的对，最后询问该对是否属于码集位置。因此，用元语言记号看，它具有 `∃[ z ] ∃[ y ]` 的形状：`z` 是后继元数，`y` 是键。各次移位只记录穿过一层或两层绑定之后仍要读取哪个原位置。此时公式本身只描述对 `C₀` 所给集合的隶属；待该位置被认作空字母表的码集后，它才得到无参性的含义。
<!--ja-->
符号集合では、論理式はアリティと骨格からなるキーのもとに格納されます。このことを一つの所属原子で表すため、`FreeAt` はまずアリティ位置の値の後続を束縛し、次にその後続と骨格との対を束縛して、最後にその対が符号集合位置に属するかを問います。したがってメタ言語の記法では `∃[ z ] ∃[ y ]` という形をもち、`z` が後続アリティ、`y` がキーです。各シフトは、一つまたは二つの束縛子の下から元のどの位置を参照するかを正確に記録します。この段階で論理式が述べるのは `C₀` に置かれた集合への所属だけです。その位置を空のアルファベットの符号集合と同定して初めて、無パラメータ性という意味が得られます。
<!--/-->

```agda
FreeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
FreeAt C₀ s a =
  ∃̇ ( sucAtL (suc a) zero
    ∧̇ ∃̇ ( prAtL zero (suc zero) (sh2 s)
         ∧̇ (var zero ∈̇ var (sh2 C₀)) ) )
```

<!--en-->
The first pair of readings works over an arbitrary environment `γ`. The
external equality `qa` identifies the value at the arity slot with the numeral
`# k`; it is a hypothesis of the semantic reading, not another clause inside
`FreeAt`. The skeleton and code-set slots remain arbitrary, so these lemmas
isolate the logical content of the two binders before the particular code set
is chosen.
<!--zh-->
第一对读式在任意环境 `γ` 上成立。外部等式 `qa` 把元数位置的取值认作数码 `# k`；它是语义读式的假设，并不是 `FreeAt` 内部的另一个子句。骨架位置与码集位置仍可任意取值，所以这些引理先单独说明两层绑定的逻辑内容，尚不指定所用的码集。
<!--ja-->
最初の一対の読みは、任意の環境 `γ` に対して成り立ちます。外側から与えられる等式 `qa` は、アリティ位置の値を数項 `# k` と同定します。これは意味論的な読みの仮定であり、`FreeAt` の内部にある別の節ではありません。骨格位置と符号集合位置はまだ任意なので、これらの補題は特定の符号集合を選ぶ前に、二つの束縛子の論理的内容だけを取り出しています。
<!--/-->

```agda

module _ {n : ℕ} (C₀ s a : Fin n) (γ : S ^ n) (k : ℕ)
         (qa : fst (lookup a γ) ≡ # k) where

```

<!--en-->
For the forward construction, suppose the intended key
`pr (# (suc k)) (fst (lookup s γ))` already belongs to the set at `C₀`.
This key supplies the two existential witnesses required by `FreeAt`: first the
numeral `# (suc k)`, then its pair with the skeleton. What remains is to verify
the successor and pairing descriptions of these witnesses; the final atom is
exactly the assumed membership.
<!--zh-->
正向构造从预期的键 `pr (# (suc k)) (fst (lookup s γ))` 已属于 `C₀` 位置上的集合这一假设出发。这个键恰好给出 `FreeAt` 所需的两个存在见证：先取数码 `# (suc k)`，再取它与骨架组成的对。余下工作只是核实这两个见证分别满足后继描述与配对描述；最末的原子正是起初假设的隶属。
<!--ja-->
順方向の構成では、意図したキー `pr (# (suc k)) (fst (lookup s γ))` がすでに `C₀` 位置の集合に属すると仮定します。このキーから `FreeAt` が要求する二つの存在証人が得られます。最初は数項 `# (suc k)`、次はそれと骨格との対です。残るのは、これらの証人がそれぞれ後続と対の記述を満たすことの確認だけであり、最後の原子は仮定した所属そのものです。
<!--/-->

```agda
  FreeAt-in : ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩
            → ⟨ γ ⊨ FreeAt C₀ s a ⟩
  FreeAt-in h = ∣ numAt , ( hsuc , ∣ keyAt , ( hpr , h ) ∣₁ ) ∣₁
    where
    numAt : S
```

<!--en-->
An existential witness for the internal language is an element of `S`, so its
underlying set must come with a proof of constructibility. The first witness
`numAt` has this proof because every numeral belongs to `L`. For the second
witness `keyAt`, the membership hypothesis places the key inside the
constructible set held at `C₀`; transitivity of `L` then makes the key itself
constructible. These proofs justify using the numeral and the key as bound
values, rather than adding any mathematical condition to `FreeAt`.
<!--zh-->
内部语言的存在见证是 `S` 的元素，因此其底层集合必须连同一份可构造性证明给出。第一个见证 `numAt` 的证明来自每个数码都属于 `L`。对于第二个见证 `keyAt`，隶属假设把该键放进 `C₀` 位置所持有的可构造集中，再由 `L` 的传递性得到键本身可构造。这两份证明只是使数码与键能够充当绑定取值，并未给 `FreeAt` 增添新的数学条件。
<!--ja-->
内部言語の存在証人は `S` の要素なので、その台となる集合には構成可能性の証明が伴わなければなりません。第一の証人 `numAt` には、すべての数項が `L` に属することからこの証明が得られます。第二の証人 `keyAt` については、所属の仮定がキーを `C₀` 位置の構成可能集合に入れ、`L` の推移性がキー自身の構成可能性を与えます。これらの証明は数項とキーを束縛値として使えるようにするものであり、`FreeAt` に新たな数学的条件を加えるものではありません。
<!--/-->

```agda
    numAt = # (suc k) , numL (suc k)
    keyAt : S
    keyAt = pr (# (suc k)) (fst (lookup s γ)) , isL-trans h (lookup C₀ γ .snd)
    hsuc : ⟨ (numAt ∷ γ) ⊨ sucAtL (suc a) zero ⟩
    hsuc = subst ⟨_⟩ (sym (sucAtL-adequate (suc a) zero (numAt ∷ γ)))
```

<!--en-->
The adequacy equations for the two auxiliary formulas now perform the promised
checks. For `hsuc`, the equality `qa` changes the value at the arity slot into
`# k`, and the successor of that numeral is `# (suc k)`. For `hpr`, adequacy of
`prAtL` reduces satisfaction to equality with the ordered pair specified by its
two component slots; `keyAt` was defined to be precisely that pair. Hence the
two semantic facts connect the chosen witnesses to the one membership atom.
<!--zh-->
两条辅助公式的充分性等式现在完成所需核实。对于 `hsuc`，等式 `qa` 把元数位置的取值换成 `# k`，而这个数码的后继就是 `# (suc k)`。对于 `hpr`，`prAtL` 的充分性把对该公式的满足化为「该取值等于两个分量位置所指定的有序对」；`keyAt` 的定义恰是这个对。因此，这两条语义事实把所选见证接到了最后那条隶属原子上。
<!--ja-->
二つの補助論理式に対する妥当性の等式が、必要な確認を行います。`hsuc` では、等式 `qa` によってアリティ位置の値を `# k` に置き換え、その数項の後続が `# (suc k)` であることを使います。`hpr` では、`prAtL` の妥当性により、充足関係は二つの成分位置が指定する順序対との等しさに帰着します。`keyAt` はまさにその対として定義されています。こうして二つの意味論的事実が、選んだ証人を最後の所属原子へ結び付けます。
<!--/-->

```agda
      (cong sucV (sym qa))
    hpr : ⟨ (keyAt ∷ numAt ∷ γ) ⊨ prAtL zero (suc zero) (sh2 s) ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate zero (suc zero) (sh2 s) (keyAt ∷ numAt ∷ γ))) refl

```

<!--en-->
The reverse reading extracts membership from a satisfaction of `FreeAt`.
Satisfaction of an existential formula provides its witness only under
propositional truncation, so the proof eliminates the outer truncation into the
desired membership proposition. A representative of the outer existential
contains the successor witness and a satisfaction of the inner existential;
the latter still has its own propositional truncation and will be eliminated in
turn.
<!--zh-->
反向读式从对 `FreeAt` 的满足关系中恢复隶属。存在公式的满足关系只在命题截断内给出见证，所以证明把外层截断消去到目标隶属命题中。外层存在量词的一个代表包含后继见证，以及对内层存在公式的满足关系；后者仍有自己的一层命题截断，随后还要再消去一次。
<!--ja-->
逆方向の読みは、`FreeAt` の充足関係から所属を取り出します。存在論理式の充足関係は証人を命題的切り詰めの内側でしか与えないため、証明は外側の切り詰めを目標の所属命題へ消去します。外側の存在量化の一つの代表は、後続の証人と内側の存在論理式の充足関係を含みます。後者にはそれ自身の命題的切り詰めが残っており、次にもう一度消去されます。
<!--/-->

```agda
  FreeAt-out : ⟨ γ ⊨ FreeAt C₀ s a ⟩
             → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩
  FreeAt-out = PT.rec (snd (pr (# (suc k)) (fst (lookup s γ))
                            ∈ fst (lookup C₀ γ))) atNum
    where
```

<!--en-->
Both truncation eliminations have the same codomain, so the proof names it
`Target`: the intended key belongs to the set at `C₀`. This type is a
proposition because membership in a set is proposition-valued. That fact is
the precise license required by each truncation eliminator; no choice of a
distinguished existential witness is being made.
<!--zh-->
两次截断消去具有同一个余域，所以证明把它命名为 `Target`：预期的键属于 `C₀` 位置上的集合。该类型是命题，因为集合的隶属关系取命题值。正是这一事实允许两次使用截断消去；证明并没有从存在见证中选出一个特定代表。
<!--ja-->
二回の切り詰め消去は同じ終域をもつので、証明はそれを `Target` と名付けます。その内容は、意図したキーが `C₀` 位置の集合に属することです。集合への所属は命題値なので、この型は命題です。この事実こそ各切り詰め消去を使うための根拠であり、存在証人から特定の代表を選んでいるわけではありません。
<!--/-->

```agda
    Target : Type (ℓ-suc ℓ)
    Target = ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩

```

<!--en-->
The branch `atKey` handles one representative of the inner existential. It is
given the outer witness `z` together with the equation saying that `z` is the
successor of the arity value, and it receives an inner witness `y` with two
facts: `y` satisfies the pairing formula and its underlying set belongs to the
set at `C₀`. The inner existential was truncated, but inside this elimination
branch its representative may be used to prove the proposition `Target`.
<!--zh-->
分支 `atKey` 处理内层存在量词的一个代表。它取得外层见证 `z` 以及「`z` 是元数取值之后继」的等式，还取得内层见证 `y` 和两条事实：`y` 满足配对公式，且其底层集合属于 `C₀` 位置上的集合。内层存在量词原本带有命题截断，但在这个消去分支内部，可以使用其代表来证明命题 `Target`。
<!--ja-->
分岐 `atKey` は、内側の存在量化の一つの代表を扱います。外側の証人 `z` と、`z` がアリティ値の後続であるという等式を受け取り、さらに内側の証人 `y` と二つの事実を受け取ります。その二つは、`y` が対の論理式を満たすことと、その台となる集合が `C₀` 位置の集合に属することです。内側の存在量化は命題的に切り詰められていますが、この消去分岐の内部では、その代表を用いて命題 `Target` を証明できます。
<!--/-->

```agda
    atKey : (z : S) → fst z ≡ sucV (fst (lookup a γ))
          → Σ[ y ∈ S ] ( ⟨ (y ∷ z ∷ γ) ⊨ prAtL zero (suc zero) (sh2 s) ⟩
                       × ⟨ fst y ∈ fst (lookup C₀ γ) ⟩ )
          → Target
    atKey z qz (y , (hp , hy)) =
```

<!--en-->
Adequacy of `prAtL` identifies the underlying set of `y` with the pair whose
first component is the underlying set of `z` and whose second component is the
skeleton. The equation for `z`, followed by `qa`, identifies that first
component with `# (suc k)`. Consequently `y` is the intended key. Transporting
the given membership of `y` along this equality proves membership of
`pr (# (suc k)) (fst (lookup s γ))`, which is `Target`.
<!--zh-->
`prAtL` 的充分性把 `y` 的底层集合认作一个对，其第一分量是 `z` 的底层集合，第二分量是骨架。先用关于 `z` 的等式，再接上 `qa`，便把第一分量认作 `# (suc k)`。因此，`y` 正是预期的键。沿此等式迁移已知的 `y` 的隶属，就得到 `pr (# (suc k)) (fst (lookup s γ))` 的隶属，也就是 `Target`。
<!--ja-->
`prAtL` の妥当性は、`y` の台となる集合を、第一成分が `z` の台となる集合、第二成分が骨格である対と同定します。`z` に関する等式に続けて `qa` を用いると、その第一成分は `# (suc k)` と同定されます。したがって `y` は意図したキーです。与えられた `y` の所属をこの等式に沿って移送すれば、`pr (# (suc k)) (fst (lookup s γ))` の所属、すなわち `Target` が得られます。
<!--/-->

```agda
      subst (λ u → ⟨ u ∈ fst (lookup C₀ γ) ⟩)
        (subst ⟨_⟩ (prAtL-adequate zero (suc zero) (sh2 s) (y ∷ z ∷ γ)) hp
         ∙ cong (λ u → pr u (fst (lookup s γ))) (qz ∙ cong sucV qa)) hy

```

<!--en-->
The outer elimination branch `atNum` receives a representative `z` together
with two pieces of evidence. The first says that `z` satisfies the successor
formula. The second, `hk`, is the still-truncated satisfaction of the inner
existential. Thus `atNum` has enough information to determine the intended
first component of the key, while postponing the inner witness until it can be
eliminated into `Target`.
<!--zh-->
外层消去分支 `atNum` 取得一个代表 `z` 和两份证据。第一份说 `z` 满足后继公式；第二份 `hk` 是仍带命题截断的内层存在公式之满足关系。因此，`atNum` 已能确定键的预期第一分量，同时把内层见证留到消去进 `Target` 时再使用。
<!--ja-->
外側の消去分岐 `atNum` は、一つの代表 `z` と二つの証拠を受け取ります。第一の証拠は `z` が後続の論理式を満たすことを述べ、第二の `hk` は、まだ命題的に切り詰められた内側の存在論理式の充足関係です。したがって `atNum` はキーの第一成分を定める情報をすでにもつ一方、内側の証人は `Target` へ消去できる段階まで切り詰めの中に保ちます。
<!--/-->

```agda
    atNum : Σ[ z ∈ S ] ( ⟨ (z ∷ γ) ⊨ sucAtL (suc a) zero ⟩
                       × ⟨ (z ∷ γ) ⊨ ∃̇ ( prAtL zero (suc zero) (sh2 s)
                                       ∧̇ (var zero ∈̇ var (sh2 C₀)) ) ⟩ )
          → Target
    atNum (z , (hs , hk)) = PT.rec (snd (pr (# (suc k)) (fst (lookup s γ))
```

<!--en-->
Adequacy of `sucAtL` decodes the first fact into the equality required by
`atKey`: `z` is the successor of the value at the arity slot. The proof then
eliminates `hk` into the proposition `Target` and applies `atKey` to each
representative. Together with the outer elimination already built into
`FreeAt-out`, this accounts for both existential layers while preserving the
propositional-truncation boundary.
<!--zh-->
`sucAtL` 的充分性把第一份证据解码成 `atKey` 所需的等式：`z` 是元数位置之取值的后继。随后，证明把 `hk` 消去到命题 `Target`，并对每个代表应用 `atKey`。连同 `FreeAt-out` 外层已有的消去，这恰好处理了两层存在量词，同时守住命题截断的边界。
<!--ja-->
`sucAtL` の妥当性は、第一の証拠を `atKey` が必要とする等式へ読み替えます。すなわち、`z` はアリティ位置の値の後続です。そこで証明は `hk` を命題 `Target` へ消去し、各代表に `atKey` を適用します。`FreeAt-out` にすでに組み込まれた外側の消去と合わせて、これで二層の存在量化が処理され、命題的切り詰めの境界も保たれます。
<!--/-->

```agda
                                         ∈ fst (lookup C₀ γ)))
      (atKey z (subst ⟨_⟩ (sucAtL-adequate (suc a) zero (z ∷ γ)) hs)) hk

```

<!--en-->
The next readings specialize the two previously arbitrary slots. The equality
`q₀` identifies the set at `C₀` with `AllCodes ∅ʟ`, whose elements are keys for
formulas over the empty alphabet, while `qa` again identifies the arity value
with `# k`. Under these hypotheses, the membership characterized by
`FreeAt-in` and `FreeAt-out` can be converted into an actual statement about
parameter-free formulas of arity `suc k`.
<!--zh-->
接下来的读式把此前任意的两个位置具体化。等式 `q₀` 把 `C₀` 位置上的集合认作 `AllCodes ∅ʟ`，其元素是空字母表上诸公式的键；`qa` 则再次把元数取值认作 `# k`。在这两项假设下，`FreeAt-in` 与 `FreeAt-out` 所刻画的隶属便能转换为关于元数为 `suc k` 的无参公式的实际陈述。
<!--ja-->
続く二つの読みでは、それまで任意だった二つの位置を具体化します。等式 `q₀` は `C₀` 位置の集合を `AllCodes ∅ʟ` と同定します。その要素は空のアルファベット上の論理式のキーです。また `qa` は、アリティ値を再び `# k` と同定します。これらの仮定のもとで、`FreeAt-in` と `FreeAt-out` が特徴付けた所属を、アリティ `suc k` の無パラメータ論理式についての具体的な主張へ変換できます。
<!--/-->

```agda
module _ {n : ℕ} (C₀ s a : Fin n) (γ : S ^ n) (k : ℕ)
         (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ))
         (qa : fst (lookup a γ) ≡ # k) where

```

<!--en-->
Starting from a satisfaction of `FreeAt`, `FreeAt-out` yields membership of the
key in the set currently held at `C₀`. Transport along `q₀` moves this
membership into `AllCodes ∅ʟ`. The earlier decoding lemma `freeCode-out` then
returns, under propositional truncation, a parameter-free formula `χ` of arity
`suc k` whose limit-stage code is the value in the skeleton slot. This is the
outward semantic reading of the one membership atom.
<!--zh-->
从对 `FreeAt` 的满足关系出发，`FreeAt-out` 得到该键属于 `C₀` 位置当前所持有的集合。沿 `q₀` 迁移后，这条隶属落入 `AllCodes ∅ʟ`。先前的解码引理 `freeCode-out` 随即在命题截断内给出一条元数为 `suc k` 的无参公式 `χ`，其极限层码正是骨架位置的取值。这就是那个隶属原子的向外语义读式。
<!--ja-->
`FreeAt` の充足関係から出発すると、`FreeAt-out` はキーが現在 `C₀` 位置に置かれた集合に属することを与えます。`q₀` に沿って移送すると、この所属は `AllCodes ∅ʟ` への所属になります。先に証明した復号補題 `freeCode-out` は、アリティ `suc k` の無パラメータ論理式 `χ` で、その極限段階の符号が骨格位置の値であるものを、命題的切り詰めのもとで返します。これが一つの所属原子の外向きの意味論的な読みです。
<!--/-->

```agda
  codeFree-out : ⟨ γ ⊨ FreeAt C₀ s a ⟩
               → ∥ Σ[ χ ∈ Formula (⊥* {ℓ}) (suc k) ]
                     (fst (lookup s γ) ≡ fst (limitCode χ)) ∥₁
  codeFree-out h = freeCode-out (suc k) (fst (lookup s γ))
    (subst (λ u → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ u ⟩) q₀
```

<!--en-->
The arity is `suc k` because a name for a definable subset uses one variable
for the candidate element in addition to its `k` parameter positions. The
formula witness in `codeFree-out` remains propositionally truncated. Although
`FreeAt-out` may eliminate its bound witnesses locally because membership is a
proposition, `freeCode-out` introduces a truncated formula witness at the final
decoding step. The result therefore asserts that such a formula exists without
selecting one.
<!--zh-->
这里的元数是 `suc k`，因为定义子集所用的名字公式除了 `k` 个参数位置之外，还要留一个变元位置给候选元素。`codeFree-out` 中的公式见证仍处于命题截断内。`FreeAt-out` 可以把自己的绑定见证局部消去到隶属命题中，但最后的解码步骤 `freeCode-out` 又给出一个带命题截断的公式见证。因此，结论只断言这样的公式存在，并不从中选出一条公式。
<!--ja-->
ここでアリティが `suc k` なのは、定義可能な部分集合の名前に使う論理式が、`k` 個のパラメータ位置に加えて、候補要素のための変数位置を一つ必要とするからです。`codeFree-out` が与える論理式の証人は、命題的に切り詰められたままです。`FreeAt-out` は所属が命題であるため自身の束縛された証人を局所的に消去できますが、最後の復号段階で `freeCode-out` が切り詰められた論理式の証人を与えます。したがって結論は、そのような論理式の存在だけを述べ、特定の一つを選びません。
<!--/-->

```agda
      (FreeAt-out C₀ s a γ k qa h))

```

<!--en-->
Conversely, `codeFree-in` begins with a specific parameter-free formula `χ` of
arity `suc k` and an equality identifying its limit-stage code with the
skeleton slot. The lemma `freeCode-in` places the corresponding key in
`AllCodes ∅ʟ`; transport along the code equality and then along the reverse of
`q₀` moves that membership to the actual skeleton and code-set slots.
`FreeAt-in` packages the resulting membership with the two existential
witnesses. This direction needs no truncated formula witness because `χ` is
part of the input.
<!--zh-->
反过来，`codeFree-in` 从一条给定的元数为 `suc k` 的无参公式 `χ` 出发，并假设它的极限层码与骨架位置的取值相等。引理 `freeCode-in` 先把相应的键放入 `AllCodes ∅ʟ`；再沿码等式以及 `q₀` 的反向迁移，便把这条隶属移到实际的骨架位置与码集位置。最后，`FreeAt-in` 用两个存在见证包装所得隶属。这个方向无须产生带命题截断的公式见证，因为 `χ` 本来就是输入数据。
<!--ja-->
逆に `codeFree-in` は、アリティ `suc k` の具体的な無パラメータ論理式 `χ` と、その極限段階の符号を骨格位置の値と同定する等式から始めます。補題 `freeCode-in` は対応するキーを `AllCodes ∅ʟ` に入れます。次に符号の等式と `q₀` の逆向きに沿って移送すると、その所属は実際の骨格位置と符号集合位置に移ります。最後に `FreeAt-in` が、得られた所属を二つの存在証人とともにまとめます。この方向では `χ` 自身が入力として与えられているため、命題的に切り詰められた論理式の証人を作る必要はありません。
<!--/-->

```agda
  codeFree-in : (χ : Formula (⊥* {ℓ}) (suc k))
              → fst (lookup s γ) ≡ fst (limitCode χ) → ⟨ γ ⊨ FreeAt C₀ s a ⟩
  codeFree-in χ q = FreeAt-in C₀ s a γ k qa
    (subst (λ u → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ u ⟩) (sym q₀)
      (subst (λ u → ⟨ pr (# (suc k)) u ∈ fst (AllCodes ∅ʟ) ⟩) (sym q)
```

<!--en-->
Together, `codeFree-out` and `codeFree-in` give the promised reading of
`FreeAt` once the arity and empty-alphabet code-set slots are identified. The
outward direction says, under propositional truncation, that the skeleton is
the code of a parameter-free formula with `suc k` variables. The inward
direction starts with a specified formula and needs no such truncation. This
finishes the recognition of a name's formula; the next question is how its
finite parameter environment records the number `k`.
<!--zh-->
一旦元数位置与空字母表码集位置得到确定，`codeFree-out` 与 `codeFree-in` 便共同给出 `FreeAt` 所承诺的读法。向外方向在命题截断内断言：骨架是一条具有 `suc k` 个变元的无参公式之码。向内方向从一条给定公式出发，因而不需要这样的截断。名字公式的识别至此完成；下一个问题是，它的有穷参数环境怎样记录数 `k`。
<!--ja-->
アリティのスロットと空のアルファベットの符号集合のスロットを同定すれば、`codeFree-out` と `codeFree-in` がそろって `FreeAt` の意図した読みを与えます。外向きには、骨格が `suc k` 個の変数をもつ無パラメータ論理式の符号であることが、命題的切り詰めのもとで得られます。内向きには具体的な論理式が初めから与えられているので、そのような切り詰めは要りません。これで名前の論理式を認識できました。次の問いは、その有限なパラメータ環境が数 `k` をどのように記録するかです。
<!--/-->

```agda
        (freeCode-in (suc k) χ)))

```

<!--en-->
## How long a sequence is
<!--zh-->
## 一个序列有多长
<!--ja-->
## 列の長さを読む
<!--/-->

<!--en-->
We first characterize arbitrary membership in the set-coded graph. If
`pr x y` belongs to `env g`, where `g` is indexed by `Fin k`, then merely there
is an index `i` for which `x ≡ # (toℕ i)` and `y ≡ g i`. The result remains
under propositional truncation because membership in a hierarchy set records
only the mere existence of a generating entry. Thus `memberOf` exposes every
possible index without choosing one.
<!--zh-->
先刻画集合编码图中的任意隶属。若 `g` 以 `Fin k` 为索引，并且`pr x y` 属于 `env g`，那么仅仅存在一个索引 `i`，使`x ≡ # (toℕ i)` 且 `y ≡ g i`。结果仍处于命题截断内，因为层级集合中的隶属只记录某个生成条目的仅仅存在。因此，`memberOf` 揭示所有可能的索引，却不从中选择一个。
<!--ja-->
まず、集合として符号化されたグラフへの任意の所属を特徴づけます。`g` が `Fin k` で添字づけられ、`pr x y` が `env g` に属するなら、`x ≡ # (toℕ i)` かつ `y ≡ g i` となる添字 `i` が単に存在します。階層の集合への所属が記録するのは、生成元となる項目の単なる存在だけなので、結果は命題的切り詰めのもとに留まります。したがって `memberOf` は可能な添字を明らかにしますが、その一つを選び出しはしません。
<!--/-->

```agda
private
  memberOf : (k : ℕ) (g : Fin k → V ℓ) (x y : V ℓ) → ⟨ pr x y ∈ env g ⟩
           → ∥ Σ[ i ∈ Fin k ] ((x ≡ # (toℕ i)) × (y ≡ g i)) ∥₁
  memberOf k g x y = PT.map
    (λ { (li , e) → lower li
```

<!--en-->
The membership witness contains an equality between a stored graph entry and
the queried pair. Injectivity of the ordered-pair constructor splits that one
equality into equalities of the two components. The stored entry is written
first in the witness, so both component paths are reversed to obtain the
orientation required by `memberOf`: from `x` and `y` to the numeral key and
the value supplied by `g`.
<!--zh-->
隶属见证携带一条等式，把图中存放的条目与所查询的有序对联系起来。有序对构造子的单射性把这一条等式拆成两个分量各自的等式。见证中的等式先写存入的条目，故两个分量的路径都要反向，才能得到 `memberOf` 所需的方向：从 `x`、`y` 分别指向数码键与 `g` 给出的取值。
<!--ja-->
所属の証人は、グラフに格納された項目と問い合わせた順序対との等式を含みます。順序対の構成子の単射性により、この一つの等式は二つの成分の等式に分かれます。証人では格納された項目が先に書かれているため、両方の成分のパスを逆向きにして、`memberOf` が必要とする向きにします。すなわち、`x` と `y` から、それぞれ数項の鍵と `g` の与える値へ向かう等式です。
<!--/-->

```agda
       , (sym (pr-inj e .fst) , sym (pr-inj e .snd)) })

```

<!--en-->
Conversely, every prescribed index supplies an entry. For `i : Fin k`, the
pair `pr (# (toℕ i)) (g i)` belongs to `env g`; the lifted index is the
membership witness and the entry equation is reflexivity. Hence `memberOf`
and `entryOf` give the two directions needed to recognize the horizontal
coordinates of this finite graph.
<!--zh-->
反过来，每个给定索引都产生一个条目。对 `i : Fin k`，有序对`pr (# (toℕ i)) (g i)` 属于 `env g`；提升后的索引就是隶属见证，而条目等式由自反性给出。因此，`memberOf` 与 `entryOf` 提供识别这个有穷图之横坐标所需的两个方向。
<!--ja-->
逆に、指定された各添字は一つの項目を与えます。`i : Fin k` に対して、順序対 `pr (# (toℕ i)) (g i)` は `env g` に属します。持ち上げられた添字が所属の証人となり、項目の等式は反射性です。こうして `memberOf` と `entryOf`は、この有限グラフの第一成分を認識するために必要な二つの向きを与えます。
<!--/-->

```agda
  entryOf : (k : ℕ) (g : Fin k → V ℓ) (i : Fin k)
          → ⟨ pr (# (toℕ i)) (g i) ∈ env g ⟩
  entryOf k g i = ∣ lift i , refl ∣₁

```

<!--en-->
The forward domain inclusion begins with the mere existence of a model element
`y` such that `pr x (fst y)` lies in the graph. Its goal is the membership
proposition `x ∈ # k`, so the outer propositional truncation may be eliminated
into that goal. After fixing one representative `y`, it remains to recover an
index from the graph membership and prove that its numeral belongs to `# k`.
<!--zh-->
定义域的正向包含从如下仅仅存在出发：存在一个模型元素 `y`，使`pr x (fst y)` 位于图中。目标是隶属命题 `x ∈ # k`，所以外层命题截断可以消去到这个目标中。固定其中一个代表 `y` 后，只须从图的隶属中恢复一个索引，并证明该索引的数码属于 `# k`。
<!--ja-->
定義域の順向きの包含は、`pr x (fst y)` がグラフに入るようなモデルの元`y` が単に存在することから始まります。目標は所属命題 `x ∈ # k` なので、外側の命題的切り詰めをこの目標へ消去できます。代表 `y` を一つ固定した後は、グラフへの所属から添字を復元し、その数項が `# k` に属することを示せば十分です。
<!--/-->

```agda
  dom-into : (k : ℕ) (g : Fin k → V ℓ) (x : V ℓ)
           → ⟨ ∃[ y ∶ S ] pr x (fst y) ∈ env g ⟩ → ⟨ x ∈ # k ⟩
  dom-into k g x = PT.rec (snd (x ∈ # k)) atEntry
    where
    atIndex : (u : V ℓ) → Σ[ i ∈ Fin k ] ((x ≡ # (toℕ i)) × (u ≡ g i))
```

<!--en-->
For an explicit index `i`, only the first component equality matters to the
domain. Since `toℕ i < k`, the numeral lemma `#mono` places
`# (toℕ i)` in `# k`; transport along `x ≡ # (toℕ i)` then places `x` there.
The second component equality identifies the graph value but is irrelevant to
this inclusion. The helper `atEntry` fixes the value `y` before eliminating
the remaining truncated index information.
<!--zh-->
对一个明确的索引 `i`，定义域只用到第一分量的等式。由于`toℕ i < k`，数码引理 `#mono` 给出 `# (toℕ i)` 属于 `# k`；再沿`x ≡ # (toℕ i)` 迁移，便得到 `x` 属于 `# k`。第二分量的等式识别图中的取值，却与这一包含无关。辅助函数 `atEntry` 先固定取值 `y`，然后才消去余下的截断索引信息。
<!--ja-->
具体的な添字 `i` に対して、定義域が必要とするのは第一成分の等式だけです。`toℕ i < k` なので、数項に関する補題 `#mono` は `# (toℕ i)` を `# k` に入れます。さらに `x ≡ # (toℕ i)` に沿って輸送すれば、`x` もそこに属します。第二成分の等式はグラフの値を同定しますが、この包含には不要です。補助関数`atEntry` は値 `y` を固定してから、残る切り詰められた添字の情報を消去します。
<!--/-->

```agda
            → ⟨ x ∈ # k ⟩
    atIndex u (i , (qx , _)) = subst (λ v → ⟨ v ∈ # k ⟩) (sym qx)
      (#mono (toℕ i) k (toℕ<n i))
    atEntry : Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ env g ⟩ → ⟨ x ∈ # k ⟩
    atEntry (y , p) = PT.rec (snd (x ∈ # k)) (atIndex (fst y))
```

<!--en-->
Applying `memberOf` supplies precisely that index information, still under
propositional truncation. Because `x ∈ # k` is a proposition, `PT.rec` may feed
each representative to `atIndex`. This closes the forward inclusion without
extracting an index as ordinary data.
<!--zh-->
对图的隶属应用 `memberOf`，恰好得到所需的索引信息，但它仍在命题截断内。由于 `x ∈ # k` 是命题，`PT.rec` 可以把每个代表交给 `atIndex`。正向包含由此完成，整个过程没有把某个索引提取成普通数据。
<!--ja-->
グラフへの所属に `memberOf` を適用すると、必要な添字の情報がちょうど得られますが、それはまだ命題的切り詰めのもとにあります。`x ∈ # k` は命題なので、`PT.rec` は各代表を `atIndex` に渡せます。これで添字を通常のデータとして取り出すことなく、順向きの包含が閉じます。
<!--/-->

```agda
      (memberOf k g x (fst y) p)

```

<!--en-->
For the reverse inclusion, suppose `x ∈ # k`. Elimination for von Neumann
numerals says, under propositional truncation, that `x ≡ # m` for some natural
number `m < k`. Such an `m` determines an index in `Fin k`. The conclusion is
itself a propositionally truncated existence of a graph value, so `PT.map` can
transform each numeral witness without choosing one. The hypothesis `cg` will
supply the constructibility certificate needed to present that value as an
element of the model.
<!--zh-->
反向包含设 `x ∈ # k`。冯·诺伊曼数码的消去表明，在命题截断内，存在一个自然数 `m < k`，使 `x ≡ # m`。这样的 `m` 决定 `Fin k` 中的一个索引。结论本身也是「图中有取值」的命题截断存在，所以 `PT.map` 可以逐一变换数码见证，而无须选择其中一个。假设 `cg` 随后提供把该取值呈现为模型元素所需的可构造性证明。
<!--ja-->
逆向きの包含では `x ∈ # k` と仮定します。von Neumann 数項の消去により、ある自然数 `m < k` について `x ≡ # m` であることが、命題的切り詰めのもとで得られます。そのような `m` は `Fin k` の添字を定めます。結論もグラフの値の存在を命題的に切り詰めたものなので、`PT.map` はいずれかを選ぶことなく、各数項の証人を変換できます。仮定 `cg` は、その値をモデルの元として提示するために必要な構成可能性の証明を供給します。
<!--/-->

```agda
  dom-from : (k : ℕ) (g : Fin k → V ℓ) → ((i : Fin k) → ⟨ isL (g i) ⟩)
           → (x : V ℓ) → ⟨ x ∈ # k ⟩ → ⟨ ∃[ y ∶ S ] pr x (fst y) ∈ env g ⟩
  dom-from k g cg x h = PT.map atNumeral (∈#-elim k x h)
    where
    atNumeral : Σ[ m ∈ ℕ ] ((m < k) × (x ≡ # m))
```

<!--en-->
For a representative `m < k`, let `i` be the corresponding finite index. The
witness for the existential is the model element `(g i , cg i)`, namely the
value at that index together with its constructibility proof. The graph fact
comes from `entryOf`: the pair with canonical first component
`# (toℕ i)` is an entry. Transporting that first component to `x` gives the
required membership of `pr x (g i)` in the graph.
<!--zh-->
对一个代表 `m < k`，令 `i` 为相应的有穷索引。存在量词的见证是模型元素`(g i , cg i)`，即该索引处的取值及其可构造性证明。图中的事实来自`entryOf`：以标准第一分量 `# (toℕ i)` 为键的有序对是一个条目。把这个第一分量迁移为 `x`，便得到所需的 `pr x (g i)` 属于图。
<!--ja-->
代表 `m < k` に対し、`i` を対応する有限添字とします。存在量化の証人はモデルの元 `(g i , cg i)`、すなわちその添字での値と構成可能性の証明です。グラフについての事実は `entryOf` から得られます。標準的な第一成分`# (toℕ i)` をもつ対が一つの項目だからです。この第一成分を `x` へ輸送すれば、`pr x (g i)` がグラフに属するという必要な所属が得られます。
<!--/-->

```agda
              → Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ env g ⟩
    atNumeral (m , (p , qx)) = (g i , cg i)
      , subst (λ u → ⟨ pr u (g i) ∈ env g ⟩) (sym qi) (entryOf k g i)
      where
      i : Fin k
```

<!--en-->
The conversion `fromℕ' k m p` turns the bound `p : m < k` into the index `i`.
Its round-trip law `toFromId'` proves `toℕ i ≡ m`. Composing `x ≡ # m` with
the numeral image of the symmetric round-trip equality gives
`qi : x ≡ # (toℕ i)`, exactly the path used to move the canonical entry to the
queried first component. This completes the reverse domain inclusion.
<!--zh-->
转换 `fromℕ' k m p` 把界限证明 `p : m < k` 化为索引 `i`。其往返律`toFromId'` 证明 `toℕ i ≡ m`。把 `x ≡ # m` 与这条往返等式之反向在数码下的像复合起来，便得到 `qi : x ≡ # (toℕ i)`；这正是把标准条目搬到所查询第一分量所需的路径。定义域的反向包含至此完成。
<!--ja-->
変換 `fromℕ' k m p` は境界の証明 `p : m < k` から添字 `i` を作ります。その往復則 `toFromId'` は `toℕ i ≡ m` を証明します。`x ≡ # m` と、往復の等式を逆向きにして数項へ写したパスとを合成すると、`qi : x ≡ # (toℕ i)` が得られます。これは標準的な項目を問い合わせた第一成分へ移すためのパスそのものです。これで定義域の逆向きの包含も完成します。
<!--/-->

```agda
      i = fromℕ' k m p
      qi : x ≡ # (toℕ i)
      qi = qx ∙ cong #_ (sym (toFromId' k m p))

```

<!--en-->
We can now compare these two set-level inclusions with the object-language
domain formula. Fix an environment `γ`, a family `g : Fin k → V ℓ`, and an
equation `qe` identifying the underlying set in slot `e` with `env g`; slot
`d` remains the proposed domain. Each `cg i` certifies that `g i` is an element
of the constructible model, exactly what the reverse inclusion needs when it
builds an existential witness. In this context the next two lemmas read and
fill `domAt e d`.
<!--zh-->
现在可以把这两个集合层面的包含与对象语言的定义域公式对应起来。固定环境`γ`、族 `g : Fin k → V ℓ`，以及等式 `qe`；后者把 `e` 位置的底集认作`env g`，而 `d` 位置仍是候选定义域。每个 `cg i` 都证明 `g i` 是可构造模型的元素，这正是反向包含构造存在见证时所需的条件。在这个语境中，接下来的两个引理分别读出与填充 `domAt e d`。
<!--ja-->
これで、二つの集合レベルの包含を対象言語の定義域の論理式と対応させられます。環境 `γ`、族 `g : Fin k → V ℓ`、そしてスロット `e` の台集合を `env g` と同定する等式 `qe` を固定し、スロット `d` は定義域の候補として残します。各 `cg i` は `g i` が構成可能モデルの元であることを証明します。これは逆向きの包含が存在の証人を作るときに、まさに必要となる条件です。この文脈で、次の二つの補題が `domAt e d` を読み出し、また充填します。
<!--/-->

```agda
module _ {n : ℕ} (e d : Fin n) (γ : S ^ n)
         (k : ℕ) (g : Fin k → V ℓ) (cg : (i : Fin k) → ⟨ isL (g i) ⟩)
         (qe : fst (lookup e γ) ≡ env g) where

```

<!--en-->
Suppose `γ` satisfies `domAt e d`. To prove that the underlying set in slot
`d` is `# k`, `domAt-numeral` applies extensionality inside `L` to the two
model elements `lookup d γ` and `(# k , numL k)`, then projects their equality
to the underlying sets. It therefore suffices to prove, for every constructible
test element `x`, that membership in the proposed domain and membership in the
numeral are the same proposition. The forward implication begins by reading
domain membership through `domAt-in`.
<!--zh-->
设 `γ` 满足 `domAt e d`。为了证明 `d` 位置的底集就是 `# k`，`domAt-numeral` 对模型元素 `lookup d γ` 与 `(# k , numL k)` 应用 `L` 内部的外延性，再把所得等式投影到底集。因此，只须对每个可构造的测试元素 `x` 证明：属于候选定义域与属于该数码是同一个命题。正向蕴含先用 `domAt-in` 读取定义域隶属。
<!--ja-->
`γ` が `domAt e d` を充足すると仮定します。スロット `d` の台集合が`# k` であることを示すため、`domAt-numeral` はモデルの元 `lookup d γ` と`(# k , numL k)` に `L` 内部の外延性を適用し、得られた等式を台集合へ射影します。したがって、構成可能な各試験要素 `x` について、定義域の候補への所属と数項への所属が同じ命題であることを示せば十分です。順向きの含意は、まず `domAt-in` によって定義域への所属を読み出します。
<!--/-->

```agda
  domAt-numeral : ⟨ γ ⊨ domAt e d ⟩ → fst (lookup d γ) ≡ # k
  domAt-numeral h = cong fst (extensionalL {a = lookup d γ} {b = # k , numL k} pt)
    where
    fwd : (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩ → ⟨ fst x ∈ # k ⟩
    fwd x hx = dom-into k g (fst x)
```

<!--en-->
In the forward implication, `domAt-in` turns membership in slot `d` into the
mere existence of a value paired with `x` in the set at slot `e`. Transport
along `qe` places that entry in `env g`, and `dom-into` yields `x ∈ # k`.
Conversely, `dom-from` turns `x ∈ # k` into the mere existence of an entry in
`env g`. Since membership in the proposed domain is a proposition, that
truncation may be eliminated; the local function `put` handles each displayed
entry.
<!--zh-->
在正向蕴含中，`domAt-in` 把 `d` 位置中的隶属化为如下仅仅存在：某个取值与`x` 配成的对位于 `e` 位置的集合中。沿 `qe` 迁移后，该条目落入 `env g`，`dom-into` 随即给出 `x ∈ # k`。反过来，`dom-from` 把 `x ∈ # k` 化为`env g` 中某个条目的仅仅存在。由于属于候选定义域是命题，可以消去这一截断；局部函数 `put` 处理每个呈现出来的条目。
<!--ja-->
順向きの含意では、`domAt-in` がスロット `d` への所属を、`x` と対をなしてスロット `e` の集合に入る値の単なる存在へ変えます。`qe` に沿って輸送するとその項目は `env g` に入り、`dom-into` が `x ∈ # k` を与えます。逆に、`dom-from` は `x ∈ # k` を `env g` の項目の単なる存在へ変えます。定義域の候補への所属は命題なので、この切り詰めを消去できます。局所関数 `put` が、提示された各項目を処理します。
<!--/-->

```agda
      (subst (λ u → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ u ⟩) qe
        (domAt-in e d γ h x hx))
    bwd : (x : S) → ⟨ fst x ∈ # k ⟩ → ⟨ fst x ∈ fst (lookup d γ) ⟩
    bwd x hx = PT.rec (snd (fst x ∈ fst (lookup d γ))) put (dom-from k g cg (fst x) hx)
      where
```

<!--en-->
For one displayed entry, `put` transports its membership back along `qe` to
the graph stored at slot `e`; `domAt-out` then gives membership in slot `d`.
Thus the two implications form, by `⇔toPath`, a path between the two
membership propositions at every `x`. Extensionality assembles those pointwise
paths into the equality of the proposed domain with `# k`. The truncated graph
witness is used only to prove membership, so no value is selected from it.
<!--zh-->
对一个呈现出来的条目，`put` 先沿 `qe` 的反向把其隶属搬回 `e` 位置所存的图，再由 `domAt-out` 得到它的第一分量属于 `d` 位置。于是，两条蕴含经`⇔toPath` 在每个 `x` 处形成两条隶属命题之间的路径；外延性把这些逐点路径组装成候选定义域与 `# k` 的相等。截断的图见证只用于证明隶属，并未从中选择任何取值。
<!--ja-->
提示された一つの項目について、`put` はその所属を `qe` の逆向きに沿ってスロット `e` に格納されたグラフへ戻し、`domAt-out` によって第一成分のスロット `d` への所属を得ます。こうして二つの含意は `⇔toPath` により、各 `x` で二つの所属命題の間のパスになります。外延性はそれらの点ごとのパスを、定義域の候補と `# k` との等式へ組み立てます。切り詰められたグラフの証人は所属を証明するためだけに用いられ、そこから値を選び出すことはありません。
<!--/-->

```agda
      put : Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ env g ⟩ → ⟨ fst x ∈ fst (lookup d γ) ⟩
      put (y , p) = domAt-out e d γ h x y
        (subst (λ u → ⟨ pr (fst x) (fst y) ∈ u ⟩) (sym qe) p)
    pt : (x : S) → (fst x ∈ fst (lookup d γ)) ≡ (fst x ∈ # k)
    pt x = ⇔toPath (fwd x) (bwd x)
```

<!--en-->
The converse starts from an equality saying that the set in slot `d` really is
`# k`. To establish `domAt e d`, `domAt-intro` asks pointwise for the two
implications that define a domain: mere existence of a value in the graph
implies membership in `d`, and membership in `d` implies the mere existence of
a value. The equations `qe` and `qd` reduce these to `dom-into` and `dom-from`,
respectively. Thus filling the formula uses the same two set-level inclusions
as reading it, in the opposite direction.
<!--zh-->
反向从一条等式开始，它断言 `d` 位置的集合确实是 `# k`。为了证明`domAt e d`，`domAt-intro` 要求对每个元素给出定义域的两条蕴含：图中仅仅存在一个取值蕴含该元素属于 `d`，而属于 `d` 又蕴含图中仅仅存在一个取值。等式 `qe` 与 `qd` 分别把这两项化为 `dom-into` 与 `dom-from`。因此，填充公式使用的仍是读出公式时那两个集合层面的包含，只是方向相反。
<!--ja-->
逆向きは、スロット `d` の集合が実際に `# k` であるという等式から始まります。`domAt e d` を示すために、`domAt-intro` は定義域を規定する二つの含意を各要素について要求します。グラフに値が単に存在すれば `d` に属し、`d` に属すればグラフに値が単に存在する、という二つです。等式 `qe` と `qd`によって、これらはそれぞれ `dom-into` と `dom-from` に帰着します。したがって論理式の充填には、読み出しで用いた二つの集合レベルの包含を逆向きにして、そのまま用います。
<!--/-->

```agda

  domAt-fill : fst (lookup d γ) ≡ # k → ⟨ γ ⊨ domAt e d ⟩
  domAt-fill qd = domAt-intro e d γ step
    where
    step : (x : S)
         → (⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup e γ) ⟩
```

<!--en-->
To fill the domain formula, it remains to prove its two pointwise implications.
For the first, suppose some value is paired with `fst x` in the graph stored at
slot `e`. Transport along `qe` puts this entry in `env g`, where `dom-into`
shows that `fst x` belongs to the numeral `# k`. Transporting back along `qd`
then places it in the proposed domain at slot `d`.
<!--zh-->
为了填充定义域公式，只须证明逐点的两个蕴含。先设某个取值与 `fst x` 配成的对属于位置 `e` 所存的图。沿 `qe` 搬运后，这个条目属于 `env g`，于是 `dom-into` 证明 `fst x` 属于数码 `# k`。再沿 `qd` 的反向搬运，便得到它属于位置 `d` 所存的候选定义域。
<!--ja-->
定義域の論理式を充足させるには、各点で二つの含意を示せば十分です。まず、ある値と `fst x` の対がスロット `e` のグラフに属するとします。`qe` に沿って輸送すると、この項目は `env g` に入り、`dom-into` によって `fst x` が数項 `# k` に属することが分かります。さらに `qd` を逆向きに使って輸送すれば、スロット `d` の定義域候補への所属が得られます。
<!--/-->

```agda
            → ⟨ fst x ∈ fst (lookup d γ) ⟩)
         × (⟨ fst x ∈ fst (lookup d γ) ⟩
            → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup e γ) ⟩)
    step x =
        (λ hy → subst (λ u → ⟨ fst x ∈ u ⟩) (sym qd) (dom-into k g (fst x)
```

<!--en-->
The reverse implication follows the same path in reverse. Membership in slot
`d` is transported by `qd` to membership in `# k`; `dom-from` then supplies,
under propositional truncation, a value paired with `fst x` in `env g`; and
transport along the inverse of `qe` returns that entry to slot `e`. These two
directions complete `domAt-fill` without choosing a value from the finite graph.
<!--zh-->
反向蕴含沿同一路径倒行。先用 `qd` 把位置 `d` 中的隶属搬到 `# k` 中；`dom-from` 随后在命题截断内给出一个取值，使它与 `fst x` 配成的对属于 `env g`；最后沿 `qe` 的反向把该条目送回位置 `e`。两个方向由此完成 `domAt-fill`，过程中没有从有穷图中选出一个取值。
<!--ja-->
逆向きの含意は、同じ道筋を反対にたどります。スロット `d` への所属を `qd` によって `# k` への所属へ移し、`dom-from` から、`fst x` と対をなして `env g` に入る値の単なる存在を得ます。最後に `qe` の逆向きに沿って、その項目をスロット `e` へ戻します。これで `domAt-fill` の二方向がそろい、有限グラフから特定の値を選び出す必要はありません。
<!--/-->

```agda
          (subst (λ u → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ u ⟩) qe hy)))
      , (λ hx → subst (λ u → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ u ⟩) (sym qe)
          (dom-from k g cg (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qd hx)))
```

<!--en-->
## What the satisfaction graph assigns
<!--zh-->
## 满足关系的图所指派的取值
<!--ja-->
## 充足関係グラフが割り当てる値
<!--/-->

<!--en-->
We now ask what the satisfaction graph assigns at a genuine formula key. Fix
an ambient environment `γ`: slot `B` supplies the carrier, while `x` and `y`
supply the proposed key and value. The abbreviation `Bs = lookup B γ` keeps
the proof uniform in all three slots. Formulas considered below therefore have
constants indexed by the members of the underlying set `fst Bs`.
<!--zh-->
现在考察满足关系图在真实公式键处指派什么。固定周围环境 `γ`：位置 `B` 给出载体，`x` 与 `y` 则给出候选键和候选取值。缩写 `Bs = lookup B γ` 使随后证明对这三个位置保持统一。因此，以下公式的常元由底集 `fst Bs` 的成员索引。
<!--ja-->
次に、充足関係グラフが実際の論理式の鍵で何を割り当てるかを調べます。周囲の環境 `γ` を固定し、スロット `B` から台を、`x` と `y` から鍵と値の候補を受け取ります。略記 `Bs = lookup B γ` により、以下の証明はこの三つのスロットについて一様に述べられます。ここで扱う論理式の定数は、台集合 `fst Bs` の要素によって添字づけられます。
<!--/-->

```agda
module _ {n : ℕ} (B x y : Fin n) (γ : S ^ n) where
  private
    Bs : S
    Bs = lookup B γ

```

<!--en-->
The graph formula packages a satisfaction recursion through fourteen bound
slots. For a model-language formula `φ`, `fr φ` supplies those slots with the
carrier `Bs`, its canonical satisfaction table, the subformula-key slot, the
environment tower, and the ten constructor-tag numerals, followed by the
ambient environment `γ`. Each component is the canonical one already
constructed for this carrier and formula.
<!--zh-->
图公式通过十四个受界位置封装满足关系递归。对模型语言公式 `φ`，`fr φ` 在这些位置依次放入载体 `Bs`、它的典范满足关系表、由子公式键组成的槽、环境塔以及十个构造子标签的数码，随后接上周围环境 `γ`。每个分量都是此前已经为该载体与公式构造好的典范对象。
<!--ja-->
グラフの論理式は、十四個の束縛されたスロットを通して充足関係の再帰をまとめます。モデル言語の論理式 `φ` に対し、`fr φ` はそれらのスロットへ、台 `Bs`、その正準な充足関係表、子論理式の鍵からなるスロット、環境の塔、そして十個の構成子タグの数項を順に置き、その後ろに周囲の環境 `γ` を続けます。どの成分も、この台と論理式についてすでに構成された正準な対象です。
<!--/-->

```agda
    fr : ∀ {m} (φ : Formula S m) → S ^ (14 + n)
    fr φ = ev numν (Tower.tower Bs) (slot Bs φ) (satTable Bs φ) Bs γ

```

<!--en-->
The ten numerals do not index the code domain. They label the ten constructor
clauses of the table specification, from zero through nine. `tgs φ` records
that every designated tag slot in `fr φ` contains the numeral matching its
constructor. This alignment lets the packaged table formula select the right
clause for each syntactic form.
<!--zh-->
这十个数码并不为码域编制索引，而是标记表规格中从零到九的十条构造子子句。`tgs φ` 记录 `fr φ` 中每个指定的标签位置都含有与其构造子相应的数码。凭借这份对齐，打包后的表公式才能为每种语法形状选中正确子句。
<!--ja-->
この十個の数項は符号領域の添字ではなく、表の仕様にある零から九までの十個の構成子節を表すタグです。`tgs φ` は、`fr φ` の各タグ用スロットが対応する構成子の数項をもつことを記録します。この対応により、まとめられた表の論理式は各構文の形に適切な節を選べます。
<!--/-->

```agda
    tgs : ∀ {m} (φ : Formula S m) → Tags (fr φ) NN
    tgs φ = numTags (Tower.tower Bs) (slot Bs φ) (satTable Bs φ) Bs γ

```

<!--en-->
The table also needs the correct family of environments for every arity.
`htow φ` applies the established tower theorem to the components of `fr φ`:
the value in the tower slot is `Tower.tower Bs`, the carrier slot is `Bs`, and
the zero-tag slot contains the required numeral. Thus `towerAt` holds in the
extended environment, with no new tower argument needed here.
<!--zh-->
满足关系表还需要为每个元数配备正确的环境族。`htow φ` 把既有的塔定理应用于 `fr φ` 的各分量：塔位置的取值是 `Tower.tower Bs`，载体位置是 `Bs`，零号标签位置则含有所需数码。因此，`towerAt` 在扩展环境中成立，此处无须重新证明关于塔的论证。
<!--ja-->
充足関係表には、各アリティに対応する正しい環境の族も必要です。`htow φ` は、すでに得られている塔の定理を `fr φ` の各成分に適用します。塔のスロットには `Tower.tower Bs`、台のスロットには `Bs`、零番のタグ用スロットには必要な数項が入っています。したがって拡張された環境で `towerAt` が成り立ち、ここで塔について新たな議論を行う必要はありません。
<!--/-->

```agda
    htow : ∀ {m} (φ : Formula S m) → ⟨ fr φ ⊨ towerAt Ei Bi (NN f0) ⟩
    htow φ = TowerHolds.holds Ei Bi (NN f0) (fr φ) Bs refl refl refl

```

<!--en-->
The domain of the canonical table is exactly the slot of formula keys. One
direction starts with a table entry and uses `inSlot` to put its key in
`slot Bs φ`; because the entry is obtained under propositional truncation,
elimination is into the membership proposition. The other direction uses
`total` to give, merely, a table value for every key in the slot.
`domAt-intro` combines these implications into `hdom φ`.
<!--zh-->
典范表的定义域恰是公式键所成的槽。一个方向从表条目出发，用 `inSlot` 证明其键属于 `slot Bs φ`；由于条目是在命题截断下取得的，这次消去落入隶属命题。另一个方向用 `total` 证明槽中的每个键都仅仅存在一个表取值。`domAt-intro` 把这两个蕴含组合成 `hdom φ`。
<!--ja-->
正準な表の定義域は、論理式の鍵からなるスロットと一致します。一方では表の項目から始め、`inSlot` によってその鍵を `slot Bs φ` に入れます。項目は命題的切り詰めのもとで得られるので、その消去先は所属命題です。他方では `total` を使い、スロット内の各鍵に表の値が単に存在することを示します。`domAt-intro` がこの二つの含意を `hdom φ` にまとめます。
<!--/-->

```agda
    hdom : ∀ {m} (φ : Formula S m) → ⟨ fr φ ⊨ domAt Ti Ci ⟩
    hdom φ = domAt-intro Ti Ci (fr φ)
      (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot Bs φ)))
                 (λ { (w , hw) → inSlot Bs φ (fst z) (fst w) hw }) h)
           , (λ h → total Bs φ (fst z) h))
```

<!--en-->
The forward reading can now be stated precisely. Let `ψ` be a formula whose
constants are members of `fst Bs`. If slot `x` contains its genuine key
`keyS Bs ψ`, and slot `y` contains the satisfaction set of the translated
model-language formula `mapFo (asConst Bs) ψ`, then `satGraphAt B x y` holds.
The value is a set of satisfying environments, rather than a single truth
value. `graphAt-value` proves the claim by supplying the canonical recursion
witness to `graphAt-in`.
<!--zh-->
现在可以准确陈述正向读式。设 `ψ` 的常元取自 `fst Bs` 的成员。若位置 `x` 含有它的真实键 `keyS Bs ψ`，位置 `y` 含有翻译后的模型语言公式 `mapFo (asConst Bs) ψ` 的满足集合，那么 `satGraphAt B x y` 成立。这里的取值是满足该公式的环境所成的集合，并非单个真值。`graphAt-value` 向 `graphAt-in` 提供典范递归见证，从而证明这一结论。
<!--ja-->
これで順方向の読みを正確に述べられます。`ψ` を、定数が `fst Bs` の要素である論理式とします。スロット `x` が実際の鍵 `keyS Bs ψ` をもち、スロット `y` がモデル言語へ移した論理式 `mapFo (asConst Bs) ψ` の充足集合をもつなら、`satGraphAt B x y` が成り立ちます。この値は論理式を充足する環境の集合であり、一つの真理値ではありません。`graphAt-value` は正準な再帰の証人を `graphAt-in` に与えて、この主張を示します。
<!--/-->

```agda

  graphAt-value : ∀ {m} (ψ : Formula ⟪ fst Bs ⟫ m)
                → fst (lookup x γ) ≡ fst (keyS Bs ψ)
                → fst (lookup y γ) ≡ fst (Sat Bs (mapFo (asConst Bs) ψ))
                → ⟨ γ ⊨ satGraphAt B x y ⟩
  graphAt-value {m} ψ qx qy = graphAt-in B x y γ
```

<!--en-->
The existential witness is assembled from the five canonical components in
the order expected by `GraphWitAt`: the numeral assignment `numν`, the tower,
the slot, the satisfaction table, and the carrier. It is then wrapped in
propositional truncation, matching the existential semantics of the graph
formula. What remains is to certify that these chosen components satisfy the
carrier, tag, tower, closure, domain, entry, and table requirements.
<!--zh-->
存在见证按 `GraphWitAt` 所需的次序由五个典范分量装配：数码指派 `numν`、塔、槽、满足关系表与载体。随后把整份见证包入命题截断，以配合图公式中存在量词的语义。余下任务是证明这些选定分量满足载体、标签、塔、闭包、定义域、条目与表规格的要求。
<!--ja-->
存在の証人は `GraphWitAt` が要求する順に、五つの正準な成分から組み立てられます。数項の割り当て `numν`、塔、スロット、充足関係表、そして台です。証人全体は、グラフの論理式における存在量化の意味に合わせて命題的切り詰めで包まれます。残るのは、選んだ成分が台、タグ、塔、閉包、定義域、項目、表の仕様を満たすことの確認です。
<!--/-->

```agda
    ∣ numν
    , (Tower.tower Bs
    , (slot Bs φ
    , (satTable Bs φ
    , (Bs
```

<!--en-->
The carrier equation is reflexivity. The next three certificates say that the
ten tag slots contain the intended numerals, that the environment slot is the
tower over `Bs`, and that `slot Bs φ` is closed under the formula constructors
with immediate subformulas. This last property is what allows the recursive
table clauses at a compound formula key to consult entries at its immediate
subformula keys.
<!--zh-->
载体等式由自反性给出。接下来的三份证明分别断言：十个标签位置含有预定数码，环境位置确实是 `Bs` 上的塔，并且 `slot Bs φ` 对带有直接子公式的构造子闭合。最后一项保证递归表在复合公式键处施用子句时，能够查阅直接子公式键处的表条目。
<!--ja-->
台についての等式は反射性です。続く三つの証明は、十個のタグ用スロットが所定の数項をもち、環境のスロットが `Bs` 上の塔であり、`slot Bs φ` が直下の子論理式をもつ構成子について閉じていることを示します。最後の性質により、再帰的な表の節は、複合論理式の鍵で直下の子論理式の鍵にある項目を参照できます。
<!--/-->

```agda
    , (refl
    , (tgs φ
    , (htow φ
    , (slotClosed Bs φ (Tower.tower Bs ∷ numν f0 ∷ numν f1 ∷ numν f2 ∷ numν f3
         ∷ numν f4 ∷ numν f5 ∷ numν f6 ∷ numν f7 ∷ numν f8 ∷ numν f9 ∷ γ)
```

<!--en-->
The final requirements identify the table's domain, its selected entry, and
its clause specification. The previously proved `hdom φ` gives the domain
formula. For the entry, `keyBridge Bs ψ` relates the key of the carrier-language
formula to that of `φ`, while `qx` and `qy` transport the canonical entry to
slots `x` and `y`. Finally, `SlotHolds.holds` proves that the canonical table
satisfies `tableAt` from the same carrier, tags, tower, slot, and table. The
assembled witness therefore establishes the graph formula.
<!--zh-->
最后三项要求分别确定表的定义域、选定条目与子句规格。先前证明的 `hdom φ` 给出定义域公式。对表条目，`keyBridge Bs ψ` 关联载体语言公式与 `φ` 的键，而 `qx`、`qy` 把典范条目搬到位置 `x`、`y` 所存的键和值上。最后，`SlotHolds.holds` 从同一载体、标签、塔、槽与表证明该典范表满足 `tableAt`。装配好的见证因而证明图公式成立。
<!--ja-->
最後の三つの条件は、表の定義域、選んだ項目、そして構成子節の仕様を確定します。すでに示した `hdom φ` が定義域の論理式を与えます。表の項目については、`keyBridge Bs ψ` が台の言語の論理式と `φ` の鍵を結び、`qx` と `qy` が正準な項目をスロット `x` と `y` の鍵と値へ輸送します。最後に `SlotHolds.holds` が、同じ台、タグ、塔、スロット、表から、正準な表が `tableAt` を充足することを示します。これで組み立てた証人がグラフの論理式を確立します。
<!--/-->

```agda
    , (hdom φ
    , (subst2 (λ u v → ⟨ pr u v ∈ fst (satTable Bs φ) ⟩)
         (sym (qx ∙ keyBridge Bs ψ)) (sym qy) (entry-in Bs φ)
    , SlotHolds.holds Bs Ti Bi Ci Ei NN (fr φ) refl (tgs φ) (htow φ) ψ refl refl)))))))))) ∣₁
    where
```

<!--en-->
Here `φ` is the model-language version of `ψ`. A constant of `ψ` is a member
of the underlying carrier, and `asConst Bs` equips that member with the
constructibility evidence needed to regard it as an element of `S`; `mapFo`
applies this constant map throughout the formula. The separate `keyBridge`
used above ensures that direct coding before this translation and internal
coding after it produce the same underlying key.
<!--zh-->
这里的 `φ` 是 `ψ` 在模型语言中的版本。`ψ` 的一个常元是底层载体的成员；`asConst Bs` 为它配上作为 `S` 中元素所需的可构造性证明，`mapFo` 再把这个常元映射施于整条公式。上文另行使用的 `keyBridge` 保证：翻译前直接编码与翻译后在模型内部编码所得的底层键相同。
<!--ja-->
ここで `φ` は `ψ` をモデル言語へ移したものです。`ψ` の定数は台集合の要素であり、`asConst Bs` はそれに、`S` の要素とみなすために必要な構成可能性の証明を添えます。`mapFo` はこの定数写像を論理式全体に適用します。上で別に用いた `keyBridge` により、翻訳前に直接符号化した鍵と、翻訳後にモデル内部で符号化した鍵の台集合が一致します。
<!--/-->

```agda
    φ : Formula S m
    φ = mapFo (asConst Bs) ψ

```

<!--en-->
For the reverse reading, suppose `satGraphAt B x y` holds and slot `x` is the
genuine key of `ψ`. `graphAt-out` exposes the fourteen existential components
only under propositional truncation. The desired conclusion is an equality in
the cumulative hierarchy `V`, and `setIsSet` says that this equality type is a
proposition. Hence `PT.rec` may inspect each displayed graph witness locally
without choosing one globally.
<!--zh-->
反向读式设 `satGraphAt B x y` 成立，且位置 `x` 是 `ψ` 的真实键。`graphAt-out` 只能在命题截断内给出十四个存在分量。所求结论是累积层级 `V` 中的一条相等，而 `setIsSet` 说明这种相等所成的类型是命题。因此，`PT.rec` 可以在局部逐一考察呈现出的图见证，而不从中作全局选择。
<!--ja-->
逆方向では、`satGraphAt B x y` が成り立ち、スロット `x` が `ψ` の実際の鍵であると仮定します。`graphAt-out` が十四個の存在成分を与えるのは、命題的切り詰めのもとだけです。求める結論は累積階層 `V` における等式であり、`setIsSet` によってその等式型は命題です。したがって `PT.rec` は、グラフの証人を大域的に選ぶことなく、提示された各証人を局所的に調べられます。
<!--/-->

```agda
  graphAt-only : ∀ {m} (ψ : Formula ⟪ fst Bs ⟫ m)
               → fst (lookup x γ) ≡ fst (keyS Bs ψ)
               → ⟨ γ ⊨ satGraphAt B x y ⟩
               → fst (lookup y γ) ≡ fst (Sat Bs (mapFo (asConst Bs) ψ))
  graphAt-only {m} ψ qx h = PT.rec (setIsSet _ _) read (graphAt-out B x y γ h)
```

<!--en-->
Unpacking one graph witness gives a proposed table `T`, a code domain `C`, an
environment tower `E`, a carrier `b`, and all their certificates. The domain
`C` need not be the canonical slot; what matters is that it is subcode-closed,
that `T` satisfies the packaged table clauses, and that the genuine key lies
in `C`. The last fact follows by applying `domAt-out` to the displayed table
entry `ha`. With that membership and the same entry, `SatSoundC.pinned` applies
to `ψ` and forces its recorded value to be the canonical satisfaction set.
<!--zh-->
拆开一个图见证，可得候选表 `T`、码域 `C`、环境塔 `E`、载体 `b` 及其全部证明。这里的 `C` 不必是典范槽；关键在于它对子码闭合，`T` 满足打包后的表子句，而且真实键属于 `C`。最后一项由表条目 `ha` 经 `domAt-out` 得到。把这份键隶属与同一个表条目交给 `SatSoundC.pinned`，便可将 `ψ` 在表中记录的取值确定为典范满足集合。
<!--ja-->
一つのグラフの証人をほどくと、表の候補 `T`、符号領域 `C`、環境の塔 `E`、台 `b`、およびそれらの証明が得られます。ここで `C` が正準なスロットである必要はありません。必要なのは、`C` が子符号について閉じ、`T` がまとめられた表の節を充足し、実際の鍵が `C` に属することです。最後の所属は、提示された表の項目 `ha` に `domAt-out` を適用して得られます。この鍵の所属と同じ表の項目を `SatSoundC.pinned` に渡すと、`ψ` について表に記録された値が正準な充足集合に定まります。
<!--/-->

```agda
    where
    read : GraphWitAt B x y γ → fst (lookup y γ) ≡ fst (Sat Bs (mapFo (asConst Bs) ψ))
    read (ν , (E , (C , (T , (b , (eb , (tg , (hE , (hc , (hd , (ha , h12))))))))))) =
      SatSoundC.pinned Ti Bi Ci Ei NN (ev ν E C T b γ) Bs eb tg hE hc h12
        ψ (subst (λ u → ⟨ u ∈ fst C ⟩) qx
```

<!--en-->
Both premises for pinning are read at the ambient key in slot `x`.
Transporting by `qx` turns the domain membership obtained from `hd` and `ha`
into membership of `keyS Bs ψ` in `C`, and turns `ha` itself into an entry of
`T` at that key and the value in slot `y`. The pinned theorem then returns
exactly the required equality: at a genuine formula key, any value admitted by
the graph is the satisfaction set of the translated formula.
<!--zh-->
钉定定理所需的两个前提起初都在周围环境的位置 `x` 处读取。沿 `qx` 搬运，一方面把由 `hd` 与 `ha` 得到的定义域隶属化为 `keyS Bs ψ` 属于 `C`，另一方面把 `ha` 本身化为 `T` 在该键与位置 `y` 所存取值处的条目。钉定定理随即交回所需相等：在真实公式键处，图所容许的任何取值都等于翻译后公式的满足集合。
<!--ja-->
固定の定理に必要な二つの前提は、初めは周囲の環境のスロット `x` で読まれます。`qx` に沿って輸送すると、`hd` と `ha` から得た定義域への所属は `keyS Bs ψ` が `C` に属するという所属になり、`ha` 自身は、その鍵とスロット `y` の値における `T` の項目になります。そこで固定の定理が必要な等式を返します。実際の論理式の鍵では、グラフが許すどの値も、翻訳された論理式の充足集合に一致します。
<!--/-->

```agda
             (domAt-out Ti Ci (ev ν E C T b γ) hd (lookup x γ) (lookup y γ) ha))
        (lookup y γ)
        (subst (λ u → ⟨ pr u (fst (lookup y γ)) ∈ fst T ⟩) qx ha)
```

<!--en-->
## A name, described at slots
<!--zh-->
## 名字，描述在诸位上
<!--ja-->
## 名前をスロット上で記述する
<!--/-->

<!--en-->
The denotation body tests one candidate `z` at a time. Its first conjunct,
`z ∈ B`, restricts the set being described to the carrier. It then binds an
environment `c` and requires `c` to be the coded environment obtained by
putting `z` in front of the parameter environment `e`. At that point `c` and
`z` precede the ambient assignment, so the reference to `e` is shifted through
two binders.
<!--zh-->
指称公式体一次检验一个候选元素 `z`。首个合取项 `z ∈ B` 把所描述的集合限制在载体之内。随后公式体绑定环境 `c`，并要求 `c` 是把 `z` 添到参数环境 `e` 前端所得的编码环境。此时 `c` 与 `z` 都位于周遭赋值之前，故对 `e` 的引用须穿过两层绑定。
<!--ja-->
表示を定める本体は、候補 `z` を一つずつ調べます。最初の連言 `z ∈ B` は、記述される集合を台の内部に制限します。次に環境 `c` を束縛し、`c` がパラメータ環境 `e` の先頭に `z` を加えて得られる符号化環境であることを要求します。この時点では `c` と `z` が周囲の割り当ての前に置かれているので、`e` への参照は二つの束縛子を越えて移されます。
<!--/-->

```agda
DenoteBody : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S (suc n)
DenoteBody B C s e =
  (var zero ∈̇ var (suc B))
  ∧̇ ∃̇ ( consAtL zero (suc zero) (sh2 e)
       ∧̇ ∃̇ ( domAt (suc zero) zero
```

<!--en-->
The remaining three witnesses determine how the skeleton is evaluated. First
`k` is required to be the domain of the extended environment `c`. Next `key`
must belong to the code set in slot `C` and equal the pair of `k` with the
skeleton code `s`. Finally `v` is a value admitted by the satisfaction graph
for the carrier `B` at that key, and the last membership says `c ∈ v`. When
`C` is the carrier's genuine code set, these clauses say that the extended
environment satisfies the skeleton rather than merely consulting the graph at
an arbitrary key.
<!--zh-->
其余三个见证决定如何解释骨架。首先要求 `k` 是扩展环境 `c` 的定义域；接着要求 `key` 属于位置 `C` 中的码集，并等于 `k` 与骨架码 `s` 组成的对；最后，`v` 是满足关系图在载体 `B` 与该键处容许的取值，末尾的隶属断言则是 `c ∈ v`。当 `C` 填入载体的真实码集时，这些条件表达的是扩展环境满足骨架，而非仅在任意键处查询图。
<!--ja-->
残る三つの証人は、骨格をどのように解釈するかを定めます。まず `k` が拡張環境 `c` の定義域であることを要求します。次に `key` はスロット `C` の符号集合に属し、`k` と骨格の符号 `s` の対に等しくなければなりません。最後に `v` は、台 `B` の充足関係グラフがその鍵で許す値であり、末尾の所属は `c ∈ v` を述べます。`C` に台の実際の符号集合が入ると、これらの条件は、任意の鍵でグラフを参照するだけではなく、拡張環境が骨格を充足することを表します。
<!--/-->

```agda
            ∧̇ ∃̇ ( (var zero ∈̇ var (sh4 C))
                 ∧̇ ( prAtL zero (suc zero) (sh4 s)
                   ∧̇ ∃̇ ( satGraphAt (sh5 B) (suc zero) zero
                        ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) ) ) ) )

```

<!--en-->
A meta-level name consists of an arity, a parameter-free formula, and a
parameter vector. `NameAt` represents these by an arity slot `a`, a skeleton
code slot `s`, and an environment slot `e`; its denotation slot `d` records the
set derived from those data. The first conjunct checks that the pair formed
from the successor of `a` and `s` belongs to the empty-alphabet code set. The
successor is essential: a name with `a` parameters needs one further variable
for the candidate member. The next conjunct requires `a` to be a member of the
model's natural numbers.
<!--zh-->
元语言名字由元数、无参公式与参数向量组成。`NameAt` 分别以元数位置 `a`、骨架码位置 `s` 与环境位置 `e` 表示这三项，并以指称位置 `d` 记录由它们导出的集合。第一个合取项检查由 `a` 的后继与 `s` 组成的对是否属于空字母表码集。这里的后继不可省略：具有 `a` 个参数的名字还需要一个变元来放置候选成员。下一个合取项要求 `a` 属于模型的自然数之集。
<!--ja-->
メタ言語の名前は、アリティ、無パラメータ論理式、パラメータベクトルからなります。`NameAt` はそれらをアリティのスロット `a`、骨格の符号のスロット `s`、環境のスロット `e` で表し、表示のスロット `d` にはそのデータから導かれる集合を記録します。最初の連言は、`a` の後続と `s` から作った対が空のアルファベットの符号集合に属することを確かめます。この後続は欠かせません。`a` 個のパラメータをもつ名前には、候補となる要素を置く変数がもう一つ必要だからです。次の連言は、`a` がモデルの自然数の集合に属することを要求します。
<!--/-->

```agda
NameAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
       → Formula S n
NameAt B C C₀ s a e d =
  FreeAt C₀ s a
  ∧̇ ( (var a ∈̇ con ωʟ)
```

<!--en-->
The third conjunct makes `e` an environment with exact domain `a` and values
in `B`; in particular, it ties the parameter vector to the arity recorded in
the preceding slot. The last conjunct characterizes `d` extensionally. For
every candidate, membership in `d` is equivalent to satisfaction of
`DenoteBody`, whose first conjunct already restricts the candidate to `B`.
Thus `d` is derived from the three pieces of a name rather than stored as an
additional piece of the meta-level name.
<!--zh-->
第三个合取项要求 `e` 是定义域恰为 `a`、取值落在 `B` 中的环境，从而把参数向量与前一位置记录的元数联系起来。最后一个合取项以外延方式刻画 `d`：对每个候选元素，属于 `d` 当且仅当它满足 `DenoteBody`，而该公式体的首项已经把候选元素限制在 `B` 中。因此，`d` 是由名字的三项数据导出的，并非元语言名字额外存储的分量。
<!--ja-->
第三の連言は、`e` が定義域をちょうど `a` とし、`B` に値をとる環境であることを要求します。これにより、パラメータベクトルが一つ前のスロットに記録されたアリティと結び付きます。最後の連言は `d` を外延的に特徴づけます。各候補について、`d` への所属は `DenoteBody` の充足と同値であり、その本体の最初の連言がすでに候補を `B` の中に制限しています。したがって `d` は名前の三つのデータから導かれるもので、メタ言語の名前に追加で保存される成分ではありません。
<!--/-->

```agda
    ∧̇ ( envOverAt e a B ∧̇ extAt d (DenoteBody B C s e) ) )

```

<!--en-->
`DenoteOf z` is the meta-level payload corresponding to the four existential
layers of `DenoteBody`. It records an extended environment `c`, its proposed
domain `k`, a formula key, and a graph value `v`, together with all the
conditions connecting them. Keeping this data in one dependent tuple exposes
the witnesses needed to assemble the object-language formula while retaining
the dependencies of each later condition on the earlier choices.
<!--zh-->
`DenoteOf z` 是与 `DenoteBody` 四层存在量词相应的元语言载荷。它记录扩展环境 `c`、其候选定义域 `k`、一个公式键和图取值 `v`，并带上联系这些对象的全部条件。把这些数据放进一个依值元组，既显露出装配对象语言公式所需的见证，也保留了后续条件对先前选择的依赖。
<!--ja-->
`DenoteOf z` は、`DenoteBody` の四層の存在量化に対応するメタ言語の中身です。拡張環境 `c`、その定義域の候補 `k`、論理式の鍵、グラフの値 `v` と、それらを結ぶすべての条件を記録します。これらを一つの依存対にまとめることで、対象言語の論理式を組み立てるのに必要な証人を明示しながら、後の条件が先に選んだ値に依存することも保たれます。
<!--/-->

```agda
module _ {n : ℕ} (B C s e : Fin n) (γ : S ^ n) where
  DenoteOf : (z : S) → Type (ℓ-suc ℓ)
  DenoteOf z = Σ[ c ∈ S ] Σ[ k ∈ S ] Σ[ key ∈ S ] Σ[ v ∈ S ]
    ( ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
    × ( ⟨ (k ∷ c ∷ z ∷ γ) ⊨ domAt (suc zero) zero ⟩
```

<!--en-->
The payload follows the semantic chain exactly. The first two satisfaction
proofs say that `c` extends the old environment and that `k` is its domain.
Membership of `key` in `C` certifies that the following graph lookup is made
at a genuine code when `C` is instantiated by `AllCodes B`. The explicit
equation then identifies that key with the pair of `k` and `s`. The last two
proofs say that `v` is the graph value at this key and that `c` belongs to
`v`. Here `v` is a set of satisfying environments, not a Boolean truth value.
<!--zh-->
这份载荷严格沿着语义链展开。前两份满足证明分别断言 `c` 扩展旧环境，以及 `k` 是它的定义域。当 `C` 实例化为 `AllCodes B` 时，`key` 对 `C` 的隶属保证随后是在真实公式码处查询图。接着的显式等式把该键确定为 `k` 与 `s` 组成的对。末两份证明则断言 `v` 是图在该键处的取值，并且 `c` 属于 `v`。这里的 `v` 是满足该公式的环境之集，并非布尔真值。
<!--ja-->
この中身は意味の連鎖をそのままたどります。最初の二つの充足の証明は、`c` がもとの環境を拡張することと、`k` がその定義域であることを述べます。`C` を `AllCodes B` で具体化すると、`key` が `C` に属するという条件により、続くグラフの参照が実際の論理式の符号で行われることが保証されます。次の明示的な等式は、その鍵を `k` と `s` の対と同一視します。最後の二つの証明は、`v` がこの鍵でのグラフの値であり、`c` が `v` に属することを述べます。ここで `v` は充足する環境の集合であって、ブール値の真理値ではありません。
<!--/-->

```agda
      × ( ⟨ fst key ∈ fst (lookup C γ) ⟩
        × ( (fst key ≡ pr (fst k) (fst (lookup s γ)))
          × ( ⟨ (v ∷ key ∷ k ∷ c ∷ z ∷ γ) ⊨ satGraphAt (sh5 B) (suc zero) zero ⟩
            × ⟨ fst c ∈ fst v ⟩ ) ) ) ) )

```

<!--en-->
`DenoteBody-in` turns this explicit payload into satisfaction of the body.
The carrier membership remains the outer conjunct, while the witnesses
`c`, `k`, `key`, and `v` are introduced in the same order as the four
existential binders. Most conditions are already stated as satisfaction
proofs. The exception is the equation defining `key`: the pairing formula's
adequacy path converts that set-theoretic equation into satisfaction of
`prAtL`.
<!--zh-->
`DenoteBody-in` 把这份显式载荷变成对公式体的满足。载体隶属保留为最外层合取项，而见证 `c`、`k`、`key` 与 `v` 按四层存在绑定的同一次序引入。多数条件本来就以满足证明陈述。例外是定义 `key` 的等式：配对公式的充分性路径把这条集合论等式转换为对 `prAtL` 的满足。
<!--ja-->
`DenoteBody-in` は、この明示的な中身を本体の充足へ変えます。台への所属は外側の連言として残り、証人 `c`、`k`、`key`、`v` は四つの存在量化子と同じ順序で導入されます。ほとんどの条件は、初めから充足の証明として述べられています。例外は `key` を定める等式です。対の論理式の妥当性を表すパスが、この集合論的な等式を `prAtL` の充足へ変換します。
<!--/-->

```agda
  DenoteBody-in : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf z
                → ⟨ (z ∷ γ) ⊨ DenoteBody B C s e ⟩
  DenoteBody-in z hz (c , (k , (key , (v , (hc , (hk , (hi , (hp , (hg , hm)))))))))
    = hz , ∣ c , (hc , ∣ k , (hk , ∣ key , (hi
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc zero) (sh4 s) (key ∷ k ∷ c ∷ z ∷ γ))) hp
```

<!--en-->
Each object-language existential is interpreted by propositional truncation,
so the construction wraps every one of the four witnesses before closing the
proof. The final line closes these four layers from the graph value out to the
extended environment. Consequently the resulting satisfaction records that
suitable data exist, while the untruncated witnesses remain available only in
the input `DenoteOf z` used to build it.
<!--zh-->
对象语言的每个存在量词都以命题截断解释，因此构造在结束证明前把四个见证逐层包入截断。最后一行从图取值向外直至扩展环境，依次闭合这四层。所得满足因而只记录适当数据存在；未截断的见证只保留在用来构造它的输入 `DenoteOf z` 中。
<!--ja-->
対象言語の各存在量化子は命題的切り詰めによって解釈されるので、この構成は証明を閉じる前に四つの証人を一層ずつ切り詰めます。最後の行は、グラフの値から拡張環境まで、この四層を内側から順に閉じます。したがって得られる充足が記録するのは適切なデータの存在であり、切り詰められていない証人は、構成に用いた入力 `DenoteOf z` の側にだけ残ります。
<!--/-->

```agda
      , ∣ v , (hg , hm) ∣₁ )) ∣₁) ∣₁) ∣₁

```

<!--en-->
`DenoteBody-out` preserves the same boundary in the reverse direction. The
outer carrier membership is available directly because it lies outside every
existential. The four witnesses, however, are exposed only within nested
propositional truncations. Each use of truncation elimination targets
`∥ DenoteOf z ∥₁`, again a proposition, so the proof may transform each local
choice of witnesses without selecting a tuple globally.
<!--zh-->
`DenoteBody-out` 在反向读取时保留同一边界。载体隶属位于所有存在量词之外，因此可以直接取得；四个见证则只能在嵌套的命题截断中显露。每次截断消去的目标都是 `∥ DenoteOf z ∥₁`，仍为一个命题，故证明可以变换每一份局部见证，却不会从中全局选出一个元组。
<!--ja-->
`DenoteBody-out` は、逆向きに読むときにも同じ境界を保ちます。台への所属はすべての存在量化子の外側にあるので、直接取り出せます。しかし四つの証人は、入れ子になった命題的切り詰めの内側でしか現れません。切り詰めの消去先は毎回 `∥ DenoteOf z ∥₁` であり、これも命題です。そのため、各局所的な証人の組を変換することはできますが、一つの組を大域的に選ぶことはありません。
<!--/-->

```agda
  DenoteBody-out : (z : S) → ⟨ (z ∷ γ) ⊨ DenoteBody B C s e ⟩
                 → ⟨ fst z ∈ fst (lookup B γ) ⟩ × ∥ DenoteOf z ∥₁
  DenoteBody-out z (hz , hc) = hz , PT.rec squash₁
    (λ { (c , (hc , hk)) → PT.rec squash₁
      (λ { (k , (hk , hkey)) → PT.rec squash₁
```

<!--en-->
At the key layer, the body supplies satisfaction of the pairing formula,
whereas `DenoteOf` requires the decoded equation
`fst key ≡ pr (fst k) (fst (lookup s γ))`. Reading the pairing formula's
adequacy path in the forward direction produces precisely this equation. The
innermost map then retains the graph and membership proofs with the witness
`v`, and the surrounding eliminations rebuild the whole payload under one
propositional truncation.
<!--zh-->
在键这一层，公式体给出对配对公式的满足，而 `DenoteOf` 要求解码后的等式 `fst key ≡ pr (fst k) (fst (lookup s γ))`。沿配对公式的充分性路径正向读取，恰好得到这条等式。最内层的映射随后把图证明与隶属证明连同见证 `v` 一并保留，外围的消去再于一层命题截断之下重建整份载荷。
<!--ja-->
鍵の層では、本体は対の論理式の充足を与えますが、`DenoteOf` が要求するのは、復号された等式 `fst key ≡ pr (fst k) (fst (lookup s γ))` です。対の論理式の妥当性を表すパスを順方向に読むと、ちょうどこの等式が得られます。最も内側の写像は、証人 `v` とともにグラフの証明と所属の証明を保ち、外側の消去が中身全体を一つの命題的切り詰めの下で組み立て直します。
<!--/-->

```agda
        (λ { (key , (hi , (hp , hv))) → PT.map
          (λ { (v , (hg , hm)) → c , (k , (key , (v , (hc , (hk , (hi
            , ( subst ⟨_⟩
                  (prAtL-adequate zero (suc zero) (sh4 s) (key ∷ k ∷ c ∷ z ∷ γ)) hp
              , (hg , hm) ))))))) }) hv }) hkey }) hk }) hc
```

<!--en-->
`NameAt-in` takes five inputs. The first three establish the fixed conjuncts:
the skeleton is parameter-free at the stated arity, the arity lies in the
model's natural numbers, and the parameter graph is an environment over the
carrier. The remaining two inputs give the two pointwise directions needed to
characterize the denotation. From `z ∈ d`, the first returns `z ∈ B` together
with an explicit `DenoteOf z`; conversely, the second turns `z ∈ B` and an
explicit `DenoteOf z` into `z ∈ d`.
<!--zh-->
`NameAt-in` 接受五份输入。前三份建立固定的合取项：骨架在给定元数处为无参公式，元数属于模型的自然数之集，参数图是载体上的环境。余下两份输入给出刻画指称所需的逐点双向蕴含。第一向从 `z ∈ d` 得到 `z ∈ B` 与一份显式的 `DenoteOf z`；反向则把 `z ∈ B` 和一份显式的 `DenoteOf z` 变成 `z ∈ d`。
<!--ja-->
`NameAt-in` は五つの入力を取ります。最初の三つは固定された連言を示します。すなわち、骨格が指定されたアリティで無パラメータであること、アリティがモデルの自然数の集合に属すること、パラメータのグラフが台の上の環境であることです。残る二つは、表示を特徴づけるための点ごとの二方向を与えます。一方は `z ∈ d` から `z ∈ B` と明示的な `DenoteOf z` を返し、他方は `z ∈ B` と明示的な `DenoteOf z` から `z ∈ d` を導きます。
<!--/-->

```agda

module _ {n : ℕ} (B C C₀ s a e d : Fin n) (γ : S ^ n) where
  NameAt-in : ⟨ γ ⊨ FreeAt C₀ s a ⟩
            → ⟨ fst (lookup a γ) ∈ ω ⟩
            → ⟨ γ ⊨ envOverAt e a B ⟩
            → ((z : S) → ⟨ fst z ∈ fst (lookup d γ) ⟩
```

<!--en-->
Both directions are stated separately for every candidate because `extAt`
expresses equality of sets by pointwise membership. They deliberately use an
untruncated `DenoteOf z`: this lemma is an introduction rule, so its caller
supplies the concrete data from which satisfaction of the body can be built.
Recovering such data from an arbitrary satisfaction of `NameAt` is a separate
adequacy argument, and its result in the following chapter remains under
propositional truncation.
<!--zh-->
两个方向都对每个候选元素分别陈述，因为 `extAt` 通过逐点隶属表达集合相等。它们有意使用未截断的 `DenoteOf z`：本引理是一条引入规则，调用方要提供可用来构造公式体满足的具体数据。从 `NameAt` 的任意满足中恢复这些数据属于另一项充分性论证；下一章给出的恢复结果仍保留在命题截断之下。
<!--ja-->
二つの方向は、どちらも候補ごとに述べられます。`extAt` が集合の等しさを点ごとの所属で表すからです。ここでは意図的に、切り詰められていない `DenoteOf z` を使います。この補題は導入規則なので、呼び出す側が本体の充足を組み立てるための具体的なデータを与えます。`NameAt` の任意の充足からそのデータを復元する仕事は別の妥当性の議論に属し、次章で得られる復元結果も命題的切り詰めの下に残ります。
<!--/-->

```agda
               → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z)
            → ((z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf B C s e γ z
               → ⟨ fst z ∈ fst (lookup d γ) ⟩)
            → ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩
  NameAt-in hf ha he into back =
```

<!--en-->
The proof feeds these two directions to the introduction rule for `extAt`.
For `z ∈ d`, the first direction supplies carrier membership and a payload,
which `DenoteBody-in` converts into satisfaction of the body. Conversely,
satisfaction of the body is read by `DenoteBody-out` as carrier membership and
a propositionally truncated payload. Truncation elimination may then apply
the second input because its target, `z ∈ d`, is a proposition. Combining
this extensional characterization with the first three inputs establishes the
whole name formula.
<!--zh-->
证明把这两个方向交给 `extAt` 的引入规则。由 `z ∈ d`，第一向给出载体隶属与载荷，`DenoteBody-in` 再把它们转换为对公式体的满足。反过来，`DenoteBody-out` 把公式体的满足读成载体隶属与经过命题截断的载荷。由于目标 `z ∈ d` 是命题，可以消去该截断并应用第二份输入。把所得外延刻画与前三份输入组合起来，便得到整条名字公式的满足。
<!--ja-->
証明は、この二方向を `extAt` の導入規則へ渡します。`z ∈ d` からは、一方の入力が台への所属と中身を与え、`DenoteBody-in` がそれらを本体の充足へ変換します。逆に、本体の充足は `DenoteBody-out` によって、台への所属と命題的に切り詰められた中身として読まれます。目標の `z ∈ d` は命題なので、この切り詰めを消去してもう一方の入力を適用できます。こうして得た外延的な特徴づけを最初の三入力と組み合わせると、名前の論理式全体が充足されます。
<!--/-->

```agda
    hf , (ha , (he , extAt-in-both d (DenoteBody B C s e) γ
      (λ z hz → DenoteBody-in B C s e γ z (into z hz .fst) (into z hz .snd))
      (λ z h → PT.rec (snd (fst z ∈ fst (lookup d γ)))
                 (back z (DenoteBody-out B C s e γ z h .fst))
                 (DenoteBody-out B C s e γ z h .snd))))

```

<!--en-->
## The order, with no recursion of its own
<!--zh-->
## 那个序，不跑自己的递归
<!--ja-->
## 再帰をもたない順序
<!--/-->

<!--en-->
The comparison formulas next bind data in blocks, so references to the ambient
assignment must be shifted uniformly. `sh3` moves an ambient slot past three
new binders. In `LexAt` these binders hold an index `i` and the two values read
from the parameter environments at `i`, allowing the original slots for the
two environments and the parameter order to remain in scope. The same shift
later carries ambient slots past the skeleton, arity, and environment of a
competing name in `LeastNameAt`.
<!--zh-->
随后的比较公式成组绑定数据，因此对周遭赋值的引用须作统一移位。`sh3` 把一个周遭位置移过三层新绑定。在 `LexAt` 中，这三层分别存放序号 `i` 以及两个参数环境在 `i` 处的取值，使原有的两个环境位置与参数序位置仍可引用。稍后的 `LeastNameAt` 也使用同一移位，把周遭位置移过一个竞争名字的骨架、元数与环境。
<!--ja-->
続く比較の論理式はデータをまとまった束縛子で導入するため、周囲の割り当てへの参照を一様に移す必要があります。`sh3` は、周囲のスロットを三つの新しい束縛子の先へ移します。`LexAt` では、この三つに添字 `i` と、二つのパラメータ環境から `i` で読み出した値が入ります。その下でも、もとの二つの環境とパラメータ順序のスロットを参照できます。後の `LeastNameAt` でも同じ移動を使い、競合する名前の骨格、アリティ、環境を束縛した先へ周囲のスロットを運びます。
<!--/-->

```agda
private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

```

<!--en-->
`sh6` performs the corresponding move past six binders. It is used when
`StepBody` binds two names, each represented by a skeleton, an arity, and a
parameter environment. The fully extended assignment therefore has the six
new values before the original one, while the carrier, the two order
relations, the two code sets, and the denotations being compared remain
ambient slots. These shifts preserve the intended references; they add no
ordering assumption and perform no comparison themselves.
<!--zh-->
`sh6` 相应地把引用移过六层绑定。`StepBody` 绑定两个名字时会使用它，每个名字都由骨架、元数与参数环境表示。完全扩展后的赋值因而把六个新取值置于原赋值之前，而载体、两个序关系、两个码集以及待比较的两个指称仍保留为周遭位置。这些移位只保持引用所指，不增添任何序假设，也不亲自执行比较。
<!--ja-->
`sh6` は、対応する移動を六つの束縛子について行います。`StepBody` が二つの名前を束縛するときに使われ、各名前は骨格、アリティ、パラメータ環境によって表されます。そのため、完全に拡張された割り当てでは六つの新しい値がもとの割り当ての前に置かれますが、台、二つの順序関係、二つの符号集合、比較する二つの表示は周囲のスロットとして残ります。これらの移動は参照先を保つだけであり、順序の仮定を加えたり、それ自体で比較を行ったりはしません。
<!--/-->

```agda
  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))

```

<!--en-->
The parameter key asks for the first position at which two parameter
environments differ. `LexAt` begins by binding an element `i` of the set in the
arity slot. When that slot contains the numeral for an arity, its members are
exactly the numerals for smaller positions, so this bounded existential ranges
over the possible indices without introducing a separate order on indices.
<!--zh-->
参数键要找两个参数环境首次相异的位置。`LexAt` 先绑定元数位置所持集合的一个成员 `i`。当该位置存放一个元数的数码时，它的成员恰是各个更小位置的数码；因此，这个有界存在量词已经遍历全部可能的序号，无须另行引入序号之序。
<!--ja-->
パラメータの鍵は、二つのパラメータ環境が最初に異なる位置を求めます。`LexAt` はまず、アリティのスロットにある集合の元 `i` を束縛します。そのスロットにアリティの数項が入っていれば、その元はちょうど、それより小さい位置を表す数項です。したがって、この有界存在量化子だけで可能な添字をすべて動かせ、添字のための別の順序は必要ありません。
<!--/-->

```agda
LexAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
LexAt P a e₁ e₂ =
  ∃̇∈ (var a) (
    ∃̇ ( ∃̇ ( appAt (sh3 e₁) (suc (suc zero)) (suc zero)
           ∧̇ ( appAt (sh3 e₂) (suc (suc zero)) zero
```

<!--en-->
After choosing `i`, two existential witnesses give values `u` and `v` with
`e₁(i)=u` and `e₂(i)=v`, and a third application asserts that the ordered pair
of `u` and `v` belongs to the parameter relation `P`. The bounded universal
then considers every `j ∈ i`; for each such `j`, an existential witness `x`
must be a value of both environment graphs at `j`. Thus the formula says
"strictly ordered here, with a common value at every earlier position." Only
after the two environments are identified as single-valued graphs does a
common value imply equality of the corresponding parameters. In the later
adequacy argument, graph lookup and injectivity of the carrier embedding supply
precisely that implication. The formula itself performs no recursion.
<!--zh-->
选定 `i` 后，两层存在量词给出取值 `u` 与 `v`，使 `e₁(i)=u`、`e₂(i)=v`；第三次应用则断言 `u` 与 `v` 组成的有序对属于参数关系 `P`。随后的有界全称量词考察每个 `j ∈ i`，并对每个这样的 `j` 要求仅仅存在一个取值 `x`，使两张环境图在 `j` 处都取到 `x`。所以整条公式说的是「此处严格有序，而每个更早位置都有共同取值」。只有把两个环境认作单值图之后，共同取值才蕴涵相应参数相等；后面的充分性论证正是用图的查表性质与载体嵌入的单射性得到这一步。公式本身不执行递归。
<!--ja-->
`i` を選ぶと、続く二つの存在量化子が値 `u` と `v` を与え、`e₁(i)=u` と `e₂(i)=v` を述べます。第三の適用は、`u` と `v` の順序対がパラメータ関係 `P` に属すことを主張します。次の有界全称量化子は各 `j ∈ i` を調べ、それぞれについて、二つの環境グラフがともに `j` で取る値 `x` が単に存在することを要求します。したがって論理式の内容は、「この位置では厳密に小さく、それ以前の各位置では共通の値をもつ」です。共通の値から対応するパラメータの等しさを導けるのは、二つの環境を一価なグラフと同定した後です。後の妥当性証明では、グラフの参照に関する性質と台の埋め込みの単射性が、まさにこの含意を与えます。論理式そのものは再帰を行いません。
<!--/-->

```agda
             ∧̇ ( appAt (sh3 P) (suc zero) zero
               ∧̇ ∀̇∈ (var (suc (suc zero))) (
                    ∃̇ ( appAt (sh5 e₁) (suc zero) zero
                      ∧̇ appAt (sh5 e₂) (suc zero) zero ) ) ) ) ) ) )

```

<!--en-->
The full name comparison now combines the three keys in their lexicographic
priority: skeleton code, arity, and parameter environment. Its first disjunct
applies the relation in slot `R` to `s₁` and `s₂`. By the adequacy of
application, this says that the ordered pair of the two skeleton codes belongs
to `R`. Keeping `R` as a slot makes the formula uniform; the later adequacy
theorem instantiates it with a relation representing the limit-stage code
order.
<!--zh-->
完整的名字比较现在按字典序的优先次序组合三个键：骨架码、元数与参数环境。第一个析取支把关系位置 `R` 应用于 `s₁` 与 `s₂`。由取值公式的充分性，这表示两个骨架码组成的有序对属于 `R`。把 `R` 保留为一个位置，使同一条公式可以通用于不同赋值；后面的充分性定理会在这里填入表示极限层码序的关系。
<!--ja-->
名前全体の比較は、骨格の符号、アリティ、パラメータ環境という三つの鍵を辞書式の優先順位で組み合わせます。第一の選言は、スロット `R` の関係を `s₁` と `s₂` に適用します。適用の妥当性により、これは二つの骨格の符号からなる順序対が `R` に属すという意味です。`R` をスロットのままにすることで、同じ論理式を異なる割り当てに使えます。後の妥当性定理では、極限段階の符号順序を表す関係がここに入ります。
<!--/-->

```agda
≺At : ∀ {n} → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
≺At R P s₁ a₁ e₁ s₂ a₂ e₂ =
      appAt R s₁ s₂
  ∨̇ ( (var s₂ ≐ var s₁)
```

<!--en-->
The second disjunct handles equal skeleton codes. It records the equality in
the direction `s₂ = s₁` and then offers the remaining two lexicographic cases:
either `a₁ ∈ a₂`, which means that the first arity is smaller when both slots
contain numerals, or `a₂ = a₁` and `LexAt P a₁ e₁ e₂` settles the comparison at
the first differing parameter. The orientations `s₂ = s₁` and `a₂ = a₁` match
the later transports that move the second name's code and parameter vector to
the first name's data.
<!--zh-->
第二个析取支处理骨架码相等的情形。它先按 `s₂ = s₁` 的方向记录等式，再给出余下两个字典序分支：若两个元数位置都存放数码，则 `a₁ ∈ a₂` 表示第一元数更小；另一分支要求 `a₂ = a₁`，再由 `LexAt P a₁ e₁ e₂` 在参数首次相异处决定次序。`s₂ = s₁` 与 `a₂ = a₁` 的方向正好配合后面的迁移，把第二个名字的码与参数向量移到第一个名字的数据上。
<!--ja-->
第二の選言は、骨格の符号が等しい場合を扱います。まず等しさを `s₂ = s₁` の向きで記録し、その後に残る二つの辞書式の場合を並べます。両方のアリティのスロットが数項なら、`a₁ ∈ a₂` は第一のアリティが小さいことを意味します。もう一つの分岐は `a₂ = a₁` を要求し、`LexAt P a₁ e₁ e₂` が最初に異なるパラメータで比較を決めます。`s₂ = s₁` と `a₂ = a₁` という向きは、第二の名前の符号とパラメータベクトルを第一の名前のデータへ移す、後の輸送の向きに合っています。
<!--/-->

```agda
    ∧̇ ( (var a₁ ∈̇ var a₂)
      ∨̇ ( (var a₂ ≐ var a₁) ∧̇ LexAt P a₁ e₁ e₂ ) ) )

```

<!--en-->
To prove a reusable reading of `LexAt`, we isolate the formula occurring under
the agreement existential. At a previously considered position `j`, `Body`
requires one value `x` to satisfy both applications, hence to occur in both
environment graphs at `j`. In the extended assignment the five new entries are
`x`, `j`, `v`, `u`, and `i`, so each reference to an ambient environment is
shifted past five binders.
<!--zh-->
为了给 `LexAt` 证明一条可复用的读式，先单独命名相符存在量词之下的公式体。在先前位置 `j` 处，`Body` 要求同一个取值 `x` 满足两次应用，也就是让两张环境图在 `j` 处都含有取值 `x`。扩张赋值中新添的五项依次是 `x`、`j`、`v`、`u`、`i`，所以对周遭环境位置的引用都须穿过五层绑定。
<!--ja-->
`LexAt` の読みを繰り返し使える形で証明するため、一致を述べる存在量化子の下にある本体を取り出して名前を付けます。先行する位置 `j` で、`Body` は同じ値 `x` が二つの適用をともに満たすこと、すなわち二つの環境グラフがともに `j` で値 `x` をもつことを要求します。拡張された割り当てには `x`、`j`、`v`、`u`、`i` の五項が新しく並ぶので、周囲の環境スロットへの参照は五つの束縛子を越えて移されます。
<!--/-->

```agda
module _ {n : ℕ} (P a e₁ e₂ : Fin n) (γ : S ^ n) where
  private
    Body : Formula S (suc (suc (suc (suc (suc n)))))
    Body = appAt (sh5 e₁) (suc zero) zero ∧̇ appAt (sh5 e₂) (suc zero) zero

```

<!--en-->
With `i`, `u`, and `v` fixed, `Inner i u v` records the body left by the first
three existential binders. Its first two components say that the graphs `e₁`
and `e₂` contain the pairs `(i,u)` and `(i,v)`. The third says that the pair
`(u,v)` belongs to the relation `P`. These are still satisfaction statements
for `appAt`; their decoded membership form will be recorded separately so that
the two presentations can be related explicitly.
<!--zh-->
固定 `i`、`u`、`v` 后，`Inner i u v` 记录前三层存在绑定之后剩下的公式体。前两个分量说图 `e₁` 与 `e₂` 分别含有对 `(i,u)` 与 `(i,v)`；第三个分量说对 `(u,v)` 属于关系 `P`。这些分量仍是关于 `appAt` 的满足关系陈述；稍后另行记录它们解码后的隶属形态，便可显式联系这两种呈现。
<!--ja-->
`i`、`u`、`v` を固定すると、`Inner i u v` は最初の三つの存在束縛子の後に残る本体を記録します。最初の二成分は、グラフ `e₁` と `e₂` がそれぞれ対 `(i,u)` と `(i,v)` を含むことを述べます。第三の成分は、対 `(u,v)` が関係 `P` に属すことを述べます。これらはまだ `appAt` の充足を表す主張です。二つの表示を明示的に結べるように、解読後の所属の形は別に記録します。
<!--/-->

```agda
    Inner : (i u v : S) → Type (ℓ-suc ℓ)
    Inner i u v =
      ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 e₁) (suc (suc zero)) (suc zero) ⟩
      × ( ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 e₂) (suc (suc zero)) zero ⟩
        × ( ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 P) (suc zero) zero ⟩
```

<!--en-->
The fourth component of `Inner` is agreement below `i`. For every model element
`j` belonging to `i`, it supplies the semantic existential
`∃[ x ∶ S ]` saying that one `x` satisfies `Body`. This existential is a
propositional truncation: it retains the existence of a common value at `j`
without exposing a chosen value as data. The bounded universal is therefore
read as a function that supplies one such truncated existence for each
`j ∈ i`.
<!--zh-->
`Inner` 的第四个分量是在 `i` 之下相符。对每个属于 `i` 的模型元素 `j`，它给出语义存在式 `∃[ x ∶ S ]`，断言某个 `x` 满足 `Body`。这个存在式是命题截断：它保留「在 `j` 处有共同取值」这一事实，却不把选定的取值作为数据暴露出来。因此，有界全称量词被读成一个函数，为每个 `j ∈ i` 给出这样一份经过命题截断的存在。
<!--ja-->
`Inner` の第四成分は、`i` より下での一致です。`i` に属するモデルの各要素 `j` に対し、一つの `x` が `Body` を満たすという意味論上の存在式 `∃[ x ∶ S ]` を与えます。この存在式は命題的切り詰めです。`j` で共通の値が存在することは保ちますが、選ばれた値をデータとして外へ出しません。したがって有界全称量化子は、各 `j ∈ i` に対して、そのように切り詰められた存在を一つ与える関数として読まれます。
<!--/-->

```agda
          × ((j : S) → ⟨ fst j ∈ fst i ⟩
             → ⟨ ∃[ x ∶ S ] (x ∷ j ∷ v ∷ u ∷ i ∷ γ) ⊨ Body ⟩) ) )

```

<!--en-->
`Agrees i` states the same agreement after decoding the two applications. For
every `j ∈ i`, merely there is an element `x : S` such that the pair formed
from the underlying sets of `j` and `x` belongs to both graphs `e₁` and `e₂`.
When `i` is an arity numeral, its members represent precisely the earlier
positions. This definition records only a common graph value. Equality of the
corresponding meta-level parameters is derived later from the known environment
graphs and the injectivity of the carrier embedding.
<!--zh-->
`Agrees i` 以两次应用解码后的形态陈述同一项相符：对每个 `j ∈ i`，仅仅存在一个元素 `x : S`，使 `j` 与 `x` 的底集组成的对同时属于图 `e₁` 与 `e₂`。当 `i` 是元数的数码时，它的成员恰好表示所有更早位置。这个定义只记录共同的图取值；相应元层参数的相等要到后面才从已知的环境图与载体嵌入的单射性导出。
<!--ja-->
`Agrees i` は、二つの適用を解読した形で同じ一致を述べます。各 `j ∈ i` について、`j` と `x` の底にある集合から作った対がグラフ `e₁` と `e₂` の両方に属すような元 `x : S` が単に存在します。`i` がアリティの数項なら、その元はちょうど先行する位置を表します。この定義が記録するのは共通のグラフ値だけです。対応するメタレベルのパラメータの等しさは、既知の環境グラフと台の埋め込みの単射性から後で導かれます。
<!--/-->

```agda
  Agrees : (i : S) → Type (ℓ-suc ℓ)
  Agrees i = (j : S) → ⟨ fst j ∈ fst i ⟩
           → ∥ Σ[ x ∈ S ] ( ⟨ pr (fst j) (fst x) ∈ fst (lookup e₁ γ) ⟩
                          × ⟨ pr (fst j) (fst x) ∈ fst (lookup e₂ γ) ⟩ ) ∥₁

```

<!--en-->
`Differs` collects the complete decoded witness for a first difference. It
contains an index `i`, values `u` and `v`, membership of `i` in the set stored
at the arity slot, graph memberships for `(i,u)` and `(i,v)`, the strict
parameter comparison at that position, and `Agrees i`. When the arity slot is
a numeral and the two graph slots are parameter environments of that arity,
these fields are exactly the data needed for a lexicographic first difference.
<!--zh-->
`Differs` 汇集首次相异见证的完整解码形态。它包含序号 `i`、取值 `u` 与 `v`、`i` 对元数位置所持集合的隶属、对 `(i,u)` 与 `(i,v)` 的两份图隶属、该位置上的严格参数比较，以及 `Agrees i`。当元数位置存放数码，且两个图位置存放该元数的参数环境时，这些字段恰好组成字典序首次相异所需的数据。
<!--ja-->
`Differs` は、最初の相違を示す証人を解読した完全な形でまとめます。添字 `i`、値 `u` と `v`、アリティのスロットにある集合への `i` の所属、対 `(i,u)` と `(i,v)` のグラフへの所属、その位置での厳密なパラメータ比較、そして `Agrees i` が含まれます。アリティのスロットが数項で、二つのグラフのスロットがそのアリティのパラメータ環境なら、これらは辞書式の最初の相違に必要なデータそのものです。
<!--/-->

```agda
  Differs : Type (ℓ-suc ℓ)
  Differs = Σ[ i ∈ S ] Σ[ u ∈ S ] Σ[ v ∈ S ]
    ( ⟨ fst i ∈ fst (lookup a γ) ⟩
    × ( ⟨ pr (fst i) (fst u) ∈ fst (lookup e₁ γ) ⟩
      × ( ⟨ pr (fst i) (fst v) ∈ fst (lookup e₂ γ) ⟩
```

<!--en-->
The strict comparison field has the same relational form as the code case of
`≺At`: the ordered pair of the underlying values of `u` and `v` belongs to the
set in slot `P`. The final field `Agrees i` records a common value at every
earlier position; for the intended single-valued environment graphs, this
certifies that no earlier parameters differ. Thus `Differs` separates the
mathematical content of the first-difference witness from the object-language
binders used to express it.
<!--zh-->
严格比较字段与 `≺At` 的码分支采用相同的关系形态：`u` 与 `v` 的底层值组成的有序对属于位置 `P` 所持的集合。末尾的 `Agrees i` 记录每个更早位置上的共同取值；对预期的单值环境图而言，这便保证更早参数没有相异。因此，`Differs` 把首次相异见证的数学内容与表达它的对象语言绑定结构分开记录。
<!--ja-->
厳密な比較のフィールドは、`≺At` の符号の場合と同じ関係の形を取ります。`u` と `v` の底にある値から作った順序対が、スロット `P` の集合に属すという形です。最後の `Agrees i` は、それ以前の各位置で共通の値があることを記録します。意図した一価な環境グラフについては、これが、それ以前のパラメータに相違がないことを保証します。こうして `Differs` は、最初の相違を示す証人の数学的内容を、それを表す対象言語の束縛構造から分けて記録します。
<!--/-->

```agda
        × ( ⟨ pr (fst u) (fst v) ∈ fst (lookup P γ) ⟩ × Agrees i ) ) ) )

```

<!--en-->
The map `pack` converts only the agreement component of `Inner` into
`Agrees`; the first three components are irrelevant to this local conversion.
For a fixed `j ∈ i`, a witness `x` for the semantic existential comes with two
satisfactions of `appAt`. Applying `appAt-adequate` to each turns them into the
two graph memberships required by `Agrees`, while preserving the same witness
`x`.
<!--zh-->
映射 `pack` 只把 `Inner` 的相符分量转换为 `Agrees`，前三个分量与这次局部转换无关。固定 `j ∈ i` 后，语义存在式的一个见证 `x` 带有两份对 `appAt` 的满足证明。分别应用 `appAt-adequate`，即可把它们变成 `Agrees` 所需的两份图隶属，同时保持同一个见证 `x`。
<!--ja-->
写像 `pack` が変換するのは、`Inner` の一致の成分だけです。最初の三成分は、この局所的な変換には使いません。`j ∈ i` を固定すると、意味論上の存在式の証人 `x` には、`appAt` を充足する二つの証明が伴います。それぞれに `appAt-adequate` を適用すれば、同じ証人 `x` を保ったまま、`Agrees` が要求する二つのグラフ所属が得られます。
<!--/-->

```agda
  private
    pack : (i u v : S) → Inner i u v → Agrees i
    pack i u v (_ , (_ , (_ , hj))) j hj' = PT.map
      (λ { (x , (p₁ , p₂)) → x
         , ( subst ⟨_⟩
```

<!--en-->
This conversion is performed inside the existing propositional truncation.
`PT.map` sends every possible witness and its two application proofs to the
same witness with two membership proofs. Since the target is again a truncated
existence, no representative is extracted and no choice principle is used.
Pointwise mapping is enough to obtain `Agrees i` for every earlier position.
<!--zh-->
这次转换在已有的命题截断之内完成。`PT.map` 把每个可能的见证及其两份应用证明，映成同一个见证及其两份隶属证明。由于目标仍是经过命题截断的存在，过程中既不取出任何代表，也不使用选择原理。逐点映射便足以对每个更早位置得到 `Agrees i` 所需的结论。
<!--ja-->
この変換は、すでにある命題的切り詰めの内部で行われます。`PT.map` は、可能な各証人と二つの適用の証明を、同じ証人と二つの所属の証明へ写します。目標も切り詰められた存在なので、代表を取り出す必要はなく、選択原理も使いません。各点で写すだけで、すべての先行する位置について `Agrees i` に必要な結論が得られます。
<!--/-->

```agda
               (appAt-adequate (sh5 e₁) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ)) p₁
           , subst ⟨_⟩
               (appAt-adequate (sh5 e₂) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ)) p₂ ) })
      (hj j hj')

```

<!--en-->
`unpack` provides the converse conversion needed to satisfy the formula. From
`Agrees i` and a position `j ∈ i`, it receives a truncated common-value
witness. For each representative `x`, it keeps that witness and prepares to
turn the two graph memberships back into satisfactions of the two applications
in `Body`.
<!--zh-->
`unpack` 给出满足原公式所需的反向转换。由 `Agrees i` 与一个位置 `j ∈ i`，它取得一份经过命题截断的共同取值见证。对其中每个可能的代表 `x`，它保留该见证，并把两份图隶属转换回 `Body` 中两次应用的满足证明。
<!--ja-->
`unpack` は、もとの論理式を充足するために必要な逆向きの変換を与えます。`Agrees i` と位置 `j ∈ i` から、切り詰められた共通値の証人を受け取ります。それぞれの代表 `x` をそのまま保ち、二つのグラフ所属を `Body` にある二つの適用の充足へ戻します。
<!--/-->

```agda
    unpack : (i u v : S) → Agrees i
           → (j : S) → ⟨ fst j ∈ fst i ⟩
           → ⟨ ∃[ x ∶ S ] (x ∷ j ∷ v ∷ u ∷ i ∷ γ) ⊨ Body ⟩
    unpack i u v hj j hj' = PT.map
      (λ { (x , (p₁ , p₂)) → x
```

<!--en-->
The same adequacy paths are now used in the reverse direction. Each membership
proof is transported along the symmetric path of `appAt-adequate`, producing
the corresponding conjunct of `Body`. Again `PT.map` keeps the construction
inside the truncated existential, so `unpack` proves the required semantic
existence without selecting a common value globally.
<!--zh-->
这里沿反方向使用同一些充分性路径。每份隶属证明都沿 `appAt-adequate` 的对称路径迁移，从而得到 `Body` 中相应的合取项。`PT.map` 再次使整个构造留在经过命题截断的存在之内，所以 `unpack` 无须在全局选定共同取值，便能证明所需的语义存在。
<!--ja-->
ここでは同じ妥当性のパスを逆向きに使います。各所属の証明を `appAt-adequate` の対称なパスに沿って輸送すると、`Body` の対応する連言が得られます。ここでも `PT.map` によって構成全体が切り詰められた存在の内部に留まるため、`unpack` は共通の値を大域的に選ぶことなく、必要な意味論上の存在を証明できます。
<!--/-->

```agda
         , ( subst ⟨_⟩
               (sym (appAt-adequate (sh5 e₁) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ))) p₁
           , subst ⟨_⟩
               (sym (appAt-adequate (sh5 e₂) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ))) p₂ ) })
      (hj j hj')
```

<!--en-->
`LexAt-in` starts from the explicit data in `Differs`. The index `i` and the
values `u` and `v` become the witnesses for the bounded existential and the two
following existentials, with `hi` certifying the bound. In the extended
assignment `γ₃ = v ∷ u ∷ i ∷ γ`, the first two graph memberships are
transported backward along `appAt-adequate` to satisfy the applications for
`e₁(i)=u` and `e₂(i)=v`. The remaining relation and agreement fields fit the
same conjunction, with `unpack` supplying its bounded-universal component.
<!--zh-->
`LexAt-in` 从 `Differs` 中的明确数据出发。序号 `i` 与取值 `u`、`v` 分别成为有界存在量词及随后两层存在量词的见证，`hi` 则证明 `i` 确实落在界内。在扩张赋值 `γ₃ = v ∷ u ∷ i ∷ γ` 中，前两份图隶属沿 `appAt-adequate` 反向迁移，得到对 `e₁(i)=u` 与 `e₂(i)=v` 两次应用的满足证明。关系字段与相符字段随后进入同一个合取结构，其中有界全称分量由 `unpack` 给出。
<!--ja-->
`LexAt-in` は、`Differs` にある明示的なデータから始めます。添字 `i` と値 `u`、`v` は、有界存在量化子と、それに続く二つの存在量化子の証人になり、`hi` が `i` が限界内にあることを証明します。拡張された割り当て `γ₃ = v ∷ u ∷ i ∷ γ` では、最初の二つのグラフ所属を `appAt-adequate` に沿って逆向きに輸送し、`e₁(i)=u` と `e₂(i)=v` を表す二つの適用を充足させます。残る関係と一致のフィールドも同じ連言構造に入り、有界全称の成分は `unpack` が与えます。
<!--/-->

```agda

  LexAt-in : Differs → ⟨ γ ⊨ LexAt P a e₁ e₂ ⟩
  LexAt-in (i , (u , (v , (hi , (h₁ , (h₂ , (hp , hj)))))))
    = ∣ i , (hi , ∣ u , ∣ v
    , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 e₁) (suc (suc zero)) (suc zero) γ₃)) h₁
      , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 e₂) (suc (suc zero)) zero γ₃)) h₂
```

<!--en-->
The final field of `Differs` completes the introduction proof. The membership
of `(u,v)` in `P` is transported backward along `appAt-adequate` to satisfy the
third application, while `unpack` turns agreement below `i` into the bounded
universal's semantic form. The assignment `γ₃ = v ∷ u ∷ i ∷ γ` makes the
binder order explicit; the surrounding constructors then close the
existentials for `v`, `u`, and `i`, from the inside out.
<!--zh-->
`Differs` 的最后两个字段完成引入证明。对 `(u,v)` 属于 `P` 的证明沿`appAt-adequate` 反向迁移，成为对第三次应用的满足关系证明；`unpack` 则把`i` 以下的相符变成有界全称量词所需的语义形态。赋值`γ₃ = v ∷ u ∷ i ∷ γ` 明确记录三层绑定的次序，外围的构造子再由内向外依次闭合 `v`、`u` 与 `i` 的存在量词。
<!--ja-->
`Differs` の最後の二つの成分が導入の証明を完成させます。`(u,v)` が `P`に属すという証明を `appAt-adequate` に沿って逆向きに輸送すると、第三の適用についての充足関係の証明になり、`unpack` は `i` より前での一致を有界全称量化子の意味論的な形へ変えます。割り当て`γ₃ = v ∷ u ∷ i ∷ γ` は三つの束縛の順序を明示しており、周囲の構成子が`v`、`u`、`i` の存在量化子を内側から順に閉じます。
<!--/-->

```agda
        , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 P) (suc zero) zero γ₃)) hp
          , unpack i u v hj ) ) ) ∣₁ ∣₁) ∣₁
    where
    γ₃ : S ^ (suc (suc (suc n)))
    γ₃ = v ∷ u ∷ i ∷ γ
```

<!--en-->
Reading `LexAt` outward must preserve the witness boundary created by its
existentials. Accordingly, `LexAt-out` targets `∥ Differs ∥₁`, a proposition,
and eliminates the outer truncation only into that target. The local function
`atValue` performs the mathematical decoding: once particular `i`, `u`, and
`v`, the bound proof, and the remaining satisfaction data are available inside
the eliminations, it builds an untruncated `Differs` record. No such record is
chosen outside those local scopes.
<!--zh-->
从 `LexAt` 向外读取时，必须保留其存在量词所设下的见证边界。因此，`LexAt-out` 的目标是命题 `∥ Differs ∥₁`，并且只把外层截断消去到这个目标中。局部函数 `atValue` 承担实际的数学解码：一旦在各次消去的局部范围内取得具体的`i`、`u`、`v`、界限证明和余下的满足关系数据，它便构造一份未截断的`Differs` 记录。这样的记录不会被选出到这些局部范围之外。
<!--ja-->
`LexAt` を外向きに読むときは、その存在量化子が設けた証人の境界を保たなければなりません。そのため `LexAt-out` の行き先は命題 `∥ Differs ∥₁` であり、外側の切り詰めはこの行き先の中へだけ消去されます。局所関数 `atValue` が実際の数学的な復号を担います。各消去の局所的な範囲で、具体的な `i`、`u`、`v`、境界の証明、残りの充足関係のデータが得られれば、切り詰められていない`Differs` の記録を作れます。その記録を局所的な範囲の外へ選び出すことはありません。
<!--/-->

```agda

  LexAt-out : ⟨ γ ⊨ LexAt P a e₁ e₂ ⟩ → ∥ Differs ∥₁
  LexAt-out = PT.rec squash₁ atIndex
    where
    atValue : (i u v : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩ → Inner i u v → Differs
    atValue i u v hi h@(h₁ , (h₂ , (hp , _))) = i , (u , (v
```

<!--en-->
The first half of `atValue` recovers the index and the two graph lookups. The
bound proof `hi` already has the form required by `Differs`. Reading the two
adequacy paths forward converts satisfaction of the applications into
membership of `(i,u)` in `e₁` and membership of `(i,v)` in `e₂`. Thus the two
values remain attached to the same index at which the formula found them.
<!--zh-->
`atValue` 的前半段恢复序号与两次图查取。界限证明 `hi` 已经具有 `Differs`要求的形态。正向读取两条充分性路径，便把两次应用的满足关系分别变成`(i,u)` 对 `e₁` 的隶属，以及 `(i,v)` 对 `e₂` 的隶属。因此，两个取值仍与公式找到它们时的同一个序号相联系。
<!--ja-->
`atValue` の前半は、添字と二つのグラフ参照を復元します。境界の証明 `hi`は、すでに `Differs` が要求する形です。二つの妥当性のパスを順方向に読むと、適用についての充足関係は、`(i,u)` の `e₁` への所属と `(i,v)` の `e₂` への所属にそれぞれ変わります。したがって二つの値は、論理式がそれらを見つけた同じ添字に結び付いたままです。
<!--/-->

```agda
      , ( hi
        , ( subst ⟨_⟩
              (appAt-adequate (sh3 e₁) (suc (suc zero)) (suc zero) (v ∷ u ∷ i ∷ γ)) h₁
          , ( subst ⟨_⟩
                (appAt-adequate (sh3 e₂) (suc (suc zero)) zero (v ∷ u ∷ i ∷ γ)) h₂
```

<!--en-->
The third application is decoded in the same way, yielding membership of
`(u,v)` in the parameter relation `P`. The function `pack` supplies the final
field by translating the bounded agreement from application form to the two
graph memberships required by `Agrees i`. These pieces form one explicit
`Differs` record inside `atValue`; the surrounding eliminations will retain
only its propositional truncation.
<!--zh-->
第三次应用以同样方式解码，得到 `(u,v)` 对参数关系 `P` 的隶属。函数 `pack`把有界范围内以应用陈述的相符翻译成 `Agrees i` 所要求的两份图隶属，从而给出最后一个字段。这些数据在 `atValue` 内组成一份明确的 `Differs` 记录；外围的各次消去最终只保留它的命题截断。
<!--ja-->
第三の適用も同じように復号され、`(u,v)` がパラメータ関係 `P` に属すことが得られます。関数 `pack` は、有界な範囲で適用の形を取っていた一致を`Agrees i` が要求する二つのグラフ所属へ翻訳し、最後の成分を与えます。これらのデータは `atValue` の内部で明示的な `Differs` の記録をなしますが、周囲の消去が最終的に保つのはその命題的切り詰めだけです。
<!--/-->

```agda
            , ( subst ⟨_⟩
                  (appAt-adequate (sh3 P) (suc zero) zero (v ∷ u ∷ i ∷ γ)) hp
              , pack i u v h ) ) ) ) ))

```

<!--en-->
The innermost existential supplies the second value `v` together with
`Inner i u v`, but only within its truncation. The handler `atSecond` uses each
locally available pair `(v,h)` to build `Differs` by `atValue` and immediately
places the result in `∥ Differs ∥₁`. This is exactly the permitted elimination:
the witness is used to prove a proposition and is not exposed by the result.
<!--zh-->
最内层存在量词给出第二个取值 `v` 及 `Inner i u v`，但二者只在该存在量词的截断内部可用。处理函数 `atSecond` 对每一份局部可用的 `(v,h)` 调用 `atValue`构造 `Differs`，并立即把结果放入 `∥ Differs ∥₁`。这正是命题截断所容许的消去：见证被用于证明一个命题，却不会由结果暴露出来。
<!--ja-->
最も内側の存在量化子は、第二の値 `v` と `Inner i u v` を与えますが、両者を使えるのはその切り詰めの内部だけです。処理関数 `atSecond` は、局所的に得られた各組 `(v,h)` から `atValue` で `Differs` を作り、ただちに`∥ Differs ∥₁` へ入れます。これは命題的切り詰めに許された消去そのものです。証人は命題を証明するために使われますが、結果から外へ現れることはありません。
<!--/-->

```agda
    atSecond : (i u : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩
             → Σ[ v ∈ S ] Inner i u v → ∥ Differs ∥₁
    atSecond i u hi (v , h) = ∣ atValue i u v hi h ∣₁

```

<!--en-->
One layer farther out, `atFirst` receives a particular first value `u` and a
truncated existence of the second value. It eliminates that inner truncation
with `atSecond`, whose result is again `∥ Differs ∥₁`. The argument therefore
passes from the first value to the completed first-difference record without
ever requiring a globally available `v`.
<!--zh-->
向外一层，`atFirst` 取得具体的第一个取值 `u`，以及第二个取值之存在的截断。它用 `atSecond` 消去这层内部截断，而 `atSecond` 的结果仍是`∥ Differs ∥₁`。所以论证可以从第一个取值走到完整的首次相异记录，而始终无须取得一个全局可用的 `v`。
<!--ja-->
一つ外の層で、`atFirst` は具体的な第一の値 `u` と、第二の値の存在を切り詰めたものを受け取ります。その内側の切り詰めを `atSecond` で消去すると、行き先は再び `∥ Differs ∥₁` です。したがって、第一の値から完成した最初の相違の記録へ進むあいだも、大域的に使える `v` を取り出す必要はありません。
<!--/-->

```agda
    atFirst : (i : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩
            → Σ[ u ∈ S ] ∥ Σ[ v ∈ S ] Inner i u v ∥₁ → ∥ Differs ∥₁
    atFirst i hi (u , h) = PT.rec squash₁ (atSecond i u hi) h

```

<!--en-->
Finally `atIndex` receives an index `i`, its proof `hi` of lying below the
arity, and the truncated remainder beginning with `u`. Eliminating that
remainder with `atFirst` completes the outward reading. Taken together, the
three handlers follow the existential nesting from `i` to `u` to `v`, while
every elimination has the same propositional target. Hence `LexAt-out`
establishes that a first-difference record merely exists, with no choice of its
index or values.
<!--zh-->
最后，`atIndex` 取得序号 `i`、证明它低于元数的 `hi`，以及从 `u` 开始的余项之截断。用 `atFirst` 消去这份余项，就完成了向外读取。三个处理函数合起来依`i`、`u`、`v` 的次序跟随存在量词的嵌套，而每次消去都有同一个命题目标。因此，`LexAt-out` 只证明首次相异记录仅仅存在，并未选择其中的序号或取值。
<!--ja-->
最後に `atIndex` は、添字 `i`、それがアリティより小さいことを示す `hi`、そして `u` から始まる残りを切り詰めたものを受け取ります。その残りを`atFirst` で消去すれば、外向きの読みは完成します。三つの処理関数は合わせて、`i`、`u`、`v` という存在量化子の入れ子をたどり、どの消去も同じ命題を行き先とします。したがって `LexAt-out` が示すのは、最初の相違の記録が単に存在することだけであり、その添字や値を選ぶことではありません。
<!--/-->

```agda
    atIndex : Σ[ i ∈ S ] ( ⟨ fst i ∈ fst (lookup a γ) ⟩
                         × ∥ Σ[ u ∈ S ] ∥ Σ[ v ∈ S ] Inner i u v ∥₁ ∥₁ )
            → ∥ Differs ∥₁
    atIndex (i , (hi , h)) = PT.rec squash₁ (atFirst i hi) h
```

<!--en-->
## Reading the comparison, and one step of the family
<!--zh-->
## 读那次比较，以及族的一步
<!--ja-->
## 比較と順序族の一ステップを読む
<!--/-->

<!--en-->
The meta-level payload `Below` now arranges the three comparison keys in the
same priority as `≺At`. Its outer sum says either that the ordered pair of
skeleton codes `(s₁,s₂)` belongs to the relation in slot `R`, or that the codes
are equal and a later key decides. A value of this sum explicitly identifies a
branch and carries its evidence; the definition does not assert that such a
branch can be decided for arbitrary slot values. This distinction matters
because object-language disjunction is interpreted by propositional
truncation.
<!--zh-->
元语言载荷 `Below` 依照 `≺At` 的同一优先次序排列三个比较键。最外层的和类型表示：或者骨架码组成的有序对 `(s₁,s₂)` 属于位置 `R` 中的关系，或者两码相等，由后面的键决定。这个和类型的一个元素会明确指出所取分支并携带相应证据；定义本身并未断言对任意位置取值都能判定应取哪一支。这一区别很要紧，因为对象语言析取的语义带有命题截断。
<!--ja-->
メタレベルの中身 `Below` は、三つの比較の鍵を `≺At` と同じ優先順位で並べます。外側の直和は、骨格の符号からなる順序対 `(s₁,s₂)` がスロット `R` の関係に属すか、または符号が等しく、後の鍵が比較を決めることを表します。この直和の要素は、どの枝に入るかを明示してその証拠を運びますが、任意のスロットの値について枝を判定できると主張する定義ではありません。この区別が必要なのは、対象言語の選言が命題的切り詰めによって解釈されるからです。
<!--/-->

```agda
module _ {n : ℕ} (R P s₁ a₁ e₁ s₂ a₂ e₂ : Fin n) (γ : S ^ n) where
  Below : Type (ℓ-suc ℓ)
  Below = ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ fst (lookup R γ) ⟩
        ⊎ ( (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
          × ( ⟨ fst (lookup a₁ γ) ∈ fst (lookup a₂ γ) ⟩
```

<!--en-->
Under equal skeleton codes, the inner sum first offers the arity comparison
`a₁ ∈ a₂`. When the slots contain arity numerals, this membership says that
the first arity is smaller. If the arities are equal instead, `Differs`
supplies the first-difference evidence for the parameter key. The equalities
are deliberately oriented as `s₂ = s₁` and `a₂ = a₁`, matching the later
transport of the second name's data to the first name's types.
<!--zh-->
在骨架码相等的前提下，内层和类型首先给出元数比较 `a₁ ∈ a₂`。当这两个位置存放元数的数码时，这条隶属表示第一元数较小。若两元数转而相等，则由`Differs` 给出参数键的首次相异证据。两条等式特意取 `s₂ = s₁` 与`a₂ = a₁` 的方向，以配合后文把第二个名字的数据迁移到第一个名字的类型中。
<!--ja-->
骨格の符号が等しい場合、内側の直和はまずアリティの比較 `a₁ ∈ a₂` を提示します。二つのスロットがアリティの数項を含むとき、この所属は第一のアリティのほうが小さいことを意味します。アリティも等しければ、`Differs` がパラメータの鍵について最初の相違の証拠を与えます。二つの等しさは意図的に `s₂ = s₁` と`a₂ = a₁` の向きに置かれ、後で第二の名前のデータを第一の名前の型へ輸送する向きに合っています。
<!--/-->

```agda
            ⊎ ( (fst (lookup a₂ γ) ≡ fst (lookup a₁ γ))
              × Differs P a₁ e₁ e₂ γ ) ) )

```

<!--en-->
`≺At-in` translates an explicit value of `Below` into satisfaction of the
comparison formula. In the code branch, the relation membership is transported
backward along `appAt-adequate` and introduced as the outer left disjunct. In
the arity branch, the code equality accompanies the outer right disjunct, and
the arity membership enters the inner left disjunct. These are introduction
steps only: the supplied branch evidence is packaged into the truncated
semantics of each object-language disjunction.
<!--zh-->
`≺At-in` 把一份明确的 `Below` 数据翻译成对比较公式的满足关系。在码分支中，关系隶属沿 `appAt-adequate` 反向迁移，并作为最外层的左析取支引入。在元数分支中，码等式随最外层右析取支进入，而元数隶属进入内层左析取支。这里所做的全是引入：已给出的分支证据被包装进各对象语言析取带命题截断的语义中。
<!--ja-->
`≺At-in` は、明示的な `Below` のデータを比較の論理式の充足関係へ翻訳します。符号の枝では、関係への所属を `appAt-adequate` に沿って逆向きに輸送し、外側の左の選言として導入します。アリティの枝では、符号の等しさとともに外側の右の選言へ入り、アリティの所属を内側の左の選言へ入れます。ここで行うのは導入だけです。与えられた枝の証拠を、対象言語の各選言に伴う切り詰められた意味へ包みます。
<!--/-->

```agda
  ≺At-in : Below → ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩
  ≺At-in (inl h) =
    ∣ inl (subst ⟨_⟩ (sym (appAt-adequate R s₁ s₂ γ)) h) ∣₁
  ≺At-in (inr (q , inl h)) = ∣ inr (q , ∣ inl h ∣₁) ∣₁
  ≺At-in (inr (q , inr (q' , h))) =
```

<!--en-->
The parameter branch takes the remaining route through both disjunctions. It
carries the code and arity equalities into their right branches, then invokes
`LexAt-in` on the supplied `Differs` record. Thus the same first-difference
data already decoded above becomes satisfaction of the parameter clause. All
three cases of `Below` are therefore inserted into `≺At` without searching for
a branch or extracting any existential witness.
<!--zh-->
参数分支沿两层析取各自的右支进入。它把码等式与元数等式带入相应的右支，再把给定的 `Differs` 记录交给 `LexAt-in`。于是，前文已经解码的首次相异数据便成为参数子句的满足关系。这样，`Below` 的三个情形都能直接引入 `≺At`，无需搜索分支，也无需从存在量词中取出见证。
<!--ja-->
パラメータの枝は、二つの選言の右側を順に進みます。符号とアリティの等しさをそれぞれの右の枝へ運び、与えられた `Differs` の記録を `LexAt-in` に渡します。こうして、すでに復号された最初の相違のデータがパラメータの節の充足関係になります。したがって `Below` の三つの場合はすべて、枝を探索したり存在証人を取り出したりせずに `≺At` へ導入できます。
<!--/-->

```agda
    ∣ inr (q , ∣ inr (q' , LexAt-in P a₁ e₁ e₂ γ h) ∣₁) ∣₁

```

<!--en-->
The reverse direction has a necessarily weaker target:
`≺At-out` returns `∥ Below ∥₁`. Satisfaction of the outer object-language
disjunction is itself truncated, so `PT.rec` may inspect a branch only while
constructing this proposition. The local function `outer` separates the code
case from the equal-code case. In the latter it retains the equality
`s₂ = s₁` and passes the still-unsorted inner disjunction to `inner`.
<!--zh-->
反向读式的目标必然较弱：`≺At-out` 返回 `∥ Below ∥₁`。最外层对象语言析取的满足关系本身带有截断，所以 `PT.rec` 只能在构造这个命题时局部查看其分支。局部函数 `outer` 把码分支与码相等分支分开；在后一情形中，它保留等式`s₂ = s₁`，并把尚未归类的内层析取交给 `inner`。
<!--ja-->
逆向きの読みの行き先は、必然的に弱い `∥ Below ∥₁` です。外側の対象言語の選言についての充足関係自体が切り詰められているため、`PT.rec` が枝を調べられるのは、この命題を構成する局所的な範囲に限られます。局所関数 `outer` は符号の場合と符号が等しい場合を分けます。後者では等しさ `s₂ = s₁` を保ち、まだ分類されていない内側の選言を `inner` に渡します。
<!--/-->

```agda
  ≺At-out : ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩ → ∥ Below ∥₁
  ≺At-out = PT.rec squash₁ outer
    where
    inner : (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
          → ⟨ fst (lookup a₁ γ) ∈ fst (lookup a₂ γ) ⟩
```

<!--en-->
Given the code equality, `inner` reads the two remaining keys. An arity
membership immediately yields the middle case of `Below`. Otherwise the
payload contains the arity equality `a₂ = a₁` and satisfaction of `LexAt`, so
only the first-difference component remains to be decoded. The signature keeps
these alternatives explicit while fixing the code equality shared by both.
<!--zh-->
在给定码等式后，`inner` 读取余下两个键。若取得元数隶属，便立即得到 `Below`的中间情形；否则，载荷包含元数等式 `a₂ = a₁` 以及对 `LexAt` 的满足关系，只剩首次相异分量尚待解码。函数签名把这两个选项明确列出，同时固定二者共同使用的码等式。
<!--ja-->
符号の等しさが与えられると、`inner` は残る二つの鍵を読みます。アリティの所属が得られれば、ただちに `Below` の中間の場合になります。もう一方の中身には、アリティの等しさ `a₂ = a₁` と `LexAt` の充足関係があり、復号すべきものは最初の相違の成分だけです。関数の型は、二つの場合に共通する符号の等しさを固定したまま、これらの選択肢を明示しています。
<!--/-->

```agda
          ⊎ ( (fst (lookup a₂ γ) ≡ fst (lookup a₁ γ))
            × ⟨ γ ⊨ LexAt P a₁ e₁ e₂ ⟩ )
          → ∥ Below ∥₁
    inner q (inl h) = ∣ inr (q , inl h) ∣₁
    inner q (inr (q' , h)) =
```

<!--en-->
In the parameter case, `LexAt-out` supplies only `∥ Differs ∥₁`, exactly as the
existential semantics requires. `PT.map` sends each locally represented
`Differs` record to the third case of `Below`, adjoining the already known code
and arity equalities. The result remains under one propositional truncation, so
the conversion carries existence to existence and never asks for a chosen
first-difference witness.
<!--zh-->
在参数分支中，`LexAt-out` 只给出 `∥ Differs ∥₁`，恰好保留存在语义所要求的边界。`PT.map` 把其中每一份局部出现的 `Differs` 记录映到 `Below` 的第三种情形，并附上已经取得的码等式与元数等式。结果仍处于一层命题截断之下，因此这次转换只是把存在带到存在，从不要求选定一份首次相异见证。
<!--ja-->
パラメータの場合、`LexAt-out` が与えるのは `∥ Differs ∥₁` だけであり、存在の意味論が要求する境界を正確に保っています。`PT.map` は、その中で局所的に表された各 `Differs` の記録を `Below` の第三の場合へ写し、すでに得られた符号とアリティの等しさを付け加えます。結果は一つの命題的切り詰めの下に留まるので、この変換は存在を存在へ移すだけで、最初の相違の証人を選ぶことはありません。
<!--/-->

```agda
      PT.map (λ u → inr (q , inr (q' , u))) (LexAt-out P a₁ e₁ e₂ γ h)

```

<!--en-->
The type of `outer` is the semantic split at the first comparison key. Its left
side is satisfaction of the application of `R` to the two skeleton slots; its
right side retains the equality `s₂ = s₁` together with satisfaction of the
remaining arity-or-parameter disjunction. Decoding the left side yields the
code case of `Below`, while eliminating the inner disjunction uses `inner`.
This two-stage reading mirrors the nesting of `≺At` and keeps the final result
at `∥ Below ∥₁`, where neither disjunction is turned into a chosen branch.
<!--zh-->
`outer` 的类型正是第一个比较键处的语义分支。左侧是关系 `R` 对两个骨架位置之应用的满足关系；右侧则保留等式 `s₂ = s₁`，并带有余下「元数或参数」析取的满足关系。解码左侧便得到 `Below` 的码分支，消去内层析取则调用 `inner`。这两阶段读取与 `≺At` 的嵌套结构相互对应，并始终把最终结果留在 `∥ Below ∥₁` 中，不把任何一层析取变成被选定的分支。
<!--ja-->
`outer` の型は、最初の比較の鍵で生じる意味論的な分岐をそのまま表します。左側は関係 `R` を二つの骨格のスロットへ適用した論理式の充足関係であり、右側は等しさ`s₂ = s₁` と、残る「アリティまたはパラメータ」の選言の充足関係を保ちます。左側を復号すれば `Below` の符号の場合が得られ、内側の選言の消去には `inner` を使います。この二段階の読みは `≺At` の入れ子に対応し、最終結果を`∥ Below ∥₁` に留めるので、どちらの選言も選ばれた枝として外へ出ません。
<!--/-->

```agda
    outer : ⟨ γ ⊨ appAt R s₁ s₂ ⟩
          ⊎ ( (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
            × ⟨ γ ⊨ ( (var a₁ ∈̇ var a₂)
                    ∨̇ ( (var a₂ ≐ var a₁) ∧̇ LexAt P a₁ e₁ e₂ ) ) ⟩ )
          → ∥ Below ∥₁
```

<!--en-->
The last two clauses finish the outward reading of the comparison. In the code
branch, `appAt-adequate` converts satisfaction of the relation application into
membership of the ordered pair of skeleton codes in `R`, producing the first
case of `Below`. In the equal-code branch, the inner object-language
disjunction is still propositionally truncated, so it is eliminated only into
`∥ Below ∥₁`. Thus every one of the three comparison keys can be recovered, but
the formula does not reveal which key decided the comparison outside the
truncation.
<!--zh-->
最后两个分支完成对比较的向外读取。在码分支中，`appAt-adequate` 把关系应用的满足关系转换成「两个骨架码组成的有序对属于 `R`」，从而得到 `Below` 的第一种情形。在码相等的分支中，内层对象语言析取仍处于命题截断之下，因此只能将它消去到 `∥ Below ∥₁` 中。这样，三个比较键中的任一情形都能被读回，但在截断之外，公式不会显露究竟是哪一个键决定了比较。
<!--ja-->
最後の二つの節で、比較を外向きに読む仕事が完了します。符号の場合には、`appAt-adequate` が関係の適用についての充足関係を、骨格の二つの符号からなる順序対が `R` に属すという主張へ変換し、`Below` の第一の場合を与えます。符号が等しい場合には、内側の対象言語の選言がなお命題的切り詰めの下にあるため、それを消去できる行き先は `∥ Below ∥₁` だけです。したがって三つの比較の鍵のどの場合も読み戻せますが、切り詰めの外で、どの鍵が比較を決めたかを取り出すことはありません。
<!--/-->

```agda
    outer (inl h) = ∣ inl (subst ⟨_⟩ (appAt-adequate R s₁ s₂ γ) h) ∣₁
    outer (inr (q , h)) = PT.rec squash₁ (inner q) h

```

<!--en-->
To describe the comparison of two least names, the body of the step needs six
fresh slots. The first three indices are fixed here: `s6a`, `a6a`, and `e6a`
refer respectively to the first name's skeleton code, arity numeral, and
parameter environment. After all six binders have been entered, these data lie
at de Bruijn positions five, four, and three. Giving the positions names keeps
the later formulas about leastness and comparison readable while leaving the
binder arithmetic in one place.
<!--zh-->
为了描述两个最小名字之间的比较，步进的公式体需要六个新槽位。这里先固定前三个索引：`s6a`、`a6a` 与 `e6a` 分别指向第一个名字的骨架码、元数数码与参数环境。进入全部六层绑定以后，这三项数据位于 de Bruijn 的第五、第四与第三位。为这些位置命名，使后面的最小性公式和比较公式保持可读，也把绑定位置的计算集中在一处。
<!--ja-->
二つの最小の名前を比較する記述には、本体の中に六つの新しいスロットが必要です。ここでは最初の三つの添字を定めます。`s6a`、`a6a`、`e6a` はそれぞれ、第一の名前の骨格の符号、アリティの数項、パラメータ環境を指します。六つの束縛子をすべて通過した後では、これらは de Bruijn 添字の第五、第四、第三の位置にあります。位置に名前を付けておけば、後の最小性と比較の論理式を読みやすく保ちながら、束縛位置の計算を一か所に集められます。
<!--/-->

```agda
private
  s6a a6a e6a s6b a6b e6b : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  s6a = suc (suc (suc (suc (suc zero))))
  a6a = suc (suc (suc (suc zero)))
  e6a = suc (suc (suc zero))
```

<!--en-->
The remaining indices `s6b`, `a6b`, and `e6b` point to positions two, one,
and zero, where the second name's data will be found. This reversal is the
usual de Bruijn effect: the witnesses are bound in the order
`s₁,a₁,e₁,s₂,a₂,e₂`, while each new witness is prepended to the environment.
Consequently the fully extended environment is
`e₂ ∷ a₂ ∷ s₂ ∷ e₁ ∷ a₁ ∷ s₁ ∷ γ`, and the six indices select precisely the
two intended triples.
<!--zh-->
余下的索引 `s6b`、`a6b` 与 `e6b` 指向第二、第一与第零位，第二个名字的数据将落在这里。这种反转来自 de Bruijn 表示的通常规律：见证按 `s₁,a₁,e₁,s₂,a₂,e₂` 的次序绑定，而每个新见证都添加在环境的最前端。因此，完全扩张后的环境是 `e₂ ∷ a₂ ∷ s₂ ∷ e₁ ∷ a₁ ∷ s₁ ∷ γ`，六个索引恰好分别选中预定的两个三元组。
<!--ja-->
残る添字 `s6b`、`a6b`、`e6b` は第二、第一、第零の位置を指し、そこに第二の名前のデータが置かれます。この反転は de Bruijn 表現に伴う通常の現象です。証人は `s₁,a₁,e₁,s₂,a₂,e₂` の順に束縛されますが、新しい証人はそのたびに環境の先頭へ加えられます。したがって、すべての束縛を加えた環境は `e₂ ∷ a₂ ∷ s₂ ∷ e₁ ∷ a₁ ∷ s₁ ∷ γ` となり、六つの添字が意図した二つの三つ組を正確に選びます。
<!--/-->

```agda
  s6b = suc (suc zero)
  a6b = suc zero
  e6b = zero

```

<!--en-->
A least name is expressed as a property of name data already occupying the
slots `s`, `a`, and `e`. Its first conjunct requires those data to satisfy
`NameAt` and hence to denote `d`. The second conjunct universally quantifies
over a competing skeleton code, arity numeral, and parameter environment. The
three nested universals place that competitor at positions two, one, and zero,
while `sh3` keeps the carrier, both code sets, and the denotation `d` referring
to their original slots.
<!--zh-->
最小名字被表达为已经占据 `s`、`a` 与 `e` 三个槽位的一组名字数据所具有的性质。第一个合取项要求这组数据满足 `NameAt`，因而指称 `d`。第二个合取项全称量化一个竞争者的骨架码、元数数码与参数环境。三层全称量词把该竞争者放在第二、第一与第零位，而 `sh3` 使载体、两个码集以及指称 `d` 仍指向原来的槽位。
<!--ja-->
最小の名前は、すでに `s`、`a`、`e` のスロットを占める名前のデータが満たす性質として表されます。第一の連言は、そのデータが `NameAt` を満たし、したがって `d` を表示することを要求します。第二の連言は、競合する骨格の符号、アリティの数項、パラメータ環境を全称量化します。三つの全称量化子は競合する三つ組を第二、第一、第零の位置に置き、`sh3` は台、二つの符号集合、表示 `d` への参照を元のスロットに保ちます。
<!--/-->

```agda
LeastNameAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n
            → Fin n → Fin n → Fin n → Fin n → Formula S n
LeastNameAt R P B C C₀ s a e d =
  NameAt B C C₀ s a e d
  ∧̇ ∀̇ (∀̇ (∀̇ ( NameAt (sh3 B) (sh3 C) (sh3 C₀)
```

<!--en-->
The implication restricts attention to competitors that are also names of the
same `d`; names denoting other sets are irrelevant to this minimum. Its
conclusion negates `≺At competitor current`, so no competing name of `d`
strictly precedes the current one in the three-key order. This formula only
states leastness. It neither searches for a name nor removes a propositional
truncation to select one. The explicit least-name construction belongs to the
meta-language naming development and uses its excluded-middle hypothesis.
<!--zh-->
蕴涵的前件把范围限制在同样指称 `d` 的竞争名字上；指称其他集合的名字与这里的最小性无关。其后件否定 `≺At competitor current`，所以 `d` 的任何竞争名字都不会在三键序中严格先于当前名字。这个公式只陈述最小性，既不搜索名字，也不通过消去命题截断来选出名字。明确的最小名字构造属于元语言中的命名理论，并使用其中的排中律假设。
<!--ja-->
含意の前件は、同じ `d` を表示する競合する名前だけに対象を限ります。別の集合を表示する名前は、この最小性には関係しません。後件は `≺At competitor current` を否定するので、`d` のどの競合する名前も、三つの鍵による順序で現在の名前に狭義に先行しません。この論理式は最小性を述べるだけです。名前を探索することも、命題的切り詰めを消去して一つを選ぶこともありません。明示的な最小の名前の構成はメタ言語の命名理論に属し、そこで排中律の仮定を用います。
<!--/-->

```agda
                      (suc (suc zero)) (suc zero) zero (sh3 d)
             ⇒̇ ¬̇ (≺At (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
                        (sh3 s) (sh3 a) (sh3 e)) )))

```

<!--en-->
Repeated existential elimination will need to change the property carried by a
witness without choosing that witness globally. The helper `exists-map`
captures exactly this operation. If each `B x` gives merely a `C x`, then mere
existence of a pair `(x , B x)` gives mere existence of `(x , C x)`. The outer
`PT.rec` eliminates the original propositional truncation into another
propositionally truncated type, and the inner `PT.map` retains the same `x`
while transforming its second component. At no point does the result expose a
particular witness of `A`.
<!--zh-->
反复消去存在量词时，需要改变见证所携带的性质，却不能在全局选出这个见证。辅助函数 `exists-map` 恰好概括这一操作。若每个 `B x` 都仅仅给出一个 `C x`，那么 `(x , B x)` 的仅仅存在便推出 `(x , C x)` 的仅仅存在。外层 `PT.rec` 把原来的命题截断消去到另一个命题截断类型中，内层 `PT.map` 则保留同一个 `x`，同时改造其第二分量。整个结果始终不会暴露 `A` 中的某个特定见证。
<!--ja-->
存在量化子を繰り返し消去するときには、証人を大域的に選ぶことなく、その証人が携える性質を変換する必要があります。補助関数 `exists-map` は、まさにこの操作を表します。各 `B x` から単に `C x` が得られるなら、対 `(x , B x)` が単に存在することから、対 `(x , C x)` が単に存在することが従います。外側の `PT.rec` は元の命題的切り詰めを別の命題的切り詰められた型へ消去し、内側の `PT.map` は同じ `x` を保ったまま第二成分を変換します。結果が `A` の特定の証人を外へ示すことはありません。
<!--/-->

```agda
private
  exists-map : {A : Type (ℓ-suc ℓ)} {B C : A → Type (ℓ-suc ℓ)}
             → ((x : A) → B x → ∥ C x ∥₁)
             → ∥ Σ A B ∥₁ → ∥ Σ A C ∥₁
  exists-map f = PT.rec squash₁ (λ { (x , h) → PT.map (x ,_) (f x h) })
```

<!--en-->
The operator `∃₆` binds six object-language variables around an arbitrary
body. Its intended use is to supply the two triples of data needed for two
names, but the operator itself does not mention names, leastness, or an order.
Keeping this binder frame separate lets its semantic introduction and
elimination rules be proved once for any formula with six additional free
positions; the mathematical conditions on the witnesses will be supplied by
`StepBody`.
<!--zh-->
算子 `∃₆` 在任意公式体外依次绑定六个对象语言变元。它将用于提供两个名字所需的两组三元数据，但算子本身并不提及名字、最小性或序。把这层绑定框架单独定义，就能对任何多出六个自由位置的公式统一给出语义上的引入与消去读法；见证必须满足的数学条件随后由 `StepBody` 提供。
<!--ja-->
演算子 `∃₆` は、任意の本体の外側で六つの対象言語の変数を順に束縛します。これは二つの名前に必要な二組の三つ組を与えるために使われますが、演算子自体は名前、最小性、順序のいずれにも言及しません。この束縛の枠を独立させることで、自由な位置が六つ多い任意の論理式について、意味論的な導入と消去の読みを一度だけ与えられます。証人に課される数学的条件は、後で `StepBody` が与えます。
<!--/-->

```agda

∃₆ : ∀ {n} → Formula S (suc (suc (suc (suc (suc (suc n)))))) → Formula S n
∃₆ φ = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ φ)))))

```

<!--en-->
For a body `φ` and an environment `γ`, `Six` records the untruncated data that
can introduce the six existentials: witnesses `s₁,k₁,p₁,s₂,k₂,p₂` together
with satisfaction of `φ`. The names `k` and `p` anticipate their later roles
as arity numerals and parameter environments; at this generic stage they are
simply elements of the carrier `S`. Since successive binders prepend their
witnesses, the satisfaction environment lists them in reverse order as
`p₂,k₂,s₂,p₁,k₁,s₁` before the original `γ`.
<!--zh-->
给定公式体 `φ` 与环境 `γ`，`Six` 记录能够引入六层存在量词的未截断数据：六个见证 `s₁,k₁,p₁,s₂,k₂,p₂`，以及 `φ` 的满足关系。字母 `k` 与 `p` 预示它们稍后将分别充当元数数码和参数环境；在这个通用定义中，它们还只是载体 `S` 的元素。由于每层绑定都把新见证添加到环境前端，满足关系所用的环境以相反次序列出它们，即在原环境 `γ` 前依次放置 `p₂,k₂,s₂,p₁,k₁,s₁`。
<!--ja-->
本体 `φ` と環境 `γ` に対して、`Six` は六つの存在量化子を導入するための、切り詰められていないデータを記録します。それは六つの証人 `s₁,k₁,p₁,s₂,k₂,p₂` と、`φ` の充足関係です。`k` と `p` という文字は、後にそれぞれアリティの数項とパラメータ環境として使われることを先取りしています。この一般的な定義の段階では、いずれも台 `S` の要素にすぎません。束縛子は新しい証人を順に環境の先頭へ加えるため、充足関係の環境では順序が反転し、元の `γ` の前に `p₂,k₂,s₂,p₁,k₁,s₁` と並びます。
<!--/-->

```agda
module _ {n : ℕ} (φ : Formula S (suc (suc (suc (suc (suc (suc n))))))) (γ : S ^ n)
         where
  Six : Type (ℓ-suc ℓ)
  Six = Σ[ s₁ ∈ S ] Σ[ k₁ ∈ S ] Σ[ p₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ k₂ ∈ S ] Σ[ p₂ ∈ S ]
          ⟨ (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) ⊨ φ ⟩
```

<!--en-->
The introduction rule starts with all six witnesses explicitly available in a
value of `Six`. It supplies them to the six existential binders in their
binding order, wrapping the remaining satisfaction proof in the propositional
truncation contributed by each existential. No search or choice is involved:
the witnesses are input data. The nested constructors also explain why the
environment seen by the body has the reverse order recorded in the definition
of `Six`.
<!--zh-->
引入读法从 `Six` 的一个值出发，其中六个见证都已明确给出。它依绑定次序把这些见证交给六层存在量词，并逐层将余下的满足关系证明放入相应存在量词带来的命题截断中。这里不需要搜索或选择，因为见证本来就是输入数据。嵌套的构造子也说明了为何公式体所见的环境具有 `Six` 定义中记录的反向次序。
<!--ja-->
導入の読みは、六つの証人がすべて明示された `Six` の値から始まります。それらを束縛の順に六つの存在量化子へ渡し、残る充足関係の証明を、各存在量化子がもたらす命題的切り詰めの中へ一層ずつ包みます。証人は入力データとしてすでに与えられているので、探索も選択も必要ありません。入れ子になった構成子から、本体が見る環境が `Six` の定義に記された逆順になる理由も読み取れます。
<!--/-->

```agda

  ∃₆-in : Six → ⟨ γ ⊨ ∃₆ φ ⟩
  ∃₆-in (s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , h)))))) =
    ∣ s₁ , ∣ k₁ , ∣ p₁ , ∣ s₂ , ∣ k₂ , ∣ p₂ , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

```

<!--en-->
The outward rule begins with satisfaction of the six-fold existential and
must end in `∥ Six ∥₁`, rather than in an exposed six-tuple. Each use of
`exists-map` crosses one existential layer while retaining its locally
available witness inside the common propositional target. The chain handles
`s₁`, `k₁`, `p₁`, `s₂`, and `k₂` in turn. At the innermost layer, `PT.map`
passes the pair consisting of `p₂` and the body's satisfaction proof into the
same final truncated payload.
<!--zh-->
向外读式从六重存在公式的满足关系出发，其终点必须是 `∥ Six ∥₁`，而不能是暴露在截断之外的六元组。每次调用 `exists-map` 都跨过一层存在量词，并把该层局部可用的见证保留在共同的命题目标中。这条链依次处理 `s₁`、`k₁`、`p₁`、`s₂` 与 `k₂`；到最内层时，`PT.map` 把由 `p₂` 与公式体满足关系证明组成的那一对送入同一个最终截断载荷。
<!--ja-->
外向きの読みは、六重の存在量化についての充足関係から始まり、切り詰めの外に現れた六つ組ではなく `∥ Six ∥₁` を行き先とします。`exists-map` を一度使うたびに存在量化子を一層通過し、その層で局所的に得られた証人を共通の命題的な行き先の内側に保ちます。この連鎖は `s₁`、`k₁`、`p₁`、`s₂`、`k₂` を順に扱います。最も内側では、`PT.map` が `p₂` と本体の充足関係の証明からなる対を、同じ最終的な切り詰められた中身へ送ります。
<!--/-->

```agda
  ∃₆-out : ⟨ γ ⊨ ∃₆ φ ⟩ → ∥ Six ∥₁
  ∃₆-out = exists-map (λ s₁ →
    exists-map (λ k₁ →
      exists-map (λ p₁ →
        exists-map (λ s₂ →
```

<!--en-->
After the fifth application of `exists-map`, the innermost existential already
has the shape needed for the last component, so the identity map suffices.
Together, `∃₆-in` and `∃₆-out` express the semantic content of the binder frame
with the correct asymmetry: explicit six-witness data introduces the formula,
whereas satisfaction of the formula yields only the mere existence of such
data. This generic result can now be specialized without reopening any of the
six truncations.
<!--zh-->
第五次应用 `exists-map` 之后，最内层存在量词已经具有最后一个分量所需的形状，因此恒等映射便已足够。`∃₆-in` 与 `∃₆-out` 合起来，以正确的不对称方式刻画这层绑定框架的语义内容：包含六个明确见证的数据可以引入公式，而从公式的满足关系向外读取时，只能得到这种数据的仅仅存在。下面可把这一通用结论用于具体公式体，无须重新打开任何一层截断。
<!--ja-->
五回目の `exists-map` の後では、最も内側の存在量化が最後の成分に必要な形をすでにもつため、恒等写像で十分です。`∃₆-in` と `∃₆-out` は合わせて、束縛の枠の意味論的内容を正しい非対称性のもとで表します。明示的な六つの証人のデータから論理式を導入できますが、論理式の充足関係から得られるのは、そのようなデータが単に存在することだけです。これで、六つの切り詰めを開き直すことなく、この一般的な結果を具体的な本体へ適用できます。
<!--/-->

```agda
          exists-map (λ k₂ → PT.map (λ p → p))))))

```

<!--en-->
The concrete body places three conditions on the two triples selected by the
six indices. The first triple must satisfy `LeastNameAt` for `x`, and the
second must satisfy it for `y`. Both use the same carrier and the same code
sets, while `R` and `P` provide the two relation slots used by name comparison.
All seven surrounding slots are shifted by `sh6`, since the body reads them
through the six newly bound witnesses.
<!--zh-->
具体的公式体对六个索引选出的两组三元数据施加三个条件。第一组三元数据必须满足关于 `x` 的 `LeastNameAt`，第二组必须满足关于 `y` 的 `LeastNameAt`。两者使用同一个载体与同一对码集，而 `R` 和 `P` 提供名字比较所需的两个关系槽位。公式体要越过六个新绑定的见证读取外围七个槽位，因此这些槽位都经 `sh6` 移位。
<!--ja-->
具体的な本体は、六つの添字が選ぶ二組の三つ組に三つの条件を課します。第一の三つ組は `x` について `LeastNameAt` を満たし、第二の三つ組は `y` についてそれを満たさなければなりません。両者は同じ台と同じ二つの符号集合を使い、`R` と `P` が名前の比較に必要な二つの関係スロットを与えます。本体は六つの新しい証人を越えて外側の七つのスロットを読むため、それらへの参照はすべて `sh6` で移されます。
<!--/-->

```agda
StepBody : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
         → Formula S (suc (suc (suc (suc (suc (suc n))))))
StepBody R P B C C₀ x y =
    LeastNameAt (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀) s6a a6a e6a (sh6 x)
  ∧̇ ( LeastNameAt (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀) s6b a6b e6b (sh6 y)
```

<!--en-->
The third condition compares the two triples with `≺At`, placing the name of
`x` strictly before the name of `y`. Hence `StepBody` says precisely that two
least names over one carrier have been supplied and that the first precedes
the second in the three-key name order. It contains no comparison of the
stages at which `x` and `y` are born, no outer recursive table, and no claim
that the represented relation is well-founded. Those belong to the larger
construction in which this one-step description is used.
<!--zh-->
第三个条件用 `≺At` 比较两组三元数据，使 `x` 的名字在三键名字序中严格先于 `y` 的名字。因此，`StepBody` 所说的恰是：在同一个载体上已经给出两个最小名字，且第一个先于第二个。它不比较 `x` 与 `y` 的诞生层，不包含外层递归表，也不主张所表示的关系具有良基性；这些内容属于使用这条单步描述的更大构造。
<!--ja-->
第三の条件は二組の三つ組を `≺At` で比較し、`x` の名前を `y` の名前より三つの鍵による名前順序で狭義に前へ置きます。したがって `StepBody` が述べるのは、同じ台の上で二つの最小の名前が与えられ、第一の名前が第二の名前に先行することです。`x` と `y` が生まれる段階の比較も、外側の再帰的な表も、表現された関係が整礎的であるという主張も含みません。それらは、この一ステップの記述を用いる、より大きな構成に属します。
<!--/-->

```agda
    ∧̇ ≺At (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b )

```

<!--en-->
`StepAt` closes `StepBody` with the six existential binders. As an
object-language formula, it asserts merely that there are data for a least
name of `x`, data for a least name of `y`, and a comparison placing the first
before the second. The formula describes this single comparison branch; it
does not itself produce either least name, perform the surrounding stage
recursion, or prove well-foundedness. Its existential semantics also means
that reading a satisfied `StepAt` outward must preserve propositional
truncation.
<!--zh-->
`StepAt` 用六层存在量词封闭 `StepBody`。作为一条对象语言公式，它断言的只是：存在 `x` 的一个最小名字的数据、`y` 的一个最小名字的数据，以及使前者先于后者的比较。公式描述这一种比较情形；它本身不产生任何一个最小名字，不执行外围的层递归，也不证明良基性。存在量词的语义还意味着，从一个已满足的 `StepAt` 向外读取时必须保留命题截断。
<!--ja-->
`StepAt` は、六つの存在量化子で `StepBody` を閉じます。対象言語の論理式として主張するのは、`x` の最小の名前のデータ、`y` の最小の名前のデータ、そして前者を後者より前に置く比較が単に存在することです。この論理式が記述するのは、この一つの比較の場合です。それ自体が最小の名前を作ることも、周囲の段階についての再帰を実行することも、整礎性を証明することもありません。また、存在量化の意味論により、充足された `StepAt` を外向きに読む際には命題的切り詰めを保つ必要があります。
<!--/-->

```agda
StepAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
       → Formula S n
StepAt R P B C C₀ x y = ∃₆ (StepBody R P B C C₀ x y)

```

<!--en-->
For fixed slots and environment, `StepOf` specializes the generic type `Six`
to `StepBody`. An element therefore contains six explicit carrier elements and
a proof that, in the reversed extended environment, they satisfy the two
least-name conditions and the name comparison. Naming this untruncated payload
separates it from the proposition expressed by `StepAt`: the following
introduction rule can consume a `StepOf` directly, while the outward rule can
return only `∥ StepOf ∥₁`. This is the precise witness boundary of the
six-binder step formula.
<!--zh-->
固定各槽位与环境以后，`StepOf` 把通用类型 `Six` 特化到 `StepBody`。因此，它的一个元素包含六个明确的载体元素，以及一份证明，说明它们在反向扩张的环境中满足两个最小名字条件与名字比较。为这份未截断载荷取名，也把它同 `StepAt` 所表达的命题区分开来：随后的引入读法可以直接使用一个 `StepOf`，而向外读式只能返回 `∥ StepOf ∥₁`。这正是六重绑定步进公式的见证边界。
<!--ja-->
スロットと環境を固定すると、`StepOf` は一般的な型 `Six` を `StepBody` に特殊化します。したがってその要素は、台の六つの明示的な要素と、それらが逆順に拡張された環境で二つの最小の名前の条件および名前の比較を満たすことの証明を含みます。この切り詰められていない中身に名前を付けることで、`StepAt` が表す命題との違いも明確になります。続く導入の読みは `StepOf` を直接使えますが、外向きの読みが返せるのは `∥ StepOf ∥₁` だけです。これが六つの束縛子をもつステップの論理式における証人の境界です。
<!--/-->

```agda
module _ {n : ℕ} (R P B C C₀ x y : Fin n) (γ : S ^ n) where
  StepOf : Type (ℓ-suc ℓ)
  StepOf = Six (StepBody R P B C C₀ x y) γ

```

<!--en-->
With the six witnesses and the proof of the body already present in `StepOf`,
the introduction direction is immediate. Each witness is placed under its
existential quantifier in binding order, so the resulting assignment satisfies
`StepAt`. This step uses the supplied proofs of the two least-name conditions
and of the comparison; it does not construct any name.
<!--zh-->
`StepOf` 已经给出六个见证以及公式体的证明，因此引入方向可以直接完成。各见证依绑定次序放入相应的存在量词之下，所得赋值便满足 `StepAt`。这里使用已经给出的两项最小名字条件及比较的证明，并不构造任何名字。
<!--ja-->
`StepOf` には六つの証人と本体の証明がすでに含まれているので、導入の向きは直ちに得られます。各証人を束縛の順に対応する存在量化子の下へ入れると、得られた割り当ては `StepAt` を満たします。ここでは与えられた二つの最小の名前の条件と比較の証明を使うだけで、名前そのものは構成しません。
<!--/-->

```agda
  StepAt-in : StepOf → ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
  StepAt-in = ∃₆-in (StepBody R P B C C₀ x y) γ

```

<!--en-->
In the converse direction, satisfaction of `StepAt` can be unpacked only as
`∥ StepOf ∥₁`. Thus there merely exist two triples satisfying the two
least-name formulas, together with satisfaction of the comparison formula
from the first triple to the second. The
propositional truncation preserves this existence while withholding the six
particular witnesses, exactly as required by the semantics of existential
quantification.
<!--zh-->
反向读取时，`StepAt` 的满足关系只能拆成 `∥ StepOf ∥₁`。因此所得结论是：仅仅存在两组三元数据，分别满足两项最小名字公式，并且从前者到后者的比较公式得到满足。命题截断保留这项存在事实，却不暴露六个具体见证，这正符合存在量词的语义。
<!--ja-->
逆向きには、`StepAt` の充足関係から取り出せるのは `∥ StepOf ∥₁` までです。したがって、二つの最小の名前の論理式をそれぞれ満たす二組の三つ組と、第一の三つ組から第二の三つ組への比較の論理式の充足とは、単に存在するにとどまります。命題的切り詰めはこの存在を保ちながら六つの具体的な証人を隠し、存在量化の意味論にちょうど対応します。
<!--/-->

```agda
  StepAt-out : ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩ → ∥ StepOf ∥₁
  StepAt-out = ∃₆-out (StepBody R P B C C₀ x y) γ
```

<!--en-->
## Against the names the meta-language built
<!--zh-->
## 对着元语言造出的诸名字
<!--ja-->
## メタ言語が構成した名前との対応
<!--/-->

<!--en-->
To compare the formula with the intended meta-level relation, fix a
constructible set `A` and a strict well-order `w` on its carrier `⟪ A ⟫`.
Names over `A` take every parameter from this carrier, so `w` supplies exactly
the order needed for their parameter vectors. The resulting adequacy argument
is relative to these data and therefore applies to any constructible set
equipped with such an order on its carrier.
<!--zh-->
为了把公式同预期的元层关系比较，固定一个可构造集 `A`，并在其载体 `⟪ A ⟫` 上固定严格良序 `w`。`A` 上名字的每个参数都取自这个载体，因此 `w` 恰好给出参数向量所需的序。以下充分性论证相对于这些数据成立，故适用于任何在自身载体上配有这种序的可构造集。
<!--ja-->
論理式を意図したメタレベルの関係と比較するため、構成可能集合 `A` と、その台 `⟪ A ⟫` 上の狭義整列順序 `w` を固定します。`A` 上の名前の各パラメータはこの台から取られるので、`w` がパラメータ列の比較に必要な順序を正確に与えます。以下の妥当性はこれらのデータに相対的であり、その台にこのような順序を備えた任意の構成可能集合に適用できます。
<!--/-->

```agda
module Adequacy (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
  private
    module NM = Naming A w

```

<!--en-->
The naming construction now provides the type `Name` and the comparisons to be
matched. A name of arity `k` contains a parameter-free formula with `suc k`
variable positions and a vector of exactly `k` parameters. Its formula code is
derived from that formula, and `_≺ₙ_` compares names by code first, arity
second, and parameter vector last. Renaming the relation of `w` to `_≺ₚ_`
simply records its role as the parameter order.
<!--zh-->
命名构造给出类型 `Name` 以及此处要对照的比较。元数为 `k` 的名字包含一条有 `suc k` 个变元位置的无参公式，以及一个恰有 `k` 个参数的向量。公式码由该公式派生，而 `_≺ₙ_` 依次比较名字的码、元数与参数向量。把 `w` 的关系改记为 `_≺ₚ_`，只是标明它在这里充当参数序。
<!--ja-->
ここで命名の構成から、型 `Name` と照合すべき比較が得られます。アリティが `k` の名前は、`suc k` 個の変数位置をもつ無パラメータ論理式と、ちょうど `k` 個のパラメータからなるベクトルを含みます。論理式の符号はその論理式から導かれ、`_≺ₙ_` はまず符号、次にアリティ、最後にパラメータ列を比較します。`w` の関係を `_≺ₚ_` と書き換えるのは、ここでの役割がパラメータ順序であることを示すためです。
<!--/-->

```agda
  open NM using ( Name; arity; params; codeOf; _≺ᵥ_; _≺ₙ_ )
  open SWO w using () renaming ( _<∙_ to _≺ₚ_ )

```

<!--en-->
The recursive vector order is compared with an explicit first-difference
relation `Lex`. For two vectors of the same length, `Lex p q` chooses an index
`i`, requires the entry of `p` there to precede the entry of `q` under
`_≺ₚ_`, and requires equality of the entries at every `j` with `j<i`. Unlike
the object-language agreement formula, this meta-level relation can state
entry equality directly and needs no common graph value as an intermediary.
<!--zh-->
为了同递归定义的向量序比较，先写出显式的首次相异关系 `Lex`。对两个等长向量，`Lex p q` 选取一个序号 `i`，要求 `p` 在该处的条目按 `_≺ₚ_` 先于 `q` 的条目，并要求每个 `j<i` 处的条目相等。不同于对象语言中的相符公式，这个元层关系可以直接陈述条目相等，无须以共同的图取值为中介。
<!--ja-->
再帰的に定義されたベクトル順序と比較するため、最初の相違を明示する関係 `Lex` を置きます。同じ長さの二つのベクトルについて、`Lex p q` は添字 `i` を選び、その位置で `p` の成分が `_≺ₚ_` により `q` の成分に先行し、すべての `j<i` では両成分が等しいことを要求します。対象言語の一致を表す論理式とは異なり、このメタレベルの関係は成分の等しさを直接述べられるため、共通のグラフ値を仲介させる必要がありません。
<!--/-->

```agda
  Lex : ∀ {k} → Vec ⟪ A ⟫ k → Vec ⟪ A ⟫ k → Type (ℓ-suc ℓ)
  Lex {k} p q = Σ[ i ∈ Fin k ]
    ( (lookup i p ≺ₚ lookup i q)
    × ((j : Fin k) → toℕ j < toℕ i → lookup j p ≡ lookup j q) )

```

<!--en-->
The map from `Lex` to the recursive order follows the location of the first
difference. At index zero, the strict comparison of the heads is already the
first clause of `_≺ᵥ_`. At a successor index, agreement below that index makes
the two heads equal, while the same witness with its index decreased compares
the tails. This is structural recursion on the vectors and uses no classical
principle.
<!--zh-->
从 `Lex` 到递归向量序的方向依首次相异所在的位置展开。序号为零时，头部的严格比较正是 `_≺ᵥ_` 的第一种情形。序号为后继时，相异位置以下的相等先给出两个头部相等；再把同一个见证的序号减一，便得到尾部之间的比较。这是对向量的结构递归，不使用任何经典原理。
<!--ja-->
`Lex` から再帰的なベクトル順序への向きは、最初の相違の位置に従います。添字が零なら、先頭どうしの狭義の比較がそのまま `_≺ᵥ_` の第一の場合です。添字が後続なら、それより下での一致から二つの先頭が等しいことが分かり、同じ証人の添字を一つ下げると尾どうしの比較が得られます。これはベクトルについての構造的再帰であり、古典的原理を用いません。
<!--/-->

```agda
  lex-vec : ∀ {k} (p q : Vec ⟪ A ⟫ k) → Lex p q → p ≺ᵥ q
  lex-vec (x ∷ p) (y ∷ q) (zero  , (h , _)) = inl h
  lex-vec (x ∷ p) (y ∷ q) (suc i , (h , ag)) =
    inr (ag zero (suc-≤-suc zero-≤) , lex-vec p q (i , (h , λ j hj → ag (suc j) (suc-≤-suc hj))))

```

<!--en-->
For the reverse map, follow the two clauses of `_≺ᵥ_`. An order proof for two
empty vectors is impossible. If the nonempty vectors are ordered because their
heads are strictly ordered, index zero witnesses `Lex`; no smaller index
exists, so the agreement condition is vacuous.
<!--zh-->
反向映射沿 `_≺ᵥ_` 的两种情形展开。两个空向量之间的序关系不可能成立。若两个非空向量因头部严格有序而被比较，序号零便见证 `Lex`；零以下没有序号，所以相等条件自动成立。
<!--ja-->
逆向きの写像は `_≺ᵥ_` の二つの場合に従います。二つの空ベクトルの間に順序の証明がある場合は不可能です。空でない二つのベクトルが先頭どうしの狭義の順序によって比較されているなら、添字零が `Lex` の証人になります。零より小さい添字はないので、一致の条件は空虚に成り立ちます。
<!--/-->

```agda
  vec-lex : ∀ {k} (p q : Vec ⟪ A ⟫ k) → p ≺ᵥ q → Lex p q
  vec-lex []      []      h = Empty.rec* h
  vec-lex (x ∷ p) (y ∷ q) (inl h) = zero , (h , λ j hj → Empty.rec (¬-<-zero hj))
  vec-lex (x ∷ p) (y ∷ q) (inr (e , h)) = suc (vec-lex p q h .fst)
    , ( vec-lex p q h .snd .fst
```

<!--en-->
In the remaining clause, the heads are equal and the tails are recursively
ordered. Applying the induction hypothesis to the tails yields their first
differing index; shifting it to a successor gives the corresponding index in
the original vectors. The supplied head equality proves agreement at position
zero, the first position below that shifted index.
<!--zh-->
余下的情形给出头部相等以及尾部的递归序关系。对尾部应用归纳假设，得到尾部首次相异的序号；把它提升为后继，就得到原向量中的对应序号。已有的头部等式证明位置零处相等，而位置零正是这个提升后序号以下的第一个位置。
<!--ja-->
残る場合には、先頭の等しさと、尾どうしの再帰的な順序が与えられます。尾に帰納法の仮定を適用して最初に異なる添字を得て、それを後続添字へ移せば、元のベクトルでの対応する位置になります。与えられた先頭の等しさが、移した添字より下にある最初の位置、すなわち位置零での一致を証明します。
<!--/-->

```agda
      , step )
    where
    step : (j : Fin (suc _)) → toℕ j < suc (toℕ (vec-lex p q h .fst))
         → lookup j (x ∷ p) ≡ lookup j (y ∷ q)
    step zero    _  = e
```

<!--en-->
At every other position below the shifted index, removing one successor from
the numerical inequality reduces the claim to the tails' own agreement. This
completes the reverse direction. Hence the explicit first-difference relation
and the recursive vector order coincide, allowing the parameter argument to
pass between their two presentations without changing the comparison.
<!--zh-->
对提升后序号以下的其余每个位置，从数值不等式两边各去掉一个后继，所需结论便化为尾部自身的相等条件。反向证明由此完成。因此，显式的首次相异关系与递归向量序相互等价，参数论证可以在这两种表述之间转换，而不改变所比较的关系。
<!--ja-->
移した添字より下にある残りの各位置では、数の不等式から両側の後続を一つずつ外すと、必要な主張は尾自身の一致へ帰着します。これで逆向きも完成します。したがって、明示的な最初の相違と再帰的なベクトル順序は同じ関係を表し、パラメータについての議論は比較を変えずに二つの表示を行き来できます。
<!--/-->

```agda
    step (suc j) hj = vec-lex p q h .snd .snd j (pred-≤-pred hj)
```

<!--en-->
## The parameters, on both sides
<!--zh-->
## 参数，两边各说一遍
<!--ja-->
## パラメータを双方向に読む
<!--/-->

<!--en-->
Formula codes are compared by a second pre-existing order. Each `codeOf t`
lies in the limit stage, whose strict well-order is `limitOrder`; writing its
relation as `_≺ˡ_` makes the code key explicit alongside the parameter key
`_≺ₚ_`. No new ordering is defined here: these are precisely the two orders
whose internal representations enter the three-key name comparison.
<!--zh-->
公式码由另一个已有的序比较。每个 `codeOf t` 都属于极限层，而该层上的严格良序是 `limitOrder`；把它的关系记为 `_≺ˡ_`，便可与参数键 `_≺ₚ_` 并列辨认码键。这里不定义新的序；三键名字比较所使用的正是这两个序在模型内的表示。
<!--ja-->
論理式の符号は、もう一つの既存の順序で比較されます。各 `codeOf t` は極限段階に属し、その上の狭義整列順序が `limitOrder` です。その関係を `_≺ˡ_` と書けば、パラメータの鍵 `_≺ₚ_` と並んで符号の鍵が明確になります。ここで新しい順序を定義するわけではありません。三つの鍵による名前の比較は、まさにこれら二つの順序のモデル内での表示を用います。
<!--/-->

```agda
  open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )

```

<!--en-->
A parameter is an element of the small carrier `⟪ A ⟫`, so it includes both an
underlying set and evidence that the set belongs to `A`. The map `ix` forgets
the membership evidence and retains the underlying set in `V`. This canonical
embedding is the common representation used when parameter values occur in
environment graphs and in ordered pairs belonging to the represented relation.
<!--zh-->
参数是小载体 `⟪ A ⟫` 的元素，因而同时含有一个底层集合以及该集合属于 `A` 的证据。映射 `ix` 忘去这份隶属证据，只保留 `V` 中的底层集合。参数值出现在环境图中，或出现在表示参数序的关系所含有序对中时，都采用这个典范嵌入像。
<!--ja-->
パラメータは小さな台 `⟪ A ⟫` の要素なので、台となる集合と、それが `A` に属すことの証拠をともに含みます。写像 `ix` はこの所属の証拠を忘れ、`V` 内の台となる集合だけを残します。パラメータの値を環境グラフに入れるときも、パラメータ順序を表す関係の順序対に入れるときも、この標準的な埋め込み像を用います。
<!--/-->

```agda
  ix : ⟪ A ⟫ → V ℓ
  ix m = ⟪ A ⟫↪ m

```

<!--en-->
The same underlying set can also be regarded as an element of the constructible
model. Since `A` is constructible and `ix m` belongs to `A`, transitivity of
constructibility shows that `ix m` is constructible. Pairing the set with this
proof gives `ixL m : S`, the form required when a parameter is used as an
object-language value.
<!--zh-->
同一个底层集合也可以视为可构造模型的元素。由于 `A` 可构造且 `ix m` 属于 `A`，可构造性的传递性说明 `ix m` 也可构造。把这个集合与该证明配对，便得到 `ixL m : S`，也就是参数充当对象语言取值时所需的形式。
<!--ja-->
同じ台となる集合は、構成可能モデルの要素としても扱えます。`A` が構成可能であり、`ix m` が `A` に属すので、構成可能性の推移性から `ix m` も構成可能です。この集合と証明を組にすると `ixL m : S` が得られ、パラメータを対象言語の値として使うための形になります。
<!--/-->

```agda
  ixL : ⟪ A ⟫ → S
  ixL m = ix m , isL-trans (∈∈ₛ {a = ix m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)) pA

```

<!--en-->
For a name `t`, the family `pfam t` reads its parameter vector pointwise. Its
domain is `Fin (arity t)`, and its value at `i` is the underlying `V`-set of
the parameter stored at that index. Thus the arity fixes the domain
definitionally, and the graph `env (pfam t)` gives the internal environment
representation of exactly that parameter vector.
<!--zh-->
对一个名字 `t`，族 `pfam t` 逐项读取其参数向量。它的定义域是 `Fin (arity t)`，在序号 `i` 处的值是该处参数的底层 `V` 集合。因此，元数依定义确定这个族的定义域，而图 `env (pfam t)` 恰好给出该参数向量在模型内的环境表示。
<!--ja-->
名前 `t` に対して、族 `pfam t` はそのパラメータベクトルを成分ごとに読みます。定義域は `Fin (arity t)` で、添字 `i` における値は、その位置に格納されたパラメータの台となる `V` の集合です。したがってアリティがこの族の定義域を定義上決め、グラフ `env (pfam t)` がそのパラメータベクトルのモデル内での環境表示を正確に与えます。
<!--/-->

```agda
  pfam : (t : Name) → Fin (arity t) → V ℓ
  pfam t i = ix (lookup i (params t))

```

<!--en-->
No information about a carrier element is lost by passing to its underlying
set. The canonical map `⟪ A ⟫↪` is an embedding, hence `ix u ≡ ix v` implies
`u ≡ v`. This injectivity is essential in the reverse parameter argument:
when two environment graphs share a value at an earlier index, equality of
their underlying `V`-sets can be read back as equality of the corresponding
entries of the parameter vectors.
<!--zh-->
把载体元素送到底层集合时不会丢失辨认该元素所需的信息。典范映射 `⟪ A ⟫↪` 是嵌入，因此 `ix u ≡ ix v` 蕴涵 `u ≡ v`。这项单射性是反向参数论证的关键：若两张环境图在较早序号处具有共同取值，就能把底层 `V` 集合的相等读回为两个参数向量相应条目的相等。
<!--ja-->
台の要素をその台となる集合へ移しても、要素を識別するための情報は失われません。標準写像 `⟪ A ⟫↪` は埋め込みなので、`ix u ≡ ix v` から `u ≡ v` が従います。この単射性はパラメータを逆向きに読む議論で欠かせません。二つの環境グラフが先行する添字で共通の値をもつとき、その台となる `V` の集合の等しさを、パラメータベクトルの対応する成分の等しさへ読み戻せます。
<!--/-->

```agda
  ix-inj : (u v : ⟪ A ⟫) → ix u ≡ ix v → u ≡ v
  ix-inj u v = isEmbedding→Inj isEmb⟪ A ⟫↪ u v

```

<!--en-->
It remains to state what the two internal relation sets must represent. For
codes, `Rrep` reads membership of the ordered pair of `u` and `v` in `Rs` as
`u ≺ˡ v`, while `Rfill` proves that membership from the comparison. For
parameters, `Prep` and `Pfill` give the same two directions between membership
of the pair of their `ix`-images in `Ps` and `u ≺ₚ v`. These four laws are
hypotheses. Under them, the three-key formula is adequate for any two
constructible relation sets with these representations; neither relation is
constructed here.
<!--zh-->
还须明确两个模型内关系集各自表示什么。对码而言，`Rrep` 把 `u` 与 `v` 的有序对属于 `Rs` 读为 `u ≺ˡ v`，`Rfill` 则从这项比较证明相应隶属。对参数而言，`Prep` 与 `Pfill` 同样在「两个 `ix` 像组成的有序对属于 `Ps`」与 `u ≺ₚ v` 之间给出两个方向。这四条表示律都是假设。在这些假设下，只要两个可构造关系集具有相应表示，三键公式便满足充分性；这里不构造其中任何一个关系。
<!--ja-->
最後に、モデル内の二つの関係集合がそれぞれ何を表すべきかを定めます。符号について、`Rrep` は `u` と `v` の順序対が `Rs` に属すことを `u ≺ˡ v` として読み、`Rfill` はこの比較からその所属を証明します。パラメータについても、`Prep` と `Pfill` が、二つの `ix` 像からなる順序対の `Ps` への所属と `u ≺ₚ v` の間の両方向を与えます。これら四つの表示則は仮定です。この仮定の下で、対応する表示をもつ任意の二つの構成可能な関係集合について三つの鍵の論理式は妥当になります。どちらの関係もここでは構成しません。
<!--/-->

```agda
  module Keys (Rs Ps : S)
              (Rrep : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩ → u ≺ˡ v)
              (Rfill : (u v : Limit) → u ≺ˡ v → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩)
              (Prep : (u v : ⟪ A ⟫) → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩ → u ≺ₚ v)
              (Pfill : (u v : ⟪ A ⟫) → u ≺ₚ v → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩)
```

<!--en-->
To apply the four representation laws to a particular parameter comparison,
fix two names together with the object-language slots in which their data are
read. The local argument is governed by five identifications: one for the
parameter relation, one for the first arity, one between the two arities, and
one for each parameter environment. Under these hypotheses, it will translate
between the explicit first difference `Lex` and the graph-based record
`Differs` in both directions.
<!--zh-->
为了把四条表示律用于一次具体的参数比较，固定两个名字，以及对象语言读取其数据的各个槽位。这个局部论证受五项等同支配：一项识别参数关系，一项识别第一个元数，一项等同两个元数，另有两项分别识别参数环境。在这些假设下，论证将在显式首次相异 `Lex` 与基于图的记录 `Differs` 之间作双向翻译。
<!--ja-->
四つの表示則を具体的なパラメータ比較に適用するため、二つの名前と、そのデータを対象言語で読むスロットを固定します。この局所的な議論を支える同一視は五つあります。パラメータ関係を定めるもの、第一のアリティを定めるもの、二つのアリティを等しくするもの、そして二つのパラメータ環境をそれぞれ定めるものです。これらの仮定のもとで、明示的な最初の相違 `Lex` とグラフによる記録 `Differs` を双方向に翻訳します。
<!--/-->

```agda
              where

```

<!--en-->
The first four identifications establish the common frame. The slot `P` holds
the relation set `Ps`; the slot `a₁` holds the numeral for `t₁`'s arity; and
`qk : arity t₂ ≡ arity t₁` makes the two parameter vectors comparable at one
length. Finally, `e₁` holds the graph of `pfam t₁`, whose value at an index is
the embedded parameter of the first name. Notice that `qk` is an equality of
natural-number arities, rather than an equation for an object-language slot.
<!--zh-->
前四项等同建立共同的比较框架。槽位 `P` 持有关系集 `Ps`；槽位 `a₁` 持有 `t₁` 的元数之数码；`qk : arity t₂ ≡ arity t₁` 则使两个参数向量能在同一个长度上比较。最后，`e₁` 持有 `pfam t₁` 的图，该族在每个序号处的值就是第一个名字的相应参数之嵌入像。须注意，`qk` 是两个自然数元数之间的等同，并不是某个对象语言槽位的等式。
<!--ja-->
最初の四つの同一視が、比較に共通する枠組みを定めます。スロット `P` は関係集合 `Ps` を持ち、スロット `a₁` は `t₁` のアリティの数項を持ちます。また `qk : arity t₂ ≡ arity t₁` によって、二つのパラメータベクトルを同じ長さで比較できます。最後に `e₁` は `pfam t₁` のグラフを持ち、その各添字での値は第一の名前の対応するパラメータの埋め込み像です。`qk` は自然数としての二つのアリティの等しさであり、対象言語のスロットを同定する式ではありません。
<!--/-->

```agda
    module _ {n : ℕ} (P a₁ e₁ e₂ : Fin n) (γ : S ^ n) (t₁ t₂ : Name)
             (qP : fst (lookup P γ) ≡ fst Ps)
             (qa : fst (lookup a₁ γ) ≡ # (arity t₁))
             (qk : arity t₂ ≡ arity t₁)
             (q₁ : fst (lookup e₁ γ) ≡ env (pfam t₁))
```

<!--en-->
The fifth identification gives the second environment the same domain. First
transport `params t₂` along `qk` from length `arity t₂` to length `arity t₁`;
then embed each transported entry into `V` and take the resulting graph. Thus
both environments can be queried by an index in `Fin (arity t₁)`. The private
families introduced next name their entries before and after this transport,
beginning with `pr₁` for the first vector.
<!--zh-->
第五项等同使第二个环境具有同一个定义域。先沿 `qk` 把 `params t₂` 从长度 `arity t₂` 搬运到长度 `arity t₁`，再把搬运后的每个条目嵌入 `V` 并取所得的图。这样，两张环境图都能用 `Fin (arity t₁)` 中的序号查取。接下来定义的私有族为搬运前后的条目取名，首先是第一个向量的 `pr₁`。
<!--ja-->
第五の同一視により、第二の環境も同じ定義域を持ちます。まず `params t₂` を `qk` に沿って長さ `arity t₂` から長さ `arity t₁` へ輸送し、次に輸送後の各成分を `V` へ埋め込んで、そのグラフを取ります。これで、どちらの環境も `Fin (arity t₁)` の添字で参照できます。続いて導入する局所的な族は輸送前後の成分に名前を付けるもので、まず第一のベクトルを読む `pr₁` を定めます。
<!--/-->

```agda
             (q₂ : fst (lookup e₂ γ)
                 ≡ env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) qk (params t₂)))))
             where
      private
        pr₁ : Fin (arity t₁) → ⟪ A ⟫
```

<!--en-->
At an index `i` of the common length, `pr₁ i` is simply the entry found in
`t₁`'s parameter vector. It remains an element of the small carrier `⟪ A ⟫`;
the embedding `ix` is applied only when this parameter is placed into an
environment graph or an ordered pair in the model. Keeping these two levels
separate lets the parameter order act on carrier elements themselves.
<!--zh-->
在共同长度的序号 `i` 处，`pr₁ i` 就是 `t₁` 的参数向量在该处的条目。它仍是小载体 `⟪ A ⟫` 的元素；只有当这个参数被放入环境图或模型中的有序对时，才施用嵌入 `ix`。把这两个层次分开，参数序便能直接作用于载体元素。
<!--ja-->
共通の長さの添字 `i` において、`pr₁ i` は `t₁` のパラメータベクトルのその成分です。これは小さな台 `⟪ A ⟫` の要素のままであり、環境グラフやモデル内の順序対へ入れるときにだけ埋め込み `ix` を施します。この二つの水準を分けておくことで、パラメータ順序を台の要素そのものに適用できます。
<!--/-->

```agda
        pr₁ i = lookup i (params t₁)

```

<!--en-->
The companion family `pr₂` reads the transported vector of `t₂`. It has the
same domain as `pr₁`, but its values are still carrier elements belonging to
the second name. Consequently `pr₁ i ≺ₚ pr₂ i` and `pr₁ j ≡ pr₂ j` are
well-typed statements at every common index, precisely the strict comparison
and prior agreement required by `Lex`.
<!--zh-->
配套的族 `pr₂` 读取 `t₂` 搬运后的向量。它与 `pr₁` 具有相同定义域，但其值仍是属于第二个名字的载体元素。因此，在每个共同序号处，`pr₁ i ≺ₚ pr₂ i` 与 `pr₁ j ≡ pr₂ j` 都是类型正确的陈述，恰好分别给出 `Lex` 所要求的严格比较与先前相符。
<!--ja-->
もう一方の族 `pr₂` は、輸送された `t₂` のベクトルを読みます。定義域は `pr₁` と同じですが、その値は第二の名前に属する台の要素です。したがって、共通の各添字で `pr₁ i ≺ₚ pr₂ i` と `pr₁ j ≡ pr₂ j` を型の合う形で述べられます。これらがそれぞれ、`Lex` の求める狭義の比較と、それ以前での一致です。
<!--/-->

```agda
        pr₂ : Fin (arity t₁) → ⟪ A ⟫
        pr₂ i = lookup i (subst (Vec ⟪ A ⟫) qk (params t₂))

```

<!--en-->
The first graph can now be read at an exact index. Suppose the pair with key
`# (toℕ i)` and value `fst u` belongs to the set in slot `e₁`. Transporting
this membership along `q₁` places it in `env (pfam t₁)`, and `lookup-spec`
identifies its second component with that graph's unique value. Since this
value is `ix (pr₁ i)`, `at₁` recovers the equality
`fst u ≡ ix (pr₁ i)`.
<!--zh-->
现在可以在一个确定序号处读取第一张图。假设以 `# (toℕ i)` 为键、以 `fst u` 为值的对属于槽位 `e₁` 中的集合。沿 `q₁` 搬运这项隶属，便把它放进 `env (pfam t₁)`；`lookup-spec` 再把其第二分量认定为该图在此处的唯一取值。这个取值就是 `ix (pr₁ i)`，故 `at₁` 恢复等式 `fst u ≡ ix (pr₁ i)`。
<!--ja-->
これで第一のグラフを特定の添字で読めます。鍵が `# (toℕ i)`、値が `fst u` である対がスロット `e₁` の集合に属すとします。この所属を `q₁` に沿って輸送すると `env (pfam t₁)` への所属になり、`lookup-spec` が第二成分をそのグラフの当該位置における唯一の値と同一視します。その値は `ix (pr₁ i)` なので、`at₁` は等式 `fst u ≡ ix (pr₁ i)` を復元します。
<!--/-->

```agda
        at₁ : (i : Fin (arity t₁)) (u : S)
            → ⟨ pr (# (toℕ i)) (fst u) ∈ fst (lookup e₁ γ) ⟩ → fst u ≡ ix (pr₁ i)
        at₁ i u h = subst ⟨_⟩ (lookup-spec (pfam t₁) i (fst u))
          (subst (λ z → ⟨ pr (# (toℕ i)) (fst u) ∈ z ⟩) q₁ h)

```

<!--en-->
The same reading applies to the second graph, with the transported family in
place of `pfam t₁`. Membership of the pair at key `# (toℕ i)` is first moved
along `q₂`; `lookup-spec` then yields `fst u ≡ ix (pr₂ i)`. Hence `at₁` and
`at₂` give the functional consequence needed here: they identify every value
found at a valid index with the particular parameter entry represented there.
<!--zh-->
第二张图以搬运后的族代替 `pfam t₁`，采用完全相同的读法。先沿 `q₂` 搬运键 `# (toℕ i)` 处那一有序对的隶属，再由 `lookup-spec` 得到 `fst u ≡ ix (pr₂ i)`。因此，`at₁` 与 `at₂` 给出这里所需的单值性结论：它们把每个有效序号处读出的值精确认定为那里所表示的参数条目。
<!--ja-->
第二のグラフも、`pfam t₁` の代わりに輸送後の族を用いて同じように読めます。鍵 `# (toℕ i)` の対の所属をまず `q₂` に沿って輸送すると、`lookup-spec` によって `fst u ≡ ix (pr₂ i)` が得られます。したがって `at₁` と `at₂` は、ここで必要な一価性の帰結を与えます。有効な添字で見つかった値を、そこで表される特定のパラメータ成分と正確に同一視するのです。
<!--/-->

```agda
        at₂ : (i : Fin (arity t₁)) (u : S)
            → ⟨ pr (# (toℕ i)) (fst u) ∈ fst (lookup e₂ γ) ⟩ → fst u ≡ ix (pr₂ i)
        at₂ i u h = subst ⟨_⟩ (lookup-spec (λ j → ix (pr₂ j)) i (fst u))
          (subst (λ z → ⟨ pr (# (toℕ i)) (fst u) ∈ z ⟩) q₂ h)

```

<!--en-->
The reverse use of `lookup-spec` supplies the canonical entry of the first
graph. Reflexivity says that `ix (pr₁ i)` is the value prescribed by
`pfam t₁` at `i`; reading the lookup equation backward turns this equality
into membership in `env (pfam t₁)`. Transport along the reverse of `q₁` then
places the same pair in the set actually stored at `e₁`. This is the witness
`put₁ i`.
<!--zh-->
反向使用 `lookup-spec`，便得到第一张图的典范条目。自反性说明 `ix (pr₁ i)` 正是 `pfam t₁` 在 `i` 处规定的值；逆向读取查表等式，就把这项相等变成对 `env (pfam t₁)` 的隶属。再沿 `q₁` 的反向搬运，即可把同一个有序对放进槽位 `e₁` 实际持有的集合。这就是见证 `put₁ i`。
<!--ja-->
`lookup-spec` を逆向きに使うと、第一のグラフの標準的な項目が得られます。反射律により `ix (pr₁ i)` は `pfam t₁` が `i` で指定する値です。この参照の等式を逆向きに読むと、その等しさは `env (pfam t₁)` への所属になります。さらに `q₁` の逆向きに輸送すれば、同じ順序対がスロット `e₁` に実際に格納された集合へ入ります。これが証人 `put₁ i` です。
<!--/-->

```agda
        put₁ : (i : Fin (arity t₁))
             → ⟨ pr (# (toℕ i)) (ix (pr₁ i)) ∈ fst (lookup e₁ γ) ⟩
        put₁ i = subst (λ z → ⟨ pr (# (toℕ i)) (ix (pr₁ i)) ∈ z ⟩) (sym q₁)
          (subst ⟨_⟩ (sym (lookup-spec (pfam t₁) i (ix (pr₁ i)))) refl)

```

<!--en-->
The witness `put₂ i` is constructed in exactly the same way for the
transported second family and the slot `e₂`. Together, the four lemmas give
both directions of graph lookup for the two names: `at₁` and `at₂` identify
any alleged values, while `put₁` and `put₂` exhibit the prescribed ones. The
forward translation will use the latter pair to build `Differs`; the reverse
translation will use the former pair to recover `Lex`.
<!--zh-->
见证 `put₂ i` 对搬运后的第二个族与槽位 `e₂` 作同样构造。于是，这四条引理为两个名字各自给出图查取的两个方向：`at₁` 与 `at₂` 识别任意给出的候选值，`put₁` 与 `put₂` 则展示图所规定的值。正向翻译将用后两者构造 `Differs`，反向翻译将用前两者恢复 `Lex`。
<!--ja-->
証人 `put₂ i` も、輸送後の第二の族とスロット `e₂` について同じように構成されます。これで四つの補題は、二つの名前のグラフ参照を両方向から扱えます。`at₁` と `at₂` は候補として与えられた値を同定し、`put₁` と `put₂` はグラフが指定する値を実際に示します。順方向の翻訳では後の二つから `Differs` を作り、逆方向の翻訳では前の二つから `Lex` を復元します。
<!--/-->

```agda
        put₂ : (i : Fin (arity t₁))
             → ⟨ pr (# (toℕ i)) (ix (pr₂ i)) ∈ fst (lookup e₂ γ) ⟩
        put₂ i = subst (λ z → ⟨ pr (# (toℕ i)) (ix (pr₂ i)) ∈ z ⟩) (sym q₂)
          (subst ⟨_⟩ (sym (lookup-spec (λ j → ix (pr₂ j)) i (ix (pr₂ i)))) refl)

```

<!--en-->
An index used by `Lex` is a finite number, whereas an index carried by
`Differs` must be an element of the constructible model. The helper `numAt`
crosses this small boundary: it pairs the von Neumann numeral `# m` with its
constructibility proof `numL m`. It does not by itself assert that the numeral
lies below an arity; that membership will be supplied separately from the
finite-index bound.
<!--zh-->
`Lex` 使用的序号是一个有穷数，而 `Differs` 携带的序号必须是可构造模型的元素。辅助定义 `numAt` 跨过这道小边界：它把 von Neumann 数码 `# m` 与其可构造性证明 `numL m` 配成一对。它本身并不断言这个数码低于某个元数；相应的隶属稍后由有穷序号自带的界限另行给出。
<!--ja-->
`Lex` が使う添字は有限な自然数ですが、`Differs` が携える添字は構成可能モデルの要素でなければなりません。補助定義 `numAt` はこの小さな隔たりを越え、von Neumann 数項 `# m` とその構成可能性の証明 `numL m` を組にします。ただし、これだけで数項があるアリティより下にあると主張するわけではありません。その所属は、有限添字に備わる境界から別に与えます。
<!--/-->

```agda
        numAt : (m : ℕ) → S
        numAt m = # m , numL m

```

<!--en-->
For the forward translation, an element of `Lex` supplies a finite index `i`,
a strict comparison `hlt` at that index, and equality `agree` at every earlier
index. The record `Differs` begins with the model element
`numAt (toℕ i)` and the two values `ixL (pr₁ i)` and `ixL (pr₂ i)`. Because a
finite index is smaller than its length, `#mono` turns `toℕ<n i` into
membership of its numeral in the arity numeral; transport along `qa` places
that membership in the arity slot.
<!--zh-->
正向翻译从 `Lex` 的一个元素取得有穷序号 `i`、该处的严格比较 `hlt`，以及每个更早序号处的相等 `agree`。所得 `Differs` 记录首先放入模型元素 `numAt (toℕ i)`，随后放入两个取值 `ixL (pr₁ i)` 与 `ixL (pr₂ i)`。有穷序号必小于其长度，故 `#mono` 把 `toℕ<n i` 化为该序号数码属于元数数码的证明；沿 `qa` 搬运以后，这项隶属便落在元数槽位中。
<!--ja-->
順方向の翻訳では、`Lex` の要素から有限添字 `i`、その位置での狭義の比較 `hlt`、およびそれ以前の各添字での等しさ `agree` が得られます。`Differs` の記録にはまずモデルの要素 `numAt (toℕ i)` を置き、続いて二つの値 `ixL (pr₁ i)` と `ixL (pr₂ i)` を置きます。有限添字はその長さより小さいので、`#mono` は `toℕ<n i` を、その添字の数項がアリティの数項に属すという証明へ変えます。これを `qa` に沿って輸送すれば、アリティのスロットへの所属が得られます。
<!--/-->

```agda
      lex-fill : Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂))
               → Differs P a₁ e₁ e₂ γ
      lex-fill (i , (hlt , agree)) = numAt (toℕ i)
        , ( ixL (pr₁ i) , ( ixL (pr₂ i)
        , ( subst (λ z → ⟨ # (toℕ i) ∈ z ⟩) (sym qa)
```

<!--en-->
The next fields certify what happens at the differing index. The witnesses
`put₁ i` and `put₂ i` put the two embedded parameter values into their
respective environment graphs. The representation law `Pfill` turns
`hlt : pr₁ i ≺ₚ pr₂ i` into membership of their ordered pair in `Ps`; transport
along the reverse of `qP` moves that membership to the relation set stored in
slot `P`. Thus the three membership fields of `Differs` express exactly the two
lookups and the strict parameter comparison.
<!--zh-->
接下来的字段证明相异序号处发生了什么。见证 `put₁ i` 与 `put₂ i` 把两个嵌入后的参数值分别放进对应的环境图。表示律 `Pfill` 把 `hlt : pr₁ i ≺ₚ pr₂ i` 化为这两个值组成的有序对属于 `Ps`；再沿 `qP` 的反向搬运，这项隶属便进入槽位 `P` 所持有的关系集。因此，`Differs` 的三项隶属字段恰好表达两次查取与参数的严格比较。
<!--ja-->
続く成分は、相違する添字で何が起きるかを証明します。証人 `put₁ i` と `put₂ i` は、二つの埋め込まれたパラメータ値をそれぞれの環境グラフに入れます。表示則 `Pfill` は `hlt : pr₁ i ≺ₚ pr₂ i` を、それらの順序対が `Ps` に属すという事実へ変えます。さらに `qP` の逆向きに輸送すると、その所属はスロット `P` が持つ関係集合への所属になります。したがって `Differs` の三つの所属成分は、二つの参照とパラメータの狭義の比較を正確に表します。
<!--/-->

```agda
              (#mono (toℕ i) (arity t₁) (toℕ<n i))
          , ( put₁ i
            , ( put₂ i
              , ( subst (λ z → ⟨ pr (ix (pr₁ i)) (ix (pr₂ i)) ∈ z ⟩) (sym qP)
                    (Pfill (pr₁ i) (pr₂ i) hlt)
```

<!--en-->
It remains to build `Agrees` below the chosen index. Given a model element `j`
with `fst j ∈ # (toℕ i)`, the numeral elimination theorem says, under
propositional truncation, that `fst j` is `# m` for some `m < toℕ i`. Mapping
the local construction `step` over this result will provide one shared value
for the two graphs at that earlier position. The truncation is preserved: the
particular natural number recovered from numeral membership is never exposed
outside the proposition required by `Agrees`.
<!--zh-->
还需构造所选序号以下的 `Agrees`。给定模型元素 `j` 及 `fst j ∈ # (toℕ i)`，数码消去定理在命题截断内说明：存在某个 `m < toℕ i`，使 `fst j` 等于 `# m`。把局部构造 `step` 映到这个结果上，就会在该较早位置为两张图给出一个共同取值。命题截断始终保留：从数码隶属中恢复的那个自然数不会暴露到 `Agrees` 所要求的命题之外。
<!--ja-->
残るのは、選んだ添字より前で `Agrees` を構成することです。モデルの要素 `j` と `fst j ∈ # (toℕ i)` が与えられると、数項の消去定理は、ある `m < toℕ i` について `fst j` が `# m` に等しいことを命題的切り詰めの中で示します。この結果に局所的な構成 `step` を写せば、その先行位置で二つのグラフに共通する値が得られます。切り詰めは保たれており、数項への所属から復元された特定の自然数が `Agrees` の求める命題の外へ現れることはありません。
<!--/-->

```agda
                , agrees ) ) ) ) ) )
        where
        agrees : Agrees P a₁ e₁ e₂ γ (numAt (toℕ i))
        agrees j hj = PT.map step (∈#-elim (toℕ i) (fst j) hj)
          where
```

<!--en-->
The function `step` makes the shared-value claim precise. From a number
`m < toℕ i` and an equality identifying `fst j` with `# m`, it must return a
model element `x` whose pair with the key `fst j` belongs to both environment
graphs. The supplied value is the first family's entry at the corresponding
finite index, packaged as `ixL (pr₁ jx)`. For the first graph, `put₁ jx`
already gives the required membership at the canonical numeral key; the
equality of the two presentations of that key transports it to `fst j`.
<!--zh-->
函数 `step` 精确陈述共同取值的要求。由 `m < toℕ i` 与把 `fst j` 认作 `# m` 的等式出发，它必须返回一个模型元素 `x`，使以 `fst j` 为键、以 `fst x` 为值的对同时属于两张环境图。给出的取值是第一族在相应有穷序号处的条目，包装为 `ixL (pr₁ jx)`。对第一张图，`put₁ jx` 已经给出典范数码键处的所需隶属；沿这个键的两种表示之间的等式搬运，即可把它改写到 `fst j` 处。
<!--ja-->
関数 `step` は、共通の値という主張を正確に述べます。`m < toℕ i` と `fst j` を `# m` に同一視する等式から、鍵 `fst j` と値 `fst x` の対が両方の環境グラフに属すようなモデルの要素 `x` を返さなければなりません。ここで与える値は、対応する有限添字における第一の族の成分であり、`ixL (pr₁ jx)` としてまとめられます。第一のグラフについては、`put₁ jx` が標準的な数項の鍵で必要な所属をすでに与えています。その鍵の二つの表示を結ぶ等式に沿って輸送すれば、鍵を `fst j` に書き換えられます。
<!--/-->

```agda
          step : Σ[ m ∈ ℕ ] ((m < toℕ i) × (fst j ≡ # m))
               → Σ[ x ∈ S ] ( ⟨ pr (fst j) (fst x) ∈ fst (lookup e₁ γ) ⟩
                            × ⟨ pr (fst j) (fst x) ∈ fst (lookup e₂ γ) ⟩ )
          step (m , (hm , qj)) = ixL (pr₁ jx)
            , ( subst (λ z → ⟨ pr z (ix (pr₁ jx)) ∈ fst (lookup e₁ γ) ⟩)
```

<!--en-->
For the second graph, the earlier-index hypothesis `agree` identifies
`pr₁ jx` with `pr₂ jx`. Transporting `put₂ jx` along the reverse of this
equality changes its value from `ix (pr₂ jx)` to the shared value
`ix (pr₁ jx)`; transporting the key as before then gives membership at
`fst j`. Hence both graphs contain the very same value at every position below
`i`, completing one result of `step` and therefore the `Agrees` field of
`Differs`.
<!--zh-->
对第二张图，先前序号处的假设 `agree` 把 `pr₁ jx` 与 `pr₂ jx` 等同。沿这项等同的反向搬运 `put₂ jx`，便把其中的值从 `ix (pr₂ jx)` 改写为共同取值 `ix (pr₁ jx)`；再像前面那样搬运键，即得到 `fst j` 处的隶属。因此，在 `i` 以下的每个位置，两张图都含有同一个取值。这就完成了 `step` 的一个结果，进而完成 `Differs` 的 `Agrees` 字段。
<!--ja-->
第二のグラフでは、先行添字についての仮定 `agree` が `pr₁ jx` と `pr₂ jx` を同一視します。この等しさの逆向きに `put₂ jx` を輸送すると、その値を `ix (pr₂ jx)` から共通の値 `ix (pr₁ jx)` へ書き換えられます。さらに先ほどと同じように鍵を輸送すれば、`fst j` での所属が得られます。したがって `i` より前のすべての位置で、二つのグラフはまったく同じ値を含みます。これで `step` の一つの結果が完成し、ひいては `Differs` の `Agrees` 成分が得られます。
<!--/-->

```agda
                  (sym qjx) (put₁ jx)
              , subst (λ z → ⟨ pr z (ix (pr₁ jx)) ∈ fst (lookup e₂ γ) ⟩) (sym qjx)
                  (subst (λ y → ⟨ pr (# (toℕ jx)) (ix y) ∈ fst (lookup e₂ γ) ⟩)
                    (sym (agree jx (subst (_< toℕ i) (sym qm) hm))) (put₂ jx)) )
            where
```

<!--en-->
The remaining identification concerns the key of the shared entry. From
`m < toℕ i` and the fact that `i` is itself below `arity t₁`, transitivity
makes `m` a valid element `jx : Fin (arity t₁)`. Converting `jx` back to a
natural number returns `m`; the path `qm` records this round trip and will let
the graph memberships use their canonical numeral key.
<!--zh-->
剩下的认同关乎共同条目的键。由 `m < toℕ i`，再结合 `i` 本身小于`arity t₁`，传递性说明 `m` 给出一个合法元素 `jx : Fin (arity t₁)`。把`jx` 再转回自然数便得到 `m`；路径 `qm` 记录这次往返，使两项图隶属可以改写到各自的典范数码键上。
<!--ja-->
残る同一視は、共通の項目の鍵に関するものです。`m < toℕ i` と、`i` 自身が`arity t₁` より小さいことから、推移性によって `m` は正当な要素`jx : Fin (arity t₁)` を定めます。`jx` を自然数へ戻すと `m` が得られ、その往復を経路`qm` が記録します。この経路により、二つのグラフへの所属をそれぞれの標準的な数項の鍵で書けます。
<!--/-->

```agda
            jx : Fin (arity t₁)
            jx = fromℕ' (arity t₁) m (<-trans hm (toℕ<n i))
            qm : toℕ jx ≡ m
            qm = toFromId' (arity t₁) m (<-trans hm (toℕ<n i))
            qjx : fst j ≡ # (toℕ jx)
```

<!--en-->
The equality `qj` identifies the original model key with `# m`, while `qm`
identifies `m` with the number of `jx`. Their composite is
`qjx : fst j ≡ # (toℕ jx)`. This is the precise change of key used above to
transport both canonical graph entries to the position named by `j`; it
completes the construction of `Agrees`, and hence the forward bridge
`lex-fill`.
<!--zh-->
等式 `qj` 把原来的模型内键认作 `# m`，而 `qm` 又把 `m` 认作 `jx` 所对应的自然数。二者复合即得`qjx : fst j ≡ # (toℕ jx)`。这正是前文所用的换键等式：它把两张图的典范条目都传输到`j` 所指的位置。至此 `Agrees` 构造完成，正向桥 `lex-fill` 也随之闭合。
<!--ja-->
等式 `qj` はもとのモデル内の鍵を `# m` と同一視し、`qm` は `m` を `jx` の表す自然数と同一視します。両者を合成すると`qjx : fst j ≡ # (toℕ jx)` が得られます。これは先ほど用いた鍵の書き換えそのもので、二つのグラフの標準的な項目を、ともに`j` が名指す位置へ輸送します。これで `Agrees` の構成が終わり、順方向の橋 `lex-fill` も完成します。
<!--/-->

```agda
            qjx = qj ∙ cong #_ (sym qm)

```

<!--en-->
The reverse bridge starts from a `Differs` record and must recover an explicit
first difference. Its recorded index `i` belongs to the arity numeral, but the
numeral-membership elimination theorem recovers the corresponding smaller
natural number only under propositional truncation. Accordingly `lex-read` returns the
propositional truncation of `Lex`: numeral elimination hides the chosen
number, and `PT.map`
performs the otherwise explicit reconstruction without removing that
truncation.
<!--zh-->
反向桥从一份 `Differs` 记录出发，目标是恢复显式的首次相异。记录中的序号 `i` 属于元数数码，但数码隶属的消去定理只能在命题截断内恢复相应的较小自然数。因此，`lex-read` 返回 `Lex` 的命题截断：数码消去隐藏所选的自然数，`PT.map` 则在不解除这层截断的前提下完成其余显式构造。
<!--ja-->
逆向きの橋は `Differs` の記録から出発し、明示的な最初の相違を復元します。記録された添字 `i` はアリティの数項に属しますが、数項への所属についての消去定理が対応する小さい自然数を復元するのは、命題的切り詰めの中だけです。そのため `lex-read` は `Lex` の命題的切り詰めを返します。数項の消去は選ばれた自然数を隠したままにし、`PT.map` がその切り詰めを外さずに残りの明示的な構成を行います。
<!--/-->

```agda
      lex-read : Differs P a₁ e₁ e₂ γ
               → ∥ Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂)) ∥₁
      lex-read (i , (u , (v , (hi , (h₁ , (h₂ , (hp , ag))))))) =
        PT.map atIndex (∈#-elim (arity t₁) (fst i)
          (subst (λ z → ⟨ fst i ∈ z ⟩) qa hi))
```

<!--en-->
Inside the mapped construction, the hidden witness is available as a concrete
number `m`, together with `m < arity t₁` and an equation identifying the model
index with `# m`. The function `atIndex` must now produce `Lex` itself. It
chooses the corresponding finite index and will prove the two obligations of
a first difference there: strict comparison at that index and agreement at
every smaller one.
<!--zh-->
进入映射后的构造时，隐藏见证已可作为具体自然数 `m` 使用，同时还有`m < arity t₁`，以及把模型内序号认作 `# m` 的等式。函数 `atIndex` 此时要直接构造`Lex`。它选取相应的有穷序号，并将在该处证明首次相异的两项要求：该序号处严格比较，所有更小序号处相符。
<!--ja-->
写像された構成の内部では、隠されていた証人を具体的な自然数 `m` として使えます。同時に`m < arity t₁` と、モデル内の添字を `# m` と同一視する等式も得られます。関数 `atIndex` はここで`Lex` そのものを構成します。対応する有限添字を選び、その位置での狭義の比較と、それより小さいすべての添字での一致という、最初の相違の二条件を証明します。
<!--/-->

```agda
        where
        atIndex : Σ[ m ∈ ℕ ] ((m < arity t₁) × (fst i ≡ # m))
                → Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂))
        atIndex (m , (hm , qi)) = ι , (below , agrees)
          where
```

<!--en-->
The bound on `m` gives `ι : Fin (arity t₁)`. As before, the numeral round trip
changes the equation for `# m` into
`qι : fst i ≡ # (toℕ ι)`, so the recorded membership in the first environment
can be queried at the canonical key for `ι`. The lookup lemma `at₁` then
identifies the recorded value `fst u` with the embedded first parameter
`ix (pr₁ ι)`.
<!--zh-->
`m` 的界给出 `ι : Fin (arity t₁)`。和正向一样，数码往返把关于 `# m` 的等式改写为`qι : fst i ≡ # (toℕ ι)`，于是记录在第一张环境图中的隶属可以在 `ι` 的典范键处读取。查取引理`at₁` 随即把记录的值 `fst u` 认作第一个参数的嵌入像 `ix (pr₁ ι)`。
<!--ja-->
`m` の境界から `ι : Fin (arity t₁)` が得られます。順方向と同様に、数項との往復によって`# m` についての等式は `qι : fst i ≡ # (toℕ ι)` へ書き換えられます。したがって、第一の環境に記録された所属を`ι` の標準的な鍵で読めます。参照の補題 `at₁` は、記録された値 `fst u` を第一のパラメータの埋め込み像`ix (pr₁ ι)` と同一視します。
<!--/-->

```agda
          ι : Fin (arity t₁)
          ι = fromℕ' (arity t₁) m hm
          qι : fst i ≡ # (toℕ ι)
          qι = qi ∙ cong #_ (sym (toFromId' (arity t₁) m hm))
          qu : fst u ≡ ix (pr₁ ι)
```

<!--en-->
Applying `at₂` to the second graph likewise gives
`fst v ≡ ix (pr₂ ι)`. The relation atom in `Differs` says that the ordered pair
of the recorded values belongs to the set in slot `P`; after rewriting that
set to `Ps` and the two values to their embedded parameters, the representation
law `Prep` reads the atom as the required strict comparison
`pr₁ ι ≺ₚ pr₂ ι`.
<!--zh-->
对第二张图应用 `at₂`，同样得到 `fst v ≡ ix (pr₂ ι)`。`Differs` 的关系原子说：记录的两个值组成的有序对属于槽位`P` 中的集合。把该集合改写为 `Ps`，再把两个值改写为相应参数的嵌入像之后，表示律 `Prep` 便把这条原子读成所需的严格比较`pr₁ ι ≺ₚ pr₂ ι`。
<!--ja-->
第二のグラフに `at₂` を適用すると、同様に `fst v ≡ ix (pr₂ ι)` が得られます。`Differs` の関係原子は、記録された二つの値の順序対がスロット`P` の集合に属すと述べます。その集合を `Ps` に、二つの値を対応するパラメータの埋め込み像に書き換えると、表示則`Prep` がこの原子を、必要な狭義の比較 `pr₁ ι ≺ₚ pr₂ ι` として読みます。
<!--/-->

```agda
          qu = at₁ ι u (subst (λ z → ⟨ pr z (fst u) ∈ fst (lookup e₁ γ) ⟩) qι h₁)
          qv : fst v ≡ ix (pr₂ ι)
          qv = at₂ ι v (subst (λ z → ⟨ pr z (fst v) ∈ fst (lookup e₂ γ) ⟩) qι h₂)
          below : pr₁ ι ≺ₚ pr₂ ι
          below = Prep (pr₁ ι) (pr₂ ι)
```

<!--en-->
The transports just described finish the proof named `below`. It remains to
recover agreement before `ι`. For any `j` with `toℕ j < toℕ ι`, the bounded
clause `ag` supplies, merely, one model element whose value occurs in both
environment graphs at that position. Since the desired equality of the two
embedded parameter sets is a proposition, this propositional truncation may be
eliminated directly into it.
<!--zh-->
上述传输完成了名为 `below` 的证明。余下任务是恢复 `ι` 之前的相符。任取满足`toℕ j < toℕ ι` 的 `j`，有界子句 `ag` 仅仅地给出一个模型元素，其值在该位置同时出现于两张环境图。所求的两个参数嵌入像之相等是命题，因此可以把这份命题截断直接消去到该相等中。
<!--ja-->
以上の輸送によって `below` と名づけられた証明が完成します。残るのは `ι` より前での一致の復元です。`toℕ j < toℕ ι` を満たす任意の `j` に対して、有界な節 `ag` は、その位置で両方の環境グラフに値として現れる一つのモデル要素を、単に存在するものとして与えます。求める二つのパラメータの埋め込み像の等しさは命題なので、この命題的切り詰めをそこへ直接消去できます。
<!--/-->

```agda
            (subst2 (λ y z → ⟨ pr y z ∈ fst Ps ⟩) qu qv
              (subst (λ z → ⟨ pr (fst u) (fst v) ∈ z ⟩) qP hp))
          agrees : (j : Fin (arity t₁)) → toℕ j < toℕ ι → pr₁ j ≡ pr₂ j
          agrees j hj = ix-inj (pr₁ j) (pr₂ j)
            (PT.rec (setIsSet (ix (pr₁ j)) (ix (pr₂ j))) same
```

<!--en-->
To invoke `ag`, the finite inequality is first converted by `#mono` into
membership of `# (toℕ j)` in `# (toℕ ι)`, then transported along `qι` to the
recorded bound. The resulting truncated witness has exactly the shape handled
by `same`: an element `x` together with membership of the pair
`(# (toℕ j), fst x)` in each environment graph. Thus the truncation contains
all the data needed for the equality, while none of that witness data escapes.
<!--zh-->
为了调用 `ag`，先由 `#mono` 把有穷不等式化为`# (toℕ j) ∈ # (toℕ ι)`，再沿 `qι` 传输到记录中的界。所得截断见证恰具有 `same` 所需的形状：一个元素`x`，以及有序对 `(# (toℕ j), fst x)` 分别属于两张环境图的证明。因此，这层截断含有所需相等的全部资料，却不让任何具体见证逸出。
<!--ja-->
`ag` を使うため、まず有限な不等式を `#mono` によって`# (toℕ j) ∈ # (toℕ ι)` という所属へ変え、さらに `qι` に沿って記録された境界へ輸送します。得られる切り詰められた証人は`same` が扱う形そのものです。すなわち、要素 `x` と、順序対 `(# (toℕ j), fst x)` がそれぞれの環境グラフに属すことの組です。したがって、切り詰めの内部には等しさを導くための情報がすべてありながら、具体的な証人は外へ出ません。
<!--/-->

```agda
              (ag (numAt (toℕ j))
                (subst (λ z → ⟨ # (toℕ j) ∈ z ⟩) (sym qι) (#mono (toℕ j) (toℕ ι) hj))))
            where
            same : Σ[ x ∈ S ] ( ⟨ pr (# (toℕ j)) (fst x) ∈ fst (lookup e₁ γ) ⟩
                              × ⟨ pr (# (toℕ j)) (fst x) ∈ fst (lookup e₂ γ) ⟩ )
```

<!--en-->
For a chosen shared value `x`, `at₁` identifies `fst x` with
`ix (pr₁ j)` and `at₂` identifies the same set with `ix (pr₂ j)`. Reversing
the first path and composing it with the second gives equality of the two
embedded parameters. Injectivity of `ix` then reflects that equality back to
`pr₁ j ≡ pr₂ j`, which is precisely the earlier-index condition of `Lex`.
The reverse bridge is now complete.
<!--zh-->
选定一个共同取值 `x` 后，`at₁` 把 `fst x` 认作 `ix (pr₁ j)`，`at₂` 则把同一个集合认作`ix (pr₂ j)`。反转第一条路径再与第二条复合，便得到两个参数嵌入像相等。`ix` 的单射性把这项相等反映回`pr₁ j ≡ pr₂ j`，恰好就是 `Lex` 在先前序号处要求的条件。反向桥至此完成。
<!--ja-->
共通の値 `x` を一つ取ると、`at₁` は `fst x` を `ix (pr₁ j)` と同一視し、`at₂` は同じ集合を`ix (pr₂ j)` と同一視します。第一の経路を逆にして第二の経路と合成すれば、二つのパラメータの埋め込み像が等しいと分かります。`ix` の単射性はこの等しさを `pr₁ j ≡ pr₂ j` へ反映し、これは `Lex` が先行添字に要求する条件そのものです。これで逆向きの橋も完成します。
<!--/-->

```agda
                 → ix (pr₁ j) ≡ ix (pr₂ j)
            same (x , (k₁ , k₂)) = sym (at₁ j x k₁) ∙ at₂ j x k₂
```

<!--en-->
## Both halves
<!--zh-->
## 两半
<!--ja-->
## 妥当性の両方向
<!--/-->

<!--en-->
Under the four representation laws supplied to `Keys`, the two relation slots stand for `limitOrder` on formula codes and the given order on carrier parameters. The two halves now compare the same three keys. `order-in` sends a concrete proof of `t₁ ≺ₙ t₂` to satisfaction of `≺At`; `order-out` reads such a satisfaction only as `∥ t₁ ≺ₙ t₂ ∥₁`. The outward half retains the propositional truncation contributed by disjunction and existential satisfaction. This completes the adequacy of the comparison formula `≺At` itself, and no stronger result about the other formulas is proved here.

The remaining boundary is precise. A meta-level `Name` stores an arity, a parameter-free formula, and a parameter vector; its denotation is derived. Internally, `NameAt` adds slots for those data and the derived denotation, which it checks using the set of satisfying environments returned by `satGraphAt`. `LeastNameAt` states that no smaller name has the same denotation, but does not choose a name. The complete adequacy of `NameAt`, `LeastNameAt`, and `StepAt`, including recovery of their witnesses, belongs to `L.Choice.NameComparisonAdequacy`; the actual least-name choice remains `CanonicalNames.leastName`.
<!--zh-->
在 `Keys` 接受的四条表示律下，两个关系位置分别表示公式码上的 `limitOrder` 和载体参数上的给定次序。现在，两半证明比较的是同样三个键。`order-in` 把一份具体的 `t₁ ≺ₙ t₂` 证明送到 `≺At` 的满足关系；`order-out` 从这样的满足关系只能读回 `∥ t₁ ≺ₙ t₂ ∥₁`。向外一半保留析取与存在满足关系带来的命题截断。因此，本章至此只完成比较公式 `≺At` 自身的充分性，没有在这里得到关于其余公式的更强结论。

余下工作的边界是明确的。元语言的 `Name` 只存储元数、无参公式和参数向量，指称由它们派生。在模型内部，`NameAt` 为这些数据和派生的指称设置位置，并用 `satGraphAt` 返回的满足环境集检查指称。`LeastNameAt` 只陈述没有同指称而更小的名字，并不选择名字。`NameAt`、`LeastNameAt` 与 `StepAt` 的完整充分性，包括从满足关系中恢复见证，属于 `L.Choice.NameComparisonAdequacy`；实际的最小名字选择仍由 `CanonicalNames.leastName` 完成。
<!--ja-->
`Keys` に与えられた四つの表示則のもとで、二つの関係スロットは、それぞれ論理式の符号上の `limitOrder` と台のパラメータ上の与えられた順序を表します。ここで証明した二方向は、同じ三つのキーを比較します。`order-in` は具体的な `t₁ ≺ₙ t₂` の証明から `≺At` の充足関係を導き、`order-out` はその充足関係から `∥ t₁ ≺ₙ t₂ ∥₁` だけを読み出します。外向きの証明には、選言と存在量化の充足関係から生じる命題的切り詰めが残ります。したがって、本章でここまでに得られたのは比較論理式 `≺At` 自体の妥当性であり、他の論理式についてこれより強い結果を証明したわけではありません。

残る仕事の境界は明確です。メタ言語の `Name` が保持するのは、アリティ、無パラメータ論理式、パラメータベクトルであり、指示対象はそれらから導かれます。モデル内部では、`NameAt` がそれらのデータと導出された指示対象のスロットを設け、`satGraphAt` が返す充足環境の集合を用いて指示対象を検査します。`LeastNameAt` は同じ指示対象をもつより小さな名前がないことを述べるだけで、名前を選択しません。充足関係からの証人の回収を含む `NameAt`、`LeastNameAt`、`StepAt` の完全な妥当性は `L.Choice.NameComparisonAdequacy` で扱われ、最小名の実際の選択は引き続き `CanonicalNames.leastName` が担います。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Two path-induction lemmas now remove a type-level obstacle from the full
three-key comparison. The first, `envShift`, concerns an arity equality
`e : arity t ≡ k`. Transporting `params t` along `e`, reading its entries, and
forming their environment graph yields the same graph as reading `params t`
at its original length. When `e` is reflexivity the claim reduces immediately,
and path induction handles every equality.
<!--zh-->
接下来两条路径归纳引理清除完整三键比较中的类型层面障碍。第一条 `envShift` 处理元数等式`e : arity t ≡ k`。沿 `e` 传输 `params t`，逐项读取并组成环境图，所得图与在原长度上直接读取`params t` 的图相等。当 `e` 是自反路径时，结论立即化简；路径归纳遂覆盖任意等式。
<!--ja-->
続く二つの経路帰納の補題は、三つの鍵による比較全体にある型の障害を取り除きます。第一の `envShift` は、アリティの等式`e : arity t ≡ k` を扱います。`params t` を `e` に沿って輸送し、成分を読んで環境グラフを作っても、もとの長さで`params t` を読んで作るグラフと等しくなります。`e` が反射経路なら主張は直ちに簡約され、経路帰納によって任意の等式の場合が従います。
<!--/-->

```agda
    private
      envShift : (t : Name) {k : ℕ} (e : arity t ≡ k)
               → env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) e (params t))))
               ≡ env (pfam t)
      envShift t e = sym (constSubstCommSlice
```

<!--en-->
The equation is oriented from the graph of the transported vector to the
original graph `env (pfam t)`. This orientation is useful in the final proof:
the hypothesis for the second environment identifies its slot with the
original graph, and the reverse of `envShift` then identifies that same slot
with the graph at the first name's arity, exactly the form expected by the
first-difference bridge.
<!--zh-->
这条等式从传输后向量的图指向原图 `env (pfam t)`。这个方向服务于最终证明：关于第二个环境的假设先把相应槽位认作原图，再接上`envShift` 的反向，便把同一槽位认作第一名字之元数上的图，恰好得到首次相异桥所要求的形式。
<!--ja-->
この等式は、輸送後のベクトルのグラフから、もとのグラフ `env (pfam t)` へ向いています。この向きは最後の証明で役立ちます。第二の環境についての仮定は、まずそのスロットをもとのグラフと同一視します。そこに`envShift` の逆向きをつなぐと、同じスロットを第一の名前のアリティ上のグラフと同一視でき、最初の相違の橋が要求する形がちょうど得られます。
<!--/-->

```agda
        (Vec ⟪ A ⟫) (V ℓ) (λ _ v → env (λ i → ix (lookup i v))) e (params t))

```

<!--en-->
The second lemma, `vecShift`, performs the parallel simplification for the
vector order. Comparing `p` with `q` after transporting `q` along an equality
of lengths gives the same proposition as comparing the original vectors.
Again the equality proof contributes no mathematical case: path induction
reduces it to reflexivity. Together, `envShift` and `vecShift` keep the graph
presentation and the vector comparison synchronized when the arities are
identified.
<!--zh-->
第二条引理 `vecShift` 对向量序作平行的化简。沿长度等式传输 `q` 后再拿它与 `p` 比较，所得命题与直接比较原向量相同。等式证明同样不引入新的数学情形：路径归纳把它化为自反路径。于是，元数一经认同，`envShift` 与`vecShift` 便使环境图的呈现和向量比较始终同步。
<!--ja-->
第二の補題 `vecShift` は、ベクトル順序について対応する簡約を行います。長さの等式に沿って `q` を輸送してから`p` と比較して得る命題は、もとのベクトルを比較する命題と同じです。ここでも等式の証明から新しい数学的場合は生じません。経路帰納によって反射経路の場合へ帰着します。したがって、アリティを同一視したとき、`envShift` と`vecShift` が環境グラフの表示とベクトルの比較を同期させます。
<!--/-->

```agda
      vecShift : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ k) (q : Vec ⟪ A ⟫ i)
               → (p ≺ᵥ subst (Vec ⟪ A ⟫) e q) ≡ (p ≺ᵥ q)
      vecShift e p q = sym (constSubstCommSlice
        (Vec ⟪ A ⟫) (Type (ℓ-suc ℓ)) (λ _ v → p ≺ᵥ v) e q)

```

<!--en-->
The final comparison is carried out at arbitrary slots of an arbitrary
environment. Two slots hold the represented relations `Rs` and `Ps`; for each
name, three more hold its formula code, arity numeral, and parameter graph.
The eight equations `qR`, `qP`, `qs₁`, `qs₂`, `qa₁`, `qa₂`, `qe₁`, and `qe₂`
pin those readings to two concrete names `t₁` and `t₂`. Under precisely these
hypotheses, the internal formula can be compared with `_≺ₙ_`.
<!--zh-->
最后的比较在任意环境的任意槽位上进行。两个槽位分别持有表示关系 `Rs` 与 `Ps`；对每个名字，另有三个槽位持有它的公式码、元数数码与参数图。八条等式`qR`、`qP`、`qs₁`、`qs₂`、`qa₁`、`qa₂`、`qe₁` 与 `qe₂` 把这些读法固定到两个具体名字`t₁`、`t₂` 上。恰在这些假设之下，内部公式才可与 `_≺ₙ_` 对照。
<!--ja-->
最後の比較は、任意の環境の任意のスロットで行います。二つのスロットには表示関係 `Rs` と `Ps` が入り、各名前についてさらに三つのスロットが、その論理式の符号、アリティの数項、パラメータのグラフを持ちます。八つの等式`qR`、`qP`、`qs₁`、`qs₂`、`qa₁`、`qa₂`、`qe₁`、`qe₂` が、これらの読みを二つの具体的な名前`t₁` と `t₂` に固定します。まさにこれらの仮定のもとで、内部の論理式を `_≺ₙ_` と照合できます。
<!--/-->

```agda
    module _ {n : ℕ} (R P s₁ a₁ e₁ s₂ a₂ e₂ : Fin n) (γ : S ^ n) (t₁ t₂ : Name)
             (qR : fst (lookup R γ) ≡ fst Rs) (qP : fst (lookup P γ) ≡ fst Ps)
             (qs₁ : fst (lookup s₁ γ) ≡ fst (codeOf t₁))
             (qs₂ : fst (lookup s₂ γ) ≡ fst (codeOf t₂))
             (qa₁ : fst (lookup a₁ γ) ≡ # (arity t₁))
```

<!--en-->
The last four slot equations pin the two arities and the two environment
graphs; in particular, no chosen coordinates are built into the theorem. To
read the second and third keys, equality found between slot values must be
lifted back to equality of the dependent data carried by names. The first
helper, `codeSame`, addresses the code key: from equality of the two skeleton
slots it reconstructs an equality `codeOf t₂ ≡ codeOf t₁` in the type
`Limit`.
<!--zh-->
最后四条槽位等式固定两个元数与两张环境图，因此定理并未把任何特定坐标写死。为了读取第二、第三个键，还须把槽位取值之间的相等提升回名字所携依值数据的相等。第一个辅助引理`codeSame` 处理码键：它从两个骨架槽位相等，重建类型 `Limit` 中的等式`codeOf t₂ ≡ codeOf t₁`。
<!--ja-->
最後の四つのスロット等式は、二つのアリティと二つの環境グラフを固定します。したがって、この定理は特定の座標を組み込んでいません。第二、第三の鍵を読むには、スロットの値の等しさを、名前が携える依存データの等しさへ持ち上げる必要があります。最初の補助関数 `codeSame` は符号の鍵を扱い、二つの骨格スロットの等しさから、型 `Limit` における等式 `codeOf t₂ ≡ codeOf t₁` を復元します。
<!--/-->

```agda
             (qa₂ : fst (lookup a₂ γ) ≡ # (arity t₂))
             (qe₁ : fst (lookup e₁ γ) ≡ env (pfam t₁))
             (qe₂ : fst (lookup e₂ γ) ≡ env (pfam t₂)) where
      private
        codeSame : fst (lookup s₂ γ) ≡ fst (lookup s₁ γ) → codeOf t₂ ≡ codeOf t₁
```

<!--en-->
An element of `Limit` is an underlying set together with evidence that it
belongs to `Lset ω`. That evidence is proposition-valued, so `Σ≡Prop` says
that a path between the underlying sets determines a path between the complete
codes. The required underlying path is the composite
`sym qs₂ ∙ q ∙ qs₁`: from the second code to its slot, across the recorded
skeleton equality, and on to the first code. This explains both why the proof
component needs no separate comparison and why the resulting equality has the
orientation required by the second branch of the name order.
<!--zh-->
`Limit` 的元素由一个底层集合及其属于 `Lset ω` 的证据组成。该证据取值于命题，因此 `Σ≡Prop` 说明：底层集合之间的一条路径就足以确定完整码之间的路径。这里所需的底层路径是复合`sym qs₂ ∙ q ∙ qs₁`：从第二个码走到它的槽位，经记录的骨架等式，再走到第一个码。这既说明证明分量无须另行比较，也说明所得等式为何具有名字序第二分支所需的方向。
<!--ja-->
`Limit` の要素は、台となる集合と、それが `Lset ω` に属すことの証拠からなります。その証拠は命題値なので、`Σ≡Prop` により、台となる集合の間の経路だけで完全な符号の間の経路が定まります。ここで必要な台の経路は`sym qs₂ ∙ q ∙ qs₁` です。第二の符号からそのスロットへ進み、記録された骨格の等式を渡って、第一の符号へ至ります。これにより、証明成分を別に比較する必要がないことと、得られる等式が名前順序の第二の分岐に必要な向きを持つことの両方が分かります。
<!--/-->

```agda
        codeSame q = Σ≡Prop (λ x → snd (x ∈ Lset ω)) (sym qs₂ ∙ q ∙ qs₁)

```

<!--en-->
The reverse conversion starts with equality in `Limit`, where a code consists of
an underlying set together with its proof of membership in the limit stage.
Projecting with `fst` gives equality of the underlying code sets. Composing it
with the two slot identifications yields the orientation required by the later
branches of the formula: the second skeleton slot equals the first.
<!--zh-->
反向转换从 `Limit` 中的等同出发；这里的码由底层集合及其属于极限层的证明组成。对这条等同施用 `fst`，便得到两个底层码集合的等同。再与两项槽位等同复合，就得到公式后两支所需的方向：第二个骨架槽等同于第一个。
<!--ja-->
逆向きの変換は `Limit` における等しさから始まります。ここで符号は、台となる集合と、それが極限段階に属することの証明から成ります。`fst` で射影すれば台となる符号集合の等しさが得られ、それを二つのスロットの同一視と合成すると、論理式の後二つの枝が要求する向き、すなわち第二の骨格スロットが第一の骨格スロットに等しいという形になります。
<!--/-->

```agda
        codeBack : codeOf t₂ ≡ codeOf t₁ → fst (lookup s₂ γ) ≡ fst (lookup s₁ γ)
        codeBack ec = qs₂ ∙ cong fst ec ∙ sym qs₁

```

<!--en-->
The parameter branch must read the second environment at the first name's
arity. Given `ek : arity t₂ ≡ arity t₁`, path induction identifies the graph of
`params t₂` with the graph obtained after transporting that vector to the new
length. Reversing this graph equality and composing it with the identification
of slot `e₂` gives exactly the transported environment expected by the
first-difference bridge.
<!--zh-->
参数支必须按第一个名字的元数读取第二张环境图。给定 `ek : arity t₂ ≡ arity t₁`，路径归纳把 `params t₂` 的图与先把该向量搬运到新长度再取图所得的集合等同起来。将这条图等同反向读取，并与槽位 `e₂` 的等同复合，便得到首次相异之桥所要求的搬运后环境。
<!--ja-->
パラメータの枝では、第二の環境を第一の名前のアリティで読まなければなりません。`ek : arity t₂ ≡ arity t₁` が与えられると、経路帰納法により、`params t₂` のグラフは、そのベクトルを新しい長さへ輸送してから作ったグラフと同一視されます。このグラフの等しさを逆向きに読み、スロット `e₂` の同一視と合成すれば、最初の相違を扱う橋が要求する輸送後の環境が得られます。
<!--/-->

```agda
        shiftEnv : (ek : arity t₂ ≡ arity t₁)
                 → fst (lookup e₂ γ)
                 ≡ env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) ek (params t₂))))
        shiftEnv ek = qe₂ ∙ sym (envShift t₂ ek)

```

<!--en-->
The forward theorem now follows the three possible reasons why one name
precedes another. In the code branch, `Rfill` turns the strict comparison of
the two formula codes by the limit order into membership of their ordered pair
in `Rs`. The equations for `R`, `s₁`, and `s₂` transport that membership to the
three slots of the formula, and `≺At-in` places the resulting witness in the
first branch of `≺At`.
<!--zh-->
正向定理现在依次处理一个名字先于另一个名字的三种缘由。在码支中，`Rfill` 把两个公式码在极限序下的严格比较化为其有序对属于 `Rs`。关于 `R`、`s₁` 与 `s₂` 的等同把这项隶属搬运到公式的三个槽位，`≺At-in` 再将所得见证放入 `≺At` 的第一支。
<!--ja-->
順方向の定理は、一方の名前が他方に先行する三つの理由を順に扱います。符号の枝では、`Rfill` が二つの論理式符号の極限順序による狭義の比較を、それらの順序対が `Rs` に属するという事実へ変えます。`R`、`s₁`、`s₂` に関する同一視でこの所属を論理式の三つのスロットへ輸送し、`≺At-in` が得られた証人を `≺At` の第一の枝へ入れます。
<!--/-->

```agda
      order-in : t₁ ≺ₙ t₂ → ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩
      order-in (inl h) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inl (subst (λ z → ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ z ⟩)
                (sym qR)
                (subst2 (λ y z → ⟨ pr y z ∈ fst Rs ⟩) (sym qs₁) (sym qs₂)
```

<!--en-->
In the arity branch, equality of codes first supplies the required equality of
the two skeleton slots through `codeBack`. The strict inequality
`arity t₁ < arity t₂` becomes membership
`# (arity t₁) ∈ # (arity t₂)` by the von Neumann numeral law `#mono`; the two
arity-slot equations then carry this membership to the formula. Thus the
second key is used only after the first key has been shown equal.
<!--zh-->
在元数支中，码的等同先经 `codeBack` 给出两个骨架槽所需的等同。严格不等式 `arity t₁ < arity t₂` 由 von Neumann 数码律 `#mono` 化为隶属 `# (arity t₁) ∈ # (arity t₂)`，两项元数槽等同再把这项隶属搬运到公式中。因此，只有在第一个键已证相等之后，第二个键才参与比较。
<!--ja-->
アリティの枝では、まず符号の等しさから `codeBack` を通じて二つの骨格スロットに必要な等しさを得ます。狭義の不等式 `arity t₁ < arity t₂` は、von Neumann 数項の法則 `#mono` によって所属 `# (arity t₁) ∈ # (arity t₂)` へ変わり、二つのアリティスロットの同一視がこの所属を論理式へ輸送します。したがって第二の鍵が比較に使われるのは、第一の鍵の等しさが示された後だけです。
<!--/-->

```agda
                  (Rfill (codeOf t₁) (codeOf t₂) h))))
      order-in (inr (ec , inl h)) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inr (codeBack ec , inl
          (subst2 (λ y z → ⟨ y ∈ z ⟩) (sym qa₁) (sym qa₂)
            (#mono (arity t₁) (arity t₂) h))))
```

<!--en-->
The parameter branch begins with equal codes and equal arities. The arity path
transports the second parameter vector to the first vector's length; `vec-lex`
then turns their recursive vector comparison into an explicit first differing
index. The map `lex-fill` then turns that witness into the `Differs` payload
used to satisfy `LexAt`: it records the index, the strict comparison there,
and all earlier agreements, using `shiftEnv` to identify the transported
second graph. This constructs the third branch of `≺At` directly from the
comparison evidence, without extracting any witness from a propositional
truncation.
<!--zh-->
参数支从码相等且元数相等的情形开始。元数路径先把第二个参数向量搬运到第一个向量的长度，`vec-lex` 再把两者的递归向量比较化为一个显式的首次相异序号。`lex-fill` 随后把这份见证化为满足 `LexAt` 所用的 `Differs` 载荷：其中记录该序号、此处的严格比较以及此前各处的相等，并用 `shiftEnv` 识别搬运后的第二张图。这样便由比较证据直接构造出 `≺At` 的第三支，无须从命题截断中提取任何见证。
<!--ja-->
パラメータの枝は、符号とアリティがともに等しい場合から始まります。アリティの経路で第二のパラメータベクトルを第一のベクトルの長さへ輸送し、`vec-lex` によって再帰的なベクトル比較を明示的な最初の相違の添字へ変えます。続いて `lex-fill` は、この証人を `LexAt` の充足に用いる `Differs` のデータへ変えます。そこには添字、その位置での狭義の比較、それ以前の各位置での等しさが記録され、`shiftEnv` が輸送後の第二のグラフを同一視します。こうして、命題的切り詰めから証人を取り出すことなく、比較の証拠から `≺At` の第三の枝を直接構成できます。
<!--/-->

```agda
      order-in (inr (ec , inr (ek , hv))) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inr (codeBack ec , inr (qa₂ ∙ cong #_ ek ∙ sym qa₁
          , lex-fill P a₁ e₁ e₂ γ t₁ t₂ qP qa₁ ek qe₁ (shiftEnv ek)
              (vec-lex (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂))
                (transport (sym (vecShift ek (params t₁) (params t₂))) hv)))))
```

<!--en-->
The reverse theorem retains the propositional truncation carried by the
object-language disjunctions and existentials. Accordingly, `≺At-out` exposes
the three cases only inside a truncation, and `PT.rec` may analyze them because
the target is itself the proposition `∥ t₁ ≺ₙ t₂ ∥₁`. In the code case, the
slot equations move the recorded pair membership back to `Rs`; `Rrep` then
reads it as the strict limit-order comparison of the two genuine codes and
supplies the first branch of the naming comparison.
<!--zh-->
反向定理保留对象语言析取与存在量词所携带的命题截断。因此，`≺At-out` 只能在截断内给出三种情形；目标本身是命题 `∥ t₁ ≺ₙ t₂ ∥₁`，故 `PT.rec` 可以在其中作情形分析。在码支中，各槽位等同把公式记录的有序对隶属搬回 `Rs`，`Rrep` 再将它读成两个真实码在极限序下的严格比较，从而给出名字比较的第一支。
<!--ja-->
逆向きの定理は、対象言語の選言と存在量化が伴う命題的切り詰めを保ちます。したがって `≺At-out` が三つの場合を取り出すのは切り詰めの内側だけです。目標自身が命題 `∥ t₁ ≺ₙ t₂ ∥₁` なので、`PT.rec` はその中で場合分けできます。符号の枝では、各スロットの同一視によって論理式に記録された順序対の所属を `Rs` へ戻し、`Rrep` がそれを二つの実際の符号の極限順序による狭義の比較として読みます。これが名前比較の第一の枝を与えます。
<!--/-->

```agda

      order-out : ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩ → ∥ t₁ ≺ₙ t₂ ∥₁
      order-out h = PT.rec squash₁ read (≺At-out R P s₁ a₁ e₁ s₂ a₂ e₂ γ h)
        where
        read : Below R P s₁ a₁ e₁ s₂ a₂ e₂ γ → ∥ t₁ ≺ₙ t₂ ∥₁
        read (inl k) = ∣ inl (Rrep (codeOf t₁) (codeOf t₂)
```

<!--en-->
In the arity case, the formula first says that the second skeleton slot equals
the first; `codeSame` lifts this underlying equality to equality of the two
codes in `Limit`. The other premise, transported through the arity-slot
equations, is membership of the first arity numeral in the second. Numeral
elimination converts that membership into `arity t₁ < arity t₂`, so equality
at the first key and strict comparison at the second assemble the arity branch
of `_≺ₙ_`.
<!--zh-->
在元数情形中，公式先给出第二个骨架槽等同于第一个；`codeSame` 把这条底层等同提升为两个码在 `Limit` 中的等同。另一项前提经元数槽等同搬运后，成为第一个元数数码属于第二个元数数码。数码消去把这项隶属化为 `arity t₁ < arity t₂`，于是第一个键的相等与第二个键的严格比较共同组成 `_≺ₙ_` 的元数支。
<!--ja-->
アリティの場合、論理式はまず第二の骨格スロットが第一の骨格スロットに等しいと述べます。`codeSame` はこの台の等しさを、二つの符号の `Limit` における等しさへ持ち上げます。もう一つの前提は、アリティスロットの同一視で輸送すると、第一のアリティの数項が第二のアリティの数項に属するという事実になります。数項についての消去がこの所属を `arity t₁ < arity t₂` へ変えるので、第一の鍵の等しさと第二の鍵の狭義の比較から `_≺ₙ_` のアリティの枝が組み立てられます。
<!--/-->

```agda
          (subst2 (λ y z → ⟨ pr y z ∈ fst Rs ⟩) qs₁ qs₂
            (subst (λ z → ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ z ⟩)
              qR k))) ∣₁
        read (inr (q , inl k)) = ∣ inr (codeSame q , inl
          (#∈#-elim (arity t₁) (arity t₂)
```

<!--en-->
The parameter case must first recover a common length. The formula gives an
equality from the second arity slot to the first; composing it with the two
slot equations yields equality of the corresponding von Neumann numerals, and
`#-inj′` recovers `ek : arity t₂ ≡ arity t₁`. With this path fixing the type of
the second vector, `lex-read` interprets the `LexAt` record against the two
environment graphs. Its result is an explicit first difference `Lex` still
inside propositional truncation, exactly preserving the existential boundary
of the formula.
<!--zh-->
参数情形必须先恢复一个共同长度。公式给出从第二个元数槽到第一个元数槽的等同；将它与两项槽位等同复合，便得到相应 von Neumann 数码的等同，`#-inj′` 再恢复 `ek : arity t₂ ≡ arity t₁`。这条路径使第二个向量具有可比较的类型以后，`lex-read` 依据两张环境图解释 `LexAt` 的记录。所得是仍处于命题截断内的显式首次相异 `Lex`，恰好保留了公式的存在见证边界。
<!--ja-->
パラメータの場合には、まず共通の長さを復元する必要があります。論理式は第二のアリティスロットから第一のアリティスロットへの等しさを与えます。これを二つのスロットの同一視と合成すると、対応する von Neumann 数項が等しいと分かり、`#-inj′` によって `ek : arity t₂ ≡ arity t₁` が得られます。この経路で第二のベクトルの型を比較可能な形にそろえると、`lex-read` は二つの環境グラフに照らして `LexAt` の記録を解釈します。結果は、命題的切り詰めの内側に保たれた明示的な最初の相違 `Lex` であり、論理式の存在証人に関する境界を正確に保っています。
<!--/-->

```agda
            (subst2 (λ y z → ⟨ y ∈ z ⟩) qa₁ qa₂ k))) ∣₁
        read (inr (q , inr (q' , dif))) = PT.map atLex
          (lex-read P a₁ e₁ e₂ γ t₁ t₂ qP qa₁ ek qe₁ (shiftEnv ek) dif)
          where
          ek : arity t₂ ≡ arity t₁
```

<!--en-->
Inside that truncation, `atLex` completes the third case. The induction
`lex-vec` turns the explicit first difference into the recursive vector order
against the transported second vector, and `vecShift` removes the transport
from the resulting proposition. Together with `codeSame q` and the recovered
arity path `ek`, this is the parameter branch of `_≺ₙ_`; `PT.map` keeps the
whole result truncated. Thus, under the two representation laws and the slot
identifications, `order-in` constructs satisfaction of `≺At` from a naming
comparison, while `order-out` recovers only `∥ t₁ ≺ₙ t₂ ∥₁`. This theorem is
the adequacy of the comparison formula itself; the corresponding readings of
`NameAt`, `LeastNameAt`, and `StepAt` require additional arguments.
<!--zh-->
在该截断内部，`atLex` 完成第三种情形。归纳 `lex-vec` 把显式首次相异化为第一个向量与搬运后第二个向量之间的递归向量序，`vecShift` 再从所得命题中消去这次搬运。把它与 `codeSame q` 及恢复出的元数路径 `ek` 合在一起，就得到 `_≺ₙ_` 的参数支；`PT.map` 则使整个结果仍处于截断内。因此，在两个序的表示律与各项槽位等同之下，`order-in` 从名字比较构造对 `≺At` 的满足，而 `order-out` 只恢复 `∥ t₁ ≺ₙ t₂ ∥₁`。这证明的是比较公式自身的充分性；`NameAt`、`LeastNameAt` 与 `StepAt` 的相应读式还需要另外的论证。
<!--ja-->
その切り詰めの内側で、`atLex` が第三の場合を完成させます。帰納法 `lex-vec` は明示的な最初の相違を、第一のベクトルと輸送後の第二のベクトルとの再帰的なベクトル順序へ変え、`vecShift` が得られた命題からその輸送を取り除きます。これに `codeSame q` と復元したアリティの経路 `ek` を合わせると `_≺ₙ_` のパラメータの枝となり、`PT.map` は結果全体を切り詰めの内側に保ちます。したがって、二つの順序の表示則と各スロットの同一視のもとで、`order-in` は名前比較から `≺At` の充足を構成し、`order-out` は `∥ t₁ ≺ₙ t₂ ∥₁` だけを復元します。ここで証明されたのは比較論理式そのものの妥当性であり、`NameAt`、`LeastNameAt`、`StepAt` の対応する読みには、さらに別の議論が必要です。
<!--/-->

```agda
          ek = #-inj′ (sym qa₂ ∙ q' ∙ qa₁)
          atLex : Lex (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂)) → t₁ ≺ₙ t₂
          atLex lx = inr (codeSame q , inr (ek
            , transport (vecShift ek (params t₁) (params t₂))
                (lex-vec (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂)) lx)))
```
