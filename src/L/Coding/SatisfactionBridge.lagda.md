<!--en-->
# Satisfaction and the recursion value
<!--zh-->
# 满足关系与递归取值
<!--ja-->
# 充足関係と再帰の値
<!--/-->

<!--en-->
The recursive construction `Sat` assigns to each formula a set of coded
environments, but its recursion equations acquire their intended meaning only
after those codes are compared with genuine assignments in the structure on
the members of `B`. The decisive choice is to use that restricted structure's
inner semantics. Its quantified variables already range over `B`, while a
bounded quantifier imposes the separate requirement of membership in the value
of its bounding term.
<!--zh-->
递归构造 `Sat` 为每条公式指定一个编码环境集，但只有把这些编码同 `B` 的成员结构中的真正赋值比较以后，那些递归方程才取得预期含义。这里的关键选择是采用该限制结构的内层语义：其中的量化变元已经遍历 `B`，而有界量词还另行要求变元属于界项的取值。
<!--ja-->
再帰的構成 `Sat` は各論理式に符号化された環境の集合を割り当てますが、その再帰方程式が意図した意味をもつためには、それらの符号を `B` の要素からなる構造の実際の割当てと比較しなければなりません。ここで重要なのは、この制限構造の内側の意味論を使うことです。量化変数はすでに `B` 上を動き、有界量化子はさらに、限界項の値への所属という別の条件を課します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The sole explicit hypothesis is excluded middle at level `ℓ-suc ℓ`. The
formula induction below does not split on propositions itself; the hypothesis
enters through the already constructed environment sets and satisfaction sets,
whose separation operations are parameterized by `lem`.
<!--zh-->
唯一显式的假设是层级 `ℓ-suc ℓ` 上的排中律。下文的公式归纳本身不对命题作分类讨论；这条假设经由已经构造好的环境集与满足集进入，而这些集合所用的分离运算以 `lem` 为参数。
<!--ja-->
明示的な仮定は、レベル `ℓ-suc ℓ` における排中律だけです。以下の論理式に関する帰納法そのものは命題について場合分けをしません。この仮定は、すでに構成された環境集合と充足集合を通して入ります。それらの分出は `lem` をパラメータとしているからです。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level and this classical instance. The chapter will compare two
descriptions of the same truth condition. On the coded side, an environment
belongs to the recursively defined set `Sat B φ`; on the semantic side, the
corresponding assignment satisfies `φ` in the structure whose domain consists
of the members of `B`. Constants must also name members of `B`, so that both
descriptions interpret them in that restricted structure.
<!--zh-->
固定一个宇宙层级与这份经典实例。本章要比较同一真值条件的两种描述。在编码一侧，一个环境属于递归定义的集合 `Sat B φ`；在语义一侧，对应的赋值在以 `B` 的成员为论域的结构中满足 `φ`。常元也必须指称 `B` 的成员，这样两种描述才能在同一个限制结构中解释它们。
<!--ja-->
一つの宇宙レベルと、この古典論理の実例を固定します。本章では、同じ真理条件の二つの記述を比較します。符号化された側では、環境が再帰的に定義された集合 `Sat B φ` に属します。意味論の側では、対応する割当てが、`B` の要素を論域とする構造で `φ` を充足します。二つの記述が同じ制限構造で定数を解釈できるように、定数も `B` の要素を名指すものに限ります。
<!--/-->

```agda
module L.Coding.SatisfactionBridge {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The proof follows the syntax of formulas. There are two atomic constructors,
three propositional connectives, falsity, two unbounded quantifiers, and two
quantifiers bounded by a term. Thus the semantic comparison has ten cases.
Terms and formulas may change their constant alphabet through `mapTm` and
`mapFo`, while `mapFo-comp` says that two successive changes agree with the
change along their composite. This is how a formula over members of `B` is
placed in the ambient constant alphabet without changing its syntactic shape.
<!--zh-->
证明沿公式的语法结构进行。公式有两个原子构造子、三个命题联结词、假、两个无界量词，以及两个受词项约束的有界量词，因此语义比较共有十种情形。词项与公式可分别通过 `mapTm` 和 `mapFo` 更换常元字母表，`mapFo-comp` 则说明连续两次更换等同于沿复合映射更换。由此，常元取自 `B` 的成员的公式可进入外围常元字母表，而其语法结构保持不变。
<!--ja-->
証明は論理式の構文に沿って進みます。論理式には二つの原子構成子、三つの命題結合子、偽、二つの非有界量化子、そして項で限界づけられた二つの有界量化子があります。したがって意味論の比較には十の場合があります。項と論理式の定数アルファベットは、それぞれ `mapTm` と `mapFo` によって取り替えられ、`mapFo-comp` は二度続けた取り替えが合成写像による取り替えと一致することを述べます。こうして `B` の要素を定数とする論理式を、その構文を変えずに周囲の定数アルファベットへ移せます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo; mapFo-comp )
```

<!--en-->
Relabelling is semantically exact. If constants are changed along a map `f`,
then evaluating `mapFo f φ` under an interpretation `ι` gives the same truth
value as evaluating `φ` under the composite interpretation `ι ∘ f`; this is
`⊨-map`. The chapter will use that equality when it passes between small
member indices, elements of the restricted structure, and constructible sets.
The surrounding hierarchy and its ordered-pair operation provide the sets from
which coded environments are built.
<!--zh-->
常元改名在语义上是精确的。若沿映射 `f` 更换常元，那么在解释 `ι` 下求值 `mapFo f φ`，所得真值与在复合解释 `ι ∘ f` 下求值 `φ` 相同；这正是 `⊨-map`。本章将在小成员索引、限制结构的元素与可构造集合之间转换时使用这条等式。外围层级及其有序对运算则提供构造编码环境所需的集合。
<!--ja-->
定数の改名は意味論的に正確です。写像 `f` に沿って定数を取り替えたとき、解釈 `ι` のもとで `mapFo f φ` を評価した真理値は、合成された解釈 `ι ∘ f` のもとで `φ` を評価した真理値と一致します。これが `⊨-map` です。本章では、小さな要素添字、制限構造の要素、構成可能集合の間を移るときに、この等式を用います。周囲の階層とその順序対演算は、符号化された環境を作る集合を供給します。
<!--/-->

```agda
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
```

<!--en-->
Three earlier constructions supply the mathematical data used by the bridge.
For a set `B`, `DefOf` gives the structure restricted to membership in `B` and
the subsets definable in that structure. Environment coding represents a
finite assignment by the graph of its values and represents extension by
prefixing one value. Finally, the environment-set construction collects all
such graphs of a fixed arity. The transitivity used here belongs to the class
`L`: it lets a member of a constructible set be regarded as constructible. It
does not assert that `B` itself is transitive.
<!--zh-->
先前三项构造提供这座桥所用的数学数据。对集合 `B`，`DefOf` 给出限制到 `B` 中隶属的结构，以及在该结构中可定义的子集。环境编码以取值的图表示有穷赋值，并以在前端加入一个值表示扩张。最后，环境集构造收集固定元数的全部此类图。这里使用的传递性属于类 `L`：它使可构造集合的成员仍可视为可构造。它并不断言 `B` 本身是传递的。
<!--ja-->
先行する三つの構成が、この橋で使う数学的データを供給します。集合 `B` に対して、`DefOf` は `B` への所属に制限した構造と、その構造で定義可能な部分集合を与えます。環境の符号化は有限の割当てを値のグラフで表し、一つの値を先頭に加えることで拡張を表します。最後に、環境集合の構成は、固定されたアリティをもつそのようなグラフをすべて集めます。ここで使う推移性はクラス `L` の推移性です。構成可能集合の要素を再び構成可能とみなすために用いられ、`B` 自身が推移的であることは主張しません。
<!--/-->

```agda
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Environment {ℓ} using ( env; cons; lookup-spec )
open import L.Coding.Expressions {ℓ} using ( consAtL; consAtL-adequate )
open import L.Coding.EnvironmentSet {ℓ} lem
```

<!--en-->
The coded and semantic sides already have complementary interfaces. An index
family gives the canonical graph `envS`, and `envSet-in` and `envSet-out` relate
canonical graphs to arbitrary members of `envSet`. The set `Sat B φ` is then
obtained by separating from `envSet B n` those graphs satisfying the recursive
condition `cond B φ`. The formula `tmIs` expresses a term-value relation, with
readers for its variable case, while the imported readers for atoms and
unbounded quantifiers translate those clauses in both directions. All these
statements describe `cond`; the additional requirement of belonging to
`envSet` remains a separate component of `Sat-mem`.
<!--zh-->
编码一侧与语义一侧已经具备互补的接口。索引族给出典范图 `envS`，`envSet-in` 与 `envSet-out` 则把典范图同 `envSet` 的任意成员联系起来。集合 `Sat B φ` 随后从 `envSet B n` 中分离出满足递归条件 `cond B φ` 的那些图。公式 `tmIs` 表达词项取值关系，并带有变元情形的读式；关于原子公式与无界量词的导入读式则在两个方向上翻译相应子句。这些陈述只解释 `cond`；属于 `envSet` 的附加要求仍是 `Sat-mem` 中独立的一项。
<!--ja-->
符号化された側と意味論の側には、すでに相補的なインターフェースがあります。添字族は正準なグラフ `envS` を与え、`envSet-in` と `envSet-out` は正準なグラフと `envSet` の任意の要素を結びます。集合 `Sat B φ` はさらに、再帰的条件 `cond B φ` を充足するグラフを `envSet B n` から分出して得られます。論理式 `tmIs` は項の値の関係を表し、その変数の場合を読む補題を伴います。原子論理式と非有界量化子に関する読み出しは、対応する節を両方向に翻訳します。これらの主張が説明するのは `cond` であり、`envSet` に属するという追加条件は `Sat-mem` の別の成分として残ります。
<!--/-->

```agda
  using ( Ix; envS; envSet; envSet-in; envSet-out )
open import L.Coding.Satisfaction {ℓ} lem
  using ( tmIs; tmIs-var-in; tmIs-var-out; cond; Sat; Sat-mem
        ; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
```

<!--en-->
The remaining readers treat the two bounded quantifiers. Together with the
preceding interfaces, they expose every non-propositional clause of `cond` in
both directions. A bounded clause keeps two restrictions distinct: the new
value must belong to the carrier `B`, and it must belong to the value of the
bounding term. The later induction will match these with the domain of the
restricted structure and the bound occurring in its inner semantics.
<!--zh-->
其余读式处理两个有界量词。它们与前面的接口合在一起，双向展开 `cond` 的每一条非命题子句。有界子句始终区分两重限制：新值必须属于载体 `B`，也必须属于界项的取值。后面的归纳会把它们分别对应到限制结构的论域与内层语义中的界。
<!--ja-->
残る読み出しは二つの有界量化子を扱います。先のインターフェースと合わせると、`cond` の命題結合子以外の各節を両方向に展開できます。有界な節では二つの制限を区別します。新しい値は台 `B` に属さなければならず、同時に限界項の値にも属さなければなりません。後の帰納法では、これらを制限構造の論域と、内側の意味論に現れる限界とにそれぞれ対応させます。
<!--/-->

```agda
        ; cond∃∈-in; cond∃∈-out; cond∀∈-in; cond∀∈-out )

```

<!--en-->
The proof compares proposition-valued statements by paths. `⇔toPath` turns two
implications between propositions into such a path, after which congruence can
carry the comparison through the logical constructors. In the membership atom,
`subst2` transports the relation after both candidate term values have been
identified with their semantic values. Existential clauses and environment
recovery use propositional truncation: a truncation is eliminated only when the
target is again a proposition, so no chosen witness is extracted.
<!--zh-->
证明以路径比较命题值陈述。`⇔toPath` 把命题之间的双向蕴涵变为这样的路径，随后同余便可把比较带过各逻辑构造子。在隶属原子情形，两个候选词项值都与各自的语义取值相认同后，`subst2` 沿这两条等式运输隶属关系。存在子句与环境恢复使用命题截断：只有当目标仍为命题时才消去截断，因而不会从中抽取被选定的见证。
<!--ja-->
証明は命題値の主張をパスによって比較します。`⇔toPath` は命題の間の二方向の含意をそのようなパスへ変え、その後は合同性によって比較を論理構成子の内部へ運べます。所属の原子の場合には、二つの候補となる項の値をそれぞれ意味論的な値と同定した後、`subst2` が二つの等式に沿って所属関係を輸送します。存在の節と環境の回復には命題的切り詰めを用います。切り詰めは目標が再び命題である場合にだけ除去されるので、選ばれた証人が取り出されることはありません。
<!--/-->

```agda
open import Cubical.Foundations.Prelude using ( subst2; funExt⁻ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
```

<!--en-->
A hierarchy set comes with a small presentation of its members. For a proof
that `a ∈ B`, the equivalence `∈-asFiber` returns an index in `⟪ B ⟫` together
with a path from the member presented by that index to `a`. The two directions
between small presentation membership and ordinary hierarchy membership let
the proof move between these views. This presentation is crucial because an
inner assignment already contains the proofs that its entries belong to `B`,
so its index family can be obtained directly.
<!--zh-->
层级中的集合带有其成员的小表现。给定 `a ∈ B` 的证明，等价 `∈-asFiber` 返回 `⟪ B ⟫` 中的一个索引，并给出从该索引所表现的成员到 `a` 的路径。小表现中的隶属与通常的层级隶属之间可双向转换，使证明能在两种观察方式之间移动。这项表现至关重要，因为内层赋值已经包含每个条目属于 `B` 的证明，所以可以直接取得它的索引族。
<!--ja-->
階層の集合には、その要素の小さな表示が備わっています。`a ∈ B` の証明から、同値 `∈-asFiber` は `⟪ B ⟫` の添字と、その添字が表示する要素から `a` へのパスを返します。小さな表示での所属と通常の階層での所属の二方向の変換により、証明は二つの見方の間を移れます。この表示が重要なのは、内側の割当てが各項目の `B` への所属証明をすでに含み、そこから添字族を直接得られるからです。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
```

<!--en-->
Finite environments use von Neumann numerals as keys. Thus a position
`i : Fin n` is recorded in its graph by the set `# (toℕ i)`. Naming the numeral
constructor here connects the finite index used by a term variable with the
set-theoretic key used by the coded environment.
<!--zh-->
有穷环境以 von Neumann 数码为键。因此，位置 `i : Fin n` 在图中由集合 `# (toℕ i)` 记录。此处引入数码构造，是为了把词项变元所用的有穷索引与编码环境所用的集合论键连接起来。
<!--ja-->
有限環境は von Neumann 数項をキーとして用います。したがって位置 `i : Fin n` は、そのグラフでは集合 `# (toℕ i)` によって記録されます。ここで数項の構成子を導入することで、項の変数が使う有限添字と、符号化された環境が使う集合論的なキーとが結ばれます。
<!--/-->

```agda
open InfinitySet using ( #_ )

```

<!--en-->
Opening the constructible universe as an `hProp`-valued structure fixes the
host carrier `S`, whose elements are sets equipped with proofs of
constructibility. It also supplies the proposition-valued membership notation
`_∈ˢ_` and the brackets `⟨_⟩` for its underlying proof type. Consequently the
equalities proved below compare truth values themselves; they are neither
equalities of hierarchy sets nor untruncated equivalences carrying extra data.
<!--zh-->
把可构造宇宙作为 `hProp` 值结构打开，便固定了宿主载体 `S`，其元素是配有可构造性证明的集合；同时也得到命题值隶属记号 `_∈ˢ_`，以及取其底层证明类型的括号 `⟨_⟩`。因此，下文的等式比较的是真值本身；它们既不是层级集合之间的等式，也不是携带额外数据的未截断等价。
<!--ja-->
構成可能宇宙を `hProp` 値の構造として開くと、構成可能性の証明を備えた集合からなる周囲の台 `S` が定まります。同時に、命題値の所属を表す `_∈ˢ_` と、その基礎の証明型を取り出す括弧 `⟨_⟩` も得られます。したがって以下の等式が比較するのは真理値そのものです。階層の集合の等式でも、追加のデータを運ぶ切り詰められていない同値でもありません。
<!--/-->

```agda
open hPropStructure 𝒮ʟ

```

<!--en-->
The object-language conditions imported above are interpreted in the
structure carried by all constructible sets. Instantiating the general
absoluteness construction with the class `isL` gives this host satisfaction
relation, written `_⊨_`, and the fixed-length environment notation `_^_`.
Its variables range over constructible sets. This host semantics reads coded
formulas such as `cond B φ` after the membership equation for `Sat` has been
opened. It is an intermediate layer on the coded side and must be kept distinct
from the still smaller structure whose domain is the members of one particular
set `B`.
<!--zh-->
前面导入的对象语言条件在由全部可构造集合承载的结构中解释。把一般绝对性构造实例化于类 `isL`，便得到这条宿主满足关系，记作 `_⊨_`，以及定长环境记号 `_^_`；其中变元遍历可构造集合。打开 `Sat` 的成员等式后，这套宿主语义用于读取编码公式 `cond B φ`。它是编码一侧的中间层，必须同论域仅为某个特定集合 `B` 的成员的更小结构区分开来。
<!--ja-->
先に導入した対象言語の条件は、すべての構成可能集合が担う構造で解釈されます。一般の絶対性の構成をクラス `isL` に具体化すると、この周囲の充足関係 `_⊨_` と、固定長の環境を表す `_^_` が得られます。その変数は構成可能集合を動きます。`Sat` の所属の等式を開いた後、この周囲の意味論が `cond B φ` のような符号化された論理式を読みます。これは符号化された側の中間層であり、論域が一つの特定の集合 `B` の要素だけからなる、さらに小さな構造とは区別しなければなりません。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The restricted structure on the carrier
<!--zh-->
## 载体上的限制结构
<!--ja-->
## 台上の制限構造
<!--/-->

<!--en-->
Now fix `B : S`. Applying `DefOf` to its underlying hierarchy set constructs
the restricted domain `DB.SM`: an element is a set together with a proof that
it belongs to `B`. The structure `DB.𝒮M` interprets membership and equality on
that domain. Opening ordinary first-order semantics there with the identity
constant interpretation yields `_⊨ᴮ_` and `⟦_⟧ᴮ`. These are exactly the inner
satisfaction and term evaluation used in the definition of `DB.defSet`, so the
semantic endpoint of the bridge and the definable subsets share one restricted
structure.
<!--zh-->
现在固定 `B : S`。把 `DefOf` 施用于它的底层层级集合，得到限制论域 `DB.SM`：其中一个元素由一个集合及其属于 `B` 的证明组成。结构 `DB.𝒮M` 在该论域上解释隶属与相等。在那里以恒等常元解释打开一般一阶语义，便得到 `_⊨ᴮ_` 与 `⟦_⟧ᴮ`。它们正是定义 `DB.defSet` 所用的内层满足与词项求值，因此桥的语义终点和可定义子集共享同一个限制结构。
<!--ja-->
ここで `B : S` を固定します。その基礎となる階層の集合に `DefOf` を適用すると、制限された論域 `DB.SM` が得られます。その要素は、集合と、それが `B` に属することの証明との対です。構造 `DB.𝒮M` は、この論域の上で所属と等号を解釈します。そこで定数の恒等解釈を用いて通常の一階意味論を開くと、`_⊨ᴮ_` と `⟦_⟧ᴮ` が得られます。これらは `DB.defSet` の定義に使われる内側の充足と項の評価そのものなので、橋の意味論的な終点と定義可能部分集合は同じ制限構造を共有します。
<!--/-->

```agda
module _ (B : S) where
  module DB = DefOf (fst B)
  module SemB = FOL.Semantics DB.𝒮M
  open SemB.At DB.SM id using () renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

```

<!--en-->
An element `x : DB.SM` already consists of an underlying set `fst x` and a
proof `snd x` that this set belongs to `B`. Since `B` is constructible and the
class `L` is transitive, `fst x` is constructible as well. The map `intoL`
keeps the underlying set and supplies precisely this new certificate, producing
an element of the host carrier `S`. No closure of `B` under membership is used.
<!--zh-->
元素 `x : DB.SM` 已经由底层集合 `fst x` 及其属于 `B` 的证明 `snd x` 组成。由于 `B` 可构造且类 `L` 具有传递性，`fst x` 也可构造。映射 `intoL` 保留底层集合，只补上这份新的证书，从而得到宿主载体 `S` 的元素。这里没有使用 `B` 对隶属封闭的性质。
<!--ja-->
要素 `x : DB.SM` は、基礎の集合 `fst x` と、それが `B` に属することの証明 `snd x` からすでに成ります。`B` が構成可能であり、クラス `L` が推移的なので、`fst x` も構成可能です。写像 `intoL` は基礎の集合を保ったまま、この新しい証明書だけを補い、周囲の台 `S` の要素を作ります。ここでは `B` が所属について閉じているとは仮定しません。
<!--/-->

```agda
  intoL : DB.SM → S
  intoL x = fst x , isL-trans {x = fst B} {y = fst x} (snd x) (snd B)

```

<!--en-->
There is one more constant alphabet to connect. An index
`m : ⟪ fst B ⟫` presents a member of `B`; `DB.ι m` packages that member with
its membership proof as an element of `DB.SM`, and `intoL` regards the same
underlying set as an element of `S`. Their composite `asConst` is therefore
the constant map used when a formula indexed by the small presentation is read
by the host semantics. The presentation map `DB.ι` and the inclusion `intoL`
play different roles, even though their composite preserves the named set.
<!--zh-->
还需连接一层常元字母表。索引 `m : ⟪ fst B ⟫` 表现 `B` 的一个成员；`DB.ι m` 把该成员及其隶属证明包装为 `DB.SM` 的元素，`intoL` 再把同一底层集合视为 `S` 的元素。故其复合 `asConst` 正是把小表现所索引的公式交给宿主语义读取时所用的常元映射。表现映射 `DB.ι` 与包含 `intoL` 承担不同角色，尽管它们的复合保持被指称的集合不变。
<!--ja-->
さらにもう一つ、定数アルファベットを結ぶ必要があります。添字 `m : ⟪ fst B ⟫` は `B` の一つの要素を表示します。`DB.ι m` はその要素と所属証明を組にして `DB.SM` の要素を作り、`intoL` は同じ基礎集合を `S` の要素とみなします。その合成 `asConst` は、小さな表示で添字づけられた論理式を周囲の意味論で読むときの定数写像です。表示写像 `DB.ι` と包含 `intoL` は異なる役割をもちますが、その合成は名指された集合を変えません。
<!--/-->

```agda
  asConst : ⟪ fst B ⟫ → S
  asConst m = intoL (DB.ι m)
```

<!--en-->
## Coding an inner assignment as an environment
<!--zh-->
## 把内层赋值编码为环境
<!--ja-->
## 内側の割当てを環境として符号化する
<!--/-->

<!--en-->
An inner environment `δ : DB.SM ^ n` stores, at every position, both a set and
its proof of membership in `B`. The coded environment needs only the sets.
Accordingly, `values δ` projects each entry to its first component. This
underlying family is kept explicit because both term evaluation and extension
will be compared with its finite graph.
<!--zh-->
内层环境 `δ : DB.SM ^ n` 在每个位置同时存放一个集合及其属于 `B` 的证明，而编码环境只需记录这些集合。因此，`values δ` 把每个条目投影到其第一分量。这里显式保留这个底层值族，因为词项求值与环境扩张都将同它的有穷图作比较。
<!--ja-->
内側の環境 `δ : DB.SM ^ n` は、各位置に集合とその `B` への所属証明をともに保存します。符号化された環境が必要とするのは集合だけです。そこで `values δ` は各項目を第一成分へ射影します。この基礎の値族を明示的に保つのは、項の評価と環境の拡張を、どちらもその有限グラフと比較するためです。
<!--/-->

```agda
  values : ∀ {n} → DB.SM ^ n → Fin n → V ℓ
  values δ i = fst (lookup i δ)

```

<!--en-->
The set `graph δ` is the finite graph of this family: at position `i` it records
the ordered pair whose key is the numeral for `i` and whose value is
`values δ i`. Thus the inner vector and the hierarchy set carry the same
assignment in two forms. The following lemmas establish the precise equations
needed to pass between them.
<!--zh-->
集合 `graph δ` 是这个值族的有穷图：在位置 `i`，它记录一个有序对，其键是 `i` 的数码，其值是 `values δ i`。因此，内层向量与层级集合以两种形式携带同一赋值。下面的引理将建立在二者之间转换所需的精确等式。
<!--ja-->
集合 `graph δ` は、この値族の有限グラフです。位置 `i` には、`i` の数項をキーとし、`values δ i` を値とする順序対が記録されます。したがって内側のベクトルと階層の集合は、同じ割当てを二つの形で保持します。以下の補題は、この二つの間を移るために必要な正確な等式を与えます。
<!--/-->

```agda
  graph : ∀ {n} → DB.SM ^ n → V ℓ
  graph δ = env (values δ)

```

<!--en-->
Binding a variable extends an assignment by placing a new value at its front.
On underlying families this is the operation `cons (fst x) (values δ)`, whereas
on inner vectors it is `x ∷ δ`. The lemma `cons-values` identifies the two
pointwise: both give `fst x` at the new first position and the old value at
every shifted position. This single coherence equation is reused by all four
quantifier cases.
<!--zh-->
绑定一个变元，就是在赋值前端加入一个新值。对底层值族而言，这是运算 `cons (fst x) (values δ)`；对内层向量而言，则是 `x ∷ δ`。引理 `cons-values` 逐点认同二者：在新的首位，两侧都给出 `fst x`；在每个后移位置，两侧都给出原来的值。这一条相干等式会由四种量词情形共同复用。
<!--ja-->
変数を束縛することは、割当ての先頭に新しい値を加えることです。基礎の値族ではこれは `cons (fst x) (values δ)` であり、内側のベクトルでは `x ∷ δ` です。補題 `cons-values` は両者を各点で同定します。新しい先頭ではどちらも `fst x` を与え、後ろへずれた各位置ではどちらも以前の値を与えます。この一つの整合性の等式が、四つの量化子の場合すべてで再利用されます。
<!--/-->

```agda
  private
    cons-values : ∀ {n} (x : DB.SM) (δ : DB.SM ^ n)
                → cons (fst x) (values δ) ≡ values (x ∷ δ)
    cons-values x δ = funExt (λ { zero → refl ; (suc i) → refl })

```

<!--en-->
The vector itself determines an index family for the small presentation of
`B`. At position `i`, the second component of `lookup i δ` proves that the
underlying value belongs to `B`. Applying `∈-asFiber` to that proof gives the
index `index δ i`. This construction uses the membership evidence already
stored in the vector, so it involves no propositional truncation and no choice
of a representative recovered from a coded graph.
<!--zh-->
向量本身决定 `B` 的小表现中的一个索引族。在位置 `i`，`lookup i δ` 的第二分量证明该底层值属于 `B`；把 `∈-asFiber` 施用于这份证明，便得到索引 `index δ i`。这项构造直接使用向量中已有的成员证据，所以既不涉及命题截断，也不需要从编码图中恢复并选择一个代表。
<!--ja-->
ベクトルそのものが、`B` の小さな表示における添字族を定めます。位置 `i` では、`lookup i δ` の第二成分が、その基礎の値が `B` に属することを証明します。この証明に `∈-asFiber` を適用して、添字 `index δ i` を得ます。この構成はベクトルにすでに保存された所属の証拠を直接使うため、命題的切り詰めも、符号化されたグラフから回復した代表の選択も含みません。
<!--/-->

```agda
    index : ∀ {n} (δ : DB.SM ^ n) → Ix B n
    index δ i = ∈-asFiber {a = values δ i} {b = fst B} (snd (lookup i δ)) .fst

```

<!--en-->
The fibre equivalence returns more than the index: it also identifies the
member presented by that index with the original underlying value.
`index-eq δ i` records this path at every position. Hence the family presented
by `index δ` and the family `values δ` agree pointwise, which is the exact input
needed to compare their finite graphs.
<!--zh-->
纤维等价交付的不只有索引；它还把该索引所表现的成员与原来的底层值认同起来。`index-eq δ i` 在每个位置记录这条路径。因此，由 `index δ` 表现的值族与 `values δ` 逐点相同，这正是比较二者有穷图所需的输入。
<!--ja-->
ファイバーの同値が返すのは添字だけではありません。その添字が表示する要素と、もとの基礎の値との同一視も返します。`index-eq δ i` は各位置でこのパスを記録します。したがって `index δ` が表示する値族と `values δ` は各点で一致し、有限グラフを比較するための正確な入力が得られます。
<!--/-->

```agda
    index-eq : ∀ {n} (δ : DB.SM ^ n) (i : Fin n)
             → ⟪ fst B ⟫↪ (index δ i) ≡ values δ i
    index-eq δ i = ∈-asFiber {a = values δ i} {b = fst B} (snd (lookup i δ)) .snd

```

<!--en-->
Using this index family in the canonical environment constructor gives
`envFor δ`, an element of the constructible host structure. It is the canonical
hierarchy code associated with the concrete vector `δ`. The next two facts
identify its underlying graph and then prove its membership in the environment
set; no arbitrary environment representative has been selected.
<!--zh-->
把这个索引族交给典范环境构造子，便得到 `envFor δ`，它是可构造宿主结构的一个元素，也是与具体向量 `δ` 对应的典范层级编码。接下来的两项事实先认出它的底层图，再证明它属于环境集；其中没有选择任意的环境代表。
<!--ja-->
この添字族を正準な環境の構成子に渡すと、構成可能な周囲の構造の要素 `envFor δ` が得られます。これは具体的なベクトル `δ` に対応する、階層における正準な符号です。続く二つの事実が、その基礎のグラフを同定し、さらに環境集合への所属を証明します。任意の環境の代表を選んではいません。
<!--/-->

```agda
  envFor : ∀ {n} → DB.SM ^ n → S
  envFor δ = envS B (index δ)

```

<!--en-->
The underlying hierarchy set of `envFor δ` is exactly `graph δ`.
Function extensionality combines the pointwise paths `index-eq δ i` into an
equality of value families, and congruence of `env` turns that equality into
`envFor-graph`. This path of underlying sets is the interface used later. In
particular, extending `δ` to `x ∷ δ` produces a new canonical environment to
which the same theorem applies, without comparing witnesses hidden inside a
truncation.
<!--zh-->
`envFor δ` 的底层层级集合恰为 `graph δ`。函数外延性把逐点路径 `index-eq δ i` 合成为值族之间的等式，`env` 的同余再把它变为 `envFor-graph`。这条底层集合的路径就是后文所用的接口。特别地，把 `δ` 扩张为 `x ∷ δ` 后会得到一个新的典范环境，同一定理可再次施用，无须比较隐藏在截断中的见证。
<!--ja-->
`envFor δ` の基礎となる階層の集合は、ちょうど `graph δ` です。関数外延性が各点のパス `index-eq δ i` を値族の等式にまとめ、`env` の合同性がそれを `envFor-graph` に変えます。後で使うインターフェースは、この基礎集合のパスです。特に、`δ` を `x ∷ δ` へ拡張すると新しい正準な環境が得られ、切り詰めの中に隠れた証人を比較せずに、同じ定理を再び適用できます。
<!--/-->

```agda
  envFor-graph : ∀ {n} (δ : DB.SM ^ n) → fst (envFor δ) ≡ graph δ
  envFor-graph δ = cong env (funExt (index-eq δ))

```

<!--en-->
The first consequence runs from a known vector to environment-set membership.
Suppose `z : S` has underlying set `graph δ`. The canonical environment
`envFor δ` belongs to `envSet B n` by `envSet-in`, and `envFor-graph` together
with the assumed path transports that membership to `z`. This proves
`graph-envSet`. Its direction is exactly what the later membership equation
needs when it removes the common environment requirement from `Sat B φ`.
The converse direction is different: `envSet-out` recovers an index family
only under propositional truncation. A later construction turns that family
into a vector, still under truncation, and keeps the recovery outside the
formula induction.
<!--zh-->
第一个推论从已知向量走向环境集中的隶属。设 `z : S` 的底层集合为 `graph δ`。典范环境 `envFor δ` 由 `envSet-in` 属于 `envSet B n`，再用 `envFor-graph` 与所给路径把这项隶属运输到 `z`，便得到 `graph-envSet`。后面的成员等式要从 `Sat B φ` 中消去共同的环境要求，所需的恰是这个方向。反方向具有不同的逻辑强度：`envSet-out` 只能在命题截断之下恢复一个索引族，后续构造仍在截断之下把它转成向量，并使这项恢复始终留在公式归纳之外。
<!--ja-->
最初の帰結は、既知のベクトルから環境集合への所属へ進みます。`z : S` の基礎集合が `graph δ` であるとします。正準な環境 `envFor δ` は `envSet-in` によって `envSet B n` に属し、`envFor-graph` と仮定したパスに沿ってその所属を `z` へ輸送すれば、`graph-envSet` が得られます。後の所属の等式が `Sat B φ` から共通の環境条件を取り除くときに必要とするのは、まさにこの向きです。逆向きは論理的な強さが異なります。`envSet-out` が回復する添字族は命題的切り詰めの中にあり、後の構成がそれをベクトルへ変換するときも切り詰めを保ちます。この回復は論理式に関する帰納法の外に置かれます。
<!--/-->

```agda
  graph-envSet : ∀ {n} (δ : DB.SM ^ n) (z : S)
               → fst z ≡ graph δ → ⟨ z ∈ˢ envSet B n ⟩
  graph-envSet {n} δ z q = subst (λ w → ⟨ w ∈ fst (envSet B n) ⟩)
    (envFor-graph δ ∙ sym q) (envSet-in B (index δ))

```

<!--en-->
The graph equation now removes the common environment requirement from the
membership equation. `Sat-mem`{.Agda} says that membership in `Sat B φ` is the
conjunction of membership in `envSet B n` and satisfaction of `cond B φ`.
Given `fst z ≡ graph δ`, the previous lemma supplies the first conjunct, so
the second conjunct is equivalent to the whole statement. `⇔toPath` turns
the two implications into a path of truth values. Thus `Sat-cond`{.Agda}
does not yet interpret the formula; it isolates the recursive condition that
the following induction will interpret.
<!--zh-->
图等式现在可以从成员等式中消去共同的环境要求。`Sat-mem`{.Agda}
说明，`z` 属于 `Sat B φ` 当且仅当它既属于 `envSet B n`，又满足`cond B φ`。给定 `fst z ≡ graph δ`，上一条引理已经提供前一个合取支，所以后一支与整个陈述逻辑等价；`⇔toPath` 再把两个方向的蕴涵变成真值之间的路径。因此，`Sat-cond`{.Agda} 还没有解释公式的语义，它只是分离出接下来要由归纳解释的递归条件。
<!--ja-->
グラフの等式により、所属の等式から共通の環境条件を取り除けます。`Sat-mem`{.Agda} は、`z` が `Sat B φ` に属すことを、`envSet B n` への所属と `cond B φ` の充足との論理積として表します。`fst z ≡ graph δ` が与えられれば、直前の補題から前者が得られるので、後者は論理積全体と論理的に同値です。`⇔toPath` はその二方向の含意を真理値の間のパスにします。したがって `Sat-cond`{.Agda} はまだ論理式の意味を説明せず、次の帰納法で解釈すべき再帰条件だけを取り出します。
<!--/-->

```agda
  Sat-cond : ∀ {n} (φ : Formula S n) (δ : DB.SM ^ n) (z : S)
           → fst z ≡ graph δ
           → (z ∈ˢ Sat B φ) ≡ ((z ∷ []) ⊨ cond B φ)
  Sat-cond φ δ z q =
    Sat-mem B φ z ∙ ⇔toPath snd (λ h → graph-envSet δ z q , h)
```

<!--en-->
## Reading terms and environment extension
<!--zh-->
## 读取词项与环境扩张
<!--ja-->
## 項と環境拡張を読み取る
<!--/-->

<!--en-->
The first reading lemma compares the object-language term predicate with
actual term evaluation. In an ambient environment `γ`, slot `ei` contains a
coded assignment and slot `vi` contains a proposed value. If the former has
underlying set `graph δ`, then satisfaction of `tmIs (mapTm intoL t) vi ei`
forces the latter to have underlying set `fst (⟦ t ⟧ᴮ δ)`. For a constant,
the predicate is already the required equation: relabelling by `intoL`
changes only the packaged carrier, while its underlying set remains the
constant's value.
<!--zh-->
第一条读引理把对象语言的词项谓词与实际的词项求值比较。在外围环境`γ` 中，槽位 `ei` 存放编码赋值，槽位 `vi` 存放候选取值。若前者的底层集合是 `graph δ`，那么满足 `tmIs (mapTm intoL t) vi ei` 就迫使后者的底层集合等于 `fst (⟦ t ⟧ᴮ δ)`。对常元而言，该谓词本身就是所需的等式：沿 `intoL` 作常元改名只改变载体的包装，底层集合仍是这个常元的取值。
<!--ja-->
最初の読み補題は、対象言語の項述語と実際の項評価を比較します。周囲の環境 `γ` では、スロット `ei` が符号化された割当てを、スロット `vi`が候補の値を収めます。前者の基礎集合が `graph δ` なら、`tmIs (mapTm intoL t) vi ei` の充足から、後者の基礎集合が`fst (⟦ t ⟧ᴮ δ)` に等しいことが従います。定数の場合、この述語はすでに求める等式です。`intoL` による定数の改名は台の包装だけを変え、基礎集合はその定数の値のままです。
<!--/-->

```agda
  tmIs-out : ∀ {n k} (t : Term DB.SM n) (δ : DB.SM ^ n) (γ : S ^ k) (vi ei : Fin k)
           → fst (lookup ei γ) ≡ graph δ
           → ⟨ γ ⊨ tmIs (mapTm intoL t) vi ei ⟩
           → fst (lookup vi γ) ≡ fst (⟦ t ⟧ᴮ δ)
  tmIs-out (con c) δ γ vi ei qe h = h
```

<!--en-->
For a variable, `tmIs-var-out`{.Agda} reads satisfaction as membership of the
pair consisting of the numeral key and the proposed value in the graph held
at `ei`. Its existential witness is propositionally truncated, but the target
membership is a proposition, so eliminating the truncation loses nothing
needed here. Transport along `qe` replaces that graph by `graph δ`, and
`lookup-spec`{.Agda} identifies membership at key `i` with equality to the
`i`th value of `δ`. This functionality of the coded graph is exactly the
variable case of term evaluation.
<!--zh-->
对变元，`tmIs-var-out`{.Agda} 把满足关系读成一条图成员关系：由索引数码与候选取值组成的对，属于 `ei` 处存放的图。它的存在见证经过命题截断，但目标成员关系是命题，所以在这里消去截断不会丢失所需信息。沿 `qe`运输后，该图变成 `graph δ`；`lookup-spec`{.Agda} 再把键 `i` 处的成员关系等同于候选取值与 `δ` 的第 `i` 项相等。这种编码图的函数性正是词项求值的变元情形。
<!--ja-->
変数の場合、`tmIs-var-out`{.Agda} は充足関係をグラフへの所属として読みます。添字の数項と候補の値との対が、`ei` に収められたグラフに属すという所属です。その存在証人は命題的に切り詰められていますが、目標の所属は命題なので、ここでの除去によって必要な情報は失われません。`qe` に沿って輸送するとグラフは `graph δ` になり、`lookup-spec`{.Agda} はキー `i` での所属を、候補の値が `δ` の第 `i`項に等しいことと同一視します。符号化グラフのこの関数性が、項評価の変数の場合にほかなりません。
<!--/-->

```agda
  tmIs-out (var i) δ γ vi ei qe h =
    subst ⟨_⟩ (lookup-spec (values δ) i (fst (lookup vi γ)))
      (subst (λ w → ⟨ pr (# (toℕ i)) (fst (lookup vi γ)) ∈ w ⟩) qe
        (tmIs-var-out i γ vi ei h))

```

<!--en-->
The converse lemma constructs the term predicate from the semantic value
equation. Its constant case is again immediate: after relabelling, the
object-language equation asks precisely for the equation supplied as the
hypothesis. Together, `tmIs-out`{.Agda} and `tmIs-in`{.Agda} make term values
available in either direction. The atomic clauses will use the pair to compare
two evaluated terms, and the bounded-quantifier clauses will use it to read
the value of their bounding term.
<!--zh-->
反向引理从语义取值等式构造词项谓词的满足。常元情形仍然是直接的：常元改名之后，对象语言等式所要求的恰是作为假设给出的等式。`tmIs-out`{.Agda} 与 `tmIs-in`{.Agda} 合在一起，使词项取值可以双向读取。原子子句会用这对引理比较两个已求值词项，有界量词子句则会用它们读取界项的取值。
<!--ja-->
逆向きの補題は、意味論的な値の等式から項述語の充足を構成します。定数の場合も直ちに従います。定数を改名した後に対象言語の等式が要求するのは、仮定として与えられた等式そのものです。`tmIs-out`{.Agda} と
`tmIs-in`{.Agda} を合わせると、項の値をどちらの向きにも読めます。原子の節ではこの二つの補題で評価済みの二項を比較し、有界量化子の節では限界項の値を読みます。
<!--/-->

```agda
  tmIs-in : ∀ {n k} (t : Term DB.SM n) (δ : DB.SM ^ n) (γ : S ^ k) (vi ei : Fin k)
          → fst (lookup ei γ) ≡ graph δ
          → fst (lookup vi γ) ≡ fst (⟦ t ⟧ᴮ δ)
          → ⟨ γ ⊨ tmIs (mapTm intoL t) vi ei ⟩
  tmIs-in (con c) δ γ vi ei qe q = q
```

<!--en-->
In the variable case, the earlier argument is reversed. `lookup-spec`{.Agda}
turns the assumed value equation into membership of the keyed pair in
`graph δ`; transport along the symmetric graph equation moves that membership
to the graph stored at `ei`; and `tmIs-var-in`{.Agda} packages it as
satisfaction of the object-language predicate. The two directions therefore
express the same functional graph fact, without choosing a representative
from any truncation.
<!--zh-->
变元情形把刚才的论证反向进行。`lookup-spec`{.Agda} 先把假设的取值等式变成带键的对属于 `graph δ`；再沿图等式的对称方向运输，把这条成员关系移到 `ei` 处存放的图中；最后，`tmIs-var-in`{.Agda} 将其包装成对象语言谓词的满足关系。两个方向因而表达同一项函数图事实，并不从任何截断中选取代表。
<!--ja-->
変数の場合には、先ほどの議論を逆向きにたどります。`lookup-spec`{.Agda} が仮定された値の等式を、キー付きの対の`graph δ` への所属に変えます。次にグラフの等式を逆向きに用いて、その所属を `ei` に収められたグラフへ輸送し、`tmIs-var-in`{.Agda} が対象言語の述語の充足として包みます。したがって二方向が表すのは同じ関数的グラフの事実であり、切り詰めから代表を選ぶことはありません。
<!--/-->

```agda
  tmIs-in (var i) δ γ vi ei qe q = tmIs-var-in i γ vi ei
    (subst (λ w → ⟨ pr (# (toℕ i)) (fst (lookup vi γ)) ∈ w ⟩) (sym qe)
      (subst ⟨_⟩ (sym (lookup-spec (values δ) i (fst (lookup vi γ)))) q))

```

<!--en-->
The second pair of readings concerns extension of an assignment. In
`consAtL ei mi di`, slot `di` holds the old graph, slot `mi` holds the new
leading value, and slot `ei` is proposed as the extended graph. If the first
two slots agree with `δ` and `x`, satisfaction of this predicate implies that
the underlying set at `ei` is `graph (x ∷ δ)`. This is the equation needed
when a quantified formula passes from an assignment to the assignment with
one new leading entry.
<!--zh-->
第二对读引理处理赋值的扩张。在 `consAtL ei mi di` 中，槽位 `di` 存放旧图，槽位 `mi` 存放新添的首值，槽位 `ei` 则是候选的扩张图。若前两个槽位分别与 `δ` 和 `x` 相符，那么满足该谓词便推出 `ei` 处的底层集合是`graph (x ∷ δ)`。量化公式从原赋值转到前端增加一个条目的赋值时，需要的正是这条等式。
<!--ja-->
第二の一対の読み補題は、割当ての拡張を扱います。`consAtL ei mi di` では、スロット `di` が古いグラフを、`mi` が新しい先頭値を収め、`ei` が拡張後のグラフの候補になります。最初の二つのスロットがそれぞれ `δ` と `x` に対応しているなら、この述語の充足から`ei` の基礎集合が `graph (x ∷ δ)` であることが従います。量化された論理式が、元の割当てから先頭に一項を加えた割当てへ移るときに必要なのがこの等式です。
<!--/-->

```agda
  consAtL-out : ∀ {n k} (δ : DB.SM ^ n) (x : DB.SM) (γ : S ^ k) (ei mi di : Fin k)
              → fst (lookup di γ) ≡ graph δ
              → fst (lookup mi γ) ≡ fst x
              → ⟨ γ ⊨ consAtL ei mi di ⟩
              → fst (lookup ei γ) ≡ graph (x ∷ δ)
```

<!--en-->
The proof first applies `consAtL-adequate`{.Agda}. Under the old-graph
hypothesis, that path identifies the proposed extension slot with
`env (cons (fst (lookup mi γ)) (values δ))`. The equation `qm` replaces its
head by `fst x`, and `cons-values`{.Agda} identifies the resulting family with
the underlying values of `x ∷ δ`. Congruence of `env` then gives the announced
graph equation. In particular, the adequacy law yields an equality with the
extended graph; no graph-membership statement occurs here.
<!--zh-->
证明先使用 `consAtL-adequate`{.Agda}。在旧图假设下，这条路径把候选扩张槽位等同于 `env (cons (fst (lookup mi γ)) (values δ))`。等式 `qm` 把其首值替换为 `fst x`，`cons-values`{.Agda} 再把所得的族等同于 `x ∷ δ`的底层取值族。最后对 `env` 使用同余，便得到所宣称的图等式。尤其要注意，充分性律给出的是与扩张图的相等，而不是在该图中的成员关系。
<!--ja-->
証明はまず `consAtL-adequate`{.Agda} を使います。古いグラフについての仮定のもとで、このパスは拡張スロットの候補を`env (cons (fst (lookup mi γ)) (values δ))` と同一視します。等式 `qm`がその先頭値を `fst x` に置き換え、`cons-values`{.Agda} が得られた族を`x ∷ δ` の基礎の値の族と同一視します。最後に `env` の合同性を使えば、求めるグラフの等式が得られます。ここで妥当性の法則が与えるのは拡張グラフとの等式であって、そのグラフへの所属ではありません。
<!--/-->

```agda
  consAtL-out δ x γ ei mi di qd qm h =
      subst ⟨_⟩ (consAtL-adequate ei mi di γ (values δ) qd) h
    ∙ cong env (cong (λ w → cons w (values δ)) qm ∙ cons-values x δ)

```

<!--en-->
The inward reading assumes all three semantic equations: the old slot contains
`graph δ`, the new-value slot contains `fst x`, and the proposed extension
slot contains `graph (x ∷ δ)`. From them it constructs satisfaction of
`consAtL`. This direction lets each quantifier clause use the canonical
environment `envFor (x ∷ δ)` as its certified extension. No untruncated
environment has to be recovered from an existential representation.
<!--zh-->
向内读式假设三条语义等式：旧槽位存放 `graph δ`，新值槽位存放 `fst x`，候选扩张槽位存放 `graph (x ∷ δ)`；由此构造 `consAtL` 的满足关系。这个方向使每个量词子句都能直接把典范环境 `envFor (x ∷ δ)` 用作经过认证的扩张，而无须从存在表示中提取一个未截断的环境。
<!--ja-->
内向きの読みは三つの意味論的な等式を仮定します。古いスロットが`graph δ` を、新しい値のスロットが `fst x` を、拡張スロットの候補が`graph (x ∷ δ)` を収めるという等式です。これらから `consAtL` の充足を構成します。この向きがあるため、各量化子の節は標準環境`envFor (x ∷ δ)` を証明済みの拡張として直接使えます。存在表示から切り詰められていない環境を取り出す必要はありません。
<!--/-->

```agda
  consAtL-in : ∀ {n k} (δ : DB.SM ^ n) (x : DB.SM) (γ : S ^ k) (ei mi di : Fin k)
             → fst (lookup di γ) ≡ graph δ
             → fst (lookup mi γ) ≡ fst x
             → fst (lookup ei γ) ≡ graph (x ∷ δ)
             → ⟨ γ ⊨ consAtL ei mi di ⟩
```

<!--en-->
The inward proof follows the path used by the outward reading in reverse.
Starting from the equation with `graph (x ∷ δ)`, the symmetric
`cons-values` equation and the head equation rewrite its right side as the
graph built from the value at `mi` and the old family. The symmetric adequacy
path then transports this equality back to satisfaction of `consAtL`. Hence
the object-language extension predicate and concrete prefixing of an
assignment are interchangeable once the relevant slots are fixed by
equalities of underlying sets.
<!--zh-->
向内证明把向外读式所用的路径反向连接。从关于 `graph (x ∷ δ)` 的等式出发，`cons-values` 的对称等式与首值等式把右端改写成由 `mi` 处的取值和旧取值族构成的图；随后，充分性路径的对称方向把这条等式运输回 `consAtL` 的满足关系。因此，只要各槽位由底层集合的等式固定，对象语言的扩张谓词与赋值的具体前置操作便可以双向转换。
<!--ja-->
内向きの証明は、外向きの読みに使ったパスを逆にたどります。`graph (x ∷ δ)` についての等式から始め、`cons-values` の逆向きの等式と先頭の値の等式によって、その右辺を `mi` の値と古い値の族から作ったグラフへ書き換えます。続いて妥当性のパスを逆向きに用い、この等式を `consAtL` の充足へ輸送します。したがって、各スロットを基礎集合の等式で固定すれば、対象言語の拡張述語と割当てを具体的に前置拡張する操作との間を双方向に移れます。
<!--/-->

```agda
  consAtL-in δ x γ ei mi di qd qm q =
    subst ⟨_⟩ (sym (consAtL-adequate ei mi di γ (values δ) qd))
      (q ∙ sym (cong env (cong (λ w → cons w (values δ)) qm ∙ cons-values x δ)))
```

<!--en-->
## Induction from recursive values to inner satisfaction
<!--zh-->
## 从递归取值到内层满足的归纳
<!--ja-->
## 再帰の値から内側の充足への帰納法
<!--/-->

<!--en-->
Formula induction is organized by the property `Adequate`{.Agda}. For every
assignment `δ` in the restricted structure, every ambient constructible
element `z`, and every equation identifying its underlying set with
`graph δ`, the property gives a path from membership in the satisfaction set
of the relabelled formula to satisfaction of the original formula under `δ`.
The quantification over `z` makes the statement independent of a chosen
representative of the graph. Its conclusion compares propositions, while
`mapFo intoL φ` on the left records the necessary change from restricted
constants to ambient constructible constants.
<!--zh-->
公式归纳由性质 `Adequate`{.Agda} 组织。对限制结构中的每个赋值 `δ`、每个外围可构造元素 `z`，以及每条把其底层集合认同为 `graph δ` 的等式，该性质都给出一条路径：从属于常元改名后公式的满足关系集合，通向原公式在`δ` 下的满足关系。对所有 `z` 作量化，使陈述不依赖于图的某个特定代表。结论比较的是两个命题，而左端的 `mapFo intoL φ` 则记录了从限制常元到外围可构造常元的必要变换。
<!--ja-->
論理式に関する帰納法は、性質 `Adequate`{.Agda} によって組織されます。制限構造の各割当て `δ`、周囲の各構成可能な要素 `z`、およびその基礎集合を`graph δ` と同一視する各等式に対し、この性質は、定数を改名した論理式の充足関係集合への所属から、元の論理式が `δ` のもとで充足されることへのパスを与えます。すべての `z` を量化するため、主張はグラフの特定の代表に依存しません。結論は二つの命題を比較し、左辺の `mapFo intoL φ` は制限された定数から周囲の構成可能な定数への必要な変更を記録します。
<!--/-->

```agda
  Adequate : ∀ {n} → Formula DB.SM n → Type (ℓ-suc (ℓ-suc ℓ))
  Adequate {n} φ = (δ : DB.SM ^ n) (z : S) → fst z ≡ graph δ
                 → (z ∈ˢ Sat B (mapFo intoL φ)) ≡ (δ ⊨ᴮ φ)

```

<!--en-->
Falsity is the base case and needs no induction hypothesis. After
`Sat-cond`{.Agda} removes the environment-set conjunct, the recursive condition
for `⊥̇` is the false proposition. The inner semantics of `⊥̇` is the same
false proposition, so the remaining comparison is definitional. Both semantics
impose the identical impossible condition.
<!--zh-->
假命题是基例，不需要归纳假设。`Sat-cond`{.Agda} 消去环境集合取项之后，`⊥̇` 的递归条件就是假命题；`⊥̇` 的内层语义也是同一个假命题，所以余下的比较按定义成立。两种语义施加的是完全相同、不可满足的条件。
<!--ja-->
偽は基底の場合であり、帰納仮定を必要としません。`Sat-cond`{.Agda} が環境集合についての論理積の項を取り除くと、`⊥̇` の再帰条件は偽命題になります。`⊥̇` の内側の意味論も同じ偽命題なので、残る比較は定義的に成り立ちます。二つの意味論は、同一の充足不能な条件を課しています。
<!--/-->

```agda

  step⊥ : ∀ {n} → Adequate {n} ⊥̇
  step⊥ δ z q = Sat-cond ⊥̇ δ z q

```

<!--en-->
For a conjunction, `Sat-cond`{.Agda} exposes the conjunction of the two
recursive subconditions. The induction hypotheses give paths from each
subcondition to the corresponding inner satisfaction proposition, at the same
assignment and the same graph representative. Applying congruence for the
truth-value conjunction `_⊓_` to both paths yields the required path for
`a ∧̇ b`. No witness management is involved because the recursive clause and
the inner semantics use the same propositional connective.
<!--zh-->
对合取，`Sat-cond`{.Agda} 展开出两个递归子条件的合取。两条归纳假设在同一个赋值和同一个图代表处，分别给出从子条件到相应内层满足命题的路径。把真值合取 `_⊓_` 的同余同时施于这两条路径，便得到 `a ∧̇ b` 所需的路径。这里不必处理任何见证，因为递归子句与内层语义使用同一个命题联结词。
<!--ja-->
論理積の場合、`Sat-cond`{.Agda} は二つの再帰的な部分条件の論理積を露わにします。二つの帰納仮定は、同じ割当てと同じグラフの代表のもとで、各部分条件から対応する内側の充足命題へのパスを与えます。真理値の論理積`_⊓_` の合同性を二つのパスに施せば、`a ∧̇ b` に必要なパスが得られます。再帰の節と内側の意味論が同じ命題結合子を使うため、証人を扱う必要はありません。
<!--/-->

```agda
  step∧ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ∧̇ b)
  step∧ a b ia ib δ z q = Sat-cond (mapFo intoL (a ∧̇ b)) δ z q
    ∙ cong₂ _⊓_ (ia δ z q) (ib δ z q)

```

<!--en-->
Disjunction has the same structure. Its recursive condition combines the two
subconditions with the truth-value disjunction `_⊔_`, and congruence carries
the two induction paths through that connective. These are operations on
propositions: the proof compares the truth of the two subformulas and the
truth of their disjunction. It does not form a union of the two satisfaction
sets.
<!--zh-->
析取具有相同的结构。其递归条件用真值析取 `_⊔_` 连接两个子条件，同余把两条归纳路径带过这个联结词。这里的运算作用于命题：证明比较两条子公式的真值以及它们析取后的真值，并没有对两个满足关系集合取并。
<!--ja-->
論理和も同じ構造をもちます。その再帰条件は真理値の論理和 `_⊔_` で二つの部分条件を結び、合同性が二つの帰納パスをこの結合子のもとへ運びます。ここでの演算は命題に作用します。証明が比較するのは二つの部分論理式の真理と、その論理和の真理であり、二つの充足関係集合の和集合を作るのではありません。
<!--/-->

```agda
  step∨ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ∨̇ b)
  step∨ a b ia ib δ z q = Sat-cond (mapFo intoL (a ∨̇ b)) δ z q
    ∙ cong₂ _⊔_ (ia δ z q) (ib δ z q)

```

<!--en-->
Implication completes the propositional cases. The recursive clause uses the
truth-value implication `_⇒_`, so congruence applied to the two induction paths
again proves the comparison immediately. Falsity and the three binary
connectives therefore require no special semantic conversion: after the
environment component has been removed, their recursive conditions already
have the same logical form as the inner semantics.
<!--zh-->
蕴涵补全命题情形。递归子句使用真值蕴涵 `_⇒_`，所以把同余施于两条归纳路径，便再次直接得到所需的比较。因此，假命题与三个二元联结词都不需要额外的语义转换：环境分量被消去以后，它们的递归条件已经与内层语义具有相同的逻辑形状。
<!--ja-->
含意で命題の場合がすべてそろいます。再帰の節は真理値の含意 `_⇒_` を使うため、二つの帰納パスに合同性を施すだけで、ここでも比較が得られます。したがって、偽と三つの二項結合子には特別な意味論的変換が要りません。環境の成分を取り除いた後では、それらの再帰条件がすでに内側の意味論と同じ論理的な形をしているからです。
<!--/-->

```agda
  step⇒ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ⇒̇ b)
  step⇒ a b ia ib δ z q = Sat-cond (mapFo intoL (a ⇒̇ b)) δ z q
    ∙ cong₂ _⇒_ (ia δ z q) (ib δ z q)

```

<!--en-->
Atomic formulas require the term-reading lemmas because their recursive
conditions quantify over candidate term values. For membership, the condition
gives, under propositional truncation, values `v` and `w`, proofs that they
represent the evaluations of `t` and `u`, and a membership from `fst v` to
`fst w`. The inner semantics instead states membership directly between the
actual evaluations `T` and `U`. The local names for those evaluations make the
two directions of this logical equivalence explicit.
<!--zh-->
原子公式的递归条件对候选词项值作量化，因此需要前面的词项读引理。对成员关系，条件在命题截断之下给出取值 `v` 与 `w`、它们分别表示 `t` 与 `u`之求值的证明，以及从 `fst v` 到 `fst w` 的成员关系。内层语义则直接陈述实际求值 `T` 与 `U` 之间的成员关系。为这两个求值设置局部名称，可以清楚写出该逻辑等价的两个方向。
<!--ja-->
原子論理式の再帰条件は項の値の候補を量化するため、先ほどの項の読み補題が必要です。所属の場合、その条件は命題的切り詰めのもとで、値 `v` と `w`、それらがそれぞれ `t` と `u` の評価を表すという証明、および `fst v` から`fst w` への所属を与えます。内側の意味論は、実際の評価 `T` と `U` の間の所属を直接述べます。この二つの評価に局所的な名前を付けることで、論理的同値の両方向を明示できます。
<!--/-->

```agda
  step∈ : ∀ {n} (t u : Term DB.SM n) → Adequate (t ∈̇ u)
  step∈ t u δ z q = Sat-cond (mapFo intoL (t ∈̇ u)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    U = ⟦ u ⟧ᴮ δ
```

<!--en-->
In the forward direction, `cond∈-out`{.Agda} exposes the truncated candidates.
The target `fst T ∈ fst U` is a proposition, so `PT.rec` may inspect each
candidate package. At the environment `w ∷ v ∷ z ∷ []`, two applications of
`tmIs-out` identify `v` with `T` and `w` with `U`. The two-variable transport
`subst2` then carries the recorded relation `fst v ∈ fst w` to
`fst T ∈ fst U`, which is exactly the inner interpretation of the atom.
<!--zh-->
在正向中，`cond∈-out`{.Agda} 展开经过截断的候选。目标`fst T ∈ fst U` 是命题，所以 `PT.rec` 可以逐个考察候选包。在环境`w ∷ v ∷ z ∷ []` 上，两次使用 `tmIs-out`，分别把 `v` 与 `T`、`w`与 `U` 认同。二元运输 `subst2` 随后把记录的关系 `fst v ∈ fst w`搬到 `fst T ∈ fst U`，这正是该原子的内层解释。
<!--ja-->
順方向では、`cond∈-out`{.Agda} が切り詰められた候補を展開します。目標 `fst T ∈ fst U` は命題なので、`PT.rec` によって各候補の包みを調べられます。環境 `w ∷ v ∷ z ∷ []` で `tmIs-out` を二度使うと、`v` は `T` と、`w` は `U` とそれぞれ同一視されます。二変数の輸送`subst2` が、記録された関係 `fst v ∈ fst w` を `fst T ∈ fst U` へ運びます。これがこの原子の内側の解釈そのものです。
<!--/-->

```agda
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ∈̇ u)) ⟩ → ⟨ fst T ∈ fst U ⟩
    fwd h = PT.rec (snd (fst T ∈ fst U))
      (λ { (v , (w , (ht , (hu , r)))) → subst2 (λ p s → ⟨ p ∈ s ⟩)
        (tmIs-out t δ (w ∷ v ∷ z ∷ []) (suc zero) (suc (suc zero)) q ht)
        (tmIs-out u δ (w ∷ v ∷ z ∷ []) zero (suc (suc zero)) q hu)
```

<!--en-->
For the reverse implication, the semantic term values themselves provide the
candidates. The map `intoL` packages `T` and `U` as ambient constructible
elements without changing their underlying sets, so `intoL T` and `intoL U`
may be inserted as the two witnesses expected by `cond∈-in`{.Agda}. This is a
direct construction from the given evaluations, not an appeal to a choice
principle or an extraction from propositional truncation.
<!--zh-->
对反向蕴涵，语义词项的取值本身就提供候选。映射 `intoL` 把 `T` 与 `U`包装成外围可构造元素，同时不改变其底层集合，因此可以把 `intoL T` 与`intoL U` 作为 `cond∈-in`{.Agda} 所需的两个见证写入。这是由给定求值直接完成的构造，并没有诉诸选择原理，也没有从命题截断中提取见证。
<!--ja-->
逆向きの含意では、意味論的な項の値そのものが候補になります。写像`intoL` は基礎集合を変えずに `T` と `U` を周囲の構成可能な要素として包むので、`intoL T` と `intoL U` を `cond∈-in`{.Agda} が要求する二つの証人として入れられます。これは与えられた評価からの直接の構成であり、選択原理を使ったり、命題的切り詰めから証人を取り出したりはしません。
<!--/-->

```agda
        r })
      (cond∈-out B (mapTm intoL t) (mapTm intoL u) z h)
    bwd : ⟨ fst T ∈ fst U ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ∈̇ u)) ⟩
    bwd r = cond∈-in B (mapTm intoL t) (mapTm intoL u) z
      ∣ intoL T , (intoL U
```

<!--en-->
With those witnesses fixed, each call to `tmIs-in`{.Agda} receives `refl`
because the underlying set of `intoL T` is definitionally `fst T`, and likewise
for `U`. The assumed membership between the evaluations is therefore already
the relation required between the candidates. Inserting this complete package
into the propositional truncation finishes the reverse implication and hence
the membership atom.
<!--zh-->
确定这两个见证之后，两次调用 `tmIs-in`{.Agda} 都可使用 `refl`：`intoL T` 的底层集合按定义就是 `fst T`，`U` 的情形亦然。因此，假设中的求值成员关系已经是候选之间所需的关系。把这份完整数据写入命题截断，便完成反向蕴涵，也完成了成员原子的充分性证明。
<!--ja-->
この二つの証人を定めると、`tmIs-in`{.Agda} の二つの呼び出しにはどちらも`refl` を渡せます。`intoL T` の基礎集合は定義によって `fst T` であり、`U` についても同様だからです。したがって、仮定された評価間の所属が、候補間に必要な関係になっています。この一式を命題的切り詰めへ入れると、逆向きの含意が閉じ、所属の原子についての妥当性が完成します。
<!--/-->

```agda
      , ( tmIs-in t δ (intoL U ∷ intoL T ∷ z ∷ []) (suc zero) (suc (suc zero)) q refl
        , ( tmIs-in u δ (intoL U ∷ intoL T ∷ z ∷ []) zero (suc (suc zero)) q refl
          , r ))) ∣₁

```

<!--en-->
The equality atom follows the same plan with equality as its candidate
relation. Under propositional truncation, the recursive condition supplies
two proposed term values, their two term readings, and a path between their
underlying sets. The inner semantics asks directly for a path
`fst T ≡ fst U`. As in the membership case, `⇔toPath` reduces adequacy to a
forward transport from candidates to evaluations and a reverse construction
using the evaluations as candidates.
<!--zh-->
相等原子沿用同一方案，只把候选之间的关系换成相等。递归条件在命题截断之下给出两个候选词项值、两份词项读式，以及它们底层集合之间的路径；内层语义则直接要求路径 `fst T ≡ fst U`。与成员原子一样，`⇔toPath` 把充分性化成两个方向：正向把候选运输到实际求值，反向把实际求值用作候选。
<!--ja-->
等号の原子も同じ方針に従い、候補間の関係だけを等号に替えます。再帰条件は命題的切り詰めのもとで、二つの項の値の候補、二つの項の読み、およびそれらの基礎集合の間のパスを与えます。内側の意味論が直接要求するのは`fst T ≡ fst U` というパスです。所属の場合と同じく、`⇔toPath` は妥当性を、候補から評価へ輸送する順方向と、評価を候補として使う逆方向とに分けます。
<!--/-->

```agda
  step≐ : ∀ {n} (t u : Term DB.SM n) → Adequate (t ≐ u)
  step≐ t u δ z q = Sat-cond (mapFo intoL (t ≐ u)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    U = ⟦ u ⟧ᴮ δ
```

<!--en-->
The forward map may eliminate the truncation because equality in the cumulative
hierarchy is a proposition. If the term readings yield paths
`ht : fst v ≡ fst T` and `hu : fst w ≡ fst U`, while the candidate relation is
`r : fst v ≡ fst w`, then the desired path has the precise orientation
`sym ht ∙ r ∙ hu`. Thus the proof first travels from the evaluation of `t`
back to its candidate, crosses the recorded candidate equality, and then
travels forward to the evaluation of `u`.
<!--zh-->
由于累积层级中的相等是命题，正向映射可以消去截断。若两条词项读式给出`ht : fst v ≡ fst T` 与 `hu : fst w ≡ fst U`，而候选关系是`r : fst v ≡ fst w`，那么所需路径的方向恰为 `sym ht ∙ r ∙ hu`。也就是先从 `t` 的实际求值逆行到其候选，经过已记录的候选相等，再正向到达 `u`的实际求值。
<!--ja-->
累積階層の等号は命題なので、順方向の写像は切り詰めを除去できます。項の読みが `ht : fst v ≡ fst T` と `hu : fst w ≡ fst U` を与え、候補間の関係が `r : fst v ≡ fst w` であるとき、求めるパスの向きは正確に`sym ht ∙ r ∙ hu` です。すなわち、まず `t` の実際の評価からその候補へ逆向きに進み、記録された候補間の等号を渡り、最後に `u` の実際の評価へ順向きに進みます。
<!--/-->

```agda
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ≐ u)) ⟩ → fst T ≡ fst U
    fwd h = PT.rec (snd (intoL T ≈ˢ intoL U))
      (λ { (v , (w , (ht , (hu , r)))) →
          sym (tmIs-out t δ (w ∷ v ∷ z ∷ []) (suc zero) (suc (suc zero)) q ht)
        ∙ r
```

<!--en-->
The reverse map again uses `intoL T` and `intoL U` as the ambient witnesses.
They satisfy the two term predicates by the inward term reading, and the
assumed path `fst T ≡ fst U` supplies exactly the candidate equality required
by `cond≐-in`{.Agda}. Membership and equality atoms therefore differ only in
the relation carried between the same two evaluated terms; their treatment of
candidate values and truncation is identical.
<!--zh-->
反向映射仍以 `intoL T` 与 `intoL U` 作为外围见证。向内词项读式证明它们满足两条词项谓词，而假设路径 `fst T ≡ fst U` 恰好提供
`cond≐-in`{.Agda} 所需的候选相等。因此，成员原子与相等原子的区别只在于同一对已求值词项之间携带哪种关系；它们处理候选取值与截断的方式完全相同。
<!--ja-->
逆向きの写像でも、`intoL T` と `intoL U` を周囲の証人として使います。内向きの項の読みによって二つの項述語が充足され、仮定されたパス`fst T ≡ fst U` が `cond≐-in`{.Agda} の要求する候補間の等号をそのまま与えます。したがって、所属の原子と等号の原子との違いは、同じ二つの評価済み項の間にどの関係を運ぶかだけです。候補の値と切り詰めの扱いは一致します。
<!--/-->

```agda
        ∙ tmIs-out u δ (w ∷ v ∷ z ∷ []) zero (suc (suc zero)) q hu })
      (cond≐-out B (mapTm intoL t) (mapTm intoL u) z h)
    bwd : fst T ≡ fst U → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ≐ u)) ⟩
    bwd r = cond≐-in B (mapTm intoL t) (mapTm intoL u) z
      ∣ intoL T , (intoL U
```

<!--en-->
The two value equations passed to `tmIs-in`{.Agda} are again `refl`, since the
witnesses were chosen to be the evaluated terms under `intoL`. The assumed
equality then completes the tuple inserted into the truncated condition.
Both atomic leaves of the formula grammar are now adequate. The remaining
cases are quantifiers, where the essential task is to relate an
object-language extension witness to prefixing an element onto the inner
assignment.
<!--zh-->
传给 `tmIs-in`{.Agda} 的两条取值等式再次都是 `refl`，因为见证就是经`intoL` 包装的词项求值；假设的相等等式随即补全写入截断条件的元组。至此，公式语法的两个原子叶都已具有充分性。余下的是量词情形，其中的核心任务是把对象语言的扩张见证对应到在内层赋值前添入一个元素。
<!--ja-->
`tmIs-in`{.Agda} に渡す二つの値の等式は、ここでも `refl` です。証人として選んだのが、`intoL` で包んだ項の評価そのものだからです。仮定された等号が、切り詰められた条件へ入れる組を完成させます。これで論理式文法の二つの原子の葉について妥当性が得られました。残るのは量化子の場合であり、そこでの中心的な課題は、対象言語の拡張の証人を、内側の割当ての先頭に一つの要素を加える操作と対応させることです。
<!--/-->

```agda
      , ( tmIs-in t δ (intoL U ∷ intoL T ∷ z ∷ []) (suc zero) (suc (suc zero)) q refl
        , ( tmIs-in u δ (intoL U ∷ intoL T ∷ z ∷ []) zero (suc (suc zero)) q refl
          , r ))) ∣₁
```

<!--en-->
For the unbounded existential, the object-language condition contains a
propositionally truncated package: an ambient element `x` together with a
proof that its underlying set belongs to `B`, an element `e` proposed as the
extended environment, satisfaction of the extension predicate, and membership
of `e` in the subformula's satisfaction set. The inner existential ranges over
`DB.SM`, whose elements already pair a set with its membership in `B`, and is
itself propositionally truncated. The forward direction can therefore map the
outer package to an inner existential witness without retaining a chosen
representative.
<!--zh-->
对无界存在量词，对象语言条件包含一份经过命题截断的数据：外围元素 `x`及其底层集合属于 `B` 的证明、作为扩张环境候选的元素 `e`、扩张谓词的满足关系，以及 `e` 属于子公式满足关系集合的证明。内层存在量词遍历`DB.SM`，而它的元素已经把一个集合及其属于 `B` 的证明配在一起；这个存在量词本身也经过命题截断。因此，正向可以把外围数据映成内层存在见证，而无须保留某个选定的代表。
<!--ja-->
非有界の存在量化子について、対象言語の条件は命題的に切り詰められた一式のデータを含みます。周囲の要素 `x` と、その基礎集合が `B` に属すという証明、拡張環境の候補 `e`、拡張述語の充足、および `e` の部分論理式の充足関係集合への所属です。内側の存在量化子は `DB.SM` 上を動き、その要素は集合とその`B` への所属証明をすでに組にしています。この存在量化子自身も命題的に切り詰められています。したがって順方向では、特定の代表を保持せずに、外側の一式を内側の存在証人へ写せます。
<!--/-->

```agda
  step∃ : ∀ {n} (a : Formula DB.SM (suc n)) → Adequate a → Adequate (∃̇ a)
  step∃ a ia δ z q = Sat-cond (mapFo intoL (∃̇ a)) δ z q ∙ ⇔toPath fwd bwd
    where
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇ a)) ⟩ → ⟨ δ ⊨ᴮ (∃̇ a) ⟩
    fwd h = PT.rec squash₁
```

<!--en-->
Inside the truncation, the ambient witness and its proof `x∈B` form the
restricted-carrier element `(fst x , x∈B)`. This is the sole domain
restriction on an unbounded quantified variable; the additional membership in
a bounding term appears only for bounded quantifiers. `consAtL-out`{.Agda}
then identifies `e` with the graph of the concretely extended assignment
`(fst x , x∈B) ∷ δ`. The induction hypothesis transports the recorded
subformula membership to inner satisfaction at that assignment, and the value
together with this proof is inserted into the inner existential truncation.
<!--zh-->
在截断之内，外围见证及其证明 `x∈B` 组成限制载体元素`(fst x , x∈B)`。这是无界量化变元唯一的论域限制；属于界项取值的附加成员条件只在有界量词中出现。随后，`consAtL-out`{.Agda} 把 `e` 认同为具体扩张赋值 `(fst x , x∈B) ∷ δ` 的图。归纳假设把已记录的子公式成员关系运输为该赋值下的内层满足关系，最后把这个取值连同证明写入内层存在的命题截断。
<!--ja-->
切り詰めの内側で、周囲の証人とその証明 `x∈B` を組にすると、制限された台の要素 `(fst x , x∈B)` が得られます。非有界の量化変数に課される論域の制限はこれだけであり、限界項の値への所属という追加条件は有界量化子で初めて現れます。続いて `consAtL-out`{.Agda} は `e` を、具体的に拡張した割当て `(fst x , x∈B) ∷ δ` のグラフと同一視します。帰納仮定が、記録された部分論理式の所属をこの割当てでの内側の充足へ輸送し、その値と証明の組が内側の存在量化の命題的切り詰めへ入れられます。
<!--/-->

```agda
      (λ { (x , (x∈B , (e , (hc , he)))) → ∣ (fst x , x∈B)
         , subst ⟨_⟩ (ia ((fst x , x∈B) ∷ δ) e
             (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ z ∷ [])
               zero (suc zero) (suc (suc zero)) q refl hc)) he ∣₁ })
      (cond∃-out B (mapFo intoL a) z h)
```

<!--en-->
For the reverse implication of the existential case, the semantic witness is
available only inside `∃[]`. We therefore map the construction over that
propositional truncation. A witness `x` is already an element of the restricted
carrier, so its first component gives the ambient set and its second component
proves membership in `B`. The condition is witnessed by `intoL x` together with
the canonical environment `envFor (x ∷ δ)` for the extended assignment.
<!--zh-->
在存在情形的反向蕴涵中，语义见证只在 `∃[]` 内给出，因此证明在这层命题截断上作映射。见证 `x` 已经是限制载体的元素，其第一分量给出外围集合，第二分量证明它属于 `B`。条件一侧以 `intoL x` 为新值，并以扩张赋值 `x ∷ δ` 的典范环境 `envFor (x ∷ δ)` 为环境见证。
<!--ja-->
存在量化の場合の逆向きの含意では、意味論的な証人は `∃[]` の内部でのみ与えられます。そこで、この命題的切り詰めの上で構成を写します。証人 `x` はすでに制限された台の要素なので、第一成分が周囲の集合を与え、第二成分が `B` への所属を証明します。条件の側では `intoL x` を新しい値とし、拡張された割当て `x ∷ δ` の正準な環境 `envFor (x ∷ δ)` を環境の証人とします。
<!--/-->

```agda
    bwd : ⟨ δ ⊨ᴮ (∃̇ a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇ a)) ⟩
    bwd h = cond∃-in B (mapFo intoL a) z (PT.map
      (λ { (x , ha) → intoL x , (snd x , (envFor (x ∷ δ)
         , ( consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ z ∷ [])
               zero (suc zero) (suc (suc zero)) q refl (envFor-graph (x ∷ δ))
```

<!--en-->
The inward reading of `consAtL` certifies this environment extension from three
equalities: the old environment has graph `δ`, `intoL x` has the underlying
value of `x`, and the canonical new environment has graph `x ∷ δ`. The
induction hypothesis is then read backwards, changing semantic satisfaction of
the subformula at `x ∷ δ` into membership of the canonical environment in the
recursive subvalue. All witness construction remains under `∃[]`; no choice of
a semantic witness escapes the truncation.
<!--zh-->
`consAtL` 的向内读式用三条等式认证这次环境扩张：旧环境的图是 `δ` 的图，`intoL x` 的底层值就是 `x` 的底层值，而新的典范环境的图是 `x ∷ δ` 的图。随后反向读取归纳假设，把子公式在 `x ∷ δ` 处的语义满足变成该典范环境属于递归子取值。见证的全部构造始终留在 `∃[]` 内，没有从命题截断中取出可供选择的语义见证。
<!--ja-->
`consAtL` の内向きの読みは、三つの等式からこの環境の拡張を証明します。古い環境は `δ` のグラフをもち、`intoL x` の基礎の値は `x` の基礎の値であり、新しい正準な環境は `x ∷ δ` のグラフをもちます。続いて帰納法の仮定を逆向きに読み、`x ∷ δ` での部分論理式の意味論的充足を、正準な環境が再帰的な部分の値に属することへ移します。証人の構成はすべて `∃[]` の内部にとどまり、意味論的な証人を命題的切り詰めの外へ選び出すことはありません。
<!--/-->

```agda
           , subst ⟨_⟩ (sym (ia (x ∷ δ) (envFor (x ∷ δ))
               (envFor-graph (x ∷ δ)))) ha ))) })
      h)

```

<!--en-->
The universal case has a different proof shape. Inner `∀[]` is a function
which, for every `x` in the restricted carrier, proves the subformula at
`x ∷ δ`; it contains no propositional truncation. After `Sat-cond` exposes the
recursive condition, the forward implication therefore takes an arbitrary
`x` and constructs the required answer directly.
<!--zh-->
全称情形具有不同的证明形状。内层 `∀[]` 是一个函数：它对限制载体中的每个 `x`，证明子公式在 `x ∷ δ` 处成立，其中没有命题截断。`Sat-cond` 展开递归条件后，正向蕴涵便取任意 `x`，直接构造所需的证明。
<!--ja-->
全称量化の場合は証明の形が異なります。内側の `∀[]` は、制限された台の任意の `x` に対して、部分論理式が `x ∷ δ` で成り立つことを示す関数であり、命題的切り詰めを含みません。`Sat-cond` が再帰的な条件を展開した後、正向きの含意は任意の `x` を取り、必要な証明を直接構成します。
<!--/-->

```agda
  step∀ : ∀ {n} (a : Formula DB.SM (suc n)) → Adequate a → Adequate (∀̇ a)
  step∀ a ia δ z q = Sat-cond (mapFo intoL (∀̇ a)) δ z q ∙ ⇔toPath fwd bwd
    where
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇ a)) ⟩ → ⟨ δ ⊨ᴮ (∀̇ a) ⟩
    fwd h x = subst ⟨_⟩ (ia (x ∷ δ) (envFor (x ∷ δ)) (envFor-graph (x ∷ δ)))
```

<!--en-->
To query the condition's universal clause, the proof supplies the ambient
representative `intoL x`, the carrier proof `snd x`, and the canonical extended
environment. The inward `consAtL` reading verifies that this environment really
extends the old graph by the value of `x`. The clause then yields membership in
the recursive subvalue, and the induction hypothesis carries it to inner
satisfaction. The only restriction on this unbounded variable is membership in
`B`, already stored in the package `x : DB.SM`.
<!--zh-->
为了调用条件的全称子句，证明给出外围代表 `intoL x`、载体成员证明 `snd x`，以及典范扩张环境。`consAtL` 的向内读式验证该环境确由 `x` 的取值扩张旧图。子句随即给出对递归子取值的隶属，归纳假设再把它送到内层满足。这个无界变元唯一的限制是属于 `B`，而该证明已经存放在 `x : DB.SM` 的包装中。
<!--ja-->
条件の全称の節を使うために、周囲での表示 `intoL x`、台への所属証明 `snd x`、そして正準な拡張環境を与えます。`consAtL` の内向きの読みは、この環境が実際に `x` の値を古いグラフの先頭に加えたものであることを示します。すると節から再帰的な部分の値への所属が得られ、帰納法の仮定がそれを内側の充足へ運びます。この非有界変数に課される唯一の制限は `B` への所属であり、その証明はすでに `x : DB.SM` の組に含まれています。
<!--/-->

```agda
      (cond∀-out B (mapFo intoL a) z h (intoL x) (envFor (x ∷ δ)) (snd x)
        (consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ z ∷ [])
          zero (suc zero) (suc (suc zero)) q refl (envFor-graph (x ∷ δ))))
    bwd : ⟨ δ ⊨ᴮ (∀̇ a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇ a)) ⟩
    bwd k = cond∀-in B (mapFo intoL a) z
```

<!--en-->
Conversely, the condition asks for a subvalue proof for every ambient `x`
known to lie in `B` and every environment certified as its extension of `z`.
The proof packages `(fst x , x∈B)` as an element of the restricted carrier and
applies the given inner universal function. The outward `consAtL` reading
identifies the certified environment with the graph of the extended assignment;
the induction hypothesis, read backwards along that equation, then produces
the required subvalue membership. This direction is pointwise throughout and
uses no truncation.
<!--zh-->
反过来，条件要求：对每个已知属于 `B` 的外围元素 `x`，以及每个经认证为 `z` 之扩张的环境，都给出对子取值的隶属。证明把 `(fst x , x∈B)` 包装成限制载体的元素，再调用已给定的内层全称函数。`consAtL` 的向外读式把经认证的环境认同为扩张赋值的图，随后沿这条等式反向读取归纳假设，得到所需的子取值隶属。整个方向都是逐点的，不使用命题截断。
<!--ja-->
逆に条件が要求するのは、`B` に属すると分かっている周囲の任意の `x` と、`z` の拡張であると証明された任意の環境に対する、部分の値への所属です。証明は `(fst x , x∈B)` を制限された台の要素として組にし、与えられた内側の全称関数を適用します。`consAtL` の外向きの読みは、証明された環境を拡張された割当てのグラフと同定します。その等式に沿って帰納法の仮定を逆向きに読めば、必要な部分の値への所属が得られます。この向きは終始点ごとの議論であり、命題的切り詰めを使いません。
<!--/-->

```agda
      (λ x e x∈B hc → subst ⟨_⟩
        (sym (ia ((fst x , x∈B) ∷ δ) e
          (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ z ∷ [])
            zero (suc zero) (suc (suc zero)) q refl hc)))
        (k (fst x , x∈B)))
```

<!--en-->
A bounded existential adds the evaluated bounding term to the unbounded
argument. Let `T = ⟦ t ⟧ᴮ δ` be its genuine value in the restricted structure.
The inner semantics now seeks, under `∃[]`, an `x : DB.SM` together with both
membership of the underlying set of `x` in the underlying set of `T` and
satisfaction of the subformula at `x ∷ δ`. Thus carrier membership and bound
membership remain distinct pieces of evidence.
<!--zh-->
有界存在在无界论证上增加了界项的求值。令 `T = ⟦ t ⟧ᴮ δ` 为该词项在限制结构中的真正取值。内层语义现在于 `∃[]` 下寻找 `x : DB.SM`，并同时要求 `x` 的底层集合属于 `T` 的底层集合，以及子公式在 `x ∷ δ` 处得到满足。因此，载体成员资格与界项成员资格始终是两份不同的证据。
<!--ja-->
有界存在量化では、非有界の場合の議論に限界項の評価が加わります。`T = ⟦ t ⟧ᴮ δ` を、制限された構造におけるその項の真の値とします。内側の意味論は `∃[]` の下で `x : DB.SM` を探し、`x` の基礎集合が `T` の基礎集合に属することと、部分論理式が `x ∷ δ` で充足されることを同時に要求します。したがって、台への所属と限界への所属は別々の証拠として保たれます。
<!--/-->

```agda
  step∃∈ : ∀ {n} (t : Term DB.SM n) (a : Formula DB.SM (suc n))
         → Adequate a → Adequate (∃̇∈ t a)
  step∃∈ t a ia δ z q = Sat-cond (mapFo intoL (∃̇∈ t a)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
```

<!--en-->
In the forward implication, the bounded condition first supplies, under an
outer truncation, a candidate `w` satisfying the term-value predicate. Its
second truncated package supplies an ambient `x`, proofs that `x` lies in `B`
and in `w`, an extended environment `e`, and the subcondition at `e`. The outer
truncation is eliminated into the propositional semantic goal, while the inner
one is mapped to the semantic existential witness `(fst x , x∈B)`.
<!--zh-->
在正向蕴涵中，有界条件先在外层截断下给出满足词项取值谓词的候选 `w`。第二个截断包裹再给出外围元素 `x`、`x` 属于 `B` 与 `w` 的证明、扩张环境 `e`，以及 `e` 处的子条件。外层截断被消去到命题值的语义目标中，内层截断则映射到语义存在见证 `(fst x , x∈B)`。
<!--ja-->
正向きの含意では、有界な条件はまず外側の切り詰めの下で、項の値を表す述語を満たす候補 `w` を与えます。第二の切り詰められた組は、周囲の要素 `x`、`x` が `B` と `w` に属する証明、拡張環境 `e`、そして `e` での部分条件を与えます。外側の切り詰めは命題値である意味論的な目標へ除去し、内側の切り詰めは意味論的な存在証人 `(fst x , x∈B)` へ写します。
<!--/-->

```agda
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇∈ t a)) ⟩ → ⟨ δ ⊨ᴮ (∃̇∈ t a) ⟩
    fwd h = PT.rec squash₁
      (λ { (w , (hw , hb)) → PT.map
        (λ { (x , ((x∈B , x∈w) , (e , (hc , he)))) → (fst x , x∈B)
           , ( subst (λ s → ⟨ fst x ∈ s ⟩)
```

<!--en-->
The term reading `tmIs-out` identifies the underlying candidate `w` with the
underlying semantic value `T`. Transport along that path changes `x∈w` into
the bound required by the inner semantics, namely `fst x ∈ fst T`. Independently,
`consAtL-out` identifies `e` with the graph of `(fst x , x∈B) ∷ δ`, so the
induction hypothesis converts the subcondition at `e` into satisfaction at the
extended assignment. These two results form the payload of the inner `∃[]`.
<!--zh-->
词项读式 `tmIs-out` 把候选 `w` 的底层集合与语义取值 `T` 的底层集合认同起来。沿这条路径运输，`x∈w` 便成为内层语义要求的界项成员证明，即 `fst x ∈ fst T`。另一方面，`consAtL-out` 把 `e` 认同为 `(fst x , x∈B) ∷ δ` 的图，因此归纳假设可把 `e` 处的子条件转成扩张赋值处的满足。这两项结果共同构成内层 `∃[]` 的载荷。
<!--ja-->
項の読み `tmIs-out` は、候補 `w` の基礎集合を意味論的な値 `T` の基礎集合と同定します。そのパスに沿って輸送すると、`x∈w` は内側の意味論が要求する限界への所属、すなわち `fst x ∈ fst T` になります。一方、`consAtL-out` は `e` を `(fst x , x∈B) ∷ δ` のグラフと同定するので、帰納法の仮定によって `e` での部分条件を拡張された割当てでの充足へ移せます。この二つの結果が内側の `∃[]` の中身になります。
<!--/-->

```agda
                 (tmIs-out t δ (w ∷ z ∷ []) zero (suc zero) q hw) x∈w
             , subst ⟨_⟩ (ia ((fst x , x∈B) ∷ δ) e
                 (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ w ∷ z ∷ [])
                   zero (suc zero) (suc (suc (suc zero))) q refl hc)) he ) })
        hb })
```

<!--en-->
For the reverse implication, use the genuine value `T` itself as the
condition's candidate for the bound. Its term-value predicate follows from
`tmIs-in` with the reflexive value equation. Mapping over the semantic `∃[]`
then reduces the remaining task to repackaging each semantic witness `x`; the
condition's inner existential remains propositionally truncated.
<!--zh-->
在反向蕴涵中，直接以真正取值 `T` 作为条件一侧的界候选。以自反的取值等式调用 `tmIs-in`，即可得到它满足词项取值谓词的证明。随后在语义 `∃[]` 上作映射，余下任务便是逐一重新包装每个语义见证 `x`；条件的内层存在仍保持命题截断。
<!--ja-->
逆向きの含意では、真の値 `T` そのものを条件側の限界の候補として用います。反射的な値の等式とともに `tmIs-in` を使えば、その項の値を表す述語が得られます。次に意味論的な `∃[]` の上で写すと、残る仕事は各意味論的証人 `x` を組み直すことだけになります。条件の内側の存在は命題的に切り詰められたままです。
<!--/-->

```agda
      (cond∃∈-out B (mapTm intoL t) (mapFo intoL a) z h)
    bwd : ⟨ δ ⊨ᴮ (∃̇∈ t a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇∈ t a)) ⟩
    bwd h = cond∃∈-in B (mapTm intoL t) (mapFo intoL a) z (PT.map
      (λ { (x , (hx , ha)) → intoL T
         , ( tmIs-in t δ (intoL T ∷ z ∷ []) zero (suc zero) q refl
```

<!--en-->
The semantic witness `x : DB.SM` supplies the two restrictions separately:
`snd x` proves membership in the carrier, while `hx` proves membership in the
bound `T`. The proof keeps `hx` unchanged because the chosen candidate really
is `intoL T`. It chooses `envFor (x ∷ δ)` for the extension, certifies it with
`consAtL-in`, and reads the induction hypothesis backwards to obtain membership
in the recursive subvalue.
<!--zh-->
语义见证 `x : DB.SM` 分别提供两道限制：`snd x` 证明它属于载体，`hx` 证明它属于界 `T`。由于选取的候选正是 `intoL T`，证明可原样保留 `hx`。扩张环境取为 `envFor (x ∷ δ)`，由 `consAtL-in` 加以认证，再反向读取归纳假设，得到对递归子取值的隶属。
<!--ja-->
意味論的証人 `x : DB.SM` は二つの制限を別々に与えます。`snd x` は台への所属を証明し、`hx` は限界 `T` への所属を証明します。選んだ候補は実際に `intoL T` なので、`hx` はそのまま使えます。拡張環境として `envFor (x ∷ δ)` を選び、`consAtL-in` でそれを証明し、帰納法の仮定を逆向きに読んで再帰的な部分の値への所属を得ます。
<!--/-->

```agda
           , ∣ intoL x , ((snd x , hx) , (envFor (x ∷ δ)
             , ( consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ intoL T ∷ z ∷ [])
                   zero (suc zero) (suc (suc (suc zero))) q refl
                   (envFor-graph (x ∷ δ))
               , subst ⟨_⟩ (sym (ia (x ∷ δ) (envFor (x ∷ δ))
```

<!--en-->
This completes both directions for bounded existence. Relative to unbounded
existence, the only new mathematical work is to name the value of the bounding
term and transport one membership proof between its coded candidate and its
semantic value. Both existential packages stay under propositional truncation,
so the proof introduces no choice principle. The excluded-middle parameter is
already present in the construction of `Sat`; this adequacy step adds no new
classical assumption.
<!--zh-->
至此，有界存在的两个方向都已完成。与无界存在相比，新增的数学工作只有两项：命名界项的取值，以及在编码候选与语义取值之间运输一条成员证明。两个存在包裹都留在命题截断之下，因此证明没有引入选择原理。排中律参数已经用于构造 `Sat`，这一步充分性证明没有增加新的经典假设。
<!--ja-->
これで有界存在量化の両方向が完成します。非有界存在量化に加わった数学的な仕事は、限界項の値を名づけることと、符号化された候補と意味論的な値の間で一つの所属証明を輸送することだけです。二つの存在の組はどちらも命題的切り詰めの下にとどまるため、選択原理は導入されません。排中律のパラメータはすでに `Sat` の構成に現れており、この妥当性の段階で新たな古典的仮定は加わりません。
<!--/-->

```agda
                   (envFor-graph (x ∷ δ)))) ha ))) ∣₁ ) })
      h)

```

<!--en-->
The bounded universal is the last constructor case. With
`T = ⟦ t ⟧ᴮ δ`, its inner meaning is a function which takes every
`x : DB.SM`, then a proof `fst x ∈ fst T`, and returns satisfaction of the
subformula at `x ∷ δ`. As in the unbounded universal case, neither direction
contains an existential package, so both implications are constructed
pointwise without truncation.
<!--zh-->
有界全称是最后一个构造子情形。令 `T = ⟦ t ⟧ᴮ δ`，其内层意义是一个函数：它先取任意 `x : DB.SM`，再取证明 `fst x ∈ fst T`，返回子公式在 `x ∷ δ` 处的满足。与无界全称情形相同，两个方向都不含存在包裹，因此两条蕴涵均逐点构造，不涉及命题截断。
<!--ja-->
有界全称量化は最後の構成子の場合です。`T = ⟦ t ⟧ᴮ δ` とすると、その内側の意味は、任意の `x : DB.SM` と証明 `fst x ∈ fst T` を受け取り、部分論理式が `x ∷ δ` で充足されることを返す関数です。非有界全称量化の場合と同じく、どちらの向きにも存在の組はないため、二つの含意は命題的切り詰めを使わず点ごとに構成されます。
<!--/-->

```agda
  step∀∈ : ∀ {n} (t : Term DB.SM n) (a : Formula DB.SM (suc n))
         → Adequate a → Adequate (∀̇∈ t a)
  step∀∈ t a ia δ z q = Sat-cond (mapFo intoL (∀̇∈ t a)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
```

<!--en-->
For the forward function, take `x` and its semantic bound proof `hx`. The
condition's universal clause is instantiated with the genuine bound value
`intoL T`, whose term reading follows from `tmIs-in`, and with the ambient
representative `intoL x`. The two guards are supplied from different sources:
`snd x` records `x ∈ B`, while `hx` records `fst x ∈ fst T`. The canonical
extension is certified by `consAtL-in`, and the induction hypothesis turns the
resulting subvalue membership into inner satisfaction.
<!--zh-->
构造正向函数时，取 `x` 及其语义界项成员证明 `hx`。条件的全称子句以真正的界值 `intoL T` 实例化，其词项读式由 `tmIs-in` 给出；变元则以外围代表 `intoL x` 实例化。两道限制来自不同来源：`snd x` 记录 `x ∈ B`，`hx` 记录 `fst x ∈ fst T`。`consAtL-in` 认证典范扩张，归纳假设再把所得的子取值隶属转成内层满足。
<!--ja-->
正向きの関数を作るには、`x` とその意味論的な限界への所属証明 `hx` を取ります。条件の全称の節では、真の限界値 `intoL T` を使い、その項の読みを `tmIs-in` から得ます。変数には周囲での表示 `intoL x` を使います。二つの制限は異なる所から来ます。`snd x` が `x ∈ B` を記録し、`hx` が `fst x ∈ fst T` を記録します。`consAtL-in` が正準な拡張を証明し、帰納法の仮定が得られた部分の値への所属を内側の充足へ移します。
<!--/-->

```agda
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇∈ t a)) ⟩ → ⟨ δ ⊨ᴮ (∀̇∈ t a) ⟩
    fwd h x hx = subst ⟨_⟩ (ia (x ∷ δ) (envFor (x ∷ δ)) (envFor-graph (x ∷ δ)))
      (cond∀∈-out B (mapTm intoL t) (mapFo intoL a) z h (intoL T)
        (tmIs-in t δ (intoL T ∷ z ∷ []) zero (suc zero) q refl)
        (intoL x) (envFor (x ∷ δ)) (snd x) hx
```

<!--en-->
For the reverse function, the condition quantifies over an arbitrary candidate
bound `w`, a proof `hw` that it reads as the term value, an ambient member `x`
with proofs `x∈B` and `x∈w`, and a certified extension `e`. The outward term
reading identifies the underlying set of `w` with `fst T`; transporting `x∈w`
along this path gives exactly the bound proof needed to apply the inner
universal function to `(fst x , x∈B)`.
<!--zh-->
构造反向函数时，条件对以下数据作全称量化：任意候选界值 `w`、证明它读作词项取值的 `hw`、带有 `x∈B` 与 `x∈w` 的外围成员 `x`，以及经认证的扩张 `e`。词项的向外读式把 `w` 的底层集合与 `fst T` 认同起来；沿这条路径运输 `x∈w`，便得到把内层全称函数用于 `(fst x , x∈B)` 所需的界项成员证明。
<!--ja-->
逆向きの関数では、条件は任意の限界候補 `w`、それが項の値として読めることを示す `hw`、`x∈B` と `x∈w` を伴う周囲の要素 `x`、そして証明された拡張 `e` のすべてについて量化します。項の外向きの読みは `w` の基礎集合を `fst T` と同定します。このパスに沿って `x∈w` を輸送すれば、内側の全称関数を `(fst x , x∈B)` に適用するための限界への所属証明がちょうど得られます。
<!--/-->

```agda
        (consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ intoL T ∷ z ∷ [])
          zero (suc zero) (suc (suc (suc zero))) q refl (envFor-graph (x ∷ δ))))
    bwd : ⟨ δ ⊨ᴮ (∀̇∈ t a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇∈ t a)) ⟩
    bwd k = cond∀∈-in B (mapTm intoL t) (mapFo intoL a) z
      (λ w hw x e x∈B x∈w hc → subst ⟨_⟩
```

<!--en-->
Applying the inner universal function gives satisfaction of the subformula at
`(fst x , x∈B) ∷ δ`. The outward `consAtL` reading identifies the certified
environment `e` with the graph of precisely that assignment. Reading the
induction path backwards therefore changes semantic satisfaction into the
subvalue membership required by the condition. This closes the bounded
universal case and completes the four quantifier arguments while preserving
the separate carrier and bound restrictions.
<!--zh-->
应用内层全称函数后，得到子公式在 `(fst x , x∈B) ∷ δ` 处的满足。`consAtL` 的向外读式把经认证的环境 `e` 认同为这个赋值的图。因此，反向读取归纳路径，便把语义满足变成条件所需的子取值隶属。至此有界全称情形闭合，四个量词论证全部完成，并且载体限制与界项限制始终彼此分明。
<!--ja-->
内側の全称関数を適用すると、部分論理式が `(fst x , x∈B) ∷ δ` で充足されることが得られます。`consAtL` の外向きの読みは、証明された環境 `e` をまさにこの割当てのグラフと同定します。したがって帰納法のパスを逆向きに読めば、意味論的充足を条件が要求する部分の値への所属へ移せます。これで有界全称量化の場合が閉じ、台への制限と限界への制限を区別したまま、四つの量化子の議論がすべて完成します。
<!--/-->

```agda
        (sym (ia ((fst x , x∈B) ∷ δ) e
          (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ w ∷ z ∷ [])
            zero (suc zero) (suc (suc (suc zero))) q refl hc)))
        (k (fst x , x∈B) (subst (λ s → ⟨ fst x ∈ s ⟩)
          (tmIs-out t δ (w ∷ z ∷ []) zero (suc zero) q hw) x∈w)))
```

<!--en-->
The individual cases now assemble into `Sat-spec` by structural recursion on
the formula. Its invariant is exact: for every assignment `δ`, every ambient
element `z`, and every path from `fst z` to `graph δ`, membership of `z` in
`Sat B (mapFo intoL φ)` is the same proposition as inner satisfaction
`δ ⊨ᴮ φ`. The first four clauses select the two atomic proofs and recursively
combine the induction paths for conjunction and disjunction.
<!--zh-->
各个情形现在沿公式作结构递归，汇合为 `Sat-spec`。它的归纳不变量十分精确：对每个赋值 `δ`、每个外围元素 `z`，以及每条从 `fst z` 到 `graph δ` 的路径，`z` 属于 `Sat B (mapFo intoL φ)` 与内层满足 `δ ⊨ᴮ φ` 是同一个命题。前四条子句选择两个原子证明，并为合取与析取递归组合归纳路径。
<!--ja-->
個々の場合を論理式の構造に沿って再帰させ、`Sat-spec` にまとめます。その帰納的不変条件は正確です。任意の割当て `δ`、任意の周囲の要素 `z`、そして `fst z` から `graph δ` への任意のパスについて、`z` が `Sat B (mapFo intoL φ)` に属することと、内側で `δ ⊨ᴮ φ` が成り立つことは同じ命題です。最初の四つの節は二つの原子の場合を選び、連言と選言について帰納的に得たパスを組み合わせます。
<!--/-->

```agda
  Sat-spec : ∀ {n} (φ : Formula DB.SM n) → Adequate φ
  Sat-spec (t ∈̇ u)  = step∈ t u
  Sat-spec (t ≐ u)  = step≐ t u
  Sat-spec (a ∧̇ b)  = step∧ a b (Sat-spec a) (Sat-spec b)
  Sat-spec (a ∨̇ b)  = step∨ a b (Sat-spec a) (Sat-spec b)
```

<!--en-->
The recursion continues with implication and falsity, then the two unbounded
quantifiers and bounded universal quantification. A compound constructor
receives precisely the adequacy proofs of its immediate subformulas; falsity
needs none. Thus every use of the induction hypothesis is local to the
syntactic branch whose recursive condition and inner semantics are being
compared.
<!--zh-->
递归接着处理蕴涵与假，再处理两个无界量词和有界全称。复合构造子恰好接收其直接子公式的充分性证明，假则不需要归纳假设。因此，每次使用归纳假设都局限于当前语法分支，用来比较该分支的递归条件与内层语义。
<!--ja-->
再帰は含意と偽へ進み、続いて二つの非有界量化子と有界全称量化を扱います。複合した構成子が受け取るのは、直接の部分論理式に対する妥当性の証明だけであり、偽の場合には帰納法の仮定は要りません。したがって帰納法の仮定は毎回、その構文の枝における再帰的な条件と内側の意味論を比較するためだけに使われます。
<!--/-->

```agda
  Sat-spec (a ⇒̇ b)  = step⇒ a b (Sat-spec a) (Sat-spec b)
  Sat-spec ⊥̇        = step⊥
  Sat-spec (∃̇ a)    = step∃ a (Sat-spec a)
  Sat-spec (∀̇ a)    = step∀ a (Sat-spec a)
  Sat-spec (∀̇∈ t a) = step∀∈ t a (Sat-spec a)
```

<!--en-->
The bounded existential clause closes the ten-case recursion. Consequently
`Sat-spec` proves adequacy for every formula whose constants lie in the
restricted carrier, after `mapFo intoL` places those constants in the ambient
language. This theorem gives each externally constructed value `Sat B φ` its
semantic reading. It neither constructs a uniform satisfaction table nor
proves a candidate table unique. `SatisfactionGraph` formulates the candidate
graph relation, `PinnedRecursion` proves the required keywise uniqueness, and
`UniformSatisfaction` combines existence with that uniqueness to construct a
uniform table before using `Sat-spec` to interpret its values.
<!--zh-->
有界存在子句闭合这场十种情形的递归。因此，`Sat-spec` 对每条常元取自限制载体的公式证明充分性，其中 `mapFo intoL` 把这些常元置入外围语言。该定理为每个在外部构造的取值 `Sat B φ` 给出语义读法，但既不构造统一满足关系表，也不证明候选表唯一。`SatisfactionGraph` 写出候选图关系，`PinnedRecursion` 证明所需的逐键唯一性，`UniformSatisfaction` 再把存在性与这项唯一性结合起来构造统一表，随后用 `Sat-spec` 解释其取值。
<!--ja-->
有界存在量化の節によって十の場合の再帰が閉じます。したがって `Sat-spec` は、定数が制限された台に属する任意の論理式について妥当性を証明します。ここで `mapFo intoL` はそれらの定数を周囲の言語へ移します。この定理は、外側で構成された各値 `Sat B φ` に意味論的な読みを与えますが、一様な充足関係表を構成することも、候補の表の一意性を証明することもありません。`SatisfactionGraph` が候補となるグラフ関係を記述し、`PinnedRecursion` が必要なキーごとの一意性を証明します。`UniformSatisfaction` は存在とこの一意性を組み合わせて一様な表を構成し、その後で `Sat-spec` を使って各値を解釈します。
<!--/-->

```agda
  Sat-spec (∃̇∈ t a) = step∃∈ t a (Sat-spec a)
```

<!--en-->
## Recovering an assignment from an environment
<!--zh-->
## 从环境恢复赋值
<!--ja-->
## 環境から割当てを復元する
<!--/-->

<!--en-->
The main theorem starts from a chosen assignment. To read an arbitrary member
of an environment set, we first convert the small indices used by its coding
into elements of the restricted carrier. For `m : ⟪ fst B ⟫`, the presentation
map gives the underlying set `⟪ fst B ⟫↪ m`; the two readings of presentation
membership show that this set lies in `fst B`. Pairing the set with that proof
defines `inB m : DB.SM`.
<!--zh-->
主定理从一项已选定的赋值出发。若要读取环境集的任意成员，首先须把其编码所用的小索引转换成限制载体的元素。对 `m : ⟪ fst B ⟫`，表现映射给出底层集合 `⟪ fst B ⟫↪ m`；表现隶属的两种读式证明该集合属于 `fst B`。把集合与这条证明配对，便得到 `inB m : DB.SM`。
<!--ja-->
主定理は、あらかじめ選ばれた割当てから出発します。環境集合の任意の要素を読むには、まずその符号化に使われる小さな添字を、制限された台の要素へ変換します。`m : ⟪ fst B ⟫` に対して、表示写像は基礎集合 `⟪ fst B ⟫↪ m` を与えます。表示における所属の二つの読みから、この集合が `fst B` に属することが分かります。集合とその証明を組にしたものが `inB m : DB.SM` です。
<!--/-->

```agda
  private
    inB : (m : ⟪ fst B ⟫) → ⟨ ⟪ fst B ⟫↪ m ∈ fst B ⟩
    inB m = ∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ m)

```

<!--en-->
An index family `g : Ix B n` contains one small member index at each finite
position. The function `tab` turns it into an assignment in `DB.SM ^ n` by
recursion on `n`: the head is the set presented by `g zero`, equipped with
`inB (g zero)`, and the tail is obtained from the shifted family
`λ i → g (suc i)`. Thus the order of entries is preserved exactly.
<!--zh-->
索引族 `g : Ix B n` 在每个有穷位置都含有一个小成员索引。函数 `tab` 按 `n` 递归，把它变成 `DB.SM ^ n` 中的赋值：首项是 `g zero` 所表现的集合，并配上 `inB (g zero)`；尾部来自移位后的族 `λ i → g (suc i)`。因此，所有条目的次序都得到精确保留。
<!--ja-->
添字族 `g : Ix B n` は、有限な各位置に小さな要素の添字を一つずつもちます。関数 `tab` は `n` に関する再帰によって、これを `DB.SM ^ n` の割当てへ変えます。先頭は `g zero` が表示する集合に `inB (g zero)` を添えたものであり、尾はずらした族 `λ i → g (suc i)` から得られます。したがって各項目の順序は正確に保たれます。
<!--/-->

```agda
    tab : ∀ {n} → Ix B n → DB.SM ^ n
    tab {zero} g = []
    tab {suc n} g = (⟪ fst B ⟫↪ (g zero) , inB (g zero)) ∷ tab (λ i → g (suc i))

```

<!--en-->
The first compatibility equation forgets the carrier proofs from `tab g` and
recovers exactly the family of sets presented by `g`. At position zero this is
reflexive; at a successor position it follows recursively from the shifted
tail. Functional extensionality combines these pointwise equations into
`tab-values`, an equality of the complete value families.
<!--zh-->
第一条相容等式从 `tab g` 忘去载体成员证明，恰好恢复 `g` 所表现的集合族。在位置零处，这条等式是自反的；在后继位置，它递归地来自移位后的尾部。函数外延性把这些逐点等式合成为 `tab-values`，即完整取值族之间的等式。
<!--ja-->
最初の整合性の等式は、`tab g` から台への所属証明を忘れると、`g` が表示する集合の族がそのまま得られることを述べます。位置 zero では反射的に成り立ち、後続の位置では、ずらした尾に対する再帰的な等式から従います。関数外延性がこれらの点ごとの等式をまとめ、値の族全体の等式 `tab-values` を与えます。
<!--/-->

```agda
    tab-values : ∀ {n} (g : Ix B n) → values (tab g) ≡ (λ i → ⟪ fst B ⟫↪ (g i))
    tab-values {zero} g = funExt (λ ())
    tab-values {suc n} g = funExt
      (λ { zero → refl
         ; (suc i) → funExt⁻ (tab-values (λ j → g (suc j))) i })
```

<!--en-->
Applying the graph operation `env` to `tab-values` gives the second
compatibility equation. It identifies `graph (tab g)` with the underlying set
of the canonical coded environment `envS B g`. Hence the index presentation
used by `envSet` and the restricted-carrier assignment used by inner semantics
describe the same finite graph, even though their entries carry different
auxiliary data.
<!--zh-->
把图运算 `env` 施用于 `tab-values`，便得到第二条相容等式。它把 `graph (tab g)` 与典范编码环境 `envS B g` 的底层集合认同起来。因此，`envSet` 所用的索引表现与内层语义所用的限制载体赋值描述同一个有穷图，尽管二者的条目携带不同的辅助数据。
<!--ja-->
グラフを作る演算 `env` を `tab-values` に施すと、第二の整合性の等式が得られます。これは `graph (tab g)` を、正準な符号化環境 `envS B g` の基礎集合と同定します。したがって `envSet` が使う添字表示と、内側の意味論が使う制限された台の割当ては、項目に異なる補助データを伴いながらも、同じ有限グラフを記述します。
<!--/-->

```agda

    tab-graph : ∀ {n} (g : Ix B n) → graph (tab g) ≡ fst (envS B g)
    tab-graph g = cong env (tab-values g)

```

<!--en-->
The outward specification of `envSet` recovers from a member `z`, under
propositional truncation, an index family `g` and a path from `fst z` to the
underlying set of `envS B g`. Mapping `g` to `tab g` and composing that path
with the reverse of `tab-graph` yields an assignment `δ` with
`fst z ≡ graph δ`. The result remains under truncation: it supplies neither a
globally chosen decoding nor a uniqueness claim. This restricted interface is
also what later clause-semantics arguments use when they must reason about an
arbitrary encoded environment.
<!--zh-->
`envSet` 的向外规格从成员 `z` 出发，在命题截断下恢复索引族 `g`，以及一条从 `fst z` 到 `envS B g` 底层集合的路径。把 `g` 映射为 `tab g`，再将该路径与 `tab-graph` 的逆向复合，便得到满足 `fst z ≡ graph δ` 的赋值 `δ`。结果仍在命题截断之下，既不提供全局选定的解码，也不声称解码唯一。后续的子句语义论证在处理任意编码环境时，使用的正是这项受限接口。
<!--ja-->
`envSet` の外向きの仕様は、要素 `z` から命題的切り詰めの下で添字族 `g` と、`fst z` から `envS B g` の基礎集合へのパスを復元します。`g` を `tab g` へ写し、そのパスを `tab-graph` の逆向きと合成すると、`fst z ≡ graph δ` を満たす割当て `δ` が得られます。結果は切り詰めの下にとどまり、大域的に選ばれた復号も一意性の主張も与えません。後の節の意味論で任意の符号化環境を扱うときにも、まさにこの制限されたインターフェースが使われます。
<!--/-->

```agda
  envSet-vectors : ∀ {n} (z : S) → ⟨ z ∈ˢ envSet B n ⟩
                 → ∥ Σ[ δ ∈ DB.SM ^ n ] (fst z ≡ graph δ) ∥₁
  envSet-vectors {n} z h = PT.map
    (λ { (g , qg) → tab g , qg ∙ sym (tab-graph g) }) (envSet-out B n z h)

```

<!--en-->
`Sat-spec` starts with a particular assignment and a graph equation.
`Sat-out` gives the corresponding statement for an arbitrary member `z` of a
satisfaction value: under `∃[]`, there is an assignment `δ` whose graph is
`fst z` and which satisfies the formula in the restricted structure. The
propositional truncation is part of the conclusion, so this theorem selects no
decoding assignment and proves no such assignment unique. It asserts only the
direction from membership in `Sat` to the existence of a satisfying
representation.
<!--zh-->
`Sat-spec` 从一项给定赋值和一条图等式出发。`Sat-out` 则陈述满足取值的任意成员 `z` 所对应的结论：在 `∃[]` 下，存在赋值 `δ`，其图就是 `fst z`，并且它在限制结构中满足该公式。命题截断是结论本身的一部分，所以这项定理既不选定解码赋值，也不证明这样的赋值唯一；它只断言从属于 `Sat` 到存在一项满足公式的表示这一方向。
<!--ja-->
`Sat-spec` は、特定の割当てとグラフの等式から出発します。`Sat-out` は、充足の値の任意の要素 `z` に対応する主張を与えます。すなわち `∃[]` のもとで、グラフが `fst z` であり、制限構造でその論理式を充足する割当て `δ` が存在します。命題的切り詰めは結論そのものの一部なので、この定理は復号する割当てを選び出さず、そのような割当ての一意性も証明しません。主張するのは、`Sat` への所属から充足する表示の存在へ進む向きだけです。
<!--/-->

```agda
  Sat-out : ∀ {n} (φ : Formula DB.SM n) (z : S)
          → ⟨ z ∈ˢ Sat B (mapFo intoL φ) ⟩
          → ∥ (Σ[ δ ∈ DB.SM ^ n ] ((fst z ≡ graph δ) × ⟨ δ ⊨ᴮ φ ⟩)) ∥₁
  Sat-out {n} φ z h = PT.map
    (λ { (g , qg) → tab g , (qg ∙ sym (tab-graph g)
```

<!--en-->
The last two lines complete the outward reading without strengthening the
recovered data. From the original proof of membership in `Sat`, `Sat-mem`
supplies only the component asserting that `z` belongs to the environment set;
`envSet-out` then returns an index family `g` and its graph equation under
propositional truncation. Inside `PT.map`, `tab g` is the corresponding inner
assignment, and `qg ∙ sym (tab-graph g)` identifies the underlying set of `z`
with its graph. With that equation fixed, `Sat-spec` transports the original
membership proof `h` directly to inner satisfaction. The assignment and its
satisfaction proof therefore remain inside the same truncation, with no choice
or uniqueness claim.
<!--zh-->
最后两行完成外向读式，同时没有增强恢复所得资料的逻辑强度。从原来的 `Sat` 成员证明出发，`Sat-mem` 只取出「`z` 属于环境集」这一分量；`envSet-out` 随即在命题截断下返回索引族 `g` 及其图等式。在 `PT.map` 内，`tab g` 是相应的内层赋值，而 `qg ∙ sym (tab-graph g)` 把 `z` 的底层集合认同为该赋值的图。固定这条等式后，`Sat-spec` 直接把原成员证明 `h` 搬运为内层满足。因此，赋值及其满足证明始终留在同一个命题截断中，这里既没有作出选择，也没有声称唯一性。
<!--ja-->
最後の二行は、復元されたデータの論理的な強さを増すことなく、外向きの読みを完成させます。もとの `Sat` への所属証明から、`Sat-mem` が取り出すのは `z` が環境集合に属するという成分だけです。続いて `envSet-out` は、命題的切り詰めの中で添字族 `g` とそのグラフ等式を返します。`PT.map` の内部では、`tab g` が対応する内側の割当てであり、`qg ∙ sym (tab-graph g)` が `z` の基礎集合をその割当てのグラフと同一視します。この等式を固定すると、`Sat-spec` はもとの所属証明 `h` を直接、内側の充足へ運びます。したがって割当てとその充足証明は同じ切り詰めの中にとどまり、選択も一意性も主張されません。
<!--/-->

```agda
       , subst ⟨_⟩ (Sat-spec φ (tab g) z (qg ∙ sym (tab-graph g))) h) })
    (envSet-out B n z (subst ⟨_⟩ (Sat-mem B (mapFo intoL φ) z) h .fst))
```

<!--en-->
## Agreement with definable subsets
<!--zh-->
## 与可定义子集相符
<!--ja-->
## 定義可能部分集合との一致
<!--/-->

<!--en-->
To compare this recursion with definable subsets, constants must pass through
three domains. A formula `ψ` begins over the small presentation
`⟪ fst B ⟫`; `DB.ι` sends its constants into the restricted carrier, and
`intoL` then sends those carrier elements into the ambient carrier `S`. By
definition their composite is `asConst`. Functoriality of constant relabelling,
expressed by `mapFo-comp`, therefore identifies the twice-relabelled formula
`mapFo intoL (mapFo DB.ι ψ)` with the directly relabelled formula
`mapFo asConst ψ`. This is an equality of formulas and will let the semantic
bridge use the constant form expected by the recursion.
<!--zh-->
为了把这项递归同可定义子集比较，常元需要穿过三个论域。公式 `ψ` 起初取常元于小呈现 `⟪ fst B ⟫`；`DB.ι` 把这些常元送入限制载体，`intoL` 再把所得载体元素送入外围载体 `S`。按定义，这两个映射的复合就是 `asConst`。因此，`mapFo-comp` 所表达的常元改名函子性把两次改名所得的公式 `mapFo intoL (mapFo DB.ι ψ)` 认同为直接改名所得的公式 `mapFo asConst ψ`。这是公式之间的等式，它使语义桥能够采用递归所需的常元形式。
<!--ja-->
この再帰を定義可能部分集合と比較するには、定数を三つの領域の間で移す必要があります。論理式 `ψ` の定数は、初めは小さな提示 `⟪ fst B ⟫` に属します。`DB.ι` はそれらを制限された台へ送り、続いて `intoL` がその台の要素を周囲の台 `S` へ送ります。定義により、この合成が `asConst` です。したがって `mapFo-comp` が表す定数の改名の関手性により、二度改名した論理式 `mapFo intoL (mapFo DB.ι ψ)` は、直接改名した論理式 `mapFo asConst ψ` と同一視されます。これは論理式の等式であり、意味論の橋を、再帰が要求する定数の形で使えるようにします。
<!--/-->

```agda
  private
    mapFo-fuse : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n)
               → mapFo intoL (mapFo DB.ι ψ) ≡ mapFo asConst ψ
    mapFo-fuse = mapFo-comp DB.ι intoL

```

<!--en-->
The second normalization concerns the one-entry assignment used by a
definable subset. The canonical environment `envS B (λ _ → m)` is built from
the constant index family with value `m`; its underlying set is the graph of
the vector `DB.ι m ∷ []`. Both graphs have the same value family, since a
length-one family has only the index `zero`. Functional extensionality checks
that index, while the successor case is impossible, and congruence carries the
result through the graph operation. Thus this concrete environment satisfies
the graph hypothesis needed by `Sat-spec`.
<!--zh-->
第二项归一化处理可定义子集所用的单条目赋值。典范环境 `envS B (λ _ → m)` 由恒取 `m` 的索引族构成，其底层集合就是向量 `DB.ι m ∷ []` 的图。两幅图的取值族相同，因为长度一的族只有索引 `zero`。函数外延性核对这个索引，后继情形不可能出现；同余再把所得等式带过图运算。因此，这个具体环境满足 `Sat-spec` 所需的图假设。
<!--ja-->
第二の正規化は、定義可能部分集合で用いる一項目の割当てに関するものです。正準な環境 `envS B (λ _ → m)` は、値が常に `m` である添字族から作られ、その基礎集合はベクトル `DB.ι m ∷ []` のグラフです。長さ一の族には添字 `zero` しかないため、二つのグラフの値の族は一致します。関数外延性がこの添字を確認し、後続の場合は不可能です。さらに合同性がその等式をグラフ演算へ運びます。こうして、この具体的な環境は `Sat-spec` が必要とするグラフの仮定を満たします。
<!--/-->

```agda
    graph-single : (m : ⟪ fst B ⟫)
                 → fst (envS B (λ _ → m)) ≡ graph (DB.ι m ∷ [])
    graph-single m = cong env (funExt (λ { zero → refl ; (suc ()) }))

```

<!--en-->
These two normalizations give the bridge in the small constant alphabet.
Suppose `z` has the same underlying set as the graph of an inner assignment
`δ`. Then membership in the recursive value for `mapFo asConst ψ` is equal to
inner satisfaction of `mapFo DB.ι ψ` at `δ`. The right-hand formula has
constants in the restricted carrier and is evaluated there with the identity
interpretation; equivalently, it is the original small formula with its
constants interpreted by `DB.ι`. The proof first uses the symmetric direction
of `mapFo-fuse` to expose the two relabellings on the left, and then applies
`Sat-spec`. This gives the small-alphabet bridge at every arity before the
one-variable specialization below.
<!--zh-->
这两项归一化给出小常元字母表中的桥。设 `z` 的底层集合等于内层赋值 `δ` 的图，则 `z` 属于 `mapFo asConst ψ` 的递归取值这一命题，等于 `mapFo DB.ι ψ` 在 `δ` 处的内层满足。右侧公式的常元属于限制载体，并在该结构中按恒等解释求值；等价地说，它就是把原小公式的常元按 `DB.ι` 解释。证明先取 `mapFo-fuse` 的对称方向，在左侧显出两次常元改名，再应用 `Sat-spec`。由此先得到适用于任意元数的小字母表版本，再在下文特化到一个自由变元。
<!--ja-->
この二つの正規化から、小さな定数アルファベットにおける橋が得られます。`z` の基礎集合が内側の割当て `δ` のグラフに等しいとします。このとき、`mapFo asConst ψ` に対する再帰の値への `z` の所属は、`δ` における `mapFo DB.ι ψ` の内側の充足と等しくなります。右辺の論理式は制限された台に定数を持ち、その構造で恒等写像を解釈として評価されます。言い換えれば、もとの小さな論理式の定数を `DB.ι` で解釈したものです。証明はまず `mapFo-fuse` を逆向きに使って左辺に二段の定数の改名を現し、次に `Sat-spec` を適用します。これにより、下で自由変数が一つの場合へ特殊化する前に、任意のアリティに対する小さなアルファベットでの橋が得られます。
<!--/-->

```agda
  Sat-small-spec : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (δ : DB.SM ^ n) (z : S)
                 → fst z ≡ graph δ
                 → (z ∈ˢ Sat B (mapFo asConst ψ)) ≡ (δ ⊨ᴮ mapFo DB.ι ψ)
  Sat-small-spec ψ δ z q = cong (λ χ → z ∈ˢ Sat B χ) (sym (mapFo-fuse ψ))
    ∙ Sat-spec (mapFo DB.ι ψ) δ z q
```

<!--en-->
Now specialize to one free variable. For a small formula `ψ` and a
presentation index `m`, `defSet-Sat` compares two propositions: the set named
by `m` belongs to the definable subset `DB.defSet ψ`, and the canonical
one-entry environment for `m` belongs to the recursive satisfaction value for
`mapFo asConst ψ`. The first path in the proof is `DB.defSet-mem`. It unfolds
the meaning of the definable subset, turning its membership proposition into
inner satisfaction of `ψ` at the assignment `DB.ι m ∷ []`, with constants
interpreted by `DB.ι`.
<!--zh-->
现在特化到一个自由变元。对小公式 `ψ` 与呈现索引 `m`，`defSet-Sat` 比较两个命题：`m` 所指称的集合属于可定义子集 `DB.defSet ψ`；而 `m` 的典范单条目环境属于 `mapFo asConst ψ` 的递归满足关系值。证明的第一条路径是 `DB.defSet-mem`。它展开可定义子集的含义，把前一项成员命题化为 `ψ` 在赋值 `DB.ι m ∷ []` 处的内层满足，其中常元由 `DB.ι` 解释。
<!--ja-->
ここで自由変数が一つの場合に特殊化します。小さな論理式 `ψ` と提示の添字 `m` に対し、`defSet-Sat` は二つの命題を比較します。`m` が名指す集合が定義可能部分集合 `DB.defSet ψ` に属することと、`m` に対する正準な一項目の環境が `mapFo asConst ψ` の再帰的な充足関係の値に属することです。証明の最初のパスは `DB.defSet-mem` です。これは定義可能部分集合の意味を展開し、前者の所属命題を、定数を `DB.ι` で解釈した `ψ` の、割当て `DB.ι m ∷ []` における内側の充足へ変えます。
<!--/-->

```agda

  defSet-Sat : (ψ : Formula ⟪ fst B ⟫ 1) (m : ⟪ fst B ⟫)
             → (⟪ fst B ⟫↪ m ∈ DB.defSet ψ)
             ≡ (envS B (λ _ → m) ∈ˢ Sat B (mapFo asConst ψ))
  defSet-Sat ψ m =
      DB.defSet-mem ψ m
```

<!--en-->
Three more paths reach the announced recursive value. First, the symmetric
direction of `⊨-map` replaces satisfaction of `ψ` with constants interpreted
by `DB.ι` by satisfaction of the relabelled formula `mapFo DB.ι ψ` under the
identity interpretation. Second, the symmetric direction of `Sat-spec`, using
`graph-single`, turns that inner satisfaction into membership in
`Sat B (mapFo intoL (mapFo DB.ι ψ))`. Finally, congruence along `mapFo-fuse`
replaces the twice-relabelled formula by `mapFo asConst ψ`. Every link is a path
between truth values. Since the assignment and its graph are given explicitly,
neither assignment recovery nor propositional truncation is involved. The
result is the one-variable interface through which definable-power-set
constructions read the recursive satisfaction value.
<!--zh-->
再接三条路径，便到达陈述中的递归取值。首先，`⊨-map` 的对称方向把「以 `DB.ι` 解释常元时 `ψ` 的满足」换成「恒等解释下，改名公式 `mapFo DB.ι ψ` 的满足」。其次，`Sat-spec` 的对称方向借助 `graph-single`，把这项内层满足换成 `Sat B (mapFo intoL (mapFo DB.ι ψ))` 中的成员。最后，沿 `mapFo-fuse` 作同余，把两次改名的公式换成 `mapFo asConst ψ`。每一环都是命题真值之间的路径。由于赋值及其图均已明确给出，这里既无须恢复赋值，也不涉及命题截断。所得结论正是一元接口，可定义幂集的构造通过它读取递归满足关系值。
<!--ja-->
さらに三つのパスをつなぐと、主張された再帰の値に到達します。まず `⊨-map` を逆向きに使い、定数を `DB.ι` で解釈した `ψ` の充足を、恒等解釈のもとで改名された論理式 `mapFo DB.ι ψ` の充足へ置き換えます。次に `graph-single` を用いて `Sat-spec` を逆向きにたどり、その内側の充足を `Sat B (mapFo intoL (mapFo DB.ι ψ))` への所属へ変えます。最後に `mapFo-fuse` に沿う合同性により、二度改名された論理式を `mapFo asConst ψ` に置き換えます。各段階は真理値の間のパスです。割当てとそのグラフは明示的に与えられているため、割当ての復元も命題的切り詰めも用いません。この結果が、定義可能冪集合の構成から再帰的な充足関係の値を読むための、一変数のインターフェースになります。
<!--/-->

```agda
    ∙ sym (⊨-map DB.𝒮M DB.ι id ψ (DB.ι m ∷ []))
    ∙ sym (Sat-spec (mapFo DB.ι ψ) (DB.ι m ∷ []) (envS B (λ _ → m))
             (graph-single m))
    ∙ cong (λ χ → envS B (λ _ → m) ∈ˢ Sat B χ) (mapFo-fuse ψ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The central result `Sat-spec` identifies membership in the recursively
constructed value with inner satisfaction for every given assignment: if
`fst z ≡ graph δ`, then membership of `z` in
`Sat B (mapFo intoL φ)` is the same proposition as `δ ⊨ᴮ φ`. When the
input is instead an arbitrary coded member, `Sat-out` produces only under
`∃[]` an assignment with the required graph and satisfaction proof; it
neither selects that assignment nor proves it unique. After constants from the
small presentation are relabelled through `DB.ι` and `intoL`,
`Sat-small-spec` gives the bridge at every arity, and `defSet-Sat` specializes
it to one free variable by identifying definable-subset membership with
membership of the canonical one-entry environment. A uniform table and the
uniqueness of candidate table values require the later pinned-recursion and
uniform-satisfaction arguments.
<!--zh-->
中心结论 `Sat-spec` 对每项给定赋值，把递归构造所得取值中的隶属与内层满足认同起来：若 `fst z ≡ graph δ`，则 `z` 属于 `Sat B (mapFo intoL φ)` 与 `δ ⊨ᴮ φ` 是同一个命题。若输入改为满足取值的任意编码成员，`Sat-out` 也只在 `∃[]` 下给出一项具有所需图等式与满足证明的赋值；它既不选定这项赋值，也不证明其唯一。把小表现中的常元依次经 `DB.ι` 与 `intoL` 改名后，`Sat-small-spec` 给出任意元数的桥，`defSet-Sat` 再把它特化到一个自由变元，将可定义子集中的隶属与典范单条目环境的隶属认同起来。统一表的构造与候选表取值的唯一性仍需后续的钉扎递归和统一满足关系论证。
<!--ja-->
中心的な結果 `Sat-spec` は、与えられた各割当てについて、再帰的に構成された値への所属を内側の充足と同定します。`fst z ≡ graph δ` ならば、`z` が `Sat B (mapFo intoL φ)` に属することと `δ ⊨ᴮ φ` は同じ命題です。入力が充足の値の任意の符号化された要素である場合、`Sat-out` は必要なグラフの等式と充足の証明を備えた割当てを `∃[]` のもとで与えるだけです。その割当てを選び出すことも、一意性を証明することもありません。小さな表示の定数を `DB.ι`、`intoL` の順に取り替えると、`Sat-small-spec` が任意のアリティで橋を与え、`defSet-Sat` はそれを自由変数が一つの場合に特殊化して、定義可能部分集合への所属を正準な一項目環境の所属と同定します。一様な表の構成と候補表の値の一意性には、後の固定された再帰と一様な充足関係の議論が必要です。
<!--/-->
