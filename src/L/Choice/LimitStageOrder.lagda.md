```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The limit-stage order inside L
<!--zh-->
# L 内部的极限层序
<!--ja-->
# L の内部にある極限段階の順序
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and the excluded-middle instance just described. The
internal relation constructed later is still conditional at this point: it is
defined inside the module `Described`{.Agda} after a formula for the finite-stage
order and its two semantic directions have been supplied. The next chapter will
provide that instance and expose `codeOrder`{.Agda} for subsequent use.
<!--zh-->
固定宇宙层级 `ℓ` 与刚才说明的排中律实例。此时后文的内部关系仍是条件式构造：只有给出描述有穷层序的公式及其两个语义方向后，它才在模块 `Described`{.Agda}
内部得到定义。下一章会提供这个实例，并把 `codeOrder`{.Agda} 公开给后续构造使用。
<!--ja-->
宇宙レベル `ℓ` と、いま説明した排中律の実例を固定する。この時点では、後で作る内部関係はまだ条件つきである。有限段階の順序を表す論理式と、その意味論の二方向を与えた後に、モジュール `Described`{.Agda} の内部で定義される。次章がその実例を与え、後続の構成が使えるように `codeOrder`{.Agda} を公開する。
<!--/-->

```agda
module L.Choice.LimitStageOrder {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; _∨̇_; ¬̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω; ∈#-elim; #∈#-elim; ω-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( numL )
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( Limit; level; level-in; levelData; limitOrder
        ; before; precedes; Agrees; Witness; finiteStage )
open import L.Choice.NameComparison {ℓ} lem using ( module Adequacy )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )
import FOL.Absoluteness
```

<!--en-->
An external strict well-order on the members of `Lset ω`{.Agda} is already
available. The question here is how its comparison can be used by formulas
inside `L`. The answer will pass through three distinct forms: a meta-level
comparison, an object-language description of that comparison, and, once the
finite-stage description has been supplied, a constructible set realizing the
described relation.
<!--zh-->
`Lset ω`{.Agda} 的诸成员在外部已经带有严格良序。本章的问题是：怎样让 `L`内部的公式使用这个比较？答案要依次经过三种彼此有别的形态：元层面的比较、对象语言中对该比较的描述，以及在有穷层描述已经给出后实现该关系的可构造集合。
<!--ja-->
`Lset ω`{.Agda} の要素には、外側ですでに狭義整列順序が与えられている。ここでの問いは、その比較を `L` の内部の論理式からどのように使えるようにするかである。答えは三つの異なる形を順に通る。メタ水準の比較、その比較の対象言語による記述、そして有限段階の記述が与えられた後に、その関係を実現する構成可能集合である。
<!--/-->

<!--en-->
All constructions are relative to one explicit instance of excluded middle at
level `ℓ-suc ℓ`. Earlier work used this hypothesis to obtain the least finite
stage at which a limit-stage member appears, and the present chapter also passes
it to the separation and bounding results it uses. This hypothesis decides
propositions when those constructions require it; it does not provide a choice
function for an arbitrary family.
<!--zh-->
本章的全部构造都相对于层级 `ℓ-suc ℓ` 上一个显式的排中律实例。前文已用这条假设取得极限层成员首次出现的最小有穷层，本章还把同一实例传给所用的分离结果与取界结果。它在这些构造需要时判定命题，却不为任意集合族提供选择函数。
<!--ja-->
この章のすべての構成は、レベル `ℓ-suc ℓ` における一つの明示的な排中律の実例に相対している。先の章では、この仮定から極限段階の要素が最初に現れる有限段階を得た。この章では、用いる分出と上界の結果にも同じ実例を渡す。この仮定は必要な箇所で命題を判定するが、任意の族に対する選択関数を与えない。
<!--/-->



<!--en-->
The object language must describe comparisons without confusing syntax with
their meaning in the hierarchy. Its formulas use variables, constants,
membership, connectives and quantifiers; because the constant domain is the
constructible carrier, a constant already denotes a particular constructible
set. The coding lemmas provide the two elementary tests needed later. An
ordered-pair equality determines both components, and the numeral coding is
injective, while `#mono`{.Agda} turns `k < m` into membership of `# k`{.Agda}
in `# m`{.Agda}. Thus set-theoretic membership can faithfully carry the strict
comparison of finite indices.
<!--zh-->
对象语言必须描述比较，同时不把语法与它在层级中的意义混为一谈。公式使用变元、常元、隶属、联结词与量词；由于常元域就是可构造载体，一个常元已经指称某个确定的可构造集合。后文所需的两个基本检验由编码引理提供。有序对的等式决定两个分量，数码编码也是单射的，而 `#mono`{.Agda} 把 `k < m` 变为 `# k`{.Agda} 属于
`# m`{.Agda}。因此，集合论隶属能够忠实承载有穷指标的严格比较。
<!--ja-->
対象言語は、構文と階層における意味を混同せずに比較を記述しなければならない。論理式は変数、定数、所属、結合子、量化子を使う。定数領域は構成可能な台なので、定数はすでに特定の構成可能集合を指す。後で必要となる二つの基本的な判定は、符号化の補題から得られる。順序対の等式は二つの成分を決定し、数項の符号化も単射である。さらに `#mono`{.Agda} は `k < m` を、`# k`{.Agda} が `# m`{.Agda} に属するという事実へ移す。したがって集合論的所属は、有限添字の狭義比較を忠実に表せる。
<!--/-->

<!--en-->
The intended structure is the constructible universe. An element of its carrier
packages a set with evidence of constructibility, and transitivity supplies the
same evidence for every member of such a set. This lets witnesses move from
ordinary hierarchy membership into environments of the object language. In
particular, `finiteStage n`{.Agda} is the stage `Lset (# n)`{.Agda}, whereas the
limit stage is `Lset ω`{.Agda}; the numeral and ordinal facts keep these indices
distinct from the stages they name. The packaged stages and the constant `ωʟ`{.Agda}
then allow formulas to refer to this hierarchy from inside the structure.
<!--zh-->
这里采用的结构是可构造宇宙。其载体元素把一个集合与可构造性证据打包在一起，而传递性又为该集合的每个成员提供同类证据。这样，普通层级隶属中的见证便能进入对象语言的环境。特别地，`finiteStage n`{.Agda} 是 `Lset (# n)`{.Agda}，极限层则是
`Lset ω`{.Agda}；关于数码与序数的事实使这些指标始终区别于它们所指名的层。经过包装的层与常元 `ωʟ`{.Agda} 随后使公式能够从结构内部谈论这条层级。
<!--ja-->
ここで用いる構造は構成可能宇宙である。その台の要素は、集合と構成可能性の証拠をひとまとめにする。推移性により、その集合の各要素にも同じ種類の証拠が得られる。このため、通常の階層における所属の証人を対象言語の環境へ移せる。とくに、`finiteStage n`{.Agda} は `Lset (# n)`{.Agda} という段階であり、極限段階は
`Lset ω`{.Agda} である。数項と順序数に関する事実により、添字と、それが名指す段階を区別できる。包装された段階と定数 `ωʟ`{.Agda} によって、論理式は構造の内部からこの階層について語れる。
<!--/-->

<!--en-->
Three bridges turn a semantic comparison into a set of `L`. First,
`smallDom`{.Agda} puts a small family inside one common constructible set, but
does not claim that the bound is its exact image. Second, separation cuts from
such a bound exactly the elements satisfying a one-variable formula. Third,
the coding formulas for pairs, relation membership, and the hierarchy sequence
come with adequacy laws that translate satisfaction into the corresponding
facts about sets. Together these tools separate the problem of finding a common
domain from the problem of stating the exact relation on that domain.
<!--zh-->
三座桥把语义上的比较变成 `L` 的一个集合。首先，`smallDom`{.Agda} 把一个小族放进同一个可构造集合，却不声称这个界恰好等于该族的像。其次，分离从这样的界中精确取出满足一元公式的元素。最后，描述有序对、关系隶属与层级序列的编码公式都带有充分性定律，把满足关系翻译成相应的集合事实。这三件工具把寻找公共定义域与在该域上陈述精确关系这两个问题分开处理。
<!--ja-->
三つの橋によって、意味論上の比較を `L` の集合へ変える。まず `smallDom`{.Agda} は、小さな族を一つの共通な構成可能集合に入れるが、その上界が族の像と一致するとは主張しない。次に分出は、その上界から一変数の論理式を満たす要素だけを正確に取り出す。最後に、順序対、関係への所属、階層列を記述する符号化論理式には、充足を対応する集合の事実へ移す妥当性の法則がある。これらにより、共通の領域を見つける問題と、その領域上で正確な関係を述べる問題を分けて扱える。
<!--/-->

<!--en-->
The comparison to be represented is already defined externally. At a successor
stage, `before (suc n)`{.Agda} compares two subsets of `finiteStage n`{.Agda}
at their earliest disagreement, using `before n`{.Agda} below that point. A
witness for `precedes R A x y`{.Agda} lies in `A`, belongs to `y` and not to
`x`, and records agreement of `x` and `y` at every earlier point; its existence
is propositionally truncated. The type `Limit`{.Agda} packages members of
`Lset ω`{.Agda}, and their least appearance levels form the primary key of
`limitOrder`{.Agda}; only equal levels invoke the corresponding `before`{.Agda}
comparison. The two representation directions for the resulting relation set
have exactly the form required by `Adequacy.Keys`{.Agda}.
<!--zh-->
要表示的比较在外部已经定义。到了后继层，`before (suc n)`{.Agda} 用
`before n`{.Agda} 排列更早的点，并在最先分歧处比较 `finiteStage n`{.Agda}
的两个子集。`precedes R A x y`{.Agda} 的见证属于 `A`，属于 `y` 而不属于 `x`，并记录 `x` 与 `y` 在每个更早点处一致；该见证的存在带有命题截断。类型
`Limit`{.Agda} 打包 `Lset ω`{.Agda} 的成员，而它们的最小出现层号构成
`limitOrder`{.Agda} 的主键；只有层号相同才调用相应的 `before`{.Agda} 比较。所得关系集的两个表示方向，形状正好符合 `Adequacy.Keys`{.Agda} 的要求。
<!--ja-->
表現すべき比較は、外側ですでに定義されている。後続段階では、`before (suc n)`{.Agda} が `before n`{.Agda} によってより前の点を並べ、`finiteStage n`{.Agda} の二つの部分集合を最初の相違で比較する。`precedes R A x y`{.Agda} の証人は `A` に属し、`y` に属して `x` には属さず、より前のすべての点で `x` と `y` が一致することを記録する。その存在は命題的に切り詰められている。型 `Limit`{.Agda} は `Lset ω`{.Agda} の要素を包装し、その最小出現段階が `limitOrder`{.Agda} の第一の鍵になる。対応する `before`{.Agda} の比較を使うのは、段階が等しい場合だけである。得られる関係集合の二つの表現方向は、`Adequacy.Keys`{.Agda} が要求する形に正確に一致する。
<!--/-->

<!--en-->
The order `limitOrder`{.Agda} is available as an `SWO`{.Agda} bundle: besides
its comparison it provides trichotomy, irreflexivity, transitivity and
well-foundedness. The internalization argument does not reprove these laws.
It uses the first three later for a specific purpose: when reading an
object-language disjunction yields only a propositionally truncated strict
comparison, trichotomy identifies the possible branch, while irreflexivity and
transitivity refute the incompatible branches.
<!--zh-->
`limitOrder`{.Agda} 以 `SWO`{.Agda} 束的形式给出：除比较本身外，还包含三歧性、非自反性、传递性与良基性。内部化论证不会重新证明这些定律。后文只为一个特定目的使用前三条：从对象语言析取读回时只能先得到带命题截断的严格比较，三歧性指出可能的分支，非自反性与传递性则排除不相容的分支。
<!--ja-->
`limitOrder`{.Agda} は `SWO`{.Agda} の構造として与えられている。比較そのものに加え、三分性、非反射性、推移性、整礎性を備える。内部化の議論はこれらの法則を証明し直さない。後では、最初の三つを一つの目的に使う。対象言語の選言から読み戻せるのが命題的に切り詰められた狭義比較だけであるとき、三分性が候補となる枝を示し、非反射性と推移性が両立しない枝を退ける。
<!--/-->

<!--en-->
The limit comparison has the lexicographic shape needed later. Its first
alternative says that the first member has a smaller level. Its second says
that the levels agree and compares the underlying sets by `before`{.Agda} at
their common level. Natural-number trichotomy analyzes the first key, and
`subst2`{.Agda} transports binary relations when equalities identify the coded
levels or endpoints. The accompanying `Lift`{.Agda} and `lower`{.Agda}
operations only reconcile universe levels; they do not remove propositional
truncation.
<!--zh-->
极限比较具有后文所需的字典序形状。第一支说第一个成员的层号更小；第二支说双方层号相同，并在共同层号处用 `before`{.Agda} 比较底层集合。自然数的三歧分析第一把键，`subst2`{.Agda} 则在等式识别出编码层号或端点时运输二元关系。与之相伴的
`Lift`{.Agda} 与 `lower`{.Agda} 只处理宇宙层级，其中 `lower` 对应命题换级；它们都不消除命题截断。
<!--ja-->
極限の比較は、後で必要となる辞書式の形をしている。第一の選択肢は、最初の要素のレベルが小さいことを述べる。第二の選択肢は、二つのレベルが一致し、その共通レベルの
`before`{.Agda} によって基礎集合を比較する。自然数の三分性が第一の鍵を分析し、`subst2`{.Agda} は等式が符号化されたレベルや端点を同定するとき、二項関係を運ぶ。付随する `Lift`{.Agda} と `lower`{.Agda} は宇宙レベルをそろえるだけであり、命題的な切り詰めを取り除く操作ではない。
<!--/-->

```agda
open import Cubical.Data.Nat.Order using ( _<_; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
```

<!--en-->
Object-language existential quantification and disjunction are interpreted as
propositionally truncated existence and choice of branch. Consequently, their
witnesses may be used only when the target is a proposition, such as
impossibility, equality of hierarchy sets, or another truncation. This does not
mean that every existential type in the chapter is truncated: explicit data,
including packaged carrier elements and bounds, remains visible when its type
requires it. Recovering a strict comparison from a truncation is not a general
elimination principle either; it relies specifically on the trichotomy and
order laws of `limitOrder`{.Agda}.
<!--zh-->
对象语言的存在量词与析取分别解释为带命题截断的存在与分支选择。因此，只有当目标是命题时才能使用其中的见证，例如不可能性、层级集合的等式或另一项命题截断。这不表示本章每个存在类型都带命题截断：当类型要求显式数据时，打包后的载体元素与公共界之类的数据仍然可见。从命题截断恢复严格比较也不是消除命题截断的一般原则；它专门依赖 `limitOrder`{.Agda} 的三歧性与序定律。
<!--ja-->
対象言語の存在量化と選言は、それぞれ命題的に切り詰められた存在と枝の選択として解釈される。したがって、その証人を使えるのは、不可能性、階層の集合の等式、別の切り詰めなど、目標が命題である場合だけである。ただし、この章に現れるすべての存在型が切り詰められているわけではない。型が明示的なデータを要求する場合、包装された台の要素や共通上界はそのまま見える。また、命題的切り詰めから狭義比較を復元する議論は一般的な除去原理ではなく、`limitOrder`{.Agda} の三分性と順序法則に特有のものである。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
```

<!--en-->
To apply the bounding lemma, the members of `Lset ω`{.Agda} need a small index
type. The fiber `⟪ Lset ω ⟫`{.Agda} provides such indices, and
`∈-asFiber`{.Agda} turns a given membership proof into an index whose image is
the original member. Taking a product of two such fibers therefore indexes all
ordered pairs of limit-stage members. The later set `pairsBound`{.Agda} will
contain every one of these pairs; exactness will come only after separation.
<!--zh-->
为了应用取界引理，`Lset ω`{.Agda} 的成员需要一个小索引类型。纤维
`⟪ Lset ω ⟫`{.Agda} 提供这种指标，而 `∈-asFiber`{.Agda} 把给定的成员证明变成一个指标，其像就是原来的成员。因此，两个这种纤维的积索引了极限层成员的所有有序对。后文的 `pairsBound`{.Agda} 会包含这些对中的每一个；精确性要到分离以后才得到。
<!--ja-->
上界の補題を使うには、`Lset ω`{.Agda} の要素に小さな添字型が必要である。ファイバー `⟪ Lset ω ⟫`{.Agda} がその添字を与え、`∈-asFiber`{.Agda} は与えられた所属証明を、像が元の要素になる添字へ変える。したがって二つのファイバーの積は、極限段階の要素からなるすべての順序対を添字づける。後で作る
`pairsBound`{.Agda} はこれらの対をすべて含むが、正確な関係が得られるのは分出の後である。
<!--/-->

```agda
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; ω )
```

<!--en-->
Three membership symbols now have separate roles. For carrier elements,
`x ∈ˢ y` is the proposition-valued membership of the constructible structure;
between underlying hierarchy sets, `fst x ∈ fst y` uses ambient membership;
inside a formula, `_∈̇_`{.Agda} is only the syntactic membership atom. The
satisfaction judgment introduced next is what turns the third form into the
first two. Keeping these layers separate will prevent a formula that describes
an order from being mistaken for a proof that its realizing set is internally
well-ordered.
<!--zh-->
现在有三种隶属记号，各自承担不同角色。对载体元素，`x ∈ˢ y` 是可构造结构中取命题值的隶属；对底层的层级集合，`fst x ∈ fst y` 使用外围隶属；在公式内部，`_∈̇_`{.Agda}
只是句法上的隶属原子。下一步引入的满足关系把第三种形式解释成前两种。分清这些层次，就不会把描述一个序的公式误当成「其实现集合在内部已被证明为良序」。
<!--ja-->
ここでは三つの所属記号が別々の役割をもつ。台の要素に対する `x ∈ˢ y` は、構成可能構造の命題値の所属である。基礎となる階層の集合どうしでは、`fst x ∈ fst y` が周囲の所属を表す。論理式の内部では `_∈̇_`{.Agda} は所属を表す構文上の原子にすぎない。次に導入する充足判定が、第三の形に最初の二つの意味を与える。この層の区別により、順序を記述する論理式を、その実現集合が内部で整列順序をなすという証明と取り違えずに済む。
<!--/-->

```agda
open hPropStructure 𝒮ʟ
```

<!--en-->
The judgment `_⊨_`{.Agda} is the inner satisfaction relation obtained by
restricting the ambient hierarchy structure to the constructible class. Its
carrier consists of sets equipped with constructibility evidence, so both
constants and quantified values range over constructible objects. Atomic
membership is interpreted through first projections, and transitivity ensures
that a member of a constructible bound can again be packaged as a carrier
element. Thus satisfaction supplies the precise bridge from an object-language
formula to ordinary membership facts about its underlying sets.
<!--zh-->
判断 `_⊨_`{.Agda} 是把外围层级结构限制到可构造类后得到的内层满足关系。它的载体由集合及其可构造性证据组成，因此常元与量化取值都遍及可构造对象。原子隶属通过第一投影解释，而传递性保证可构造界的成员仍能包装成载体元素。于是，满足关系在对象语言公式与其底层集合的普通隶属事实之间给出精确的桥梁。
<!--ja-->
判定 `_⊨_`{.Agda} は、周囲の階層構造を構成可能クラスに制限して得られる内側の充足関係である。その台は集合と構成可能性の証拠からなるので、定数も量化される値も構成可能な対象を範囲とする。原子的所属は第一射影を通して解釈され、推移性により、構成可能な限界の要素を再び台の要素として包装できる。したがって充足は、対象言語の論理式から、その基礎集合についての通常の所属事実へ至る正確な橋になる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
Write `_≺ˡ_`{.Agda} for the comparison carried by `limitOrder`{.Agda}. It orders
two limit-stage members first by their least appearance levels and, when those
levels coincide, by earliest disagreement in the common finite stage. The
remaining goal is conditional: given an object-language formula representing
every finite-stage `before`{.Agda} relation on its intended domain, construct
inside `Described`{.Agda} a set `codeOrder`{.Agda} such that the ordered pair of
`u` and `v` belongs to it exactly when `u ≺ˡ v`. The next chapter supplies the
required finite-stage formula and thereby obtains the usable instance.
<!--zh-->
把 `limitOrder`{.Agda} 携带的比较记作 `_≺ˡ_`{.Agda}。它先按最小出现层号比较两个极限层成员；层号相同，再按共同有穷层中的最先分歧比较。接下来的目标是条件式的：假设有一条对象语言公式在预定定义域上表示每个有穷层的 `before`{.Agda} 关系，便在
`Described`{.Agda} 内部构造集合 `codeOrder`{.Agda}，使 `u` 与 `v` 的有序对属于它当且仅当 `u ≺ˡ v`。下一章会给出所需的有穷层公式，从而得到可实际使用的实例。
<!--ja-->
`limitOrder`{.Agda} がもつ比較を `_≺ˡ_`{.Agda} と書く。二つの極限段階の要素を、まず最小出現レベルで比較し、それが一致するときは共通の有限段階における最初の相違で比較する。残る目標は条件つきである。各有限段階の `before`{.Agda} 関係を所定の領域で表現する対象言語の論理式が与えられたと仮定し、`Described`{.Agda} の内部で集合
`codeOrder`{.Agda} を作る。そして `u` と `v` の順序対がこの集合に属することと`u ≺ˡ v` が成り立つことを同値にする。次章が必要な有限段階の論理式を与え、実際に使える実例を得る。
<!--/-->

```agda
open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )
```

<!--en-->
Bound variables are represented by de Bruijn positions. Opening two nested
binders therefore moves every position from the surrounding environment past
two new entries, and `sh2`{.Agda} records exactly this shift. It will be used
when earliest disagreement binds a candidate point and then a point below it,
and when the unequal-level branch binds the two level numerals. The shift
changes only how an existing free variable is addressed; it does not change the
set or relation denoted by that variable.
<!--zh-->
约束变元用 de Bruijn 位置表示。打开两个嵌套的绑定后，外围环境中的每个位置都要越过两个新条目，`sh2`{.Agda} 正好记录这次移位。最先分歧公式先绑定候选分歧点、再绑定其下的点时会用到它；不同层号分支绑定两个层号数码时也会用到它。移位只改变既有自由变元的寻址方式，不改变该变元所指称的集合或关系。
<!--ja-->
束縛変数は de Bruijn 位置で表される。二つの入れ子になった束縛を開くと、外側の環境にある各位置は二つの新しい項目を越える必要があり、`sh2`{.Agda} がその移動を正確に記録する。最初の相違を表す論理式が候補となる相違点と、その下にある点を順に束縛するとき、また異なるレベルの枝が二つのレベル数項を束縛するときに使う。この移動は既存の自由変数の参照位置だけを変え、その変数が指す集合や関係を変えない。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```

<!--en-->
An environment contains elements of the constructible carrier rather than bare
hierarchy sets. For a natural number `k`, `towerS k`{.Agda} therefore packages
the stage `Lset (# k)`{.Agda} with its constructibility evidence. The definition
is opaque so later proofs use its public projection equation instead of
expanding the hierarchy construction. This opacity controls reduction only; no
mathematical assumption is added.
<!--zh-->
环境包含的是可构造载体的元素，而不是未包装的层级集合。因此，对自然数 `k`，`towerS k`{.Agda} 把层 `Lset (# k)`{.Agda} 与其可构造性证据打包在一起。该定义保持不透明，使后续证明通过公开的投影等式使用它，而不展开层级构造。不透明性只控制归约，不会增加任何数学假设。
<!--ja-->
環境が含むのは、裸の階層集合ではなく構成可能な台の要素である。そこで自然数 `k` に対し、`towerS k`{.Agda} は段階 `Lset (# k)`{.Agda} とその構成可能性の証拠を包装する。定義は不透明なので、後の証明は階層の構成を展開せず、公開された射影等式を通して使う。この不透明性は簡約を制御するだけであり、数学的な仮定を加えない。
<!--/-->

```agda
opaque
  towerS : ℕ → S
  towerS k = LsetS (# k) (numeral-ord k)
```

<!--en-->
The equation `towerS-fst k`{.Agda} identifies the underlying set of this carrier
element with `Lset (# k)`{.Agda}. It is the transport point between two views of
the same stage: formulas receive the packaged element `towerS k`{.Agda}, while
the external level lemmas state membership in the underlying hierarchy set.
Later proofs cross this equation whenever they move a membership fact between
those views.
<!--zh-->
等式 `towerS-fst k`{.Agda} 把这个载体元素的底层集合认同为 `Lset (# k)`{.Agda}。它连接同一层的两种视角：公式接收包装后的元素 `towerS k`{.Agda}，外部层级引理则陈述底层层级集合中的隶属。后续证明在这两种视角之间运输成员事实时，都会经过这条等式。
<!--ja-->
等式 `towerS-fst k`{.Agda} は、この台の要素の基礎集合を `Lset (# k)`{.Agda} と同一視する。同じ段階に対する二つの見方を結ぶ点である。論理式は包装された要素
`towerS k`{.Agda} を受け取り、外側の階層の補題は基礎となる階層集合への所属を述べる。後の証明は、二つの見方の間で所属事実を運ぶたびにこの等式を通る。
<!--/-->

```agda
  towerS-fst : (k : ℕ) → fst (towerS k) ≡ Lset (# k)
  towerS-fst k = refl
```

<!--en-->
The index itself needs a separate carrier element. The value `numS k`{.Agda}
packages the numeral `# k`{.Agda} with evidence that it is constructible.
Keeping `numS k`{.Agda} distinct from `towerS k`{.Agda} prevents a common
confusion: the former denotes the ordinal index, while the latter denotes the
constructible stage indexed by it. `LevelAt`{.Agda} will relate these two
objects through the hierarchy-sequence description.
<!--zh-->
指标自身还需要一个单独的载体元素。`numS k`{.Agda} 把数码 `# k`{.Agda} 与其可构造性证据打包。把 `numS k`{.Agda} 与 `towerS k`{.Agda} 分开可避免一种常见混淆：前者指称序数指标，后者指称由它索引的可构造层。`LevelAt`{.Agda} 将通过层级序列的描述把这两个对象联系起来。
<!--ja-->
添字そのものにも別の台の要素が必要である。`numS k`{.Agda} は数項 `# k`{.Agda} と、それが構成可能であることの証拠を包装する。`numS k`{.Agda} と `towerS k`{.Agda} を区別することで、前者が順序数添字を指し、後者がその添字で指定される構成可能段階を指すという違いが明確になる。`LevelAt`{.Agda} は階層列の記述を通して、この二つの対象を結ぶ。
<!--/-->

```agda
  numS : ℕ → S
  numS k = # k , numL k
```

<!--en-->
The projection equation `numS-fst k`{.Agda} recovers `# k`{.Agda} from the
packaged numeral. Together with `towerS-fst k`{.Agda}, it lets the same natural
number be used coherently in both roles: as a level value in an environment and
as the index of the stage exhibited by a witness. These equations justify the
transports between object-language values and external facts about numerals and
stages.
<!--zh-->
投影等式 `numS-fst k`{.Agda} 从包装后的数码中恢复 `# k`{.Agda}。它与
`towerS-fst k`{.Agda} 配合，使同一个自然数能够协调地承担两种角色：一方面作为环境中的层号取值，另一方面作为见证所展示之层的指标。这两条等式为对象语言取值与外部的数码、层事实之间的运输提供依据。
<!--ja-->
射影等式 `numS-fst k`{.Agda} は、包装された数項から `# k`{.Agda} を取り出す。`towerS-fst k`{.Agda} と合わせることで、同じ自然数を二つの役割で整合的に使える。一方では環境におけるレベルの値であり、他方では証人が示す段階の添字である。これらの等式が、対象言語の値と、数項や段階についての外側の事実との間の輸送を正当化する。
<!--/-->

```agda
  numS-fst : (k : ℕ) → fst (numS k) ≡ # k
  numS-fst k = refl
```

<!--en-->
Suppose position `i` of an environment has underlying set `# j`{.Agda}.
The lemma `towerGraph`{.Agda} places `towerS j`{.Agda} in the fresh position
and proves that `LsetGraphAt`{.Agda} relates the two positions. Its content is
exactly the hierarchy-sequence specification: the value associated with the
numeral `# j`{.Agda} is the stage `Lset (# j)`{.Agda}. Thus the same lemma
supplies a genuine tower witness both for existence at the true level and for
testing minimality against that level.
<!--zh-->
设环境位置 `i` 的底层集合是 `# j`{.Agda}。引理 `towerGraph`{.Agda} 把
`towerS j`{.Agda} 放进新位置，并证明 `LsetGraphAt`{.Agda} 联系这两个位置。它的内容恰是层级序列的规格：与数码 `# j`{.Agda} 对应的取值是层 `Lset (# j)`{.Agda}。因此，同一条引理既为真实层号处的存在性提供塔见证，也为用该层检验最小性提供塔见证。
<!--ja-->
環境の位置 `i` の基礎集合が `# j`{.Agda} であるとする。補題 `towerGraph`{.Agda} は、新しい位置に `towerS j`{.Agda} を置き、`LsetGraphAt`{.Agda} が二つの位置を関係づけることを証明する。その内容は階層列の仕様そのものである。数項 `# j`{.Agda} に対応する値は段階 `Lset (# j)`{.Agda} である。したがって同じ補題が、真のレベルにおける存在と、そのレベルを用いた最小性の検証の双方に、実際の塔の証人を与える。
<!--/-->

```agda
towerGraph : ∀ {n} (j : ℕ) (δ : S ^ n) (i : Fin n) → fst (lookup i δ) ≡ # j
           → ⟨ (towerS j ∷ δ) ⊨ LsetGraphAt zero (suc i) ⟩
towerGraph j δ i q = Lset-defines zero (suc i) (towerS j ∷ δ)
  (subst IsOrd (sym q) (numeral-ord j))
  (towerS-fst j ∙ cong Lset (sym q))
```

<!--en-->
## The level, said inside
<!--zh-->
## 层号，在内部说出
<!--ja-->
## レベルを内部で述べる
<!--/-->

<!--en-->
The formula `LevelAt b x`{.Agda} begins the first key. It first requires the
value at `b` to belong to `ω`, so it can be decoded as a numeral. It then asks
for a value described by `LsetGraphAt`{.Agda} at that numeral and requires the
value at `x` to belong to the resulting stage. These clauses say that `b` is an
appearance stage for `x`; the remaining clause will make it the least one.
<!--zh-->
公式 `LevelAt b x`{.Agda} 开始刻画第一把键。它先要求位置 `b` 的取值属于 `ω`，因而可解码为数码；随后要求存在一个由 `LsetGraphAt`{.Agda} 在该数码处描述的取值，并要求位置 `x` 的取值属于所得的层。这些子句说明 `b` 是 `x` 的一个出现层；余下的子句将说明它还是最小的出现层。
<!--ja-->
論理式 `LevelAt b x`{.Agda} が第一の鍵の記述を始める。まず位置 `b` の値が `ω` に属することを要求するので、その値は数項として復号できる。次に、その数項において
`LsetGraphAt`{.Agda} が記述する値の存在を求め、位置 `x` の値が得られた段階に属することを要求する。これらの節により `b` は `x` の出現段階となり、残る節がそれを最小にする。
<!--/-->

```agda
LevelAt : ∀ {n} → Fin n → Fin n → Formula S n
LevelAt b x =
  (var b ∈̇ con ωʟ)
  ∧̇ ( ∃̇ ( LsetGraphAt zero (suc b) ∧̇ (var (suc x) ∈̇ var zero) )
    ∧̇ ∀̇∈ (var b) (∀̇ ( LsetGraphAt zero (suc zero)
```

<!--en-->
Minimality is expressed over every member `u` of the candidate numeral `b`,
not merely over its immediate predecessor. For every stage described at such a
`u`, the value at `x` must fail to belong to that stage. Since the members of
`# k`{.Agda} are precisely the smaller numerals, a candidate `b = # k`{.Agda}
therefore excludes all stages `0, …, k-1`. The two nested binders account for
the shifted occurrence of `x`. Semantically the universal clauses are function
types; the nearby propositionally truncated decoding of numeral membership is
used only with a propositional target and does not select a smaller index.
<!--zh-->
最小性遍及候选数码 `b` 的每个成员 `u`，而不只检查它的直接前驱。对每个在这样的`u` 处被描述出来的层，位置 `x` 的取值都不得属于该层。由于 `# k`{.Agda} 的成员恰是更小的数码，候选 `b = # k`{.Agda} 因而排除了从 `0` 到 `k-1` 的所有层。两个嵌套绑定解释了 `x` 的移位。语义上，这些全称子句是函数类型；附近对数码成员的命题截断解码只在命题目标下使用，并不会选定一个更小指标。
<!--ja-->
最小性は、候補となる数項 `b` の直前の要素だけでなく、すべての要素 `u` にわたって表される。そのような `u` で記述される各段階に、位置 `x` の値は属してはならない。`# k`{.Agda} の要素はちょうど小さい数項なので、候補 `b = # k`{.Agda} は `0` から`k-1` までのすべての段階を排除する。二つの入れ子の束縛が `x` の位置の移動を説明する。意味論上、これらの全称節は関数型である。近くにある数項所属の命題的に切り詰められた復号は、命題を目標とするときだけ使われ、小さい添字を一つ選び出すことはない。
<!--/-->

```agda
                     ⇒̇ ¬̇ (var (sh2 x) ∈̇ var zero) )) )
```

<!--en-->
To prove the two readings of `LevelAt`{.Agda}, fix a genuine limit-stage member
`a`, a natural number `k`, and an equation `qk : level a ≡ k` identifying `k`
with its least appearance level. The positive component of `levelData a`{.Agda},
transported along `qk`, gives `aIn`{.Agda}: the underlying set of `a` belongs to
`Lset (# k)`{.Agda}. The negative component says that membership in any
`Lset (# m)`{.Agda} with `m < k` is impossible. These are exactly the existence
and minimality facts needed to show that the formula recognizes the true level,
and later to prove that any level recognized by the formula equals `# k`{.Agda}.
<!--zh-->
为证明 `LevelAt`{.Agda} 的两个读法，固定一个真实的极限层成员 `a`、一个自然数 `k`，以及把 `k` 认同为其最小出现层号的等式 `qk : level a ≡ k`。把
`levelData a`{.Agda} 的正面分量沿 `qk` 运输，便得到 `aIn`{.Agda}：`a` 的底层集合属于 `Lset (# k)`{.Agda}。负面分量则说，对任何 `m < k`，它不可能属于
`Lset (# m)`{.Agda}。这恰是证明公式识别真实层号所需的存在性与最小性事实；随后还会用它们证明公式识别出的任何层号都等于 `# k`{.Agda}。
<!--ja-->
`LevelAt`{.Agda} の二つの読みを証明するため、実際の極限段階の要素 `a`、自然数 `k`、そして `k` をその最小出現レベルと同定する等式 `qk : level a ≡ k` を固定する。`levelData a`{.Agda} の正の成分を `qk` に沿って運ぶと `aIn`{.Agda} が得られる。これは `a` の基礎集合が `Lset (# k)`{.Agda} に属するという事実である。負の成分は、`m < k` である任意の `m` に対し、`Lset (# m)`{.Agda} への所属が不可能であることを述べる。これらは、論理式が真のレベルを認識するために必要な存在と最小性の事実であり、さらに論理式が認識したどのレベルも `# k`{.Agda} に等しいことを示すために使われる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Level (a : Limit) (k : ℕ) (qk : level a ≡ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    aIn : ⟨ fst a ∈ Lset (# k) ⟩
    aIn = subst (λ j → ⟨ fst a ∈ Lset (# j) ⟩) qk (level-in a)
```

<!--en-->
The second projection of `levelData a`{.Agda} supplies the minimality needed
throughout the argument. If the underlying set of `a` already belongs to
`Lset (# m)`{.Agda} and `m < k`, the equation `qk`{.Agda} turns this last
inequality into `m < level a`{.Agda}, contradicting that minimality. The
comparison expected by `levelData`{.Agda} lives one universe higher, so it is
wrapped with `lift`{.Agda}. This is only a universe-level adjustment; no
propositional truncation is involved.
<!--zh-->
`levelData a`{.Agda} 的第二个投影给出后续论证所需的最小性。若 `a` 的底层集合已经属于 `Lset (# m)`{.Agda}，且 `m < k`，等式 `qk`{.Agda}
就把后一条不等式化为 `m < level a`{.Agda}，与该最小性矛盾。`levelData`{.Agda} 所需的比较位于更高一层宇宙，因此这里用
`lift`{.Agda} 包装它。这只是宇宙层级的调整，不涉及命题截断。
<!--ja-->
`levelData a`{.Agda} の第二射影は、以下の議論で必要となる最小性を与える。`a` の基礎集合がすでに `Lset (# m)`{.Agda} に属し、しかも`m < k` なら、等式 `qk`{.Agda} によって後者は
`m < level a`{.Agda} に移され、この最小性に反する。`levelData`{.Agda} が要求する比較は一つ上の宇宙にあるので、ここでは
`lift`{.Agda} で包む。これは宇宙水準の調整にすぎず、命題的切り詰めとは関係ない。
<!--/-->

```agda
    aMin : (m : ℕ) → ⟨ fst a ∈ Lset (# m) ⟩ → m < k → ⊥₀
    aMin m h hm = levelData a .snd .snd m h
      (lift (subst (λ j → m < j) (sym qk) hm))
```

<!--en-->
The two readings of `LevelAt`{.Agda} are proved at arbitrary positions `b`
and `x` in an arbitrary environment. For the outward reading it is useful to
name the information hidden by the existential: a carrier element `c` that
satisfies the hierarchy graph at the value of `b`, together with a proof that
the value of `x` belongs to the underlying set of `c`. The private type
`Body`{.Agda} is exactly this witness data before propositional truncation.
<!--zh-->
`LevelAt`{.Agda} 的两条读式都在任意环境的任意位置 `b` 与 `x` 上证明。为了向外读取公式，先为存在量词所隐藏的信息命名会很方便：一个载体元素`c` 在 `b` 的值处满足层级图，并且 `x` 的值属于 `c` 的底层集合。私有类型
`Body`{.Agda} 恰好就是施加命题截断之前的这份见证数据。
<!--ja-->
`LevelAt`{.Agda} の二つの読みは、任意の環境にある任意の位置 `b` と`x` について証明される。外向きに論理式を読むためには、存在量化が隠している情報に名前を付けると便利である。それは、`b` の値において階層のグラフを満たす台の要素 `c` と、`x` の値が `c` の基礎集合に属するという証明である。私的な型 `Body`{.Agda} は、命題的切り詰めを施す前のこの証人データにほかならない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module _ {n : ℕ} (b x : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
    private
      Body : S → Type (ℓ-suc ℓ)
      Body c = ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
             × ⟨ fst (lookup x γ) ∈ fst c ⟩
```

<!--en-->
For the inward reading, suppose that `b` denotes the numeral `# k`{.Agda}
and `x` denotes the underlying set of `a`. The conclusion has the three
components of `LevelAt`{.Agda}: the value of `b` lies in `ω`, a hierarchy
value at `b` contains the value of `x`, and every hierarchy value indexed by
a member of `b` omits it. The proof names these components `hω`{.Agda},
`hex`{.Agda}, and `hmin`{.Agda} so that existence and minimality can be
established separately.
<!--zh-->
向内读取时，设 `b` 表示数码 `# k`{.Agda}，而 `x` 表示 `a` 的底层集合。结论包含 `LevelAt`{.Agda} 的三个部分：`b` 的值属于 `ω`；`b` 处有一个层级取值包含 `x` 的值；由 `b` 的成员所索引的每个层级取值都不包含它。证明把这三部分分别命名为 `hω`{.Agda}、`hex`{.Agda} 与 `hmin`{.Agda}，从而分开建立存在性与最小性。
<!--ja-->
内向きの読みでは、`b` が数項 `# k`{.Agda} を表し、`x` が `a` の基礎集合を表すと仮定する。結論は `LevelAt`{.Agda} の三つの成分からなる。`b` の値が `ω` に属すること、`b` における階層の値が `x` の値を含むこと、そして `b` の各要素が添字づける階層の値はそれを含まないことである。証明はこれらを `hω`{.Agda}、`hex`{.Agda}、`hmin`{.Agda} と名付け、存在性と最小性を分けて示す。
<!--/-->

```agda
    LevelAt-in : fst (lookup b γ) ≡ # k → fst (lookup x γ) ≡ fst a
               → ⟨ γ ⊨ LevelAt b x ⟩
    LevelAt-in qb qx = hω , (hex , hmin)
      where
      hω : ⟨ fst (lookup b γ) ∈ ω ⟩
```

<!--en-->
The first component follows from the elementary fact that every numeral
belongs to `ω`. The equation `qb`{.Agda} identifies the value stored at `b`
with `# k`{.Agda}; transporting `#∈ω k`{.Agda} along the symmetric direction
of that equation gives the required membership. This transport connects a
fact about the explicit numeral with the same fact about an environment
position.
<!--zh-->
第一部分来自每个数码都属于 `ω` 这一基本事实。等式 `qb`{.Agda} 把位置 `b`所存的值与 `# k`{.Agda} 认同；沿该等式的反向运输 `#∈ω k`{.Agda}，便得到所需的成员证明。这次运输把关于显式数码的事实接到关于环境位置的同一事实上。
<!--ja-->
第一の成分は、すべての数項が `ω` に属するという基本的事実から従う。等式 `qb`{.Agda} は位置 `b` に格納された値を `# k`{.Agda} と同一視する。そこで `#∈ω k`{.Agda} をこの等式の逆向きに運べば、必要な所属が得られる。この運搬は、明示された数項についての事実を、環境の位置についての同じ事実へ結び付ける。
<!--/-->

```agda
      hω = subst (λ u → ⟨ u ∈ ω ⟩) (sym qb) (#∈ω k)
```

<!--en-->
For the existential component, choose the packaged finite stage
`towerS k`{.Agda}. The lemma `towerGraph`{.Agda}, using `qb`{.Agda}, proves
that this witness is the hierarchy value at `b`. Its underlying set is
`Lset (# k)`{.Agda} by `towerS-fst k`{.Agda}, so the remaining obligation is
the known membership `aIn`{.Agda} after the endpoint is aligned by `qx`{.Agda}.
<!--zh-->
对于存在部分，取包装后的有穷层 `towerS k`{.Agda} 为见证。引理
`towerGraph`{.Agda} 借助 `qb`{.Agda} 证明这个见证就是 `b` 处的层级取值。由 `towerS-fst k`{.Agda}，其底层集合是 `Lset (# k)`{.Agda}，所以只需再用 `qx`{.Agda} 对齐端点，即可应用已知的成员事实 `aIn`{.Agda}。
<!--ja-->
存在の成分には、包装された有限段階 `towerS k`{.Agda} を証人として選ぶ。補題 `towerGraph`{.Agda} は `qb`{.Agda} を用いて、この証人が `b` における階層の値であることを示す。その基礎集合は `towerS-fst k`{.Agda} によって `Lset (# k)`{.Agda} なので、残る課題は `qx`{.Agda} で端点をそろえた後の既知の所属 `aIn`{.Agda} である。
<!--/-->

```agda
      hex : ⟨ γ ⊨ ∃̇ ( LsetGraphAt zero (suc b) ∧̇ (var (suc x) ∈̇ var zero) ) ⟩
      hex = ∣ towerS k , (towerGraph k γ b qb , hm) ∣₁
        where
        hm : ⟨ fst (lookup x γ) ∈ fst (towerS k) ⟩
        hm = subst (λ u → ⟨ fst (lookup x γ) ∈ u ⟩) (sym (towerS-fst k))
```

<!--en-->
The fact `aIn`{.Agda} already says that the underlying set of `a` belongs to
`Lset (# k)`{.Agda}. Transporting it along the symmetric direction of
`qx`{.Agda} changes the member from the underlying set of `a` to the value at
`x`. Combined with the preceding projection transport, this proves `hm`{.Agda}
and completes the existential witness under propositional truncation.
<!--zh-->
事实 `aIn`{.Agda} 已经说明 `a` 的底层集合属于 `Lset (# k)`{.Agda}。沿
`qx`{.Agda} 的反向运输，把其中的成员从 `a` 的底层集合改成 `x` 处的值。再与前面的投影运输合并，便证明了 `hm`{.Agda}，并在命题截断之下完成存在见证。
<!--ja-->
`aIn`{.Agda} はすでに、`a` の基礎集合が `Lset (# k)`{.Agda} に属することを述べている。これを `qx`{.Agda} の逆向きに運ぶと、所属する要素が `a` の基礎集合から `x` の位置の値へ変わる。先の射影に沿う運搬と合わせれば
`hm`{.Agda} が得られ、命題的切り詰めの中の存在証人が完成する。
<!--/-->

```agda
          (subst (λ u → ⟨ u ∈ Lset (# k) ⟩) (sym qx) aIn)
```

<!--en-->
The bounded universal expresses global minimality. Given `u` in the value of
`b`, a candidate `c` satisfying the hierarchy graph at `u`, and a supposed
membership of the value of `x` in `c`, the proof must derive a contradiction.
After `qb`{.Agda} rewrites `u` as a member of `# k`{.Agda},
`∈#-elim`{.Agda} says, under propositional truncation, that `u` is `# m` for
some `m < k`. The truncation may be eliminated because the target is the empty
type, hence a proposition. The resulting contradiction is lifted only to meet
the universe level of object-language negation.
<!--zh-->
这个有界全称表达全局最小性。给定 `b` 的值中的成员 `u`、一个在 `u` 处满足层级图的候选 `c`，以及一份声称 `x` 的值属于 `c` 的证明，目标是导出矛盾。用 `qb`{.Agda} 把 `u` 的成员身份改写到 `# k`{.Agda} 后，`∈#-elim`{.Agda} 在命题截断之下给出某个 `m < k`，使 `u` 等于 `# m`。由于目标是空类型，因而是命题，可以消去这个命题截断。所得矛盾只为匹配对象语言否定所在的宇宙层级而被抬升。
<!--ja-->
この有界全称は大域的な最小性を表す。`b` の値の要素 `u`、`u` において階層のグラフを満たす候補 `c`、および `x` の値が `c` に属するという仮定が与えられたとき、矛盾を導かなければならない。`qb`{.Agda} によって `u` の所属を `# k`{.Agda} への所属に書き換えると、`∈#-elim`{.Agda} は命題的切り詰めのもとで、ある `m < k` と `u = # m` を与える。目標は空の型で命題なので、この切り詰めは除去できる。得られた矛盾を持ち上げるのは、対象言語の否定が置かれた宇宙レベルに合わせるためだけである。
<!--/-->

```agda
      hmin : ⟨ γ ⊨ ∀̇∈ (var b) (∀̇ ( LsetGraphAt zero (suc zero)
                                  ⇒̇ ¬̇ (var (sh2 x) ∈̇ var zero) )) ⟩
      hmin u u∈ c hg hmem = lift (rec₁ isProp⊥ step
        (∈#-elim k (fst u) (subst (λ w → ⟨ fst u ∈ w ⟩) qb u∈)))
        where
```

<!--en-->
Fix an explicit decoding `m < k` and `fst u ≡ # m`{.Agda}. The graph proof
`hg`{.Agda} does more than certify that `c` is some possible witness:
`Lset-only`{.Agda}, supplied with the ordinal proof transported from the
numeral `# m`{.Agda}, identifies its underlying set with
`Lset (fst u)`{.Agda}. Thus the formula cannot hide an arbitrary set behind
its existential witness; the hierarchy graph determines the finite stage.
<!--zh-->
固定一次显式解码，得到 `m < k` 与 `fst u ≡ # m`{.Agda}。图证明
`hg`{.Agda} 不仅说明 `c` 是某个可能的见证；把数码 `# m`{.Agda} 的序数证明运输过去后，`Lset-only`{.Agda} 会把 `c` 的底层集合认同为
`Lset (fst u)`{.Agda}。因此，公式不能在存在见证后藏入任意集合，层级图会确定相应的有穷层。
<!--ja-->
明示的な復号として `m < k` と `fst u ≡ # m`{.Agda} を固定する。グラフの証明 `hg`{.Agda} は、`c` が何らかの候補であること以上を保証する。数項 `# m`{.Agda} の順序数性を運んで `Lset-only`{.Agda} に渡すと、`c` の基礎集合は `Lset (fst u)`{.Agda} と同一視される。したがって論理式は、存在証人の背後に任意の集合を隠すことはできない。階層のグラフが対応する有限段階を決定する。
<!--/-->

```agda
        step : Σ[ m ∈ ℕ ] ((m < k) × (fst u ≡ # m)) → ⊥₀
        step (m , (hm , qu)) = aMin m inStage hm
          where
          qc : fst c ≡ Lset (fst u)
          qc = Lset-only zero (suc zero) (c ∷ u ∷ γ) hg
```

<!--en-->
Now transport the alleged membership through the three identifications. First
`qc`{.Agda} places the value of `x` in `Lset (fst u)`{.Agda}; then
`qx`{.Agda} replaces that value by the underlying set of `a`; finally
`qu`{.Agda} replaces `fst u` by `# m`{.Agda}. The result is
`fst a ∈ Lset (# m)`{.Agda}, precisely the statement that `aMin`{.Agda}
rules out when `m < k`. Hence no finite stage indexed below `k` contains `a`.
<!--zh-->
现在沿三条认同运输那份假设的成员证明。先由 `qc`{.Agda} 把 `x` 的值放入
`Lset (fst u)`{.Agda}，再由 `qx`{.Agda} 把该值替换为 `a` 的底层集合，最后由 `qu`{.Agda} 把 `fst u` 替换为 `# m`{.Agda}。所得结论是
`fst a ∈ Lset (# m)`{.Agda}；当 `m < k` 时，这正是 `aMin`{.Agda} 所排除的陈述。因此，没有由小于 `k` 的数码索引的有穷层包含 `a`。
<!--ja-->
仮定された所属を三つの同一視に沿って運ぶ。まず `qc`{.Agda} により`x` の値を `Lset (fst u)`{.Agda} に入れ、次に `qx`{.Agda} によりその値を`a` の基礎集合へ置き換え、最後に `qu`{.Agda} により `fst u` を
`# m`{.Agda} へ置き換える。得られるのは
`fst a ∈ Lset (# m)`{.Agda} であり、`m < k` のもとで `aMin`{.Agda} がまさに排除する主張である。したがって `k` より小さい数項が添字づける有限段階には `a` は含まれない。
<!--/-->

```agda
            (subst IsOrd (sym qu) (numeral-ord m))
          inStage : ⟨ fst a ∈ Lset (# m) ⟩
          inStage = subst (λ w → ⟨ fst a ∈ Lset w ⟩) qu
            (subst (λ w → ⟨ w ∈ Lset (fst u) ⟩) qx
              (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) qc hmem))
```

<!--en-->
For the outward reading, assume `LevelAt b x`{.Agda} and continue to identify
the value of `x` with the underlying set of the fixed member `a`. The aim is
to prove that the candidate at `b` is the true numeral `# k`{.Agda}. Its
membership in `ω` reveals a natural-number index only under propositional
truncation. The target is an equality in the cumulative hierarchy, and
`setIsSet`{.Agda} shows that this equality type is a proposition, so the
truncated numeral data may be eliminated into it.
<!--zh-->
向外读取时，假设 `LevelAt b x`{.Agda} 成立，并仍把 `x` 的值认同为固定成员`a` 的底层集合。目标是证明 `b` 处的候选正是真实数码 `# k`{.Agda}。候选属于 `ω` 只能在命题截断之下揭示其自然数索引。目标是累积层级中的一条等式，而 `setIsSet`{.Agda} 表明这个等式类型是命题，因此可以把截断的数码数据消去到其中。
<!--ja-->
外向きの読みでは `LevelAt b x`{.Agda} を仮定し、引き続き `x` の値を固定した要素 `a` の基礎集合と同一視する。目標は、`b` にある候補が真の数項
`# k`{.Agda} であると示すことである。候補が `ω` に属することから自然数の添字が得られるのは、命題的切り詰めのもとでだけである。目標は累積階層における等式であり、`setIsSet`{.Agda} によってその等式型は命題だと分かるため、切り詰められた数項データをそこへ除去できる。
<!--/-->

```agda
    LevelAt-out : ⟨ γ ⊨ LevelAt b x ⟩ → fst (lookup x γ) ≡ fst a
                → fst (lookup b γ) ≡ # k
    LevelAt-out (hω , (hex , hmin)) qx =
      rec₁ (setIsSet (fst (lookup b γ)) (# k)) named hω
      where
```

<!--en-->
First exclude a decoded index `m` above the true level, so assume `k < m` and
that the value of `b` is `# m`{.Agda}. By `#mono`{.Agda}, `# k`{.Agda}
belongs to `# m`{.Agda}; the wrappers `numS k`{.Agda} and
`towerS k`{.Agda} therefore let the minimality clause of `LevelAt`{.Agda} be
tested at the genuine finite stage `Lset (# k)`{.Agda}. That clause says the
value of `x` is absent there, contradicting `aIn`{.Agda}. It returns a lifted
contradiction, and `lower`{.Agda} removes only this universe lift, an instance
of propositional resizing rather than propositional truncation.
<!--zh-->
先排除解码所得索引 `m` 高于真实层号的情形，即假设 `k < m`，且 `b` 的值是
`# m`{.Agda}。由 `#mono`{.Agda}，`# k`{.Agda} 属于 `# m`{.Agda}；于是包装
`numS k`{.Agda} 与 `towerS k`{.Agda} 让我们能在真正的有穷层
`Lset (# k)`{.Agda} 处使用 `LevelAt`{.Agda} 的最小性子句。该子句说 `x` 的值不在那里，与 `aIn`{.Agda} 矛盾。它返回抬升后的矛盾，`lower`{.Agda} 只移除这个宇宙抬升；这是命题换级，而不是命题截断。
<!--ja-->
まず、復号された添字 `m` が真のレベルより上にある場合を排除する。つまり`k < m` であり、`b` の値が `# m`{.Agda} だと仮定する。`#mono`{.Agda} により `# k`{.Agda} は `# m`{.Agda} に属するので、包装
`numS k`{.Agda} と `towerS k`{.Agda} を使えば、`LevelAt`{.Agda} の最小性の節を実際の有限段階 `Lset (# k)`{.Agda} で適用できる。この節は`x` の値がそこにないと述べるが、これは `aIn`{.Agda} と矛盾する。節が返す矛盾は持ち上げられており、`lower`{.Agda} はこの宇宙の持ち上げだけを除く。これは命題リサイズであって、命題的切り詰めではない。
<!--/-->

```agda
      notAbove : (m : ℕ) → fst (lookup b γ) ≡ # m → k < m → ⊥₀
      notAbove m qb hk = lower (hmin (numS k)
        (subst (λ w → ⟨ w ∈ fst (lookup b γ) ⟩) (sym (numS-fst k))
          (subst (λ w → ⟨ # k ∈ w ⟩) (sym qb) (#mono k m hk)))
        (towerS k) (towerGraph k (numS k ∷ γ) zero (numS-fst k))
```

<!--en-->
The last argument to that minimality clause is the positive membership it is
about to refute. Starting from `aIn`{.Agda}, the symmetric direction of
`qx`{.Agda} replaces the underlying set of `a` by the value of `x`, and the
symmetric direction of `towerS-fst k`{.Agda} replaces
`Lset (# k)`{.Agda} by the underlying set of its carrier wrapper. The formula
and the external minimal-level argument are thereby speaking about the same
member of the same finite stage.
<!--zh-->
传给该最小性子句的最后一个实参，正是它即将反驳的正面成员证明。从
`aIn`{.Agda} 出发，沿 `qx`{.Agda} 的反向把 `a` 的底层集合替换成 `x` 的值，再沿 `towerS-fst k`{.Agda} 的反向把 `Lset (# k)`{.Agda} 替换成其载体包装的底层集合。这样，公式与外部的最小层号论证便在谈论同一个有穷层中的同一个成员。
<!--ja-->
この最小性の節に渡す最後の引数は、まさにこれから反証される正の所属である。`aIn`{.Agda} から始め、`qx`{.Agda} の逆向きによって `a` の基礎集合を `x` の値へ置き換え、さらに `towerS-fst k`{.Agda} の逆向きによって
`Lset (# k)`{.Agda} をその台の包装の基礎集合へ置き換える。こうして論理式と外部の最小レベルの議論は、同じ有限段階の同じ要素について語る。
<!--/-->

```agda
        (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) (sym (towerS-fst k))
          (subst (λ w → ⟨ w ∈ Lset (# k) ⟩) (sym qx) aIn)))
```

<!--en-->
Next exclude a decoded index below the true level. If `m < k`, the existential
component of `LevelAt`{.Agda} supplies, under propositional truncation, a
carrier `c` that satisfies the hierarchy graph at `b` and contains the value
of `x`. This is exactly the data named by `Body`{.Agda}. Since the desired
result is a contradiction, the truncation may be eliminated into the empty
type; each explicit witness will force `a` to occur at stage `m`.
<!--zh-->
再排除解码所得索引低于真实层号的情形。若 `m < k`，`LevelAt`{.Agda} 的存在部分就在命题截断之下给出一个载体 `c`：它在 `b` 处满足层级图，并包含 `x` 的值。这恰是 `Body`{.Agda} 所命名的数据。由于目标是导出矛盾，可以把命题截断消去到空类型；每个显式见证都将迫使 `a` 已在第 `m` 个有穷层出现。
<!--ja-->
次に、復号された添字が真のレベルより下にある場合を排除する。`m < k` なら、`LevelAt`{.Agda} の存在成分は命題的切り詰めのもとで、`b` において階層のグラフを満たし、`x` の値を含む台の要素 `c` を与える。これは
`Body`{.Agda} と名付けたデータそのものである。目標は矛盾なので、切り詰めを空の型へ除去できる。明示された各証人は、`a` がすでに第 `m` 有限段階に現れることを強いる。
<!--/-->

```agda
      notBelow : (m : ℕ) → fst (lookup b γ) ≡ # m → m < k → ⊥₀
      notBelow m qb hm = rec₁ isProp⊥ atTower hex
        where
        atTower : Σ[ c ∈ S ] Body c → ⊥₀
        atTower (c , (hg , hmem)) = aMin m inStage hm
```

<!--en-->
For such a witness, `Lset-only`{.Agda} first identifies the underlying set of
`c` with the hierarchy stage indexed by the value of `b`. Its ordinal premise
comes from `numeral-ord m`{.Agda}, transported along the equation that the
value of `b` is `# m`{.Agda}. Composing the resulting equality with
`cong Lset qb`{.Agda} yields the concrete identification
`fst c ≡ Lset (# m)`{.Agda}.
<!--zh-->
对于这样的见证，`Lset-only`{.Agda} 先把 `c` 的底层集合认同为由 `b` 的值索引的层级阶段。它所需的序数前提来自 `numeral-ord m`{.Agda}，并沿「`b` 的值是 `# m`{.Agda}」这条等式运输。再把所得等式与 `cong Lset qb`{.Agda} 复合，便得到具体认同 `fst c ≡ Lset (# m)`{.Agda}。
<!--ja-->
この証人について、`Lset-only`{.Agda} はまず `c` の基礎集合を `b` の値が添字づける階層段階と同一視する。必要な順序数性は `numeral-ord m`{.Agda}
から得て、`b` の値が `# m`{.Agda} であるという等式に沿って運ぶ。得られた等式を `cong Lset qb`{.Agda} と合成すると、具体的な同一視
`fst c ≡ Lset (# m)`{.Agda} が得られる。
<!--/-->

```agda
          where
          qc : fst c ≡ Lset (# m)
          qc = Lset-only zero (suc b) (c ∷ γ) hg
                 (subst IsOrd (sym qb) (numeral-ord m))
             ∙ cong Lset qb
```

<!--en-->
The membership stored in the witness can now be read at the concrete finite
stage. Transport along `qc`{.Agda} turns it into membership of the value of
`x` in `Lset (# m)`{.Agda}, and transport along `qx`{.Agda} turns that value
into the underlying set of `a`. Thus `a` occurs at stage `m`; together with
`m < k`, this contradicts `aMin`{.Agda}. The candidate index is therefore not
below the true level.
<!--zh-->
现在可以在具体的有穷层读取见证中保存的成员事实。沿 `qc`{.Agda} 运输后，它变成 `x` 的值属于 `Lset (# m)`{.Agda}；再沿 `qx`{.Agda} 运输，该值变成 `a`的底层集合。因此 `a` 已在第 `m` 个有穷层出现；结合 `m < k`，这与
`aMin`{.Agda} 矛盾。故候选索引不可能低于真实层号。
<!--ja-->
証人に含まれる所属は、これで具体的な有限段階において読める。`qc`{.Agda} に沿って運ぶと `x` の値が `Lset (# m)`{.Agda} に属することになり、さらに `qx`{.Agda} に沿って運ぶとその値は `a` の基礎集合になる。したがって `a` は第 `m` 有限段階にすでに現れており、`m < k` と合わせると
`aMin`{.Agda} に反する。ゆえに候補の添字は真のレベルより下ではない。
<!--/-->

```agda
          inStage : ⟨ fst a ∈ Lset (# m) ⟩
          inStage = subst (λ w → ⟨ w ∈ Lset (# m) ⟩) qx
            (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) qc hmem)
```

<!--en-->
It remains to identify the numeral decoded from membership in `ω`. An explicit
decoded package contains `j : Lift ℕ` and an equality from `# (lower j)`{.Agda}
to the value at `b`. Reversing that equality gives `qb`{.Agda}. Once the
natural-number comparison proves `lower j ≡ k`{.Agda}, applying the numeral
map and composing equalities yields the required value
`fst (lookup b γ) ≡ # k`{.Agda}.
<!--zh-->
还需认同从 `ω` 的成员身份中解码出的数码。一份显式解码数据包含`j : Lift ℕ`，以及从 `# (lower j)`{.Agda} 到 `b` 处之值的等式。反转该等式便得到 `qb`{.Agda}。一旦自然数比较证明 `lower j ≡ k`{.Agda}，对这条等式应用数码映射并作复合，就得到所需结论 `fst (lookup b γ) ≡ # k`{.Agda}。
<!--ja-->
最後に、`ω` への所属から復号された数項を同定する。明示された復号データは`j : Lift ℕ` と、`# (lower j)`{.Agda} から `b` の値への等式を含む。その等式を逆にすると `qb`{.Agda} が得られる。自然数の比較から
`lower j ≡ k`{.Agda} が得られれば、それに数項写像を施して等式を合成することで、必要な `fst (lookup b γ) ≡ # k`{.Agda} に到達する。
<!--/-->

```agda
      named : Σ[ j ∈ Lift ℕ ] (# (lower j) ≡ fst (lookup b γ))
            → fst (lookup b γ) ≡ # k
      named (j , qj) = qb ∙ cong #_ (decide (lower j ≟ k))
        where
        qb : fst (lookup b γ) ≡ # (lower j)
```

<!--en-->
Trichotomy for natural numbers supplies exactly the required equality. The
case `lower j < k` contradicts `notBelow`{.Agda}, while the case
`k < lower j` contradicts `notAbove`{.Agda}; the equality case returns its
proof unchanged. Consequently the two readings are inverse at the level of
truth: the true least stage satisfies `LevelAt`{.Agda}, and any candidate
reported by that formula for the fixed member `a` must be its true level.
<!--zh-->
自然数的三歧性恰好给出所需等式。`lower j < k` 的情形与
`notBelow`{.Agda} 矛盾，`k < lower j` 的情形与 `notAbove`{.Agda} 矛盾；相等情形则原样返回其证明。因此，两条读式在真值层面互相对应：真实的最小有穷层满足 `LevelAt`{.Agda}，而该公式为固定成员 `a` 报告的任何候选都必是它的真实层号。
<!--ja-->
自然数の三分律が、必要な等式をちょうど与える。`lower j < k` の場合は
`notBelow`{.Agda} に反し、`k < lower j` の場合は `notAbove`{.Agda} に反し、等しい場合はその証明をそのまま返す。したがって二つの読みは真理値の水準で対応する。真の最小有限段階は `LevelAt`{.Agda} を満たし、この論理式が固定された要素 `a` について報告する候補は、その真のレベルでなければならない。
<!--/-->

```agda
        qb = sym qj
        decide : NatOrder.Trichotomy (lower j) k → lower j ≡ k
        decide (NatOrder.lt h) = ⊥₀-rec (notBelow (lower j) qb h)
        decide (NatOrder.eq e) = e
        decide (NatOrder.gt h) = ⊥₀-rec (notAbove (lower j) qb h)
```
</div>
</details>

</div>
</details>

<!--en-->
## The earliest disagreement, said inside
<!--zh-->
## 最先的分歧，在内部说出
<!--ja-->
## 最初の相違を内部で述べる
<!--/-->

<!--en-->
To compare sets by a formula, external members of a constructible carrier must
first be presented as elements of the semantic carrier `S`. If `A : S` and
`z` belongs to its underlying set, transitivity of constructibility turns the
certificate stored in `A` into a certificate that `z` is constructible.
`memS`{.Agda} packages `z` with this inherited proof. It constructs an element
of the dependent carrier, not a set-theoretic ordered pair.
<!--zh-->
要用公式比较集合，必须先把可构造载体的外部成员表示成语义载体 `S` 的元素。若 `A : S` 且 `z` 属于它的底层集合，可构造性的传递性就会把 `A` 中保存的证书化为 `z` 可构造的证书。`memS`{.Agda} 把 `z` 与这份继承来的证明包装起来。它构造的是依值载体的一个元素，不是集合论的有序对。
<!--ja-->
論理式で集合を比較するには、構成可能な台の外部の要素を、まず意味論的な台`S` の要素として提示しなければならない。`A : S` で、その基礎集合に `z`が属するなら、構成可能性の推移性により、`A` に格納された証明から `z` が構成可能であるという証明が得られる。`memS`{.Agda} は `z` をこの継承された証明とともに包装する。これは依存的な台の要素を作るのであって、集合論的な順序対を作るのではない。
<!--/-->

```agda
opaque
  memS : (A : S) (z : V ℓ) → ⟨ z ∈ fst A ⟩ → S
  memS A z h = z , isL-trans {x = fst A} {y = z} h (snd A)
```

<!--en-->
The projection equation `memS-fst`{.Agda} states that this packaging preserves
the set being discussed: the underlying set of `memS A z h`{.Agda} is `z`.
It holds by reflexivity, but exposing it as a lemma is what allows later
transports to pass between a quantified carrier element and the external set
it represents without unfolding the package.
<!--zh-->
投影等式 `memS-fst`{.Agda} 说明这次包装保留了正在讨论的集合：`memS A z h`{.Agda} 的底层集合就是 `z`。该等式由自反性成立，但把它显式写成引理后，后续运输便能在量化所得的载体元素与它所表示的外部集合之间往返，而无须展开包装。
<!--ja-->
射影等式 `memS-fst`{.Agda} は、この包装が議論中の集合を保つことを述べる。`memS A z h`{.Agda} の基礎集合は `z` である。この等式自体は反射性で成り立つが、補題として明示することで、後の運搬は包装を展開せずに、量化された台の要素とそれが表す外部の集合との間を行き来できる。
<!--/-->

```agda
  memS-fst : (A : S) (z : V ℓ) (h : ⟨ z ∈ fst A ⟩) → fst (memS A z h) ≡ z
  memS-fst A z h = refl
```

<!--en-->
`PrecedesAt`{.Agda} expresses one earliest-disagreement step relative to a
relation already stored at `r` and a carrier stored at `A`. For the sets at
`x` and `y`, it asks for a witness `z` in the carrier such that `z` belongs to
`y` but not to `x`. This orientation determines the comparison: at the
deciding point the right-hand set has membership value one and the left-hand
set has membership value zero, so `x` precedes `y`.
<!--zh-->
`PrecedesAt`{.Agda} 相对于已存于 `r` 的关系和已存于 `A` 的载体，表达一步最先分歧比较。对于 `x` 与 `y` 处的集合，它要求存在载体成员 `z`，使 `z` 属于`y` 而不属于 `x`。这个方向决定比较结果：在作出判定的点上，右侧集合的成员值为一，左侧集合的成员值为零，所以 `x` 先于 `y`。
<!--ja-->
`PrecedesAt`{.Agda} は、`r` に格納された関係と `A` に格納された台に相対して、最初の相違による比較の一段階を表す。`x` と `y` にある集合について、台の要素 `z` で、`y` には属するが `x` には属さないものを要求する。この向きが比較を決める。決定点では右側の集合の所属値が一、左側の集合の所属値が零なので、`x` が `y` に先立つ。
<!--/-->

```agda
PrecedesAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
PrecedesAt r A x y =
  ∃̇ ( (var zero ∈̇ var (suc A))
    ∧̇ ( (var zero ∈̇ var (suc y))
      ∧̇ ( ¬̇ (var zero ∈̇ var (suc x))
```

<!--en-->
The witness must also be the first disagreement according to the relation at
`r`. For every `w` in the carrier `A`, if that relation places `w` before
`z`, membership of `w` in `x` and in `y` must agree in both directions.
The formula consults the relation through `appAt`{.Agda}: semantically this
asks whether the set-theoretic pair of `w` and `z` belongs to the relation set
stored at `r`. The existential binder for `z` and the universal binder for
`w` account for the two-position shift applied to the older variables.
<!--zh-->
这个见证还必须是关系 `r` 所判定的最先分歧点。对载体 `A` 中的每个 `w`，若该关系把 `w` 排在 `z` 之前，则 `w` 属于 `x` 与属于 `y` 必须双向一致。公式通过 `appAt`{.Agda} 查阅关系；在语义上，这询问由 `w` 与 `z` 组成的集合论有序对是否属于存放在 `r` 的关系集。约束 `z` 的存在量词与约束 `w` 的全称量词，正好说明旧变量为何要移过两个位置。
<!--ja-->
この証人はさらに、`r` の関係が定める最初の相違でなければならない。台 `A`の各 `w` について、その関係が `w` を `z` より前に置くなら、`w` の `x` への所属と `y` への所属は両方向で一致しなければならない。論理式は
`appAt`{.Agda} を通して関係を調べる。意味論的には、`w` と `z` の集合論的な順序対が `r` に格納された関係集合に属するかを問うている。`z` を束縛する存在量化子と `w` を束縛する全称量化子が、以前の変項を二つずらす理由である。
<!--/-->

```agda
        ∧̇ ∀̇∈ (var (suc A))
             ( appAt (sh2 r) zero (suc zero)
             ⇒̇ ( ((var zero ∈̇ var (sh2 x)) ⇒̇ (var zero ∈̇ var (sh2 y)))
               ∧̇ ((var zero ∈̇ var (sh2 y)) ⇒̇ (var zero ∈̇ var (sh2 x))) ) ) ) ) )
```

<!--en-->
The module `Precedes`{.Agda} states precisely what is required to read this
formula. Besides the four positions and their environment, it fixes a
meta-level relation `R`{.Agda}. The law `Rrep`{.Agda} reads membership of a
set-theoretic pair in the relation set at `r` as an `R`{.Agda}-fact, while
`Rfill`{.Agda} writes such a fact back as membership. These laws need only
constructible endpoints because every quantified endpoint already lies in
`S`, and external carrier members can be wrapped by `memS`{.Agda}. No order
axiom for `R`{.Agda} is assumed: the formula represents the definition of one
comparison step independently of any later proof that a particular relation
is a well-order.
<!--zh-->
模块 `Precedes`{.Agda} 准确列出读取这条公式所需的数据。除四个位置及其环境外，它还固定一个元层关系 `R`{.Agda}。定律 `Rrep`{.Agda} 把集合论有序对属于 `r`处关系集的事实读成一个 `R`{.Agda} 事实，`Rfill`{.Agda} 则把这种事实写回成员关系。两条定律只需处理可构造端点，因为每个量化端点本来就在 `S` 中，而外部的载体成员可由 `memS`{.Agda} 包装。这里不假设 `R`{.Agda} 满足任何序公理；公式只表示一步比较的定义，不依赖后来对某个具体关系为良序的证明。
<!--ja-->
モジュール `Precedes`{.Agda} は、この論理式を読むために必要なデータを正確に述べる。四つの位置と環境に加えて、メタレベルの関係 `R`{.Agda} を固定する。法則 `Rrep`{.Agda} は `r` にある関係集合への集合論的な順序対の所属を
`R`{.Agda} の事実として読み、`Rfill`{.Agda} はその事実を所属へ書き戻す。これらの法則が構成可能な端点だけを扱えば十分なのは、量化された端点はすでに`S` に属し、外部の台の要素も `memS`{.Agda} で包装できるからである。ここでは
`R`{.Agda} に順序公理を仮定しない。この論理式は一段階の比較の定義を表すだけであり、特定の関係が整列順序であるという後の証明には依存しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Precedes {n : ℕ} (r A x y : Fin n) (γ : S ^ n)
                (R : V ℓ → V ℓ → hProp (ℓ-suc ℓ))
                (Rrep : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup r γ) ⟩
                      → ⟨ R (fst u) (fst v) ⟩)
                (Rfill : (u v : S) → ⟨ R (fst u) (fst v) ⟩
                       → ⟨ pr (fst u) (fst v) ∈ fst (lookup r γ) ⟩)
                where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Fix the carrier first. Every claim about a point earlier than the disagreement
is bounded by the constructible set denoted by the value at `A`, so the
comparison never ranges beyond the stage on which its base relation acts.
<!--zh-->
先固定载体。关于早于分歧点之元素的每个断言，都由环境中 `A` 处取值所指的可构造集合限定，因此比较不会越出基底关系所作用的那一层。
<!--ja-->
まず台を固定する。相違点より前の要素についての各主張は、環境の `A` にある値が表す構成可能集合に制限される。したがって、比較が基礎関係の働く段階の外へ出ることはない。
<!--/-->

```agda
  private
    Aʟ : S
    Aʟ = lookup A γ
```

<!--en-->
Write `xv` for the set denoted by the value at `x`. This lets the argument
state membership in the left set without repeating the environment lookup in
every clause.
<!--zh-->
用 `xv` 表示环境中 `x` 处取值所指的集合。这样便能直接陈述左侧集合中的隶属，而不必在每个子句中重复环境查找。
<!--ja-->
環境の `x` にある値が表す集合を `xv` と書く。これにより、各節で環境からの参照を繰り返さずに、左側の集合への所属を述べられる。
<!--/-->

```agda
    xv : V ℓ
    xv = fst (lookup x γ)
```

<!--en-->
Likewise, `yv` denotes the set given by the value at `y`. The order of these
two names matters because the first disagreement belongs to the right set and
fails to belong to the left one.
<!--zh-->
同样，`yv` 表示环境中 `y` 处取值所给的集合。这两个名称的次序很重要，因为首个分歧点属于右侧集合而不属于左侧集合。
<!--ja-->
同様に、`yv` は環境の `y` にある値が与える集合を表す。この二つの名前の順序は重要である。最初の相違点は右側の集合に属し、左側の集合には属さないからである。
<!--/-->

```agda
    yv : V ℓ
    yv = fst (lookup y γ)
```

<!--en-->
Before the first disagreement, the two sets must give the same membership answer. `Both w` records precisely this equivalence: membership of `w` in `xv` implies membership in `yv`, and conversely.
<!--zh-->
在首个分歧点之前，两个集合必须对隶属给出相同答案。`Both w` 精确记录这一等价：`w` 属于 `xv` 蕴含它属于 `yv`，反向亦然。
<!--ja-->
最初の相違点より前では、二つの集合は所属について同じ答えを与えなければならない。`Both w` はこの同値を正確に記録し、`w` の `xv` への所属から `yv` への所属を導き、その逆も導く。
<!--/-->

```agda
    Both : V ℓ → Type (ℓ-suc ℓ)
    Both w = (⟨ w ∈ xv ⟩ → ⟨ w ∈ yv ⟩) × (⟨ w ∈ yv ⟩ → ⟨ w ∈ xv ⟩)
```

<!--en-->
For a proposed disagreement witness `z`, `Agreeing z` examines every `w` in the carrier that the coded base relation places before `z`. The atom `appAt r w z` means that the relation set contains the ordered pair of `w` and `z`; under that premise, `xv` and `yv` must agree at `w`.
<!--zh-->
对候选分歧见证 `z`，`Agreeing z` 考察载体中被编码基底关系排在 `z` 之前的每个 `w`。原子 `appAt r w z` 表示关系集含有 `w` 与 `z` 的有序对；在此前提下，`xv` 与 `yv` 必须在 `w` 处一致。
<!--ja-->
相違の証人の候補 `z` に対して、`Agreeing z` は、符号化された基礎関係によって `z` より前に置かれる台の各要素 `w` を調べる。アトム `appAt r w z` は、関係集合が `w` と `z` の順序対を含むことを意味し、その仮定のもとで `xv` と `yv` は `w` において一致しなければならない。
<!--/-->

```agda
    Agreeing : S → Type (ℓ-suc ℓ)
    Agreeing z = (w : S) → ⟨ fst w ∈ fst Aʟ ⟩
               → ⟨ (w ∷ z ∷ γ) ⊨ appAt (sh2 r) zero (suc zero) ⟩
               → Both (fst w)
```

<!--en-->
The witness itself must lie in the carrier and in `yv`, while being absent from `xv`; all base-earlier carrier members must satisfy the agreement condition. Thus this orientation says that `xv` precedes `yv`. No order laws for the supplied base relation are assumed here, so calling the disagreement earliest is justified only when that relation really is an order.
<!--zh-->
见证本身必须属于载体和 `yv`，但不属于 `xv`；载体中每个按基底关系更早的成员都必须满足一致条件。因此这个方向表示 `xv` 先于 `yv`。这里并未假设所给基底关系满足任何序律，所以只有当该关系确实是序时，才能称此见证为「最早」分歧。
<!--ja-->
証人自身は台と `yv` に属し、`xv` には属さなければならない。また、基礎関係でそれより前にある台の要素はすべて一致条件を満たす。したがって、この向きは `xv` が `yv` に先行することを表す。ここでは与えられた基礎関係に順序法則を仮定していないため、「最初」という読みは、その関係が実際に順序である場合に限って正当化される。
<!--/-->

```agda
    Body : S → Type (ℓ-suc ℓ)
    Body z = ⟨ fst z ∈ fst Aʟ ⟩
           × ( ⟨ fst z ∈ yv ⟩
             × ( (⟨ fst z ∈ xv ⟩ → Lift {j = ℓ-suc ℓ} ⊥₀) × Agreeing z ) )
```

<!--en-->
To read the formula outward, eliminate its propositionally truncated existential into the proposition `precedes R A xv yv`. It is enough to transform each displayed model witness into a witness for the host-level definition, because the target retains only its propositional truncation.
<!--zh-->
要把公式向外读，就把它的命题截断存在消去到命题 `precedes R A xv yv`。只需把每个给出的模型见证变成宿主层定义的见证，因为目标也只保留其命题截断。
<!--ja-->
論理式を外へ読むには、その命題的に切り詰められた存在を命題 `precedes R A xv yv` へ消去する。示された各モデル内の証人をホスト側の定義の証人へ移せば十分である。目標もその命題的切り詰めだけを保持するからである。
<!--/-->

```agda
  PrecedesAt-out : ⟨ γ ⊨ PrecedesAt r A x y ⟩
                 → ⟨ precedes R (fst Aʟ) xv yv ⟩
  PrecedesAt-out = rec₁ squash₁ atZ
    where
    atZ : Σ[ z ∈ S ] Body z → ⟨ precedes R (fst Aʟ) xv yv ⟩
```

<!--en-->
The underlying set of `z` supplies the host witness, and the first three fields already give its carrier membership and the directed disagreement. The remaining task is to prove agreement at an arbitrary host-level `w` that lies before it.
<!--zh-->
`z` 的底层集给出宿主层见证，前三个分量已经给出它的载体隶属与有向分歧。剩下的任务是在任意宿主层元素 `w` 被排在它之前时证明两边一致。
<!--ja-->
`z` の底の集合がホスト側の証人となり、最初の三つの成分が台への所属と向きづけられた相違をすでに与える。残る課題は、それより前にある任意のホスト側の要素 `w` で両側が一致することを示すことである。
<!--/-->

```agda
    atZ (z , (z∈A , (z∈y , (z∉x , hag)))) =
      ∣ fst z , (z∈A , (z∈y , ((λ h → lower (z∉x h)) , ag))) ∣₁
      where
      ag : Agrees R (fst Aʟ) xv yv (fst z)
      ag w w∈A hR = subst Both (memS-fst Aʟ w w∈A) (hag wS w∈A' happ)
```

<!--en-->
Since `w` belongs to the constructible carrier, it inherits constructibility and can be packaged as a model element `wS`. Its projection equation transports the original carrier-membership proof to the form expected by the bounded object-language clause.
<!--zh-->
由于 `w` 属于可构造载体，它继承可构造性，因而可打包为模型元素 `wS`。其投影等式把原来的载体隶属证明搬运成对象语言有界子句所需的形式。
<!--ja-->
`w` は構成可能な台に属するので構成可能性を受け継ぎ、モデルの要素 `wS` としてまとめられる。その射影の等式に沿って、もとの台への所属の証明を、対象言語の有界な節が要求する形へ運ぶ。
<!--/-->

```agda
        where
        wS : S
        wS = memS Aʟ w w∈A
        w∈A' : ⟨ fst wS ∈ fst Aʟ ⟩
        w∈A' = subst (λ u → ⟨ u ∈ fst Aʟ ⟩) (sym (memS-fst Aʟ w w∈A)) w∈A
```

<!--en-->
The premise currently says `R w z` at the host level. After aligning `w` with `wS`, `Rfill` writes this fact as membership of the ordered pair in the relation set, exactly the information needed to establish the application atom.
<!--zh-->
当前前提在宿主层表示 `R w z`。把 `w` 与 `wS` 对齐后，`Rfill` 将这个事实写成有序对属于关系集，这恰是建立应用原子所需的信息。
<!--ja-->
いまの仮定はホスト側で `R w z` を述べている。`w` を `wS` とそろえた後、`Rfill` はこの事実を順序対の関係集合への所属として書き込む。これは適用アトムを示すために必要な情報そのものである。
<!--/-->

```agda
        hp : ⟨ pr (fst wS) (fst z) ∈ fst (lookup r γ) ⟩
        hp = Rfill wS z
          (subst (λ u → ⟨ R u (fst z) ⟩) (sym (memS-fst Aʟ w w∈A)) hR)
        happ : ⟨ (wS ∷ z ∷ γ) ⊨ appAt (sh2 r) zero (suc zero) ⟩
        happ = subst ⟨_⟩
```

<!--en-->
Adequacy for `appAt` converts that pair-membership statement into satisfaction in the environment extended by `wS` and `z`. The object-language agreement hypothesis can now be applied.
<!--zh-->
`appAt` 的充分性把这个有序对隶属陈述变成在由 `wS` 与 `z` 延拓的环境中的满足。现在即可应用对象语言中的一致假设。
<!--ja-->
`appAt` の妥当性により、この順序対の所属の主張は、`wS` と `z` で拡張した環境における充足へ変換される。これで対象言語の一致の仮定を適用できる。
<!--/-->

```agda
          (sym (appAt-adequate (sh2 r) zero (suc zero) (wS ∷ z ∷ γ))) hp
```

<!--en-->
The converse starts with the propositionally truncated witness in `precedes`. Because satisfaction of `PrecedesAt` is itself a proposition, the truncation may be eliminated while each host witness is converted into an object-language existential witness.
<!--zh-->
反向从 `precedes` 中的命题截断见证开始。由于 `PrecedesAt` 的满足本身是命题，可以消去该截断，并把每个宿主层见证转成对象语言的存在见证。
<!--ja-->
逆向きは、`precedes` にある命題的に切り詰められた証人から始まる。`PrecedesAt` の充足自体が命題なので、この切り詰めを消去し、各ホスト側の証人を対象言語の存在証人へ変換できる。
<!--/-->

```agda
  PrecedesAt-in : ⟨ precedes R (fst Aʟ) xv yv ⟩
                → ⟨ γ ⊨ PrecedesAt r A x y ⟩
  PrecedesAt-in = rec₁ squash₁ atZ
    where
    atZ : Σ[ z ∈ V ℓ ] Witness R (fst Aʟ) xv yv z
```

<!--en-->
Unpack a host witness `z` together with its carrier membership, its membership in the right set, its exclusion from the left set, and its earlier-point agreement. Its carrier membership makes `z` constructible, so `zS` can serve as the formula’s quantified witness.
<!--zh-->
展开宿主层见证 `z`，连同它的载体隶属、右侧隶属、左侧排除以及在更早点处的一致。它属于载体，因而具有可构造性，所以 `zS` 可以充当公式的量化见证。
<!--ja-->
ホスト側の証人 `z` を、台への所属、右側への所属、左側からの排除、より前の点での一致とともに取り出す。台への所属から `z` の構成可能性が得られるので、`zS` を論理式の量化された証人として使える。
<!--/-->

```agda
        → ⟨ γ ⊨ PrecedesAt r A x y ⟩
    atZ (z , (z∈A , (z∈y , (z∉x , ag)))) =
      ∣ zS , (z∈A' , (z∈y' , (z∉x' , hag))) ∣₁
      where
      zS : S
```

<!--en-->
The projection `fst zS` is equal to the original `z`. Transport along this equality shows that the packaged witness still belongs to the carrier, so packaging changes only its presentation and not its mathematical role.
<!--zh-->
投影 `fst zS` 等于原来的 `z`。沿此等式搬运可知，打包后的见证仍属于载体，所以打包只改变它的呈现，不改变其数学作用。
<!--ja-->
射影 `fst zS` はもとの `z` に等しい。この等式に沿って運ぶと、まとめられた証人も台に属することが分かる。したがって、まとめる操作は表示だけを変え、数学的な役割は変えない。
<!--/-->

```agda
      zS = memS Aʟ z z∈A
      qz : fst zS ≡ z
      qz = memS-fst Aʟ z z∈A
      z∈A' : ⟨ fst zS ∈ fst Aʟ ⟩
      z∈A' = subst (λ u → ⟨ u ∈ fst Aʟ ⟩) (sym qz) z∈A
```

<!--en-->
The same projection equation transports membership in `yv` and nonmembership in `xv`. It remains to translate the formula’s relation premise back to `R`, so that the host agreement hypothesis can be used.
<!--zh-->
同一投影等式也搬运 `yv` 中的隶属和 `xv` 中的非隶属。还需把公式中的关系前提读回 `R`，才能使用宿主层的一致假设。
<!--ja-->
同じ射影の等式に沿って、`yv` への所属と `xv` への非所属も運ぶ。あとは論理式の関係についての仮定を `R` へ読み戻せば、ホスト側の一致の仮定を使える。
<!--/-->

```agda
      z∈y' : ⟨ fst zS ∈ yv ⟩
      z∈y' = subst (λ u → ⟨ u ∈ yv ⟩) (sym qz) z∈y
      z∉x' : ⟨ fst zS ∈ xv ⟩ → Lift {j = ℓ-suc ℓ} ⊥₀
      z∉x' h = lift (z∉x (subst (λ u → ⟨ u ∈ xv ⟩) qz h))
      hag : Agreeing zS
```

<!--en-->
Given a model element `w` in the carrier, adequacy for `appAt` first reads satisfaction as membership of the pair of `w` and `zS` in the coded relation. This is the reverse passage from the one used in the outward proof.
<!--zh-->
给定载体中的模型元素 `w`，`appAt` 的充分性先把满足读成 `w` 与 `zS` 的有序对属于编码关系。这正是向外证明中所用转换的反向。
<!--ja-->
台に属するモデル要素 `w` が与えられると、`appAt` の妥当性はまず充足を、`w` と `zS` の順序対が符号化された関係に属するという主張へ読み替える。これは外向きの証明で用いた移行の逆向きである。
<!--/-->

```agda
      hag w w∈A happ = ag (fst w) w∈A hR
        where
        hp : ⟨ pr (fst w) (fst zS) ∈ fst (lookup r γ) ⟩
        hp = subst ⟨_⟩ (appAt-adequate (sh2 r) zero (suc zero) (w ∷ zS ∷ γ)) happ
        hR : ⟨ R (fst w) z ⟩
```

<!--en-->
Now `Rrep` reads relation-set membership back as `R (fst w) zS`; transporting the second endpoint from `fst zS` to `z` supplies the premise expected by the original agreement proof. The two membership implications in `Both` follow.
<!--zh-->
现在 `Rrep` 把关系集隶属读回 `R (fst w) zS`；再把第二个端点从 `fst zS` 搬运到 `z`，便得到原一致证明所需的前提，从而取得 `Both` 中的两条隶属蕴含。
<!--ja-->
ここで `Rrep` は関係集合への所属を `R (fst w) zS` として読み戻す。第二の端点を `fst zS` から `z` へ運ぶと、もとの一致の証明が要求する仮定が得られ、`Both` の二つの所属の含意が従う。
<!--/-->

```agda
        hR = subst (λ u → ⟨ R (fst w) u ⟩) qz (Rrep w zS hp)
```
</div>
</details>

<!--en-->
## The order, composed
<!--zh-->
## 那个序，接合起来
<!--ja-->
## 順序を合成する
<!--/-->

<!--en-->
An element `a : Limit` carries a proof that its underlying set belongs to `Lset ω`. Membership in this constructible stage yields the `isL` evidence needed to regard the same underlying set as an element of the model, called `limitEl a`.
<!--zh-->
元素 `a : Limit` 携带其底层集属于 `Lset ω` 的证明。属于这个可构造层便给出所需的 `isL` 证据，使同一个底层集可作为模型元素 `limitEl a`。
<!--ja-->
要素 `a : Limit` は、その底の集合が `Lset ω` に属するという証明を持つ。この構成可能な段階への所属から必要な `isL` の証拠が得られ、同じ底の集合をモデル要素 `limitEl a` とみなせる。
<!--/-->

```agda
opaque
  limitEl : Limit → S
  limitEl a = fst a , Lset→isL ω ω-ord (fst a) (snd a)
```

<!--en-->
Packaging does not alter the set: projecting `limitEl a` returns `fst a` by definition. This equation will later align model-built pairs with the ambient pairs used in the statement of representation.
<!--zh-->
打包并不改变集合：按定义投影 `limitEl a` 就得到 `fst a`。这个等式随后会把模型内构造的有序对与表示定理中使用的外围有序对对齐。
<!--ja-->
まとめる操作は集合を変えない。`limitEl a` を射影すると、定義により `fst a` が戻る。この等式は後で、モデル内で作った順序対を表現定理に現れる周囲の順序対とそろえる。
<!--/-->

```agda
  limitEl-fst : (a : Limit) → fst (limitEl a) ≡ fst a
  limitEl-fst a = refl
```

<!--en-->
To place a relation inside `L`, its related endpoints must be represented by an ordered pair that is itself a model element. `prS` supplies that internal pair for any two constructible endpoints.
<!--zh-->
要把一条关系放入 `L`，相关的两个端点必须由一个本身也是模型元素的有序对表示。`prS` 为任意两个可构造端点给出这个内部有序对。
<!--ja-->
関係を `L` の内部に置くには、関係する二つの端点を、それ自身がモデル要素である順序対で表さなければならない。`prS` は任意の二つの構成可能な端点に対して、その内部順序対を与える。
<!--/-->

```agda
  prS : S → S → S
  prS a b = prʟ a b
```

<!--en-->
The projection law for `prS` identifies its underlying set with the ambient ordered pair of the two underlying endpoints. Hence internal pair construction and external relation membership speak about the same set.
<!--zh-->
`prS` 的投影律把其底层集认同为两个底层端点的外围有序对。因此，内部配对构造与外部关系隶属谈论的是同一个集合。
<!--ja-->
`prS` の射影則は、その底の集合を二つの端点の底の集合からなる周囲の順序対と同一視する。したがって、内部の対構成と外部の関係への所属は同じ集合について述べている。
<!--/-->

```agda
  prS-fst : (a b : S) → fst (prS a b) ≡ pr (fst a) (fst b)
  prS-fst a b = prʟ-fst a b
```

<!--en-->
Before separation can select the ordered pairs satisfying the comparison, all candidate pairs need one set-sized bound. Present `Lset ω` by its small fiber of members, package each presented member as constructible, and index pairs by the product of those two small fibers.
<!--zh-->
在分离选出满足比较的有序对之前，所有候选对需要一个集合大小的共同界。先用小纤维呈现 `Lset ω` 的成员，把每个呈现出的成员打包为可构造元素，再用两个小纤维的积为有序对编索引。
<!--ja-->
分出によって比較を満たす順序対を選ぶ前に、候補となるすべての対を含む集合サイズの共通の上界が必要である。`Lset ω` の要素を小さなファイバーで表示し、各要素を構成可能なものとしてまとめ、その二つの小さなファイバーの積で順序対を添字づける。
<!--/-->

```agda
pairsBound : Σ[ D ∈ S ] ((u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst D ⟩)
pairsBound = d .fst , onPair
  where
  ixL : ⟪ Lset ω ⟫ → S
  ixL m = ⟪ Lset ω ⟫↪ m , Lset→isL ω ω-ord (⟪ Lset ω ⟫↪ m)
```

<!--en-->
Each presentation index really denotes a member of `Lset ω`. The membership bridge turns that presentation fact into ordinary membership, and membership in the stage supplies the constructibility proof used by the package `ixL`.
<!--zh-->
每个呈现索引确实指向 `Lset ω` 的一个成员。隶属桥把呈现事实变成通常的隶属，而属于该层又给出 `ixL` 打包所需的可构造性证明。
<!--ja-->
各表示添字は実際に `Lset ω` の要素を表す。所属の橋は表示についての事実を通常の所属へ変え、その段階への所属から `ixL` がまとめるために必要な構成可能性の証明が得られる。
<!--/-->

```agda
    (∈∈ₛ {a = ⟪ Lset ω ⟫↪ m} {b = Lset ω} .snd (∈ₛ⟪ Lset ω ⟫↪ m))
```

<!--en-->
Applying `smallDom` to this small product produces a constructible set containing every internally formed pair. It is only a common bound: it can contain additional objects, and the exact comparison relation will be obtained by separation inside it.
<!--zh-->
把 `smallDom` 用于这个小积，得到一个含有所有内部构造有序对的可构造集合。它只是共同界，可以含有额外对象；精确的比较关系要靠在其中施行分离获得。
<!--ja-->
この小さな積に `smallDom` を適用すると、内部で作られたすべての順序対を含む構成可能集合が得られる。これは共通の上界にすぎず、余分な対象を含んでもかまわない。正確な比較関係は、その中で分出を行うことによって得られる。
<!--/-->

```agda
  d : Σ[ D ∈ S ] ((p : ⟪ Lset ω ⟫ × ⟪ Lset ω ⟫)
                  → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
  d = smallDom (⟪ Lset ω ⟫ × ⟪ Lset ω ⟫) (λ p → prʟ (ixL (fst p)) (ixL (snd p)))
```

<!--en-->
For arbitrary `u,v : Limit`, their underlying sets have presentation indices in the small fiber of `Lset ω`. The pair at those indices belongs to the bound, and the projection equations transport that membership to the ambient pair `pr (fst u) (fst v)`.
<!--zh-->
对任意 `u,v : Limit`，它们的底层集在 `Lset ω` 的小纤维中都有呈现索引。由这些索引形成的有序对属于共同界，再沿投影等式搬运，就得到外围有序对 `pr (fst u) (fst v)` 的隶属。
<!--ja-->
任意の `u,v : Limit` に対し、それぞれの底の集合は `Lset ω` の小さなファイバー内に表示添字を持つ。その添字から作った順序対は共通の上界に属し、射影の等式に沿って運ぶことで、周囲の順序対 `pr (fst u) (fst v)` の所属が得られる。
<!--/-->

```agda
  onPair : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst (d .fst) ⟩
  onPair u v = subst (λ t → ⟨ t ∈ fst (d .fst) ⟩)
    (prʟ-fst (ixL (fu .fst)) (ixL (fv .fst)) ∙ cong₂ pr (fu .snd) (fv .snd))
    (d .snd (fu .fst , fv .fst))
    where
```

<!--en-->
The two fiber witnesses recover exactly the presentation indices used above, together with equations identifying their displayed members with `fst u` and `fst v`. These equations are why the small presentation suffices for every actual limit-stage endpoint.
<!--zh-->
两条纤维见证恰好恢复上面使用的呈现索引，并附带把所呈现成员分别认同为 `fst u` 与 `fst v` 的等式。正因这些等式，小呈现才足以覆盖每个实际的极限层端点。
<!--ja-->
二つのファイバーの証人は、上で使う表示添字と、そこで示される要素をそれぞれ `fst u`、`fst v` と同一視する等式を取り出す。この等式があるため、小さな表示で実際のすべての極限段階の端点を扱える。
<!--/-->

```agda
    fu = ∈-asFiber {a = fst u} {b = Lset ω} (snd u)
    fv = ∈-asFiber {a = fst v} {b = Lset ω} (snd v)
```

<!--en-->
Reading a formula can yield only the propositional truncation of a strict limit
comparison. `strictLimit` recovers the comparison by first consulting
trichotomy for the already proved strict well-order `limitOrder`; if
trichotomy gives `a ≺ˡ b`, there is nothing left to choose.
<!--zh-->
从公式读取时，有时只能得到极限严格比较的命题截断。`strictLimit` 先使用已经证明的严格良序 `limitOrder` 的三歧性来恢复比较；若三歧性给出 `a ≺ˡ b`，就无需再作任何选择。
<!--ja-->
論理式から読み取れるのが、極限上の狭義比較の命題的切り詰めだけである場合がある。`strictLimit` は、すでに証明された狭義整列順序 `limitOrder` の三分律を先に調べて比較を復元する。三分律が `a ≺ˡ b` を与える場合、選ぶべきものはもうない。
<!--/-->

```agda
strictLimit : (a b : Limit) → ∥ a ≺ˡ b ∥₁ → a ≺ˡ b
strictLimit a b h = decide (SWO.tri∙ limitOrder a b)
  where
  decide : Tri (a ≺ˡ b) (a ≡ b) (b ≺ˡ a) → a ≺ˡ b
  decide (lt k) = k
```

<!--en-->
The other two trichotomy cases are impossible under the truncated forward
comparison. If `a = b`, transport would give a self-comparison; if `b ≺ˡ a`,
transitivity with the hidden forward comparison would again give a
self-comparison. Irreflexivity refutes both propositions, so truncation is
eliminated only into contradiction.
<!--zh-->
在已有截断的正向比较时，三歧性的另外两种情形不可能成立。若 `a = b`，搬运会给出自比较；若 `b ≺ˡ a`，它与隐藏的正向比较经传递性也会给出自比较。非自反性反驳这两个命题，因此这里只把命题截断消去到矛盾中。
<!--ja-->
切り詰められた順向きの比較があるなら、三分律の残る二つの場合は不可能である。`a = b` なら、運ぶことで自己比較が得られる。`b ≺ˡ a` なら、隠された順向きの比較と推移性から再び自己比較が得られる。非反射性がどちらの命題も否定するため、命題的切り詰めは矛盾へだけ除去されている。
<!--/-->

```agda
  decide (eq q) = ⊥₀-rec (rec₁ isProp⊥
    (λ k → SWO.irr∙ limitOrder b (subst (λ t → t ≺ˡ b) q k)) h)
  decide (gt k) = ⊥₀-rec (rec₁ isProp⊥
    (λ j → SWO.irr∙ limitOrder a (SWO.trans∙ limitOrder a b a j k)) h)
```

<!--en-->
The defining property of `level a` places `fst a` in `finiteStage (level a)`. An equation `level a ≡ k` transports this membership to `finiteStage k`, providing exactly the stage boundary required when the finite comparison is invoked.
<!--zh-->
`level a` 的定义性质把 `fst a` 放在 `finiteStage (level a)` 中。等式 `level a ≡ k` 把这一隶属搬运到 `finiteStage k`，恰好给出调用有限层比较时所需的层边界。
<!--ja-->
`level a` の定義的性質により、`fst a` は `finiteStage (level a)` に属する。等式 `level a ≡ k` に沿ってこの所属を `finiteStage k` へ運ぶと、有限段階の比較を使う際に必要な段階の境界がちょうど得られる。
<!--/-->

```agda
levelStage : (a : Limit) (k : ℕ) → level a ≡ k → ⟨ fst a ∈ finiteStage k ⟩
levelStage a k q = subst (λ j → ⟨ fst a ∈ Lset (# j) ⟩) q (level-in a)
```

<!--en-->
`Described` is a conditional framework. It accepts a formula `BeforeAt`
intended to describe `before m`, together with an inward direction that may be
used only when the value at `b` denotes `# m` and the first endpoint lies in
`finiteStage m`.
<!--zh-->
`Described` 是一个条件式框架。它接收一条用来描述 `before m` 的公式 `BeforeAt`，以及一个向内方向；只有当 `b` 处的取值表示 `# m`，且第一个端点属于 `finiteStage m` 时，才能使用这个方向。
<!--ja-->
`Described` は条件つきの枠組みである。`before m` を記述するための論理式 `BeforeAt` と内向きの規則を受け取る。この規則を使えるのは、`b` にある値が `# m` を表し、第一の端点が `finiteStage m` に属する場合に限られる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Described
  (BeforeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (BeforeAt-in : ∀ {n} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
               → fst (lookup b γ) ≡ # m
               → ⟨ fst (lookup x γ) ∈ finiteStage m ⟩
               → ⟨ fst (lookup y γ) ∈ finiteStage m ⟩
               → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
               → ⟨ γ ⊨ BeforeAt b x y ⟩)
  (BeforeAt-out : ∀ {n} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
                → fst (lookup b γ) ≡ # m
                → ⟨ fst (lookup x γ) ∈ finiteStage m ⟩
                → ⟨ fst (lookup y γ) ∈ finiteStage m ⟩
                → ⟨ γ ⊨ BeforeAt b x y ⟩
                → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩)
  where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The inward hypothesis also requires the second endpoint to lie in the same finite stage and requires the actual comparison `before m x y`; from these data it produces satisfaction of `BeforeAt`. Thus the framework does not construct a finite-stage relation or infer its order laws.
<!--zh-->
向内假设还要求第二个端点属于同一有限层，并要求实际比较 `before m x y`；由这些数据，它产出 `BeforeAt` 的满足。因此，这个框架既不构造有限层关系，也不推出它的序律。
<!--ja-->
内向きの仮定は、第二の端点も同じ有限段階に属することと、実際の比較 `before m x y` が成り立つことをさらに要求し、そこから `BeforeAt` の充足を与える。したがって、この枠組みは有限段階の関係を構成せず、その順序法則も導かない。
<!--/-->

<!--en-->
The outward hypothesis has the same numeral and stage boundaries and reads satisfaction back as `before m x y`. Only a formula satisfying both directions can instantiate the framework; the actual `BeforeAt` and hence the resulting `codeOrder` are supplied by `EarliestDisagreement`, not unconditionally at this point.
<!--zh-->
向外假设具有相同的数码与层边界，并把满足读回 `before m x y`。只有同时满足两个方向的公式才能实例化这个框架；实际的 `BeforeAt` 以及由此得到的 `codeOrder` 由 `EarliestDisagreement` 提供，此处并没有无条件得到它们。
<!--ja-->
外向きの仮定も同じ数項と段階の境界を持ち、充足を `before m x y` として読み戻す。両方向を満たす論理式だけがこの枠組みを具体化できる。実際の `BeforeAt` と、そこから得られる `codeOrder` は `EarliestDisagreement` によって与えられ、この時点で無条件に得られるものではない。
<!--/-->

<!--en-->
The first branch of `LimitOrdAt` handles unequal levels. It binds two candidate numerals, proves separately that they are the least levels of `x` and `y`, and requires the numeral for `x` to be a member of the numeral for `y`, which expresses strict inequality of natural-number levels.
<!--zh-->
`LimitOrdAt` 的第一支处理层号不等的情形。它绑定两个候选数码，分别证明它们是 `x` 与 `y` 的最小层号，并要求 `x` 的数码属于 `y` 的数码，从而表达自然数层号的严格不等。
<!--ja-->
`LimitOrdAt` の第一の枝は、レベルが異なる場合を扱う。二つの数項候補を束縛し、それぞれが `x` と `y` の最小レベルであることを示したうえで、`x` の数項が `y` の数項に属することを要求する。これは自然数としてのレベルの狭義不等式を表す。
<!--/-->

```agda
  opaque
    LimitOrdAt : ∀ {n} → Fin n → Fin n → Formula S n
    LimitOrdAt x y =
      ∃̇ ( ∃̇ ( LevelAt (suc zero) (sh2 x)
             ∧̇ ( LevelAt zero (sh2 y) ∧̇ (var (suc zero) ∈̇ var zero) ) ) )
```

<!--en-->
The second branch handles equal levels by binding one common numeral. Both `LevelAt` clauses identify that same numeral as the least level, after which the assumed `BeforeAt` compares the endpoints inside that finite stage. Sharing one witness expresses equality without adding a separate object-language equality.
<!--zh-->
第二支用一个共同数码处理层号相等的情形。两个 `LevelAt` 子句都把同一数码认作最小层号，然后由假设的 `BeforeAt` 在该有限层内比较两个端点。共享一个见证便表达了相等，无须另加对象语言等式。
<!--ja-->
第二の枝は、一つの共通の数項を束縛してレベルが等しい場合を扱う。二つの `LevelAt` の節が同じ数項を最小レベルとして特定し、その後、仮定された `BeforeAt` がその有限段階の内部で端点を比較する。一つの証人を共有することで、対象言語の等号を別に加えずに等しさを表せる。
<!--/-->

```agda
      ∨̇ ∃̇ ( LevelAt zero (suc x)
           ∧̇ ( LevelAt zero (suc y) ∧̇ BeforeAt zero (suc x) (suc y) ) )
```

<!--en-->
To prove adequacy of this formula, fix the two positions `x` and `y` in the
environment and identify their values with actual `u,v : Limit`. Explicit
indices `ku,kv` and equations to the true levels allow the proof to move
cleanly between natural-number comparisons, numeral membership, and stage
membership.
<!--zh-->
为证明这条公式的充分性，先固定环境中的两个位置 `x` 与 `y`，并把其取值分别认同为实际的 `u,v : Limit`。显式指数 `ku,kv` 及其与真实层号的等式，使证明能在自然数比较、数码隶属与层隶属之间清楚转换。
<!--ja-->
この論理式の妥当性を示すため、環境の二つの位置 `x` と `y` を固定し、その値を実際の `u,v : Limit` と同一視する。明示された添字 `ku,kv` と真のレベルとの等式により、自然数の比較、数項の所属、段階への所属の間を明確に移れる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Order {n : ℕ} (x y : Fin n) (γ : S ^ n)
               (u v : Limit) (ku kv : ℕ)
               (qu : level u ≡ ku) (qv : level v ≡ kv)
               (qx : fst (lookup x γ) ≡ fst u)
               (qy : fst (lookup y γ) ≡ fst v)
               where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The two `Level` instances provide more than convenient names: each one supplies the verified reading of `LevelAt` for the corresponding actual endpoint and its least level. They are the bridge that rules out spurious numeral witnesses in the outward direction.
<!--zh-->
两个 `Level` 实例不只是提供方便的名称：每个实例都为相应的实际端点及其最小层号给出 `LevelAt` 的已验证读法。向外读取时，正是这座桥排除了伪造的数码见证。
<!--ja-->
二つの `Level` の具体例は、単に便利な名前を与えるだけではない。それぞれが、対応する実際の端点とその最小レベルについて、`LevelAt` の検証済みの読みを与える。外向きに読むとき、この橋によって見かけだけの数項証人が排除される。
<!--/-->

```agda
    private module Lu = Level u ku qu
    private module Lv = Level v kv qv
```

<!--en-->
`Split c d` is the semantic content of the unequal-level branch. It says that `c` is the least-level numeral for the left endpoint, `d` is the least-level numeral for the right endpoint, and `c ∈ d`; the last clause fixes the direction as left level smaller than right level.
<!--zh-->
`Split c d` 是层号不等分支的语义内容。它表示 `c` 是左端点的最小层数码，`d` 是右端点的最小层数码，并且 `c ∈ d`；最后一项把方向固定为左侧层号小于右侧层号。
<!--ja-->
`Split c d` はレベルが異なる枝の意味内容である。`c` が左端点の最小レベルの数項、`d` が右端点の最小レベルの数項であり、さらに `c ∈ d` が成り立つことを述べる。最後の条件によって、左のレベルが右のレベルより小さいという向きが定まる。
<!--/-->

```agda
    private
      Split : S → S → Type (ℓ-suc ℓ)
      Split c d = ⟨ (d ∷ c ∷ γ) ⊨ LevelAt (suc zero) (sh2 x) ⟩
                × ( ⟨ (d ∷ c ∷ γ) ⊨ LevelAt zero (sh2 y) ⟩
                  × ⟨ fst c ∈ fst d ⟩ )
```

<!--en-->
`Same c` is the semantic content of the equal-level branch. The same `c` must describe the least level of both endpoints, and only then may `BeforeAt c x y` supply their comparison within that common finite stage.
<!--zh-->
`Same c` 是层号相等分支的语义内容。同一个 `c` 必须描述两个端点的最小层号，只有随后才能由 `BeforeAt c x y` 给出它们在该共同有限层内的比较。
<!--ja-->
`Same c` はレベルが等しい枝の意味内容である。同じ `c` が両方の端点の最小レベルを記述しなければならず、その後に限って `BeforeAt c x y` が共通の有限段階内での比較を与える。
<!--/-->

```agda
      Same : S → Type (ℓ-suc ℓ)
      Same c = ⟨ (c ∷ γ) ⊨ LevelAt zero (suc x) ⟩
             × ( ⟨ (c ∷ γ) ⊨ LevelAt zero (suc y) ⟩
               × ⟨ (c ∷ γ) ⊨ BeforeAt zero (suc x) (suc y) ⟩ )
```

<!--en-->
Suppose `ku < kv`. Choose the genuine numerals `# ku` and `# kv`, packaged as model elements, for the two existential witnesses. The two `LevelAt-in` results verify that these numerals describe the actual least levels of the aligned endpoints.
<!--zh-->
设 `ku < kv`。选择打包为模型元素的真实数码 `# ku` 与 `# kv` 作为两个存在见证。两次 `LevelAt-in` 验证这些数码确实描述了已对齐端点的实际最小层号。
<!--ja-->
`ku < kv` と仮定する。二つの存在証人には、モデル要素としてまとめた真の数項 `# ku` と `# kv` を選ぶ。二つの `LevelAt-in` によって、これらの数項が、そろえられた端点の実際の最小レベルを記述することが確かめられる。
<!--/-->

```agda
      split-in : ku < kv → Split (numS ku) (numS kv)
      split-in hlt =
          Lu.LevelAt-in (suc zero) (sh2 x) (numS kv ∷ numS ku ∷ γ)
            (numS-fst ku) qx
        , ( Lv.LevelAt-in zero (sh2 y) (numS kv ∷ numS ku ∷ γ)
```

<!--en-->
Strict inequality of natural numbers gives `# ku ∈ # kv` by numeral monotonicity. Transporting along the projection equations of the two packaged numerals supplies the membership `fst (numS ku) ∈ fst (numS kv)` required by `Split`.
<!--zh-->
自然数的严格不等经数码单调性给出 `# ku ∈ # kv`。沿两个打包数码的投影等式搬运，就得到 `Split` 所需的隶属 `fst (numS ku) ∈ fst (numS kv)`。
<!--ja-->
自然数の狭義不等式から、数項の単調性により `# ku ∈ # kv` が得られる。二つのまとめられた数項の射影等式に沿って運ぶと、`Split` が要求する所属 `fst (numS ku) ∈ fst (numS kv)` が得られる。
<!--/-->

```agda
              (numS-fst kv) qy
          , subst2 (λ s t → ⟨ s ∈ t ⟩) (sym (numS-fst ku)) (sym (numS-fst kv))
              (#mono ku kv hlt) )
```

<!--en-->
For the equal-level branch, an equation `level v ≡ level u` lets the one numeral `# ku` describe both endpoints. The left `LevelAt` reading uses `qu` directly, while the right reading uses the equality to express the level of `v` by the same index `ku`.
<!--zh-->
在同层分支中，等式 `level v ≡ level u` 使同一个数码 `# ku` 能描述两个端点。左侧的 `LevelAt` 读法直接使用 `qu`，右侧则利用该等式把 `v` 的层号也表示为同一指数 `ku`。
<!--ja-->
同じレベルの枝では、等式 `level v ≡ level u` により、一つの数項 `# ku` で両方の端点を記述できる。左側の `LevelAt` の読みは `qu` を直接使い、右側の読みはこの等式を使って `v` のレベルも同じ添字 `ku` で表す。
<!--/-->

```agda
      same-in : (e : level v ≡ level u)
              → ⟨ before (level u) (fst u) (fst v) ⟩ → Same (numS ku)
      same-in e h =
          Lu.LevelAt-in zero (suc x) (numS ku ∷ γ) (numS-fst ku) qx
        , ( Level.LevelAt-in v ku (e ∙ qu) zero (suc y) (numS ku ∷ γ)
```

<!--en-->
The conditional hypothesis `BeforeAt-in` may be used only after its boundaries
are established. The level equations place both looked-up endpoints in
`finiteStage ku`, while the projection equation for `numS ku` shows that the
common value supplied for the numeral really denotes `# ku`.
<!--zh-->
只有先建立所需边界，才能使用条件式假设 `BeforeAt-in`。层号等式把查得的两个端点都放入 `finiteStage ku`，而 `numS ku` 的投影等式表明作为共同数码给出的取值确实表示 `# ku`。
<!--ja-->
条件つきの仮定 `BeforeAt-in` を使えるのは、必要な境界を先に示した後だけである。レベルの等式によって参照された二つの端点はどちらも `finiteStage ku` に置かれ、`numS ku` の射影等式によって、共通の数項として与えた値が確かに `# ku` を表すことが分かる。
<!--/-->

```agda
              (numS-fst ku) qy
          , BeforeAt-in zero (suc x) (suc y) (numS ku ∷ γ) ku (numS-fst ku)
              (subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qx)
                (levelStage u ku qu))
              (subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qy)
```

<!--en-->
Finally, transport the given comparison from index `level u` to `ku` and align its two endpoints with the environment values. Together with the two stage-membership proofs, this satisfies every premise of `BeforeAt-in` and completes `Same (numS ku)`.
<!--zh-->
最后，把给定比较从指数 `level u` 搬运到 `ku`，并把它的两个端点与环境中的值对齐。连同两条层隶属证明，这满足 `BeforeAt-in` 的全部前提，从而完成 `Same (numS ku)`。
<!--ja-->
最後に、与えられた比較を添字 `level u` から `ku` へ運び、その二つの端点を環境の値とそろえる。二つの段階への所属の証明と合わせると、`BeforeAt-in` のすべての仮定が満たされ、`Same (numS ku)` が完成する。
<!--/-->

```agda
                (levelStage v ku (e ∙ qu)))
              (subst2 (λ s t → ⟨ before ku s t ⟩) (sym qx) (sym qy)
                (subst (λ j → ⟨ before j (fst u) (fst v) ⟩) qu h)) )
```

<!--en-->
Reading a `Split c d` outward first identifies `c` with `# ku` and `d` with `# kv` by the two `LevelAt-out` lemmas. After transporting `c ∈ d` along those identifications, numeral membership eliminates to `ku < kv`, and the stored level equations turn this into `level u < level v`.
<!--zh-->
向外读取 `Split c d` 时，先由两条 `LevelAt-out` 引理把 `c` 认同为 `# ku`、把 `d` 认同为 `# kv`。沿这些认同搬运 `c ∈ d` 后，消去数码隶属便得到 `ku < kv`，再由保存的层号等式转成 `level u < level v`。
<!--ja-->
`Split c d` を外へ読むとき、まず二つの `LevelAt-out` の補題によって `c` を `# ku`、`d` を `# kv` と同一視する。これらの同一視に沿って `c ∈ d` を運び、数項の所属を消去すると `ku < kv` が得られる。保存されたレベルの等式により、これは `level u < level v` へ変わる。
<!--/-->

```agda
      split-out : (c d : S) → Split c d → level u < level v
      split-out c d (hx , (hy , hlt)) = subst2 _<_ (sym qu) (sym qv)
        (#∈#-elim ku kv (subst2 (λ s t → ⟨ s ∈ t ⟩) qc qd hlt))
        where
        qc : fst c ≡ # ku
```

<!--en-->
Each numeral identification is obtained in the correct extended environment: the first `LevelAt` refers past both new witnesses to `x`, while the second refers to `y`. This binder alignment ensures that the final inequality compares the true levels of the original two endpoints rather than the witnesses themselves.
<!--zh-->
每个数码认同都在正确的延拓环境中取得：第一条 `LevelAt` 越过两个新见证指向 `x`，第二条则指向 `y`。这种绑定者对齐保证最终比较的是原来两个端点的真实层号，而不是见证本身。
<!--ja-->
それぞれの数項の同一視は、正しく拡張された環境で得られる。第一の `LevelAt` は二つの新しい証人を越えて `x` を参照し、第二の `LevelAt` は `y` を参照する。この束縛子の整合により、最後の不等式が証人自身ではなく、もとの二つの端点の真のレベルを比較していることが保証される。
<!--/-->

```agda
        qc = Lu.LevelAt-out (suc zero) (sh2 x) (d ∷ c ∷ γ) hx qx
        qd : fst d ≡ # kv
        qd = Lv.LevelAt-out zero (sh2 y) (d ∷ c ∷ γ) hy qy
```

<!--en-->
In the common-level branch, one model element `c` serves as the proposed level numeral for both `u` and `v`. Reading its two `LevelAt` certificates therefore has two consequences: the actual levels must agree, and the assumed finite-stage formula can be read as the comparison of `u` with `v` at that common level.
<!--zh-->
在同层支中，同一个模型元素 `c` 同时充当 `u` 与 `v` 的候选层号数码。读取它的两份 `LevelAt` 证书会得到两个结论：双方的真实层号必定相等，而给定的有穷层公式也可以读成公共层内 `u` 在 `v` 之前。
<!--ja-->
同じ段階の枝では、一つのモデル要素 `c` が `u` と `v` の双方に対する候補の段階番号を表す。二つの `LevelAt` の証明を読み取ると、実際の段階番号が一致することと、与えられた有限段階の論理式がその共通段階での `u` と `v` の比較を表すことが得られる。
<!--/-->

```agda
      same-out : (c : S) → Same c
               → (level v ≡ level u) × ⟨ before (level u) (fst u) (fst v) ⟩
      same-out c (hx , (hy , hb)) = e , below
        where
        qc : fst c ≡ # ku
```

<!--en-->
The first certificate identifies the underlying set of `c` with `# ku`, while the second identifies it with `# kv`. Injectivity of numeral coding then gives `ku = kv`; composing this equality with the equations that define `ku` and `kv` yields `level v = level u`. Thus level equality is recovered from the shared witness rather than asserted inside the object-language formula.
<!--zh-->
第一份证书把 `c` 的底层集合认作数码 `# ku`，第二份则把它认作 `# kv`。数码编码的单射性于是给出 `ku = kv`；再与定义 `ku`、`kv` 的层号等式复合，便得到 `level v = level u`。因此，层号相等是从共同见证中恢复的，并未作为等式写进对象语言公式。
<!--ja-->
一つ目の証明は `c` の台となる集合を数項 `# ku` と同定し、二つ目はそれを `# kv` と同定する。数項符号化の単射性から `ku = kv` が従い、これを `ku` と `kv` を定める段階番号の等式と合成すると `level v = level u` が得られる。したがって、段階番号の一致は対象言語の論理式に等式として書かれるのではなく、共通の証人から復元される。
<!--/-->

```agda
        qc = Lu.LevelAt-out zero (suc x) (c ∷ γ) hx qx
        qc' : fst c ≡ # kv
        qc' = Lv.LevelAt-out zero (suc y) (c ∷ γ) hy qy
        e : level v ≡ level u
        e = qv ∙ sym (#-inj′ (sym qc ∙ qc')) ∙ sym qu
```

<!--en-->
To use the assumed reading of `BeforeAt`, both compared sets must be known to
lie in the same finite stage. The level membership of `u` supplies this fact at
`ku`; the newly established level equality supplies it for `v` at that very
stage. The environment equations then identify those two sets with the values
at `x` and `y`.
<!--zh-->
要使用假定的 `BeforeAt` 读取方向，必须先知道被比较的两个集合都属于同一个有穷层。`u` 的层号隶属给出它位于第 `ku` 层，新得到的层号等式则把 `v` 也放入这一层；环境等式再把这两个集合分别认作 `x` 与 `y` 处的取值。
<!--ja-->
仮定された `BeforeAt` の読み取り方向を使うには、比較する二つの集合が同じ有限段階に属することが必要である。`u` の段階所属から `ku` における事実が得られ、新しく得た段階番号の等式によって `v` も同じ段階に置かれる。さらに環境の等式が、この二つの集合を `x` と `y` にある値に同定する。
<!--/-->

```agda
        xIn : ⟨ fst (lookup x γ) ∈ finiteStage ku ⟩
        xIn = subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qx) (levelStage u ku qu)
        yIn : ⟨ fst (lookup y γ) ∈ finiteStage ku ⟩
        yIn = subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qy)
          (levelStage v ku (e ∙ qu))
```

<!--en-->
The abstract `BeforeAt-out` hypothesis now applies at the numeral represented by `c`. It returns `before ku` for the two environment values; replacing those values by `fst u` and `fst v`, and replacing `ku` by `level u`, produces the finite-stage component required by the limit order. This completes the common-level reading without assuming any meaning for `BeforeAt` outside its stated stage boundary.
<!--zh-->
现在可以在 `c` 所表示的数码处应用抽象假设 `BeforeAt-out`。它先给出两个环境值之间的 `before ku`；把这两个值换成 `fst u` 与 `fst v`，再把 `ku` 换成 `level u`，便得到极限序同层支所需的有穷层比较。整个论证只在假设规定的层边界内使用 `BeforeAt`，不要求它在边界外具有任何语义。
<!--ja-->
ここで、`c` が表す数項のもとで抽象的な仮定 `BeforeAt-out` を適用できる。まず環境の二つの値に対する `before ku` が得られ、それらを `fst u` と `fst v` に、さらに `ku` を `level u` に置き換えると、極限段階の順序の同段階枝に必要な有限段階の比較になる。この議論では、仮定された段階の境界外で `BeforeAt` に意味があるとは仮定していない。
<!--/-->

```agda
        below : ⟨ before (level u) (fst u) (fst v) ⟩
        below = subst (λ j → ⟨ before j (fst u) (fst v) ⟩) (sym qu)
          (subst2 (λ s t → ⟨ before ku s t ⟩) qx qy
            (BeforeAt-out zero (suc x) (suc y) (c ∷ γ) ku qc xIn yIn hb))
```

<!--en-->
The two mathematical clauses of `LimitOrdAt` remain visible through their
adequacy laws: different levels are compared by their numeral codes, while
equal levels are compared by the supplied finite-stage formula. The opaque
boundary makes every use of the definition pass through those two laws.
Consequently, every result inside `Described` remains conditional on its three
inputs.
<!--zh-->
`LimitOrdAt` 的两条充分性律保留了两个数学分支的意义：层号不同时比较其数码，同层时使用外部提供的有穷层公式。不透明边界使这一定义的每次使用都经过这两条定律。因此，`Described` 内的每项结果都以它的三个输入为条件。
<!--ja-->
`LimitOrdAt` の二つの数学的な枝の意味は、その妥当性の法則によって保たれる。段階番号が異なる場合は数項を比較し、同じ場合は与えられた有限段階の論理式を使う。不透明な境界により、この定義を使うたびにその二つの法則を経由する。したがって、`Described` 内のすべての結果は三つの入力を仮定した条件つきである。
<!--/-->

```agda
    opaque
      unfolding LimitOrdAt
```

<!--en-->
Suppose first that `u` appears at a strictly earlier finite level than `v`. The object-language witness consists of the two model numerals `# ku` and `# kv`; their `LevelAt` certificates identify the levels of the two objects, and membership of the first numeral in the second expresses `ku < kv`. These data inhabit the different-level branch of `LimitOrdAt`.
<!--zh-->
先设 `u` 首次出现的有穷层严格早于 `v`。对象语言中的两个见证是模型数码 `# ku` 与 `# kv`；它们的 `LevelAt` 证书分别认出两个对象的层号，而第一个数码属于第二个数码正好表达 `ku < kv`。这些资料共同构成 `LimitOrdAt` 的异层支。
<!--ja-->
まず、`u` が `v` より真に早い有限段階で初めて現れるとする。対象言語で用いる二つの証人はモデル内の数項 `# ku` と `# kv` である。それぞれの `LevelAt` の証明が二対象の段階番号を同定し、最初の数項が二つ目に属することが `ku < kv` を表す。これらのデータが `LimitOrdAt` の異なる段階の枝を成する。
<!--/-->

```agda
      LimitOrdAt-in : u ≺ˡ v → ⟨ γ ⊨ LimitOrdAt x y ⟩
      LimitOrdAt-in h = decide-in h
        where
        lower-in : ku < kv → ⟨ γ ⊨ LimitOrdAt x y ⟩
        lower-in hlt = ∣ inl ∣ numS ku , ∣ numS kv , split-in hlt ∣₁ ∣₁ ∣₁
```

<!--en-->
If the levels agree, a single numeral `# ku` certifies both `LevelAt` statements. The finite-stage part of the external comparison is then written into the assumed `BeforeAt` formula at that common stage. Using one witness is significant: equality of the two levels is conveyed by sharing the numeral, so no object-language equality between two level codes is needed.
<!--zh-->
若双方层号相等，只需一个数码 `# ku` 同时证明两条 `LevelAt` 陈述。外部比较中的有穷层部分随后被写入这一公共层处的 `BeforeAt` 公式。共同使用一个见证本身就表达两个层号相等，因此对象语言里不需要另写两个层号数码之间的等式。
<!--ja-->
段階番号が一致する場合は、一つの数項 `# ku` が二つの `LevelAt` の主張を同時に保証する。外部比較の有限段階部分は、その共通段階における `BeforeAt` の論理式へ書き込まれる。一つの証人を共有すること自体が二つの段階番号の一致を表すので、対象言語で二つの段階番号の数項の等式を書く必要はない。
<!--/-->

```agda
        inner-in : (e : level v ≡ level u)
                 → ⟨ before (level u) (fst u) (fst v) ⟩
                 → ⟨ γ ⊨ LimitOrdAt x y ⟩
        inner-in e k = ∣ inr ∣ numS ku , same-in e k ∣₁ ∣₁
```

<!--en-->
The external limit comparison presents exactly these alternatives. In its first branch, `Lift` only raises the universe of the proposition; `lower` removes that resizing and reveals the ordinary inequality of natural numbers. After the defining equations for `ku` and `kv` align the indices, the different-level constructor applies.
<!--zh-->
外部极限比较恰好给出这两个选项。在第一支中，`Lift` 只把命题放入更高的宇宙；`lower` 所做的是命题换级，从中取回普通的自然数不等式。再用 `ku` 与 `kv` 的定义等式对齐索引，便可应用异层支的构造。
<!--ja-->
外部の極限比較は、ちょうどこの二つの選択肢からなる。第一の枝にある `Lift` は命題の宇宙だけを持ち上げており、`lower` はそのリサイズを戻して通常の自然数の不等式を取り出す。`ku` と `kv` の定義等式で添字をそろえれば、異なる段階の枝を構成できる。
<!--/-->

```agda
        decide-in : Lift {ℓ-zero} {ℓ-suc ℓ} (level u < level v)
                  ⊎ ((level v ≡ level u)
                     × ⟨ before (level u) (fst u) (fst v) ⟩)
                  → ⟨ γ ⊨ LimitOrdAt x y ⟩
        decide-in (inl k)       = lower-in (subst2 _<_ qu qv (lower k))
```

<!--en-->
The second external alternative already contains both ingredients needed at a common level: the equality of levels and the `before` comparison there. Passing them to the common-level construction completes the filling direction. Hence `LimitOrdAt-in` follows the lexicographic definition of the existing limit order, rather than introducing a new order.
<!--zh-->
外部比较的第二个选项已经包含同层构造所需的两项资料：层号相等，以及该层中的 `before` 比较。把二者交给同层构造便完成填充方向。因此，`LimitOrdAt-in` 只是依照既有极限序的字典式定义行事，并未引入一条新序。
<!--ja-->
外部比較の第二の選択肢には、共通段階の構成に必要な二つの要素、すなわち段階番号の等式とその段階での `before` 比較がすでに含まれている。これらを同段階の構成へ渡すと、書き込み方向が完成する。したがって `LimitOrdAt-in` は既存の極限順序の辞書式定義に従うものであり、新しい順序を導入するものではない。
<!--/-->

```agda
        decide-in (inr (e , k)) = inner-in e k
```

<!--en-->
Reading `LimitOrdAt` starts from a propositionally truncated choice of its two branches, so the result is initially a propositionally truncated comparison. In the different-level branch, the two existential witnesses are read by `split-out`, which turns numeral membership back into strict inequality of the actual levels. That inequality is inserted into the first branch of the external limit comparison and kept under truncation.
<!--zh-->
读取 `LimitOrdAt` 时，两个分支的选择已经处在命题截断之中，所以最初只能得到命题截断的比较。在异层支中，两层存在见证由 `split-out` 读取；数码隶属由此还原为真实层号之间的严格不等式。所得不等式进入外部极限比较的第一支，并继续保留在命题截断内。
<!--ja-->
`LimitOrdAt` の読み取りは、二つの枝の選択が命題的切り詰めの中にある状態から始まるため、最初に得られる比較も命題的切り詰められている。異なる段階の枝では、二つの存在証人を `split-out` で読み、数項の所属を実際の段階番号の狭義不等式へ戻す。その不等式を外部の極限比較の第一の枝に入れ、切り詰めの内側に保つ。
<!--/-->

```agda
      LimitOrdAt-out : ⟨ γ ⊨ LimitOrdAt x y ⟩ → ∥ u ≺ˡ v ∥₁
      LimitOrdAt-out = rec₁ squash₁ decide
        where
        atSplit : (c : S) → Σ[ d ∈ S ] Split c d → ∥ u ≺ˡ v ∥₁
        atSplit c (d , hs) = ∣ inl (lift (split-out c d hs)) ∣₁
```

<!--en-->
In the common-level branch, `same-out` returns equality of the actual levels together with the finite-stage `before` comparison. Those two pieces are precisely the second branch of the external limit comparison. No inequality is derived in this case; the ordering information comes entirely from the within-level comparison.
<!--zh-->
在同层支中，`same-out` 返回真实层号相等以及该有穷层中的 `before` 比较。这两项正好构成外部极限比较的第二支。这里不会导出任何层号不等式；次序信息完全来自层内比较。
<!--ja-->
同じ段階の枝では、`same-out` が実際の段階番号の等式と、その有限段階における `before` の比較を返す。この二つがそのまま外部の極限比較の第二の枝になる。この場合、段階番号の不等式は導かれず、順序情報はすべて段階内の比較から得られる。
<!--/-->

```agda
        atSame : Σ[ c ∈ S ] Same c → ∥ u ≺ˡ v ∥₁
        atSame (c , hs) = ∣ inr (same-out c hs) ∣₁
```

<!--en-->
The semantic disjunction separates the two mathematical cases before any witnesses are inspected. Its left side contains two nested existential levels and numeral membership; its right side contains one shared level and the finite-stage formula. This shape mirrors the level-primary, then within-level, comparison of the limit order.
<!--zh-->
语义析取先把两个数学情形分开，再处理各自的见证。左侧含有两层嵌套的层号存在见证与数码隶属，右侧则含有一个共同层号及有穷层公式。这一结构正对应极限序先比较层号、同层时再作层内比较的字典式次序。
<!--ja-->
意味論的な選言は、各証人を調べる前に二つの数学的場合を分ける。左側には入れ子になった二つの段階番号の存在証人と数項の所属があり、右側には一つの共通段階と有限段階の論理式がある。この形は、まず段階番号を比較し、同じなら段階内を比較する極限順序の辞書式構造に対応する。
<!--/-->

```agda
        decide : ⟨ γ ⊨ ∃̇ ( ∃̇ ( LevelAt (suc zero) (sh2 x)
                            ∧̇ ( LevelAt zero (sh2 y)
                              ∧̇ (var (suc zero) ∈̇ var zero) ) ) ) ⟩
               ⊎ ⟨ γ ⊨ ∃̇ ( LevelAt zero (suc x)
                         ∧̇ ( LevelAt zero (suc y)
```

<!--en-->
Each existential is eliminated only into the propositionally truncated target. The different-level case exposes a candidate for each level and applies `atSplit`; the common-level case exposes its single shared candidate and applies `atSame`. The witnesses are used locally to justify the comparison, and no choice of level numeral escapes the truncation.
<!--zh-->
每个存在见证都只被消去到命题截断的目标中。异层情形局部取出两个候选层号并应用 `atSplit`，同层情形局部取出唯一的共同候选并应用 `atSame`。这些见证只用于证明当前比较，没有任何层号数码的选择逸出命题截断。
<!--ja-->
各存在証人は、命題的切り詰められた目標に対してだけ除去される。異なる段階の場合は二つの候補を局所的に取り出して `atSplit` を適用し、同じ段階の場合は一つの共通候補を取り出して `atSame` を適用する。証人はその比較を正当化するために局所的に使われ、段階番号の数項の選択が切り詰めの外へ出ることはない。
<!--/-->

```agda
                           ∧̇ BeforeAt zero (suc x) (suc y) ) ) ⟩
               → ∥ u ≺ˡ v ∥₁
        decide (inl h) = rec₁ squash₁
          (λ { (c , hd) → rec₁ squash₁ (atSplit c) hd }) h
        decide (inr h) = rec₁ squash₁ atSame h
```
</div>
</details>

<!--en-->
## The order, as a set
<!--zh-->
## 那个序，作为一个集合
<!--ja-->
## 順序を集合にする
<!--/-->

<!--en-->
To turn comparison into a relation set, the separating condition must recognize a candidate ordered pair. `Cond₀` binds possible components `c` and `d`, requires the candidate to be the coded pair of those components, and requires `LimitOrdAt c d`. Thus the condition speaks about both the shape of an element and the direction of the represented comparison.
<!--zh-->
要把比较化为关系集，分离条件必须先辨认候选元素是否为有序对。`Cond₀` 绑定可能的分量 `c` 与 `d`，要求候选元素是二者的编码有序对，并要求 `LimitOrdAt c d` 成立。因此，这个条件同时规定元素的配对形状与其所表示比较的方向。
<!--ja-->
比較を関係集合へ変えるには、分出条件が候補の要素を順序対として認識しなければならない。`Cond₀` は候補の成分 `c` と `d` を束縛し、候補がそれらの符号化された順序対であることと、`LimitOrdAt c d` が成り立つことを要求する。したがって、この条件は要素の対としての形と、表現される比較の向きの両方を述べる。
<!--/-->

```agda
  Cond₀ : Formula S 1
  Cond₀ = ∃̇ ( ∃̇ ( prAtL (sh2 zero) (suc zero) zero
                 ∧̇ LimitOrdAt (suc zero) zero ) )
```

<!--en-->
Within an instance of `Described`, separation applies `Cond₀` to the common bound containing all pairs of limit-stage elements. The resulting model element `codeOrder` contains exactly the candidates in that bound that satisfy the comparison condition. Its existence is conditional on the supplied `BeforeAt` formula and its two adequacy directions; the concrete instance is provided in the next chapter.
<!--zh-->
在 `Described` 的一个实例内部，分离以 `Cond₀` 筛选包含所有极限层元素对的公共界。所得模型元素 `codeOrder` 恰好包含这个界内满足比较条件的候选元素。它的存在以给定的 `BeforeAt` 公式及其两条充分性方向为条件；下一章才提供具体实例。
<!--ja-->
`Described` の具体例の内部では、極限段階の要素のすべての対を含む共通の上界に `Cond₀` を用いて分出を行う。得られるモデル要素 `codeOrder` は、その上界のうち比較条件を満たす候補をちょうど含む。その存在は、与えられた `BeforeAt` の論理式と二つの妥当性の方向を条件としており、具体的な実現は次の章で与えられる。
<!--/-->

```agda
  opaque
    codeOrder : S
    codeOrder = hasSeparationL (pairsBound .fst) Cond₀ .fst .fst
```

<!--en-->
The separation specification is the usable characterization of membership: a candidate lies in `codeOrder` exactly when it lies in `pairsBound` and satisfies `Cond₀`. The bound alone may contain extra elements, so it supplies only set-sized containment. Exactness comes from the second conjunct, which identifies an ordered pair and verifies its limit comparison.
<!--zh-->
分离规格给出可直接使用的隶属刻画：一个候选元素属于 `codeOrder`，当且仅当它属于 `pairsBound` 并满足 `Cond₀`。公共界本身可能还含有额外元素，因此只负责给出集合大小的包容；精确性来自第二个合取项，它辨认有序对并验证相应的极限比较。
<!--ja-->
分出の仕様は、所属について直接使える特徴づけを与える。候補が `codeOrder` に属することは、それが `pairsBound` に属し、かつ `Cond₀` を満たすことと同値である。上界そのものは余分な要素を含み得るので、集合としての包含だけを与える。正確さを担うのは第二の連言であり、順序対を同定して対応する極限比較を検証する。
<!--/-->

```agda
    codeOrder-mem : (z : S) → (z ∈ˢ codeOrder)
                  ≡ ((z ∈ˢ pairsBound .fst) ⊓ ((z ∷ []) ⊨ Cond₀))
    codeOrder-mem = hasSeparationL (pairsBound .fst) Cond₀ .fst .snd
```

<!--en-->
For fixed `z`, `c`, and `d`, `Inner` isolates the two facts required by the separating formula: `z` is the coded ordered pair of `c` and `d`, and `c` precedes `d` according to `LimitOrdAt`. Keeping these facts together makes clear that the endpoints used by the comparison are the very components encoded by the candidate pair.
<!--zh-->
固定 `z`、`c`、`d` 后，`Inner` 集中记录分离公式所需的两个事实：`z` 是 `c` 与 `d` 的编码有序对，并且 `LimitOrdAt` 判定 `c` 在 `d` 之前。把二者放在一起，便能确保比较所用的端点正是候选对编码的两个分量。
<!--ja-->
`z`、`c`、`d` を固定すると、`Inner` は分出の論理式に必要な二つの事実をまとめる。すなわち、`z` が `c` と `d` の符号化された順序対であることと、`LimitOrdAt` によって `c` が `d` より前にあることである。二つを一緒に保持することで、比較に使う端点が候補の対に符号化された成分そのものであることが明確になる。
<!--/-->

```agda
  private
    Inner : S → S → S → Type (ℓ-suc ℓ)
    Inner z c d = ⟨ (d ∷ c ∷ z ∷ []) ⊨ prAtL (sh2 zero) (suc zero) zero ⟩
                × ⟨ (d ∷ c ∷ z ∷ []) ⊨ LimitOrdAt (suc zero) zero ⟩
```

<!--en-->
`Outer z` displays the witness pattern of the two nested existential quantifiers. A first component `c` is accompanied by the propositionally truncated existence of a second component `d` satisfying `Inner z c d`. The nesting matches the semantics of `Cond₀` and preserves witness dependence without choosing a canonical decomposition of `z`.
<!--zh-->
`Outer z` 展示两层嵌套存在量词的见证结构：先给出第一个分量 `c`，再在命题截断中给出满足 `Inner z c d` 的第二个分量 `d`。这种嵌套与 `Cond₀` 的语义一致，既保留见证之间的依赖，也不为 `z` 选择一个规范分解。
<!--ja-->
`Outer z` は、入れ子になった二つの存在量化の証人の形を明示する。第一の成分 `c` に、`Inner z c d` を満たす第二の成分 `d` の命題的切り詰められた存在が伴う。この入れ子は `Cond₀` の意味論と一致し、証人間の依存を保ちながら、`z` の標準的な分解を選ぶことはない。
<!--/-->

```agda
    Outer : S → Type (ℓ-suc ℓ)
    Outer z = Σ[ c ∈ S ] ∥ (Σ[ d ∈ S ] Inner z c d) ∥₁
```

<!--en-->
Given actual components and the two facts in `Inner`, the separating condition is satisfied by placing those components under its nested existential quantifiers. Both existential witnesses are propositionally truncated, as object-language existence records only that suitable components occur. This is sufficient for separation because membership in the resulting set is itself a proposition.
<!--zh-->
给定实际分量以及 `Inner` 中的两个事实，只要把这些分量依次放入嵌套存在量词，就能满足分离条件。两个存在见证都处在命题截断中，因为对象语言的存在只记录合适分量确实存在。分离所得集合的隶属本身是命题，所以这些资料已经足够。
<!--ja-->
実際の成分と `Inner` の二つの事実があれば、それらの成分を入れ子になった存在量化へ順に入れることで分出条件を満たせる。対象言語の存在は適切な成分があることだけを記録するため、二つの存在証人はいずれも命題的に切り詰められている。得られる集合への所属も命題なので、分出にはこれで十分である。
<!--/-->

```agda
    cond-in : (z c d : S) → Inner z c d → ⟨ (z ∷ []) ⊨ Cond₀ ⟩
    cond-in z c d hi = ∣ c , ∣ d , hi ∣₁ ∣₁
```

<!--en-->
Conversely, satisfaction of `Cond₀` already has the truncated nested shape recorded by `Outer`. The reading therefore preserves that evidence directly, without selecting either component. This small observation is what allows later membership proofs to unpack the separating condition while remaining entirely within propositionally truncated existence.
<!--zh-->
反过来，满足 `Cond₀` 的证据已经具有 `Outer` 所记录的截断嵌套结构，所以读取时可以直接保留这份证据，不必选择任何一个分量。借助这一点，后面的隶属证明可以展开分离条件，同时始终留在命题截断的存在之内。
<!--ja-->
逆に、`Cond₀` の充足はすでに `Outer` が記録する切り詰められた入れ子の形をしている。そのため読み取りでは、どちらの成分も選ばずに証拠をそのまま保てる。この点により、後の所属の証明は、命題的切り詰められた存在の範囲にとどまったまま分出条件を展開できる。
<!--/-->

```agda
    cond-out : (z : S) → ⟨ (z ∷ []) ⊨ Cond₀ ⟩ → ∥ Outer z ∥₁
    cond-out z h = h
```

<!--en-->
The filling law begins with an external comparison `u ≺ˡ v` and aims to place the ordinary ordered pair of their underlying sets in `codeOrder`. The proof first works with `limitEl u` and `limitEl v`, which are genuine elements of the model, and with their model-coded pair. A final equality relates that internal presentation to `pr (fst u) (fst v)`.
<!--zh-->
填充律从外部比较 `u ≺ˡ v` 出发，目标是证明二者底层集合的普通有序对属于 `codeOrder`。论证先使用真正位于模型中的 `limitEl u`、`limitEl v` 及其模型内编码对；最后再用一条等式把这一内部呈现与 `pr (fst u) (fst v)` 对齐。
<!--ja-->
書き込み則は外部の比較 `u ≺ˡ v` から始め、二つの台となる集合の通常の順序対が `codeOrder` に属することを目指す。まず、モデルの実際の要素である `limitEl u` と `limitEl v`、およびそれらのモデル内で符号化された対を用いる。最後に一つの等式で、この内部表現を `pr (fst u) (fst v)` に対応づける。
<!--/-->

```agda
  codeOrder-fill : (u v : Limit) → u ≺ˡ v
                 → ⟨ pr (fst u) (fst v) ∈ fst codeOrder ⟩
  codeOrder-fill u v h =
    subst (λ t → ⟨ t ∈ fst codeOrder ⟩) qz
      (subst ⟨_⟩ (sym (codeOrder-mem (prS (limitEl u) (limitEl v))))
```

<!--en-->
The separation specification reduces the membership goal to two mathematical obligations. The model-coded pair must lie in the common bound, and `Cond₀` must hold with `limitEl u` and `limitEl v` as its two witnesses. Once these obligations are met, separation returns membership, which is then transported along the equality of the two pair presentations.
<!--zh-->
分离规格把隶属目标归约为两个数学义务。模型内编码对必须属于公共界，而 `Cond₀` 必须以 `limitEl u` 与 `limitEl v` 为两个见证成立。完成这两项后，分离规格给出隶属，再沿两个配对呈现之间的等式得到原目标。
<!--ja-->
分出の仕様により、所属の目標は二つの数学的な課題へ帰着する。モデル内で符号化された対が共通の上界に属することと、`limitEl u` と `limitEl v` を二つの証人として `Cond₀` が成り立つことである。これらを満たすと分出の仕様から所属が得られ、二つの対の表現を結ぶ等式に沿って元の目標へ移せる。
<!--/-->

```agda
        (inBound , cond-in (prS (limitEl u) (limitEl v))
                     (limitEl u) (limitEl v) (hpr , hord)))
    where
    qz : fst (prS (limitEl u) (limitEl v)) ≡ pr (fst u) (fst v)
    qz = prS-fst (limitEl u) (limitEl v)
```

<!--en-->
The alignment equality is obtained in two transparent steps. The projection of the model pairing is the external pair of the projections, and each `limitEl` projects to the underlying set of its original limit element. Combining these facts ensures that changing presentation does not change either endpoint or their order.
<!--zh-->
对齐等式由两个直接步骤组成。模型内配对的投影等于两个投影的外部有序对，而每个 `limitEl` 又投影回原极限层元素的底层集合。复合这两个事实可知，改变呈现既不改变任何端点，也不改变端点的顺序。
<!--ja-->
対応づけの等式は二つの明確な段階から得られる。モデル内の対の射影は二つの射影からなる外部の順序対であり、各 `limitEl` は元の極限段階の要素の台となる集合へ射影される。これらを合成することで、表現を変えても端点もその順番も変わらないことが保証される。
<!--/-->

```agda
       ∙ cong₂ pr (limitEl-fst u) (limitEl-fst v)
```

<!--en-->
The first separation obligation uses the defining property of `pairsBound`: it covers the ordered pair arising from every two elements of the limit stage. The pair is aligned with that covered external pair before the bound certificate is used. No converse property of the bound is needed, since `Cond₀` supplies the exact comparison criterion.
<!--zh-->
第一个分离义务使用 `pairsBound` 的定义性质：任取两个极限层元素，由它们形成的有序对都受这个界覆盖。应用覆盖证书前，先把模型内编码对与相应的外部有序对对齐。这里不需要公共界的反向刻画，因为精确的比较标准由 `Cond₀` 提供。
<!--ja-->
第一の分出の課題には `pairsBound` の定義的な性質を使う。極限段階の任意の二要素から作る順序対は、この上界に含まれる。包含の証明を使う前に、モデル内で符号化された対を対応する外部の順序対にそろえる。正確な比較条件は `Cond₀` が与えるため、上界の逆向きの特徴づけは不要である。
<!--/-->

```agda
    inBound : ⟨ fst (prS (limitEl u) (limitEl v)) ∈ fst (pairsBound .fst) ⟩
    inBound = subst (λ t → ⟨ t ∈ fst (pairsBound .fst) ⟩) (sym qz)
      (pairsBound .snd u v)
```

<!--en-->
The pairing conjunct of `Cond₀` is established by adequacy of `prAtL`. The model pairing already projects to the required ordered pair, so that adequacy law turns the projection equality into satisfaction of the pairing atom. This connects the set-theoretic pair used by the bound with the object-language description used by separation.
<!--zh-->
`Cond₀` 的配对合取项由 `prAtL` 的充分性建立。模型内配对的投影已经是所需的有序对，因此这条充分性律把投影等式转成配对原子的满足证据。由此，公共界所用的集合论有序对与分离条件所用的对象语言描述连接起来。
<!--ja-->
`Cond₀` の対を表す連言は、`prAtL` の妥当性によって示される。モデル内の対はすでに必要な順序対へ射影されるので、その妥当性の法則が射影の等式を対アトムの充足へ変換する。こうして、上界で使う集合論的な順序対と、分出条件で使う対象言語の記述が結びつく。
<!--/-->

```agda
    hpr : ⟨ (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
          ⊨ prAtL (sh2 zero) (suc zero) zero ⟩
    hpr = subst ⟨_⟩ (sym (prAtL-adequate (sh2 zero) (suc zero) zero
      (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])))
      (prS-fst (limitEl u) (limitEl v))
```

<!--en-->
The comparison conjunct is supplied by `LimitOrdAt-in` at the environment containing the candidate pair and its two components. Its alignment equations are reflexive after the components are chosen as `limitEl u` and `limitEl v`, and the original hypothesis `u ≺ˡ v` supplies the comparison. This finishes the conditional representation of the forward direction.
<!--zh-->
比较合取项由 `LimitOrdAt-in` 在含有候选对及其两个分量的环境中给出。把分量取为 `limitEl u` 与 `limitEl v` 后，所需的对齐等式都是自反等式，而原假设 `u ≺ˡ v` 正好提供比较。至此完成条件式表示的正向证明。
<!--ja-->
比較を表す連言は、候補の対とその二成分を含む環境で `LimitOrdAt-in` を使って与える。成分を `limitEl u` と `limitEl v` に選べば、必要な対応の等式は反射律であり、元の仮定 `u ≺ˡ v` が比較を与える。これで条件つき表現の順方向が完成する。
<!--/-->

```agda
    hord : ⟨ (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
          ⊨ LimitOrdAt (suc zero) zero ⟩
    hord = Order.LimitOrdAt-in (suc zero) zero
      (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
      u v (level u) (level v) refl refl (limitEl-fst u) (limitEl-fst v) h
```

<!--en-->
The reading law starts from membership of `pr (fst u) (fst v)` in `codeOrder`. Separation will yield a propositionally truncated pair of components satisfying the pairing and comparison conditions; reading those conditions gives only `∥ u ≺ˡ v ∥₁`. The final use of `strictLimit` is justified by the already proved strict well order `limitOrder`, whose trichotomy excludes equality and the reverse comparison.
<!--zh-->
读取律从 `pr (fst u) (fst v)` 属于 `codeOrder` 出发。分离条件会给出一对处于命题截断中的分量，并证明它们满足配对与比较条件；读取这些条件最初只能得到 `∥ u ≺ˡ v ∥₁`。最后由既已证明的严格良序 `limitOrder` 应用 `strictLimit`，利用三歧性排除相等与反向比较，才得到未截断的结论。
<!--ja-->
読み取り則は、`pr (fst u) (fst v)` が `codeOrder` に属することから始まる。分出条件からは、対と比較の条件を満たす二成分が命題的切り詰めの中で得られ、それらを読んでも最初は `∥ u ≺ˡ v ∥₁` だけが得られる。最後に、すでに証明された狭義整列順序 `limitOrder` の三分律で等しい場合と逆向きの比較を排除し、`strictLimit` によって切り詰められていない結論を得る。
<!--/-->

```agda
  codeOrder-rep : (u v : Limit)
                → ⟨ pr (fst u) (fst v) ∈ fst codeOrder ⟩ → u ≺ˡ v
  codeOrder-rep u v h = strictLimit u v
    (rec₁ squash₁ atC
      (cond-out (prS (limitEl u) (limitEl v))
```

<!--en-->
As in the filling direction, the model-coded pair is identified with the external pair of the two underlying sets. After membership is transferred to that presentation, `codeOrder-mem` exposes the two conjuncts of separation, and its second conjunct is satisfaction of `Cond₀`. The proof can ignore the bound conjunct from this point, because all endpoint information lies in the separating condition.
<!--zh-->
与填充方向相同，先把模型内编码对认作两个底层集合的外部有序对。把隶属转到这一呈现后，`codeOrder-mem` 展开分离的两个合取项，其中第二项正是满足 `Cond₀`。从此可以不再使用公共界合取项，因为端点及比较的全部信息都在分离条件中。
<!--ja-->
書き込み方向と同様に、モデル内で符号化された対を二つの台となる集合の外部の順序対と同定する。その表現へ所属を移すと、`codeOrder-mem` が分出の二つの連言を示し、第二の連言として `Cond₀` の充足が得られる。端点と比較の情報はすべて分出条件にあるので、ここから先は上界の連言を使う必要がない。
<!--/-->

```agda
        (subst ⟨_⟩ (codeOrder-mem (prS (limitEl u) (limitEl v))) inSet .snd)))
    where
    qz : fst (prS (limitEl u) (limitEl v)) ≡ pr (fst u) (fst v)
    qz = prS-fst (limitEl u) (limitEl v)
       ∙ cong₂ pr (limitEl-fst u) (limitEl-fst v)
```

<!--en-->
The given membership concerns the external pair, whereas the separating specification is applied to the model element produced by `prS`. Their underlying sets are equal by the pair-alignment equation, so membership transports to the model presentation. This change of presentation is essential before the object-language condition can be read in the environment carried by that model element.
<!--zh-->
已知隶属针对外部有序对，而分离规格要应用于 `prS` 产生的模型元素。配对对齐等式说明二者的底层集合相等，因此可以把隶属转到模型内呈现。只有完成这一步，才能在该模型元素所形成的环境中读取对象语言条件。
<!--ja-->
与えられた所属は外部の順序対についてのものであるが、分出の仕様は `prS` が作るモデル要素に適用される。対を対応づける等式により両者の台となる集合は等しいので、所属をモデル内の表現へ移せる。この表現の変更を行って初めて、そのモデル要素が作る環境で対象言語の条件を読み取れる。
<!--/-->

```agda
    inSet : ⟨ fst (prS (limitEl u) (limitEl v)) ∈ fst codeOrder ⟩
    inSet = subst (λ t → ⟨ t ∈ fst codeOrder ⟩) (sym qz) h
```

<!--en-->
For particular witnesses `c` and `d`, the pairing atom first shows that they are the endpoints encoded by the original pair. With those endpoint equalities in the required orientation, `LimitOrdAt-out` reads the accompanying comparison formula as a propositionally truncated `u ≺ˡ v`. Thus the comparison cannot be read independently of the pairing conjunct: the latter identifies which external limit elements the formula is about.
<!--zh-->
对给定见证 `c`、`d`，配对原子先证明它们正是原有序对所编码的两个端点。把所得端点等式调整到所需方向后，`LimitOrdAt-out` 才能把随附的比较公式读成命题截断的 `u ≺ˡ v`。因此，比较合取项不能脱离配对合取项单独读取，后者负责认定公式所比较的究竟是哪两个外部极限层元素。
<!--ja-->
具体的な証人 `c` と `d` に対して、まず対アトムから、それらが元の順序対に符号化された端点であることを示す。得られた端点の等式を必要な向きにすると、`LimitOrdAt-out` が付随する比較の論理式を命題的切り詰められた `u ≺ˡ v` として読み取れる。したがって比較の連言は対の連言から独立には読めない。後者が、論理式がどの外部の極限段階の要素を比較しているかを同定する。
<!--/-->

```agda
    atD : (c d : S) → Inner (prS (limitEl u) (limitEl v)) c d → ∥ u ≺ˡ v ∥₁
    atD c d (hpr , hord) = Order.LimitOrdAt-out (suc zero) zero
      (d ∷ c ∷ prS (limitEl u) (limitEl v) ∷ []) u v (level u) (level v)
      refl refl (sym (split .fst)) (sym (split .snd)) hord
      where
```

<!--en-->
Adequacy of the pairing atom turns its satisfaction into an equality between the candidate's underlying set and `pr (fst c) (fst d)`. The earlier alignment identifies that same candidate with `pr (fst u) (fst v)`. Composing the two equalities therefore equates the two ordered pairs and prepares the endpoint identities needed to read `LimitOrdAt`.
<!--zh-->
配对原子的充分性把其满足证据转成候选元素底层集合与 `pr (fst c) (fst d)` 之间的等式。先前的对齐又把同一个候选元素认作 `pr (fst u) (fst v)`。复合这两个等式便得到两个有序对相等，并为读取 `LimitOrdAt` 准备好所需的端点等式。
<!--ja-->
対アトムの妥当性により、その充足は候補の台となる集合と `pr (fst c) (fst d)` の等式へ変わる。先の対応づけは、同じ候補を `pr (fst u) (fst v)` と同定している。二つの等式を合成すると二つの順序対が等しいことが得られ、`LimitOrdAt` を読むために必要な端点の等式を導ける。
<!--/-->

```agda
      qcd : pr (fst u) (fst v) ≡ pr (fst c) (fst d)
      qcd = sym qz
        ∙ subst ⟨_⟩ (prAtL-adequate (sh2 zero) (suc zero) zero
            (d ∷ c ∷ prS (limitEl u) (limitEl v) ∷ [])) hpr
      split : (fst u ≡ fst c) × (fst v ≡ fst d)
```

<!--en-->
Injectivity of ordered-pair coding separates that pair equality into `fst u = fst c` and `fst v = fst d`. Both position and direction are preserved, so the left component cannot be exchanged with the right. Reversing these equalities gives exactly the alignment hypotheses expected by the reading theorem for `LimitOrdAt`.
<!--zh-->
有序对编码的单射性把配对等式拆成 `fst u = fst c` 与 `fst v = fst d`。两个分量的位置与方向都被保留，左端不会与右端交换。把这两条等式反向，正好得到 `LimitOrdAt` 读取定理所需的对齐假设。
<!--ja-->
順序対符号化の単射性により、対の等式は `fst u = fst c` と `fst v = fst d` に分かれる。成分の位置と順番は保たれるため、左端と右端が入れ替わることはない。これらの等式を逆向きにすると、`LimitOrdAt` の読み取り定理が要求する対応の仮定になる。
<!--/-->

```agda
      split = pr-inj qcd
```

<!--en-->
The outer reader processes the nested witnesses in the same order as `Cond₀` binds them: first `c`, then a truncated `d` together with `Inner`. Each elimination targets the propositionally truncated comparison already produced by `atD`, so truncation is respected throughout. After all possible decompositions have been mapped to that proposition, `strictLimit` supplies the final untruncated comparison.
<!--zh-->
外层读取按照 `Cond₀` 的绑定次序处理嵌套见证：先处理 `c`，再在命题截断内处理 `d` 及其 `Inner` 证据。每次消去的目标都是 `atD` 已给出的命题截断比较，所以整个过程始终遵守截断限制。所有可能分解都被映到这个命题后，再由 `strictLimit` 给出最终未截断的比较。
<!--ja-->
外側の読み取りは、`Cond₀` が束縛する順序どおりに入れ子の証人を処理する。まず `c` を取り、次に命題的切り詰めの中で `d` と `Inner` の証拠を扱う。各除去の目標は `atD` が作る命題的切り詰められた比較なので、全過程で切り詰めの制約が守られる。可能なすべての分解をその命題へ写した後、`strictLimit` が最後の切り詰められていない比較を与える。
<!--/-->

```agda
    atC : Outer (prS (limitEl u) (limitEl v)) → ∥ u ≺ˡ v ∥₁
    atC (c , hd) = rec₁ squash₁ (λ { (d , hi) → atD c d hi }) hd
```

<!--en-->
## The code slot, filled
<!--zh-->
## 那个为诸码所设的位，已填上
<!--ja-->
## 符号用のスロットを埋める
<!--/-->

<!--en-->
`CodeKeys` records one possible use of the conditional code relation in name
comparison over an arbitrary constructible carrier `A`. Besides `A` and its
constructibility proof, it fixes a strict well-order `w` on the small type of
members of `A`. The name-comparison adequacy results may then use `w` for
parameters and the current `Described` instance for codes. This nested module
is a reusable consequence of the representation theorem; the main construction
does not depend on it.
<!--zh-->
`CodeKeys` 记录了在任意可构造载体 `A` 上进行名字比较时，使用这条条件式码关系的一种方式。除了 `A` 及其可构造性证明，它还固定 `A` 的小成员类型上的严格良序 `w`。名字比较的充分性结果于是可用 `w` 比较参数，并用当前 `Described` 实例比较码。这个嵌套模块是表示定理的一项可复用推论，主构造并不依赖它。
<!--ja-->
`CodeKeys` は、任意の構成可能な台 `A` 上の名前比較で、この条件つきのコード関係を利用する一つの方法を記録する。`A` とその構成可能性の証明に加えて、`A` の要素からなる小さい型上の狭義整列順序 `w` を固定する。名前比較の妥当性の結果は、パラメータには `w` を、コードには現在の `Described` の具体例を使える。この入れ子のモジュールは表現定理から得られる再利用可能な帰結であり、主要な構成はこれに依存しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module CodeKeys (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
```
</summary>
<div class="submodule-fold-content">

```agda
    private module Ad = Adequacy A pA w
```

<!--en-->
The strict relation of `w` is given a local symbol to keep the parameter comparison distinct from `u ≺ˡ v`, the limit-stage comparison used for codes. This distinction matters because the two relations live on different carriers and receive separate internal relation sets. Their adequacy laws have the same shape, but their mathematical inputs are independent.
<!--zh-->
`w` 的严格关系在局部获得一个专用记号，以便把参数比较与码所用的极限层比较 `u ≺ˡ v` 区分开来。两条关系位于不同载体上，也由不同的内部关系集表示。它们的充分性律形状相同，但数学输入彼此独立。
<!--ja-->
`w` の狭義関係には局所的な記号を与え、コードに使う極限段階の比較 `u ≺ˡ v` とパラメータの比較を区別する。二つの関係は異なる台の上にあり、別々の内部関係集合によって表される。妥当性の法則は同じ形であるが、数学的な入力は互いに独立である。
<!--/-->

```agda
    open SWO w using () renaming ( _<∙_ to _≺ₚ_ )
```

<!--en-->
If a model relation `Ps` represents the parameter order in both directions,
`AtParams` presents it together with `codeOrder` and the two code-order
representation laws to `Adequacy.Keys`. The two represented relations remain
mathematically independent. The actual downstream route instantiates
`Described` in `EarliestDisagreement`, exports `codeOrder`,
`codeOrder-fill`, and `codeOrder-rep`, and has `InternalWellOrder` pass those
three results directly to `NameComparisonAdequacy.At.Least` together with the
separately represented parameter order.
<!--zh-->
若模型关系 `Ps` 从两个方向表示参数序，`AtParams` 就把它连同 `codeOrder` 及码序的两条表示律一起交给 `Adequacy.Keys`；这两条被表示的关系在数学上仍彼此独立。真实的下游路线在 `EarliestDisagreement` 中实例化 `Described`，公开 `codeOrder`、`codeOrder-fill` 与 `codeOrder-rep`，再由 `InternalWellOrder` 把这三项连同另行表示的参数序直接交给 `NameComparisonAdequacy.At.Least`。
<!--ja-->
モデル内の関係 `Ps` がパラメータ順序を双方向に表すなら、`AtParams` はそれを `codeOrder` およびコード順序の二つの表現則とともに `Adequacy.Keys` に渡す。表現される二つの関係は数学的には独立のままである。実際の後続経路では、`EarliestDisagreement` が `Described` を具体化して `codeOrder`、`codeOrder-fill`、`codeOrder-rep` を公開し、`InternalWellOrder` がこの三つを、別に表現されたパラメータ順序とともに `NameComparisonAdequacy.At.Least` へ直接渡する。
<!--/-->

```agda
    module AtParams (Ps : S)
      (Prep : (a b : ⟪ A ⟫) → ⟨ pr (Ad.ix a) (Ad.ix b) ∈ fst Ps ⟩ → a ≺ₚ b)
      (Pfill : (a b : ⟪ A ⟫) → a ≺ₚ b → ⟨ pr (Ad.ix a) (Ad.ix b) ∈ fst Ps ⟩)
      where
      open Ad.Keys codeOrder Ps codeOrder-rep codeOrder-fill Prep Pfill public
```
</div>
</details>

</div>
</details>

<!--en-->
## What is left, named exactly
<!--zh-->
## 剩下什么，点准了名
<!--ja-->
## 残る仮定を正確に述べる
<!--/-->

<!--en-->
The remaining input to `Described`{.Agda} is a formula `BeforeAt`{.Agda}
together with its two readings. These readings are required only when the
first value is the numeral `# m`{.Agda} and the two endpoints belong to
`finiteStage m`{.Agda}; under those hypotheses, satisfaction of the formula
is equivalent to `before m`{.Agda} comparing the endpoints. The module
`EarliestDisagreement` supplies exactly this data: `relAt m`{.Agda} represents
`before m`{.Agda}, `beforeFam`{.Agda} collects these represented relations over
the internal natural numbers, and its `BeforeAt`{.Agda} retrieves the relation
at the given numeral before applying it. Instantiating `Described`{.Agda} with
these results yields the public relation set `codeOrder`{.Agda} and its two
representation laws, `codeOrder-fill`{.Agda} and `codeOrder-rep`{.Agda}.
<!--zh-->
`Described`{.Agda} 尚需一条公式 `BeforeAt`{.Agda} 及其两条读式。这两条读式只要求处理如下情形：第一个取值是数码 `# m`{.Agda}，两个端点都属于 `finiteStage m`{.Agda}；在这些假设下，公式成立当且仅当 `before m`{.Agda} 比较这两个端点。模块 `EarliestDisagreement` 恰好给出这些资料：`relAt m`{.Agda} 表示 `before m`{.Agda}，`beforeFam`{.Agda} 沿内部自然数收集这些已经表示的关系，而其中的 `BeforeAt`{.Agda} 先取出给定数码处的关系，再把它应用于两个端点。以这些结果实例化 `Described`{.Agda}，便得到公开的关系集 `codeOrder`{.Agda} 及其两条表示律 `codeOrder-fill`{.Agda} 与 `codeOrder-rep`{.Agda}。
<!--ja-->
`Described`{.Agda} に残る入力は、論理式 `BeforeAt`{.Agda} とその二つの読みである。これらの読みが必要とされるのは、最初の値が数項 `# m`{.Agda} であり、二つの端点がともに `finiteStage m`{.Agda} に属する場合だけである。その仮定のもとで、論理式の充足は `before m`{.Agda} による端点の比較と同値になる。モジュール `EarliestDisagreement` は、まさにこのデータを与える。`relAt m`{.Agda} が `before m`{.Agda} を表現し、`beforeFam`{.Agda} が表現された関係を内部自然数に沿って集め、その `BeforeAt`{.Agda} が与えられた数項での関係を取り出してから二つの端点に適用する。これらの結果で `Described`{.Agda} を具体化すると、公開された関係集合 `codeOrder`{.Agda} と、その二つの表現則 `codeOrder-fill`{.Agda} および `codeOrder-rep`{.Agda} が得られる。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`LevelAt`{.Agda} identifies the numeral coding the least finite stage in which
a given limit-stage member appears, while `PrecedesAt`{.Agda} represents one
earliest-disagreement comparison relative to any already represented base
relation. Given the bounded two-way reading of `BeforeAt`{.Agda},
`Described`{.Agda} combines unequal-level and equal-level comparison in
`LimitOrdAt`{.Agda}, bounds all candidate ordered pairs, and separates the
conditional relation set `codeOrder`{.Agda}. Its filling and reading laws give,
for every `u,v : Limit`, both directions between `u ≺ˡ v` and membership of
`pr (fst u) (fst v)`{.Agda} in that set; the reading direction uses
`strictLimit`{.Agda} and the existing strict well-order to recover a comparison
from propositional truncation. `EarliestDisagreement` discharges the finite-stage
hypotheses, but this chapter neither asserts an object-language well-ordering of
`codeOrder`{.Agda} nor proves the Axiom of Choice.
<!--zh-->
`LevelAt`{.Agda} 认出给定极限层成员首次出现的有穷层所对应的数码，`PrecedesAt`{.Agda} 则相对于任意已经表示的基底关系，表示一次最先分歧比较。给定 `BeforeAt`{.Agda} 在规定边界内的双向读法后，`Described`{.Agda} 用 `LimitOrdAt`{.Agda} 组合异层比较与同层比较，为所有候选有序对取界，再由分离得到条件式关系集 `codeOrder`{.Agda}。对每个 `u,v : Limit`，填充律与读取律给出 `u ≺ˡ v` 和 `pr (fst u) (fst v)`{.Agda} 属于该集合之间的两个方向；读取方向使用 `strictLimit`{.Agda} 与既有严格良序，从命题截断恢复比较。`EarliestDisagreement` 兑现有穷层假设，但本章既不在对象语言中断言 `codeOrder`{.Agda} 是良序，也不证明选择公理。
<!--ja-->
`LevelAt`{.Agda} は、与えられた極限段階の要素が最初に現れる有限段階を符号化する数項を同定し、`PrecedesAt`{.Agda} は、すでに表現された任意の基礎関係に相対して、最初の相違による一回の比較を表現する。所定の範囲における `BeforeAt`{.Agda} の双方向の読みが与えられると、`Described`{.Agda} は `LimitOrdAt`{.Agda} の中で異なる段階の比較と同じ段階の比較を組み合わせ、候補となるすべての順序対に上界を与え、分出によって条件つきの関係集合 `codeOrder`{.Agda} を得る。各 `u,v : Limit` に対し、書き込み則と読み取り則は、`u ≺ˡ v` と `pr (fst u) (fst v)`{.Agda} がその集合に属することの両方向を与える。読み取り方向では、`strictLimit`{.Agda} と既存の狭義整列順序を用いて、命題的切り詰めから比較を復元する。`EarliestDisagreement` が有限段階についての仮定を満たすが、この章は `codeOrder`{.Agda} が整列順序をなすことを対象言語で主張せず、選択公理も証明しない。
<!--/-->
