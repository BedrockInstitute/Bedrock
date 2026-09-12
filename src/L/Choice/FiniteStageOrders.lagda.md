<!--en-->
# Well-orders on finite stages

This chapter proves that every numeral-indexed stage is finite and equips it with the earliest-disagreement well-order, then combines stage number and local order to well-order the limit stage.

The earlier choice construction locates, for each cell of a family, the stage at which the cell first has a member, and showed that this stage is a successor. Every member of the cell that appears exactly there is therefore a definable subset of one and the same set: a name written over a single stage. What is still missing is a way to **compare** those names, and comparison is what this chapter builds, at the bottom of the tower.

The chapter rests on two claims. The first is that each stage indexed by a numeral is finite, in the precise sense given below: it comes with a finite list of sets that includes all of its members. The second is that a finite stage carries a well-order, obtained by comparing two of its members at the earliest point where they disagree, and giving the larger place to whichever of the two contains that point.

The second claim is the mathematical content, and it is a claim about **finite** sets in an essential way. Order the subsets of the natural numbers by that same recipe and there is an infinite descent: the set of all numbers, then all numbers from one on, then all from two on, and so forth, each step deleting the earliest surviving point and so landing strictly lower. Nothing about the recipe forbids this; what forbids it over a finite base is that a finite base has only finitely many subsets, so a search for a smallest one terminates. The well-foundedness proof below goes exactly this way: a finite list plus a linear order yields a smallest member of any inhabited property, by scanning the list and keeping, at each step, the smallest candidate so far; and "every inhabited property has a smallest member" is, classically, well-foundedness.

Finiteness propagates up the tower because the definable subsets of a finite set are all of its subsets, and a set with a list has only finitely many subsets, one for each vector of bits over that list. So a list of the stage yields a list of the next stage, and the recursion is enough to carry the whole construction through.

The limit-stage construction does not require a compatibility theorem for the finite-stage orders. It uses the first stage at which an element appears as the primary key. Two members of the limit that first appear at different finite stages are compared by those stage numbers alone; two that first appear at the same stage are compared by that stage's own order. No compatibility between the finite-stage orders is needed, and none is asserted.
<!--zh-->
# 有限层上的良序

本章证明每个以数码为索引的层都是有穷的，并以最先分歧赋予其良序；随后结合层号与局部序来良序化极限层。

先前的选择构造为一个族的每一格定位了该格首次拥有成员的层，并证明了它是一个后继。于是该格中恰在那里现身的每个成员，都是同一个集合的可定义子集：一个写在单一层之上的名字。尚缺的是**比较**这些名字的办法，而本章要在塔的底部造出的正是这种比较。

本章依赖两个论断。第一，凡以数码为索引的层都是有穷的，其确切含义见下文：它附带一份有穷的集合清单，清单包含它的全部成员。第二，有穷层带有一个良序：比较两个成员时，看它们最先在何处出现分歧，并把较大的位置判给含有该处的那一个。

第二个论断才是数学内容所在，它本质上是关于**有穷**集合的论断。若把同一构造用于自然数的子集，就会出现无穷下降：先是全体自然数，然后是从一开始的全体，再是从二开始的全体，如此下去，每一步删去尚存者中最先的那一个，因而严格落到更低处。构造本身并不排除这种情形；在有穷基底上，只有有穷多个子集，因此寻找最小成员的过程会终止。下文据此证明良基性：一份有穷清单加上一个线序，可以为任何非空性质给出最小成员，方法是逐项检查清单，并在每一步保留截至该处最小的候选；而「每个非空性质都有最小成员」在经典意义下就是良基性。

有穷性能沿塔逐层推广，是因为有穷集合的可定义子集就是它的全部子集，而带清单的集合只有有穷多个子集，清单上的每个位向量对应其中一个。于是一层的清单给出下一层的清单，递归便足以推进整个构造。

极限层的构造无须假设或证明各有穷层序之间相容。它先比较元素首次出现的层号；层号相同，才使用该层自己的序。因此，不同层的元素由层号比较，同一层首次出现的元素由局部序比较。
<!--ja-->
# 有限段階上の整列順序

本章では、数項で添字づけられた各段階が有限であることを証明し、最初の相違による整列順序を与える。さらに段階番号と局所順序を組み合わせて極限段階を整列順序づける。

先の選択の構成は、族の各セルについて、そのセルが初めて要素を持つ段階を特定し、その段階が後者であることを示した。したがって、ちょうどそこに現れるセルの各要素は、同一の集合上の定義可能部分集合、すなわち単一の段階に書かれた名前である。いまだ欠けているのは、それらの名前を**比較**する方法であり、本章が塔の底部で築くのはまさにこの比較である。

本章は二つの主張に依拠する。第一に、数項で添字づけられた各段階は有限である、という主張である。その正確な意味は下で述べる。すなわち、その段階は自身のすべての要素を含む有限な集合のリストを備える。第二に、有限段階は整列順序を担う、という主張である。これは、二つの要素をそれらが最初に相違する位置で比較し、その位置を含むほうを大きいとするものである。

第二の主張こそが数学的内容であり、本質的に**有限**集合についての主張である。同じ方式を自然数の部分集合に適用すると、無限降下が生じる。まず全自然数、次に 1 以上の全体、さらに 2 以上の全体、というように、各歩で生存者の中の最初の点を削り、厳密に低いところへ落ちていく。方式そのものはこれを禁じない。有限の基底でこれを禁じるのは、有限の基底の部分集合が有限個しかなく、したがって最小元を探す探索が必ず終わることである。以下の整礎性の証明はまさにこの方法をとる。有限なリストと線形順序があれば、非空な任意の性質に対し、リストを走査して各歩でそれまでの最小候補を保持することにより最小の要素が得られる。「非空な任意の性質は最小元を持つ」が、古典的には整礎性にほかならない。

有限性は塔を上へと伝播する。有限集合の定義可能部分集合はそのすべての部分集合であり、リストを持つ集合の部分集合は、そのリスト上の各ビットベクトルに一つずつ、有限個しかないからである。よって段階のリストから次の段階のリストが得られ、この帰納だけで構成全体を進められる。

極限段階の構成には、有限段階の順序どうしの整合性を仮定したり証明したりする必要がない。まず要素が初めて現れる段階番号を比較し、番号が等しいときだけ、その段階自身の順序を用いる。したがって異なる段階の要素は段階番号で、同じ段階に初めて現れる要素は局所順序で比較される。
<!--/-->

<!--en-->
The setting is the constructible universe built over the ambient cumulative hierarchy $V$. Excluded middle enters here as an explicit hypothesis: the module is parameterized by a decision `lem` for every proposition at level `ℓ-suc ℓ`. This one level is all the chapter asks for, and every construction below is allowed to call this single fixed decision; nothing is claimed for propositions at other levels beyond what the displayed theorems actually prove.
<!--zh-->
讨论的舞台是建立在累积层级 $V$ 之上的可构造宇宙。排中律在这里作为显式假设出现：整个模块由一个参数 `lem` 给出，它对层级 `ℓ-suc ℓ` 上的每个命题作出判定。本章需要的正是这一个层级，下文的所有构造都可以使用这一固定判定；对于其他层级上的命题，除已证明的定理所述内容外，不作任何论断。
<!--ja-->
舞台となるのは、周囲の累積階層 $V$ の上に構成される構成可能宇宙です。排中律はここで明示的な仮定として現れます。モジュールは、階層 `ℓ-suc ℓ` のすべての命題に対する判定を与えるパラメータ `lem` を受け取ります。本章が必要とするのはこの一つの階層だけで、以下の構成はどれもこの固定された判定を用います。表示されている定理が実際に証明する範囲を超えて、他の階層の命題については何も主張しません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.FiniteStageOrders {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The names used throughout are those of the constructible hierarchy: a stage `Lset α` of the tower, the operator `𝒟ₒ` producing the definable subsets of a stage, and the fact `numeral-ord` that the numeral `# n` is an ordinal. In particular each finite stage `Lset (# n)` is a genuine stage, which is what lets the recursion of later sections climb the numerals. Also imported is `Lset-suc` and the `FinOf` machinery, which ties a stage to the finite sets inside it.
<!--zh-->
下文使用的名称都来自可构造层级：塔的层 `Lset α`、产生一层的全部可定义子集的算子 `𝒟ₒ`，以及数码 `# n` 是序数这一事实 `numeral-ord`。于是每个有限层 `Lset (# n)` 都是真正的层，这正是后续各节的递归能沿数码攀爬的原因。这里还引入了 `Lset-suc` 与 `FinOf` 相关工具，它们把一层与其内部的有穷集合联系起来。
<!--ja-->
以下で使う名前は構成可能階層のものです。塔の段階 `Lset α`、段階の定義可能部分集合を生み出す演算子 `𝒟ₒ`、そして数項 `# n` が順序数であるという事実 `numeral-ord` です。したがって各有限段階 `Lset (# n)` は正真正銘の段階であり、これが後の節の帰納が数項を登れる理由です。ここではさらに `Lset-suc` と `FinOf` の仕組みも取り込み、段階とその内部の有限集合とを結びつけます。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Axioms.Basic {ℓ}
```

<!--en-->
Comparison needs a base order with trichotomy. The order `natOrder` on natural numbers is a strict, strongly well-founded linear order packaged as `SWO`, with a three-case comparison `Tri` split into `lt`, `eq`, `gt`. The search routines of later sections are written against this interface, so they work for any `SWO`, and the natural number instance is the one that orders the numerals.
<!--zh-->
比较需要一个满足三分律的基底序。自然数上的序 `natOrder` 是一个严格强良基的线序，打包为 `SWO`，其三情形比较 `Tri` 分为 `lt`、`eq`、`gt` 三种。后面各节的搜索程序都针对这一接口编写，因此适用于任何 `SWO`；而自然数的实例正是用来给数码排序的那一个。
<!--ja-->
比較には三分律を満たす基底順序が必要です。自然数上の順序 `natOrder` は、厳格で強整礎な線形順序であり、`SWO` としてまとめられ、その三つの場合の比較 `Tri` は `lt`、`eq`、`gt` に分かれます。後の節の探索手続きはこのインターフェースに対して書かれているため、任意の `SWO` に適用でき、自然数の実例が数項を順序づけるものになります。
<!--/-->

```agda
  using ( finSet; finSet-in; finSet-out; Lset-suc; module FinOf )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; leastOf; natOrder )

open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Data.Nat using ( _+_ )
```

<!--en-->
Booleans enter as masks: to enumerate the subsets of a tallied set, each entry is either kept or dropped, recorded by `true` or `false` on `Bool`, where `false≢true` distinguishes the two. On the index side, natural numbers are compared with the strict order `_<_`, which is transitive and well-founded, admits no loops by `¬m<m`, and is decidable via `_≟_`. These are precisely the properties needed to find the least index witnessing a property, and to make head-on decisions inside a scan.
<!--zh-->
布尔值在这里作为掩码出现：要枚举带点名册的集合的子集，就把每个条目保留或丢弃，用 `Bool` 上的 `true` 或 `false` 记录，而 `false≢true` 保证二者可区分。在索引一侧，自然数用严格序 `_<_` 比较，它是传递且良基的，由 `¬m<m` 排除自环，并可用 `_≟_` 判定相等。这些恰好是找出见证某性质的最小下标所需的性质，也是扫描中作出逐步判定所需的性质。
<!--ja-->
ブール値はマスクとして登場します。数え上げられた集合の部分集合を列挙するには、各項目を保持するか捨てるかを `Bool` の `true` か `false` で記録し、`false≢true` が両者を区別します。添字の側では、自然数を厳格順序 `_<_` で比較します。これは推移的かつ整礎で、`¬m<m` によりループを排除し、`_≟_` で判定可能です。これらは、ある性質を証拠立てる最小の添字を見つけるため、また走査の中で各歩の判定を下すために、まさに必要となる性質です。
<!--/-->

```agda
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
```

<!--en-->
Well-foundedness here is the accessibility predicate `Acc`: a point is accessible when every predecessor is accessible, packaged by the constructor `acc`. A relation is well-founded, of type `WellFounded`, when all its points are accessible. The proof obligations from `Acc` are propositions, which is recorded by `isPropAcc` and used when eliminating merely existential data into an accessibility statement. The module `WFI` supplies the recursion principle that consumes a well-founded relation.
<!--zh-->
这里的良基性由可达性谓词 `Acc` 表达：一个点是可达的，当且仅当它的每个前驱都可达，由构造子 `acc` 封装。当关系的一切点都可达时，称它具有 `WellFounded` 类型。`Acc` 上的证明义务都是命题，这一事实由 `isPropAcc` 记录，并在从「仅仅存在」的数据消去到可达性陈述时用到。模块 `WFI` 提供消费良基关系的递归原理。
<!--ja-->
ここでの整礎性は、到達可能性の述語 `Acc` で表されます。ある点が到達可能であるのはそのすべての先行元が到達可能なときであり、構成子 `acc` でまとめられます。関係のすべての点が到達可能なとき、その関係は型 `WellFounded` を持ちます。`Acc` に関する証明義務は命題であり、この事実は `isPropAcc` として記録され、「単に存在する」データから到達可能性の主張への除去に使われます。モジュール `WFI` は整礎な関係を消費する帰納原理を提供します。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; isPropAcc; module WFI )
```

<!--en-->
For a set `x` in the cumulative hierarchy, `⟪ x ⟫` is its small presentation type and `⟪ x ⟫↪` embeds that type into the hierarchy. The equivalence `∈∈ₛ` relates presentation membership to hierarchy membership, while `∈-asFiber` recovers an index and its identifying path from a membership proof. The empty set supplies stage zero, and the von Neumann numerals `# n` with their limit `ω` index the finite stages and their limit.
<!--zh-->
对累积层级中的集合 `x`，`⟪ x ⟫` 是它的小呈现类型，`⟪ x ⟫↪` 把该类型嵌入层级。等价 `∈∈ₛ` 联系呈现中的成员关系与层级成员关系，`∈-asFiber` 则从成员证明恢复索引及其等同路径。空集给出第零层，冯·诺伊曼数码 `# n` 及其极限 `ω` 用来索引诸有穷层与极限。
<!--ja-->
累積階層の集合 `x` に対し、`⟪ x ⟫` はその小さな表示型であり、`⟪ x ⟫↪` はその型を階層へ埋め込む。同値 `∈∈ₛ` は表示上の所属と階層の所属を結び、`∈-asFiber` は所属証明から添字とその同一視のパスを取り出す。空集合が零段階を与え、フォン・ノイマン数項 `# n` とその極限 `ω` が有限段階と極限の添字になる。
<!--/-->

```agda
open import Cubical.Relation.Nullary using ( isProp¬ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
```

<!--en-->
Membership statements below are proposition-valued. Thus `⟨ x ∈ˢ A ⟩` is the type of evidence that `x` belongs to `A`; tallies use this form both to certify each listed entry and to state that every member is represented.
<!--zh-->
下文的隶属陈述取命题为值。因此，`⟨ x ∈ˢ A ⟩` 是 `x` 属于 `A` 的证据类型；点名册用这一形式证明每个列出项确实属于集合，并陈述每个成员都被表示。
<!--ja-->
以下の所属命題は命題に値を取る。したがって `⟨ x ∈ˢ A ⟩` は `x` が `A` に属する証拠の型であり、数え上げはこの形を、各項の所属の証明と全要素が表現されるという主張の双方に用いる。
<!--/-->

```agda
open InfinitySet using ( #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Tallies

A `Tally`{.Agda} presents every member of a set by a finite indexed family, allowing repetitions and requiring neither injectivity nor decidable equality.

Finiteness enters as a **tally**: a number, a family of that many sets all belonging to `A`, and the statement that every member of `A` is merely one of them. `onto` records that every member is merely represented in the family.

Repetitions and undecidable equality cause no difficulty. A scan may revisit the same element, and a bit vector records choices by position even when two positions name the same set. This deliberately weak finiteness notion is therefore stable under the construction of the next stage.
<!--zh-->
## 点名册

`Tally`{.Agda} 用一个有穷索引族呈现集合的每个成员，允许重复，也不要求单射性或可判定相等。

有穷性以**点名册**的形式引入：取一个数和一个由相应多个集合组成的族，族中的每个集合都属于 `A`，并要求「`A` 的每个成员都仅仅等于其中某一个」。`onto` 表示该族列出了 `A` 的所有成员。

重复与不可判定的相等都不造成困难。扫描可以再次遇到同一元素，位向量也按位置记录取舍，即使两个位置名指同一集合亦然。因此，这种刻意保持较弱的有穷性概念能在下一层的构造中保持下去。
<!--ja-->
## 有限な数え上げ

`Tally`{.Agda} は集合の全要素を有限添字族で提示し、重複を許し、単射性も決定可能な等しさも要求しない。

有限性は**数え上げ**として導入されます。それは、一つの数、その個数だけの集合からなりすべて `A` に属する族、そして「`A` のすべての要素はそれらのうちのどれかである」という主張です。`onto` は、すべての要素がこの族の中に単に表現されていることを記録します。

重複も等しさの決定不能性も問題にならない。走査は同じ要素を再び訪れてよく、二つの位置が同じ集合を指していても、ビットベクトルは位置ごとに選択を記録できる。したがって、この意図的に弱い有限性の概念は次の段階の構成で保たれる。
<!--/-->

<!--en-->
A tally of a set `A` has three data fields. The number `size` fixes how many entries are listed, and `item` turns each valid position, an element of `Fin size`, into a set `item i`. The field `inside` certifies that every listed entry genuinely belongs to `A`; without it, a longer list would trivially cover a small set. Note that the same element may well appear at several positions: the record does not prevent this, and no field asks whether two positions hold the same set.
<!--zh-->
集合 `A` 的点名册有三个数据字段：数 `size` 决定列出的条目数，`item` 把每个合法位置 (即 `Fin size` 的元素) 映为集合 `item i`，而字段 `inside` 证明每个被列出的条目确实属于 `A`。没有这一条，更长的清单会平凡地覆盖较小的集合。注意同一元素完全可能出现在多个位置上：record 并不禁止这一点，也没有任何字段询问两个位置上的集合是否相同。
<!--ja-->
集合 `A` の数え上げは三つのデータ欄を持ちます。数 `size` が列挙する項目数を決め、`item` が各正当な位置、すなわち `Fin size` の要素を集合 `item i` に対応させ、欄 `inside` が列挙された各項目が実際に `A` に属することを証明します。これがなければ、長いリストは小さな集合を自明に被覆してしまいます。同じ要素が複数の位置に現れても構いません。record はそれを禁じず、二つの位置の集合が等しいかを尋ねる欄もありません。
<!--/-->

```agda
record Tally (A : S) : Type (ℓ-suc ℓ) where
  field
    size   : ℕ
    item   : Fin size → S
    inside : (i : Fin size) → ⟨ item i ∈ˢ A ⟩
```

<!--en-->
The fourth field states coverage. Given `x` together with a proof that it belongs to `A`, `onto` returns the propositional truncation of an index `i` and a path `item i ≡ x`. Thus an index exists merely, without exposing a chosen position. Later eliminations use this truncated witness only when their targets are propositions.
<!--zh-->
第四个字段陈述覆盖性。给定 `x` 及其属于 `A` 的证明，`onto` 返回「索引 `i` 配路径 `item i ≡ x`」的命题截断。因此，只能得到某个索引仅仅存在，而不会暴露一个选定位置。后文只在目标为命题时消去这份截断见证。
<!--ja-->
第四の欄は被覆を述べる。`x` とその `A` への所属証明から、`onto` は添字 `i` とパス `item i ≡ x` の命題的切断を返す。したがって添字は単に存在するだけで、選ばれた位置は外へ現れない。後では、この切断された証人を目標が命題である場合にだけ除去する。
<!--/-->

```agda
    onto   : (x : S) → ⟨ x ∈ˢ A ⟩ → ∥ Σ[ i ∈ Fin size ] (item i ≡ x) ∥₁
```

<!--en-->
## Splitting a finite index

The maps `splitFin`{.Agda} and `joinFin`{.Agda} identify an index below a sum with an index in one summand, supplying the arithmetic used to enumerate masks.

Tallying a power set means enumerating bit vectors, and there are twice as many vectors of length `n + 1` as of length `n`. So one piece of index arithmetic is needed: an index below `a + b` is either an index below `a` or an index below `b`, and conversely. Only one of the two round trips is ever used, so only that one is proved; `bumpLeft` is the shift that makes the recursion on `a` type-check.

A concrete picture helps. If `a = 2` and `b = 3`, an index below `5` is exactly either an index below `2` or one below `3`: `joinFin` sends the left summand to the first two slots and the right summand to the last three, while `splitFin` asks which zone an index fell into. Repetitions are irrelevant here, since these maps concern positions, not the entries that later sit at them.
<!--zh-->
## 劈开一个有穷索引

`splitFin`{.Agda} 与 `joinFin`{.Agda} 把小于和数的索引与某个加数中的索引对应起来，提供枚举掩码所需的算术。

为幂集清点需要枚举位向量，而长度为 `n + 1` 的向量个数是长度为 `n` 的两倍。因此需要一项索引算术：小于 `a + b` 的索引对应于小于 `a` 的索引或小于 `b` 的索引，反之亦然。后文只使用其中一个方向，所以这里只证明该方向；`bumpLeft` 是使沿 `a` 的递归通过类型检查所需的移位。

一个具体的图景有帮助。取 `a = 2`、`b = 3`，小于 `5` 的索引恰好等于「小于 `2` 的索引或小于 `3` 的索引」：`joinFin` 把左加数放进前两个位置、把右加数放进后三个位置，而 `splitFin` 询问一个索引落入哪个区域。这里与重复无关，因为这两张图关心的是位置，而不是日后放在位置上的条目。
<!--ja-->
## 有限添字を分割する

`splitFin`{.Agda} と `joinFin`{.Agda} は和より小さい添字を一方の加数の添字に対応させ、マスクの列挙に必要な算術を与える。

冪集合を数え上げることはビットベクトルを列挙することであり、長さ `n + 1` のベクトルの個数は長さ `n` のもののちょうど二倍です。そこで一つの添字算術が必要になります。`a + b` より小さい添字とは、`a` より小さい添字か `b` より小さい添字のどちらかであり、逆も成り立ちます。往復のうち片方向しか後で使われないため、その方向だけが証明されます。`bumpLeft` は `a` 上の再帰が型検査を通るようにするずらしです。

具体的な図が助けになります。`a = 2`、`b = 3` とすると、`5` より小さい添字とは「`2` より小さい添字か `3` より小さい添字」のいずれかにほかなりません。`joinFin` は左の加数を最初の二つの枠に、右の加数を残り三つの枠に送り、`splitFin` は一つの添字がどちらの領域に落ちたかを尋ねます。ここで重複は無関係です。これらの写像は位置についてのものであり、後にそこへ置かれる項目についてのものではないからです。
<!--/-->

<!--en-->
The first map concerns sums whose left side grows by one. `bumpLeft` takes an index in either `a` or `b` and produces an index in `suc a` or `b`: a left index is pushed one slot further out, a right index is left alone. It has no content of its own; it exists so that the recursive step of `splitFin`, which peels one slot off the left summand, can restore a left index to the right type. Note `joinFin` is stated only in the direction from `Fin a ⊎ Fin b` to `Fin (a + b)`, with `a` explicit so the recursion can pattern-match on it.
<!--zh-->
第一张图处理左端增加一的和。`bumpLeft` 取一个属于 `a` 或 `b` 的索引，给出一个属于 `suc a` 或 `b` 的索引：左边的索引被外推一格，右边的原样保留。它本身没有内容，存在的原因只是 `splitFin` 的递归步会从左加数剥掉一格，需要一个移位把左索引放回正确的类型。注意 `joinFin` 只给出了从 `Fin a ⊎ Fin b` 到 `Fin (a + b)` 的方向，且 `a` 显式给出，以便递归能对它作模式匹配。
<!--ja-->
最初の写像は、左側が一つ伸びる和に関するものです。`bumpLeft` は `a` か `b` のいずれかの添字を受け取り、`suc a` か `b` のいずれかの添字を返します。左の添字は一つ先へずらされ、右の添字はそのままです。それ自体には内容はなく、`splitFin` の再帰の各歩が左の加数から一つを剥がすため、左の添字を正しい型へ戻すずらしが必要だというだけのものです。`joinFin` は `Fin a ⊎ Fin b` から `Fin (a + b)` への方向だけが与えられ、`a` は再帰がパターン照合できるよう明示されている点にも注意してください。
<!--/-->

```agda
bumpLeft : {a b : ℕ} → Fin a ⊎ Fin b → Fin (suc a) ⊎ Fin b
bumpLeft (inl i) = inl (suc i)
bumpLeft (inr j) = inr j

joinFin : (a : ℕ) {b : ℕ} → Fin a ⊎ Fin b → Fin (a + b)
joinFin zero    (inr j)       = j
```

<!--en-->
`joinFin` and `splitFin` are mutual inverses in shape, though only one round trip will be proved. `joinFin` is recursive in `a`: at `zero` an index below `0 + b` is just an index below `b`, and at a successor the first slot belongs to the left summand, so a left index at position zero maps to slot zero and everything else shifts up by one. `splitFin` runs the same recursion backwards: an index below `a + b` first asks whether it is below `a`, and the `suc` case uses `bumpLeft` to restore the peeled type.
<!--zh-->
`joinFin` 与 `splitFin` 形状上互为逆映射，不过后文只证明一个方向的往返。`joinFin` 沿 `a` 递归：`a` 为零时，小于 `0 + b` 的索引就是小于 `b` 的索引；`a` 为后继时，第一个位置属于左加数，于是位置为零的左索引映到零号位置，其余一律上移一格。`splitFin` 沿同一递归倒着走：小于 `a + b` 的索引先问它是否小于 `a`，后继情形用 `bumpLeft` 恢复被剥掉的类型。
<!--ja-->
`joinFin` と `splitFin` は形の上では互いの逆ですが、証明される往復は一方向だけです。`joinFin` は `a` 上の再帰です。`a` が零のとき、`0 + b` より小さい添字はそのまま `b` より小さい添字であり、後者のときは最初の枠が左の加数に属するので、位置零の左の添字は零番の枠へ写り、残りはすべて一つ上へずれます。`splitFin` は同じ再帰を逆向きにたどります。`a + b` より小さい添字はまず `a` より小さいかを問い、後者の場合は `bumpLeft` で剥がされた型を復元します。
<!--/-->

```agda
joinFin (suc a) (inl zero)    = zero
joinFin (suc a) (inl (suc i)) = suc (joinFin a (inl i))
joinFin (suc a) (inr j)       = suc (joinFin a (inr j))

splitFin : (a : ℕ) {b : ℕ} → Fin (a + b) → Fin a ⊎ Fin b
splitFin zero    j       = inr j
```

<!--en-->
The round trip `split-join` says that splitting an index that was just joined returns the original left-or-right index. Every clause is either `refl` or a application of `cong` to the recursive path: the computation of `splitFin (joinFin x)` already reduces to `bumpLeft` applied to the recursive answer, and `cong bumpLeft` carries the induction hypothesis through that shift. The opposite composite is never claimed, and nothing here asserts that joining is injective.
<!--zh-->
往返 `split-join` 说的是：对刚刚拼合的索引再作劈分，就回到原来的左或右索引。每条子句要么是 `refl`，要么是对递归路径施用 `cong`：`splitFin (joinFin x)` 的计算已经归约到对递归答案施加 `bumpLeft`，而 `cong bumpLeft` 把归纳假设穿过这一移位。相反的复合从未被断言，这里也没有任何关于「拼合是单射」的主张。
<!--ja-->
往復 `split-join` は、つねに合されたばかりの添字を分割すればもとの左か右かの添字に戻る、という主張です。各節は `refl` か再帰呼び出しに対する合同性のどちらかです。`splitFin (joinFin x)` の計算はすでに再帰の答えへの `bumpLeft` の適用に簡約され、`cong bumpLeft` がそのずらしを通して帰納仮定を運びます。逆向きの合成は主張されず、ここでは合が単射であるという主張も一切ありません。
<!--/-->

```agda
splitFin (suc a) zero    = inl zero
splitFin (suc a) (suc i) = bumpLeft (splitFin a i)

split-join : (a : ℕ) {b : ℕ} (x : Fin a ⊎ Fin b) → splitFin a (joinFin a x) ≡ x
split-join zero    (inr j)       = refl
split-join (suc a) (inl zero)    = refl
```

<!--en-->
What this buys for the mask section is exact bookkeeping of sizes. When the enumeration of masks at length `suc n` splits its index in half at `maskCount n`, `splitFin` decides whether the leading bit is `false` or `true` and hands the remaining index to the recursion at `n`, where `mask-onto` and `split-join` together show that every bit vector is reached.
<!--zh-->
这一算术给掩码一节带来的是对规模的精确记账。当长度 `suc n` 的掩码枚举在 `maskCount n` 处把索引一分为二时，`splitFin` 判定首位是 `false` 还是 `true`，并把剩下的索引交给 `n` 处的递归；`mask-onto` 与 `split-join` 合起来证明每个位向量都被触及。
<!--ja-->
この算術がマスクの節にもたらすのは、規模の正確な簿記です。長さ `suc n` のマスクの列挙が `maskCount n` で添字を半分に分けるとき、`splitFin` が先頭ビットが `false` か `true` かを決め、残りの添字を `n` での再帰に渡します。そこで `mask-onto` と `split-join` が合わさって、すべてのビットベクトルが届くことを示します。
<!--/-->

```agda
split-join (suc a) (inl (suc i)) = cong bumpLeft (split-join a (inl i))
split-join (suc a) (inr j)       = cong bumpLeft (split-join a (inr j))
```

<!--en-->
## Enumerating the masks

`maskAt`{.Agda} enumerates every Boolean vector of a fixed length, and `mask-onto`{.Agda} proves that every selection pattern occurs.

A **mask** of length `n` is a vector of `n` bits; it will say, of a tallied set, which entries to keep. There are `maskCount n` of them, that number being two to the `n` written as an iterated doubling, and `maskAt` reads an index as a mask: split the index in half, and the half it lands in supplies the leading bit while the rest supplies the tail. Every mask is read off some index, which is `mask-onto`, and that is the only property of the enumeration that is needed. No pointwise injectivity property is required.

For `n = 2`, the four indices give the four masks from `false ∷ false ∷ []` through `true ∷ true ∷ []`. The construction in fact enumerates them without repetition, although the later tally argument needs only the proved coverage `mask-onto` and does not rely on injectivity.
<!--zh-->
## 枚举掩码

`maskAt`{.Agda} 枚举固定长度的全部布尔向量，而 `mask-onto`{.Agda} 证明每种选取模式都会出现。

长度为 `n` 的**掩码**是一个 `n` 位向量；对已经清点的集合，它指明保留哪些条目。共有 `maskCount n` 个掩码，即二的 `n` 次幂，这里写成反复加倍的形式。`maskAt` 把索引解释为掩码：按索引属于两个加数中的哪一支确定首位，再由该支中的剩余索引确定尾部。每个掩码都由某个索引得到，这就是 `mask-onto`，也是后文使用该枚举所需的唯一性质；该枚举不要求逐点单射。

取 `n = 2`，四个索引给出从 `false ∷ false ∷ []` 到 `true ∷ true ∷ []` 的四个掩码。这个构造事实上无重复地枚举它们；不过后面的点名册论证只使用已证明的覆盖性 `mask-onto`，并不依赖单射性。
<!--ja-->
## マスクを列挙する

`maskAt`{.Agda} は固定長のすべてのブール・ベクトルを列挙し、`mask-onto`{.Agda} は各選択パターンが現れることを証明する。

長さ `n` の**マスク**とは `n` ビットのベクトルであり、数え上げられた集合についてどの項目を残すかを指示します。その個数は `maskCount n`、すなわち繰り返し二倍として書かれた 2 の `n` 乗です。`maskAt` は添字をマスクとして読みます。添字を半分に分け、どちらの半分に落ちたかで先頭ビットが決まり、残りが尾を与えます。すべてのマスクがなんらかの添字から読み出されること、これが `mask-onto` であり、この列挙について必要とされる唯一の性質です。逐点的な単射性は要求されません。

`n = 2` では、四つの添字が `false ∷ false ∷ []` から `true ∷ true ∷ []` までの四つのマスクを与える。この構成は実際には重複なく列挙するが、後の数え上げの議論が用いるのは証明済みの被覆 `mask-onto` だけであり、単射性には依存しない。
<!--/-->

<!--en-->
The count of masks is defined by the recursion it will be enumerated with: length zero admits exactly one mask, and a mask of length `suc n` is a leading bit together with a mask of length `n`, giving the sum `maskCount n + maskCount n`. This is two to the `n` written as iterated doubling, which is exactly the shape `splitFin` expects, since both numbers being added are the same.
<!--zh-->
掩码的计数按「将来枚举它的那个递归」来定义：长度为零恰有一个掩码；长度为 `suc n` 的掩码是一个首位加上一个长度为 `n` 的掩码，故计数为 `maskCount n + maskCount n`。这就是写成反复加倍形式的二的 `n` 次幂，而两个加数相同，恰好正是 `splitFin` 所期待的形状。
<!--ja-->
マスクの個数は、それを列挙する再帰そのものに沿って定義されます。長さ零のマスクはちょうど一つ、長さ `suc n` のマスクは先頭ビットと長さ `n` のマスクの組であり、個数は `maskCount n + maskCount n` となります。これは繰り返し二倍として書かれた 2 の `n` 乗であり、加えられる二つの数が等しいので、`splitFin` が期待する形に正確に一致します。
<!--/-->

```agda
maskCount : ℕ → ℕ
maskCount zero    = 1
maskCount (suc n) = maskCount n + maskCount n

maskCons : (n : ℕ) → (Fin (maskCount n) → Vec Bool n)
         → Fin (maskCount n) ⊎ Fin (maskCount n) → Vec Bool (suc n)
```

<!--en-->
`maskCons` glues a leading bit onto a tail read from the appropriate half of the index, choosing `false` for the left summand and `true` for the right. `maskAt` then reads an index as a mask: at length zero the only mask is the empty vector, and at length `suc n` the index below `maskCount (suc n) = maskCount n + maskCount n` is split in half, the half naming the leading bit and the inner index naming the tail. The reading is a definition, not a theorem: it simply computes.
<!--zh-->
`maskCons` 把一个首位接到从索引相应半支读出的尾部上：左加数取 `false`，右加数取 `true`。于是 `maskAt` 把索引读成掩码：长度为零时唯一的掩码是空向量；长度为 `suc n` 时，小于 `maskCount (suc n) = maskCount n + maskCount n` 的索引被一分为二，所在的半支给出首位，内层索引给出尾部。这个读法是一个定义而非定理：它只是按规则计算。
<!--ja-->
`maskCons` は先頭ビットを、添字の対応する半分から読んだ尾に接ぎます。左の加数なら `false`、右なら `true` を選びます。そして `maskAt` が添字をマスクとして読みます。長さ零では唯一のマスクは空ベクトル、長さ `suc n` では `maskCount (suc n) = maskCount n + maskCount n` より小さい添字が半分に分けられ、落ちた半分が先頭ビットを、内側の添字が尾を名指します。この読みは定理ではなく定義であり、ただ計算するだけのものです。
<!--/-->

```agda
maskCons n r (inl j) = false ∷ r j
maskCons n r (inr j) = true  ∷ r j

maskAt : (n : ℕ) → Fin (maskCount n) → Vec Bool n
maskAt zero    j = []
maskAt (suc n) j = maskCons n (maskAt n) (splitFin (maskCount n) j)
```

<!--en-->
Coverage is the content of `mask-onto`, and it is deliberately untruncated: given a vector `v`, the statement produces an actual index together with a path from the mask read there to `v`. At the base the empty vector comes from the zeroth index. The recursion follows the vector itself, so the enumeration can deliver this explicit index rather than only its mere existence.
<!--zh-->
覆盖性是 `mask-onto` 的内容，而它有意不带截断：给定一个向量 `v`，该陈述产生一个真实的索引，连同从该索引读出的掩码到 `v` 的路径。基情形中，空向量来自第零号索引。这是整个枚举中唯一必须交付数据而非仅仅存在性的地方，而它之所以能做到，是因为递归沿着向量本身进行。
<!--ja-->
被覆こそが `mask-onto` の内容であり、ここでは意図的に切断を行いません。ベクトル `v` が与えられると、この主張は実際の添字と、そこから読んだマスクから `v` への経路とをともに作り出します。基底の場合、空ベクトルは零番の添字から来ます。列挙の中で単なる存在ではなくデータを渡さねばならないのはここだけですが、再帰がベクトルそのものに沿って進むため、それが可能になります。
<!--/-->

```agda

mask-onto : (n : ℕ) (v : Vec Bool n) → Σ[ j ∈ Fin (maskCount n) ] (maskAt n j ≡ v)
mask-onto zero    []          = zero , refl
mask-onto (suc n) (false ∷ v) =
  joinFin (maskCount n) (inl (mask-onto n v .fst))
  , (cong (maskCons n (maskAt n)) (split-join (maskCount n) (inl (mask-onto n v .fst)))
```

<!--en-->
At a successor the vector decides the branch. For a leading `false` the tail's index is joined into the left half by `joinFin`, and the path is assembled in two steps: first `split-join` shows that splitting the joined index recovers the left half as claimed, and then the recursive path is carried under the leading bit by `cong (false ∷_)`. The `true` case is verbatim the same with the right half. Together with the count, this says the masks of a tallied set are covered by `Fin (maskCount size)`, which is exactly the shape a `Tally` field expects.
<!--zh-->
后继情形由向量决定分支。首位为 `false` 时，尾部的索引经 `joinFin` 拼入左半支；路径分两步拼装：先用 `split-join` 证明对拼合索引的劈分确实还原出左半支，再用 `cong (false ∷_)` 把递归得到的路径带上首位。`true` 的情形逐字相同，只是换成右半支。结合计数，这说明已清点集合的掩码被 `Fin (maskCount size)` 覆盖，恰好是 `Tally` 字段所期待的形状。
<!--ja-->
後者の段階ではベクトルが分岐を決めます。先頭が `false` なら、尾の添字は `joinFin` で左半分に合され、経路は二歩で組み立てられます。まず `split-join` によって、合された添字の分割が主張どおり左半分を復元することを示し、次に `cong (false ∷_)` で再帰の経路を先頭ビットの下へ運びます。`true` の場合は右半分に替わるだけで、それ以外はそっくり同じです。個数と合わせて、これは数え上げられた集合のマスクが `Fin (maskCount size)` に被覆されることを意味し、まさに `Tally` の欄が期待する形です。
<!--/-->

```agda
     ∙ cong (false ∷_) (mask-onto n v .snd))
mask-onto (suc n) (true ∷ v)  =
  joinFin (maskCount n) (inr (mask-onto n v .fst))
  , (cong (maskCons n (maskAt n)) (split-join (maskCount n) (inr (mask-onto n v .fst)))
     ∙ cong (true ∷_) (mask-onto n v .snd))
```

<!--en-->
## Selecting a sub-family

`select`{.Agda} filters a finite family by a Boolean mask, while its membership lemmas connect selected entries with the positions marked true.

`select` applies a mask to a family: it keeps the entries whose bit is `true` and returns them as a family again, together with its own length. The length is **produced by the recursion**, which is the point: nothing has to be counted, and no arithmetic relates the answer to the mask.

Two specifications say what the result contains, and both are untruncated, because each is read straight off the same recursion. `marks` runs in the other direction, turning a decision on the entries into the mask that records it.

A small example shows the interaction with repetitions. Take a family with a repeated entry and the mask that keeps both copies: the selection then contains that entry twice, and both copies are answered by the lemmas, each with its own original position. Nothing is lost or merged, because nothing is ever required to be unique.
<!--zh-->
## 选出一个子族

`select`{.Agda} 按布尔掩码筛选一个有穷族，其成员引理则把选中的条目与标为真的位置对应起来。

`select` 把掩码作用到一个族上：它保留那些位为 `true` 的条目，并把它们重新组成一个族，同时给出该族的长度。长度是**由递归产生**的，这正是关键：无须计数，也不需要任何算术把答案与掩码联系起来。

两条规格说明各自刻画结果包含什么，且都不带截断，因为二者都是同一次递归的直接推论。`marks` 的方向相反：它把对诸条目的一次判定变成记录该判定的掩码。

一个小例子显示了与重复的交互。取一个含重复条目的族，并取保留两个副本的掩码：选出的子族便两次含有该条目，两条副本各由引理以各自的原始位置回答。没有任何东西被丢失或合并，因为从来没有任何东西被要求唯一。
<!--ja-->
## 部分族を選び出す

`select`{.Agda} はブール・マスクで有限族を絞り込み、その要素補題は選ばれた項と真に印づけられた位置を対応させる。

`select` はマスクを族に適用します。ビットが `true` の項目を残し、それらを再び族として、その長さとともに返します。長さは**再帰が生み出す**ものであり、これが要点です。何かを数える必要はなく、答えとマスクを結びつける算術も要りません。

二つの仕様が結果に何が含まれるかを述べ、どちらも切断を含みません。どちらも同じ再帰から直接読み取れるからです。`marks` は逆向きに走り、項目への判定を、それを記録するマスクへ変えます。

小さな例が重複との相互作用を示します。同じ項目が二度現れる族と、両方の写しを残すマスクを取ると、選ばれた族はその項目を二度含み、二つの写しはそれぞれ固有のもとの位置とともに補題によって答えられます。何かが失われたり併合されたりすることはありません。一意であることはそもそも要求されていないからです。
<!--/-->

<!--en-->
The helper `selectStep` performs one step of the filter: given an entry `x` and an already-selected family, it prepends `x` and reports the new length `suc k`. Its result type packages the family with its length in a dependent pair, so the recursion can grow the length without ever consulting the mask arithmetically.
<!--zh-->
辅助函数 `selectStep` 完成筛选的一步：给定条目 `x` 与已选好的族，它把 `x` 排在最前并报告新长度 `suc k`。其结果类型把族与长度打包成一个依赖对，于是递归可以增长长度而不必对掩码做任何算术。
<!--ja-->
補助関数 `selectStep` は絞り込みの一歩を行います。項目 `x` とすでに選ばれた族が与えられると、`x` を先頭に付け、新しい長さ `suc k` を報告します。その結果の型は族と長さを依存対としてまとめるため、再帰はマスクに算術を一切用いずに長さを伸ばせます。
<!--/-->

```agda
selectStep : {ℓ' : Level} {X : Type ℓ'} → X → Σ[ k ∈ ℕ ] (Fin k → X)
           → Σ[ k ∈ ℕ ] (Fin k → X)
selectStep {X = X} x (k , g) = suc k , h
  where
  h : Fin (suc k) → X
```

<!--en-->
`select` is a recursion on the mask. The empty mask selects nothing, signaled by an absurd pattern: there is no position in a family of length zero. A leading `false` drops the head and recurses on the shifted family; a leading `true` keeps the head with `selectStep`. At each step the family is shifted by one, which is what the `λ i → f (suc i)` throughout records.
<!--zh-->
`select` 是沿掩码的递归。空掩码什么也不选，用荒谬模式表达：长度为零的族没有任何位置。首位为 `false` 时丢弃头部并沿右移后的族递归；首位为 `true` 时用 `selectStep` 保留头部。每一步族都右移一格，这正是全篇出现的 `λ i → f (suc i)` 所记录的内容。
<!--ja-->
`select` はマスク上の再帰です。空のマスクは何も選ばず、それを荒謬パターンで示します。長さ零の族には位置が存在しないからです。先頭が `false` なら頭を落としてずらした族に再帰し、`true` なら `selectStep` で頭を残します。各歩で族が一つずらされること、これが随所の `λ i → f (suc i)` が記録しているものです。
<!--/-->

```agda
  h zero    = x
  h (suc i) = g i

select : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) → (Fin n → X) → Vec Bool n
       → Σ[ k ∈ ℕ ] (Fin k → X)
select zero    f v           = zero , λ ()
```

<!--en-->
The first specification, `select-out`, reads the selection forwards: every position `j` of the selected family comes from some original position `i` whose bit is `true`, and the entry there really is the original entry `f i`. The claim is data, not a mere existence: an actual witness `i` is produced, with both the bit and the equality given explicitly.
<!--zh-->
第一条规格 `select-out` 顺向读出选取结果：被选族的每个位置 `j` 都来自某个位为 `true` 的原始位置 `i`，且该处的条目确实是原来的条目 `f i`。这一主张是数据而非仅仅的存在性：实际产生一个见证 `i`，位与等式都显式给出。
<!--ja-->
最初の仕様 `select-out` は選択を順方向に読みます。選ばれた族の各位置 `j` は、ビットが `true` であるもとの位置 `i` から来ており、そこにある項目は実際にもとの項目 `f i` です。この主張は単なる存在ではなくデータです。実際の証人が作り出され、ビットも等式も明示的に与えられます。
<!--/-->

```agda
select (suc n) f (false ∷ v) = select n (λ i → f (suc i)) v
select (suc n) f (true ∷ v)  = selectStep (f zero) (select n (λ i → f (suc i)) v)

select-out : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (v : Vec Bool n)
             (j : Fin (select n f v .fst))
           → Σ[ i ∈ Fin n ] ((lookup i v ≡ true) × (select n f v .snd j ≡ f i))
```

<!--en-->
The proof walks the same recursion as the definition. In the `false` case the head is gone, so the original position answering `j` in the tail is shifted up to `suc i` in the full vector; the local `step` performs exactly this bookkeeping on the witness triple.
<!--zh-->
证明沿与定义相同的递归走。`false` 情形中头部已被丢弃，于是在尾部回答 `j` 的原始位置要上移成整向量中的 `suc i`；局部的 `step` 恰好完成对见证三元组的这一簿记。
<!--ja-->
証明は定義と同じ再帰をたどります。`false` の場合は頭が落ちているため、尾で `j` に答えるもとの位置は、全ベクトルでは `suc i` ずり上げられます。局所的な `step` がこの簿記を、証人三つ組に対してまさに行います。
<!--/-->

```agda
select-out zero    f []          ()
select-out (suc n) f (false ∷ v) j       = step (select-out n (λ i → f (suc i)) v j)
  where
  step : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
           × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
```

<!--en-->
In the `true` case there are two subcases. If the selected position is the first, the answer is the head itself, with both equations holding by `refl` because `select` returned the head untouched as slot zero. Otherwise the recursion answers the tail positions, and the same shift applies.
<!--zh-->
`true` 情形分两个子情形。若被选位置是第一个，答案就是头部本身，两条等式都因 `select` 把头部原封不动作为零号位置返回而由 `refl` 成立；否则递归回答尾部的位置，同样的上移照旧适用。
<!--ja-->
`true` の場合は二つの下位の場合に分かれます。選ばれた位置が最初なら、答えは頭そのものであり、`select` が頭をそのまま零番の枠として返すため、二つの等式はともに `refl` で成立します。そうでなければ再帰が尾の位置に答え、同じずらしがそのまま当てはまります。
<!--/-->

```agda
       → Σ[ i ∈ Fin (suc n) ] ((lookup i (false ∷ v) ≡ true)
           × (select (suc n) f (false ∷ v) .snd j ≡ f i))
  step (i , e , q) = suc i , (e , q)
select-out (suc n) f (true ∷ v)  zero    = zero , (refl , refl)
select-out (suc n) f (true ∷ v)  (suc j) = step (select-out n (λ i → f (suc i)) v j)
```

<!--en-->
The second subcase repeats the shift bookkeeping, now with the head present: the selected family of `true ∷ v` is the head followed by the selection of the tail, so a position beyond the head answers in the tail and maps back to `suc i`. The two branches differ only in this relocation, which is why both need their own `step`.
<!--zh-->
第二个子情形重复同样的上移簿记，只是此时头部仍在：`true ∷ v` 的被选族是头部接上尾部的选取结果，因此头部之后的位置在尾部得到回答并映回 `suc i`。两个分支只在这一重定位上不同，这正是它们各自需要一个 `step` 的原因。
<!--ja-->
第二の下位の場合は同じずらしの簿記を、頭がある状態で繰り返します。`true ∷ v` の選ばれた族は頭に尾の選択が続いたものなので、頭より先の位置は尾で答えられ、`suc i` へと写し戻されます。二つの分岐が異なるのはこの配置替えだけであり、だからこそそれぞれに `step` が必要なのです。
<!--/-->

```agda
  where
  step : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
           × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
       → Σ[ i ∈ Fin (suc n) ] ((lookup i (true ∷ v) ≡ true)
           × (select (suc n) f (true ∷ v) .snd (suc j) ≡ f i))
```

<!--en-->
The converse specification, `select-in`, says every marked entry is selected: an original position `i` whose bit is `true` has a selected position `j` whose entry is `f i`. Again the claim is explicit data, an actual `j` together with a path. Nothing is truncated in either direction, which is what lets the later membership arguments pass real witnesses across the selection.
<!--zh-->
反向规格 `select-in` 说每个被标记的条目都被选中：位为 `true` 的原始位置 `i` 拥有一个被选位置 `j`，其条目为 `f i`。同样，这一主张是显式的数据，即一个真实的 `j` 连同一条路径。两个方向都不带截断，这正是后文关于成员性的论证能在选取两侧传递真实见证的原因。
<!--ja-->
逆の仕様 `select-in` は、印づけられた項目はすべて選ばれることを述べます。ビットが `true` であるもとの位置 `i` には、項目が `f i` である選ばれた位置 `j` が対応します。ここでも主張は明示的なデータ、実際の `j` と経路です。どちらの向きも切断を含まないことが、後の所属の議論で選択の両側に実際の証人を渡せる理由です。
<!--/-->

```agda
  step (i , e , q) = suc i , (e , q)

select-in : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (v : Vec Bool n)
            (i : Fin n) → lookup i v ≡ true
          → Σ[ j ∈ Fin (select n f v .fst) ] (select n f v .snd j ≡ f i)
select-in zero    f []          ()      e
```

<!--en-->
Its proof mirrors the recursion from the other end. A position in an empty family is absurd. In a `false` case the head cannot be marked true, so the hypothesis `e` contradicts `false≢true`; a shifted position recurses. In a `true` case the head answers with position zero, and deeper positions recurse.
<!--zh-->
其证明从另一端映照同一递归。空族中的位置是荒谬的。`false` 情形中头部不可能被标为真，故假设 `e` 与 `false≢true` 矛盾；右移后的位置照旧递归。`true` 情形中头部以零号位置作答，更深的位置照旧递归。
<!--ja-->
その証明は同じ再帰を逆向きに映します。空の族の位置は荒謬であり、`false` の場合は頭が真に印づけられることはないので仮定 `e` は `false≢true` と矛盾し、ずらされた位置は再帰します。`true` の場合は頭が零番の位置で答え、より深い位置は再帰します。
<!--/-->

```agda
select-in (suc n) f (false ∷ v) zero    e = Empty.rec (false≢true e)
select-in (suc n) f (false ∷ v) (suc i) e = select-in n (λ i → f (suc i)) v i e
select-in (suc n) f (true ∷ v)  zero    e = zero , refl
select-in (suc n) f (true ∷ v)  (suc i) e = step (select-in n (λ i → f (suc i)) v i e)
  where
```

<!--en-->
The final clause performs the prepend bookkeeping: the position found in the tail becomes `suc j` in the family that now has the head in front, with the entry equality carried through unchanged. Both specifications together say that the selection is neither larger nor smaller than what the mask marked, though nothing asserts the two ways of matching positions are mutually inverse.
<!--zh-->
最后一条子句完成前置的簿记：尾部找到的位置变成现在头部在前的新族中的 `suc j`，条目等式原样保留。两条规格合起来说明选取结果既不比掩码标出的多、也不比它少，尽管没有断言这两种位置对应方式互为逆映射。
<!--ja-->
最後の節は先頭付けの簿記を行います。尾で見つかった位置は、頭が前に付いた族では `suc j` となり、項目の等式はそのまま保たれます。二つの仕様を合わせると、選択はマスクが印づけたものより大きくも小さくもないことが分かりますが、位置の対応の二つの仕方が互いに逆であるという主張はありません。
<!--/-->

```agda
  step : Σ[ j ∈ Fin (select n (λ i → f (suc i)) v .fst) ]
           (select n (λ i → f (suc i)) v .snd j ≡ f (suc i))
       → Σ[ j ∈ Fin (select (suc n) f (true ∷ v) .fst) ]
           (select (suc n) f (true ∷ v) .snd j ≡ f (suc i))
  step (j , q) = suc j , q
```

<!--en-->
`marks` runs the filter in reverse: instead of reading a mask and keeping entries, it takes a Boolean verdict `d` on entries and writes down the mask recording it, one bit per position. The base is the empty vector, and the step asks `d` at the head and recurses on the shifted family.
<!--zh-->
`marks` 把筛选反过来用：它不读掩码来保留条目，而是取一个关于条目的布尔裁决 `d`，并写下记录该裁决的掩码，每个位置一位。基情形是空向量，递归步在头部询问 `d` 并沿右移后的族继续。
<!--ja-->
`marks` は絞り込みを逆向きに使います。マスクを読んで項目を残す代わりに、項目へのブールの判定 `d` を受け取り、それを記録するマスクを書き出します。一位置につき一ビットです。基底は空ベクトルで、ステップは頭で `d` を尋ね、ずらした族に再帰します。
<!--/-->

```agda

marks : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) → (Fin n → X) → (X → Bool) → Vec Bool n
marks zero    f d = []
marks (suc n) f d = d (f zero) ∷ marks n (λ i → f (suc i)) d

marks-lookup : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (d : X → Bool)
               (i : Fin n) → lookup i (marks n f d) ≡ d (f i)
```

<!--en-->
`marks-lookup` certifies that the recorded mask really answers the verdict at each position: looking up position `i` in `marks n f d` gives `d (f i)`. The head case is `refl` by the computation rule of `marks`, and deeper positions recurse. This lemma is what lets `maskOf` later prove that the mask it writes down reproduces a given subset.
<!--zh-->
`marks-lookup` 证明记录下的掩码确实在每个位置回答裁决：在 `marks n f d` 的位置 `i` 处查询得到 `d (f i)`。头部情形由 `marks` 的计算规则得 `refl`，更深的位置照旧递归。有了这条引理，后面的 `maskOf` 才能证明它写下的掩码重现给定的子集。
<!--ja-->
`marks-lookup` は、記録されたマスクが各位置で判定に正しく答えることを裏付けます。`marks n f d` の位置 `i` を参照すると `d (f i)` が得られます。頭の場合は `marks` の計算規則により `refl` であり、深い位置は再帰します。この補題があるため、後の `maskOf` が書き出したマスクが与えられた部分集合を再現することを証明できるのです。
<!--/-->

```agda
marks-lookup (suc n) f d zero    = refl
marks-lookup (suc n) f d (suc i) = marks-lookup n (λ i → f (suc i)) d i
```

<!--en-->
## A truth value, decided into a bit

Excluded middle turns each proposition into the Boolean bit used by a mask, and the two specifications recover truth and falsity from that bit.

The excluded middle hands over a disjunction, while a mask requires a bit, so the two have to be connected. The verdict is taken as an argument rather than looked up inside the definition: that is what lets the two round-trip lemmas be proved by matching on it, with the truth value itself supplied explicitly so that the round-trip statement has the intended proposition as its parameter.

This conversion is one concrete use of excluded middle in the tally construction: it decides a membership proposition and records the answer as a bit.
<!--zh-->
## 把一个真值判定成一位

排中律把每个命题化为掩码所用的布尔位，而两条规格从该位分别读回真与假。

排中律给出的是一个析取，而掩码需要的是一位，故须把二者衔接起来。裁决作为实参显式传入，而不是在定义内部求解：正是这一点使两条来回引理能靠对它作模式匹配来证明；真值本身也显式给出，使来回规格以预期命题为参数。

这一转换是排中律在点名册构造中的一个具体用途：判定一条成员命题，再把答案记录为一位。
<!--ja-->
## 真理値を一ビットに決定する

排中律は各命題をマスクで使うブール値へ変え、二つの仕様はそのビットから真と偽をそれぞれ読み戻す。

排中律が渡すのは論理和であり、マスクが必要とするのは一ビットです。そこで両者をつなぐ必要があります。判定は定義の内部で求めるのではなく実引数として受け取ります。これにより二つの往復補題は判定に対する照合で証明でき、真理値そのものも明示的に与え、往復の仕様が意図した命題を引数に取るようにします。

この変換は、数え上げの構成における排中律の具体的な用途の一つである。所属命題を判定し、その答えを一ビットとして記録する。
<!--/-->

<!--en-->
`decideOf` turns a verdict into a bit: the left alternative, a proof of `⟨ P ⟩`, is recorded as `true`, and the right, a refutation of `⟨ P ⟩`, as `false`. The proposition `P` itself is irrelevant to the computation; only the verdict is matched, which is why the definition is a pair of equations rather than a proof.
<!--zh-->
`decideOf` 把裁决变成一位：左支是 `⟨ P ⟩` 的证明，记为 `true`；右支是 `⟨ P ⟩` 的反驳，记为 `false`。命题 `P` 本身与计算无关，被匹配的只是裁决，因此这个定义是一对方程而非证明。
<!--ja-->
`decideOf` は判定を一ビットへ変えます。左の選択肢、すなわち `⟨ P ⟩` の証明は `true` として記録され、右の選択肢、`⟨ P ⟩` の反証は `false` となります。命題 `P` 自体は計算に関係せず、照合されるのは判定だけです。だからこそこの定義は一組の等式であって証明ではありません。
<!--/-->

```agda
decideOf : (P : Ω) → (⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → Bool
decideOf P (inl _) = true
decideOf P (inr _) = false

decide-true : (P : Ω) (s : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → ⟨ P ⟩ → decideOf P s ≡ true
decide-true P (inl _)  p = refl
```

<!--en-->
The two round trips connect the bit back to the truth value. `decide-true` says a proof of `⟨ P ⟩` forces the bit to be `true`: in the refutation branch the proof itself would be refuted, which is a contradiction. `decide-sound` reads the other way: a bit of `true` yields a proof of `⟨ P ⟩`, taken directly from the left branch or obtained because the right branch would force `false ≡ true`. Together they say the bit faithfully answers whether `⟨ P ⟩` holds, for the verdict that was passed in.
<!--zh-->
两条往返把位接回真值。`decide-true` 说 `⟨ P ⟩` 的证明迫使该位为 `true`：在反驳支中这个证明本身会被反驳，那正是矛盾。`decide-sound` 反向读出：位为 `true` 便给出 `⟨ P ⟩` 的证明，或直接取自左支，或因右支会迫使 `false ≡ true` 而得。合起来，它们说明对于传入的那个裁决，该位忠实地回答 `⟨ P ⟩` 是否成立。
<!--ja-->
二つの往復がビットを真理値へと結び戻します。`decide-true` は、`⟨ P ⟩` の証明がビットを `true` に強いることを述べます。反証の分岐ではその証明自体が反証され、それが矛盾です。`decide-sound` は逆向きに読みます。ビットが `true` なら `⟨ P ⟩` の証明が得られ、左の分岐から直接取られるか、右の分岐が `false ≡ true` を強いることになるために得られます。合わせて、渡された判定に対してビットが `⟨ P ⟩` の成立を忠実に答えることを示します。
<!--/-->

```agda
decide-true P (inr np) p = Empty.rec (np p)

decide-sound : (P : Ω) (s : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → decideOf P s ≡ true → ⟨ P ⟩
decide-sound P (inl p) _ = p
decide-sound P (inr _) e = Empty.rec (false≢true e)
```

<!--en-->
## The definable subsets of a tallied stage

Finiteness travels up the tower through this section. Fix an ordinal `σ` and a tally of the stage `Lset σ`; the goal is a tally of `𝒟ₒ (Lset σ)`, the definable subsets of that stage. Each entry of the given tally is a member of the stage, hence has a name in the stage's small member type; a mask over the tally selects which names to keep, and `part` spans the kept names into a finite set. By the basic-axioms chapter's `finSet∈𝒟ₒ`, such a spanned set is a definable subset of the stage, defined by the finite disjunction of "equals one of these entries". Conversely, any definable subset `x` of the stage can be recovered: mark each tally entry according to decidable membership in `x`, and the spanned set of that mask is exactly `x`, where the inclusion `𝒟ₒ∋⊆` guarantees that every member of `x` is listed by the tally in the first place. So masks, of which there are `maskCount size`, merely cover all definable subsets, and that is precisely what a `Tally` demands.
<!--zh-->
## 已清点层的可定义子集

有穷性经由本节沿塔逐级传递。固定序数 `σ` 和层 `Lset σ` 的一份点名册，目标是给出 `𝒟ₒ (Lset σ)` (该层可定义子集的全体) 的点名册。已知点名册的每个条目都是该层的成员，因而在该层的小成员类型中有相应的元素；掩码指明保留哪些元素，`part` 把保留的元素张成有穷集。按基本公理一章的 `finSet∈𝒟ₒ`，这样张成的集合是该层的可定义子集，由「等于这些条目之一」的有穷析取定义。反过来，该层的任何可定义子集 `x` 也能被恢复：按每个点名册条目是否属于 `x` 的可判定成员关系加以标记，该掩码张成的集合恰是 `x`，其中包含关系 `𝒟ₒ∋⊆` 保证 `x` 的每个成员本就被点名册列出。于是 `maskCount size` 个掩码仅仅覆盖全部可定义子集，而这正是 `Tally` 所要求的。
<!--ja-->
## 数え上げられた段階の定義可能部分集合

有限性はこの節を通して塔を一段ずつ上ります。順序数 `σ` と段階 `Lset σ` の数え上げを固定し、目標は `𝒟ₒ (Lset σ)` (この段階の定義可能部分集合全体) の数え上げを得ることです。与えられた数え上げの各項目はその段階の要素ですから、段階の小さな要素型の中に対応する名前を持ちます。マスクはどの名前を残すかを指定し、`part` は残った名前を有限集合に張り合わせます。基本公理の章の `finSet∈𝒟ₒ` により、こうして張られた集合はその段階の定義可能部分集合であり、「これらの項目のいずれかに等しい」という有限論理和で定義されます。逆に、段階の任意の定義可能部分集合 `x` も復元できます。各項目を `x` への決定可能な所属関係に従って印づけると、そのマスクで張った集合はちょうど `x` になります。ここで包含 `𝒟ₒ∋⊆` が、`x` の各要素がそもそも数え上げに列挙されていることを保証します。したがって `maskCount size` 個のマスクがすべての定義可能部分集合を単に覆っており、これこそ `Tally` が要求する性質です。
<!--/-->

<!--en-->
A member of `Lset σ` lives in the stage as a set, but `finSet` needs a name in the small member type `⟪ Lset σ ⟫`. The embedding `⟪ Lset σ ⟫↪` reads such a name as a set. Membership is presented as a truncated fiber, but this embedding has proposition-valued fibers, so `∈-asFiber` may eliminate the truncation and return an explicit name together with its path to `item i`. The definitions `index i` and `index-eq i` are the two projections of that fiber element. This does not choose an index from an arbitrary finite tally fiber, whose repetitions need not be proposition-valued.
<!--zh-->
`Lset σ` 的成员作为集合处在该层中，但 `finSet` 需要小成员类型 `⟪ Lset σ ⟫` 中的名字；嵌入 `⟪ Lset σ ⟫↪` 把这种名字读成集合。成员关系呈现为截断原像，不过这个嵌入的原像取值为命题，所以 `∈-asFiber` 可以消去截断，返回一个显式名字及其等同于 `item i` 的路径。`index i` 与 `index-eq i` 正是该原像元素的两个投影。这并非从任意点名册原像中选取索引，因为允许重复的点名册原像未必是命题。
<!--ja-->
`Lset σ` の要素は集合としてその段階にありますが、`finSet` には小さな要素型 `⟪ Lset σ ⟫` の名前が必要です。埋め込み `⟪ Lset σ ⟫↪` はその名前を集合として読みます。所属は切り詰められたファイバーとして提示されますが、この埋め込みのファイバーは命題なので、`∈-asFiber` は切り詰めを消去し、明示的な名前と、それが `item i` に等しいというパスを返せます。`index i` と `index-eq i` は、このファイバー要素の二つの射影です。重複を許す有限な数え上げの任意のファイバーから添字を選ぶこととは異なり、そちらのファイバーは命題とは限りません。
<!--/-->

```agda
module PowerStep (σ : S) (oσ : IsOrd σ) (t : Tally (Lset σ)) where
  open Tally t
  open FinOf σ oσ using ( finSet∈𝒟ₒ )

  index : Fin size → ⟪ Lset σ ⟫
  index i = ∈-asFiber {a = item i} {b = Lset σ} (inside i) .fst
```

<!--en-->
The second component of the same fiber is the path `index-eq i`, recording that the embedded name returns to `item i` along a path, not by a definitional equation. Every later transfer between the set `item i` and the name `index i` will go through this path by transport. With the names in place, a mask `v` over the tally is turned into a selection: `chosen v` is a length together with a function listing exactly the selected names, as built by the earlier `select`.
<!--zh-->
同一纤维的第二个分量是路径 `index-eq i`，它记录嵌入元素经一条路径而非定义等式回到 `item i`。此后在集合 `item i` 与元素 `index i` 之间的每一次转换都要沿这条路径用传输完成。元素就位后，掩码 `v` 被转换为一次选取：`chosen v` 给出一个长度，连同恰好列出被选元素的函数，这由此前的 `select` 构造。
<!--ja-->
同じファイバーの第二成分が経路 `index-eq i` であり、埋め込まれた名前が定義等式ではなく経路を介して `item i` に戻ることを記録します。以後、集合 `item i` と名前 `index i` の間のすべての移し替えは、この経路に沿った輸送を通して行われます。名前がそろったところで、数え上げ上のマスク `v` は選択に変換されます。`chosen v` は長さと、選ばれた名前をちょうど列挙する関数の組であり、以前の `select` が構成したものです。
<!--/-->

```agda

  index-eq : (i : Fin size) → ⟪ Lset σ ⟫↪ (index i) ≡ item i
  index-eq i = ∈-asFiber {a = item i} {b = Lset σ} (inside i) .snd

  chosen : Vec Bool size → Σ[ k ∈ ℕ ] (Fin k → ⟪ Lset σ ⟫)
  chosen v = select size index v

  part : Vec Bool size → S
```

<!--en-->
`part` is the spanned set: it reads each selected name through the embedding and forms the finite set of the results, landing in the type `S` of sets. Because a finite family of members of `Lset σ` spans a definable subset of that stage, `part-def` obtains the certificate `⟨ part v ∈ˢ 𝒟ₒ (Lset σ) ⟩` directly from `finSet∈𝒟ₒ`, with no further work. The first specification then reads membership backwards: if `y` lies in `part v`, then merely there is a tally position whose bit is `true` and whose entry equals `y`.
<!--zh-->
`part` 就是张成的集合：它把每个被选元素经嵌入读出，并取所得结果的有穷集，落在集合类型 `S` 中。由于 `Lset σ` 成员的有穷族张成该层的可定义子集，`part-def` 直接由 `finSet∈𝒟ₒ` 得到证书 `⟨ part v ∈ˢ 𝒟ₒ (Lset σ) ⟩`，无须额外工作。第一条规格从反方向读成员关系：若 `y` 属于 `part v`，则仅仅存在某个点名册位置，其位为 `true` 且其条目等于 `y`。
<!--ja-->
`part` は張り合わせた集合です。選ばれた各名前を埋め込みを通して読み出し、その結果の有限集合を作り、集合の型 `S` に着地します。`Lset σ` の要素からなる有限族はその段階の定義可能部分集合を張るので、`part-def` は `finSet∈𝒟ₒ` から証明書 `⟨ part v ∈ˢ 𝒟ₒ (Lset σ) ⟩` を追加の仕事なしに得ます。最初の仕様は所属を逆向きに読みます。`y` が `part v` に属するなら、ビットが `true` でありその項目が `y` に等しい数え上げの位置が、単に存在するということです。
<!--/-->

```agda
  part v = finSet (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j))

  part-def : (v : Vec Bool size) → ⟨ part v ∈ˢ 𝒟ₒ (Lset σ) ⟩
  part-def v = finSet∈𝒟ₒ (chosen v .fst) (chosen v .snd)

  part-out : (v : Vec Bool size) (y : S) → ⟨ y ∈ˢ part v ⟩
           → ∥ Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (item i ≡ y)) ∥₁
```

<!--en-->
The proof composes two steps. First, `finSet-out` unwraps membership in the spanned finite set: it merely produces a position `j` in the selection with the embedded name equal to `y`. Second, `select-out` traces that position back to its origin in the full tally, recovering the index `i` with `lookup i v ≡ true` and the agreement `chosen v .snd j ≡ index i`. Both steps produce their data inside the truncation, so no chosen witness is extracted from a mere existence claim.
<!--zh-->
证明分两步复合。第一步，`finSet-out` 解开有穷张成集中的成员关系：它仅仅给出选取中的一个位置 `j`，使嵌入元素等于 `y`。第二步，`select-out` 把该位置追回到完整点名册中的来源，恢复索引 `i`，满足 `lookup i v ≡ true` 以及 `chosen v .snd j ≡ index i`。两步的数据都在截断之内产生，因此没有从单纯存在性命题中提取选定的见证。
<!--ja-->
証明は二つの段階を合成します。まず `finSet-out` が張り合わせた有限集合における所属をほどき、選択の中の位置 `j` と、埋め込まれた名前が `y` に等しいことを単に生み出します。次に `select-out` がその位置を完全な数え上げの中での由来までたどり、`lookup i v ≡ true` と `chosen v .snd j ≡ index i` を満たす添字 `i` を回復します。どちらの段階でもデータは截断の中で生み出されるので、単なる存在主張から選ばれた証人が取り出されることはありません。
<!--/-->

```agda
  part-out v y y∈ = PT.map step
    (finSet-out (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j)) y y∈)
    where
    step : Σ[ j ∈ Fin (chosen v .fst) ] (⟪ Lset σ ⟫↪ (chosen v .snd j) ≡ y)
         → Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (item i ≡ y))
```

<!--en-->
The final equality has the source direction `item i ≡ y`. First `sym (index-eq i)` goes from `item i` to the embedded name `index i`. Next, `select-out` gives `chosen v .snd j ≡ index i`, so its symmetry is mapped through the embedding to reach the selected embedded name. Finally the path `q` supplied by finite-set membership reaches `y`. Their concatenation is exactly the three paths displayed in the proof.
<!--zh-->
最后所需等式的方向是 `item i ≡ y`。先沿 `sym (index-eq i)` 从 `item i` 到嵌入后的名字 `index i`。随后 `select-out` 给出 `chosen v .snd j ≡ index i`，取其对称并施加嵌入，便到达选中的嵌入名字。最后，有限集成员关系给出的路径 `q` 到达 `y`。三者的复合正是证明中显示的三段路径。
<!--ja-->
最後に必要な等式の向きは `item i ≡ y` です。まず `sym (index-eq i)` で `item i` から埋め込まれた名前 `index i` へ進みます。次に `select-out` が `chosen v .snd j ≡ index i` を与えるので、その対称を埋め込みの下へ写して、選ばれた埋め込み名へ進みます。最後に有限集合への所属が与えるパス `q` で `y` に到達します。この三つの合成が、証明に表示されたパス列そのものです。
<!--/-->

```agda
    step (j , q) = out .fst
                 , ( out .snd .fst
                   , (sym (index-eq (out .fst))
                      ∙ cong ⟪ Lset σ ⟫↪ (sym (out .snd .snd)) ∙ q) )
      where
```

<!--en-->
The opposite specification runs forward. If the bit at position `i` is `true`, the entry `item i` does belong to `part v`. The reason is that the selection really contains that name: `select-in` finds, for every marked position, a slot in the chosen family holding the same name, and `finSet-in` then certifies membership of the embedded form.
<!--zh-->
相反的规格正向运行。若位置 `i` 处的位为 `true`，则条目 `item i` 确实属于 `part v`。原因在于选取中确实含有该元素：`select-in` 对每个被标记的位置，在被选族中找到一个持有同一元素的槽位，随后 `finSet-in` 证明其嵌入形式的成员关系。
<!--ja-->
逆向きの仕様は順方向に働きます。位置 `i` のビットが `true` なら、項目 `item i` は実際に `part v` に属します。理由は、選択がその名前を本当に含んでいるからです。`select-in` は印づけられた各位置に対して、選ばれた族の中で同じ名前を保持する枠を見つけ、続いて `finSet-in` がその埋め込み形の所属を証明します。
<!--/-->

```agda
      out : Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (chosen v .snd j ≡ index i))
      out = select-out size index v j

  part-mem : (v : Vec Bool size) (i : Fin size) → lookup i v ≡ true
           → ⟨ item i ∈ˢ part v ⟩
  part-mem v i e = subst (λ w → ⟨ w ∈ˢ part v ⟩) path
```

<!--en-->
Since membership in the spanned set is stated for the embedded name while the goal concerns the entry `item i`, the two are connected by the path `path` below, and `subst` moves the membership certificate along it. The auxiliary `ins` holds the slot that `select-in` produces: a position in the chosen family whose entry equals `index i`.
<!--zh-->
由于张成集中的成员关系是针对嵌入元素陈述的，而目标针对条目 `item i`，两者要靠下文的路径 `path` 连接，并用 `subst` 沿该路径搬移成员证书。辅助的 `ins` 保存 `select-in` 给出的槽位：被选族中的一个位置，其条目等于 `index i`。
<!--ja-->
張り合わせた集合における所属は埋め込まれた名前について述べられているのに対し、目標は項目 `item i` に関するので、両者は下の経路 `path` で結ばれ、`subst` がその経路に沿って所属の証明を移します。補助の `ins` は `select-in` が生み出す枠を保持します。選ばれた族の中で、その項目が `index i` に等しい位置です。
<!--/-->

```agda
    (finSet-in (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j))
      (⟪ Lset σ ⟫↪ (chosen v .snd (ins .fst))) ∣ ins .fst , refl ∣₁)
    where
    ins : Σ[ j ∈ Fin (chosen v .fst) ] (chosen v .snd j ≡ index i)
    ins = select-in size index v i e
```

<!--en-->
The remaining path `path` concatenates the slot's equality with `index-eq i`, so the transported membership is exactly membership of `item i`. With both directions in place, the construction can now be run in reverse. `maskOf` assigns to any set `x` the verdict mask obtained by deciding, for each tally entry, whether it belongs to `x`; excluded middle `lem` supplies the disjunction, and `decideOf` turns it into a bit. The goal `part-mask` states that for a definable subset `x` of the stage, the spanned set of this mask is `x` itself.
<!--zh-->
余下的路径 `path` 把槽位的等式与 `index-eq i` 拼接，因此传输后的成员关系正是 `item i` 的成员关系。两个方向就位后，构造可以反向运行。`maskOf` 对任意集合 `x` 给出裁决掩码：对每个点名册条目判定它是否属于 `x`；排中律 `lem` 供给析取，`decideOf` 把它变成一位。目标 `part-mask` 陈述：对该层中的可定义子集 `x`，此掩码张成的集合就是 `x` 本身。
<!--ja-->
残りの経路 `path` は枠の等式と `index-eq i` をつなぎ合わせるので、輸送された所属はまさに `item i` の所属です。両方向がそろったところで、構成を逆向きに走らせます。`maskOf` は任意の集合 `x` に対して、各数え上げの項目が `x` に属するかどうかを判定して得られる判定マスクを割り当てます。排中律 `lem` が論理和を供給し、`decideOf` がそれを一ビットに変えます。目標 `part-mask` は、段階の定義可能部分集合 `x` に対して、このマスクで張った集合が `x` そのものであると述べています。
<!--/-->

```agda
    path : ⟪ Lset σ ⟫↪ (chosen v .snd (ins .fst)) ≡ item i
    path = cong ⟪ Lset σ ⟫↪ (ins .snd) ∙ index-eq i

  maskOf : S → Vec Bool size
  maskOf x = marks size item (λ y → decideOf (y ∈ˢ x) (lem (y ∈ˢ x)))

  part-mask : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset σ) ⟩ → part (maskOf x) ≡ x
```

<!--en-->
Membership in a set of the hierarchy is a proposition, so extensionality `extensionalV` reduces the claimed equality `part (maskOf x) ≡ x` to a pointwise equivalence of membership statements; `⇔toPath` assembles the two directions into the path. The forward direction shows every member of the spanned set lies in `x`.
<!--zh-->
层次中集合的成员关系是命题，因此外延性 `extensionalV` 把所断言的等式 `part (maskOf x) ≡ x` 归约为逐点的成员关系等价；`⇔toPath` 把两个方向组装成路径。正向表明张成集的每个成员都属于 `x`。
<!--ja-->
階層の集合における所属は命題なので、外延性 `extensionalV` は主張された等式 `part (maskOf x) ≡ x` を、所属の主張の各点ごとの同値へと帰着させます。`⇔toPath` が二つの方向を経路へと組み立てます。順方向は、張り合わせた集合の各要素が `x` に属することを示します。
<!--/-->

```agda
  part-mask x x∈ = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
    where
    fwd : (y : S) → ⟨ y ∈ˢ part (maskOf x) ⟩ → ⟨ y ∈ˢ x ⟩
    fwd y y∈ = PT.rec (snd (y ∈ˢ x)) step (part-out (maskOf x) y y∈)
      where
```

<!--en-->
The hypothesis of the forward direction is itself merely an existence: some marked position with entry equal to `y`. Because the target `⟨ y ∈ˢ x ⟩` is a proposition, the truncation may be eliminated into it. The recorded witness is a position `i` whose bit is `true` and whose entry is `y`; since the bit was computed by deciding membership of that very entry in `x`, reading the bit back with `decide-sound` yields membership in `x` for `item i`, and the equality `item i ≡ y` transfers it to `y`.
<!--zh-->
正向的前提本身就是单纯的存在性：某个被标记的位置，其条目等于 `y`。由于目标 `⟨ y ∈ˢ x ⟩` 是命题，截断可以消去到其中。记录的见证是位置 `i`，其位为 `true` 且条目为 `y`；由于该位正是通过判定这个条目是否属于 `x` 算出的，用 `decide-sound` 把位读回即得 `item i` 属于 `x`，再用等式 `item i ≡ y` 把它传输给 `y`。
<!--ja-->
順方向の仮定はそれ自体が単なる存在主張です。ビットが `true` で項目が `y` に等しい位置が何かあるということです。目標 `⟨ y ∈ˢ x ⟩` は命題なので、截断はその中へと消去できます。記録された証人は位置 `i` であり、そのビットは `true` で項目は `y` です。このビットはまさにその項目の `x` への所属を判定して計算されたものですから、`decide-sound` でビットを読み戻せば `item i` の `x` への所属が得られ、等式 `item i ≡ y` によってそれを `y` へと輸送します。
<!--/-->

```agda
      step : Σ[ i ∈ Fin size ] ((lookup i (maskOf x) ≡ true) × (item i ≡ y))
           → ⟨ y ∈ˢ x ⟩
      step (i , e , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) q
        (decide-sound (item i ∈ˢ x) (lem (item i ∈ˢ x))
          (sym (marks-lookup size item
```

<!--en-->
The backward direction starts from membership of `y` in `x` and must produce membership in the spanned set. Since that target is again a proposition, its truncated hypothesis can be eliminated. Here the hypothesis comes from the tally's coverage: `x` is a definable subset of the stage, and `𝒟ₒ∋⊆` says every member of a definable subset of `Lset σ` is a member of `Lset σ` itself, so the tally's `onto` merely lists `y` as some entry `item i`.
<!--zh-->
反向从 `y` 属于 `x` 出发，须产生张成集中的成员关系。由于该目标又是命题，其截断的前提可以消去。这里的前提来自点名册的覆盖：`x` 是该层的可定义子集，而 `𝒟ₒ∋⊆` 说 `Lset σ` 的可定义子集的每个成员都是 `Lset σ` 自身的成员，因此点名册的 `onto` 单纯地把 `y` 列为某个条目 `item i`。
<!--ja-->
逆方向は `y` の `x` への所属から出発し、張り合わせた集合への所属を生み出さねばなりません。この目標も再び命題なので、その截断された仮定は消去できます。ここでの仮定は数え上げの被覆から来ます。`x` は段階の定義可能部分集合であり、`𝒟ₒ∋⊆` は `Lset σ` の定義可能部分集合の各要素が `Lset σ` 自身の要素でもあると言うので、数え上げの `onto` が `y` をある項目 `item i` として単に列挙します。
<!--/-->

```agda
                 (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i) ∙ e))
    bwd : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ part (maskOf x) ⟩
    bwd y y∈x = PT.rec (snd (y ∈ˢ part (maskOf x))) step
      (onto y (𝒟ₒ∋⊆ (Lset σ) x x∈ y y∈x))
      where
```

<!--en-->
Given the entry `i` equal to `y`, it suffices to show `item i` belongs to the spanned set and transport along `item i ≡ y`. By `part-mem`, membership needs the bit at `i` to be `true`. And it is: the mask recorded the decision for `item i ∈ˢ x`, and since `y` belongs to `x`, the path `item i ≡ y` transports that proof so `decide-true` forces the bit to be `true`.
<!--zh-->
给定等于 `y` 的条目 `i`，只需证明 `item i` 属于张成集，并沿 `item i ≡ y` 传输。由 `part-mem`，成员关系需要位置 `i` 的位为 `true`。它确实如此：掩码记录了 `item i ∈ˢ x` 的判定，而由于 `y` 属于 `x`，路径 `item i ≡ y` 把该证明传输过来，`decide-true` 便迫使该位为 `true`。
<!--ja-->
`y` に等しい項目 `i` が与えられれば、`item i` が張り合わせた集合に属することを示し、`item i ≡ y` に沿って輸送すれば十分です。`part-mem` により、所属には位置 `i` のビットが `true` であることが必要です。そして実際そうです。マスクは `item i ∈ˢ x` の判定を記録しており、`y` が `x` に属するので、経路 `item i ≡ y` がその証明を輸送し、`decide-true` がビットを `true` に強制します。
<!--/-->

```agda
      step : Σ[ i ∈ Fin size ] (item i ≡ y) → ⟨ y ∈ˢ part (maskOf x) ⟩
      step (i , q) = subst (λ w → ⟨ w ∈ˢ part (maskOf x) ⟩) q
        (part-mem (maskOf x) i
          (marks-lookup size item (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i
           ∙ decide-true (item i ∈ˢ x) (lem (item i ∈ˢ x))
```

<!--en-->
Both directions of `part-mask` are now assembled, and the section's payoff is at hand. Since every mask arises from some index via `mask-onto`, the masks enumerate, merely and with repetitions allowed, all definable subsets of `Lset σ`. There are `maskCount size` of them, so `powerTally` records a tally with that size, whose entry at index `j` is the spanned set of the mask `maskAt size j`. The remaining fields complete the record: each entry carries its definability certificate, and the coverage clause is supplied next.
<!--zh-->
`part-mask` 的两个方向就此组装完毕，本节的关键成果随之而来。由于每个掩码都经 `mask-onto` 来自某个索引，掩码 (允许重复、单纯地) 枚举了 `Lset σ` 的全部可定义子集。它们共有 `maskCount size` 个，因此 `powerTally` 记录一个该大小的点名册，其在索引 `j` 处的条目是掩码 `maskAt size j` 张成的集合。其余字段补全记录：每个条目附带其可定义性证书，覆盖条款随后给出。
<!--ja-->
`part-mask` の両方向がこれで組み上がり、この節の収穫が目の前にあります。`mask-onto` によりすべてのマスクがある添字から生じるので、マスクは (繰り返しを許して、単に)`Lset σ` のすべての定義可能部分集合を列挙します。その個数は `maskCount size` ですから、`powerTally` はその大きさの数え上げを記録します。添字 `j` における項目は、マスク `maskAt size j` で張った集合です。残りの欄が記録を完成させます。各項目は定義可能性の証明書を伴い、被覆の条項はこの次に与えられます。
<!--/-->

```agda
               (subst (λ w → ⟨ w ∈ˢ x ⟩) (sym q) y∈x)))

  powerTally : Tally (𝒟ₒ (Lset σ))
  powerTally = record
    { size   = maskCount size
    ; item   = λ j → part (maskAt size j)
```

<!--en-->
The record's `inside` field reuses the certificate `part-def` at each enumerated mask, so every entry of `powerTally` is genuinely a definable subset of the stage. It remains to check `onto`, the truncated coverage. Given any definable subset `x` of `Lset σ`, we must merely exhibit an index whose enumerated entry equals `x`.
<!--zh-->
记录的 `inside` 字段在每个被枚举的掩码处复用证书 `part-def`，因此 `powerTally` 的每个条目确实是该层的可定义子集。剩下检查 `onto`，即截断的覆盖性。给定 `Lset σ` 的任意可定义子集 `x`，必须单纯地给出一个索引，其被枚举的条目等于 `x`。
<!--ja-->
記録の `inside` の欄は、列挙された各マスクで証明書 `part-def` を再利用するので、`powerTally` の各項目は実際に段階の定義可能部分集合です。残るは `onto`、つまり截断された被覆の確認です。`Lset σ` の任意の定義可能部分集合 `x` が与えられたとき、列挙された項目が `x` に等しい添字を単に示せばよいことになります。
<!--/-->

```agda
    ; inside = λ j → part-def (maskAt size j)
    ; onto   = cover }
    where
    cover : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset σ) ⟩
          → ∥ Σ[ j ∈ Fin (maskCount size) ] (part (maskAt size j) ≡ x) ∥₁
```

<!--en-->
The witness index is the one that `mask-onto` produces for the verdict mask `maskOf x`. The enumerated entry at that index is `part (maskAt size j)`, which equals `part (maskOf x)` after rewriting the mask along the produced path, and `part-mask` then identifies that with `x`. The whole statement lands in a truncation, which is all a `Tally`'s coverage requires: every definable subset is hit, though not necessarily by a unique mask.
<!--zh-->
见证索引是 `mask-onto` 为裁决掩码 `maskOf x` 产生的那个。该索引处被枚举的条目是 `part (maskAt size j)`，沿所得路径改写掩码后它等于 `part (maskOf x)`，随后 `part-mask` 把它与 `x` 等同。整个命题落在截断之中，这正是 `Tally` 的覆盖性所要求的：每个可定义子集都被命中，尽管未必由唯一的掩码命中。
<!--ja-->
証人となる添字は、判定マスク `maskOf x` に対して `mask-onto` が生み出すものです。その添字で列挙される項目は `part (maskAt size j)` であり、生み出された経路に沿ってマスクを書き換えれば `part (maskOf x)` に等しく、続いて `part-mask` がそれを `x` と同一視します。命題全体が截断の中に着地します。これが `Tally` の被覆が要求するすべてであり、すべての定義可能部分集合が命中するものの、一意なマスクによるとは限りません。
<!--/-->

```agda
    cover x x∈ = ∣ mask-onto size (maskOf x) .fst
                 , (cong part (mask-onto size (maskOf x) .snd) ∙ part-mask x x∈) ∣₁
```

<!--en-->
## Smallest elements, and well-foundedness

This section spends the tally built earlier rather than making one. Fix a type with a relation that is trichotomous, irreflexive and transitive: everything a strict well-order asks for except well-foundedness. The procedure `scan` walks a finite family and returns, without any truncation, either an entry that satisfies the predicate and is smallest among the entries that do, or a refutation showing no entry satisfies it. It is a plain recursion on the length: at each step excluded middle decides the predicate at the head, and trichotomy compares the head with the best found so far; the four combinations are the four clauses. The absence of truncation matters, because the caller wants an actual element, not a mere existence. Assuming the family merely covers the whole type, `Search.Over.least` upgrades this to a smallest element of any merely inhabited predicate over the whole type: the no-entry-satisfies-it branch is refuted by the witness, whose fiber in the family the predicate would have to hit. Well-foundedness then follows by the minimal-counterexample argument, described when its code is reached.
<!--zh-->
## 最小元与良基性

本节花用的是先前造好的点名册，而非再造一份。固定一个类型及其上一个三歧、非自反且传递的关系，即严格良序所要求的一切，只差良基。过程 `scan` 走过一个有穷族，并且不带任何截断地返回：要么是一个满足谓词、且在满足者之中最小的条目，要么是「没有条目满足它」的反驳。它是沿长度的普通递归：每一步由排中律判定谓词在头部是否成立，再由三歧比较头部与迄今为止的最佳者；四种组合即四条子句。全程无截断这一点很要紧，因为调用方要的是一个货真价实的元素，不是仅仅的存在性。在「该族单纯覆盖整个类型」的假设下，`Search.Over.least` 把它升级为「整个类型上任一单纯非空谓词的最小元」：「没有条目满足它」那一支被见证者驳倒，因为该谓词本该命中它在族中的纤维。良基性随后的最小反例论证在其代码处再作说明。
<!--ja-->
## 最小要素と整礎性

この節では、先につくった数え上げを使う側の議論を進めます。型と、その上の三岐・非反射・推移的な関係を固定します。これは整列順序が要求する性質のうち整礎性を除くすべてです。手続き `scan` は有限族をたどり、截断を一切伴わずに、述語を満たし満たすものの中で最小である項目か、満たす項目が存在しないことの反駁を返します。長さについての素朴な再帰です。各段階で排中律が頭部での述語を判定し、三岐性が頭部とそれまでの最良の候補を比較します。四つの組み合わせが四つの節です。どこにも截断がないことが重要です。呼び出し側が求めるのは単なる存在ではなく実際の要素だからです。族が型全体を単に被覆するという仮定の下で、`Search.Over.least` はこれを「型全体上の任意の単に非空な述語の最小要素」へと引き上げます。満たす項目がないという枝は、述語がそのファイバーを命中させねばならない証人によって反駁されます。整礎性はその後、最小の反例の議論によって導かれ、そのコードのところで述べます。
<!--/-->

<!--en-->
Fix a strict relation `≺` on `A` with trichotomy, irreflexivity and transitivity. The aim is to derive well-foundedness from a finite covering family rather than assume it. For a predicate `P`, `Least P m` records both that `m` satisfies `P` and that every strictly smaller satisfier leads to contradiction.
<!--zh-->
固定 `A` 上满足三歧、非自反与传递的严格关系 `≺`。目标是从有穷覆盖族推出良基性，而不是把良基性作为假设。对谓词 `P`，`Least P m` 同时记录 `m` 满足 `P`，以及每个严格更小的满足者都会导出矛盾。
<!--ja-->
`A` 上の狭義関係 `≺` が三岐性・非反射性・推移性を満たすとする。整礎性は仮定せず、有限な被覆族から導く。述語 `P` に対し、`Least P m` は `m` が `P` を満たすことと、より小さい充足者がすべて矛盾を導くことを記録する。
<!--/-->

```agda
module Search {A : Type (ℓ-suc ℓ)} (_≺_ : A → A → Type (ℓ-suc ℓ))
              (tri : (a b : A) → Tri (a ≺ b) (a ≡ b) (b ≺ a))
              (irr : (a : A) → a ≺ a → Empty.⊥)
              (trans : (a b c : A) → a ≺ b → b ≺ c → a ≺ c) where

  Least : (P : A → Ω) → A → Type (ℓ-suc ℓ)
```

<!--en-->
The scan's output type `Found P n f` is a disjunction of two explicit alternatives. In the left one, some position `i` holds an entry satisfying `P` and no other entry satisfying `P` lies below it within the family. In the right one, every entry fails the predicate. Both alternatives carry full data rather than truncated existence, which is what lets the later constructions return actual elements.
<!--zh-->
扫描的输出类型 `Found P n f` 是两个显式选项的析取。左支中，某个位置 `i` 持有一个满足 `P` 的条目，且族内没有其他满足 `P` 的条目位于其下。右支中，每个条目都不满足谓词。两个选项携带的都是完整数据而非截断的存在性，这使后续构造能返回真实的元素。
<!--ja-->
走査の出力型 `Found P n f` は二つの明示的な選択肢の論理和です。左の選択肢では、ある位置 `i` が `P` を満たす項目を保持し、族の中でそれより下に `P` を満たす他の項目はありません。右の選択肢では、すべての項目が述語を満たしません。どちらの選択肢も截断された存在ではなく完全なデータを運ぶので、後の構成が実際の要素を返せます。
<!--/-->

```agda
  Least P m = ⟨ P m ⟩ × ((b : A) → ⟨ P b ⟩ → b ≺ m → Empty.⊥)

  Found : (P : A → Ω) (n : ℕ) (f : Fin n → A) → Type (ℓ-suc ℓ)
  Found P n f =
    (Σ[ i ∈ Fin n ] (⟨ P (f i) ⟩ × ((j : Fin n) → ⟨ P (f j) ⟩ → f j ≺ f i → Empty.⊥)))
    ⊎ ((i : Fin n) → ⟨ P (f i) ⟩ → Empty.⊥)
```

<!--en-->
`scan` is defined by recursion on the family's length. The empty family returns the right alternative vacuously. For a family with a head, the recursion first handles the tail, shifting positions by one, and the verdict of excluded middle on `P` at the head is handed to `combine`, which merges the tail's outcome with the head's verdict into an outcome for the whole family.
<!--zh-->
`scan` 沿族长度递归定义。空族空虚地返回右支。对有头部的族，递归先处理尾部，把位置整体后移一位；排中律对 `P` 在头部的裁决交给 `combine`，它把尾部的结果与头部的裁决合并成整个族的结果。
<!--ja-->
`scan` は族の長さについての再帰で定義されます。空の族は空虚に右の選択肢を返します。頭部を持つ族では、再帰がまず尾を (位置を一つずらして) 処理し、頭部での `P` に対する排中律の判定が `combine` に渡されます。`combine` は尾の結果と頭部の判定を族全体の結果へと統合します。
<!--/-->

```agda

  scan : (P : A → Ω) (n : ℕ) (f : Fin n → A) → Found P n f
  scan P zero    f = inr (λ ())
  scan P (suc n) f = combine (scan P n (λ i → f (suc i))) (lem (P (f zero)))
    where
    combine : Found P n (λ i → f (suc i))
```

<!--en-->
The first clause of `combine` handles the case where the tail already yielded a smallest satisfier `f (suc i)` and the head also satisfies the predicate. Then two candidates compete, and trichotomy decides which of `f zero` and `f (suc i)` is smaller; the auxiliary `decide` analyses the three outcomes of that comparison.
<!--zh-->
`combine` 的第一支处理尾部已经给出最小满足者 `f (suc i)`、而头部也满足谓词的情形。此时两个候选竞争，三歧判定 `f zero` 与 `f (suc i)` 哪个更小；辅助函数 `decide` 分析该比较的三种结果。
<!--ja-->
`combine` の最初の節は、尾がすでに最小の充足者 `f (suc i)` を与え、頭部も述語を満たす場合を扱います。ここでは二つの候補が競い、三岐性が `f zero` と `f (suc i)` のどちらが小さいかを判定します。補助の `decide` がその比較の三通りの結果を分析します。
<!--/-->

```agda
            → (⟨ P (f zero) ⟩ ⊎ (⟨ P (f zero) ⟩ → Empty.⊥)) → Found P (suc n) f
    combine (inl (i , pi , mi)) (inl p₀) = decide (tri (f zero) (f (suc i)))
      where
      decide : Tri (f zero ≺ f (suc i)) (f zero ≡ f (suc i)) (f (suc i) ≺ f zero)
             → Found P (suc n) f
```

<!--en-->
If the head is strictly below the tail's champion, the head becomes the new champion. Its minimality is verified position by position: at the head itself, a claim `f zero ≺ f zero` contradicts irreflexivity outright; at a tail position, transitivity chains `f j ≺ f zero ≺ f (suc i)` and hands the result to the tail's already-established minimality `mi`.
<!--zh-->
若头部严格小于尾部的优胜者，头部便成为新的优胜者。其最小性逐位置核验：在头部自身处，断言 `f zero ≺ f zero` 直接与非自反性矛盾；在尾部各位置，传递性把 `f j ≺ f zero ≺ f (suc i)` 连成链，交给尾部已确立的最小性 `mi`。
<!--ja-->
頭部が尾の優位者より狭義に小さければ、頭部が新しい優位者になります。その最小性は位置ごとに確かめられます。頭部自身では `f zero ≺ f zero` の主張は非反射性と直ちに矛盾し、尾の位置では推移性が `f j ≺ f zero ≺ f (suc i)` をつなぎ、その結果を尾で確立済みの最小性 `mi` に渡します。
<!--/-->

```agda
      decide (lt h) = inl (zero , (p₀ , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f zero → Empty.⊥
        minAt zero    pj hj = irr (f zero) hj
        minAt (suc j) pj hj = mi j pj (trans (f (suc j)) (f zero) (f (suc i)) hj h)
```

<!--en-->
If the head equals the tail's current least candidate, that candidate remains least. A hypothetical comparison placing the head below the candidate is transported along their equality into a self-comparison of the candidate and contradicted by irreflexivity; tail positions are still handled by `mi`.
<!--zh-->
若头部等于尾部当前的最小候选，该候选仍为最小。假设头部低于候选，沿二者的等式传输后就得到候选低于自身，与非自反性矛盾；尾部位置仍由 `mi` 处理。
<!--ja-->
頭部が尾の現在の最小候補と等しければ、その候補は引き続き最小である。頭部が候補より小さいという仮定は、両者の等式に沿って候補自身より小さいという比較へ輸送され、非反射性に反する。尾の位置は引き続き `mi` が扱う。
<!--/-->

```agda
      decide (eq h) = inl (suc i , (pi , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
        minAt zero    pj hj = irr (f (suc i)) (subst (λ w → w ≺ f (suc i)) h hj)
        minAt (suc j) pj hj = mi j pj hj
```

<!--en-->
If the tail's champion is strictly below the head, it survives. A hypothetical entry below the champion now has two ways down: transitivity through the head `f (suc i) ≺ f zero ≺ f (suc i)` produces a self-comparison refuted by irreflexivity, while the tail's own positions go to `mi`. The champion's certificate is thus rebuilt from the old one in every branch.
<!--zh-->
若尾部的优胜者严格小于头部，它得以保留。此时优胜者之下的假设性条目有两条出路：经头部 `f (suc i) ≺ f zero ≺ f (suc i)` 的传递性给出一个自比较，由非自反性驳倒；而尾部自身的各位置交给 `mi`。优胜者的证书在每个分支都由旧证书重建。
<!--ja-->
尾の優位者が頭部より狭義に小さければ、優位者は生き残ります。優位者の下にあると仮定した要素には二つの落ち方が生じます。頭部を経由する推移性 `f (suc i) ≺ f zero ≺ f (suc i)` が非反射性で反駁される自己比較を生み、尾自身の位置は `mi` に渡されます。優位者の証明書はどの枝でも古い証明書から組み立て直されるのです。
<!--/-->

```agda
      decide (gt h) = inl (suc i , (pi , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
        minAt zero    pj hj = irr (f (suc i)) (trans (f (suc i)) (f zero) (f (suc i)) h hj)
        minAt (suc j) pj hj = mi j pj hj
```

<!--en-->
The second clause keeps the tail's champion when the head fails the predicate. No comparison is needed at all: the head cannot challenge the champion because it does not satisfy `P`, so a supposed counterexample at the head is refuted directly by the verdict `n₀`, and tail positions again go to `mi`.
<!--zh-->
第二支在头部不满足谓词时保留尾部的优胜者。这里完全不需要比较：头部既然不满足 `P`，便无从挑战优胜者，因此头部处的假想反例直接由裁决 `n₀` 驳倒，尾部各位置依旧交给 `mi`。
<!--ja-->
二つ目の節は、頭部が述語を満たさない場合に尾の優位者を保ちます。比較はまったく要りません。頭部は `P` を満たさないので優位者に挑戦できず、頭部での仮想の反例は判定 `n₀` によって直接反駁され、尾の位置はやはり `mi` に渡されます。
<!--/-->

```agda
    combine (inl (i , pi , mi)) (inr n₀) = inl (suc i , (pi , minAt))
      where
      minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
      minAt zero    pj hj = Empty.rec (n₀ pj)
      minAt (suc j) pj hj = mi j pj hj
```

<!--en-->
Symmetrically, when the tail had no satisfier at all and the head does satisfy the predicate, the head is the new champion. Its minimality is immediate: the head itself is handled by irreflexivity, and any tail position satisfying the predicate would contradict the tail's refutation `none`.
<!--zh-->
对称地，当尾部全无满足者而头部确实满足谓词时，头部就是新的优胜者。其最小性立即可得：头部自身由非自反性处理，任何满足谓词的尾部位置都与尾部的反驳 `none` 矛盾。
<!--ja-->
対称的に、尾に充足者がまったくなく頭部が述語を満たす場合は、頭部が新しい優位者です。その最小性は直ちに得られます。頭部自身は非反射性で処理され、述語を満たす尾の位置があれば尾の反駁 `none` と矛盾します。
<!--/-->

```agda
    combine (inr none) (inl p₀) = inl (zero , (p₀ , minAt))
      where
      minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f zero → Empty.⊥
      minAt zero    pj hj = irr (f zero) hj
      minAt (suc j) pj hj = Empty.rec (none j pj)
```

<!--en-->
The last clause is the agreement case: neither the tail nor the head supplies a satisfier, so the whole family is reported as satisfying nothing. The refutation is assembled positionwise, dispatching the head to `n₀` and each tail position to `none`. With this clause the four combinations announced in the lead are complete.
<!--zh-->
最后一支是一致情形：尾部与头部都给不出满足者，于是报告整个族中无人满足。反驳逐位置组装：头部交给 `n₀`，每个尾部位置交给 `none`。至此，导言所说的四种组合齐备。
<!--ja-->
最後の節は一致の場合です。尾にも頭にも充足者がいないので、族全体が何も満たさないと報告されます。反駁は位置ごとに組み立てられ、頭部は `n₀` に、各尾の位置は `none` に回されます。これで導入部に予告した四つの組み合わせがそろいました。
<!--/-->

```agda
    combine (inr none) (inr n₀) = inr atAll
      where
      atAll : (i : Fin (suc n)) → ⟨ P (f i) ⟩ → Empty.⊥
      atAll zero    p = n₀ p
      atAll (suc i) p = none i p
```

<!--en-->
The sub-module `Over` adds the one premise that turns a finite family into a tally: `cov` says every element of `A` is merely hit by the family, a truncated coverage with repetitions allowed. Under this premise `least` upgrades the scan's answer to a least element for the whole type: its input is only a truncated witness that some element satisfies `P`, and its output is explicit data, an element together with `Least P m`.
<!--zh-->
子模块 `Over` 添加了把有穷族变成点名册所需的那条前提：`cov` 说 `A` 的每个元素都被该族单纯命中，这是允许重复的截断覆盖。在此前提下，`least` 把扫描的答案升级为整个类型上的最小元：其输入只是一个「某元素满足 `P`」的截断见证，其输出则是显式数据，即一个元素连同 `Least P m`。
<!--ja-->
副モジュール `Over` は、有限族を数え上げへと変えるための唯一の前提を追加します。`cov` は `A` のすべての要素が族によって単に命中されると言うもので、重複を許す截断的被覆です。この前提のもとで `least` は走査の答えを型全体への最小要素へと引き上げます。入力は「ある要素が `P` を満たす」という截断された証人だけですが、出力は明示的なデータ、すなわち要素と `Least P m` の組です。
<!--/-->

```agda

  module Over (n : ℕ) (f : Fin n → A)
              (cov : (a : A) → ∥ Σ[ i ∈ Fin n ] (f i ≡ a) ∥₁) where

    least : (P : A → Ω) → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ m ∈ A ] Least P m
    least P h = decide (scan P n f)
      where
```

<!--en-->
Inside `least`, the auxiliary `nowhere` disposes of the scan's no-satisfier branch: assuming no entry satisfies `P`, it must refute the given truncated witness. The elimination is legitimate because the target is the empty type, a proposition, so the truncation of the witness may be taken apart without choosing anything.
<!--zh-->
在 `least` 内部，辅助函数 `nowhere` 处理扫描的「无满足者」分支：假定没有条目满足 `P`，就必须驳倒给定的截断见证。该消去是合法的，因为目标是空类型这一命题，因此见证的截断可以在不作任何选择的情况下拆开。
<!--ja-->
`least` の内部で、補助の `nowhere` は走査の「充足者なし」の枝を処理します。どの項目も `P` を満たさないと仮定したとき、与えられた截断された証人を反駁せねばなりません。この消去が正当なのは、目標が命題である空の型だからで、証人の截断は何も選ばずにほどけます。
<!--/-->

```agda
      nowhere : ((i : Fin n) → ⟨ P (f i) ⟩ → Empty.⊥) → Empty.⊥
      nowhere none = PT.rec Empty.isProp⊥ atWitness h
        where
        atWitness : Σ[ a ∈ A ] ⟨ P a ⟩ → Empty.⊥
        atWitness (a , pa) = PT.rec Empty.isProp⊥
```

<!--en-->
Concretely, the witness supplies an element `a` with `⟨ P a ⟩`, and the coverage `cov a` merely names a family position `i` with `f i ≡ a`; again the target is a proposition, so the fiber may be read. Transporting the proof of `⟨ P a ⟩` backwards along `f i ≡ a` gives `⟨ P (f i) ⟩`, which the assumed refutation `none` turns into a contradiction. The next lines carry out exactly this transport.
<!--zh-->
具体而言，见证给出元素 `a` 及 `⟨ P a ⟩`，覆盖 `cov a` 单纯地指出族中位置 `i` 满足 `f i ≡ a`；由于目标仍是命题，该纤维可以被读出。把 `⟨ P a ⟩` 的证明沿 `f i ≡ a` 反向传输得到 `⟨ P (f i) ⟩`，假定的反驳 `none` 便将其化为矛盾。紧接的代码行执行的正是这次传输。
<!--ja-->
具体的には、証人が要素 `a` と `⟨ P a ⟩` を与え、被覆 `cov a` が `f i ≡ a` を満たす族の位置 `i` を単に指し示します。ここでも目標は命題なのでファイバーを読めます。`⟨ P a ⟩` の証明を `f i ≡ a` に沿って逆向きに輸送すれば `⟨ P (f i) ⟩` が得られ、仮定した反駁 `none` がそれを矛盾に変えます。続く行がまさにこの輸送を行います。
<!--/-->

```agda
          (λ { (i , q) → none i (subst (λ w → ⟨ P w ⟩) (sym q) pa) }) (cov a)
      decide : Found P n f → Σ[ m ∈ A ] Least P m
      decide (inl (i , pi , mi)) = f i , (pi , everywhere)
        where
        everywhere : (b : A) → ⟨ P b ⟩ → b ≺ f i → Empty.⊥
```

<!--en-->
The transport announced earlier is carried out here, in both components at once. Given a supposed entry `b` of the whole type below the champion, with `⟨ P b ⟩` and `b ≺ f i`, the coverage merely names a family position `j` with `f j ≡ b`; both the satisfaction and the comparison are transported backwards along that path, and the champion's family-level certificate `mi` refutes them together. Hence the scan's only remaining branch, the refutation `none`, is outright contradictory, since the witness was shown to force a satisfier into the family.
<!--zh-->
前面预告的传输在这里执行，且两个分量同时进行。给定整个类型中位于优胜者之下的假想条目 `b`，附有 `⟨ P b ⟩` 与 `b ≺ f i`，覆盖单纯地给出满足 `f j ≡ b` 的族位置 `j`；把满足性与比较性都沿该路径反向传输，优胜者的族级证书 `mi` 便把二者一并驳倒。于是扫描仅剩的分支，即反驳 `none`，彻底矛盾，因为见证已被证明必然把一个满足者带进族中。
<!--ja-->
先に予告した輸送がここで、両成分にわたって一度に行われます。型全体の中で優位者の下にあると仮定した項目 `b` と `⟨ P b ⟩`、`b ≺ f i` が与えられると、被覆が `f j ≡ b` を満たす族の位置 `j` を単に指し示します。充足と比較の両方をその経路に沿って逆向きに輸送すれば、優位者の族レベルの証明書 `mi` が両者をまとめて反駁します。したがって走査に残る唯一の枝である反駁 `none` は完全に矛盾します。証人が必ず族の中に充足者を引き込むことが示されたからです。
<!--/-->

```agda
        everywhere b pb hb = PT.rec Empty.isProp⊥
          (λ { (j , q) → mi j (subst (λ w → ⟨ P w ⟩) (sym q) pb)
                              (subst (λ w → w ≺ f i) (sym q) hb) }) (cov b)
      decide (inr none) = Empty.rec (nowhere none)

    wellFounded : WellFounded _≺_
```

<!--en-->
To prove well-foundedness, first decide accessibility of an arbitrary `a`. The positive case returns its certificate. In the negative case, finite search produces a least element `m` whose accessibility is refuted. If every predecessor of `m` is accessible, `acc below` makes `m` accessible; applying the refutation stored in `found` to this certificate yields the contradiction. The original refutation of `a` is used only to witness that the predicate of non-accessibility is inhabited.
<!--zh-->
为证明良基性，先判定任意 `a` 是否可及；肯定支直接返回证书。否定支用有穷扫描找出可及性被反驳的最小元素 `m`。若 `m` 的每个前驱都可及，`acc below` 就证明 `m` 可及；把 `found` 中保存的 `m` 的反驳作用于这份证书即得矛盾。最初关于 `a` 的反驳只用于证明「不可及」这一谓词非空。
<!--ja-->
整礎性を示すため、まず任意の `a` の到達可能性を判定する。肯定の場合は証明をそのまま返す。否定の場合、有限走査により、到達可能性が反駁される最小の要素 `m` を得る。`m` のすべての前駆が到達可能なら `acc below` が `m` の到達可能性を与え、`found` に保存された `m` の反駁をこの証明に適用して矛盾を得る。もとの `a` の反駁は、非到達可能という述語が非空であることを示すためだけに用いる。
<!--/-->

```agda
    wellFounded a = fromDec (lem (Acc _≺_ a , isPropAcc a))
      where
      fromDec : (Acc _≺_ a ⊎ (Acc _≺_ a → Empty.⊥)) → Acc _≺_ a
      fromDec (inl h) = h
      fromDec (inr nh) = Empty.rec (found .snd .fst (acc below))
```

<!--en-->
The property to be minimized is `NotAcc`, non-accessibility. Its underlying statement is a negation, and negations are propositions, so `NotAcc` is a legitimate truth value `Ω` and `least` may be applied to it. The input is the truncated pairing of `a` with the assumed refutation `nh`, so the hypothesis merely says that the set of non-accessible elements is nonempty.
<!--zh-->
被取最小的性质是 `NotAcc`，即不可及性。其底层陈述是一个否定，而否定是命题，故 `NotAcc` 是合法的真值 `Ω`，`least` 可以作用于它。输入是 `a` 与假定反驳 `nh` 的截断配对，因此该假设只是说不可及元素之集非空。
<!--ja-->
最小化の対象となる性質は `NotAcc`、すなわち到達不可能性です。その下にある主張は否定であり、否定は命題なので、`NotAcc` は正当な真理値 `Ω` であり、`least` を適用できます。入力は `a` と仮定された反駁 `nh` の截断された組であり、仮定は単に到達不能な要素の集まりが空でないと言っているにすぎません。
<!--/-->

```agda
        where
        NotAcc : A → Ω
        NotAcc b = (Acc _≺_ b → Empty.⊥) , isProp¬ _
        found : Σ[ m ∈ A ] Least NotAcc m
        found = least NotAcc ∣ a , nh ∣₁
```

<!--en-->
Let `m` be the least non-accessible element just found. To show it accessible, one must show every predecessor `b` accessible, and accessibility of `b` is again a proposition, so it is decided once more by excluded middle; the auxiliary `pick` returns the certificate in the affirmative branch.
<!--zh-->
设 `m` 是刚求得的最小不可及元素。要证它可及，须证每个前驱 `b` 可及，而 `b` 的可及性又是命题，故再次由排中律判定；辅助函数 `pick` 在肯定支中返回证书。
<!--ja-->
今求めた最小の到達不能要素を `m` とします。これが到達可能であることを示すには、すべての前駆 `b` が到達可能であることを示さねばならず、`b` の到達可能性もまた命題なので、再び排中律で判定します。補助の `pick` が肯定の枝で証明書を返します。
<!--/-->

```agda
        below : (b : A) → b ≺ found .fst → Acc _≺_ b
        below b hb = pick (lem (Acc _≺_ b , isPropAcc b))
          where
          pick : (Acc _≺_ b ⊎ (Acc _≺_ b → Empty.⊥)) → Acc _≺_ b
          pick (inl h)  = h
```

<!--en-->
In the negative branch, `b` would be a non-accessible element strictly below the least non-accessible element `m`, and the minimality clause of `Least NotAcc m` refutes exactly that. Hence every predecessor is accessible, the certificate `acc below` is legitimate, and feeding it to the assumed refutation of accessibility closes the contradiction. Note that no infinite descending sequence was ever constructed or excluded; the argument is entirely this contradiction.
<!--zh-->
在否定支中，`b` 将是严格小于最小不可及元素 `m` 的不可及元素，而 `Least NotAcc m` 的最小性条款恰好驳斥这一点。于是每个前驱皆可及，证书 `acc below` 合法，把它交给假定的可及性反驳便封闭了矛盾。注意：全程并未构造或排除任何无穷下降序列，论证完全就是这个矛盾。
<!--ja-->
否定の枝では、`b` は最小の到達不能要素 `m` より狭義に小さい到達不能要素となるはずで、`Least NotAcc m` の最小性の条項がまさにそれを反駁します。したがってすべての前駆が到達可能であり、証明書 `acc below` は正当で、仮定された到達可能性の反駁に与えることで矛盾が閉じます。無限下降列が構成されたり排除されたりしたのではなく、議論は完全にこの矛盾によるものです。
<!--/-->

```agda
          pick (inr nb) = Empty.rec (found .snd .snd b nb hb)
```

<!--en-->
## The earliest disagreement

This section defines the order that finite stages will carry. Fix a set `A` and a relation `R` on sets, read as an order on the members of `A`. Two subsets of `A` are compared by looking at where they disagree. A witness that `x` comes before `y` is a member `z` of `A` that belongs to `y` and not to `x`, such that `x` and `y` **agree** below `z`, meaning that every member of `A` that `R` puts before `z` belongs to one exactly when it belongs to the other. Read backwards: `z` is the earliest point of disagreement, and `y` is the one that has it. The relation `precedes R A` is the truncated existence of such a witness, and irreflexivity is immediate and needs no hypothesis at all: a witness for `x` against itself would belong to `x` and not belong to `x`. The later proofs establish trichotomy and transitivity from hypotheses on the base order, and use finiteness for well-foundedness.
<!--zh-->
## 最先的分歧

本节定义有穷层将要携带的序。固定一个集合 `A` 与集合之上的一个关系 `R`，后者读作 `A` 的诸成员上的一个序。`A` 的两个子集，按它们在何处分歧来比较。「`x` 先于 `y`」的见证，是 `A` 的一个成员 `z`，它属于 `y` 而不属于 `x`，且 `x` 与 `y` 在 `z` 之下**一致**，意即 `A` 中被 `R` 排在 `z` 之前的每个成员，属于其中之一当且仅当属于另一个。倒过来读：`z` 就是最先的分歧点，而它属于 `y`。关系 `precedes R A` 是这类见证的截断存在；非自反性立刻成立，且完全不需要任何前提：`x` 对自己的见证会既属于 `x` 又不属于 `x`。后文证明在关于基底序的前提下得到三歧与传递，并用有穷性得到良基性。
<!--ja-->
## 最初の相違

この節は、有限段階が担う順序を定義します。集合 `A` と、集合の上の関係 `R` を固定します。`R` は `A` の要素の上の順序と読みます。`A` の二つの部分集合は、どこで食い違うかによって比較されます。「`x` が `y` に先行する」ことの証人は、`A` の要素 `z` であって、`y` に属し `x` には属さず、かつ `x` と `y` が `z` の下で**一致**するものです。つまり `R` が `z` の前に置く `A` の各要素は、一方に属するならばちょうど他方にも属するということです。逆向きに読めば、`z` が最初の相違点であり、それを持つのが `y` です。関係 `precedes R A` はそのような証人の截断された存在であり、非反射性は直ちに成り立ち、まったく仮定を要しません。`x` 自身に対する証人は `x` に属すると同時に属さないことになるからです。続く証明は基底の順序への仮定から三岐性と推移性を確立し、整礎性には有限性を用います。
<!--/-->

<!--en-->
The two ingredients are stated separately. `Agrees R A x y z` says that membership in `x` and in `y` coincides for every member `w` of `A` that `R` places before `z`, in both directions. `Witness R A x y z` then assembles the full witness: `z` lies in `A`, it belongs to `y`, it does not belong to `x`, and agreement holds below it. The direction of the membership clauses is what decides which side wins the comparison.
<!--zh-->
两个成分分别陈述。`Agrees R A x y z` 说：对 `A` 中被 `R` 排在 `z` 之前的每个成员 `w`，属于 `x` 与属于 `y` 双向重合。`Witness R A x y z` 随后组装完整见证：`z` 属于 `A`，属于 `y`，不属于 `x`，且其下方一致成立。正是成员条款的方向决定了比较中哪一方胜出。
<!--ja-->
二つの材料は別々に述べられます。`Agrees R A x y z` は、`R` が `z` の前に置く `A` の各要素 `w` について、`x` への所属と `y` への所属が双方向に一致することを言います。`Witness R A x y z` は続いて完全な証人を組み立てます。`z` は `A` に属し、`y` に属し、`x` には属さず、その下で一致が成り立つ、ということです。所属条項の向きこそが、比較でどちらが勝つかを決めます。
<!--/-->

```agda
Agrees : (R : S → S → Ω) (A x y z : S) → Type (ℓ-suc ℓ)
Agrees R A x y z = (w : S) → ⟨ w ∈ˢ A ⟩ → ⟨ R w z ⟩
                 → (⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩) × (⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩)

Witness : (R : S → S → Ω) (A x y z : S) → Type (ℓ-suc ℓ)
Witness R A x y z =
```

<!--en-->
`precedes R A x y` is the proposition that such a witness merely exists, packaged with `PT.squash₁` as a truth value. Because the witness is hidden behind a truncation, its existence is all that is asserted; nothing chooses `z`. Irreflexivity then costs one line: eliminating the truncation into the empty type, a proposition, exposes a witness with `z ∈ x` and `z ∉ x`, and the second clause applied to the first is the contradiction.
<!--zh-->
`precedes R A x y` 是「这类见证单纯存在」的命题，随 `PT.squash₁` 打包成一个真值。由于见证藏在截断之后，被断言的只有其存在，任何东西都不选定 `z`。非自反性于是只花一行：把截断消去到空类型 (一个命题) 中，暴露出同时有 `z ∈ x` 与 `z ∉ x` 的见证，把第二条施于第一条即是矛盾。
<!--ja-->
`precedes R A x y` は、そのような証人が単に存在するという命題であり、`PT.squash₁` とともに真理値としてまとめられています。証人は截断の後ろに隠れているので、主張されるのはその存在だけで、`z` が選ばれることはありません。非反射性はそこで一行で済みます。截断を命題である空の型へと消去すれば、`z ∈ x` と `z ∉ x` を同時に持つ証人が現れ、第二の条項を第一に施せば矛盾です。
<!--/-->

```agda
  ⟨ z ∈ˢ A ⟩ × ⟨ z ∈ˢ y ⟩ × (⟨ z ∈ˢ x ⟩ → Empty.⊥) × Agrees R A x y z

precedes : (R : S → S → Ω) (A : S) → S → S → Ω
precedes R A x y = ∥ Σ[ z ∈ S ] Witness R A x y z ∥₁ , PT.squash₁

precedes-irrefl : (R : S → S → Ω) (A x : S) → ⟨ precedes R A x x ⟩ → Empty.⊥
precedes-irrefl R A x = PT.rec Empty.isProp⊥ (λ { (z , _ , z∈ , z∉ , _) → z∉ z∈ })
```

<!--en-->
Transitivity and trichotomy of the earliest-disagreement order do need hypotheses on the base order, and the two need different ones, so both are collected in one module. Its parameters are trichotomy and transitivity of `R` on the members of `A`, and the smallest-element principle for `R` over those members; in the tower these come from the stage below.

Transitivity is a comparison of two witnesses. If `x` comes before `y` at `p` and `y` comes before `z` at `q`, then `p` and `q` cannot be equal, since `p` belongs to `y` and `q` does not; and whichever of the two is smaller witnesses that `x` comes before `z`. Both branches check the same two things: that the smaller point is on the right side, and that the agreement below it composes.
<!--zh-->
最先分歧序的传递性与三歧确实需要关于基底序的前提，而二者所需不同，故一并收进一个模块。其参数是 `R` 在 `A` 诸成员上的三歧与传递，以及 `R` 在那些成员上的最小元原则；在塔中，这些都来自下面那一层。

传递性是两个见证之间的比较。若 `x` 在 `p` 处先于 `y`，`y` 在 `q` 处先于 `z`，则 `p` 与 `q` 不可能相等，因为 `p` 属于 `y` 而 `q` 不属于；而二者中较小的那个就见证了 `x` 先于 `z`。两支要核对的是同样的两件事：较小的那一点方向正确，以及它之下的一致性可以复合。
<!--ja-->
最初の相違による順序の推移性と三岐性は、基底の順序への仮定を indeed 必要とし、しかも両者は異なる仮定を要するので、一つのモジュールにまとめられます。そのパラメータは、`A` の要素の上での `R` の三岐性と推移性、およびそれらの要素の上での `R` の最小要素原理です。塔の中では、これらは下の段階から供給されます。

推移性は二つの証人の比較です。`x` が `p` で `y` に先行し、`y` が `q` で `z` に先行するなら、`p` は `y` に属し `q` は属さないので `p` と `q` は等しくありえず、両者のうち小さいほうが `x` が `z` に先行することの証人となります。どちらの枝でも確かめることは同じ二つです。小さいほうの点が正しい側にあることと、その下での一致が合成できることです。
<!--/-->

<!--en-->
The module collects the three premises the earliest-disagreement order will inherit. `baseTri` and `baseTrans` say that `R` restricted to members of `A` is trichotomous and transitive, and `baseLeast` is the smallest-element principle over `A`: from a merely inhabited property of members of `A` it returns an element satisfying it that no smaller member of `A` satisfies. Note the shape of the conclusion: it is explicit data, not a truncation, since the caller needs the actual least element.
<!--zh-->
该模块收集最先分歧序将要继承的三条前提。`baseTri` 与 `baseTrans` 说 `R` 限制在 `A` 的成员上时三歧且传递，`baseLeast` 是 `A` 上的最小元原则：从「`A` 成员的某个性质单纯非空」出发，它给出一个满足该性质、且没有更小的 `A` 成员也满足的元素。注意结论的形状：它是显式数据而非截断，因为调用方需要真实的极小元。
<!--ja-->
このモジュールは、最初の相違の順序が受け継ぐ三つの前提を集めます。`baseTri` と `baseTrans` は、`A` の要素に制限した `R` が三岐かつ推移的であると言い、`baseLeast` は `A` の上の最小要素原理です。`A` の要素のある性質が単に非空であることから、その性質を満たし、より小さい `A` の要素がどれも満たさない要素を返します。結論の形に注意してください。呼び出し側が実際の最小要素を必要とするので、截断ではなく明示的なデータです。
<!--/-->

```agda
module Difference (R : S → S → Ω) (A : S)
  (baseTri : (a b : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ A ⟩ → Tri ⟨ R a b ⟩ (a ≡ b) ⟨ R b a ⟩)
  (baseTrans : (a b c : S) → ⟨ R a b ⟩ → ⟨ R b c ⟩ → ⟨ R a c ⟩)
  (baseLeast : (P : S → Ω) → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × ⟨ P a ⟩) ∥₁
             → Σ[ m ∈ S ] (⟨ m ∈ˢ A ⟩ × ⟨ P m ⟩
```

<!--en-->
The statement of transitivity takes the two hypotheses exactly as `precedes` produces them: truncated witnesses for `x ≺ y` and for `y ≺ z`, and returns a truncated witness for `x ≺ z`. The proof therefore begins by eliminating the first truncation, then the second, both into a target that is again a truncation and hence a proposition.
<!--zh-->
传递性的陈述恰好按 `precedes` 的产出形式取两条前提：`x ≺ y` 与 `y ≺ z` 的截断见证，并返回 `x ≺ z` 的截断见证。因此证明先消去第一个截断，再消去第二个，二者的目标都又是截断、因而是命题。
<!--ja-->
推移性の主張は、二つの仮定を `precedes` が生み出す通りの形で受け取ります。`x ≺ y` と `y ≺ z` の截断された証人を受け取り、`x ≺ z` の截断された証人を返します。したがって証明は、最初の截断を消去し、次に第二の截断を消去することから始まります。どちらの目標も再び截断であり、したがって命題です。
<!--/-->

```agda
                 × ((b : S) → ⟨ b ∈ˢ A ⟩ → ⟨ P b ⟩ → ⟨ R b m ⟩ → Empty.⊥)))
  where

  precedes-trans : (x y z : S) → ⟨ precedes R A x y ⟩ → ⟨ precedes R A y z ⟩
                 → ⟨ precedes R A x z ⟩
  precedes-trans x y z hxy hyz =
```

<!--en-->
With both witnesses exposed, `both` receives the full data: a point `p` witnessing `x` before `y`, with its membership clauses `agp`, and a point `q` witnessing `y` before `z`, with `agq`. The comparison of the two base points is delegated to the base trichotomy, and the auxiliary `decide` analyses its three outcomes.
<!--zh-->
两个见证都暴露后，`both` 接收完整数据：见证 `x` 先于 `y` 的点 `p` 及其成员条款 `agp`，以及见证 `y` 先于 `z` 的点 `q` 及其 `agq`。两个基底点的比较交给基底三歧，辅助函数 `decide` 分析其三种结果。
<!--ja-->
両方の証人が現れたところで、`both` は完全なデータを受け取ります。`x` が `y` に先行することの証人である点 `p` とその所属条項 `agp`、そして `y` が `z` に先行することの証人である点 `q` とその `agq` です。二つの基底点の比較は基底の三岐性に委ねられ、補助の `decide` がその三通りの結果を分析します。
<!--/-->

```agda
    PT.rec PT.squash₁ (λ wp → PT.rec PT.squash₁ (both wp) hyz) hxy
    where
    both : Σ[ p ∈ S ] Witness R A x y p → Σ[ q ∈ S ] Witness R A y z q
         → ⟨ precedes R A x z ⟩
    both (p , p∈A , p∈y , p∉x , agp) (q , q∈A , q∈z , q∉y , agq) =
```

<!--en-->
If `p` is strictly below `q`, it keeps the role of witness for `x` before `z`. Its own clauses carry over unchanged, being about `x` and `y`; what must be verified is that `p` belongs to `z` and that agreement holds below `p` between `x` and `z`. Membership in `z` comes from `agq` at the point `p`, which transports `p`'s membership in `y` across the composite comparison.
<!--zh-->
若 `p` 严格小于 `q`，它继续充当 `x` 先于 `z` 的见证。它自身的条款原封不动，因为它们只涉及 `x` 与 `y`；须核实的是 `p` 属于 `z`，以及 `p` 之下 `x` 与 `z` 的一致性。`p` 属于 `z` 由 `agq` 在点 `p` 处给出，它把 `p` 对 `y` 的成员关系沿复合比较传输过去。
<!--ja-->
`p` が `q` より狭義に小さければ、`p` が `x` の `z` への先行の証人であり続けます。それ自身の条項は `x` と `y` だけに関わるのでそのまま引き継がれ、確かめるべきなのは `p` が `z` に属することと、`p` の下で `x` と `z` の一致が成り立つことです。`z` への所属は点 `p` での `agq` から来ます。`p` の `y` への所属を合成された比較を通して輸送するのです。
<!--/-->

```agda
      decide (baseTri p q p∈A q∈A)
      where
      decide : Tri ⟨ R p q ⟩ (p ≡ q) ⟨ R q p ⟩ → ⟨ precedes R A x z ⟩
      decide (lt h) = ∣ p , (p∈A , (agq p p∈A h .fst p∈y , (p∉x , ag))) ∣₁
        where
```

<!--en-->
Agreement below `p` is composed clause by clause. To show `w ∈ x` implies `w ∈ z`: `agp` lifts `w ∈ x` to `w ∈ y`, then `agq` lifts membership in `y` up to `z`, using base transitivity to know that `w` lies below `q` as well. The backward clause is symmetric, running `z` down to `y` and then to `x`. The equality case cannot occur: `p` belongs to `y` while `q` does not, so transporting membership along the path `p ≡ q` yields a contradiction.
<!--zh-->
`p` 之下的一致性逐条款复合。要证 `w ∈ x` 蕴含 `w ∈ z`：`agp` 把 `w ∈ x` 提升为 `w ∈ y`，再用 `agq` 把对 `y` 的成员提升到 `z`，其中用基底传递性保证 `w` 也位于 `q` 之下。反向条款对称，把 `z` 降到 `y` 再降到 `x`。相等情形不可能出现：`p` 属于 `y` 而 `q` 不属于，沿路径 `p ≡ q` 传输成员关系即得矛盾。
<!--ja-->
`p` の下での一致は条項ごとに合成されます。`w ∈ x` が `w ∈ z` を導くことを示すには、`agp` が `w ∈ x` を `w ∈ y` に引き上げ、続いて `agq` が `y` への所属を `z` まで引き上げます。その際、基底の推移性によって `w` が `q` の下にもあることを使います。逆向きの条項は対称で、`z` を `y` へ、さらに `x` へと下ろします。等しい場合は起こりえません。`p` は `y` に属し `q` は属さないので、経路 `p ≡ q` に沿って所属を輸送すれば矛盾が得られます。
<!--/-->

```agda
        ag : Agrees R A x z p
        ag w w∈A hw =
            (λ wx → agq w w∈A (baseTrans w p q hw h) .fst (agp w w∈A hw .fst wx))
          , (λ wz → agp w w∈A hw .snd (agq w w∈A (baseTrans w p q hw h) .snd wz))
      decide (eq h) = Empty.rec (q∉y (subst (λ v → ⟨ v ∈ˢ y ⟩) h p∈y))
```

<!--en-->
If instead `q` is strictly below `p`, the roles swap: `q` witnesses `x` before `z`. Its clauses about `y` and `z` carry over, but membership in `x` and agreement must be established. For membership, `agp` read at the point `q` transports membership of `q` in `x` down to membership in `y`, contradicting `q ∉ y`; the auxiliary `q∉x` packages this refutation.
<!--zh-->
若改为 `q` 严格小于 `p`，角色对调：由 `q` 见证 `x` 先于 `z`。它关于 `y` 与 `z` 的条款照旧，但须确立对 `x` 的成员与一致性。关于成员，在点 `q` 处读 `agp`，把 `q` 对 `x` 的成员传输为对 `y` 的成员，与 `q ∉ y` 矛盾；辅助函数 `q∉x` 把这一反驳打包。
<!--ja-->
逆に `q` が `p` より狭義に小さければ、役割が入れ替わり、`q` が `x` の `z` への先行を証明します。`y` と `z` に関する条項はそのまま引き継げますが、`x` への所属と一致を確立せねばなりません。所属については、点 `q` で `agp` を読むと `q` の `x` への所属が `y` への所属へと輸送され、`q ∉ y` と矛盾します。補助の `q∉x` がこの反駁をまとめます。
<!--/-->

```agda
      decide (gt h) = ∣ q , (q∈A , (q∈z , (q∉x , ag))) ∣₁
        where
        q∉x : ⟨ q ∈ˢ x ⟩ → Empty.⊥
        q∉x qx = q∉y (agp q q∈A h .fst qx)
        ag : Agrees R A x z q
```

<!--en-->
Agreement below `q` composes in the mirrored order: membership in `x` is pushed down to `y` by `agp`, using base transitivity with `q ≺ p` to place `w` below `p`, and `agq` then carries it up to `z`; the backward clause descends `z` to `y` first and then to `x`. With both asymmetric cases handled, and equality refuted, transitivity is complete.
<!--zh-->
`q` 之下的一致性以镜像顺序复合：先用 `agp` 借助 `q ≺ p` 的基底传递性把 `w` 置于 `p` 之下，从而把对 `x` 的成员下推到 `y`，`agq` 再把它上提到 `z`；反向条款先把 `z` 降到 `y`，再降到 `x`。两个不对称情形都已处理、相等已被驳倒，传递性就此完成。
<!--ja-->
`q` の下での一致は鏡像の順で合成されます。まず `agp` が `q ≺ p` と基底の推移性によって `w` を `p` の下に置き、`x` への所属を `y` へと押し下げ、続いて `agq` がそれを `z` まで引き上げます。逆向きの条項はまず `z` を `y` へ、さらに `x` へと下ろします。二つの非対称な場合が処理され、等しい場合は反駁されたので、推移性が完成します。
<!--/-->

```agda
        ag w w∈A hw =
            (λ wx → agq w w∈A hw .fst (agp w w∈A (baseTrans w q p hw h) .fst wx))
          , (λ wz → agp w w∈A (baseTrans w q p hw h) .snd (agq w w∈A hw .snd wz))
```

<!--en-->
Trichotomy is where the excluded middle and the smallest-element principle are used. Ask whether the two subsets disagree anywhere in `A`. If they do not, they agree everywhere in `A`; since both stay inside `A`, they already agree everywhere, and extensionality identifies them. If they do, there is an earliest point of disagreement, and one further decision, whether that point belongs to the first subset, says which way the comparison goes. Agreement below the point holds automatically in both branches: nothing below it disagrees, by the choice of the point.

The excluded middle is used a second time inside `agree`, to turn "not disagreeing" into "agreeing"; that step is exactly a double negation elimination.
<!--zh-->
三歧正是使用排中律与最小元原则的地方。先问这两个子集在 `A` 中是否有分歧之处。若没有，则它们在 `A` 中处处一致；又因二者都不超出 `A`，故它们本就处处一致，外延性把它们认同。若有，则存在一个最先的分歧点；再作一次判定，即该点是否属于第一个子集，就知道比较朝哪个方向走。该点之下的一致性在两支中都自动成立：按该点的选法，它之下无一处分歧。

排中律在 `agree` 内部第二次被使用，用来把「没有分歧」变成「一致」；这一步恰是一次双重否定的消去。
<!--ja-->
三分法は、排中律と最小要素原理が実際に使われる箇所である。まず、二つの部分集合が `A` のどこかに相違点を持つかを問う。持たなければ、両者は `A` の至る所で一致する。さらにどちらも `A` の中にとどまるので、もともと至る所で一致しており、外延性が両者を同一視する。持てば、最初の相違点が存在し、もう一つの判定、すなわちその点が第一の部分集合に属するかどうかによって、比較の向きが決まる。その点より下での一致はどちらの分岐でも自動的に成り立つ。その点の選び方から、それより下に相違点はないからである。

排中律は `agree` の内部で二度目に使われ、「相違しない」を「一致する」へ変える。この一歩はまさに二重否定の除去である。
<!--/-->

<!--en-->
The statement takes the two subsets `x` and `y` of `A` not as certificates of definability but as ordinary sets, together with the hypothesis that each stays inside `A`. The conclusion is a `Tri`, the three-way disjunction used throughout this chapter: `x` before `y`, equal as sets, or `y` before `x`. The proof begins by asking excluded middle about `Some`, and `Some` will be built as a proposition, namely a truncated existence statement, so `lem` may be fed `PT.squash₁` as its propositionhood certificate.
<!--zh-->
这里的陈述并不把 `A` 的两个子集 `x`、`y` 当作可定义性证书，而是当作普通集合，并附上二者都不超出 `A` 的前提。结论是一个 `Tri`，即本章通用的三分判断：`x` 先于 `y`、作为集合相等，或 `y` 先于 `x`。证明先对 `Some` 使用排中律发问；`Some` 将被构造成一个命题，即一条截断的存在陈述，因此可以把 `PT.squash₁` 作为其命题性证书交给 `lem`。
<!--ja-->
この定理は `A` の二つの部分集合 `x`、`y` を定義可能性の証明書としてではなく、普通の集合として受け取り、それぞれが `A` の中にとどまるという前提を添える。結論は本章で一貫して使われる三分の判断 `Tri`、すなわち `x` が `y` に先立つか、集合として等しいか、`y` が `x` に先立つかである。証明はまず `Some` について排中律を問うことに始まる。`Some` は命題、つまり截断された存在文として構成されるので、`PT.squash₁` をその命題性の証明として `lem` に渡せる。
<!--/-->

```agda
  precedes-tri : (x y : S) → ((w : S) → ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ A ⟩)
                           → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ A ⟩)
               → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
  precedes-tri x y x⊆ y⊆ = decide (lem (Some , PT.squash₁))
    where
```

<!--en-->
Two truncations organise the question. The predicate `Apart w` says, merely, that `w` distinguishes the two subsets, in either direction: it belongs to one and not the other. The truncated type `Some` says, merely, that some member of `A` is apart. Both are wrapped with `PT.squash₁`, so both are propositions rather than data; that is exactly what licenses deciding them by excluded middle, and later, eliminating a refutation of `Some` into contradiction.
<!--zh-->
两条截断组织了这个问题。谓词 `Apart w` 仅仅说 `w` 区分了这两个子集，方向不限：它属于其一而不属于另一。截断类型 `Some` 仅仅说 `A` 的某个成员是分歧点。二者都配以 `PT.squash₁`，因而都是命题而非数据；这正是可以用排中律判定它们、随后又能把 `Some` 的反驳消去成矛盾的依据。
<!--ja-->
二つの截断がこの問いを組織する。述語 `Apart w` は、`w` が二つの部分集合を区別すること、向きは問わず、片方には属しもう片方には属さないことを、単に主張する。截断型 `Some` は、`A` のある要素が相違点であることを単に主張する。どちらも `PT.squash₁` を添え、命題であってデータではない。これこそが、排中律による判定、さらに `Some` の反駁を矛盾への除去を正当化する。
<!--/-->

```agda
    Apart : S → Ω
    Apart w = ∥ (⟨ w ∈ˢ x ⟩ × (⟨ w ∈ˢ y ⟩ → Empty.⊥))
              ⊎ ((⟨ w ∈ˢ x ⟩ → Empty.⊥) × ⟨ w ∈ˢ y ⟩) ∥₁ , PT.squash₁
    Some : Type (ℓ-suc ℓ)
    Some = ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × ⟨ Apart a ⟩) ∥₁
```

<!--en-->
The helper `agree` converts absence of disagreement into agreement, one direction at a time. Its hypothesis `na` refutes `Apart w`, and its conclusion is the two inclusion clauses of membership equivalence at `w`. The conversion from a negative statement to the required membership implication is a double-negation-elimination step.
<!--zh-->
辅助引理 `agree` 把「无分歧」转成「一致」，一次一个方向。前提 `na` 反驳 `Apart w`，结论是 `w` 处成员等价的两条包含子句。证明只有这里需要从否定性陈述造出成员蕴含，而它实际上是化了装的双重否定消去。
<!--ja-->
補題 `agree` は「相違の不在」を「一致」へ変える。一度に一方向ずつである。前提 `na` は `Apart w` を反駁し、結論は `w` における所属同値の二つの包含節である。証明が否定形の命題から所属蕴含を作り出す必要があるのはここだけで、それは実質的に二重否定の除去となる。
<!--/-->

```agda
    agree : (w : S) → (⟨ Apart w ⟩ → Empty.⊥)
          → (⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩) × (⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩)
    agree w na = fwd , bwd
      where
      fwd : ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩
```

<!--en-->
For the forward clause, suppose `w ∈ˢ x` and ask excluded middle about `w ∈ˢ y`. If it holds, we are done. If its refutation `nh` is produced, then `w` is apart after all, witnessed by the left disjunct `wx , nh`; packaging that witness into the truncation and handing it to `na` yields a contradiction, from which `Empty.rec` produces any desired element, here the missing membership proof. The target `Empty.⊥` is a proposition, so eliminating the truncated `Apart w` into it is legitimate.
<!--zh-->
前向子句：设 `w ∈ˢ x`，对 `w ∈ˢ y` 用排中律发问。若成立即完成。若得到反驳 `nh`，那么 `w` 其实是分歧点，左析取支 `wx , nh` 就是见证；把该见证装入截断交给 `na` 便得矛盾，`Empty.rec` 再从矛盾产出所需元素，这里就是缺失的成员证明。目标 `Empty.⊥` 是命题，故把截断的 `Apart w` 消去到它是正当的。
<!--ja-->
前向きの節では、`w ∈ˢ x` を仮定し、`w ∈ˢ y` について排中律を問う。成り立てばそれで足りる。反駁 `nh` が得られたなら、実は `w` は相違点であり、左の選択肢 `wx , nh` がその証人である。この証人を截断に包んで `na` に渡せば矛盾が得られ、`Empty.rec` がそこから所望の要素、ここでは欠けた所属の証明を作る。目標 `Empty.⊥` は命題なので、截断された `Apart w` をそこへ除去するのは正当である。
<!--/-->

```agda
      fwd wx = pick (lem (w ∈ˢ y))
        where
        pick : (⟨ w ∈ˢ y ⟩ ⊎ (⟨ w ∈ˢ y ⟩ → Empty.⊥)) → ⟨ w ∈ˢ y ⟩
        pick (inl h)  = h
        pick (inr nh) = Empty.rec (na ∣ inl (wx , nh) ∣₁)
```

<!--en-->
The backward clause is the mirror image. Assuming `w ∈ˢ y`, excluded middle decides `w ∈ˢ x`; a refutation would make `w` apart through the right disjunct `nh , wy`, and `na` refutes that. Together the two clauses say: if no point of difference exists at `w`, membership in `x` and membership in `y` coincide at `w`.
<!--zh-->
后向子句是其镜像。设 `w ∈ˢ y`，排中律判定 `w ∈ˢ x`；若有反驳，则经右析取支 `nh , wy` 会使 `w` 成为分歧点，而 `na` 恰好反驳这一点。两条子句合起来说：若在 `w` 处不存在差异点，则属于 `x` 与属于 `y` 在 `w` 处重合。
<!--ja-->
後向きの節はその鏡像である。`w ∈ˢ y` を仮定し、排中律が `w ∈ˢ x` を判定する。反駁が得られたなら、右の選択肢 `nh , wy` を通じて `w` は相違点となり、`na` がまさにそれを反駁する。二つの節を合わせれば、`w` に差異の点が存在しない限り、`x` への所属と `y` への所属は `w` で一致する、ということになる。
<!--/-->

```agda
      bwd : ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩
      bwd wy = pick (lem (w ∈ˢ x))
        where
        pick : (⟨ w ∈ˢ x ⟩ ⊎ (⟨ w ∈ˢ x ⟩ → Empty.⊥)) → ⟨ w ∈ˢ x ⟩
        pick (inl h)  = h
```

<!--en-->
Now suppose `Some` is refuted, so no member of `A` is apart. The helper `nApart` packages this as a pointwise refutation of `Apart`, and `same` will use it at every `w` to prove the sets equal. The premise that the refuted witness lies in `A` is discharged next, and the membership equivalence of `agree` then applies at each point.
<!--zh-->
现在设 `Some` 被反驳，即 `A` 中没有分歧点。辅助引理 `nApart` 把这一点包装成对 `Apart` 的逐点反驳，`same` 将在每处 `w` 使用它来证明两集合相等。被反驳的见证落在 `A` 中这一前提在下一步了结，随后 `agree` 的成员等价即可在每点使用。
<!--ja-->
次に `Some` が反駁されたとする。つまり `A` の中に相違点はない。補題 `nApart` はこれを `Apart` の各点での反駁として包み、`same` はすべての `w` でそれを用いて二つの集合の相等を証明する。反駁された証人が `A` に属するという前提は次で処理され、その後 `agree` の所属同値が各点で適用できる。
<!--/-->

```agda
        pick (inr nh) = Empty.rec (na ∣ inr (nh , wy) ∣₁)
    same : (Some → Empty.⊥) → x ≡ y
    same ns = extensionalV step
      where
      nApart : (w : S) → ⟨ Apart w ⟩ → Empty.⊥
```

<!--en-->
An apart point always lies in `A`, provided the two subsets do. Indeed, the truncated disjunction `ha` is eliminated into the proposition `w ∈ˢ A`: if the left disjunct holds, `w` belongs to `x`, and `x⊆` moves it into `A`; if the right holds, `y⊆` does the same. Note the direction of the elimination: into a proposition-valued membership, which is exactly what propositional truncation permits.
<!--zh-->
只要两个子集都落在 `A` 中，分歧点必属于 `A`。事实上，截断析取 `ha` 被消去到命题 `w ∈ˢ A` 中：左支成立时 `w` 属于 `x`，`x⊆` 把它送进 `A`；右支成立时 `y⊆` 同理。注意消去的方向：进入取值为命题的成员关系，这恰是命题截断所允许的。
<!--ja-->
二つの部分集合が `A` の中にある限り、相違点は必ず `A` に属する。実際、截断された選言 `ha` は命題 `w ∈ˢ A` へと除去される。左の選言肢が成り立てば `w` は `x` に属し、`x⊆` がそれを `A` へ移す。右が成り立てば `y⊆` が同様に扱う。除去の向きに注意。命題値の所属関係への除去であり、これこそ命題的截断が許すことである。
<!--/-->

```agda
      nApart w ha = ns ∣ w , (inA , ha) ∣₁
        where
        inA : ⟨ w ∈ˢ A ⟩
        inA = PT.rec (snd (w ∈ˢ A))
          (λ { (inl (wx , _)) → x⊆ w wx ; (inr (_ , wy)) → y⊆ w wy }) ha
```

<!--en-->
At each `w`, the two clauses of `agree w (nApart w)` assert membership in `x` if and only if membership in `y`. The combinator `⇔toPath` promotes this iff between the two propositions `w ∈ˢ x` and `w ∈ˢ y` to a path between them as types, which is the form extensionality for the cumulative hierarchy consumes. Feeding the pointwise paths to `extensionalV` yields the path `x ≡ y`, so the `eq` branch of the trichotomy is closed.
<!--zh-->
在每处 `w`，`agree w (nApart w)` 的两条子句断言：属于 `x` 当且仅当属于 `y`。组合子 `⇔toPath` 把这两个命题 `w ∈ˢ x` 与 `w ∈ˢ y` 之间的这份当且仅当提升为二者作为类型之间的路径，而这正是累积层级的外延性所消费的形式。把逐点路径交给 `extensionalV` 便得路径 `x ≡ y`，于是三歧的 `eq` 分支得证。
<!--ja-->
各 `w` で、`agree w (nApart w)` の二つの節は、`x` への所属と `y` への所属が同値であると主張する。コンビネータ `⇔toPath` は、二つの命題 `w ∈ˢ x` と `w ∈ˢ y` の間のこの同値を、型としての両者の間のパスへ引き上げる。これは累積階層の外延性が受け取る形である。各点のパスを `extensionalV` に渡せばパス `x ≡ y` が得られ、三分法の `eq` の分岐が閉じる。
<!--/-->

```agda
      step : (w : S) → (w ∈ˢ x) ≡ (w ∈ˢ y)
      step w = ⇔toPath (agree w (nApart w) .fst) (agree w (nApart w) .snd)
    decide : (Some ⊎ (Some → Empty.⊥))
           → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
    decide (inr ns) = eq (same ns)
```

<!--en-->
In the other branch, `Some` holds: some member of `A` is apart. The smallest-element principle `baseLeast`, available for the base order `R` on the members of `A`, is applied to the predicate `Apart`, and it returns an explicit record `found`, not a truncated existence: a point `m` in `A`, apart, with nothing apart below it in the `R` order. This explicitness is what lets the least apart point be used as a witness later.
<!--zh-->
另一支中 `Some` 成立：`A` 的某个成员是分歧点。把最小元原则 `baseLeast` (对 `A` 的成员上的基底序 `R` 可用) 作用于谓词 `Apart`，它返回显式的记录 `found`，而非截断的存在陈述：一个点 `m`，在 `A` 中、分歧，且在 `R` 序之下其下方再无分歧点。正是这种显式性，使得最小分歧点此后能被用作见证。
<!--ja-->
もう一方の分岐では `Some` が成立する。つまり `A` のある要素が相違点である。`A` の要素上の基底順序 `R` に対して使える最小要素原理 `baseLeast` を述語 `Apart` に適用すると、截断された存在ではなく明示的なレコード `found` が返る。`A` に属し相違している点 `m` で、`R` 順序の下ではそれより下に相違点がない。この明示性こそが、最小の相違点を後に証人として使える理由である。
<!--/-->

```agda
    decide (inl hs) = side (lem (m ∈ˢ x))
      where
      found : Σ[ m ∈ S ] (⟨ m ∈ˢ A ⟩ × ⟨ Apart m ⟩
                × ((b : S) → ⟨ b ∈ˢ A ⟩ → ⟨ Apart b ⟩ → ⟨ R b m ⟩ → Empty.⊥))
      found = baseLeast Apart hs
```

<!--en-->
The components of `found` are unpacked once and named: the point `m`, its membership `m∈A` in `A`, the apartness `apartM`, and the leastness `belowM`. Giving each a name keeps the two symmetric branches below readable, since each will cite several of these fields.
<!--zh-->
`found` 的各分量被一次性拆开并命名：点 `m`、其在 `A` 中的成员关系 `m∈A`、分歧性 `apartM`、以及最小性 `belowM`。逐一命名使下面两个对称分支保持可读，因为每一支都要引用其中若干字段。
<!--ja-->
`found` の各成分は一度ほどいて名前を与えられる。点 `m`、`A` への所属 `m∈A`、相違性 `apartM`、最小性 `belowM` である。それぞれに名を付けておくことで、以下の対称な二つの分岐が読みやすくなる。両者ともこれらの欄のいくつかを引用するからである。
<!--/-->

```agda
      m : S
      m = found .fst
      m∈A : ⟨ m ∈ˢ A ⟩
      m∈A = found .snd .fst
      apartM : ⟨ Apart m ⟩
```

<!--en-->
The leastness field `belowM` refutes any apart point strictly below `m`; its argument order is rearranged here to put the comparison hypothesis last, which suits the coming uses. With the least apart point in hand, excluded middle decides whether `m` belongs to `x`, and `side` turns each answer into a branch of the trichotomy.
<!--zh-->
最小性字段 `belowM` 反驳任何严格低于 `m` 的分歧点；这里把它改排为比较假设在末位的形式，以配合即将到来的用法。手握最小分歧点之后，排中律判定 `m` 是否属于 `x`，`side` 把每个答案化为三歧的一个分支。
<!--ja-->
最小性の欄 `belowM` は、`m` より真に下にある相違点を反駁する。ここでは比較の仮定が末尾に来るよう引数の順を組み替えており、今後の使用に適する。最小の相違点を手にすれば、最後にもう一度排中律が `m` が `x` に属するかを判定し、`side` がそれぞれの答えを三分法の一分岐へ変える。
<!--/-->

```agda
      apartM = found .snd .snd .fst
      belowM : (w : S) → ⟨ w ∈ˢ A ⟩ → ⟨ R w m ⟩ → ⟨ Apart w ⟩ → Empty.⊥
      belowM w w∈A hw ha = found .snd .snd .snd w w∈A ha hw
      side : (⟨ m ∈ˢ x ⟩ ⊎ (⟨ m ∈ˢ x ⟩ → Empty.⊥))
           → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
```

<!--en-->
If `m` does belong to `x`, then `m` witnesses that `y` comes before `x`: it lies in the second set and not the first. The sublemma `m∉y` refutes `m ∈ˢ y` by case analysis on the truncated `apartM`: in the left disjunct the witness itself carries a refutation of `m ∈ˢ y`, and in the right disjunct the refutation of `m ∈ˢ x` clashes with `mx`. Eliminating the truncation is allowed because the target `Empty.⊥` is a proposition.
<!--zh-->
若 `m` 确实属于 `x`，则 `m` 见证 `y` 先于 `x`：它在第二个集合中而不在第一个中。子引理 `m∉y` 通过对截断的 `apartM` 作情形分析来反驳 `m ∈ˢ y`：左支中见证本身就带有对 `m ∈ˢ y` 的反驳；右支中对 `m ∈ˢ x` 的反驳与 `mx` 相抵触。消去截断是允许的，因为目标 `Empty.⊥` 是命题。
<!--ja-->
`m` が実際に `x` に属するなら、`m` は `y` が `x` に先立つことの証人である。第二の集合に属し第一には属さないからである。補題 `m∉y` は、截断された `apartM` の場合分けによって `m ∈ˢ y` を反駁する。左の選言肢では証人自身が `m ∈ˢ y` の反駁を帯びており、右では `m ∈ˢ x` の反駁が `mx` と衝突する。目標 `Empty.⊥` が命題であるため、この截断の除去は許される。
<!--/-->

```agda
      side (inl mx) = gt ∣ m , (m∈A , (mx , (m∉y , ag))) ∣₁
        where
        m∉y : ⟨ m ∈ˢ y ⟩ → Empty.⊥
        m∉y my = PT.rec Empty.isProp⊥
          (λ { (inl (_ , nmy)) → nmy my ; (inr (nmx , _)) → nmx mx }) apartM
```

<!--en-->
Agreement below `m` also swaps sides for free. For each `w` below `m`, `belowM` refutes `Apart w`, so `agree w` applies and gives membership equivalence in both directions; the pair is merely written in the reversed order, producing `Agrees R A y x m` from an agreement originally oriented from `x` to `y`. Together with `m∈A`, `mx` and `m∉y`, this is a complete `Witness` that `y` precedes `x`, delivered inside the truncation by `gt`.
<!--zh-->
`m` 之下的一致性也免费换边。对 `m` 之下的每个 `w`，`belowM` 反驳 `Apart w`，故 `agree w` 适用，给出双向的成员等价；这里只是把二元组按相反次序写出，把原本从 `x` 到 `y` 取向的一致性变成 `Agrees R A y x m`。与 `m∈A`、`mx`、`m∉y` 合起来，这是一份完整的 `Witness`，见证 `y` 先于 `x`，由 `gt` 装入截断交付。
<!--ja-->
`m` より下での一致も、向きの交換がただで手に入る。`m` より下の各 `w` に対し `belowM` が `Apart w` を反駁するので `agree w` が適用でき、両方向の所属同値が得られる。組を逆向きに書き並べるだけで、元は `x` から `y` へ向いていた一致から `Agrees R A y x m` が作られる。`m∈A`、`mx`、`m∉y` と合わせて、これは `y` が `x` に先立つことの完全な `Witness` であり、`gt` が截断の中で渡す。
<!--/-->

```agda
        ag : Agrees R A y x m
        ag w w∈A hw = agree w (belowM w w∈A hw) .snd , agree w (belowM w w∈A hw) .fst
      side (inr nmx) = lt ∣ m , (m∈A , (my , (nmx , ag))) ∣₁
        where
        my : ⟨ m ∈ˢ y ⟩
```

<!--en-->
The mirrored branch assumes instead that `m` does not belong to `x`, and produces the `lt` witness that `x` precedes `y`. Extracting `m ∈ˢ y` from `apartM` is another truncated case analysis: the left disjunct would assert `m ∈ˢ x`, refuted by `nmx`, so only the right disjunct survives and it carries the membership outright. Agreement below `m` needs no reversal this time, since the witness is oriented from `x` to `y` exactly as `agree` produces it. With both symmetric branches in place, the trichotomy of `precedes` is complete, and the local order on a stage is a linear order on its members, pending well-foundedness.
<!--zh-->
镜像的一支改设 `m` 不属于 `x`，产出 `x` 先于 `y` 的 `lt` 见证。从 `apartM` 提取 `m ∈ˢ y` 又是一次截断情形分析：左支会断言 `m ∈ˢ x`，被 `nmx` 反驳，故只有右支存活，而它直接带有该成员关系。这次 `m` 之下的一致性无须换向，因为见证的取向恰与 `agree` 的产出一致。两个对称分支齐备后，`precedes` 的三歧完成，一层上的局部序便是其成员上的线序，只待良基性。
<!--ja-->
鏡像の分岐は、代わりに `m` が `x` に属さないと仮定し、`x` が `y` に先立つことの `lt` の証人を作る。`apartM` から `m ∈ˢ y` を取り出すのもまた截断の場合分けである。左の選言肢は `m ∈ˢ x` を主張することになり `nmx` が反駁するので、右の選言肢だけが生き残り、それは所属をそのまま帯びている。今回 `m` より下の一致は向きの交換を要しない。証人の向きが `agree` の作るものと一致しているからである。対称な二つの分岐がそろい、`precedes` の三分法が完成し、段階上の局所順序は整礎性を残して要素上の線順序となる。
<!--/-->

```agda
        my = PT.rec (snd (m ∈ˢ y))
          (λ { (inl (mx , _)) → Empty.rec (nmx mx) ; (inr (_ , h)) → h }) apartM
        ag : Agrees R A x y m
        ag w w∈A hw = agree w (belowM w w∈A hw)
```

<!--en-->
## The finite stages

Recursion over numerals carries both a tally and an earliest-disagreement
well-order from each finite stage to the next.

The stages indexed by numerals are the finite ones, and the order on each is
built by recursion: stage zero is empty, and the order on the stage after `n` is
comparison at the earliest disagreement over stage `n`, with stage `n`'s own
order as the base. `before-irrefl` holds at every stage and needs no induction,
since irreflexivity of the comparison needed no hypothesis and stage zero carries
no comparison at all.
<!--zh-->
## 有穷诸层

沿数码的递归把点名册与最先分歧良序从每个有穷层传到下一层。

以数码为索引的层正是有穷层，每层上的序由递归构造：第零层为空；`n` 的后继层上的序以层 `n` 自身的序为基础，并按最先分歧处比较层 `n` 的可定义子集。`before-irrefl` 在每层都成立且无需归纳，因为该比较的非自反性不需要前提，而第零层没有任何比较。
<!--ja-->
## 有限段階

数項上の再帰により、数え上げと最初の相違による整列順序を各有限段階から次の段階へ同時に運ぶ。

数項で添字づけられた段階こそ有限の段階であり、各段階上の順序は再帰によって構成される。段階零は空であり、`n` の後者の段階上の順序は、段階 `n` 自身の順序を基底として、段階 `n` の定義可能部分集合を最初の相違点で比較するものである。`before-irrefl` はすべての段階で成立し、帰納を要しない。この比較の非反射性は前提を要さず、段階零にはそもそも比較が存在しないからである。
<!--/-->

<!--en-->
The definition begins with a small piece of plumbing for the three-way judgment. `Tri-map` acts on a `Tri` by applying one function in each alternative; the three clauses are its computation rules. It will convert the trichotomy proved about two sets into the trichotomy needed about two points of a stage, which differ only by carrying membership proofs.
<!--zh-->
定义从三分判断的一件小工具开始。`Tri-map` 对 `Tri` 逐支作用：每个备选支各应用一个函数；三条子句就是它的计算规则。它将把「关于两个集合证明的三歧」转换为「关于一层的两个点所需的三歧」，二者只差是否附带成员证明。
<!--ja-->
定義は、三分の判断のための小さな道具から始まる。`Tri-map` は `Tri` の選言肢ごとに関数を一つ適用するものであり、三つの節がその計算規則である。これは、二つの集合について証明された三分法を、段階の二つの点について必要な三分法へ変換するのに使われる。両者は所属の証明を帯びるかどうかだけが違う。
<!--/-->

```agda
Tri-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}
          {A₁ : Type ℓ₁} {B₁ : Type ℓ₂} {C₁ : Type ℓ₃}
          {A₂ : Type ℓ₄} {B₂ : Type ℓ₅} {C₂ : Type ℓ₆}
        → (A₁ → A₂) → (B₁ → B₂) → (C₁ → C₂) → Tri A₁ B₁ C₁ → Tri A₂ B₂ C₂
Tri-map f g h (lt a) = lt (f a)
```

<!--en-->
The stages indexed by numerals are named: `finiteStage n` is the stage `Lset (# n)`. The relation `before` is then a recursion on the index. At zero it is the falsity truth value, so no pair is ever related. At a successor it is `precedes` applied to the previous stage: the base set over which membership is compared is the stage `n` itself, and the base order along which the earliest disagreement is sought is `before n`, the order the recursion built one step down.
<!--zh-->
以数码为索引的层在此命名：`finiteStage n` 即层 `Lset (# n)`。关系 `before` 随后是对索引的递归。零处它取假真值，任何一对都不会被关系到。后继处它是对前一层使用 `precedes`：比较隶属关系的基底集合就是层 `n` 本身，而寻找最先分歧所沿的基底序是 `before n`，即递归在下一层造出的那个序。
<!--ja-->
数項で添字づけられた段階に名が与えられる。`finiteStage n` は段階 `Lset (# n)` である。関係 `before` は続いて添字上の再帰である。零では偽の真理値が取られ、いかなる対も関係されない。後者では `precedes` を一つ下の段階に適用したものである。所属を比較する基底集合は段階 `n` そのもの、最初の相違点を探す際にたどる基底順序は一段下で再帰が作った `before n` である。
<!--/-->

```agda
Tri-map f g h (eq b) = eq (g b)
Tri-map f g h (gt c) = gt (h c)

finiteStage : ℕ → S
finiteStage n = Lset (# n)

before : ℕ → S → S → Ω
```

<!--en-->
Irreflexivity of `before` holds at every numeral, and its proof does no induction. At zero the hypothesis is a proof of falsity, which `Empty.rec*` eliminates. At a successor it is exactly `precedes-irrefl`, the hypothesis-free irreflexivity established when the comparison was defined. This is why irreflexivity is not one of the data the recursion has to carry.
<!--zh-->
`before` 的非自反性在所有数码处成立，且证明不作归纳。零处前提是假命题的证明，由 `Empty.rec*` 消去；后继处恰是 `precedes-irrefl`，即定义该比较时已确立的无前提非自反性。正因如此，非自反性不属于递归必须携带的数据。
<!--ja-->
`before` の非反射性はすべての数項で成立し、その証明は帰納を行わない。零では前提は偽の真理値の住人であり、`Empty.rec*` がそれを除去する。後者ではまさに `precedes-irrefl`、つまりこの比較を定義した際に前提なしで確立された非反射性である。だからこそ、非反射性は再帰が運ぶべきデータには入らない。
<!--/-->

```agda
before zero    x y = ⊥
before (suc n) = precedes (before n) (finiteStage n)

before-irrefl : (n : ℕ) (x : S) → ⟨ before n x x ⟩ → Empty.⊥
before-irrefl zero    x h = Empty.rec* h
before-irrefl (suc n) x h = precedes-irrefl (before n) (finiteStage n) x h
```

<!--en-->
The base case's emptiness is recorded separately as `zero-empty`: no set is a member of the stage zero. Reading a membership certificate out of `Lset (# zero)` produces, merely, some stage `δ` with `δ` a member of the numeral zero and `x` a definable subset of `Lset δ`; the numeral zero has no members, and `∅-empty` turns any alleged member into a contradiction. The elimination of the truncation is legitimate because the target `Empty.⊥` is a proposition.
<!--zh-->
基例的空性单独记录为 `zero-empty`：没有集合是第零层的成员。从 `Lset (# zero)` 读出成员证书，仅仅给出某一层 `δ`，使 `δ` 属于数码零且 `x` 是 `Lset δ` 的可定义子集；数码零没有成员，`∅-empty` 把任何所谓的成员变成矛盾。由于目标 `Empty.⊥` 是命题，消去该截断是正当的。
<!--ja-->
基底の場合の空性は `zero-empty` として別に記録される。段階零の要素となる集合はない。`Lset (# zero)` から所属の証明書を読み出すと、単に、`δ` が数項零の要素で `x` が `Lset δ` の定義可能部分集合であるようなある段階 `δ` が得られるだけである。数項零に要素はなく、`∅-empty` がいかなる所属の主張も矛盾へ変える。目標 `Empty.⊥` が命題であるため、この截断の除去は正当である。
<!--/-->

```agda

zero-empty : (x : S) → ⟨ x ∈ˢ finiteStage zero ⟩ → Empty.⊥
zero-empty x h = PT.rec Empty.isProp⊥ step (Lset-out (# zero) x h)
  where
  step : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → Empty.⊥
  step (δ , δ∈ , _) = ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈)
```

<!--en-->
What the recursion has to carry is a tally, trichotomy and transitivity, and
nothing else: irreflexivity holds automatically at every stage, and
well-foundedness is derived where it is used rather than transported.
A point of a stage is a set together with its membership, which is a
proposition, so two points are equal as soon as their sets are; that is all the
work involved in passing between the statements about sets and the bundle, whose
carrier must be a type.
<!--zh-->
递归必须携带的数据只有一份对成员的清点、三歧与传递：非自反性在每层都自动成立，而良基性只在用到之处当场推出，不必随身携带。层的一个点是一个集合连同它的隶属证明；由于隶属是命题，两个点只要集合相等就相等。在「关于集合的陈述」与「载体必须是类型的那个束」之间往返时，需要做的全部工作就在于此。
<!--ja-->
再帰が運ぶべきデータは、要素の数え上げ、三分法、推移性の三つだけであり、それ以外には何もない。非反射性はすべての段階で自動的に成立し、整礎性は使う箇所でその場で導出されるので、運ぶ必要はない。段階の点とは集合にその所属の証明を添えたものであり、所属は命題なので、二つの点は集合が等しければただちに等しい。「集合についての述定」と「台が型でなければならない束」との間を行き来するのに必要な作業は、これだけである。
<!--/-->

<!--en-->
The search machinery of the earlier section works over a type, so a member of a stage is packaged as a `Point`: a set together with its membership certificate in `finiteStage n`. The relation `Below` reads `before n` at the underlying sets. Since membership is a proposition, two points with the same set are already equal; this one fact does all the work of moving between statements about sets and statements about points.
<!--zh-->
前节的搜索机制作用在类型上，故层的一个成员被包装成 `Point`：一个集合连同它在 `finiteStage n` 中的成员证书。关系 `Below` 在底层集合处读取 `before n`。由于隶属是命题，集合相同的两个点已然相等；这一个事实承担了「关于集合的陈述」与「关于点的陈述」之间往返的全部工作。
<!--ja-->
前節の探索機構は型の上で働くので、段階の要素は `Point` として包まれる。すなわち、集合に `finiteStage n` への所属の証明書を添えたものである。関係 `Below` は根底の集合で `before n` を読む。所属は命題なので、同じ集合を持つ二つの点ははじめから等しい。この一事実が、「集合についての述定」と「点についての述定」との間の行き来のすべての作業を担う。
<!--/-->

```agda
Point : ℕ → Type (ℓ-suc ℓ)
Point n = Σ[ x ∈ S ] ⟨ x ∈ˢ finiteStage n ⟩

Below : (n : ℕ) → Point n → Point n → Type (ℓ-suc ℓ)
Below n a b = ⟨ before n (a .fst) (b .fst) ⟩

record StageOrder (n : ℕ) : Type (ℓ-suc ℓ) where
```

<!--en-->
The induction at stage `n` retains exactly the facts needed for the successor: a tally of `finiteStage n`, trichotomy of `before n` for members of that stage, and transitivity of `before n` on arbitrary sets. Irreflexivity follows uniformly from earliest disagreement, while well-foundedness is recovered from the tally whenever the local order is used.
<!--zh-->
层 `n` 的归纳恰好保留后继步所需的事实：`finiteStage n` 的点名册、`before n` 对该层成员的三歧性，以及 `before n` 对任意集合的传递性。非自反性由最先分歧统一推出；局部序需要良基性时，则从点名册重新得到。
<!--ja-->
段階 `n` の帰納は、後者の一歩に必要な事実だけを保つ。すなわち `finiteStage n` の数え上げ、その段階の要素に対する `before n` の三岐性、そして任意の集合に対する `before n` の推移性である。非反射性は最初の相違から一様に従い、局所順序の整礎性は必要なときに数え上げから得られる。
<!--/-->

```agda
  field
    tally : Tally (finiteStage n)
    tri   : (x y : S) → ⟨ x ∈ˢ finiteStage n ⟩ → ⟨ y ∈ˢ finiteStage n ⟩
          → Tri ⟨ before n x y ⟩ (x ≡ y) ⟨ before n y x ⟩
    trans : (x y z : S) → ⟨ before n x y ⟩ → ⟨ before n y z ⟩ → ⟨ before n x z ⟩
```

<!--en-->
Inside `Ordered`, the first task is trichotomy about points. `triPoint` applies `Tri-map` to the trichotomy `tri` about sets; the middle component, where the conclusion is a path, needs converting, and `Σ≡Prop` supplies exactly that: a path between the underlying sets extends to a path between the points, because the second components are proofs of a proposition.
<!--zh-->
在 `Ordered` 内部，第一项任务是关于点的三歧。`triPoint` 把关于集合的三歧 `tri` 交给 `Tri-map`；中间一支的结论是路径，需要转换，`Σ≡Prop` 恰好提供这一点：由于第二分量是某个命题的证明，底层集合之间的路径可以延拓为点之间的路径。
<!--ja-->
`Ordered` の内部での最初の課題は、点についての三分法である。`triPoint` は集合についての三分法 `tri` を `Tri-map` に渡す。中央の選言肢は結論がパスなので変換が要り、`Σ≡Prop` がまさにそれを供給する。第二成分は命題の証明であるから、根底の集合の間のパスは点の間のパスへ延長できる。
<!--/-->

```agda

module Ordered (n : ℕ) (r : StageOrder n) where
  open StageOrder r public
  open Tally tally

  triPoint : (a b : Point n) → Tri (Below n a b) (a ≡ b) (Below n b a)
  triPoint a b = Tri-map id (Σ≡Prop (λ z → snd (z ∈ˢ finiteStage n))) id
```

<!--en-->
The tally is lifted from sets to points by pairing each entry with its own membership proof, giving `points`. The coverage statement `covers` is then `onto` transported through this pairing: given a point, `onto` merely provides an index whose entry has the same set, and `Σ≡Prop` upgrades the equality of sets to an equality of points. Coverage remains truncated, as it was for the tally itself.
<!--zh-->
点名册由集合提升到点：把每个条目配上它自己的成员证明，得到 `points`。覆盖陈述 `covers` 随后是 `onto` 经这一配对的搬运：给定一个点，`onto` 仅仅提供一个索引，其条目具有相同的集合，`Σ≡Prop` 再把集合的等式升级为点的等式。覆盖仍然是截断的，与点名册本身一样。
<!--ja-->
数え上げは、各項にそれ自身の所属の証明を対にすることで、集合から点へ引き上げられ `points` となる。被覆の述定 `covers` は、この対を通して `onto` を運んだものである。点が与えられれば、`onto` は同じ集合を持つ項の添字を単に提供し、`Σ≡Prop` が集合の等式を点の等式へ引き上げる。被覆は数え上げ自身と同様、截断されたままである。
<!--/-->

```agda
    (tri (a .fst) (b .fst) (a .snd) (b .snd))

  points : Fin size → Point n
  points i = item i , inside i

  covers : (a : Point n) → ∥ Σ[ i ∈ Fin size ] (points i ≡ a) ∥₁
  covers a = PT.map (λ { (i , q) → i , Σ≡Prop (λ z → snd (z ∈ˢ finiteStage n)) q })
```

<!--en-->
For points of the stage, trichotomy, irreflexivity and transitivity combine with the finite tally to give two consequences. Finite search yields a least point satisfying any merely inhabited predicate, and the same least-counterexample argument yields well-foundedness of the point relation.
<!--zh-->
在层的点上，三歧、非自反与传递同有穷点名册结合，给出两个结论：有穷扫描为每个仅仅非空的谓词找出最小点，而同一个最小反例论证给出点关系的良基性。
<!--ja-->
段階の点について、三岐性・非反射性・推移性を有限な数え上げと合わせると二つの帰結が得られる。有限走査は単に非空な任意の述語に最小の点を与え、同じ最小反例の議論が点の関係の整礎性を与える。
<!--/-->

```agda
    (onto (a .fst) (a .snd))

  open Search (Below n) triPoint (λ a → before-irrefl n (a .fst))
              (λ a b c → trans (a .fst) (b .fst) (c .fst)) public
  open Over size points covers public

  order : SWO (Point n)
```

<!--en-->
These facts determine a strict well-order on the points of `finiteStage n`: the relation is `Before n`, its three order laws come from the stage comparison, and its well-foundedness comes from finite search. The construction therefore separates the local comparison from the finiteness argument that rules out infinite descent.
<!--zh-->
这些事实确定了 `finiteStage n` 诸点上的严格良序：关系是 `Before n`，三条序律来自层比较，良基性则来自有穷扫描。因此，构造清楚地区分了局部比较与排除无穷下降的有穷性论证。
<!--ja-->
これらの事実は `finiteStage n` の点上の狭義整列順序を定める。関係は `Before n`、三つの順序法則は段階内の比較から、整礎性は有限走査から得られる。この構成では局所的な比較と、無限降下を排除する有限性の議論が明確に分かれている。
<!--/-->

```agda
  order = record
    { _<∙_   = Below n
    ; tri∙   = triPoint
    ; irr∙   = λ a → before-irrefl n (a .fst)
    ; trans∙ = λ a b c → trans (a .fst) (b .fst) (c .fst)
```

<!--en-->
The last lemma packages least elements in the shape the next stage needs. `leastMem` takes a predicate `P` on sets that is merely satisfied by some member of the stage, and returns an explicit member `m` satisfying `P`, together with leastness in the `before n` order: no member `b` of the stage satisfying `P` lies strictly below `m`. Nothing here is truncated except the hypothesis.
<!--zh-->
最后一条引理以下一层所需的形状包装最小元。`leastMem` 取集合上的一个谓词 `P`，它仅仅被该层的某个成员满足，并返回显式的满足 `P` 的成员 `m`，连同 `before n` 序下的最小性：该层中满足 `P` 的成员 `b` 没有严格低于 `m` 的。除前提外，这里没有任何截断。
<!--ja-->
最後の補題は、最小要素を次の段階が必要とする形に包む。`leastMem` は、段階のある要素に単に満たされる集合上の述語 `P` を受け取り、`P` を満たす明示的な要素 `m` を、`before n` 順序での最小性、すなわち `P` を満たす段階の要素 `b` で `m` より真に下にあるものが存在しないこととともに返す。前提を除けば、ここに截断はない。
<!--/-->

```agda
    ; wf∙    = wellFounded }

  leastMem : (P : S → Ω) → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ finiteStage n ⟩ × ⟨ P a ⟩) ∥₁
           → Σ[ m ∈ S ] (⟨ m ∈ˢ finiteStage n ⟩ × ⟨ P m ⟩
               × ((b : S) → ⟨ b ∈ˢ finiteStage n ⟩ → ⟨ P b ⟩
                          → ⟨ before n b m ⟩ → Empty.⊥))
```

<!--en-->
The proof runs the search at the point level and unpacks the result. `least` is applied to the lifted predicate and the repackaged truncated witness, returning an explicit pair: a point `m` and its `Least` certificate. The three components of the point and the two of the certificate are then reassembled into the set-level statement, with the leastness clause composed by applying the certificate to the pair `b , b∈`.
<!--zh-->
证明在点的层面运行搜索并拆包结果。`least` 作用于提升后的谓词与重新包装的截断见证，返回显式的对：一个点 `m` 及其 `Least` 证书。随后把点的三个分量与证书的两个分量重新装配成集合层面的陈述，最小性子句由把证书作用于对 `b , b∈` 而得。
<!--ja-->
証明は点の水準で探索を走らせ、結果をほどく。`least` を引き上げた述語と包装し直した截断的証人に適用すると、明示的な対、点 `m` とその `Least` の証明書が返る。点の三つの成分と証明書の二つの成分を集合水準の述定へ組み立て直し、最小性の節は証明書を対 `b , b∈` に適用することで作られる。
<!--/-->

```agda
  leastMem P h = found .fst .fst
               , ( found .fst .snd
                 , ( found .snd .fst
                   , (λ b b∈ pb hb → found .snd .snd (b , b∈) pb hb) ) )
    where
```

<!--en-->
Only the glue remains visible: `Q` reads the set-level predicate at the underlying set of a point, and `found` invokes `least` with the truncated hypothesis repackaged from a triple into a pair of a point and a proof. This `leastMem` is exactly what the recursion feeds to `Difference` as `baseLeast` at the successor stage, closing the loop between the search machinery and the earliest-disagreement order.
<!--zh-->
剩下的只是粘合：`Q` 在点的底层集合处读取集合层面的谓词，`found` 以从三元组重新包装成「一个点加一个证明」的截断前提调用 `least`。这条 `leastMem` 正是递归在后继层作为 `baseLeast` 喂给 `Difference` 的东西，它把搜索机制与最先分歧序之间的环节闭合。
<!--ja-->
残るのは接合だけである。`Q` は点の根底の集合で集合水準の述語を読み、`found` は三つ組から「点と証明の対」へ包装し直した截断的前提で `least` を呼ぶ。この `leastMem` こそ、後者の段階で再帰が `baseLeast` として `Difference` に渡すものであり、探索機構と最初の相違の順序との環を閉じる。
<!--/-->

```agda
    Q : Point n → Ω
    Q a = P (a .fst)
    found : Σ[ m ∈ Point n ] Least Q m
    found = least Q (PT.map (λ { (a , a∈ , pa) → (a , a∈) , pa }) h)
```

<!--en-->
The recursion starts with the empty tally and vacuous order laws at stage zero. At a successor, the previous tally is lifted across the definable power set. Earliest disagreement supplies trichotomy from the two subset hypotheses and supplies transitivity directly from the preceding stage's order; the successor-stage identity is used only where membership must be moved between the stage and that definable power set.
<!--zh-->
递归在第零层取空点名册，两条序律由空性成立。到后继层，上一层的点名册经可定义幂集提升。最先分歧比较利用两条子集前提给出三歧，并直接从上一层的序推出传递性；只有在成员关系需要于该层与其可定义幂集之间转换时，才使用后继层恒等式。
<!--ja-->
再帰は零段階の空の数え上げと、空性から従う順序法則から始まる。後者段階では、一つ前の数え上げを定義可能冪集合へ持ち上げる。最初の相違による比較は、二つの部分集合条件から三岐性を与え、前段階の順序から推移性を直接与える。後者段階の同一視を使うのは、段階とその定義可能冪集合の間で所属を移す箇所だけである。
<!--/-->

<!--en-->
The base case assembles a record whose three fields are the three small facts just displayed. The tally `empty` has size zero: the index type `Fin zero` is empty, so the entry and membership fields are given by the absurd pattern, functions from no possible arguments. There is nothing to list at stage zero, and that is the whole content of the tally.
<!--zh-->
基例把三个字段装配成一个记录，三者正是刚建立的三件小事。点名册 `empty` 的长度为零：索引类型 `Fin zero` 为空，故条目与成员字段都用荒谬模式给出，即从无可能实参出发的函数。第零层没有可列的东西，这就是该点名册的全部内容。
<!--ja-->
基底の場合、三つの欄を一つのレコードに組み立てる。それらはまさに今示した三つの小さな事実である。数え上げ `empty` のサイズは零である。添字型 `Fin zero` は空なので、項と所属の欄は荒謬パターン、すなわち与えられない引数に対する関数で与えられる。段階零には列挙すべきものがなく、それがこの数え上げの内容のすべてである。
<!--/-->

```agda
stageOrder : (n : ℕ) → StageOrder n
stageOrder zero = record { tally = empty ; tri = triZero ; trans = transZero }
  where
  empty : Tally (finiteStage zero)
  empty = record
```

<!--en-->
The remaining fields of the zero-stage tally have the same source. Its membership certificate for any listed item is impossible because there is no index, while coverage of the stage follows from `zero-empty`: a supposed member of `finiteStage zero` yields a contradiction. Thus `empty` really enumerates the empty stage in both directions.
<!--zh-->
第零层点名册的其余字段来自同一个事实。任何被列条目的成员证书都不可能出现，因为根本没有索引；而层的覆盖则由 `zero-empty` 给出：假设 `finiteStage zero` 有成员便导出矛盾。因此，`empty` 在两个方向上都确实枚举了空层。
<!--ja-->
零段階の数え上げの残る欄も、同じ事実から得られる。添字が存在しないため、列挙された項の所属証明は生じようがなく、段階の被覆は `zero-empty` から従う。`finiteStage zero` の要素を仮定すれば矛盾が得られるからである。したがって `empty` は両方向で空の段階を正確に列挙している。
<!--/-->

```agda
    { size   = zero
    ; item   = λ ()
    ; inside = λ ()
    ; onto   = λ x x∈ → Empty.rec (zero-empty x x∈) }
  triZero : (x y : S) → ⟨ x ∈ˢ finiteStage zero ⟩ → ⟨ y ∈ˢ finiteStage zero ⟩
```

<!--en-->
The two order fields are vacuous. Trichotomy at zero receives membership certificates for `x` and `y`, but no such certificates exist, so `zero-empty` extracts a contradiction from the first and discharges the goal. Transitivity at zero receives a hypothesis of type `before zero x y`, which by the computation rule of `before` is the falsity truth value, and `Empty.rec*` eliminates it. Empty premises make empty conclusions; no property of the empty order is used beyond its being empty.
<!--zh-->
两条序字段都是空洞的。零处的三歧收到 `x` 与 `y` 的成员证书，但这样的证书不存在，`zero-empty` 从第一个提取矛盾并了结目标。零处的传递收到类型为 `before zero x y` 的前提，按 `before` 的计算规则它是假真值，由 `Empty.rec*` 消去。空前提给出空结论；除「这个序是空的」之外，没有使用空序的任何性质。
<!--ja-->
二つの順序の欄は空虚である。零での三分法は `x` と `y` の所属の証明書を受け取るが、そのような証明書は存在しないので、`zero-empty` が一つ目から矛盾を取り出して目標を処理する。零での推移性は型が `before zero x y` である前提を受け取るが、`before` の計算規則によりそれは偽の真理値であり、`Empty.rec*` が除去する。空の前提が空の結論を作る。この順序が空であること以外に、空の順序の性質は使われない。
<!--/-->

```agda
          → Tri ⟨ before zero x y ⟩ (x ≡ y) ⟨ before zero y x ⟩
  triZero x y x∈ y∈ = Empty.rec (zero-empty x x∈)
  transZero : (x y z : S) → ⟨ before zero x y ⟩ → ⟨ before zero y z ⟩
            → ⟨ before zero x z ⟩
  transZero x y z h k = Empty.rec* h
```

<!--en-->
The successor step needs three mathematical inputs from stage `n`: its least-element principle, the trichotomy and transitivity of `before n`, and a tally of its members. The first two make earliest disagreement a strict comparison on subsets of that stage, while the tally enumerates those subsets through Boolean masks. Together they provide exactly the tally and order laws required at stage `suc n`.
<!--zh-->
后继步需要层 `n` 的三类数学输入：其最小元原理、`before n` 的三歧与传递性，以及其成员的一份点名册。前两类使最先分歧成为该层诸子集上的严格比较，点名册则通过布尔掩码枚举这些子集；三者共同给出层 `suc n` 所需的点名册与序律。
<!--ja-->
後者の一歩が段階 `n` から必要とする数学的入力は、その最小要素原理、`before n` の三岐性と推移性、そして要素の数え上げである。前二者により最初の相違はその段階の部分集合上の狭義比較となり、数え上げはブールマスクを通してそれらの部分集合を列挙する。これらが段階 `suc n` に必要な数え上げと順序法則を与える。
<!--/-->

```agda
stageOrder (suc n) = record { tally = raised ; tri = triSuc ; trans = transSuc }
  where
  module Prev = Ordered n (stageOrder n)
  module Diff = Difference (before n) (finiteStage n) Prev.tri Prev.trans Prev.leastMem
  module Power = PowerStep (# n) (numeral-ord n) Prev.tally
```

<!--en-->
The identification `step` is the path `Lset-suc (# n)`, stating that the stage after `n` is the definable power set of stage `n`. The new tally `raised` keeps the size and the items of the power tally, so it enumerates the same definable subsets; what changes is only where the membership certificates are read, which is where `step` enters.
<!--zh-->
认同 `step` 是路径 `Lset-suc (# n)`，它断言 `n` 的后继层就是层 `n` 的可定义幂集。新点名册 `raised` 保留幂集点名册的长度与条目，因此枚举的是同样的可定义子集；改变的只是成员证书从何处读取，这正是 `step` 进入之处。
<!--ja-->
同一視 `step` はパス `Lset-suc (# n)` であり、`n` の後者の段階が段階 `n` の定義可能冪集合であると述べる。新しい数え上げ `raised` は冪数え上げのサイズと項をそのまま保つので、列挙するのは同じ定義可能部分集合である。変わるのは所属の証明書をどこから読むかだけであり、そこに `step` が現れる。
<!--/-->

```agda

  step : finiteStage (suc n) ≡ 𝒟ₒ (finiteStage n)
  step = Lset-suc (# n)

  raised : Tally (finiteStage (suc n))
  raised = record
    { size   = Tally.size Power.powerTally
```

<!--en-->
The `inside` field transports each membership certificate from the definable power set to the successor stage along the reverse of `step`, since the certificate proves membership in the power set but the tally claims membership in `Lset (# suc n)`. Symmetrically, `onto` takes a membership certificate in the successor stage and transports it forward along `step` before calling the power tally's coverage. In both directions the transport acts on a membership statement and nothing else.
<!--zh-->
`inside` 字段把每份成员证书沿 `step` 的逆向从可定义幂集传输到后继层，因为证书证明的是在幂集中的成员关系，而点名册声称的是在 `Lset (# suc n)` 中的成员关系。对称地，`onto` 取后继层的成员证书，先沿 `step` 向前传输，再调用幂集点名册的覆盖。两个方向的传输都只作用于一句成员陈述，别无其他。
<!--ja-->
`inside` の欄は、各所属の証明書を `step` の逆向きに沿って定義可能冪集合から後者の段階へ輸送する。証明書が証明するのは冪集合への所属であり、数え上げが主張するのは `Lset (# suc n)` への所属だからである。対称的に、`onto` は後者の段階への所属の証明書を受け取り、`step` に沿って前向きに輸送してから冪数え上げの被覆を呼ぶ。どちらの向きでも輸送は一句の所属の述定にだけ働く。
<!--/-->

```agda
    ; item   = Tally.item Power.powerTally
    ; inside = λ i → subst (λ w → ⟨ Tally.item Power.powerTally i ∈ˢ w ⟩) (sym step)
                       (Tally.inside Power.powerTally i)
    ; onto   = λ x x∈ → Tally.onto Power.powerTally x
                          (subst (λ w → ⟨ x ∈ˢ w ⟩) step x∈) }
```

<!--en-->
The auxiliary `members` extracts the inclusion hypothesis that `precedes-tri` asks for. A definable subset of stage `n` has all of its members in stage `n`; this is `𝒟ₒ∋⊆`, read backwards from a membership in the definable power set. The transport along `step` moves the certificate for `x` into the power set first, and what results is a function: for every member `w` of `x`, a certificate that `w` lies in stage `n`.
<!--zh-->
辅助引理 `members` 提取 `precedes-tri` 所要求的包含前提。层 `n` 的可定义子集的成员都在层 `n` 中；这就是 `𝒟ₒ∋⊆`，从可定义幂集中的成员关系反向读出。先沿 `step` 把 `x` 的证书传输进幂集，所得是一个函数：对 `x` 的每个成员 `w`，给出 `w` 落在层 `n` 中的证书。
<!--ja-->
補題 `members` は、`precedes-tri` が要求する包含の前提を取り出す。段階 `n` の定義可能部分集合の要素はすべて段階 `n` にある。それが `𝒟ₒ∋⊆` であり、定義可能冪集合への所属から逆向きに読むものである。まず `step` に沿って `x` の証明書を冪集合へ輸送すれば、得られるものは関数である。`x` の各要素 `w` に対し、`w` が段階 `n` にあることの証明書を与える。
<!--/-->

```agda

  members : (x : S) → ⟨ x ∈ˢ finiteStage (suc n) ⟩
          → (w : S) → ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ finiteStage n ⟩
  members x x∈ = 𝒟ₒ∋⊆ (finiteStage n) x (subst (λ v → ⟨ x ∈ˢ v ⟩) step x∈)

  triSuc : (x y : S) → ⟨ x ∈ˢ finiteStage (suc n) ⟩ → ⟨ y ∈ˢ finiteStage (suc n) ⟩
         → Tri ⟨ before (suc n) x y ⟩ (x ≡ y) ⟨ before (suc n) y x ⟩
```

<!--en-->
Both successor fields are now one-line applications. `triSuc` is `Diff.precedes-tri` with the two inclusion hypotheses supplied by `members`, since `before (suc n)` is by definition `precedes (before n) (finiteStage n)`. `transSuc` is `Diff.precedes-trans` verbatim, its hypotheses already having the right shape. The recursion closes: each stage's order facts are the previous stage's, consumed by the earliest-disagreement theory.
<!--zh-->
两条后继字段现在都是一行的应用。`triSuc` 是 `Diff.precedes-tri`，两条包含前提由 `members` 提供，因为 `before (suc n)` 按定义就是 `precedes (before n) (finiteStage n)`。`transSuc` 逐字就是 `Diff.precedes-trans`，其前提本就具有正确的形状。递归就此闭合：每层的序事实都是上一层的序事实，被最先分歧理论所消费。
<!--ja-->
後者の二つの欄は今や一行の適用である。`before (suc n)` は定義により `precedes (before n) (finiteStage n)` だから、`triSuc` は二つの包含の前提を `members` が供給する `Diff.precedes-tri` である。`transSuc` はそのまま `Diff.precedes-trans` であり、前提ははじめから正しい形をしている。再帰はここで閉じる。各段階の順序の事実は一つ下の段階の事実であり、最初の相違の理論がそれを消費する。
<!--/-->

```agda
  triSuc x y x∈ y∈ = Diff.precedes-tri x y (members x x∈) (members y y∈)

  transSuc : (x y z : S) → ⟨ before (suc n) x y ⟩ → ⟨ before (suc n) y z ⟩
           → ⟨ before (suc n) x z ⟩
  transSuc = Diff.precedes-trans
```

<!--en-->
## The limit stage

Every member of `Lset ω`{.Agda} receives its least finite level; comparing levels
first and the local stage order second gives the limit-stage well-order.

A member of `Lset ω` appears at some numeral-indexed finite stage. Among its stages of appearance, natural-number least-element search gives a smallest one, called its **level**. Natural-number well-foundedness is used again later to organize descent between different levels.
<!--zh-->
## 极限层

`Lset ω`{.Agda} 的每个成员取得其最小有穷层号；先比较层号、再比较局部层序，便得到极限层良序。

`Lset ω` 的成员会出现在某个由数码索引的有穷层。在它出现的诸层中，自然数的最小元搜索给出最小者，称为该元素的**层号**。后文组织不同层号之间的下降时，还会再次使用自然数的良基性。
<!--ja-->
## 極限段階

`Lset ω`{.Agda} の各要素に最小の有限レベルを与え、まずレベルを、次に局所的な段階順序を比較して、極限段階の整列順序を得る。

`Lset ω` の要素は、ある数項で添字づけられた有限段階に現れる。その出現段階の中から自然数の最小要素探索で最小のものを取り、それを要素の**レベル**と呼ぶ。異なるレベル間の降下を組み立てる際にも、自然数の整礎性を再び用いる。
<!--/-->

<!--en-->
The limit's members are packaged as `Limit`, a set together with a membership certificate in `Lset ω`. The lemma `inSome` converts such a certificate into a truncated statement that the set appears at some finite stage. Reading the certificate out of the limit stage produces, merely, some `δ` in `ω` with the set a definable subset of `Lset δ`; the outer elimination is into a truncated type, which is a proposition, so it is legitimate.
<!--zh-->
极限的成员被包装成 `Limit`：一个集合连同它在 `Lset ω` 中的成员证书。引理 `inSome` 把这样的证书转换成一句截断的陈述：该集合出现在某个有穷层。从极限层读出证书，仅仅给出某个属于 `ω` 的 `δ`，使该集合是 `Lset δ` 的可定义子集；外层消去的目标是截断类型，而截断类型是命题，故消去正当。
<!--ja-->
極限の要素は `Limit` として包まれる。すなわち集合に `Lset ω` への所属の証明書を添えたものである。補題 `inSome` はそのような証明書を、その集合がある有限段階に現れるという截断された述定へ変換する。極限段階から証明書を読み出すと、`ω` に属しその集合が `Lset δ` の定義可能部分集合であるようなある `δ` が単に得られるだけである。外側の除去の目標は截断型であり、それは命題なので除去は正当である。
<!--/-->

```agda
Limit : Type (ℓ-suc ℓ)
Limit = Σ[ x ∈ S ] ⟨ x ∈ˢ Lset ω ⟩

inSome : (x : S) → ⟨ x ∈ˢ Lset ω ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩ ∥₁
inSome x h = PT.rec PT.squash₁ atStage (Lset-out ω x h)
  where
```

<!--en-->
It remains to identify the index `δ` below `ω`. Membership `δ ∈ ω` is the truncated assertion that `δ` equals a numeral `# (lower k)` for some lifted natural number `k`. After opening that truncated numeral witness with `PT.map`, the path rewrites the definable-subset certificate for `𝒟ₒ (Lset δ)` to one over `Lset (# lower k)`; `Lset-suc` then places `x` in `finiteStage (suc (lower k))`. This proves appearance at a finite stage without confusing the index `ω` with the stage `Lset ω`.
<!--zh-->
还需识别 `ω` 以下的索引 `δ`。隶属 `δ ∈ ω` 是一条截断陈述：存在提升后的自然数 `k`，使 `δ` 等于数码 `# (lower k)`。用 `PT.map` 在截断内取得该数码见证后，路径把关于 `𝒟ₒ (Lset δ)` 的可定义子集证书改写到 `Lset (# lower k)` 上；再由 `Lset-suc` 把 `x` 放入 `finiteStage (suc (lower k))`。这证明了元素出现在有穷层，同时没有混淆索引 `ω` 与层 `Lset ω`。
<!--ja-->
残るのは `ω` より下の添字 `δ` を同定することである。所属 `δ ∈ ω` は、持ち上げられた自然数 `k` が存在して `δ` が数項 `# (lower k)` に等しいという切断された主張である。`PT.map` により切断の内部でこの数項の証人を用いると、パスが `𝒟ₒ (Lset δ)` に関する定義可能部分集合の証明を `Lset (# lower k)` 上のものへ書き換え、`Lset-suc` が `x` を `finiteStage (suc (lower k))` に置く。これにより、添字 `ω` と段階 `Lset ω` を混同せずに有限段階での出現が示される。
<!--/-->

```agda
  atStage : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
          → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩ ∥₁
  atStage (δ , δ∈ω , x∈) = PT.map named δ∈ω
    where
    named : Σ[ k ∈ Lift ℕ ] (# (lower k) ≡ δ) → Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩
```

<!--en-->
With the numeral named, `named` produces the actual stage of appearance. Since `Lset-suc` identifies `Lset (# (suc k))` with the definable power set of `Lset (# k)`, the certificate that the set is a definable subset of `Lset (# (lower k))` transports, along `sym (Lset-suc ...)`, into a membership in `finiteStage (suc (lower k))`. So the numeral indexing the stage of appearance is one more than the numeral appearing inside `ω`, which is the familiar off-by-one between an index and its successor stage.
<!--zh-->
数码命名之后，`named` 产出实际的出现层。由于 `Lset-suc` 把 `Lset (# (suc k))` 认同为 `Lset (# k)` 的可定义幂集，「该集合是 `Lset (# (lower k))` 的可定义子集」的证书沿 `sym (Lset-suc ...)` 传输为 `finiteStage (suc (lower k))` 中的成员关系。所以索引出现层的数码比出现在 `ω` 内部的数码多一，这正是索引与其后继层之间常见的差一。
<!--ja-->
数項に名が付いたので、`named` が実際の出現段階を作る。`Lset-suc` が `Lset (# (suc k))` を `Lset (# k)` の定義可能冪集合と同一視するので、その集合が `Lset (# (lower k))` の定義可能部分集合であることの証明書は、`sym (Lset-suc ...)` に沿って輸送され、`finiteStage (suc (lower k))` への所属となる。したがって出現段階を添字づける数項は、`ω` の内部に現れる数項より一つ大きい。これは添字とその後者の段階の間の、いつもの一つずれである。
<!--/-->

```agda
    named (k , q) = suc (lower k)
      , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc (# (lower k))))
          (subst (λ w → ⟨ x ∈ˢ 𝒟ₒ (Lset w) ⟩) (sym q) x∈)

levelData : (a : Limit)
          → Σ[ n ∈ ℕ ] IsLeast natOrder (λ m → a .fst ∈ˢ finiteStage m) n
```

<!--en-->
`levelData` is where the truncated existence meets the least-element theorem. It applies `leastOf` for the natural-number order and excluded middle to the predicate `m ↦ a .fst ∈ˢ finiteStage m` and the truncated witness `inSome`, returning an explicit numeral together with `IsLeast` data: the stage at that numeral contains the set, and no smaller numeral has that property. The level is therefore the least stage of appearance, not an arbitrary stage selected from the truncation.
<!--zh-->
`levelData` 正是截断存在与最小元定理相遇之处。它对谓词 `m ↦ a .fst ∈ˢ finiteStage m` 与截断见证 `inSome` 应用自然数序的 `leastOf` 与排中律，返回一个显式数码连同 `IsLeast` 数据：该数码处的层含有该集合，且更小的数码都没有该性质。因此层号是最小的出现层，而非从截断中任意选出的层。
<!--ja-->
`levelData` が、截断された存在と最小要素の定理が出会う箇所である。述語 `m ↦ a .fst ∈ˢ finiteStage m` と截断された証人 `inSome` に対し、自然数順序についての `leastOf` と排中律を適用すると、明示的な数項と `IsLeast` のデータが返る。その数項の段階は集合を含み、より小さい数項ではその性質は成り立たない。したがってレベルは最小の出現段階であり、截断から任意に選ばれた段階ではない。
<!--/-->

```agda
levelData a =
  leastOf natOrder lem (λ m → a .fst ∈ˢ finiteStage m) (inSome (a .fst) (a .snd))

level : Limit → ℕ
level a = levelData a .fst

level-in : (a : Limit) → ⟨ a .fst ∈ˢ finiteStage (level a) ⟩
```

<!--en-->
The two projections have convenient names: `level a` is the least numeral at which the underlying set appears, and `level-in a` is the membership certificate at that stage. Everything the limit order needs about a member's floor is now available as data, and the next section builds the order out of exactly these two ingredients.
<!--zh-->
两个投影有方便的名字：`level a` 是底层集合出现的最小数码，`level-in a` 是该层处的成员证书。极限序所需的关于成员「楼层」的一切现在都已是数据，下一节将恰好用这两个材料构造那个序。
<!--ja-->
二つの射影には扱いやすい名が付いている。`level a` は根底の集合が現れる最小の数項であり、`level-in a` はその段階での所属の証明書である。要素の「階」について整列順序が必要とするものはすべてデータとして手に入り、次の節はまさにこの二つの材料から順序を組み立てる。
<!--/-->

```agda
level-in a = levelData a .snd .fst
```

<!--en-->
The order on the limit takes the level as the primary key: a member of a lower level comes first, and two members of the same level are compared by that level's own order. The equation between levels is carried in the second alternative, and carried in the direction that lets the second member be read at the first's level, which is what keeps the definition free of any transport.

Irreflexivity and transitivity are case analyses on that alternative, with the level equations moving the stage-order facts to the level where they are needed. Trichotomy compares levels first and defers to the stage only when they agree.
<!--zh-->
极限上的序先按层号比较：层号较低的成员在前，同层的两个成员则按该层自己的序比较。第二支处理层号相等的情形，其方向使得第二个成员可以在第一个成员的层上读出；正因如此，定义中不出现任何跨层的转换。

非自反与传递是对那一支的分情形，层号等式的情形直接使用相应层上的层序事实。三歧先比较层号，仅当层号相同时才由层序判定。
<!--ja-->
極限上の順序はレベルを第一の鍵として比較する：レベルの低い要素が先に来て、同じレベルの二つの要素はそのレベル自身の順序で比較される。第二の選択肢はレベルの等しさを保持するが、その向きのおかげで第二の要素を第一の要素のレベルで読み取ることができ、定義に余計な輸送が現れない。

非反射性と推移性はこの選択肢についての場合分けであり、レベルの等式を使って段階順序の事実を必要なレベルへ移す。三分法はまずレベルを比較し、一致する場合にのみ段階の順序に委ねる。
<!--/-->

<!--en-->
The relation `a ≺ b` is a disjoint sum of two ways to come first. The left alternative says `a`'s level is strictly smaller; the right alternative says the levels coincide and, inside stage `level a`, the underlying sets stand in that stage's own `before` order. The `Lift` on the left raises the natural-number comparison from `Type ℓ-zero` to `Type (ℓ-suc ℓ)`, the universe where the right alternative already lives, so both branches share one type. Reading the relation is lexicographic: level decides unless it ties, and only a tie consults the stage.
<!--zh-->
关系 `a ≺ b` 是「占先」的两种方式的不相交和。左支说 `a` 的层号严格更小；右支说两层号相等，并且在层 `level a` 内，两个底层集合处于该层自己的 `before` 序中。左支的 `Lift` 把自然数上的比较从 `Type ℓ-zero` 抬升到 `Type (ℓ-suc ℓ)`，即右支本已所在的宇宙，于是两支共用一个类型。这个关系按字典序读：层号分出高下，唯有打平时才去问层。
<!--ja-->
関係 `a ≺ b` は、先に来る二つの仕方の非交和です。左の選択肢は `a` のレベルが厳密に小さいと言い、右の選択肢はレベルが一致し、段階 `level a` の中で基底の集合がその段階自身の `before` 順序に入ると言います。左辺の `Lift` は自然数上の比較を `Type ℓ-zero` から、右の選択肢が既に住む宇宙 `Type (ℓ-suc ℓ)` へ引き上げ、両者の枝が一つの型を共有するようにします。この関係は辞書式に読みます：レベルが決め手となり、同点のときにだけ段階に問い合わせます。
<!--/-->

```agda
_≺_ : Limit → Limit → Type (ℓ-suc ℓ)
a ≺ b = Lift {ℓ-zero} {ℓ-suc ℓ} (level a < level b)
      ⊎ ((level b ≡ level a) × ⟨ before (level a) (a .fst) (b .fst) ⟩)

limit-irrefl : (a : Limit) → a ≺ a → Empty.⊥
limit-irrefl a (inl h)       = ¬m<m (lower h)
```

<!--en-->
Irreflexivity disposes of each branch with the corresponding fact about the ingredients: a strict inequality `level a < level a` is refused by `¬m<m`, and a witness of `before (level a)` against `a` itself is refused by `before-irrefl`, which held at every stage without induction. Transitivity then splits by which branch each hypothesis uses. When both steps descend in level, `<-trans` composes the two inequalities; when only one step does, the equality of levels in the other hypothesis is used with `subst` to move the one strict inequality to the right endpoint, still yielding the left branch.
<!--zh-->
非自反性对每一支分别用相应成分的事实处理：严格不等式 `level a < level a` 被 `¬m<m` 拒绝；对 `a` 自身的 `before (level a)` 见证被 `before-irrefl` 拒绝，而后者在每层都成立且无需归纳。传递性则按两个前提各取哪一支来分情形。若两步都在层号上下降，`<-trans` 复合两个不等式；若只有一步在层号上下降，就用另一前提中的层号等式配合 `subst`，把那条严格不等式搬到正确的端点，结果仍在左支。
<!--ja-->
非反射性は、各枝について対応する成分の事実で処理されます：厳密な不等式 `level a < level a` は `¬m<m` が拒み、`a` 自身に対する `before (level a)` の証人は `before-irrefl` が拒みます。後者は全段階で帰納なしに成り立っていました。推移性は、二つの前提がそれぞれどちらの枝を使うかで場合分けします。両段階ともレベルで下降するなら `<-trans` が二つの不等式を合成し、片方だけが下降するなら、もう一方の前提にあるレベルの等式を `subst` とともに用いて厳密な不等式を正しい端点へ移し、やはり左の枝を得ます。
<!--/-->

```agda
limit-irrefl a (inr (_ , h)) = before-irrefl (level a) (a .fst) h

limit-trans : (a b c : Limit) → a ≺ b → b ≺ c → a ≺ c
limit-trans a b c (inl h)       (inl k)       = inl (lift (<-trans (lower h) (lower k)))
limit-trans a b c (inl h)       (inr (q , _)) =
  inl (lift (subst (λ j → level a < j) (sym q) (lower h)))
```

<!--en-->
When both hypotheses use their equal-level branches, `q : level b ≡ level a` comes from `a ≺ b` and `p : level c ≡ level b` comes from `b ≺ c`. Their composite `p ∙ q : level c ≡ level a` is the equation required for `a ≺ c`. The stage-order fact `hbc` is stated at `level b`; transport along `q` moves it to `level a`, where it composes with `hab` by StageOrder.trans.
<!--zh-->
当两个前提都取同层支时，`a ≺ b` 给出 `q : level b ≡ level a`，`b ≺ c` 给出 `p : level c ≡ level b`。复合 `p ∙ q : level c ≡ level a` 正是 `a ≺ c` 所需的等式。层序事实 `hbc` 陈述在 `level b`；沿 `q` 传输后落到 `level a`，便可由 `StageOrder.trans` 与 `hab` 复合。
<!--ja-->
二つの仮定がともに同レベルの分岐にあるとき、`a ≺ b` から `q : level b ≡ level a`、`b ≺ c` から `p : level c ≡ level b` を得る。合成 `p ∙ q : level c ≡ level a` が `a ≺ c` に必要な等式である。段階順序の事実 `hbc` は `level b` で述べられているので、`q` に沿って `level a` へ輸送し、そこで `StageOrder.trans` により `hab` と合成する。
<!--/-->

```agda
limit-trans a b c (inr (q , _)) (inl k)       =
  inl (lift (subst (λ j → j < level c) q (lower k)))
limit-trans a b c (inr (q , hab)) (inr (p , hbc)) = inr (p ∙ q , joined)
  where
  moved : ⟨ before (level a) (b .fst) (c .fst) ⟩
```

<!--en-->
The transport in `moved` moves `hbc` along the equation `q`, changing only the stage at which the `before` statement is made, from `level b` to `level a`. At that point both witnesses live in one stage: `hab` says `a`'s set precedes `b`'s there, and `moved` says `b`'s precedes `c`'s, so `StageOrder.trans` at stage `level a` joins them into `joined`, the witness that `a` precedes `c` inside its own level. This finishes transitivity; trichotomy is stated next and is decided by comparing the two levels outright.
<!--zh-->
`moved` 中的传输沿等式 `q` 移动 `hbc`，只改变 `before` 陈述所处的层，从 `level b` 换到 `level a`。此后两个见证便同处一层：`hab` 说在该层中 `a` 的集合先于 `b` 的，`moved` 说 `b` 的先于 `c` 的，于是在层 `level a` 处用 `StageOrder.trans` 把二者接成 `joined`，即 `a` 在自己层内先于 `c` 的见证。传递性至此完成；接着陈述三歧性，其判定方式是直接比较两层号。
<!--ja-->
`moved` の輸送は等式 `q` に沿って `hbc` を移し、`before` の主張がなされる段階を `level b` から `level a` へ変えるだけです。こうして二つの証人は同じ段階に住みます。`hab` はそこで `a` の集合が `b` の集合に先行し、`moved` は `b` の集合が `c` の集合に先行すると言うので、段階 `level a` での `StageOrder.trans` が両者を `joined` へとつなぎ、`a` が自レベル内で `c` に先行する証人となります。これで推移性は完成です。続く三分法は、二つのレベルを直接比較して判定します。
<!--/-->

```agda
  moved = subst (λ j → ⟨ before j (b .fst) (c .fst) ⟩) q hbc
  joined : ⟨ before (level a) (a .fst) (c .fst) ⟩
  joined = StageOrder.trans (stageOrder (level a)) (a .fst) (b .fst) (c .fst) hab moved

limit-tri : (a b : Limit) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
limit-tri a b = byLevel (level a ≟ level b)
```

<!--en-->
Trichotomy first decides `level a ≟ level b`. Unequal levels immediately give the corresponding strict branch. In the equality case the decision supplies `p : level a ≡ level b`; transporting `level-in b` along `sym p` places `b` in `finiteStage (level a)`, so StageOrder.tri can compare both underlying sets in that one stage.
<!--zh-->
三歧性先判定 `level a ≟ level b`。层号不等时立即得到相应的严格比较支。相等支给出 `p : level a ≡ level b`；沿 `sym p` 传输 `level-in b`，便把 `b` 放入 `finiteStage (level a)`，于是 `StageOrder.tri` 能在同一层比较两个底层集合。
<!--ja-->
三岐性ではまず `level a ≟ level b` を判定する。レベルが異なれば、対応する狭義比較の分岐が直ちに得られる。等しい場合には `p : level a ≡ level b` が得られ、`level-in b` を `sym p` に沿って輸送すると `b` が `finiteStage (level a)` に入る。そこで `StageOrder.tri` が一つの段階内で二つの基底集合を比較できる。
<!--/-->

```agda
  where
  byLevel : NatOrder.Trichotomy (level a) (level b) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
  byLevel (NatOrder.lt h) = lt (inl (lift h))
  byLevel (NatOrder.gt h) = gt (inl (lift h))
  byLevel (NatOrder.eq p) = same
```

<!--en-->
The local trichotomy is repackaged into the limit relation with the equality in the required direction. A local result `a before b` returns the right branch of `a ≺ b` with `sym p : level b ≡ level a`; a local result `b before a` returns the right branch of `b ≺ a` with `p`, transporting the before-proof to stage `level b`. Equality of underlying sets lifts to equality in `Limit` because its membership component is propositional.
<!--zh-->
局部三歧按极限关系所需的方向重新打包。若局部结果是 `a before b`，就在 `a ≺ b` 的同层支中返回 `sym p : level b ≡ level a`；若结果是 `b before a`，就在 `b ≺ a` 的同层支中返回 `p`，并把 before 证明传输到层 `level b`。底层集合相等可提升为 `Limit` 中的相等，因为成员证明分量是命题。
<!--ja-->
局所的な三岐性を、極限関係が要求する等式の向きで包み直す。局所結果が `a before b` なら、`a ≺ b` の同レベル分岐に `sym p : level b ≡ level a` を返す。`b before a` なら、`b ≺ a` の同レベル分岐に `p` を返し、before の証明を段階 `level b` へ輸送する。基底集合の等式は、所属証明の成分が命題なので `Limit` の等式へ持ち上がる。
<!--/-->

```agda
    (StageOrder.tri (stageOrder (level a)) (a .fst) (b .fst) (level-in a) b∈)
    where
    b∈ : ⟨ b .fst ∈ˢ finiteStage (level a) ⟩
    b∈ = subst (λ j → ⟨ b .fst ∈ˢ finiteStage j ⟩) (sym p) (level-in b)
    same : Tri ⟨ before (level a) (a .fst) (b .fst) ⟩ (a .fst ≡ b .fst)
```

<!--en-->
Repackaging splits by the stage's verdict. If `a`'s set precedes `b`'s, the result is the right branch of `≺`, fed with the equation `sym p` in exactly the direction the definition asks for. If the sets are equal, `Σ≡Prop` promotes that to a path between the pairs `a` and `b`, legitimate because the second component of `Limit` is a proposition; this is the `eq` case. If `b`'s set precedes `a`'s, the `before` fact is transported along `p` to the level where it is stated, and the result is the right branch with the arguments reversed. No case here needed anything beyond the ingredients already built.
<!--zh-->
重新包装按该层的判定分三种。若 `a` 的集合先于 `b` 的，结果是 `≺` 的右支，并以 `sym p` 供给等式，方向恰是定义所要求的。若两集合相等，`Σ≡Prop` 把它提升为配对 `a` 与 `b` 之间的路径；这是合法的，因为 `Limit` 的第二个分量是命题，这就是 `eq` 情形。若 `b` 的集合先于 `a` 的，则沿 `p` 把该 `before` 事实传输到它应被陈述的层号处，结果是以相反实参给出的右支。这里的每种情形都没有用到已造好的成分之外的任何东西。
<!--ja-->
組み替えは段階の判定によって三通りに分かれます。`a` の集合が `b` の集合に先行するなら、結果は `≺` の右の枝で、等式は定義が要求する向きどおりに `sym p` で供給されます。二つの集合が等しいなら、`Σ≡Prop` がそれを対 `a` と `b` の間の経路に引き上げます。`Limit` の第二成分が命題であるためこれが正当化され、これが `eq` の場合です。`b` の集合が `a` の集合に先行するなら、その `before` の事実を `p` に沿って述べられるべきレベルへ輸送し、結果は引数を入れ替えた右の枝となります。どの場合も、すでに組み上げた材料以外のものは何も要りませんでした。
<!--/-->

```agda
               ⟨ before (level a) (b .fst) (a .fst) ⟩
         → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    same (lt h) = lt (inr (sym p , h))
    same (eq q) = eq (Σ≡Prop (λ z → snd (z ∈ˢ Lset ω)) q)
    same (gt h) = gt (inr (p , subst (λ j → ⟨ before j (b .fst) (a .fst) ⟩) p h))
```

<!--en-->
Well-foundedness is two nested inductions, and they are kept apart on purpose. The outer one is induction on the level, in the library's packaged form, and it hands down a hypothesis covering every lower level. The inner one is an ordinary descent along the accessibility that the finite stage already has, which is legitimate precisely because that stage is finite. A step down in level appeals to the outer hypothesis; a step within a level appeals to the inner one; and since the inner function recurses on nothing but its own accessibility argument, the two never have to be compared.
<!--zh-->
良基性的证明是两层嵌套的归纳，而把它们分开是有意的。外层是对层号的归纳，采用库中现成的封装，它提供一条覆盖所有更低层的归纳假设。内层沿有穷层已有的可及性作普通的下降，其合法性正来自该层的有穷性。跨层下降的一步使用外层假设，层内的一步使用内层假设；内层函数除自己的可及性实参外不沿任何东西递归，因此二者从不需要同时比较。
<!--ja-->
整礎性の証明は二重の入れ子になった帰納であり、意図的に二つを分けています。外側はレベルについての帰納で、ライブラリの既成の形を用い、より低いすべてのレベルを網羅する帰納仮定を手渡します。内側は、有限段階がすでに持つ accessibility に沿う通常の下降であり、その正当性はまさにその段階の有限性に由来します。レベルをまたぐ下降の一歩は外側の仮定に訴え、レベル内の一歩は内側に訴えます。内側の関数は自分自身の accessibility の実引数以外には再帰しないため、二つを比べる必要は一度も生じません。
<!--/-->

<!--en-->
Fix a target `b` at level `k` and a point `u` of stage `k` with the same underlying set. The inner argument turns accessibility of `u` for the local relation `Below k` into accessibility of `b` for the limit relation. After unfolding `Acc`, an arbitrary predecessor is named `c`. If `c` has lower level, the outer induction hypothesis applies; if it has the same level, it becomes a local predecessor of `u` and the inner accessibility proof applies.
<!--zh-->
固定层号为 `k` 的目标 `b`，以及层 `k` 中与它底层集合相同的点 `u`。内层论证把 `u` 关于局部关系 `Below k` 的可及性转成 `b` 关于极限关系的可及性。展开 `Acc` 后，任意前驱记为 `c`。若 `c` 的层号更低，就使用外层归纳假设；若层号相同，就把它变成 `u` 的局部前驱并使用内层可及性。
<!--ja-->
レベル `k` の目標 `b` と、同じ基底集合をもつ段階 `k` の点 `u` を固定する。内側の議論は、局所関係 `Below k` に関する `u` の到達可能性を、極限関係に関する `b` の到達可能性へ移す。`Acc` を一段展開すると、任意の前駆を `c` とする。`c` のレベルが低ければ外側の帰納仮定を使い、同じレベルなら `u` の局所前駆にして内側の到達可能性を使う。
<!--/-->

```agda
accInside : (k : ℕ)
          → ((m : ℕ) → m < k → (b : Limit) → level b ≡ m → Acc _≺_ b)
          → (u : Point k) → Acc (Below k) u
          → (b : Limit) → level b ≡ k → b .fst ≡ u .fst → Acc _≺_ b
accInside k ih u (acc ru) b q e = acc step
```

<!--en-->
Discharging `step` splits by the branch of the hypothesis `c ≺ b`. In the left branch, `c` has strictly smaller level than `b`, hence than `k`; the inequality is moved under the equation `q` with `subst`, and then `ih` applies at level `level c`, exactly the cross-level case. In the right branch, `c` shares `b`'s level, so both live inside stage `k`, and the descent is handed to the inner accessibility: `ru` is the function that the `acc` constructor of `u`'s accessibility provides, and it is applied to the point `pc` corresponding to `c` and to the proof that `pc` is below `u`.
<!--zh-->
完成 `step` 按前提 `c ≺ b` 所取的支分情形。左支中，`c` 的层号严格小于 `b`，因而小于 `k`；该不等式用 `subst` 在等式 `q` 之下搬动，然后在层号 `level c` 处使用 `ih`，这正是跨层的情形。右支中，`c` 与 `b` 同层号，故二者都在层 `k` 之内，下降便交给内层可及性：`ru` 是 `u` 的可及性的 `acc` 构造子所提供的函数，把它作用于与 `c` 对应的点 `pc` 以及 `pc` 位于 `u` 之下的证明。
<!--ja-->
`step` の遂行は、前提 `c ≺ b` が取る枝で場合分けします。左の枝では `c` のレベルは `b` より厳密に小さく、したがって `k` よりも小さい。この不等式を `subst` で等式 `q` の下に動かし、レベル `level c` で `ih` を適用します。これがレベルをまたぐ場合です。右の枝では `c` は `b` とレベルを共有するので、両者は段階 `k` の内側に住み、下降は内側の accessibility に引き渡されます。`ru` は `u` の accessibility の `acc` 構成子が供給する関数で、`c` に対応する点 `pc` と、`pc` が `u` より下であることの証明に適用されます。
<!--/-->

```agda
  where
  step : (c : Limit) → c ≺ b → Acc _≺_ c
  step c (inl h) = ih (level c) (subst (λ j → level c < j) q (lower h)) c refl
  step c (inr (qb , hc)) = accInside k ih pc (ru pc below) c qc refl
    where
```

<!--en-->
The right branch needs its bookkeeping made explicit. First `qc` composes the two level equations, `sym qb` with `q`, to certify that `level c ≡ k`; this is what lets `c` be seen at stage `k` at all. Then `pc` packages `c`'s underlying set with its membership in stage `k`, the membership being obtained by transporting `level-in c` along `qc`. A `Point k` is a set together with such a certificate, so this one construction moves the argument from the limit back into the finite stage where the inner order lives.
<!--zh-->
右支的簿记需要显式写出。首先 `qc` 复合两条层号等式，即 `sym qb` 与 `q`，证明 `level c ≡ k`；正是这一点使 `c` 能被放到层 `k` 中看。然后 `pc` 把 `c` 的底层集合与它在层 `k` 中的隶属打包在一起，该隶属由 `level-in c` 沿 `qc` 传输得到。`Point k` 就是一个集合连同这样的证书，所以这一个构造把论证从极限带回内层序所在的有穷层。
<!--ja-->
右の枝の簿記は明示的に書き出す必要があります。まず `qc` は二つのレベルの等式 `sym qb` と `q` を合成し、`level c ≡ k` を証明します。`c` を段階 `k` で見られるようにするのはまさにこの等式です。次に `pc` は `c` の基底集合と、段階 `k` での所属を一つにまとめます。所属は `level-in c` を `qc` に沿って輸送して得ます。`Point k` とは集合にこうした証書を添えたものなので、この一つの構成が議論を極限から、内側の順序の住む有限段階へと引き戻します。
<!--/-->

```agda
    qc : level c ≡ k
    qc = sym qb ∙ q
    pc : Point k
    pc = c .fst , subst (λ j → ⟨ c .fst ∈ˢ finiteStage j ⟩) qc (level-in c)
    below : Below k pc u
```

<!--en-->
In the equal-level case, every predecessor `b` of `u` lies in the same finite stage `k` and is below `u` in that stage order. The equalities carried by the case merely align both endpoints with this fixed `k`; the accessibility of `u` for `Below k` then supplies accessibility of `b`. Thus the inner recursion descends only inside one finite-stage order.
<!--zh-->
在层号相同的情形，每个极限前驱 `b` 都与 `u` 位于同一有穷层 `k`，并在该层序中低于 `u`。该分支携带的等式只把两个端点对齐到固定的 `k`；随后 `u` 关于 `Below k` 的可及性给出 `b` 的可及性。因此，内层递归只沿一个有穷层的序下降。
<!--ja-->
レベルが等しい場合、`u` の各極限前駆 `b` は同じ有限段階 `k` に属し、その段階の順序で `u` より小さい。この場合に伴う等式は両端点を固定した `k` にそろえるだけであり、`Below k` に関する `u` の到達可能性が `b` の到達可能性を与える。したがって内側の再帰は一つの有限段階の順序の中だけを下降する。
<!--/-->

```agda
    below = subst (λ v → ⟨ before k (c .fst) v ⟩) e
              (subst (λ j → ⟨ before j (c .fst) (b .fst) ⟩) qc hc)

accByLevel : (k : ℕ) → (b : Limit) → level b ≡ k → Acc _≺_ b
accByLevel = WFI.induction <-wellfounded outer
  where
```

<!--en-->
The outer induction is well-founded induction on the natural-number level. Its hypothesis handles every predecessor whose level is strictly smaller than `k`; the inner accessibility argument handles predecessors that remain at level `k`. These two cases form the lexicographic proof and require no compatibility assumption between the orders on different finite stages.
<!--zh-->
外层是对自然数层号的良基归纳，其归纳假设处理层号严格小于 `k` 的前驱；内层可及性处理仍处于层号 `k` 的前驱。两种情形合成字典序式的证明，无须假设不同有穷层上的序彼此相容。
<!--ja-->
外側は自然数のレベルに関する整礎帰納であり、その帰納仮定はレベルが `k` より真に小さい前駆を扱う。内側の到達可能性はレベル `k` にとどまる前駆を扱う。この二場合が辞書式の証明をなし、異なる有限段階の順序どうしの整合性を仮定する必要はない。
<!--/-->

```agda
  outer : (k : ℕ) → ((m : ℕ) → m < k → (b : Limit) → level b ≡ m → Acc _≺_ b)
        → (b : Limit) → level b ≡ k → Acc _≺_ b
  outer k ih b q = accInside k ih here
    (Ordered.wellFounded k (stageOrder k) here) b q refl
    where
```

<!--en-->
The body of `outer` reduces its goal to the inner lemma. It first forms `here`, the point of stage `k` corresponding to `b`, built exactly like `pc` above; then `Ordered.wellFounded k (stageOrder k) here` supplies the accessibility of that point inside stage `k`'s order, and `accInside` takes it from there, with the remaining two arguments being the level equation `q` and the reflexive identification of `b`'s set with `here`'s. The final statement `limit-wf` says every member of the limit is accessible, obtained by instantiating the level induction at `level a` with the trivial equation `refl`.
<!--zh-->
`outer` 的主体把目标化归到内层引理。它先造出 `here`，即与 `b` 对应的层 `k` 的点，其造法与上面的 `pc` 完全相同；然后 `Ordered.wellFounded k (stageOrder k) here` 提供该点在层 `k` 序中的可及性，`accInside` 便由此接手，其余两个实参是层号等式 `q` 以及把 `b` 的底层集合与 `here` 的认同起来的自反等式。最后的陈述 `limit-wf` 说极限的每个成员都可及，做法是在层号 `level a` 处以平凡等式 `refl` 实例化层号归纳。
<!--ja-->
`outer` の本体は目標を内側の補題へ帰着させます。まず `b` に対応する段階 `k` の点 `here` を作ります。その作り方は上の `pc` とまったく同じです。次に `Ordered.wellFounded k (stageOrder k) here` がその点の段階 `k` の順序における accessibility を供給し、`accInside` がそこから引き受けます。残る二つの実引数はレベルの等式 `q` と、`b` の基底集合を `here` のそれと同一視する自反射的な等式です。最後の主張 `limit-wf` は極限のすべての要素が accessible であることを言い、レベルの帰納を `level a` で自明な等式 `refl` とともに具体化して得られます。
<!--/-->

```agda
    here : Point k
    here = b .fst , subst (λ j → ⟨ b .fst ∈ˢ finiteStage j ⟩) q (level-in b)

limit-wf : WellFounded _≺_
limit-wf a = accByLevel (level a) a refl

limitOrder : SWO Limit
```

<!--en-->
Consequently `≺` is a strict well-order on `Limit`: it is trichotomous, irreflexive and transitive, and the two-level induction proves it well-founded. Elements from different first-appearance levels are ordered by level; only equal-level elements are compared by a single finite-stage order.
<!--zh-->
因此，`≺` 是 `Limit` 上的严格良序：它满足三歧、非自反与传递，而两层归纳证明其良基性。首次出现层号不同的元素按层号排序；只有层号相同的元素才由一个有穷层序比较。
<!--ja-->
したがって `≺` は `Limit` 上の狭義整列順序である。三岐性・非反射性・推移性を満たし、二段階の帰納が整礎性を証明する。初出レベルが異なる要素はレベルで順序づけ、レベルが等しい要素だけを一つの有限段階の順序で比較する。
<!--/-->

```agda
limitOrder = record
  { _<∙_   = _≺_
  ; tri∙   = limit-tri
  ; irr∙   = limit-irrefl
  ; trans∙ = limit-trans
```

<!--en-->
Thus `limitOrder` is a strict well-order on the members of `Lset ω`: levels are the primary key, and elements with the same least level are compared by that finite stage’s order. Its least-element operation can therefore select from any merely inhabited proposition-valued family on the limit stage.
<!--zh-->
因此，`limitOrder` 是 `Lset ω` 诸成员上的严格良序：层号是主键，最小层号相同的元素由该有穷层的序比较。于是，它的最小元运算可从极限层上任意仅仅非空的命题值族中作出选取。
<!--ja-->
したがって `limitOrder` は `Lset ω` の要素上の狭義整列順序である。レベルを第一のキーとし、最小レベルが等しい要素はその有限段階の順序で比較する。その最小要素演算により、極限段階上の単に非空な命題値族から選択できる。
<!--/-->

```agda
  ; wf∙    = limit-wf }
```

<!--en-->
## Recap

Finite tallies climb through definable powersets, support the well-founded earliest-disagreement order at every numeral stage, and culminate in `limitOrder`{.Agda} on `Lset ω`{.Agda}.

`Tally`{.Agda} is all the finiteness this chapter owns: a finite family that hits every member, with no injectivity and no decidable equality asked for. `PowerStep.powerTally`{.Agda} carries one up to the definable power set, by enumerating the bit vectors over the tally and observing that every subset of a tallied stage is definable; `stageOrder`{.Agda} then runs that step along the numerals, so every finite stage has a tally.

`precedes`{.Agda} compares two subsets at the earliest point where they disagree. It is irreflexive for free, transitive by comparing two witnesses, and trichotomous by the excluded middle together with the base's smallest elements. Well-foundedness does not follow from the definition of the comparison alone. Here it comes from the tally through `Search`{.Agda}; the descending-chain example on subsets of the natural numbers shows why the finite-stage hypothesis matters.

`limitOrder`{.Agda} is a strict well-order on the members of `Lset ω`{.Agda}, with the level as the primary key and each finite stage's own order inside a level. It is the interface the axiom of choice will take: with it, `leastOf`{.Agda} picks a member out of any inhabited property of members of the limit stage, and picks the same one every time.
<!--zh-->
## 小结

有穷点名册沿可定义幂集上升，支撑每个数码层处良基的最先分歧序，并最终给出 `Lset ω`{.Agda} 上的 `limitOrder`{.Agda}。

`Tally`{.Agda} 就是本章拥有的全部有穷性：一个命中每个成员的有穷族，既不要求单射，也不要求可判定的相等。`PowerStep.powerTally`{.Agda} 把它抬到可定义幂集上，办法是枚举点名册上的位向量，并指出已清点层的每个子集都可定义；`stageOrder`{.Agda} 随后沿诸数码跑完这一步，于是每个有穷层都有一份点名册。

`precedes`{.Agda} 在两个子集最先分歧之处比较它们。它的非自反性直接由定义推出，传递性由比较两个见证得到，三歧则由排中律连同基底的最小元得到。良基性并不单由这条比较的定义推出；在这里，它经由 `Search`{.Agda} 从点名册得到。自然数子集上的下降链例子说明了为何有穷层这一假设不可省略。

`limitOrder`{.Agda} 是 `Lset ω`{.Agda} 诸成员上的一个严格良序，以层号为主键，层内则用各有穷层自己的序。它就是选择公理将要取用的接口：有了它，`leastOf`{.Agda} 能从极限层诸成员的任一非空性质中挑出一个成员，且每次挑出同一个。
<!--ja-->
## まとめ

有限な数え上げは定義可能冪集合を通じて上昇し、各数項段階で整礎な最初の相違の順序を支え、最後に `Lset ω`{.Agda} 上の `limitOrder`{.Agda} を与えます。

`Tally`{.Agda} がこの章の持つ有限性のすべてです：すべての要素を命中させる有限族であり、単射性も決定可能な等しさも要求しません。`PowerStep.powerTally`{.Agda} は、数え上げの上のビットベクトルを列挙し、数え上げられた段階のすべての部分集合が定義可能であることを指摘することで、それを定義可能冪集合へ運びます。`stageOrder`{.Agda} はその一歩を数項に沿って進めるので、すべての有限段階が数え上げを持ちます。

`precedes`{.Agda} は二つの部分集合を最初に相違する点で比較します。非反射性は定義から直接従い、推移性は二つの証人の比較から、三分法は排中律と基底の最小要素とから得られます。整礎性はそもそもこの比較の性質ではありません：それは数え上げから `Search`{.Agda} を通じて来るものであり、無限の基底の上では成立しなくなるでしょう。だからこそ有限性を先に確立しておく必要があったのです。

`limitOrder`{.Agda} は `Lset ω`{.Agda} の要素上の狭義の整列順序であり、レベルを第一の鍵とし、レベルの内側では各有限段階自身の順序を用います。これが選択公理が取る interface です：これがあれば、`leastOf`{.Agda} は極限段階の要素上の任意の inhabited な性質から一つの要素を取り出し、毎回同じものを取り出します。
<!--/-->
