<!--en-->
# Canonical names for successor-stage members

A member of a successor stage is determined by a formula and finitely many parameters from the preceding stage. This chapter packages that data as a name, proves that every member has one, and orders all names so that a least representative can be chosen.

A member of a successor stage is a definable subset of the stage below, and the earlier chapters said what that means twice over: once in `L.Definability`, as a formula with parameters drawn from that stage, and once in `FOL.Manipulation.ParameterAbstraction`, after the parameters leave the syntax, as a **parameter-free formula together with a vector of parameters**. The second form is the one that can be compared. Its formula is a finite piece of syntax, so its code is a hereditarily finite set and has already appeared at the limit stage `Lset ω`, which `L.Choice.FiniteStageOrders` well-orders; its parameters are members of the stage below, which the surrounding construction has well-ordered by the time it calls this one. A **name** is that pair, with the arity between them, and this chapter builds it, shows every member of the successor stage has one, and well-orders the names.

The order is a three-key lexicographic comparison, written out. Nothing here is an instance of a general order on dependent sums, and that is deliberate: such a thing would have to carry a family of orders indexed by the first key and prove its four laws in that generality, which is a larger theorem than the one wanted, for a single use. The three keys are named, and each is compared by an order that already exists.
<!--zh-->
# 后继层成员的典范名字

后继层的成员由一条公式及前一层中的有限多个参数确定。本章把这些数据封装成名字，证明每个成员都有名字，再良序化所有名字，以便选出最小代表。

后继层的成员就是下面那一层的可定义子集，而前面的章节已经把这句话说了两遍：一遍在 `L.Definability` 中，说成带参数的公式，参数取自那一层；另一遍在 `FOL.Manipulation.ParameterAbstraction` 中，在参数离开语法之后，说成**一条无参公式配上一个参数向量**。可比较的是后一种形式。它的公式是一段有穷的语法，故它的码是遗传有穷集，早已现身于极限层 `Lset ω`，而 `L.Choice.FiniteStageOrders` 恰把那里良序化；它的参数是下面那一层的成员，而在外围构造调用本章时，那一层已被良序化。**名字**就是这样一对，中间夹着元数；本章造出它，证明后继层的每个成员都有一个，并把诸名字良序化。

那个序是一次写开了的三键字典序比较。此处没有任何东西是「依值和上的一般序」的实例，而这是有意为之：那样一件东西得携带一族以第一个键为索引的序，并在那种一般性下证出它的四条定律，而这比所要的定理更大，却只用一次。三个键各有其名，而每个键都由一个已然存在的序来比较。
<!--ja-->
# 後者段階の要素の正準な名前

後続段階の要素は、一つの論理式と直前の段階から取った有限個のパラメータによって定まる。本章ではそのデータを名前としてまとめ、すべての要素が名前をもつことを示し、最小の代表を選べるよう名前全体を整列する。

後続段階の要素とは、その下の段階の定義可能部分集合のことであり、前の章たちはこのことを二通りに述べてきた。一つは `L.Definability` で、その段階から取ったパラメータ付きの論理式としてであり、もう一つは `FOL.Manipulation.ParameterAbstraction` で、パラメータを構文から取り除いた後の「パラメータなし論理式とパラメータ列の組」としてである。比較できるのは後者の形である。その論理式は有限な構文片なので、そのコードは遺伝的有限集合であり、極限段階 `Lset ω` に既に現れている。`L.Choice.FiniteStageOrders` はまさにそこを整列する。パラメータは下の段階の要素であり、この章が呼ばれる時点で、外側の構成によって既に整列されている。**名前**とは、その間にアリティを挟んだこの組であり、本章はそれを構成し、後続段階の各要素が名前をもつことを示し、名前全体を整列する。

この順序は、三つの鍵による辞書式比較をそのまま書き下したものである。ここに「依存和上の一般的な順序」のインスタンスは何もなく、それは意図的なことである。そのような一般論は、第一の鍵で索引された順序の族を運び、四つの法則をその一般性のもとで証明せねばならず、一度しか使わない用途には大きすぎる定理になる。三つの鍵にはそれぞれ名前がついており、各鍵は既に存在する順序によって比較される。
<!--/-->

<!--en-->
The explicit classical input is `lem : LEM (ℓ-suc ℓ)`. It supplies the finite-stage limit order used for formula codes and the least-element search used at the end. Keeping it as a module parameter records the common strength required by both constructions; the intervening coding, abstraction, lexicographic laws, and accessibility arguments add no further axiom.
<!--zh-->
显式的经典输入是 `lem : LEM (ℓ-suc ℓ)`。它既供给公式码所用的有限层极限序，也供给结尾的极小元搜索。把它保留为模块参数，便准确记录两项构造共同需要的强度；中间的编码、抽象、字典序定律与可及性论证不再加入其他公理。
<!--ja-->
明示的な古典的入力は `lem : LEM (ℓ-suc ℓ)` です。これは論理式コードに用いる有限段階の極限順序と、最後の最小要素探索の双方を支えます。モジュール引数として保つことで、二つの構成が共通して必要とする強さを記録できます。その間の符号化、抽象化、辞書式順序の法則、到達可能性の議論は追加の公理を用いません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.CanonicalNames {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The vocabulary a name is written in comes from the first-order language of set theory. A formula here carries a domain of constant symbols together with a fixed number of free-variable slots, and the constructors cover membership, equality, the connectives, falsity, and both kinds of quantifiers, with bounded forms listed alongside. This syntax already exists; the chapter only needs to name and compare formulas of a special shape, those whose constant domain is empty.
<!--zh-->
名字赖以书写的词汇来自集合论的一阶语言。这里的公式带有一个常元符号域和固定数目的自由变量槽位，构造子覆盖了隶属、相等、联结词、假，以及两类量词，其中受限形式也一并列出。这套语法早已存在；本章只需对一种特殊形状的公式，即常元域为空的那些公式，加以命名和比较。
<!--ja-->
名前を書き表す語彙は、集合論の一階述語論理の言語から来る。ここでの論理式は、定数記号の領域と固定個数の自由変数スロットをともに持ち、構成子は所属、等号、論理結合子、偽、そして両種の量化子を覆う。有界形式も並べて挙げられている。この構文は既に存在しており、本章が要するのは、定数領域が空であるという特別な形の論理式に名前を付け、比較することだけである。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
```

<!--en-->
Several existing operations on formulas do the real work of turning a definition with constants into a name. The coding of terms and formulas as sets supplies the code that will become the first key; the relabelling lemma says that reading a formula under an embedding of constant domains preserves satisfaction; occurrence counting and parameter abstraction together replace constants by fresh variables and a parameter vector. On the side of the universe, the structure `𝒮ᵥ` interprets the language inside `V`, and the pair construction `pr` is what packages code fragments as sets.
<!--zh-->
几项既有的公式操作承担了「把带常元的定义变成名字」的实质工作。把词项与公式编码为集合的操作给出将成为第一个键的码；改名引理说，经常元域的嵌入去读一条公式时满足关系不变；出现计数与参数抽象一起，把常元换成新变量和一个参数向量。在宇宙一侧，结构 `𝒮ᵥ` 在 `V` 之内解释这套语言，而配对构造 `pr` 正是把码的片段包装成集合的东西。
<!--ja-->
定数付きの定義を名前へ変える実質的な作業は、論理式に対する既存のいくつかの操作が担う。項と論理式を集合へ符号化する操作は、第一の鍵となるコードを供給する。定数の改名の補題は、定数領域の埋め込みを通して論理式を読んでも充足関係が保たれることを述べる。出現の数え上げとパラメータの抽象は、定数を新しい変数とパラメータ列に置き換える。宇宙の側では、構造 `𝒮ᵥ` が `V` の中でこの言語を解釈し、対の構成 `pr` がコードの断片を集合として包む。
<!--/-->

```agda
open import FOL.Manipulation.ConstantMapping using ( mapTm; embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo; constantsFo )
open import FOL.Manipulation.ParameterAbstraction using ( absFo; ⊨-abs₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The constructible side contributes the objects being named. `Lset` is a stage of the constructible hierarchy inside `V`, and `𝒟ₒ` is the definable-powerset operator: it takes a set and returns the set of its subsets definable by a one-variable formula with constants from it. Crucially, `𝒟ₒ` hands back only a truncated witness that such a formula exists, so completeness of naming will inherit that truncation rather than a chosen formula. The module `DefOf` carries the inner satisfaction relation and its smallness facts, which denotation is built from.
<!--zh-->
可构造一侧贡献的是被命名的对象。`Lset` 是 `V` 之内可构造层级的一层，而 `𝒟ₒ` 是可定义幂集算子：它取一个集合，返回其中由「带该集合常元的单变量公式」可定义的子集所成之集。关键在于，`𝒟ₒ` 交还的只是「存在这样一条公式」这一截断的见证，因此命名的完备性将继承这种截断，而非一条被选定的公式。模块 `DefOf` 载有内层满足关系及其小性事实，指称正是由它们造出的。
<!--ja-->
構成可能な側は、名前を付けられる対象を供給する。`Lset` は `V` の中の構成可能階層の一つの段階であり、`𝒟ₒ` は定義可能冪集合の演算子である。これは集合を一つ取り、その部分集合のうち、それを定数域とする一変数の論理式で定義できるもの全体を返す。決定的なのは、`𝒟ₒ` が手渡すのはそのような論理式が存在することの截断された証拠だけだという点で、したがって名前付けの完全性は、選ばれた論理式ではなくこの截断を引き継ぐことになる。モジュール `DefOf` は内側の充足関係とその小ささの事実を運び、指示対象はこれらから組み立てられる。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( Lset; Lset-mono; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
```

<!--en-->
The first key needs a home where an order already reaches it. The numerals of the language, the von Neumann naturals, are ordinals inside `L`, and each numeral sits in the successor of its own stage; pairs of stage members appear two stages later. The limit stage `Lset ω` collects what appears by some finite stage, and `Limit` is a member of it together with a certificate of that membership. On this stage `limitOrder` well-orders everything, and `Tri-map` transports trichotomy verdicts along an equivalence, a tool the last key's trichotomy will reuse.
<!--zh-->
第一个键需要一个既有序可及的安身之处。该语言的数码，即 von Neumann 自然数，是 `L` 之内的序数，且每个数码落在其后一层之中；层成员的配对则在两阶之后出现。极限层 `Lset ω` 收拢了到某个有穷层为止出现的对象，而 `Limit` 就是它的成员连同隶属的凭证。在这一层上，`limitOrder` 把一切良序化；`Tri-map` 则沿等价搬运三歧判决，第三键的三歧将复用这一工具。
<!--ja-->
第一の鍵には、既に順序が届く居場所が必要である。この言語の数項、すなわち von Neumann 自然数は `L` の中の順序数であり、各数項はその一段上の段階に属する。段階の要素どうしの対は、さらに二段先に現れる。極限段階 `Lset ω` は、何らかの有限段階までに現れたものを集め、`Limit` はその要素に所属の証明書を添えたものである。この段階の上で `limitOrder` がすべてを整列し、`Tri-map` は同値に沿って三分の判定を輸送する。この道具は第三の鍵の三分で再利用される。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( pr∈Lset-suc )
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Limit; inSome; limitOrder; Tri-map )
open import L.WellOrder.Base {ℓ-suc ℓ}
```

<!--en-->
The abstract notion of order is a strict well-order packaged as a record: a strict comparison, trichotomy, irreflexivity, transitivity, and well-foundedness, together with a least-element search `leastOf` that consumes such a record. These four laws are exactly what the names will be shown to satisfy. On the type-theoretic side, the imported tools handle the dependent bookkeeping that arises because a name's formula and parameter vector have the arity as an index: a way to build a path into a dependent pair, a commutation of substitution with a constant function along a path, the two directions of an equivalence, and injectivity extracted from an embedding.
<!--zh-->
序的抽象概念被打包成记录的严格良序：一个严格比较、三歧性、非自反性、传递性与良基性，连同使用这种记录的最小元搜索 `leastOf`。名字将被证明恰好满足这四条定律。在类型论一侧，导入的工具处理因名字的公式与参数向量以元数为索引而产生的依值类型中的等式处理：向依值对中造路径的办法、替换沿路径与常值函数的交换、等价的两个方向，以及从嵌入提取的单射性。
<!--ja-->
順序の抽象概念は、レコードとしてまとめられた狭義整列順序である。狭義の比較、三分性、非反射性、推移性、整礎性に加え、そのようなレコードを用いる最小要素探索 `leastOf` をともなう。名前が満たすと示されるのは、まさにこの四つの法則である。型理論の側で読み込まれる道具は、名前の論理式とパラメータ列がアリティを指数にもつことから生じる依存型における等式の処理を扱う。依存対へのパスの構成、パスに沿った置換と定数関数の交換、同値の両方向、そして埋め込みから取り出す単射性である。
<!--/-->

```agda
  using ( Tri; lt; eq; gt; SWO; IsLeast; leastOf )

open import Cubical.Foundations.Prelude using ( toPathP )
open import Cubical.Foundations.Transport using ( constSubstCommSlice )
open import Cubical.Foundations.Equiv using ( equivFun; invEq )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
```

<!--en-->
Natural numbers supply the arities, and their order supplies the middle key. Its trichotomy here is decidable, so the comparison of names can branch on `arity a ≟ arity b` directly; transitivity and well-foundedness of `_<_` enter the corresponding laws. `⇔toPath` turns a proof of a propositional biconditional into a path, which is how the membership characterization of a denotation will be stated as an equality of propositions rather than two implications, and `toℕ` reads a bounded index as an ordinary numeral.
<!--zh-->
自然数供出诸元数，而自然数上的序供出中间那个键。它的三歧在此是可判定的，故名字的比较可以直接在 `arity a ≟ arity b` 上分岔；`_<_` 的传递性与良基性进入相应的定律。`⇔toPath` 把命题双条件的证明变成路径，指称的隶属刻画正因此才被陈述为命题的等式，而非两个蕴涵；`toℕ` 则把一个有界索引读成普通的数码。
<!--ja-->
自然数はアリティを供給し、自然数上の順序は中間の鍵を供給する。ここでのその三分は決定可能なので、名前の比較は `arity a ≟ arity b` の上で直接分岐できる。`_<_` の推移性と整礎性は対応する法則に入る。`⇔toPath` は命題的な同値条件の証明をパスへ変えるもので、これにより指示対象の所属の特徴づけは、二つの含意ではなく命題の等式として述べられる。`toℕ` は有界な添字を通常の数項として読む。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Nat using ( _+_; +-comm )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.FinData using ( toℕ )
```

<!--en-->
The lexicographic comparison will be written as a sum type: each key's verdict is either strictly below or equal, and after equality the next key decides. So the chapter needs binary sums with their constructors, vectors of parameters with their map, and the well-founded induction toolkit: `Acc` expresses that every strict descent from an element terminates, `acc` packages such a proof, and `WFI` turns it into an induction principle. The vectors here are indexed by their lengths, which is what forces the arity transport questions studied later.
<!--zh-->
字典序比较将写成和类型：每个键的判决要么严格在前，要么相等，相等时再由下一个键决定。因此本章需要带构造子的二元和、带 `map` 的参数向量，以及良基归纳的工具箱：`Acc` 表达「从任一元素出发的严格下降都会终止」，`acc` 打包这样一份证明，`WFI` 把它变成归纳原理。这里的向量以其长度为索引，正是这一点引出后文要研究的元数转换问题。
<!--ja-->
辞書式比較は和型として書かれる。各鍵の判定は「狭義に前」か「等しい」かのいずれかであり、等しい場合は次の鍵が決める。したがって本章には、構成子つきの二項和、`map` をもつパラメータ列、そして整礎帰納の道具一式が要る。`Acc` は要素からの任意の狭義降下が終わることを表し、`acc` がその証明を包み、`WFI` がそれを帰納原理に変える。ここでの列は長さを指数にもつ。まさにそれが、後で扱うアリティの輸送の問題を強いるのである。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Vec using ( map )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )
```

<!--en-->
Two eliminations have their target types fixed by the mathematics. The empty type's recursor discharges the impossible cases, such as a parameter-free formula containing a constant. Propositional truncation turns a chosen witness into a mere existence claim: `∥ A ∥₁` is inhabited as soon as `A` is, and it may be eliminated only into proposition-valued targets. The hierarchy of cumulative sets contributes `sett`, a set assembled from a small index type, and the embedding `⟪_⟫` that regards a small type's element as a member of the universe.
<!--zh-->
两种消去的靶类型由数学本身固定。空类型的消去子处理不可能的情形，比如一条含常元的无参公式。命题截断把被选定的见证变成单纯的存在主张：只要 `A` 有元素，`∥ A ∥₁` 就有元素，而它只能消去到取值为命题的靶子。累积集合的层级贡献了 `sett`，即由小索引类型组装出的一个集合，以及嵌入 `⟪_⟫`，它把小类型中的元素看作宇宙的成员。
<!--ja-->
二つの消去の帰結となる型は、数学そのものによって固定されている。空型の消去子は、定数を含むパラメータなし論理式といった不可能な場合を片付ける。命題的截断は、選ばれた証拠を単なる存在主張へ変える。`A` が居住者をもてば `∥ A ∥₁` ももつが、その消去は命題値の帰結に限られる。累積的集合の階層は、小さな指数型から組み立てられる集合 `sett` と、小さな型の要素を宇宙の要素とみなす埋め込み `⟪_⟫` を供給する。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
```

<!--en-->
The last group fixes the concrete interpretation the names will be read in. `#` turns a natural number into the corresponding numeral inside the universe, and `ω` is the infinite set, so numeral membership certificates like those in the limit stage can be produced. Then the truth values are pinned to propositions: opening the truth algebra at `hPropAlgebra (ℓ-suc ℓ)` makes the logical connectives act on `hProp`, and opening the `ZFStructure` semantics at the structure `𝒮ᵥ` fixes what a formula means inside `V`. Every satisfaction judgment below is this inner one, and that is what ties a name's denotation to the definable powerset's own notion of definability.
<!--zh-->
最后一组固定了诸名字被解读于其中的具体解释。`#` 把自然数变成宇宙之内对应的数码，而 `ω` 是无穷集，于是极限层那类数码隶属凭证便可制造。随后真值被固定在命题上：在 `hPropAlgebra (ℓ-suc ℓ)` 处打开真值代数，使诸逻辑联结词作用于 `hProp`；再在结构 `𝒮ᵥ` 处打开 `ZFStructure` 的语义，便固定了一条公式在 `V` 之内意味着什么。下文的每一个满足判断都是这个内层判断，而正是它把名字的指称与可定义幂集自己的可定义性概念扣在一起。
<!--ja-->
最後のグループは、名前が読まれる具体的な解釈を固定する。`#` は自然数を宇宙の中の対応する数項へ変え、`ω` は無限集合である。したがって極限段階で用いた種類の数項の所属証明書が作れる。次に真値は命題に固定される。真理値代数を `hPropAlgebra (ℓ-suc ℓ)` で開けば論理結合子が `hProp` の上に働き、構造 `𝒮ᵥ` のもとで `ZFStructure` の意味論を開けば、論理式が `V` の中で何を意味するかが定まる。以下のすべての充足判断はこの内側の判断であり、名前の指示対象を定義可能冪集合自身の定義可能性の概念に結びつけるのはこれである。
<!--/-->

```agda
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )

```

<!--en-->
These final declarations fix the interpretation used throughout the chapter: formulas are read in the set-theoretic structure on `V`, with proposition-valued truth.
<!--zh-->
最后这些声明固定了全章采用的解释：公式在 `V` 上的集合论结构中读取，真值取命题。
<!--ja-->
最後の宣言群は章全体で用いる解釈を固定する。論理式は `V` 上の集合論的構造で読み、真理値は命題とする。
<!--/-->

```agda
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## A parameter-free code is hereditarily finite

The first key of a name is the code of its parameter-free formula. Such a finite syntax code is hereditarily finite, so it already belongs to the limit stage where the established well-order can compare it.

The first key wants the formula as a member of `Lset ω`{.Agda}, so the first thing to establish is that its code is one. Read the coding clauses in `V.Coding` and nothing else is used: a numeral for the tag, a numeral for a de Bruijn index, and Kuratowski pairs holding the parts. The one construction that could leave the finite world is the constant clause, which puts an arbitrary set into the code, and a parameter-free formula has no constants at all.

So two closure facts suffice, and both are lifted rather than re-derived: `inSome`{.Agda} of `L.Choice.FiniteStageOrders` says a member of `Lset ω`{.Agda} has appeared by some finite stage, and `pr∈Lset-suc`{.Agda} of `L.Axioms.Basic` says a Kuratowski pair of two members of a stage appears two stages later. Advancing from one finite stage to a later one is monotonicity applied along the successors of the numerals, which is the only recursion here.
<!--zh-->
## 无参的码是遗传有穷的

名字的第一个键是其无参公式的码。这样的有限语法码是遗传有穷的，因此早已属于极限层，可以由既有良序比较。

第一个键要把公式当作 `Lset ω`{.Agda} 的成员，故首先要立的就是「它的码是这样一个成员」。读一遍 `V.Coding` 的诸编码子句便知别无他物：一个数码作标签，一个数码作 de Bruijn 序号，以及装着各部分的 Kuratowski 对。唯一可能走出有穷世界的构造是常元那一条，它把一个任意集合放进码里，而无参公式压根没有常元。

于是两条封闭性事实就够了，而两条都是引用既有结果、并非重新证明：`L.Choice.FiniteStageOrders` 的 `inSome`{.Agda} 说 `Lset ω`{.Agda} 的成员到某个有穷层为止已经现身，而 `L.Axioms.Basic` 的 `pr∈Lset-suc`{.Agda} 说两层成员的 Kuratowski 对在两阶之后现身。至于从一个有穷层推进到更晚的层，只需沿数码的后继逐级施用单调性，这也是本节唯一的递归。
<!--ja-->
## パラメータなしコードは遺伝的有限である

名前の第一の鍵は、パラメータなし論理式のコードである。この有限な構文コードは遺伝的有限なので、既に極限段階に属し、そこで構成済みの整列順序によって比較できる。

第一の鍵は、論理式を `Lset ω`{.Agda} の要素として扱う。そこでまず示すべきは、そのコードがそうであるということだ。`V.Coding` の符号化の節々を読めば、使われているのはこれだけである。タグのための数項、de Bruijn 番号のための数項、そして各部分を包む Kuratowski 対。有穷の世界から出てしまうおそれのある構成は定数の節だけだが、それは任意の集合をコードに入れるものであり、パラメータなし論理式には定数がそもそもない。

そこで必要なのは二つの閉包性の事実だけで、どちらも再証明せず既存の結果を引き上げて使う。`L.Choice.FiniteStageOrders` の `inSome`{.Agda} は、`Lset ω`{.Agda} の要素が有限段階の中には現れていることを言い、`L.Axioms.Basic` の `pr∈Lset-suc`{.Agda} は、一つの段階の二つの要素の Kuratowski 対が二段階後に現れることを言う。ある有限段階から後の段階へ進むのは、数項の後者に沿って単調性を適用することであり、これがこの節で唯一の再帰である。
<!--/-->

<!--en-->
A membership certificate for the limit stage is hard to use directly, because it says only that the element is somewhere in the finite stages. The auxiliary predicate `AtStage` records which finite stage: a natural number `k` together with a proof that the element lies in `Lset (# k)`. Once an element is pinned to a stage, `raiseTo` moves the certificate forward, from stage `# k` to stage `# (d + k)`, by recursion on `d`: each successor step observes that a stage contains the numeral bounding it, via `self∈sucV`, and `Lset-mono` turns that into monotonicity of the stages.
<!--zh-->
极限层的隶属凭证难以直接使用，因为它只说该元素处在某个有穷层之中。辅助谓词 `AtStage` 记录的是哪个有穷层：一个自然数 `k`，连同该元素属于 `Lset (# k)` 的证明。一旦把元素固定在某一层上，`raiseTo` 便能前移这份凭证，从层 `# k` 推进到层 `# (d + k)`，对 `d` 递归：每一步后继都通过 `self∈sucV` 观察到该层包含界定它的那个数码，而 `Lset-mono` 把这一点转成层的单调性。
<!--ja-->
極限段階への所属の証明書は、要素が有限段階のどこかにあるとしか言わないので、直接使うには扱いにくい。補助の述語 `AtStage` は、どの有限段階かを記録する。自然数 `k` と、その要素が `Lset (# k)` に属する証明の組である。要素を一つの段階に固定してしまえば、`raiseTo` はその証明書を前へ進められる。段階 `# k` から段階 `# (d + k)` へ、`d` についての再帰で進む。各後者の段階で、`self∈sucV` によりその段階がそれを限定する数項を含むことが観察され、`Lset-mono` がそれを段階の単調性に変える。
<!--/-->

```agda
private
  AtStage : S → Type (ℓ-suc ℓ)
  AtStage x = Σ[ k ∈ ℕ ] ⟨ x ∈ˢ Lset (# k) ⟩

  raiseTo : (x : S) (d k : ℕ) → ⟨ x ∈ˢ Lset (# k) ⟩ → ⟨ x ∈ˢ Lset (# (d + k)) ⟩
  raiseTo x zero    k h = h
```

<!--en-->
Numerals are the atoms of this argument, so their placement comes first. By `numeral-ord`, `# k` is an ordinal in `L`, and `ord∈Lset-suc` places it in the successor of its own stage. The proof `#∈ω` says that the bounding numeral belongs to `ω`; monotonicity therefore lifts the numeral into the limit stage. The companion closure statement places `pr x y` in the limit whenever both components are there, exactly as the coding of composite syntax requires.
<!--zh-->
数码是整个论证的原子，故先安置它们。由 `numeral-ord`，`# k` 是 `L` 中的序数，`ord∈Lset-suc` 把它放入自身层的后继。证明 `#∈ω` 说明作为界的数码属于 `ω`，故单调性把该数码提升到极限层。相伴的封闭性陈述则说明，只要 `x` 与 `y` 都在极限层，`pr x y` 也在那里；复合语法的编码恰好需要这一点。
<!--ja-->
数項はこの議論の原子なので、その配置から始めます。`numeral-ord` により `# k` は `L` の順序数であり、`ord∈Lset-suc` はそれを自身の段階の後者に置きます。`#∈ω` は境界となる数項が `ω` に属することを述べるので、単調性によってその数項を極限段階へ持ち上げられます。対に関する閉性は、`x` と `y` がともに極限段階にあれば `pr x y` もそこにあると述べ、複合構文の符号化に必要な事実を与えます。
<!--/-->

```agda
  raiseTo x (suc d) k h = Lset-mono (self∈sucV (# (d + k))) (raiseTo x d k h)

numeral∈limit : (k : ℕ) → ⟨ (# k) ∈ˢ Lset ω ⟩
numeral∈limit k = Lset-mono (#∈ω (suc k)) (ord∈Lset-suc (# k) (numeral-ord k))

pr∈limit : (x y : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ y ∈ˢ Lset ω ⟩
         → ⟨ pr x y ∈ˢ Lset ω ⟩
```

<!--en-->
The proof of the pair statement has one wrinkle: `inSome` delivers its stage witnesses inside a propositional truncation, so the stage numbers cannot be picked out as data. The goal, however, is a membership proposition, and truncated witnesses may be eliminated into a proposition-valued target. The outer `PT.rec` unpacks the witness for `x`, and the inner one the witness for `y`, feeding both into the helper `both`, which does the actual work.
<!--zh-->
配对这条陈述的证明有一处波折：`inSome` 把层见证交在命题截断之内，故那些层编号无法作为数据被选出。但目标本身是一个隶属命题，而截断的见证允许消去到取值为命题的靶子。外层的 `PT.rec` 拆开 `x` 的见证，内层的拆开 `y` 的见证，然后把两者交给真正干活的辅助引理 `both`。
<!--ja-->
対の主張の証明には一つ折り返し点がある。`inSome` が渡す段階の証人は命題的截断の中にあるため、その段階の番号をデータとして取り出すことはできない。しかし帰結は所属の命題であり、截断された証人は命題値の帰結へは消去できる。外側の `PT.rec` が `x` の証人をほどき、内側のものが `y` の証人をほどき、両方を実際の作業をする補題 `both` に渡す。
<!--/-->

```agda
pr∈limit x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset ω))
  (λ atX → PT.rec (snd (pr x y ∈ˢ Lset ω)) (both atX) (inSome y hy))
  (inSome x hx)
  where
  both : AtStage x → AtStage y → ⟨ pr x y ∈ˢ Lset ω ⟩
```

<!--en-->
Given stage numbers `j` for `x` and `k` for `y`, the two elements are raised to the common stage `# (k + j)`, so that `pr∈Lset-suc` applies and puts the pair two stages later, under the numeral `# (suc (suc (k + j)))` that bounds it in `ω`; the summands of the common stage come in opposite orders, and one substitution along `+-comm` repairs that. With numerals and pairs closed under the limit stage, a tagged code, which is just the pair of a numeral and the payload, is closed as well, by `tag∈limit`. These three facts are the whole induction load for the syntax to come.
<!--zh-->
设 `x` 的层号为 `j`，`y` 的为 `k`，先把两个元素抬到公共层 `# (k + j)`，使 `pr∈Lset-suc` 得以适用，把这一对放进两阶之后、由 `# (suc (suc (k + j)))` 在 `ω` 中界定的层；公共层的两个加数顺序相反，一次沿 `+-comm` 的替换把它修正。既然数码与对都对极限层封闭，而带标签的码不过是数码与载荷组成的对，`tag∈limit` 便也给出封闭性。这三条事实就是接下来那场语法归纳的全部负担。
<!--ja-->
`x` の段階の番号を `j`、`y` のそれを `k` とすると、まず二つの要素を共通の段階 `# (k + j)` へ持ち上げて `pr∈Lset-suc` が適用できるようにし、その対を二段階後、`ω` において `# (suc (suc (k + j)))` の下に置く。共通段階の被加数は逆順に現れるので、`+-comm` に沿った一回の置換がこれを正す。数項と対が極限段階で閉じている以上、タグ付きコードも、それは数項と中身の対にすぎないが、`tag∈limit` により閉じている。この三つの事実が、これから行う構文の帰納の負担のすべてである。
<!--/-->

```agda
  both (j , hj) (k , hk) = Lset-mono (#∈ω (suc (suc (k + j))))
    (pr∈Lset-suc (# (k + j)) x y (raiseTo x k j hj)
      (subst (λ n → ⟨ y ∈ˢ Lset (# n) ⟩) (+-comm j k) (raiseTo y j k hk)))

tag∈limit : (k : ℕ) (x : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ VCode.mkTag k x ∈ˢ Lset ω ⟩
tag∈limit k x h = pr∈limit (# k) x (numeral∈limit k) h
```

<!--en-->
With numerals, pairs and tags in place, the placement of every parameter-free code follows by structural induction on the syntax. The induction is short because the three closure facts above carry all the work; the constructor cases only reassemble them, and the constant case, the only one that could escape, is void because the constant domain is the empty type. The tag numbers appear as literals throughout, and nothing about their values is used beyond their being numerals.
<!--zh-->
数码、配对与标签齐备之后，每条无参码的安置便由语法上的结构归纳给出。这条归纳很短，因为上面三条封闭性事实承担了全部工作；各构造子情形只是把它们重新拼装，而唯一可能逃出有穷世界的常元情形是空的，因为常元域是空类型。标签数字全程以字面量出现，除「是数码」之外没有用到它们的任何值。
<!--ja-->
数項、対、タグが揃えば、すべてのパラメータなしコードの配置は構文上の構造的帰納で従う。この帰納が短いのは、先の三つの閉包性の事実がすべての仕事を担うからである。各構成子の場合はそれらを組み立て直すだけであり、有穷の世界から逃げ出しうる唯一の場合である定数の場合は、定数領域が空型であるため空である。タグの数字は全体を通してリテラルとして現れるが、その値について使われるのは、数項であるという以上のことではない。
<!--/-->

<!--en-->
Terms are handled first, and their induction is two clauses. A variable has no constant content, so its code is the numeral for its de Bruijn index wrapped in the tag `1`, and `tag∈limit` applies at once. The constant clause of a parameter-free term is a contradiction: the constant domain `⊥*` has no elements, so the impossible case is discharged by the empty type's recursor. The `mapTm` in the statement is the embedding of a parameter-free term into the working syntax, which replaces constants by host values; over `⊥*` it has nothing to replace.
<!--zh-->
先处理词项，其归纳只有两条子句。变量不含常元内容，故其码是包在标签 `1` 里的 de Bruijn 序号的数码，`tag∈limit` 当即适用。无参词项的常元子句是矛盾：常元域 `⊥*` 没有元素，不可能情形由空类型的消去子打发。陈述中的 `mapTm` 是把无参词项嵌入工作语法的操作，它把常元换成宿主值；对 `⊥*` 而言无物可换。
<!--ja-->
まず項を扱う。その帰納は二つの節からなる。変数は定数の内容をもたないので、そのコードは de Bruijn 番号の数項をタグ `1` で包んだものであり、`tag∈limit` が直ちに適用される。パラメータなし項の定数の節は矛盾である。定数領域 `⊥*` には要素がないので、不可能な場合は空型の消去子で片付く。述語の中の `mapTm` は、パラメータなし項を作業用の構文へ埋め込む操作で、定数をホストの値に置き換える。`⊥*` の上では置き換えるものは何もない。
<!--/-->

```agda
codeTm∈limit : ∀ {n} (t : Term (⊥* {ℓ}) n)
             → ⟨ VCode.⌜ mapTm Empty.rec* t ⌝ᵗ ∈ˢ Lset ω ⟩
codeTm∈limit (con c) = Empty.rec* c
codeTm∈limit (var i) = tag∈limit 1 (# (toℕ i)) (numeral∈limit (toℕ i))

code∈limit : ∀ {n} (χ : Formula (⊥* {ℓ}) n) → ⟨ VCode.⌜ embed χ ⌝ ∈ˢ Lset ω ⟩
```

<!--en-->
Formulas follow the same pattern, with one tag per constructor. Each binary clause pairs the codes of the two immediate subformulas or subterms under a tag, the connective and quantifier clauses wrap a single subcode, and falsity is tag `5` applied to the numeral zero. In every case the result is a `tag∈limit` or `pr∈limit` application to induction hypotheses, so the clause bodies are one line each.
<!--zh-->
公式遵循同一模式，每个构造子一个标签。每个二元子句把两条直接子公式或子词项的码在一个标签下配成对，联结词与量词子句包装单一的子码，而假就是零的裸数码。每种情形的结果都是对归纳假设施用一次 `tag∈limit` 或 `pr∈limit`，故各子句体都只有一行。
<!--ja-->
論理式は同じ形をたどり、構成子ごとに一つのタグをもつ。二項の各節は、直下の二つの部分論理式または部分項のコードを一つのタグのもとで対にし、結合子と量化子の節は単一の部分コードを包み、偽は零の裸の数項である。いずれの場合も帰結は、帰納の仮定に対する `tag∈limit` か `pr∈limit` の一回の適用であり、だから各節の本体は一行である。
<!--/-->

```agda
code∈limit (t ∈̇ u)  = tag∈limit 0 _ (pr∈limit _ _ (codeTm∈limit t) (codeTm∈limit u))
code∈limit (t ≐ u)  = tag∈limit 1 _ (pr∈limit _ _ (codeTm∈limit t) (codeTm∈limit u))
code∈limit (φ ∧̇ ψ)  = tag∈limit 2 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
code∈limit (φ ∨̇ ψ)  = tag∈limit 3 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
code∈limit (φ ⇒̇ ψ)  = tag∈limit 4 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
```

<!--en-->
The last four clauses cover the quantifiers and their bounded forms, with tags `6` through `9`; the bounded forms additionally pair in the code of the ranging term. What matters for the chapter is only the end result: every parameter-free formula has a code sitting in the limit stage, ready to be compared by the order that stage already carries. The tag numbering is arbitrary bookkeeping, not part of any mathematical claim.
<!--zh-->
最后四条子句覆盖量词及其受限形式，标签为 `6` 到 `9`；受限形式还额外把辖域词项的码配进对中。对本章要紧的只是最终结果：每条无参公式都有一个落在极限层中的码，随时可被该层既带的序去比较。标签编号只是编码约定，不属于任何数学主张。
<!--ja-->
最後の四つの節は量化子とその有界形式を覆い、タグは `6` から `9` までである。有界形式はさらに、範囲を定める項のコードを対に加える。この章にとって重要なのは帰結だけである。すべてのパラメータなし論理式は極限段階に居座るコードをもち、その段階が既にもつ順序で比較できる。タグの番号付けは任意の簿記であり、数学的主張の一部ではない。
<!--/-->

```agda
code∈limit ⊥̇        = tag∈limit 5 _ (numeral∈limit 0)
code∈limit (∃̇ φ)    = tag∈limit 6 _ (code∈limit φ)
code∈limit (∀̇ φ)    = tag∈limit 7 _ (code∈limit φ)
code∈limit (∀̇∈ t φ) = tag∈limit 8 _ (pr∈limit _ _ (codeTm∈limit t) (code∈limit φ))
code∈limit (∃̇∈ t φ) = tag∈limit 9 _ (pr∈limit _ _ (codeTm∈limit t) (code∈limit φ))
```

<!--en-->
A member of the limit stage carries a certificate of membership, so the first key is not the bare code but the code together with that certificate. This subsection packages the two, and records one auxiliary fact about transporting along equalities of arities that the comparison will need.
<!--zh-->
极限层的成员带有隶属凭证，故第一个键不是光秃秃的码，而是码连同那张凭证。本小节把二者打包，并记录一项关于沿元数等式传输的辅助事实，比较时将用到它。
<!--ja-->
極限段階の要素は所属の証明書をともなう。それゆえ第一の鍵は裸のコードではなく、コードとその証明書を合わせたものである。この小節は両者をまとめ、比較に必要となる、アリティの等式に沿う輸送についての補助事実を一つ記録する。
<!--/-->

<!--en-->
`limitCode` sends a parameter-free formula to the pair of its code and the membership proof just constructed; this pair is exactly an element of `Limit`, the type the limit-stage order acts on. The second statement concerns a subtlety of dependent syntax: a formula's type mentions its arity, so after two names have been found to have equal arities, one formula must be substituted along that equality before it can even be compared with the other. `code-shift` says this substitution is invisible to the code: transporting a formula of arity `suc i` along a path `i ≡ j` yields a formula with the same code.
<!--zh-->
`limitCode` 把无参公式送到「码与刚造好的隶属证明」组成的对；这一对恰是 `Limit` 的元素，即极限层序所作用的对象。第二条陈述涉及依值语法的一处微妙：公式的类型提及它的元数，故当发现两个名字的元数相等之后，必须先把一条公式沿该等式替换，才能与另一条比较。`code-shift` 说这次替换对码不可见：把元数为 `suc i` 的公式沿路径 `i ≡ j` 传输，得到的公式具有相同的码。
<!--ja-->
`limitCode` は、パラメータなし論理式を、そのコードと今作った所属証明の対へ送る。この対はまさに `Limit` の要素であり、極限段階の順序が作用する対象である。二番目の主張は依存的な構文の微妙さに関わる。論理式の型はそのアリティに言及するので、二つの名前のアリティが等しいと判明した後、一方の論理式はその等式に沿って置換しなければ、他方と比較することさえできない。`code-shift` は、この置換がコードには見えないことを言う。アリティ `suc i` の論理式をパス `i ≡ j` に沿って輸送しても、同じコードをもつ論理式が得られる。
<!--/-->

```agda
limitCode : ∀ {n} → Formula (⊥* {ℓ}) n → Limit
limitCode χ = VCode.⌜ embed χ ⌝ , code∈limit χ

code-shift : {i j : ℕ} (e : i ≡ j) (χ : Formula (⊥* {ℓ}) (suc i))
           → VCode.⌜ embed (subst (λ k → Formula (⊥* {ℓ}) (suc k)) e χ) ⌝
           ≡ VCode.⌜ embed χ ⌝
```

<!--en-->
The proof invokes the general fact that a function whose result type does not depend on the index commutes with substitution in that index. The coding of formulas lands in the fixed type `S` of sets, regardless of the arity the formula lives at, so the transported formula's code equals the original's by `constSubstCommSlice`; the statement is arranged with `sym` so the path reads from the substituted formula back to the original.
<!--zh-->
证明援引一条一般事实：结果类型不依赖索引的函数，与沿该索引的替换可交换。公式的编码落在固定的集合类型 `S` 中，与公式所处的元数无关，故由 `constSubstCommSlice`，传输后的公式的码等于原来的码；陈述用 `sym` 排布成从被替换的公式指回原公式的方向。
<!--ja-->
証明は、帰結の型が指数に依存しない関数はその指数に沿う置換と可換だという一般事実を用いる。論理式の符号化は、論理式がどのアリティに居ようと、固定された型 `S` に落ちる。それゆえ `constSubstCommSlice` により、輸送された論理式のコードは元のものと等しい。主張は `sym` で、置換された論理式から元の論理式へと読める方向に並べてある。
<!--/-->

```agda
code-shift e χ = sym (constSubstCommSlice
  (λ k → Formula (⊥* {ℓ}) (suc k)) S (λ _ ψ → VCode.⌜ embed ψ ⌝) e χ)

```

<!--en-->
## A parameter-free formula is recovered from its image

At a fixed arity, coding does not identify two different parameter-free formulas. Injectivity follows by decoding the hereditarily finite image and then using injectivity of the syntax encoding.

Two names with the same code and the same arity must be built from the same formula, or the comparison would rank two different names as neither below the other and equal to nothing. `V.Coding` proved its own injectivity, but it proved it over the working syntax, whose constant domain is the carrier; what is needed here is injectivity for the parameter-free formulas, which reach that syntax through `embed`{.Agda}.

The gap is closed by an **erasure** running the other way, and the erasure can be crude because it only has to be a left inverse on the parameter-free formulas. A constant is sent to the variable of index zero, which is available because every formula under consideration has at least one free-variable slot, and every other clause is the identity on the constructor. On a formula with no constants the erasure changes nothing, one clause at a time, and injectivity is then three path compositions.
<!--zh-->
## 无参公式可从它的像还原

在固定元数下，编码不会把两条不同的无参公式等同起来。先从遗传有穷的像解码，再用语法编码的单射性，即得这一单射性。

码与元数都相同的两个名字，其公式必须相同，否则那次比较就会把两个不同的名字判为「互不更小、又不与任何东西相等」。`V.Coding` 证过它自己的单射性，但它是对工作语法证的，那里的常元域是载体；此处所需的是无参公式的单射性，而无参公式经 `embed`{.Agda} 映入那套语法。

上述缺口由一个反向的**抹除**补上，而抹除可以粗糙，因为它只需在无参公式上作左逆。常元被送到序号为零的变量，那个槽位总在，因为视野中的每条公式至少有一个自由变量槽位；其余每条子句都是构造子上的恒等。对一条本来就没有常元的公式，抹除逐条子句什么也没改，于是单射性就是三次路径复合。
<!--ja-->
## パラメータなし論理式はその像から復元できる

同じアリティでは、符号化は異なる二つのパラメータなし論理式を同一視しない。遺伝的有限な像を復号し、構文の符号化の単射性を使えば、この単射性が得られる。

コードとアリティがともに等しい二つの名前は、同じ論理式から作られていなければならない。さもなければ比較は、互いに小さくもなく何とも等しくもないと、異なる二つの名前を判定してしまう。`V.Coding` はそれ自身の単射性を証明しているが、それは作業用の構文、すなわち定数域が台である構文の上でのことだった。ここで必要なのは、`embed`{.Agda} を通してその構文に届くパラメータなし論理式についての単射性である。

この隙間は逆向きに走る**抹消**で埋められる。パラメータなし論理式の上での左逆であれば足りるのだから、抹消は粗雑で構わない。定数は番号零の変数へ送られる。そのスロットは常にあり、扱う論理式はどれも少なくとも一つの自由変数スロットをもつからである。他の各節は構成子の上での恒等写像である。もともと定数を含まない論理式には、抹消は節ごとに何も変えない。すると単射性は、三つのパスの合成になる。
<!--/-->

<!--en-->
The erasure of a term does the only creative work. A constant, whose value in the working syntax is an arbitrary set, is replaced by the variable of index zero; a variable is left alone. This is legitimate only because the target restricts to formulas of arity `suc n`, so slot zero always exists. The erasure of a formula is then declared homomorphically, taking each constructor to itself with the erasures of the parts.
<!--zh-->
词项的抹除是唯一有创造性的工作。常元 (在工作语法中取值为任意集合) 被换成序号为零的变量；变量保持原样。这之所以合法，只因目标限定在元数为 `suc n` 的公式，故零号槽位总在。公式的抹除随后按同态方式声明：每个构造子映到自身，各部分取抹除。
<!--ja-->
項の抹消が、唯一の創造的な仕事をする。作業用の構文では任意の集合を値にもつ定数は、番号零の変数に置き換えられる。変数はそのまま残る。これが正当なのは、帰結がアリティ `suc n` の論理式に制限されているからで、だからこそ零番のスロットが常に存在する。論理式の抹消はその後、同型的に宣言される。各構成子を自身へ写し、部分には抹消を施す。
<!--/-->

```agda
private
  eraseTm : ∀ {n} → Term S (suc n) → Term (⊥* {ℓ}) (suc n)
  eraseTm (con x) = var zero
  eraseTm (var i) = var i

  eraseFo : ∀ {n} → Formula S (suc n) → Formula (⊥* {ℓ}) (suc n)
```

<!--en-->
The first five clauses cover the atomic and propositional formulas: the two atomic relations erase their term arguments, and the three binary connectives recurse on both subformulas. Nothing happens here beyond distributing the erasure through the constructor; the constant information has already been discarded at the term level.
<!--zh-->
前五条子句覆盖原子公式与命题联结词：两条原子关系对各自的词项实参作抹除，三个二元联结词对两条子公式递归。这里发生的不过是把抹除沿构造子分发；常元信息已在词项一层被丢弃。
<!--ja-->
最初の五つの節は、原子論理式と命題結合子を覆う。二つの原子関係は項の実引数に抹消を施し、三つの二項結合子は両方の部分論理式に再帰する。ここで起きるのは、抹消を構成子を通して分配することだけで、定数の情報はすでに項の水準で捨てられている。
<!--/-->

```agda
  eraseFo (t ∈̇ u)  = eraseTm t ∈̇ eraseTm u
  eraseFo (t ≐ u)  = eraseTm t ≐ eraseTm u
  eraseFo (φ ∧̇ ψ)  = eraseFo φ ∧̇ eraseFo ψ
  eraseFo (φ ∨̇ ψ)  = eraseFo φ ∨̇ eraseFo ψ
  eraseFo (φ ⇒̇ ψ)  = eraseFo φ ⇒̇ eraseFo ψ
```

<!--en-->
The remaining five clauses are literally the identity: falsity has no parts, and each quantifier rebuilds itself around the erased body. Every clause is forced; there is no choice in how a formula is erased, which is what makes the left-inverse computation below predictable.
<!--zh-->
余下五条子句就是字面上的恒等：假没有部件，而每个量词围着被抹除的主体重建自身。每条子句都是被迫的；公式如何被抹除没有选择余地，这正是下面左逆计算可以预期的原因。
<!--ja-->
残りの五つの節は文字どおりの恒等である。偽は部分をもたず、各量化子は抹消された本体を包んで自身を組み立て直す。どの節も強制されており、論理式の抹消のされ方に選択の余地はない。これが、このあとの左逆の計算を予測可能にしている。
<!--/-->

```agda
  eraseFo ⊥̇        = ⊥̇
  eraseFo (∃̇ φ)    = ∃̇ eraseFo φ
  eraseFo (∀̇ φ)    = ∀̇ eraseFo φ
  eraseFo (∀̇∈ t φ) = ∀̇∈ (eraseTm t) (eraseFo φ)
  eraseFo (∃̇∈ t φ) = ∃̇∈ (eraseTm t) (eraseFo φ)
```

<!--en-->
The left-inverse property is stated and proved one level at a time. For a term, `eraseTm` after `mapTm Empty.rec*` returns the term itself: the constant case is void because a parameter-free term has no constants, and the variable case is `refl`, since both composites rebuild the same variable. The formula-level statement then claims that erasing the embedding of a parameter-free formula gives back that formula, up to a path.
<!--zh-->
左逆性质逐层陈述、逐层证明。对词项而言，`mapTm Empty.rec*` 之后再作 `eraseTm` 得回原词项：常元情形是空的，因为无参词项本无常元；变量情形是 `refl`，因为两种复合都重建同一个变量。公式层面的陈述随后主张：抹除一条无参公式的嵌入，沿一条路径得回原公式。
<!--ja-->
左逆の性質は、一段ずつ述べられ、一段ずつ証明される。項については、`mapTm Empty.rec*` の後で `eraseTm` を施すと元の項が返る。定数の場合は、パラメータなし項には定数がないので空であり、変数の場合は、どちらの合成も同じ変数を組み立て直すので `refl` である。論理式の水準の主張はその次に、パラメータなし論理式の埋め込みを抹消すれば、パスをひとつ添えて元の論理式が返る、と述べる。
<!--/-->

```agda

  eraseTm-embed : ∀ {n} (t : Term (⊥* {ℓ}) (suc n))
                → eraseTm (mapTm Empty.rec* t) ≡ t
  eraseTm-embed (con c) = Empty.rec* c
  eraseTm-embed (var i) = refl

  eraseFo-embed : ∀ {n} (χ : Formula (⊥* {ℓ}) (suc n)) → eraseFo (embed χ) ≡ χ
```

<!--en-->
The proof proceeds by induction on the formula, reusing the term-level fact wherever a term occurs. Atomic and binary-connective clauses apply a binary congruence `cong₂` to the two recursive results, building the path for the composite from the paths for the parts.
<!--zh-->
证明对公式归纳，凡词项出现处复用词项层的事实。原子与二元联结词的子句对两个递归结果施用二元同余 `cong₂`，由各部分的路径造出复合体的路径。
<!--ja-->
証明は論理式についての帰納で進み、項が現れるところでは項の水準の事実を再利用する。原子と二項結合子の節は、二つの再帰結果に二項の同余 `cong₂` を適用し、部分のパスから合成物のパスを組み立てる。
<!--/-->

```agda
  eraseFo-embed (t ∈̇ u)  = cong₂ _∈̇_ (eraseTm-embed t) (eraseTm-embed u)
  eraseFo-embed (t ≐ u)  = cong₂ _≐_ (eraseTm-embed t) (eraseTm-embed u)
  eraseFo-embed (φ ∧̇ ψ)  = cong₂ _∧̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
  eraseFo-embed (φ ∨̇ ψ)  = cong₂ _∨̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
  eraseFo-embed (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
```

<!--en-->
Falsity needs only `refl`, since nothing was embedded into it, and the four quantifier clauses apply a unary congruence, or `cong₂` where the bounded form also carries a term. With this, every parameter-free formula has an explicit path from its erased image back to itself.
<!--zh-->
假只需 `refl`，因为没有东西被嵌入其中；四个量词子句施用一元同余，受限形式还带词项，故用 `cong₂`。至此，每条无参公式都有一条从被抹除的像指回自身的显式路径。
<!--ja-->
偽には `refl` が要るだけである。そこには何も埋め込まれていないからである。四つの量化子の節は一項の同余を適用し、有界形式は項も運ぶので `cong₂` を使う。これで、すべてのパラメータなし論理式に、抹消された像から自身へ戻る明示的なパスが備わった。
<!--/-->

```agda
  eraseFo-embed ⊥̇        = refl
  eraseFo-embed (∃̇ φ)    = cong ∃̇_ (eraseFo-embed φ)
  eraseFo-embed (∀̇ φ)    = cong ∀̇_ (eraseFo-embed φ)
  eraseFo-embed (∀̇∈ t φ) = cong₂ ∀̇∈ (eraseTm-embed t) (eraseFo-embed φ)
  eraseFo-embed (∃̇∈ t φ) = cong₂ ∃̇∈ (eraseTm-embed t) (eraseFo-embed φ)
```

<!--en-->
Injectivity is now one sentence. Suppose two parameter-free formulas at the same arity have equal embedded codes. The coding's own injectivity turns that into an equality of the embedded formulas; erasing both sides keeps the equality, because erasure is a function; and the left-inverse paths reduce each side to the original formula. The composite path is the desired `χ ≡ ψ`, so distinct parameter-free formulas of one fixed arity cannot have equal codes.
<!--zh-->
单射性如今只是一句话。设两条同元数无参公式的嵌入码相同。编码自身的单射性把它变成两条嵌入公式的相等；对两侧作抹除仍保持相等，因为抹除是一个函数；而左逆路径把两侧各自化归到原公式。复合出的路径就是想要的 `χ ≡ ψ`，故在固定元数下，两条不同的无参公式不可能具有相同的码。
<!--ja-->
単射性は今や一つの文である。同じアリティの二つのパラメータなし論理式について、埋め込まれたコードが一致すると仮定する。符号化自身の単射性がそれを、埋め込まれた論理式どうしの等式に変える。両辺に抹消を施しても等式は保たれる。抹消は関数だからである。そして左逆のパスが、両辺を元の論理式へと帰着させる。合成されたパスが求める `χ ≡ ψ` であり、したがって、固定したアリティでは、異なる二つのパラメータなし論理式のコードは等しくならない。
<!--/-->

```agda

code-inj : ∀ {n} (χ ψ : Formula (⊥* {ℓ}) (suc n))
         → VCode.⌜ embed χ ⌝ ≡ VCode.⌜ embed ψ ⌝ → χ ≡ ψ
code-inj χ ψ e = sym (eraseFo-embed χ)
               ∙ cong eraseFo (VCode.⌜⌝-inj (embed χ) (embed ψ) e)
               ∙ eraseFo-embed ψ
```

<!--en-->
## The naming data

A name records an arity, a parameter-free formula with one output variable, and a parameter vector of that arity. Its denotation is the subset of the stage cut out by the formula under that environment.

Everything in the rest of the chapter is relative to one set `A`, the stage the names are written over, and to one strict well-order of that stage's members, so the work proceeds inside a module `Naming A w`. A **name** is an arity, a parameter-free formula with one more free-variable slot than that, and a vector of that many parameters drawn from `A`'s small member type. The extra slot is the one a subset is carved by; the rest receive the parameters, and the first key is read off the formula at once.
<!--zh-->
## 命名数据

一个名字记录元数、一条多出一个输出变量的无参公式，以及相应长度的参数向量。它所指称的，是该公式在这个环境下从层中界定出的子集。

本章余下的一切都相对于一个集合 `A`，即诸名字据以写出的那一层，也相对于该层成员上的一个严格良序，故工作在模块 `Naming A w` 之内进行。一个**名字**由三部分组成：一个元数、一条比该元数多一个自由变量槽位的无参公式，以及一个由 `A` 的小成员类型取出、长度等于该元数的参数向量。多出的那个槽位正是用于选出子集的；其余槽位接收诸参数，而第一个键当即从那条公式读出。
<!--ja-->
## 名前を構成するデータ

名前は、アリティ、一つの出力変数を余分にもつパラメータなし論理式、そのアリティのパラメータ列を記録する。その指示対象は、この環境で論理式が段階から切り出す部分集合である。

本章の残りの部分はすべて、一つの集合 `A`、すなわち名前が書かれる段階と、その段階の要素の上の一つの狭義整列順序とに相対的である。そこで作業はモジュール `Naming A w` の中で進む。**名前**とは、アリティ、それより一つ多い自由変数スロットをもつパラメータなし論理式、そして `A` の小さな要素型から取った、その個数のパラメータの列である。余分なスロットが部分集合を切り出すためのものであり、残りのスロットがパラメータを受け取る。第一の鍵は論理式から直ちに読み取れる。
<!--/-->

<!--en-->
The module takes the stage `A` and, crucially, a strict well-order of its members as parameters, since the third key will compare parameters by that order and nothing in this chapter constructs one over an arbitrary stage. The type `Name` is a dependent triple: a natural number `k`, a parameter-free formula with `suc k` free-variable slots, and a vector of `k` members of `A`'s carrier. The vector's length is forced to be the arity, so a name cannot pair a formula with the wrong number of parameters.
<!--zh-->
模块取层 `A`，以及关键的、其成员上的一个严格良序作为参数，因为第三个键将按这个序比较参数，而本章不会在任意层上构造一个序。类型 `Name` 是一个依值三元组：自然数 `k`、有 `suc k` 个自由变量槽位的无参公式、以及由 `k` 个 `A` 载体成员组成的向量。向量长度被强制等于元数，故名字不可能把公式与错误数目的参数配对。
<!--ja-->
モジュールは、段階 `A` と、決定的に重要なことにその要素の上の狭義整列順序とをパラメータとして取る。第三の鍵がパラメータをその順序で比較するのであり、任意の段階の上に順序を作るのはこの章の仕事ではないからである。型 `Name` は依存的な三つ組である。自然数 `k`、`suc k` 個の自由変数スロットをもつパラメータなし論理式、そして `A` の台の `k` 個の要素の列。列の長さはアリティに強制されるので、名前が公式と誤った個数のパラメータを組にすることはない。
<!--/-->

```agda
module Naming (A : S) (w : SWO ⟪ A ⟫) where
  module DA = DefOf A
  open DA using ( _⊨ᵐ_ )

  Name : Type ℓ
  Name = Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) (suc k) × Vec ⟪ A ⟫ k)
```

<!--en-->
The projections name the three keys' sources: `arity` returns the number, `formula` the embedded-free formula of exactly one more variable slot, and `params` the vector. Their types are dependent on the name itself, so `formula a` lives at arity `suc (arity a)` and `params a` at `arity a`; this dependence is the source of every transport question in the comparison to come.
<!--zh-->
诸投影标出三个键的来源：`arity` 返回那个数，`formula` 返回恰好多一个变量槽位的无参公式，`params` 返回那个向量。它们的类型依值于名字自身，故 `formula a` 处在元数 `suc (arity a)` 上，`params a` 处在 `arity a` 上；这份依值正是后文比较中每个传输问题的来源。
<!--ja-->
射たちは三つの鍵の出所に名前を与える。`arity` はその数を返し、`formula` はちょうど一つ多い変数スロットをもつパラメータなし論理式を、`params` は列を返す。それらの型は名前そのものに依存する。だから `formula a` はアリティ `suc (arity a)` に、`params a` は `arity a` に住む。この依存性こそ、のちの比較における輸送の問題すべての出所である。
<!--/-->

```agda

  arity : Name → ℕ
  arity a = a .fst

  formula : (a : Name) → Formula (⊥* {ℓ}) (suc (arity a))
  formula a = a .snd .fst

  params : (a : Name) → Vec ⟪ A ⟫ (arity a)
```

<!--en-->
The first key is a projection as well: `codeOf` applies `limitCode` to the formula, delivering its code in the limit stage together with the membership certificate, ready for `limitOrder` to compare.
<!--zh-->
第一个键同样是一个投影：`codeOf` 对公式施用 `limitCode`，交付它的码连同极限层中的隶属凭证，随时可由 `limitOrder` 比较。
<!--ja-->
第一の鍵もまた射である。`codeOf` は論理式に `limitCode` を適用し、そのコードを極限段階での所属証明書とともに届ける。`limitOrder` が比較できるように。
<!--/-->

```agda
  params a = a .snd .snd

  codeOf : Name → Limit
  codeOf a = limitCode (formula a)
```

<!--en-->
What a name denotes is the subset of `A` its formula selects when the parameters are supplied in the **environment**, in the order expected by parameter abstraction. The environment is one member followed by the parameters, all read into the restricted carrier by the definable powerset's own constant interpretation, and the satisfaction is the inner one, so the denotation is a subset of `A` carved by exactly the notion `Def A`{.Agda} was defined by. Smallness is inherited: the inner satisfaction at any formula and any environment is small, so the subset is a `sett`{.Agda} over a small index type with no resizing spent.
<!--zh-->
一个名字所**指称**的，是当参数由**环境**给出时，它的公式所选中的 `A` 的子集，次序与参数抽象定理一致。环境由一个成员后接诸参数组成，全部经可定义幂集所用的常元解释读入限制载体，而满足关系取内层版本；因此，指称正是由「`Def A`{.Agda} 据以定义的那个概念」选出的 `A` 的子集，与定义完全一致。小性直接继承：任何公式在任何环境处的内层满足皆小，故该子集是小索引类型上的一个 `sett`{.Agda}，降至小索引类型无须额外工作。
<!--ja-->
名前の**指示対象**とは、パラメータが**環境**として与えられたとき、その論理式が選び出す `A` の部分集合です。その並びはパラメータ抽象化定理が要求する順序です。環境は一つの要素とそれに続くパラメータ列からなり、すべて定義可能冪集合自身の定数解釈によって制限された台へ読み込まれ、充足は内側のものを取ります。したがって指示対象は、`Def A`{.Agda} を定義したのと同じ概念によって `A` から切り出された部分集合です。小ささはそのまま引き継がれます。任意の論理式と任意の環境における内側の充足は小さいので、この部分集合は小さな索引型の上の `sett`{.Agda} となり、レベルの引き下げの費用は一切かかりません。
<!--/-->

<!--en-->
A subset of `A` carved by a predicate is presented directly: `subsetOf` takes a family of propositions over `A`'s small member type and builds a `sett` whose index type is the dependent pair of a member `m` and a proof that the predicate holds at `m`, sent to the set `⟪ A ⟫↪ m`. An index is therefore a witness together with its certificate, and membership in the resulting set asks only that such a pair *merely* exists. This is the same shape `defSet` was built in, so predicates phrased in either form present the same kind of object.
<!--zh-->
由一条谓词从 `A` 中刻出的子集可直接呈现：`subsetOf` 接受 `A` 的小成员类型上的一个命题族，构造一个 `sett`，其索引类型是「成员 `m` 连同谓词在 `m` 处成立的证明」的依值和，并把这个对子送到集合 `⟪ A ⟫↪ m`。于是一个索引就是一位见证连同其证书，而所得集合的隶属只断言这样的对子仅仅存在。这与 `defSet` 的构造形状相同，故两种形式写出的谓词呈现的是同一类对象。
<!--ja-->
述語によって `A` から切り出される部分集合は直接提示できます。`subsetOf` は `A` の小さな要素型の上の命題族を受け取り、索引型を「要素 `m` と、その `m` で述語が成り立つ証明」の依存対とし、その対を集合 `⟪ A ⟫↪ m` へ送る `sett` を組み立てます。したがって索引とは証人とその証明書の対であり、結果の集合への所属はそのような対が「だけ」存在することを要求します。これは `defSet` と同じ形なので、どちらの形で書いた述語も同じ種類の対象を提示します。
<!--/-->

```agda
  private
    module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M
    open SemM using ( _^_ )

    subsetOf : (⟪ A ⟫ → hProp ℓ) → S
    subsetOf P = sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ P m ⟩) (λ p → ⟪ A ⟫↪ (p .fst))
```

<!--en-->
Two presentation details matter before the denotation itself. The auxiliary `⟪⟫↪-inj` records that the map `⟪ A ⟫↪` is an embedding, so a path between two of its values comes from a path between the underlying indices; this recovers `m' ≡ m` and will close the forward direction of the membership specification. The environment is then assembled: for a member `m` marking the free variable, it is `DA.ι m` followed by the parameters each decoded by `DA.ι`. The head entry fills the one extra slot that carves the subset, the tail entries fill the parameter slots, and the length of the environment is definitionally `suc (arity a)`, exactly the arity of the name's formula.
<!--zh-->
在指称本身之前，有两个呈现细节要交代。辅助事实 `⟪⟫↪-inj` 记录映射 `⟪ A ⟫↪` 是嵌入，故其两个值之间的路径来自底层索引之间的路径；这将恢复 `m' ≡ m`，并在隶属规格的正向中使用。环境随即拼装而成：对标记自由变量的成员 `m`，环境是 `DA.ι m` 后接逐个经 `DA.ι` 解码的诸参数。头一项填入界定子集的那个额外槽位，其余各项填入参数槽位，且环境的长度按定义就是 `suc (arity a)`，恰为该名字公式的元数。
<!--ja-->
指示対象そのものの前に、提示上の二つの細部を確かめます。補題 `⟪⟫↪-inj` は、写像 `⟪ A ⟫↪` が埋め込みであること、つまりその値の間の経路が根底の添字の間の経路から来ることを記録します。これにより `m' ≡ m` が復元され、所属の仕様の順方向を閉じるのに使われます。環境はその後組み立てられます。自由変数を担う要素 `m` に対し、環境は `DA.ι m` に `DA.ι` で復号したパラメータ列を続けたものです。先頭の項が部分集合を切り出す一つの余分なスロットを埋め、残りの項がパラメータのスロットを埋めます。環境の長さは定義上 `suc (arity a)` であり、名前の論理式のアリティとちょうど一致します。
<!--/-->

```agda

    ⟪⟫↪-inj : {m' m : ⟪ A ⟫} → ⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m → m' ≡ m
    ⟪⟫↪-inj {m'} {m} = isEmbedding→Inj isEmb⟪ A ⟫↪ m' m

  environment : (a : Name) → ⟪ A ⟫ → DA.SM ^ (suc (arity a))
  environment a m = DA.ι m ∷ map DA.ι (params a)

  satAt : (a : Name) → ⟪ A ⟫ → hProp ℓ
```

<!--en-->
The predicate that defines a name's denotation is `satAt a m`, the small proposition equivalent to the inner satisfaction of the embedded formula at the assembled environment. Taking it through `subsetOf` gives `denote a` as a set of the hierarchy, a subset of `A` selected by exactly the inner semantics. No new sizing decision is made anywhere: smallness enters once through `⊨ᵐ-small` and is spent on the `sett`'s index type.
<!--zh-->
定义一个名字指称的谓词是 `satAt a m`：内层语义在该拼装环境中满足嵌入后公式这一陈述的等价小命题。经 `subsetOf` 之后，`denote a` 就是层级中的一个集合，恰由内层语义从 `A` 中选出的子集。这里没有再作任何尺寸上的决定：小性经 `⊨ᵐ-small` 一次进入，全部花费在 `sett` 的索引类型上。
<!--ja-->
名前の指示対象を定める述語は `satAt a m` です。これは、埋め込まれた論理式が組み立てた環境で内側の充足を受けるという命題と同値な小さな命題です。これを `subsetOf` に通すと、`denote a` は階層の集合となり、内側の意味論が `A` から選んだ部分集合になります。ここで新たなサイズの決定は一切行われません。小ささは `⊨ᵐ-small` を通じて一度だけ入り、`sett` の索引型に費やされるのです。
<!--/-->

```agda
  satAt a m = DA.⊨ᵐ-small (embed (formula a)) (environment a m) .fst

  denote : Name → S
  denote a = subsetOf (satAt a)
```

<!--en-->
The specification says the word "denotes" literally: a member of `A` belongs to the denotation exactly when the inner world satisfies the name's formula at the environment the name prescribes. The compression to a small proposition was only an encoding, and the equivalence carries it back.
<!--zh-->
下面把「指称」的规格逐字写出：`A` 的一个成员属于该指称，当且仅当内层世界在该名字所规定的环境处满足它的公式。压缩成小命题只是编码上的安排，而那个等价把它原样送回。
<!--ja-->
この仕様は「指示する」という語を文字どおりに述べます。`A` の要素がその指示対象に属するのは、内側の世界が名前の定める環境でその論理式を充足するとき、そしてそのときに限ります。小さな命題への圧縮は符号化にすぎず、同値がそれを元に戻します。
<!--/-->

<!--en-->
The theorem is a path of propositions, matching the form in which `defSet-mem` was stated, and it is proved by `⇔toPath` from two implications. The auxiliary `decode` re-expands `satAt a m` into the full pair that `⊨ᵐ-small` returns, so that both directions can use the equivalence in its second component, the one connecting the small proposition to the inner satisfaction statement.
<!--zh-->
该定理是命题之间的路径，与 `defSet-mem` 的陈述形式一致，并由两个蕴含经 `⇔toPath` 证明。辅助定义 `decode` 把 `satAt a m` 重新展开成 `⊨ᵐ-small` 返回的完整对子，于是两个方向都能使用其第二分量中的等价，即连接小命题与内层满足陈述的那一个。
<!--ja-->
この定理は命題としての経路であり、`defSet-mem` が述べられたのと同じ形をしています。二つの含意から `⇔toPath` によって証明されます。補助定義 `decode` は `satAt a m` を `⊨ᵐ-small` が返す完全な対へ展開し直し、両方向がその第二成分の同値、つまり小さな命題と内側の充足の命題を結ぶ同値を使えるようにします。
<!--/-->

```agda
  denote-mem : (a : Name) (m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ denote a) ≡ (environment a m ⊨ᵐ embed (formula a))
  denote-mem a m = ⇔toPath fwd bwd
    where
    decode = DA.⊨ᵐ-small (embed (formula a)) (environment a m)
```

<!--en-->
Membership in a `sett` only *merely* supplies its index, so the forward direction eliminates a truncation into a proposition and obtains an index `(m' , h)` together with a path `q` from `⟪ A ⟫↪ m'` to `⟪ A ⟫↪ m`. Embedding injectivity turns `q` into `m' ≡ m`, transporting `h` along it yields a proof of `satAt a m`, and the equivalence of `decode` converts that proof into the satisfaction statement. Every step spends a proof where only a proposition is wanted, so no witness is chosen.
<!--zh-->
`sett` 的隶属只给出索引的截断存在，故正向把截断消入一个命题，得到索引 `(m' , h)` 连同从 `⟪ A ⟫↪ m'` 到 `⟪ A ⟫↪ m` 的路径 `q`。嵌入的单射性把 `q` 变为 `m' ≡ m`，沿它搬运 `h` 得到 `satAt a m` 的证明，`decode` 的等价再把这个证明转换为满足陈述。每一步都只在需要命题之处花费证明，因此没有选取任何见证。
<!--ja-->
`sett` への所属は添字の存在を切り捨てた形で与えるので、順方向は切断を命題へ消去し、索引 `(m' , h)` と `⟪ A ⟫↪ m'` から `⟪ A ⟫↪ m` への経路 `q` を得ます。埋め込みの単射性が `q` を `m' ≡ m` に変え、それに沿って `h` を輸送すれば `satAt a m` の証明が得られ、`decode` の同値がその証明を充足の命題へ変換します。各段階は命題しか要らない場所で証明を費やすだけで、証人が選ばれることはありません。
<!--/-->

```agda
    fwd : ⟨ ⟪ A ⟫↪ m ∈ˢ denote a ⟩ → ⟨ environment a m ⊨ᵐ embed (formula a) ⟩
    fwd = PT.rec (snd (environment a m ⊨ᵐ embed (formula a)))
      (λ { ((m' , h) , q) →
        invEq (decode .snd) (subst (λ v → ⟨ satAt a v ⟩) (⟪⟫↪-inj q) h) })
    bwd : ⟨ environment a m ⊨ᵐ embed (formula a) ⟩ → ⟨ ⟪ A ⟫↪ m ∈ˢ denote a ⟩
```

<!--en-->
The reverse direction runs the same equivalence the other way: a satisfaction proof becomes a proof of `satAt a m`, taken as the index `(m , proof)` with the trivial path, and truncated with `∣_∣₁`. Together the two directions identify membership with inner satisfaction without remainder, which is what the word "denotes" was required to mean.
<!--zh-->
反向把同一等价反向使用：一个满足的证明经等价变成 `satAt a m` 的证明，取作带平凡路径的索引 `(m , 证明)`，再以 `∣_∣₁` 截断。两个方向合起来把隶属与内层满足毫无剩余地等同起来，这正是「指称」一词被要求表达的含义。
<!--ja-->
逆方向は同じ同値を逆向きに走らせます。充足の証明が `satAt a m` の証明に変わり、それを自明な経路とともに索引 `(m , 証明)` として `∣_∣₁` で切断します。両方向を合わせると、所属と内側の充足は余りなく同一視され、これが「指示する」という語に求められた意味です。
<!--/-->

```agda
    bwd h = ∣ (m , equivFun (decode .snd) h) , refl ∣₁
```

<!--en-->
## Every member of the successor stage has a name

The definable-power-set specification supplies a formula with constants for each successor-stage member. Abstracting those constants produces the parameter-free formula and parameter vector that form its name.

A member of `𝒟ₒ A`{.Agda} is, by that operator's own specification, merely a subset definable by a formula of one free variable with constants from `A`; and parameter abstraction turns such a formula into a parameter-free one of higher arity together with its list of occurring constants. Reading the second off the first is the whole of naming, and it is a function.
<!--zh-->
## 后继层的每个成员都有名字

可定义幂集的规格为后继层的每个成员给出一条带常元的公式。把这些常元抽象出去，就得到构成其名字的无参公式与参数向量。

按那个算子自己的规格，`𝒟ₒ A`{.Agda} 的成员仅仅是「由带 `A` 中常元的单变量公式可定义的子集」；参数抽象把这样一条公式变成元数更高的无参公式，并给出其中出现的常元列表。从前者读出后者，就是命名的全部，而且它是一个函数。
<!--ja-->
## 後者段階の各要素は名前をもつ

定義可能冪集合の仕様は、後続段階の各要素に定数付き論理式を与える。その定数を抽象すると、名前を構成するパラメータなし論理式とパラメータ列が得られる。

`𝒟ₒ A`{.Agda} の要素は、その演算子自身の仕様によれば、`A` の定数を用いた一自由変数の論理式で定義される部分集合にすぎません。パラメータ抽象化は、その論理式をより高いアリティのパラメータなし論理式へ変換し、そこに現れる定数の列を与えます。後者を前者から読み出すこと、それが名付けのすべてであり、しかもそれは関数です。
<!--/-->

<!--en-->
The function `nameOf` assembles the three keys at once. `countFo φ` counts each constant occurrence, giving the arity, so the abstraction `absFo φ` lives at `1 + countFo φ` free slots, which is `suc` of the arity; `constantsFo φ` lists the constants in the same order, a vector of exactly that length in `⟪ A ⟫`. Note that `nameOf` takes a formula with constants, not yet a name's parameter-free component: the abstraction happens inside the definition, one clause per constructor.
<!--zh-->
函数 `nameOf` 一举拼装三个键。`countFo φ` 逐次计数每个常元出现，给出元数，于是抽象 `absFo φ` 落在 `1 + countFo φ` 个自由槽位上，恰为元数的后继；`constantsFo φ` 按同一顺序列出诸常元，是 `⟪ A ⟫` 中长度恰合的向量。注意 `nameOf` 接受的是带常元的公式，而非名字的无参分量：抽象发生在定义内部，每个构造子一条子句。
<!--ja-->
関数 `nameOf` は三つの鍵を一度に組み立てます。`countFo φ` は定数の出現を一つずつ数えてアリティを与え、したがって抽象 `absFo φ` は `1 + countFo φ` 個の自由スロット、つまりアリティの後続数のところに住みます。`constantsFo φ` は同じ順序で定数を並べ、`⟪ A ⟫` の中のちょうどその長さの列です。`nameOf` が受け取るのは定数付きの論理式であって、名前のパラメータなし成分ではないことに注意してください。抽象化は定義の内部で、構成子ごとに一つの節として行われます。
<!--/-->

```agda
  nameOf : Formula ⟪ A ⟫ 1 → Name
  nameOf φ = countFo φ , (absFo φ , constantsFo φ)
```

<!--en-->
Adequacy follows from the parameter-abstraction theorem `⊨-abs₁`, after identifying the two interpretations of the empty constant domain. Two readings of a parameter-free formula are in play and they have to be identified first: the name's denotation reads it inside the constant domain `⟪ A ⟫`{.Agda}, through `embed`{.Agda}, while the abstraction theorem reads it at the empty constant domain. The two interpretations are functions out of the empty type, so they agree, and stating this agreement is the only verification the identification requires.
<!--zh-->
其充分性来自参数抽象定理 `⊨-abs₁`，使用前须先认同空常元域的两种解释。这里有两种读一条无参公式的方式，必须先把二者认同：名字的指称经 `embed`{.Agda} 在常元域 `⟪ A ⟫`{.Agda} 之内读它，而抽象定理在空常元域处读它。两个解释都是从空类型出发的函数，故它们相符；把这个相符说出来，便是这次认同所需的全部验证。
<!--ja-->
その妥当性はパラメータ抽象化定理 `⊨-abs₁` から従い、その前に空の定数領域に対する二つの解釈を同一視します。パラメータなし論理式には二つの読み方が現れるので、まず両者を同一視しなければなりません。名前の指示対象は `embed`{.Agda} を通して定数域 `⟪ A ⟫`{.Agda} の中で式を読み、一方抽象化の定理は空の定数域で読みます。二つの解釈は空型から出る関数なので一致し、この一致を述べることが同一視に必要な検証のすべてです。
<!--/-->

<!--en-->
The abstraction theorem `⊨-abs₁` speaks of satisfaction over the empty constant domain, while the name's semantics reads over `⟪ A ⟫`. To compare the two statements term by term, `emptySat` fixes the shape of a satisfaction statement at an arbitrary constant interpretation `f : ⊥* → DA.SM`, so that changing `f` is a matter of applying a function to a function. The formula itself never mentions a constant, which is what makes this uniformity available.
<!--zh-->
抽象定理 `⊨-abs₁` 谈的是空常元域上的满足，而名字的语义读的是 `⟪ A ⟫` 上的满足。要逐项比较两个陈述，`emptySat` 把「在任意常元解释 `f : ⊥* → DA.SM` 处的满足陈述」固定为一个形状，使改动 `f` 成为把一个函数应用于函数的事。公式本身从不提及常元，正是这一点使这种一致性可用。
<!--ja-->
抽象化の定理 `⊨-abs₁` は空の定数域の上での充足を語り、一方名前の意味論は `⟪ A ⟫` の上の充足を読みます。二つの命題を項ごとに比べるため、`emptySat` は任意の定数解釈 `f : ⊥* → DA.SM` における充足の命題の形を固定し、`f` の変更を関数の関数への適用の問題にします。論理式そのものは定数を一切言及しないので、この一様性が使えるのです。
<!--/-->

```agda
  private
    emptySat : (f : ⊥* {ℓ} → DA.SM) {n : ℕ}
             → DA.SM ^ n → Formula (⊥* {ℓ}) n → Ω
    emptySat f γ χ = γ ⊨ᶠ χ
      where open SemM.At (⊥* {ℓ}) f using () renaming ( _⊨_ to _⊨ᶠ_ )
```

<!--en-->
Two constant interpretations of a parameter-free formula both have type `⊥* → DA.SM`: the one the working semantics uses, sending every constant to `DA.ι (Empty.rec* b)`, and the eliminator `Empty.rec*` itself. Since `⊥*` has no elements, `funExt` plus the eliminator proves the two functions equal as `sameReading`, without inspecting anything. The statement `absSat` then compares the environment reading used by the denotation, through `embed`, with the empty-domain reading used by the abstraction theorem, at the same member `m` and the same abstracted formula.
<!--zh-->
无参公式的两个常元解释都有类型 `⊥* → DA.SM`：工作语义所用的那个，把每个常元送到 `DA.ι (Empty.rec* b)`；以及消去子 `Empty.rec*` 本身。由于 `⊥*` 没有元素，`funExt` 加上消去子便证得这两个函数相等，即 `sameReading`，无须检视任何东西。随后，`absSat` 陈述的是：指称所用的、经 `embed` 的环境读法，与抽象定理所用的空域读法，在同一个成员 `m` 与同一条抽象公式处相符。
<!--ja-->
パラメータなし論理式の二つの定数解釈は、どちらも型 `⊥* → DA.SM` をもちます。作業用の意味論が使う方、すべての定数を `DA.ι (Empty.rec* b)` へ送るものと、消去子 `Empty.rec*` 自身です。`⊥*` には要素がないので、`funExt` と消去子だけで二つの関数の相等 `sameReading` が証明され、何も検査する必要がありません。そして `absSat` は、指示対象が `embed` を通して使う環境の読み方と、抽象化の定理が使う空定数域の読み方が、同じ要素 `m` と同じ抽象化された論理式において一致することを述べます。
<!--/-->

```agda

    sameReading : (λ (b : ⊥* {ℓ}) → DA.ι (Empty.rec* b)) ≡ Empty.rec*
    sameReading = funExt (λ b → Empty.rec* b)

    absSat : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
           → (environment (nameOf φ) m ⊨ᵐ embed (formula (nameOf φ)))
           ≡ ((DA.ι m ∷ []) ⊨ᵐ φ)
```

<!--en-->
The proof is a three-step path. The relabelling lemma `embed-⊨` says that embedding a parameter-free formula into a richer constant domain does not change what it says, which moves the left side to the `Empty.rec*`-marked reading; `sameReading` then substitutes the denotation's own reading for that one; and `⊨-abs₁`, read backwards, is exactly the abstraction theorem's identification of the abstracted formula's satisfaction with the original one at the single parameter. Each step is a theorem from an earlier chapter, connected rather than re-derived.
<!--zh-->
证明是一条三步的路径。改名引理 `embed-⊨` 说把无参公式嵌入更丰富的常元域不改变它所说的话，这一步把左边搬到带 `Empty.rec*` 标记的读法；`sameReading` 再把指称自己的读法代入其中；最后反着读 `⊨-abs₁`，恰好就是抽象定理对「抽象后的公式在单个参数处的满足」与「原公式的满足」的认同。每一步都是此前某章的定理，只作连接，不作重证。
<!--ja-->
証明は三段の経路です。改名の補題 `embed-⊨` は、パラメータなし論理式をより豊かな定数域へ埋め込んでもその意味は変わらないと言い、これが左辺を `Empty.rec*` の標識の読み方へ移します。次に `sameReading` が指示対象自身の読み方をそこへ代入します。最後に `⊨-abs₁` を逆向きに読むと、抽象化された論理式の単一パラメータにおける充足と元の論理式の充足とを同一視する抽象化の定理そのものです。各段階は前の章の定理をつなぐだけで、再証明はしません。
<!--/-->

```agda
    absSat φ m =
        embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι (absFo φ)
          (environment (nameOf φ) m)
      ∙ cong (λ f → emptySat f (environment (nameOf φ) m) (absFo φ)) sameReading
      ∙ sym (⊨-abs₁ (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι φ (DA.ι m))
```

<!--en-->
With the two readings identified as propositions, `satAt-abs` lifts the identification from satisfaction statements to the small propositions the sets are built from. It compares `satAt (nameOf φ) m`, the small proposition behind the name's denotation, with `DA.smallSat φ m`, the small proposition behind `defSet φ`. The two auxiliary names `big` and `small` unpack the corresponding `⊨ᵐ-small` pairs, so each direction can use both of the packaged equivalences.
<!--zh-->
把两种读法在命题层面认同之后，`satAt-abs` 把这一认同从满足陈述提升到集合据以构造的小命题上。它比较 `satAt (nameOf φ) m`，即名字指称背后的小命题，与 `DA.smallSat φ m`，即 `defSet φ` 背后的小命题。两个辅助名 `big` 与 `small` 展开各自的 `⊨ᵐ-small` 对子，使每个方向都能使用两份打包好的等价。
<!--ja-->
二つの読み方を命題の面で同一視したうえで、`satAt-abs` はこの同一視を充足の命題から、集合が構成される小さな命題へ引き上げます。比較するのは、名前の指示対象の根底にある小さな命題 `satAt (nameOf φ) m` と、`defSet φ` の根底にある小さな命題 `DA.smallSat φ m` です。補助名 `big` と `small` がそれぞれの `⊨ᵐ-small` の対を展開し、どちらの方向も二つの同値を使えるようにします。
<!--/-->

```agda

    satAt-abs : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
              → satAt (nameOf φ) m ≡ DA.smallSat φ m
    satAt-abs φ m = ⇔toPath fwd bwd
      where
      big = DA.⊨ᵐ-small (embed (formula (nameOf φ))) (environment (nameOf φ) m)
```

<!--en-->
The forward direction composes three conversions, all applied to proofs: run the big equivalence backwards to reach the embedded satisfaction statement, transport the proof along the path `absSat φ m` to the empty-domain statement, then run the small equivalence forwards to reach `DA.smallSat φ m`. The path `absSat φ m` identifies the two satisfaction types, so ordinary transport moves a proof in the required direction. Their propositionhood is used to package each satisfaction type as an `hProp`; transport itself only requires the path.
<!--zh-->
正向把三次转换复合，全部施加于证明：先把大的等价反向运行，抵达嵌入后的满足陈述；沿路径 `absSat φ m` 把证明搬运到空域陈述；再把小的等价正向运行，抵达 `DA.smallSat φ m`。路径 `absSat φ m` 认同了两个满足类型，普通的传输便可沿所需方向移动证明。命题性用于把满足类型打包成 `hProp`；传输本身只需要这条路径。
<!--ja-->
順方向は三つの変換を証明に施して合成します。まず大きい方の同値を逆向きに走らせて埋め込まれた充足の命題に達し、経路 `absSat φ m` に沿って証明を空定数域の命題へ輸送し、それから小さい方の同値を順方向に走らせて `DA.smallSat φ m` に達します。経路 `absSat φ m` が二つの充足型を同一視するので、通常の輸送によって証明を必要な向きへ移せます。命題性は充足型を `hProp` としてまとめるために使われ、輸送そのものが必要とするのはこの経路です。
<!--/-->

```agda
      small = DA.⊨ᵐ-small φ (DA.ι m ∷ [])
      fwd : ⟨ satAt (nameOf φ) m ⟩ → ⟨ DA.smallSat φ m ⟩
      fwd h = equivFun (small .snd) (subst ⟨_⟩ (absSat φ m) (invEq (big .snd) h))
      bwd : ⟨ DA.smallSat φ m ⟩ → ⟨ satAt (nameOf φ) m ⟩
      bwd h = equivFun (big .snd)
```

<!--en-->
The backward direction is the same composition with the path reversed: `sym (absSat φ m)` moves proofs the other way, and the two equivalences are applied in the opposite order. Nothing new is proved here; the point is that `satAt (nameOf φ) m` and `DA.smallSat φ m` are the same small proposition for every `m`, which is what makes the two sets equal in the next step.
<!--zh-->
反向是同一复合、路径取反：`sym (absSat φ m)` 把证明向另一方向搬运，两个等价也以相反次序应用。这里没有证明任何新东西；要点在于，对每个 `m`，`satAt (nameOf φ) m` 与 `DA.smallSat φ m` 是同一个小命题，这正是下一步两个集合得以相等的原因。
<!--ja-->
逆方向は同じ合成で経路を逆向きにしたものです。`sym (absSat φ m)` が証明を逆方向へ動かし、二つの同値も逆の順序で適用されます。ここで新たに証明されるものはありません。要点は、すべての `m` に対して `satAt (nameOf φ) m` と `DA.smallSat φ m` が同じ小さな命題であることであり、これが次の段階で二つの集合を等しくするのです。
<!--/-->

```agda
        (subst ⟨_⟩ (sym (absSat φ m)) (invEq (small .snd) h))
```

<!--en-->
Both subsets are cut out of `A` by a small predicate on its members, so once the two predicates are equal the two sets are equal by a congruence, with no appeal to extensionality. Completeness follows by transporting along that equality, and it is stated truncated because that is how the definable powerset yields a formula in the first place.
<!--zh-->
两个子集都是由 `A` 的成员上的一条小谓词从 `A` 中选出的，故两条谓词一旦相等，两个集合便由一次同余而相等，无须援引外延性。完备性沿那条等式即可得到，而它陈述为截断形式，因为可定义幂集本来就是这样给出一条公式的。
<!--ja-->
どちらの部分集合も、その要素の上の小さな述語によって `A` から切り出されています。したがって二つの述語が等しければ、二つの集合は合同によって等しく、外延性を持ち出す必要はありません。完全性はその等式に沿って輸送すれば得られ、命題的に切り詰めた形で述べられます。定義可能冪集合が論理式を与える仕方がもともとそうだからです。
<!--/-->

<!--en-->
The equality `denote-defSet` is the predicate agreement `satAt-abs` made into an equality of sets: `funExt` gathers the pointwise equalities into an equality of predicate families, and `cong subsetOf` carries it to the presented sets. Completeness then takes the certificate `h : ⟨ x ∈ˢ 𝒟ₒ A ⟩` and inverts it with `𝒟ₒ-inv`, which merely supplies a formula `φ` with `defSet φ ≡ x`; the conclusion is correspondingly a truncated existence of a name and an equality, not a chosen name.
<!--zh-->
等式 `denote-defSet` 把谓词的相符 `satAt-abs` 变成集合的相等：`funExt` 把逐点相等聚成谓词族的相等，`cong subsetOf` 再把它带到所呈现的集合上。完备性于是取证书 `h : ⟨ x ∈ˢ 𝒟ₒ A ⟩`，用 `𝒟ₒ-inv` 反演，它仅仅给出一条满足 `defSet φ ≡ x` 的公式 `φ`；相应地，结论也是「存在一个名字与一个等式」的截断形式，而非被选定的名字。
<!--ja-->
等式 `denote-defSet` は、述語の一致 `satAt-abs` を集合の等式に変えたものです。`funExt` が点ごとの等しさを述語族の等しさにまとめ、`cong subsetOf` がそれを提示された集合へ運びます。完全性は証明書 `h : ⟨ x ∈ˢ 𝒟ₒ A ⟩` を `𝒟ₒ-inv` で反転することから始まります。これは `defSet φ ≡ x` を満たす論理式 `φ` を「だけ」与えるものであり、したがって結論も名前と等式の存在を切り詰めた形であり、選ばれた名前ではありません。
<!--/-->

```agda
  denote-defSet : (φ : Formula ⟪ A ⟫ 1) → denote (nameOf φ) ≡ DA.defSet φ
  denote-defSet φ = cong subsetOf (funExt (satAt-abs φ))

  names-complete : (x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
                 → ∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁
  names-complete x h = PT.map named (𝒟ₒ-inv A x h)
```

<!--en-->
Inside the truncation, the step from the inverted data to the desired pair is ordinary: the formula `φ` is named by `nameOf φ`, and the required equality is `denote-defSet φ ∙ q`, the path from the name's denotation to `defSet φ` followed by the given path to `x`. Since the target `∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁` is a proposition, `PT.map` may work under the truncation, mapping the merely supplied formula to a merely supplied name without ever inspecting which one it is.
<!--zh-->
在截断之内，从反演数据到目标对的步骤是平凡的：公式 `φ` 由 `nameOf φ` 命名，所需的等式是 `denote-defSet φ ∙ q`，即从名字的指称到 `defSet φ` 的路径再接上给定的到 `x` 的路径。由于目标 `∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁` 是命题，`PT.map` 可以在截断之下工作，把仅仅给出的公式映为仅仅给出的名字，而无须检视它究竟是哪一条。
<!--ja-->
切断の内側では、反転されたデータから求める対への段階は普通のものです。論理式 `φ` は `nameOf φ` によって名付けられ、必要な等式は `denote-defSet φ ∙ q`、つまり名前の指示対象から `defSet φ` への経路に、与えられた `x` への経路を続けたものです。目標の `∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁` は命題なので、`PT.map` は切断の下で働き、ただ与えられた論理式をただ与えられた名前へ写します。それがどの論理式かを検査することは一切ありません。
<!--/-->

```agda
    where
    named : Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DA.defSet φ ≡ x)
          → Σ[ a ∈ Name ] (denote a ≡ x)
    named (φ , q) = nameOf φ , (denote-defSet φ ∙ q)
```

<!--en-->
## The order on the parameter vectors

Parameter vectors are compared lexicographically by the given well-order on members of `A`. The relation accepts two possibly different lengths: an exhausted vector has no predecessor in either mixed-length case, while two nonempty vectors compare their heads and continue to their tails only when the heads agree. This formulation makes transitivity available for three vectors at their actual lengths. Trichotomy is later invoked only after an arity path transports one vector to the other length.
<!--zh-->
## 参数向量上的序

参数向量按 `A` 的成员上的既定良序作字典序比较。该关系接受两个可能不同的长度：任一向量先耗尽的混合长度情形都没有前驱；两个非空向量先比较首项，只有首项相等时才继续比较尾部。这样，传递性可以直接用于三个向量各自的实际长度；三歧性则要等元数路径把一个向量传到另一长度后才使用。
<!--ja-->
## パラメータ列上の順序

パラメータ列は `A` の要素に与えられた整列順序によって辞書式に比較します。この関係は異なる二つの長さを受け取り、一方が先に尽きる場合には先行元を持たず、両方が空でなければ先頭を比較し、先頭が等しいときだけ尾へ進みます。この形により、三つの列の実際の長さのまま推移性を使えます。三分性は後で、アリティの経路に沿って一方を他方の長さへ輸送してから適用します。
<!--/-->

<!--en-->
Two well-orders are in play and both are fixed once with short names. The limit-stage order `limitOrder` compares formula codes and becomes `_≺_`; the module parameter `w`, the well-order of `A`'s members, compares parameters and becomes `_≺ₚ_`. Each opening also renames the trichotomy, irreflexivity, transitivity and well-foundedness laws, so the proofs to come can invoke either order's laws without long qualified names.
<!--zh-->
这里有两个良序在起作用，且都以短名一次性固定。极限层的序 `limitOrder` 比较公式码，改记为 `_≺_`；模块参数 `w`，即 `A` 的成员上的良序，比较参数，改记为 `_≺ₚ_`。每次开启同时改名了三歧、非自反、传递与良基四条定律，故后文的证明调用任一序的定律时不必写长长的限定名。
<!--ja-->
ここでは二つの整列順序が働いており、どちらも短い名前で一度に固定されます。極限段階の順序 `limitOrder` は論理式コードを比較し、`_≺_` と改名されます。モジュールパラメータ `w`、つまり `A` の要素の上の整列順序はパラメータを比較し、`_≺ₚ_` と改名されます。各 open は三分性・非反射性・推移性・整礎性の法則も改名するので、これからの証明はどちらの順序の法則も長い修飾名なしに呼び出せます。
<!--/-->

```agda
  open SWO limitOrder using () renaming
    ( _<∙_ to _≺_ ; tri∙ to ≺-tri ; irr∙ to ≺-irr
    ; trans∙ to ≺-trans ; wf∙ to ≺-wf )
  open SWO w using () renaming
    ( _<∙_ to _≺ₚ_ ; tri∙ to ≺ₚ-tri ; irr∙ to ≺ₚ-irr
```

<!--en-->
The comparison itself is defined by pattern matching on both vectors, indexed by their lengths `j` and `k`. Whenever either vector is empty, no descent is possible, and the result type is the empty type: there is nothing below an exhausted vector at any position. These cases cost nothing, and the fact that they are refutable is what the transitivity and irreflexivity proofs will consume.
<!--zh-->
比较本身按两个向量的模式匹配定义，向量各带长度索引 `j` 与 `k`。只要有一个向量为空，就不可能再下降，结果类型是空类型：走完的向量在任何位置都无物可低于它。这些情形毫无代价，而它们可反驳这一事实，正是传递性与非自反性的证明所要消耗的。
<!--ja-->
比較そのものは両ベクトルのパターン照合で定義され、長さ `j` と `k` で添字づけられます。どちらかの列が空なら、それ以上の降下は不可能で、結果の型は空型になります。使い尽くされた列の下にはどの位置にも何もないのです。これらの場合は費用がゼロで、反証できるという事実こそ、推移性と非反射性の証明で使われるものです。
<!--/-->

```agda
    ; trans∙ to ≺ₚ-trans ; wf∙ to ≺ₚ-wf )

  infix 20 _≺ᵥ_
  _≺ᵥ_ : ∀ {j k} → Vec ⟪ A ⟫ j → Vec ⟪ A ⟫ k → Type (ℓ-suc ℓ)
  []      ≺ᵥ []      = ⊥*
  []      ≺ᵥ (y ∷ q) = ⊥*
```

<!--en-->
Two nonempty vectors are compared at their heads: either the head `x` drops below `y` in the parameter order, or the heads are equal as a path and the descent continues into the tails. The strict case is a left summand and the equal-head case a right one, so later proofs can branch on which position first decided. Note that the head equality is a path `x ≡ y`, which the mixed transitivity cases will substitute into comparisons.
<!--zh-->
两个非空向量在头部比较：要么头部 `x` 按参数序低于 `y`，要么两条头部经一个路径相等而下降继续进入尾部。严格情形是和的左支，等头情形是右支，故后文的证明可以按「首次判定发生在哪个位置」来分支。注意头部的相等是路径 `x ≡ y`，混合的传递情形将把它代入比较之中。
<!--ja-->
二つの空でない列は先頭で比較されます。先頭 `x` がパラメータ順序で `y` より下に落ちるか、先頭同士が経路として等しく、降下が尾へ続くかのどちらかです。狭義の場合が和の左の支、等しい先頭の場合が右の支なので、後の証明はどの位置が先に判定したかで場合分けできます。先頭の相等は経路 `x ≡ y` であり、推移性の混在する場合はこれを比較の中へ代入することになります。
<!--/-->

```agda
  (x ∷ p) ≺ᵥ []      = ⊥*
  (x ∷ p) ≺ᵥ (y ∷ q) = (x ≺ₚ y) ⊎ ((x ≡ y) × (p ≺ᵥ q))
```

<!--en-->
Three of the four laws are immediate inductions. Irreflexivity and trichotomy ask for equal lengths, since only there is a vector equal to another at all; transitivity does not, and gets three vectors of three lengths, with every case but the all-inhabited one refuted by the empty type.
<!--zh-->
四条定律里有三条是当即的归纳。非自反与三歧要求长度相等，因为只有在那里，一个向量才谈得上与另一个相等；传递性则不要求，它拿到三个长度各异的向量，而除「三者皆非空」之外的每个情形都由空类型反驳。
<!--ja-->
四つの法則のうち三つはそのままの帰納法で得られます。非反射性と三分性は長さが等しいことを要求します。列がある列と等しくなりうるのはそこでだけだからです。推移性はそれを要求せず、三つの異なる長さの列を受け取り、すべての列が空でない場合を除くすべての場合が空型によって反証されます。
<!--/-->

<!--en-->
Irreflexivity is proved by induction on the vector: a vector can never be below itself. The statement makes sense only at a single length, since `p ≺ᵥ p` requires the two occurrences to have the same length, and the induction consumes the statement at the tail, one length down. The transitivity statement follows, stated for three lengths at once.
<!--zh-->
非自反性对向量作归纳证明：一个向量永不可能低于它自己。该陈述只在单一长度处有意义，因为 `p ≺ᵥ p` 要求两次出现的长度相同，而归纳沿尾部消耗短一格处的陈述。接着是传递性的陈述，它同时对三个长度陈述。
<!--ja-->
非反射性はベクトルに関する帰納法で証明されます。ベクトルが自分自身より下になることは決してありません。`p ≺ᵥ p` は二つの出現が同じ長さをもつことを要求するので、この命題は単一の長さでのみ意味をもち、帰納法は一段短い長さでの命題を尾に対して消費します。続いて推移性の命題が続きます。こちらは三つの長さに対して一度に述べられます。
<!--/-->

```agda
  ≺ᵥ-irr : ∀ {k} (p : Vec ⟪ A ⟫ k) → p ≺ᵥ p → Empty.⊥
  ≺ᵥ-irr []      h             = Empty.rec* h
  ≺ᵥ-irr (x ∷ p) (inl h)       = ≺ₚ-irr x h
  ≺ᵥ-irr (x ∷ p) (inr (_ , h)) = ≺ᵥ-irr p h

  ≺ᵥ-trans : ∀ {i j k} (p : Vec ⟪ A ⟫ i) (q : Vec ⟪ A ⟫ j) (r : Vec ⟪ A ⟫ k)
```

<!--en-->
Transitivity is proved by simultaneous case analysis on the three vectors. If the first descent starts at an exhausted vector, its comparison type is already the empty type, and the same holds when the middle vector is exhausted; if the third is exhausted, the second comparison is refutable. In every such case the proof is the empty type's eliminator, with no mathematical content of its own.
<!--zh-->
传递性对三个向量同时作情形分析。若第一次下降始于走完的向量，其比较类型已是空类型；中间向量走完时同理；第三个向量走完时，第二个比较可反驳。每种情形的证明都是空类型的消去子，自身不携带任何数学内容。
<!--ja-->
推移性は三つのベクトルに対する同時の場合分けで証明されます。最初の降下が使い尽くされた列から始まるなら、その比較の型はすでに空型であり、中間の列が使い尽くされた場合も同様です。三番目の列が使い尽くされた場合は、二番目の比較が反証可能です。そのようなすべての場合において証明は空型の消去子であり、それ自体の数学的内容はありません。
<!--/-->

```agda
           → p ≺ᵥ q → q ≺ᵥ r → p ≺ᵥ r
  ≺ᵥ-trans []      []      r       h k = Empty.rec* h
  ≺ᵥ-trans []      (y ∷ q) r       h k = Empty.rec* h
  ≺ᵥ-trans (x ∷ p) []      r       h k = Empty.rec* h
  ≺ᵥ-trans (x ∷ p) (y ∷ q) []      h k = Empty.rec* k
```

<!--en-->
When all three vectors are inhabited, the comparison reads off the heads, and the first two mixed cases are the interesting ones. If `x` is below `y` while `y` equals `z`, substituting the path into the first comparison yields `x` below `z`; and symmetrically, an equality `x ≡ y` followed by `y` below `z` transports the second comparison backwards along the path. Both are instances of the same move: a path of elements acts on comparisons by transport.
<!--zh-->
当三个向量都非空时，比较从头部读出，而前两个混合情形是有趣的。若 `x` 低于 `y` 而 `y` 与 `z` 相等，把该路径代入第一个比较即得 `x` 低于 `z`；对称地，先有 `x ≡ y` 再有 `y` 低于 `z`，则沿该路径把第二个比较反方向搬运。二者是同一动作的实例：元素的路径通过搬运作用于比较。
<!--ja-->
三つの列がすべて空でないとき、比較は先頭から読み取れ、最初の二つの混在する場合が興味の対象です。`x` が `y` より下で `y` が `z` と等しいなら、その経路を最初の比較に代入して `x` が `z` より下であることが得られます。対称的に、`x ≡ y` の後に `y` が `z` より下が続くなら、二番目の比較を経路に沿って逆向きに輸送します。どちらも同じ動きの実例です。要素の経路は輸送によって比較に作用するのです。
<!--/-->

```agda
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inl h) (inl k) = inl (≺ₚ-trans x y z h k)
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inl h) (inr (e , k)) =
    inl (subst (λ v → x ≺ₚ v) e h)
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inr (e , h)) (inl k) =
    inl (subst (λ v → v ≺ₚ z) (sym e) k)
```

<!--en-->
The last transitivity case keeps both heads where they are: the two paths concatenate into `x ≡ z` and the recursion descends into the tails, at whatever three lengths they carry. With transitivity done, trichotomy is stated for two vectors of one length, since only there can the two names coincide at all; the empty vectors are equal by `refl`.
<!--zh-->
传递性的最后一个情形让两个头部原地不动：两条路径拼接成 `x ≡ z`，递归下降进入尾部，长度随它们各自所带。传递性完成后，三歧性对同一长度的两个向量陈述，因为只有在那里两个向量才谈得上重合；空向量经 `refl` 相等。
<!--ja-->
推移性の最後の場合は両方の先頭をそのままにします。二つの経路は `x ≡ z` に連結され、再帰は尾へ降ります。長さはそれぞれの列がもつものそのままです。推移性が済むと、三分性は一つの長さをもつ二つの列に対して述べられます。二つの列が一致しうるのはそこでだけだからです。空の列どうしは `refl` によって等しくなります。
<!--/-->

```agda
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inr (e , h)) (inr (e' , k)) =
    inr (e ∙ e' , ≺ᵥ-trans p q r h k)

  ≺ᵥ-tri : ∀ {k} (p q : Vec ⟪ A ⟫ k) → Tri (p ≺ᵥ q) (p ≡ q) (q ≺ᵥ p)
  ≺ᵥ-tri []      []      = eq refl
  ≺ᵥ-tri (x ∷ p) (y ∷ q) = decide (≺ₚ-tri x y)
```

<!--en-->
For inhabited vectors the heads are compared by the parameter order's trichotomy, and the helper `decide` transports the verdict from heads to vectors. A strict verdict either way becomes a left summand: the head decided, the tails never enter. The equal case is the only one that must consult the tails, and it is taken up next.
<!--zh-->
非空向量的头部由参数序的三歧性比较，辅助函数 `decide` 把判定从头部搬运到整个向量。无论哪一方的严格判定都变成左支：头部已定，尾部根本不参与。相等情形是唯一必须考察尾部的情形，下一处处理。
<!--ja-->
空でない列では、先頭がパラメータ順序の三分性によって比較され、補助 `decide` が判定を先頭から列全体へ運びます。どちら向きの狭義の判定も左の支になります。先頭で決着がつき、尾は一切登場しないからです。等しい場合だけが尾を調べる必要があり、それは次で扱われます。
<!--/-->

```agda
    where
    decide : Tri (x ≺ₚ y) (x ≡ y) (y ≺ₚ x)
           → Tri ((x ∷ p) ≺ᵥ (y ∷ q)) ((x ∷ p) ≡ (y ∷ q)) ((y ∷ q) ≺ᵥ (x ∷ p))
    decide (lt h) = lt (inl h)
    decide (gt h) = gt (inl h)
```

<!--en-->
When the heads are equal by a path `e`, the vector comparison reduces to the tails', and `Tri-map` relabels the three outcomes. A tail strictly below becomes the right summand `e , h`; tail equality, under `cong₂ _∷_`, becomes equality of the whole vectors; and the mirrored verdict attaches `sym e`. The recursion is structural in the tails, closing the induction.
<!--zh-->
当头部经路径 `e` 相等时，向量比较归结为尾部的比较，`Tri-map` 把三种结果重新标记。尾部严格更低变成右支 `e , h`；尾部相等在 `cong₂ _∷_` 之下变成整个向量的相等；镜像的判定则附上 `sym e`。递归在尾部上是结构的，归纳就此闭合。
<!--ja-->
先頭が経路 `e` によって等しいとき、ベクトルの比較は尾の比較に帰着し、`Tri-map` が三つの結果に付け替えます。尾が狭義に下なら右の支 `e , h` となり、尾が等しいことは `cong₂ _∷_` のもとで列全体の相等となり、鏡像の判定には `sym e` が付きます。再帰は尾について構造的で、帰納はここで閉じます。
<!--/-->

```agda
    decide (eq e) =
      Tri-map (λ h → inr (e , h)) (cong₂ _∷_ e) (λ h → inr (sym e , h))
        (≺ᵥ-tri p q)
```

<!--en-->
Well-foundedness is the one that needs a plan. Descending from a vector, the head either drops in the given order, and then the tail is replaced by an arbitrary one of the same length, or the head stays and the tail drops. So the descent is two nested inductions: the given order's well-foundedness for the head, and the tail's accessibility for the tail, with the arbitrary tails supplied by the statement one length down. That third ingredient is why the whole thing recurses on the length as well, and why the head's induction is taken as an induction principle rather than as a second recursive argument: with all three appetites served in one recursion the descent has no single decreasing measure to offer.
<!--zh-->
需要谋划的是良基性。从一个向量向下走，头部或者按给定的序下降，此时尾部被换成同长的任意一个；或者头部不动而尾部下降。故这次下降是两层嵌套的归纳：头部用给定序的良基性，尾部用尾部的可及性，而那些任意的尾部由「短一格的那条陈述」供给。正是这第三样配料使整件事也对长度递归，也正因如此，头部的归纳取作归纳原理而非取作第二个递归实参：若三副胃口都在同一场递归里伺候，那次下降就交不出单一的递减尺度。
<!--ja-->
整礎性は計画を要するものです。ベクトルから降りていくと、先頭が与えられた順序で落ちて尾が同じ長さの任意のものに置き換わるか、先頭はそのままで尾が落ちるかのどちらかです。したがって降下は二重の帰納です。先頭には与えられた順序の整礎性を、尾には尾の到達可能性を使い、任意の尾は一段短い長さでの命題が供給します。この第三の材料があるからこそ、全体も長さについて再帰します。また、先頭の帰納を再帰引数ではなく帰納原理として取るのはこのためです。三つの要求を一つの再帰で同時に満たそうとすると、降下が単一の減少尺度を提示できなくなるからです。
<!--/-->

<!--en-->
The helper `consAcc` lifts accessibility from length `k` to length `suc k`: assuming every vector of length `k` is accessible, it builds accessibility for `y ∷ q`. Its input `prev` is exactly the statement at the previous length, which is what allows the strict case to replace the tail with an arbitrary `r` of the same length. The proof then runs the given order's well-founded induction on the head, so the head's descent is the engine and the tail's accessibility is consumed inside.
<!--zh-->
辅助函数 `consAcc` 把可及性从长度 `k` 提升到长度 `suc k`：在「长度 `k` 的每个向量都可及」的前提下，它为 `y ∷ q` 构造可及性。输入 `prev` 正是前一长度处的陈述，这使得严格情形能把尾部换成同长的任意 `r`。证明随后对头部运行给定序的良基归纳，于是头部的下降是引擎，尾部的可及性在其内部被消耗。
<!--ja-->
補助 `consAcc` は到達可能性を長さ `k` から `suc k` へ持ち上げます。長さ `k` のすべての列が到達可能であるという仮定のもとで、`y ∷ q` の到達可能性を組み立てます。入力 `prev` は一段前の長さでの命題そのものであり、狭義の場合に尾を同じ長さの任意の `r` に置き換えられるのはこのためです。証明は先頭について与えられた順序の整礎帰納を実行し、先頭の降下が駆動装置となり、尾の到達可能性はその内部で使われます。
<!--/-->

```agda
  private
    consAcc : (k : ℕ) → ((r : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) r)
            → (y : ⟪ A ⟫) (q : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) q
            → Acc (_≺ᵥ_ {suc k} {suc k}) (y ∷ q)
    consAcc k prev = WFI.induction ≺ₚ-wf onHead
```

<!--en-->
The induction hypothesis `ih` is stated carefully: for every `z` strictly below `y`, accessibility of `z ∷ q` holds for *every* tail `q` of length `k`, given the tail's own accessibility. The universal quantification over `q` is what makes the strict case work without recursion on the vector being examined, and it is available precisely because `≺ₚ-wf` was applied as an induction principle rather than invoked recursively.
<!--zh-->
归纳假设 `ih` 的陈述很讲究：对每个严格低于 `y` 的 `z`，在给定尾部自身可及性的前提下，`z ∷ q` 的可及性对**每个**长度为 `k` 的尾部 `q` 都成立。对 `q` 的全称量化使严格情形无须对被考察的向量作递归即可工作，而这恰恰因为 `≺ₚ-wf` 是被当作归纳原理使用，而不是被递归地调用。
<!--ja-->
帰納仮説 `ih` の述べ方は慎重です。`y` より狭義に下のすべての `z` に対し、尾自身の到達可能性を与えれば、`z ∷ q` の到達可能性が長さ `k` の**すべての**尾 `q` について成り立つというものです。`q` についての全称量化があるから、狭義の場合は調べているベクトルへの再帰なしに機能します。そしてこれが可能なのは、`≺ₚ-wf` を再帰的に呼び出すのではなく帰納原理として適用したからです。
<!--/-->

```agda
      where
      onHead : (y : ⟪ A ⟫)
             → ((z : ⟪ A ⟫) → z ≺ₚ y → (q : Vec ⟪ A ⟫ k)
                  → Acc (_≺ᵥ_ {k} {k}) q → Acc (_≺ᵥ_ {suc k} {suc k}) (z ∷ q))
             → (q : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) q
```

<!--en-->
Accessibility is constructed data: `acc` pairs an element with a function taking every strictly-below element to its own accessibility. So the goal for `y ∷ q` is produced by `acc`, applied to a step function that must handle the two shapes a strict descent from `y ∷ q` can take, and the remainder of the proof is the body of that step.
<!--zh-->
可及性是被构造的数据：`acc` 把一个元素与一个函数配对，该函数把每个严格更低的元素送到它自身的可及性。于是 `y ∷ q` 的目标由 `acc` 给出，应用于一个必须处理「从 `y ∷ q` 出发的严格下降」的两种形状的步进函数，证明的余下部分就是这个步进函数的主体。
<!--ja-->
到達可能性は構成されたデータです。`acc` は要素と、狭義に下のすべての要素をその要素自身の到達可能性へ送る関数とを対にします。したがって `y ∷ q` に対する目標は `acc` によって与えられ、それに適用されるのは、`y ∷ q` からの狭義の降下が取りうる二つの形を処理するステップ関数です。証明の残りはこのステップ関数の本体です。
<!--/-->

```agda
             → Acc (_≺ᵥ_ {suc k} {suc k}) (y ∷ q)
      onHead y ih q (acc rq) = acc step
        where
        step : (r : Vec ⟪ A ⟫ (suc k)) → r ≺ᵥ (y ∷ q)
             → Acc (_≺ᵥ_ {suc k} {suc k}) r
```

<!--en-->
The strict case has a head `z` below `y` and an arbitrary tail `r`, and here the induction hypothesis does all the work: it supplies `Acc` for `z ∷ r` from `z ≺ₚ y` and `prev r`, the accessibility of `r` at length `k`. The equal case keeps the head: the path identifies `z` with `y`, so transporting the accessibility of `y ∷ r` backwards along `sym e` produces accessibility of `z ∷ r`. This transport along a head path is the price of comparing across lengths, and it is paid once here.
<!--zh-->
严格情形中头部 `z` 低于 `y`，尾部 `r` 是任意的，这里归纳假设完成全部工作：它由 `z ≺ₚ y` 与 `prev r`，即 `r` 在长度 `k` 处的可及性，供给 `z ∷ r` 的 `Acc`。相等情形保留头部：路径把 `z` 与 `y` 认同，故沿 `sym e` 把 `y ∷ r` 的可及性反向搬运，得到 `z ∷ r` 的可及性。沿头部路径的这一搬运是跨长度比较的代价，在此一次性付清。
<!--ja-->
狭義の場合は先頭 `z` が `y` より下で、尾 `r` は任意です。ここでは帰納仮説がすべての仕事をします。`z ≺ₚ y` と、長さ `k` における `r` の到達可能性 `prev r` とから、`z ∷ r` の `Acc` が供給されます。等しい場合は先頭を保ちます。経路が `z` と `y` を同一視するので、`y ∷ r` の到達可能性を `sym e` に沿って逆向きに輸送すれば `z ∷ r` の到達可能性が得られます。先頭の経路に沿ったこの輸送が、長さを越えた比較の代価であり、ここで一度だけ支払われます。
<!--/-->

```agda
        step (z ∷ r) (inl h)       = ih z h r (prev r)
        step (z ∷ r) (inr (e , h)) =
          subst (λ v → Acc (_≺ᵥ_ {suc k} {suc k}) (v ∷ r)) (sym e)
            (onHead y ih r (rq r h))

  ≺ᵥ-wf : (k : ℕ) (p : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) p
```

<!--en-->
The main theorem is induction on the length. The empty vector's accessibility is immediate, since its only would-be predecessor is the empty vector itself and that comparison is the empty type. For `x ∷ p`, `consAcc` is applied with `≺ᵥ-wf k` supplying the statement at the previous length for arbitrary tails, and `≺ᵥ-wf k p` supplying the accessibility of this vector's own tail; both come from one structural recursion on `k`.
<!--zh-->
主定理对长度作归纳。空向量的可及性是当即的：它唯一的准前驱是空向量自身，而那个比较是空类型。对 `x ∷ p`，应用 `consAcc`，以 `≺ᵥ-wf k` 供给前一长度处对任意尾部的陈述，以 `≺ᵥ-wf k p` 供给本向量自身尾部的可及性；二者都来自对 `k` 的一次结构递归。
<!--ja-->
主定理は長さに関する帰納法です。空の列の到達可能性は直ちに得られます。唯一の候補となる先行要素は空の列自身であり、その比較は空型だからです。`x ∷ p` に対しては `consAcc` を適用し、`≺ᵥ-wf k` が一段前の長さでの任意の尾についての命題を、`≺ᵥ-wf k p` がこの列自身の尾の到達可能性を供給します。両方とも `k` に関する一つの構造的再帰から来ます。
<!--/-->

```agda
  ≺ᵥ-wf zero    []      = acc (λ { [] h → Empty.rec* h })
  ≺ᵥ-wf (suc k) (x ∷ p) = consAcc k (≺ᵥ-wf k) x p (≺ᵥ-wf k p)
```

<!--en-->
One derived fact travels with the comparison and is proved by path induction: moving a vector along an equality of lengths does not change what it is below or above. The two places that need it are the trichotomy and the descent, both of which meet two vectors whose lengths are equal but not identical.
<!--zh-->
还有一件派生的事实随这次比较同行，并由一次路径归纳证出：把一个向量沿长度的等式搬过去，不改变它在谁之下、在谁之上。需要它的有两处，即三歧与下降，二者遇到的都是「长度相等但并非同一」的两个向量。
<!--ja-->
この比較に伴って一つの派生的な事実が使われ、経路の帰納法で証明されます。列を長さの等式に沿って移しても、それが何の下にあるか、何がその下にあるかは変わりません。これが必要なのは三分性と降下の二箇所で、どちらも長さが等しいが同一ではない二つの列に出会います。
<!--/-->

<!--en-->
The left lemma states that the comparison `subst (Vec ⟪ A ⟫) e p ≺ᵥ q` is a path to `p ≺ᵥ q`: transporting the compared vector along the length equality `e` leaves the comparison proposition unchanged. The proof does not unfold the vector cases at all. The general lemma `constSubstCommSlice` says that transporting along `e` commutes with a family of types that does not use the index, and the comparison against the fixed `q` is exactly such a family; the `sym` puts the equation in the direction the later proofs need.
<!--zh-->
左边的引理说：比较 `subst (Vec ⟪ A ⟫) e p ≺ᵥ q` 与 `p ≺ᵥ q` 之间是一条路径，即沿长度等式 `e` 搬运被比较的向量不改变比较命题本身。证明完全不展开向量的情形。一般引理 `constSubstCommSlice` 说，沿 `e` 的搬运与「不使用该索引的类型族」可交换，而对固定的 `q` 作比较恰是这样的类型族；`sym` 把等式调到后文证明所需的方向。
<!--ja-->
左側の補題は、比較 `subst (Vec ⟪ A ⟫) e p ≺ᵥ q` が `p ≺ᵥ q` への経路であること、つまり比較される列を長さの等式 `e` に沿って輸送しても比較の命題は変わらないことを述べます。証明はベクトルの場合分けをまったく展開しません。一般の補題 `constSubstCommSlice` は、`e` に沿う輸送が添字を使わない型族と可換であることを言い、固定された `q` との比較はまさにそのような型族です。`sym` は等式を後の証明が必要とする向きに整えます。
<!--/-->

```agda
  private
    ≺ᵥ-subst-left : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ i) (q : Vec ⟪ A ⟫ k)
                  → (subst (Vec ⟪ A ⟫) e p ≺ᵥ q) ≡ (p ≺ᵥ q)
    ≺ᵥ-subst-left e p q = sym (constSubstCommSlice
      (Vec ⟪ A ⟫) (Type (ℓ-suc ℓ)) (λ _ v → v ≺ᵥ q) e p)
```

<!--en-->
The right lemma is the mirror image: moving the *other* vector along its own length equality does not change what is below it. Both directions are needed because the name comparison transports parameters of the first name to the second's length in the `lt` case and in the opposite direction in the `gt` case, and later the well-foundedness proof moves either side. Stated once, in both orientations, no proof afterwards has to reason about `subst` on vectors.
<!--zh-->
右边的引理是镜像：把**另一个**向量沿它自己的长度等式搬过去，不改变在它之下的东西。两个方向都需要，因为名字比较在 `lt` 情形把第一个名字的参数搬到第二个的长度，在 `gt` 情形方向相反，而后文的良基性证明两边都要搬。两个朝向一次证完，此后的证明就不必再对向量上的 `subst` 说理。
<!--ja-->
右側の補題は鏡像です。**もう一方**の列をそれ自身の長さの等式に沿って移しても、その下にあるものは変わりません。両方向が必要なのは、名前の比較が `lt` の場合は最初の名前のパラメータを二番目の長さへ輸送し、`gt` の場合は逆向きだからであり、後の整礎性の証明ではどちら側も動きます。両方の向きを一度に述べておけば、これ以降の証明は列の上の `subst` について推論する必要がなくなります。
<!--/-->

```agda

    ≺ᵥ-subst-right : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ k) (q : Vec ⟪ A ⟫ i)
                   → (p ≺ᵥ subst (Vec ⟪ A ⟫) e q) ≡ (p ≺ᵥ q)
    ≺ᵥ-subst-right e p q = sym (constSubstCommSlice
      (Vec ⟪ A ⟫) (Type (ℓ-suc ℓ)) (λ _ v → p ≺ᵥ v) e q)

```

<!--en-->
## Three keys, in order

Names are ordered lexicographically by formula code, arity, and parameter vector. The comparison is written as three explicit cases, so its trichotomy and transitivity follow one key at a time.
<!--zh-->
## 三个键，依次

名字依次按公式码、元数与参数向量作字典序比较。比较写成三个明确情形，因而三歧性与传递性都可逐键证明。
<!--ja-->
## 三つの鍵を順に比較する

名前は論理式コード、アリティ、パラメータ列の順に辞書式で比較します。比較を三つの場合として明示することで、三分性と推移性を鍵ごとに示せます。
<!--/-->

<!--en-->
The comparison is a family of types read off from the definition. Its outer summand is strict comparison of formula codes under the limit order: if one name's code drops below the other's, the codes decide and nothing else is consulted. Its right summand carries the path `codeOf b ≡ codeOf a`, the equality of codes that licenses moving on to the next key, and packages it with the second key's comparison, strict inequality of natural-number arities.
<!--zh-->
这个比较是从定义直接读出的类型族。其外侧的和支是公式码在极限序下的严格比较：若一个名字的码低于另一个的，码即判定，其余一概不问。右侧的和支携带路径 `codeOf b ≡ codeOf a`，即允许进入下一个键的码相等，并把它与第二个键的比较打包，即自然数元数的严格不等。
<!--ja-->
この比較は定義からそのまま読み取れる型の族です。外側の支は、極限順序の下での論理式コードの狭義の比較です。一方の名前のコードが他方より下なら、コードが判定し、他は一切問われません。右の支は経路 `codeOf b ≡ codeOf a`、つまり次の鍵へ進むことを許すコードの相等を携え、それを第二の鍵の比較、自然数のアリティの狭義の不等号と組みにします。
<!--/-->

```agda
  infix 20 _≺ₙ_
  _≺ₙ_ : Name → Name → Type (ℓ-suc ℓ)
  a ≺ₙ b = (codeOf a ≺ codeOf b)
         ⊎ ( (codeOf b ≡ codeOf a)
           × ( (arity a < arity b)
```

<!--en-->
The innermost summand completes the descent: under equal codes and equal arities, carried again as paths `arity b ≡ arity a`, the parameter vectors are compared by `_≺ᵥ_`. Each level of nesting is therefore a pair of an equality of the previous key with the strict comparison of the next, which is exactly the shape the four laws' case analyses will follow, key by key.
<!--zh-->
最内侧的和支完成下降：在码相等且元数相等之下 (后者同样以路径 `arity b ≡ arity a` 携带)，参数向量由 `_≺ᵥ_` 比较。因此嵌套的每一层都是「前一个键的相等」与「下一个键的严格比较」的对，四条定律的情形分析正是沿这一形状逐键进行。
<!--ja-->
最も内側の支が降下を完成させます。コードが等しくアリティも等しい場合、後者はやはり経路 `arity b ≡ arity a` として携えられ、その上でパラメータ列が `_≺ᵥ_` によって比較されます。したがって入れ子の各層は「前の鍵の相等」と「次の鍵の狭義の比較」の対であり、四つの法則の場合分けはまさにこの形に沿って鍵ごとに進みます。
<!--/-->

```agda
             ⊎ ((arity b ≡ arity a) × (params a ≺ᵥ params b)) ) )
```

<!--en-->
Irreflexivity and transitivity are then the three keys' own laws, sorted by case. The mixed cases of transitivity substitute an equality of one key into the other's comparison, and that is all the verification required; the parameter case appeals to the vector comparison at three lengths, which is why that one was proved across lengths.
<!--zh-->
于是非自反与传递就是三个键各自的定律，按情形归类。传递性的混合情形把一个键上的等式代入另一个键的比较，所需的验证仅此而已；参数那一情形援引三个长度上的向量比较，而这正是当初把那一条跨长度证出的原因。
<!--ja-->
非反射性と推移性は、三つの鍵それぞれの法則を場合分けで並べたものです。推移性の混在する場合は、一方の鍵の等式を他方の鍵の比較に代入するだけで、必要な検証はそれですみます。パラメータの場合は三つの長さでの列の比較を援用します。あの比較を長さを越えて証明したのはこのためです。
<!--/-->

<!--en-->
A name can never be strictly below itself, and the three clauses say why: whichever summand witnesses `a ≺ₙ a` would witness a strict descent in one of the three keys from a key to itself. The code case contradicts the limit order's irreflexivity, the arity case is a natural number strictly below itself, refuted by `¬m<m`, and the parameter case contradicts vector irreflexivity at `params a`'s own length.
<!--zh-->
一个名字永不可能严格低于它自己，三个子句各道其由：无论哪个和支见证 `a ≺ₙ a`，都等于见证三个键中某键从自身到自身的严格下降。码的情形与极限序的非自反性矛盾；元数的情形是自然数严格小于自身，由 `¬m<m` 反驳；参数的情形与 `params a` 自身长度处的向量非自反性矛盾。
<!--ja-->
名前が自分自身より狭義に下になることは決してなく、三つの節がそれぞれ理由を言います。`a ≺ₙ a` を証明する和の支はどれも、三つの鍵のどれかが自分自身への狭義の降下を与えることになるからです。コードの場合は極限順序の非反射性と矛盾し、アリティの場合は自分自身より小さい自然数となり `¬m<m` で反証され、パラメータの場合は `params a` 自身の長さでの列の非反射性と矛盾します。
<!--/-->

```agda
  ≺ₙ-irr : (a : Name) → a ≺ₙ a → Empty.⊥
  ≺ₙ-irr a (inl h)                 = ≺-irr (codeOf a) h
  ≺ₙ-irr a (inr (_ , inl h))       = ¬m<m h
  ≺ₙ-irr a (inr (_ , inr (_ , h))) = ≺ᵥ-irr (params a) h

  ≺ₙ-trans : (a b c : Name) → a ≺ₙ b → b ≺ₙ c → a ≺ₙ c
```

<!--en-->
Transitivity is stated for three names and proved by case analysis on where the two comparisons decided. When both decided at the codes, the limit order's transitivity applies directly. The first mixed case has `a` strictly below `b` at the codes while the second comparison carries `codeOf c ≡ codeOf b`; substituting that equality backwards puts `codeOf a` below `codeOf c`, and the symmetric case is the same substitution read forwards. Each mixed case is one transport, nothing more.
<!--zh-->
传递性对三个名字陈述，按两次比较各自在何处判定作情形分析。当二者都在码处判定时，直接援引极限序的传递性。第一个混合情形中，`a` 在码处严格低于 `b`，而第二次比较只知道 `codeOf c ≡ codeOf b`；把该等式反向代入，即得 `codeOf a` 低于 `codeOf c`；对称的情形是同一次代入正向读出。每个混合情形只是一次搬运，别无其他。
<!--ja-->
推移性は三つの名前に対して述べられ、二つの比較がそれぞれどこで決着したかによる場合分けで証明されます。両方がコードで決着したときは、極限順序の推移性を直接適用します。最初の混在した場合は、`a` がコードで `b` より狭義に下であり、二番目の比較が知っているのは `codeOf c ≡ codeOf b` だけです。その等式を逆向きに代入すれば `codeOf a` が `codeOf c` より下であることが得られ、対称の場合は同じ代入を順方向に読んだものです。混在した各場合は輸送が一回あるだけで、それ以上ではありません。
<!--/-->

```agda
  ≺ₙ-trans a b c (inl h) (inl k) =
    inl (≺-trans (codeOf a) (codeOf b) (codeOf c) h k)
  ≺ₙ-trans a b c (inl h) (inr (q , _)) =
    inl (subst (λ v → codeOf a ≺ v) (sym q) h)
  ≺ₙ-trans a b c (inr (q , _)) (inl k) =
```

<!--en-->
The cases decided at the arity key reuse the same pattern with natural numbers. Two strict arity inequalities compose by `<-trans`; a strict one beside an equality of arities is transported into a strict inequality with the appropriate endpoint substituted. Note the direction of the carried paths: the comparison records `codeOf b ≡ codeOf a` and `arity b ≡ arity a`, equality stated at the larger name, so the concatenations and substitutions run against that orientation.
<!--zh-->
在元数键处判定的诸情形以自然数重复同一模式。两条严格的元数不等经 `<-trans` 复合；严格不等与元数相等并列时，代换相应的端点即被搬运成严格不等。注意所携路径的方向：比较记录的是 `codeOf b ≡ codeOf a` 与 `arity b ≡ arity a`，即陈述在更大的名字处的相等，故拼接与代换都逆着这一朝向进行。
<!--ja-->
アリティの鍵で決着した場合は、自然数で同じ型を繰り返します。二つの狭義のアリティの不等号は `<-trans` で合成され、狭義の不等号とアリティの等式が並ぶときは、適切な端点を代入する輸送で狭義の不等号に変わります。携えられる経路の向きに注意してください。比較が記録するのは `codeOf b ≡ codeOf a` と `arity b ≡ arity a`、つまりより大きな名前の側で述べた相等なので、連結と代入はその向きに逆らって走ります。
<!--/-->

```agda
    inl (subst (λ v → v ≺ codeOf c) q k)
  ≺ₙ-trans a b c (inr (q , inl h)) (inr (q' , inl k)) =
    inr (q' ∙ q , inl (<-trans h k))
  ≺ₙ-trans a b c (inr (q , inl h)) (inr (q' , inr (e , _))) =
    inr (q' ∙ q , inl (subst (λ j → arity a < j) (sym e) h))
```

<!--en-->
The final case is where all three keys agreed up to the parameters, and here the third key's transitivity at three possibly distinct lengths is exactly what is needed: `≺ᵥ-trans` takes `params a ≺ᵥ params b` and `params b ≺ᵥ params c` at whatever lengths those vectors carry and returns `params a ≺ᵥ params c`. The two arity paths concatenate to `arity a ≡ arity c`, completing the right summand with all three components.
<!--zh-->
最后的情形是三个键直到参数处都相符，而这里恰需第三个键在三个可能不同的长度上的传递性：`≺ᵥ-trans` 接受各带其长度的 `params a ≺ᵥ params b` 与 `params b ≺ᵥ params c`，返回 `params a ≺ᵥ params c`。两条元数路径拼接成 `arity a ≡ arity c`，右支的三个分量就此齐备。
<!--ja-->
最後の場合は、三つの鍵がパラメータに至るまで一致しているところであり、ここでまさに必要なのが第三の鍵の三つの長さでの推移性です。`≺ᵥ-trans` はそれぞれの列のもつ長さで `params a ≺ᵥ params b` と `params b ≺ᵥ params c` を受け取り、`params a ≺ᵥ params c` を返します。二つのアリティの経路は `arity a ≡ arity c` に連結され、右の支の三つの成分がそろいます。
<!--/-->

```agda
  ≺ₙ-trans a b c (inr (q , inr (e , _))) (inr (q' , inl k)) =
    inr (q' ∙ q , inl (subst (λ j → j < arity c) e k))
  ≺ₙ-trans a b c (inr (q , inr (e , h))) (inr (q' , inr (e' , k))) =
    inr (q' ∙ q , inr (e' ∙ e , ≺ᵥ-trans (params a) (params b) (params c) h k))
```

<!--en-->
Trichotomy is the third law, and it is the one that reads the comparison off rather than combines the other laws. The proof descends the keys in order: if the codes already decide, the verdict is given immediately; if the codes agree, the arities decide; if the arities agree too, the parameter vectors decide. Only this last stage needs care. Equal arities are connected by a path, not identified, so `params a` and `params b` live at different lengths; the vector comparison can only run after the first is transported to the second's length, and the strict verdicts it returns must be transported back before they count as comparisons of the original names. In the equality case something more is required: the two names must be presented as equal dependent triples, so the formulas themselves must agree, and that is exactly what injectivity of the code gives, since `code-shift` says transporting along the arity path leaves the code unchanged and the code verdict says the codes already agree.
<!--zh-->
三歧性是第三条定律，也是逐字读出比较本身而非组合前两条定律的那一条。证明沿诸键依次下降：若码已经判定，结论立即给出；若码相等，则由元数判定；若元数也相等，则由参数向量判定。只有最后一步需要用心。相等的元数由一条路径相连而非被等同，因此 `params a` 与 `params b` 处在不同的长度上；必须先把前者传输到后者的长度，向量比较才能进行，而比较返回的严格判决也要传回原类型，才算原有两个名字之间的比较。相等情形还需要更多：两个名字要作为相等的依值三元组呈现出来，故两条公式本身必须一致，而这正是码的单射性所给出的，因为 `code-shift` 表明沿元数路径的传输不改变码，而码上的判定说明码本来就已相等。
<!--ja-->
三歧性は三番目の法則であり、他の法則を組み合わせるのではなく比較そのものを読み取るものです。証明は鍵の順に降りていきます。コードがすでに判定を与えれば直ちに結論が出て、コードが等しければアリティが判定し、アリティも等しければパラメータ列が判定します。最後の段階だけが注意を要します。等しいアリティは同一化ではなく経路で結ばれているため、`params a` と `params b` は異なる長さに住んでいます。まず前者を後者の長さへ輸送しなければベクトル比較は実行できず、比較が返す狭義の判定も元の型へ輸送し戻して初めて、元の二つの名前の間の比較になります。等しい場合はさらに多くが要ります。二つの名前を等しい依存三つ組として提示しなければならないので、論理式そのものも一致する必要があり、それを与えるのがまさにコードの単射性です。`code-shift` はアリティの経路に沿う輸送がコードを変えないことを述べ、コード上の判定はコードがすでに一致していると言っているからです。
<!--/-->

<!--en-->
The statement is a `Tri`, a three-way verdict carrying either a proof of `a ≺ₙ b`, a path `a ≡ b`, or a proof of `b ≺ₙ a`. The proof hands the whole question to the code order: `≺-tri` already returns such a verdict for the two codes, and a local helper `byCodes` converts a verdict at the codes into one at the names. The helper is introduced by type first, so the shape of the conversion is visible before its clauses.
<!--zh-->
结论的类型是 `Tri`，即三选一的判定，携带或是 `a ≺ₙ b` 的证明、路径 `a ≡ b`、或是 `b ≺ₙ a` 的证明。证明把整个问题交给码上的序：`≺-tri` 已经对两个码给出这样的判定，局部辅助函数 `byCodes` 再把码层面的判定转换为名字层面的判定。先以类型引入这个辅助函数，使转换的形状在各子句之前就可看见。
<!--ja-->
主張の型は `Tri`、つまり三択の判定であり、`a ≺ₙ b` の証明、経路 `a ≡ b`、あるいは `b ≺ₙ a` の証明のいずれかを運びます。証明は問題全体をコード上の順序に委ねます。`≺-tri` はすでに二つのコードに対しこうした判定を返すので、局所的な補助関数 `byCodes` がコード上の判定を名前上の判定へ変換します。補助関数はまず型で導入されるため、変換の形が各節の前に見えています。
<!--/-->

```agda
  ≺ₙ-tri : (a b : Name) → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
  ≺ₙ-tri a b = byCodes (≺-tri (codeOf a) (codeOf b))
    where
    byCodes : Tri (codeOf a ≺ codeOf b) (codeOf a ≡ codeOf b) (codeOf b ≺ codeOf a)
            → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
```

<!--en-->
The strict cases are immediate: a strict comparison of codes is the left summand of the name order, whichever way it points. The equality case opens the second key, delegating to `byArities`, which does for the arities what `byCodes` did for the codes.
<!--zh-->
严格情形是直接的：无论偏向哪一方，码上的严格比较正是名字序和类型的左支。相等的情形则打开第二个键，交给 `byArities`，它对元数做的事正如 `byCodes` 对码做的事。
<!--ja-->
狭義の場合は直接です。どちら向きであれ、コードの狭義比較は名前の順序の和の左成分そのものです。等しい場合は第二の鍵が開かれ、`byArities` に委ねられます。これはアリティに対して、`byCodes` がコードに対してしたのと同じことをします。
<!--/-->

```agda
    byCodes (lt h) = lt (inl h)
    byCodes (gt h) = gt (inl h)
    byCodes (eq ec) = byArities (arity a ≟ arity b)
      where
      byArities : NatOrder.Trichotomy (arity a) (arity b)
```

<!--en-->
Here the verdicts take the right summand, and they carry the code equality itself. Note the orientation: the comparison records `codeOf b ≡ codeOf a`, equality stated at the larger name, so the strict case below needs `sym ec` while the dual case needs `ec` as written. When the arities are also equal, `≺ᵥ-tri` compares vectors; but `params a` sits at length `arity a` and `params b` at `arity b`, so the first vector is transported along the arity path `e` before the comparison runs.
<!--zh-->
这里的判定取和的右支，并携带码等式本身。请注意方向：比较记录的是在较大名字处陈述的 `codeOf b ≡ codeOf a`，所以这一侧的严格情形需要 `sym ec`，而对偶情形需要照原样的 `ec`。当元数也相等时，由 `≺ᵥ-tri` 比较向量；但 `params a` 位于长度 `arity a`，`params b` 位于 `arity b`，所以第一个向量要沿元数路径 `e` 传输之后才能比较。
<!--ja-->
ここでの判定は和の右成分を取り、コードの等式そのものを運びます。向きに注意してください。比較は大きな名前の側で述べた `codeOf b ≡ codeOf a` を記録するので、こちらの狭義の場合には `sym ec` が、双対の場合には書かれたままの `ec` が要ります。アリティも等しいときは `≺ᵥ-tri` がベクトルを比較しますが、`params a` は長さ `arity a`、`params b` は `arity b` に住むので、最初のベクトルはアリティの経路 `e` に沿って輸送されてから比較されます。
<!--/-->

```agda
                → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
      byArities (NatOrder.lt h) = lt (inr (sym ec , inl h))
      byArities (NatOrder.gt h) = gt (inr (ec , inl h))
      byArities (NatOrder.eq e) =
        byParams (≺ᵥ-tri (subst (Vec ⟪ A ⟫) e (params a)) (params b))
```

<!--en-->
The transported vector is given a name, `shifted`, so the statements below stay readable at their real lengths. The equality case will need more than the vectors: to conclude `a ≡ b` outright, the formulas must agree as well, and `sameFormula` states this at the transported formula, whose type is that of the formula of a name with arity `arity b`. Without such an equality the two names could agree in both decided keys and in parameters yet still differ in syntax.
<!--zh-->
被传输的向量得到一个名字 `shifted`，使下面的陈述能在各自真实的长度上保持可读。相等情形需要的还不止向量：要直接得出 `a ≡ b`，两条公式也必须一致，`sameFormula` 就是在被传输的公式处陈述这一点，后者的类型正是元数为 `arity b` 的名字的公式的类型。若没有这样一条等式，两个名字可能在两个已判定的键与参数上都相符，语法上却仍不相同。
<!--ja-->
輸送されたベクトルには `shifted` という名前が与えられ、以下の記述が各自の実際の長さで読みやすく保たれます。等しい場合に必要なのはベクトルだけではありません。`a ≡ b` を直接得るには論理式も一致しなければならず、`sameFormula` は輸送された論理式のところでこれを述べます。その型は、アリティ `arity b` の名前の論理式の型です。この等式がなければ、二つの名前は判定済みの二つの鍵でもパラメータでも一致しながら、構文の上ではなお異なり得ます。
<!--/-->

```agda
        where
        shifted : Vec ⟪ A ⟫ (arity b)
        shifted = subst (Vec ⟪ A ⟫) e (params a)

        sameFormula : subst (λ k → Formula (⊥* {ℓ}) (suc k)) e (formula a)
                    ≡ formula b
```

<!--en-->
Why the formulas agree: transporting `formula a` along `e` does not change its code, by `code-shift`, and the first component of `ec` says the code of `formula a` equals the code of `formula b`. Concatenating gives equal codes, and `code-inj` turns equal codes back into equal parameter-free formulas. This is the same injectivity proved earlier in the chapter, here doing the work its statement anticipated. With `shifted` and `sameFormula` in hand, `byParams` converts a vector verdict into a verdict at the names.
<!--zh-->
两条公式为何一致：由 `code-shift`，把 `formula a` 沿 `e` 传输不改变它的码，而 `ec` 的第一个分量说明 `formula a` 的码等于 `formula b` 的码。串接二者即得相同的码，再由 `code-inj` 把相同的码还原为相等的无参公式。这正是本章前面证过的那条单射性，在此完成它的陈述所预示的工作。备好 `shifted` 与 `sameFormula` 之后，`byParams` 便把向量层面的判定转换为名字层面的判定。
<!--ja-->
なぜ論理式が一致するのか。`code-shift` により、`formula a` を `e` に沿って輸送してもそのコードは変わらず、`ec` の第一成分は `formula a` のコードが `formula b` のコードと等しいことを述べます。これらを連結すれば等しいコードが得られ、`code-inj` が等しいコードを等しいパラメータなし論理式へと戻します。これは本章の前半で証した単射性そのものであり、ここでその主張が予期していた仕事を果たします。`shifted` と `sameFormula` がそろえば、`byParams` がベクトル上の判定を名前上の判定へ変換します。
<!--/-->

```agda
        sameFormula =
          code-inj (subst (λ k → Formula (⊥* {ℓ}) (suc k)) e (formula a))
            (formula b)
            (code-shift e (formula a) ∙ cong fst ec)

        byParams : Tri (shifted ≺ᵥ params b) (shifted ≡ params b)
```

<!--en-->
The strict verdicts were obtained at the transported lengths, so their statements must be moved back. `≺ᵥ-subst-left` says that comparing `subst (Vec ⟪ A ⟫) e p` against `q` is the same proposition as comparing `p` against `q`; transporting `h` along that equality turns a comparison of `shifted` into one of `params a`. Each verdict also carries the code and arity equalities, oriented as the sum requires. The dual case is symmetric, using `≺ᵥ-subst-right` on the other side of the comparison.
<!--zh-->
严格判决是在被传输的长度处得到的，所以它们的陈述要传回。`≺ᵥ-subst-left` 说：把 `subst (Vec ⟪ A ⟫) e p` 与 `q` 相比，作为命题与把 `p` 与 `q` 相比相同；把 `h` 沿这条等式传输，就把对 `shifted` 的比较换成对 `params a` 的比较。每个判决还要携带码等式与元数等式，方向按和的要求放置。对偶情形对称，在比较的另一侧使用 `≺ᵥ-subst-right`。
<!--ja-->
狭義の判定は輸送後の長さで得られたので、その述べ方を元へ戻す必要があります。`≺ᵥ-subst-left` は、`subst (Vec ⟪ A ⟫) e p` を `q` と比べることは命題として `p` を `q` と比べることと同じだと言うので、`h` をこの等式に沿って輸送すれば `shifted` についての比較が `params a` についての比較に変わります。どちらの判定も、和が要求する向きに揃えたコードとアリティの等式を運びます。双対の場合は対称で、比較の反対側の `≺ᵥ-subst-right` を使います。
<!--/-->

```agda
                       (params b ≺ᵥ shifted)
                 → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
        byParams (lt h) = lt (inr (sym ec , inr (sym e ,
          transport (≺ᵥ-subst-left e (params a) (params b)) h)))
        byParams (gt h) = gt (inr (ec , inr (e ,
```

<!--en-->
The equality verdict is a path between two elements of `Name`, which is itself a triple. `ΣPathP` pairs the arity path `e` with paths between the remaining components: `toPathP sameFormula` lifts the formula equality across the type family `Formula (⊥*) (suc k)`, and `toPathP ep` does the same for the vector equality. This is where `sameFormula` earns its place: with both decided keys equal and the parameters equal, it is only the formula equality that is still missing, and once supplied the two names are identical as data.
<!--zh-->
相等判定是 `Name` 中两个元素之间的路径，而 `Name` 本身是个三元组。`ΣPathP` 把元数路径 `e` 与其余分量之间的路径配对：`toPathP sameFormula` 把公式等式沿类型族 `Formula (⊥*) (suc k)` 提升，`toPathP ep` 对向量等式做同样的事。这正是 `sameFormula` 的用武之地：在两个已判定的键相等、参数也相等之后，缺的只是公式等式，而它一旦补上，两个名字作为数据便完全相同。
<!--ja-->
等しいという判定は `Name` の二つの元の間の経路であり、`Name` はそれ自身三つ組です。`ΣPathP` はアリティの経路 `e` を残りの成分どうしの経路と組み合わせます。`toPathP sameFormula` が論理式の等式を型族 `Formula (⊥*) (suc k)` に沿って持ち上げ、`toPathP ep` がベクトルの等式に同じことをします。ここが `sameFormula` の出番です。判定済みの二つの鍵が等しくパラメータも等しい後、欠けているのは論理式の等式だけであり、それが補われれば二つの名前はデータとして同一になります。
<!--/-->

```agda
          transport (≺ᵥ-subst-right e (params b) (params a)) h)))
        byParams (eq ep) =
          eq (ΣPathP (e , ΣPathP (toPathP sameFormula , toPathP ep)))
```

<!--en-->
## Descending the three keys

Well-foundedness follows by nested descent, one layer per key. Innermost, the code and the arity are fixed and the parameters descend, with the vector's accessibility as the decreasing argument; in the middle layer, the code is fixed and the arity descends; outermost, the code descends. Each layer is a separate function taking the outer layers' induction hypotheses as arguments, so each recurses on exactly one accessibility proof and the recursion is structural throughout. Everything is stated at names themselves, together with equations saying where each key sits; that is the same discipline the trichotomy observed, since a statement at a name's projections would have to be matched against one at the name.
<!--zh-->
## 沿三个键下降

良基性来自嵌套下降，一个键一层。最内层，码与元数固定，诸参数下降，递减的实参是向量的可及性；中间一层，码固定，元数下降；最外层，码下降。每一层各是一个函数，把外层的诸归纳假设当实参收进来，于是每一层恰对一份可及性证明递归，且处处都是结构递归。一切陈述都落在名字自身上，连同说明各键位置所在的等式；这正是三歧处同一条规矩的再现：陈述在名字诸投影上的内容，必须与陈述在名字上的内容对得上。
<!--ja-->
## 三つの鍵に沿って降下する

整礎性は入れ子になった降下に従い、鍵ごとに一層をなします。最内層ではコードとアリティを固定してパラメータ列を降り、減少する引数はベクトルの到達可能性です。中層ではコードを固定してアリティを降り、最外層ではコードを降ります。各層は外側の層の帰納仮定を引数として受け取る別個の関数なので、それぞれがちょうど一つの到達可能性の証明について再帰し、再帰は至る所構造的です。すべての主張は名前そのものの上で、各鍵の位置を言う等式とともになされます。これは三歧性で見たのと同じ規律であり、名前の射影の上で述べた内容は名前の上で述べた内容と一致させなければなりません。
<!--/-->

<!--en-->
The innermost layer is a function whose telescope records the whole descent picture at once. It is given: a fixed code `c`; the outer induction hypothesis `ihC`, covering every name whose code drops below `c`; a bound `k`; the middle induction hypothesis `ihK`, covering names with code `c` and arity below `k`; a parameter vector `p` with its own vector accessibility; and the name `a` under study, with three equations: `qc` pins its code at `c`, `ek` pins its arity at `k`, and `qp` identifies its transported parameters with `p`. The conclusion is simply that `a` is accessible.
<!--zh-->
最内层是一个函数，其参数序列把整幅下降图景一次记录完毕。它拿到的有：一个固定的码 `c`；覆盖所有码小于 `c` 的名字的外层归纳假设 `ihC`；一个界 `k`；覆盖码为 `c` 且元数小于 `k` 的名字的中层归纳假设 `ihK`；一个参数向量 `p` 连同它自身的向量可及性；以及所研究的名字 `a`，并带三条等式：`qc` 把码固定在 `c`，`ek` 把元数固定在 `k`，`qp` 把传输后的参数认同为 `p`。结论只是：`a` 可及。
<!--ja-->
最内層は、降下の全体像を一つの引数列に記録する関数です。与えられるのは、固定されたコード `c`、コードが `c` より下のすべての名前を覆う外側の帰納仮定 `ihC`、境界 `k`、コードが `c` でアリティが `k` より下の名前を覆う中層の帰納仮定 `ihK`、それ自身のベクトル到達可能性をもつパラメータ列 `p`、そして研究対象の名前 `a` と、三つの等式です。`qc` はコードを `c` に、`ek` はアリティを `k` に固定し、`qp` は輸送されたパラメータ列を `p` と同一視しますです。結論は単に `a` が到達可能だということです。
<!--/-->

```agda
  private
    accAtParam : (c : Limit)
               → ((b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b)
               → (k : ℕ)
               → ((b : Name) → codeOf b ≡ c → arity b < k → Acc _≺ₙ_ b)
```

<!--en-->
The type of the vector accessibility parameter is stated at the single length `k`, matching `p`; this is why the parameters were transported into `p`'s length by the equation `qp` rather than compared in place. Accessibility of `a` is supplied as the constructor `acc` together with a step function: to prove every name is accessible, it suffices, for each `a`, to exhibit a function that takes any `b` below `a` and returns `b`'s accessibility.
<!--zh-->
向量可及性参数的类型陈述在单一长度 `k` 上，与 `p` 相配；这正是参数要经等式 `qp` 传输到 `p` 的长度、而非就地比较的原因。`a` 的可及性由构造子 `acc` 连同一个步进函数给出：要证每个名字可及，只需对每个 `a` 展示一个函数，它接收任一位于 `a` 之下的 `b` 并返回 `b` 的可及性。
<!--ja-->
ベクトル到達可能性のパラメータの型は単一の長さ `k` で述べられ、`p` と一致しています。これが、パラメータをその場で比較するのではなく等式 `qp` によって `p` の長さへ輸送する理由です。`a` の到達可能性は構成子 `acc` とステップ関数によって与えられます。すべての名前が到達可能だと示すには、各 `a` に対し、`a` より下の任意の `b` を受け取って `b` の到達可能性を返す関数を示せば十分です。
<!--/-->

```agda
               → (p : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) p
               → (a : Name) → codeOf a ≡ c → (ek : arity a ≡ k)
               → subst (Vec ⟪ A ⟫) ek (params a) ≡ p
               → Acc _≺ₙ_ a
    accAtParam c ihC k ihK p (acc rp) a qc ek qp = acc step
```

<!--en-->
The step function splits on which key decided `b ≺ₙ a`. If the code dropped, `qc` transports `codeOf b ≺ codeOf a` into `codeOf b ≺ c`, and the outer induction hypothesis finishes. If the arity decided, this predecessor judgment carries `q : codeOf a ≡ codeOf b`; hence `sym q ∙ qc : codeOf b ≡ c`. Transporting `arity b < arity a` along `ek : arity a ≡ k` gives `arity b < k`, so the middle induction hypothesis applies.
<!--zh-->
步进函数按哪个键判定 `b ≺ₙ a` 分情形。若码下降，`qc` 把 `codeOf b ≺ codeOf a` 传成 `codeOf b ≺ c`，外层归纳假设即告完成。若元数判定，这个前驱判断携带 `q : codeOf a ≡ codeOf b`，故有 `sym q ∙ qc : codeOf b ≡ c`。再沿 `ek : arity a ≡ k` 把 `arity b < arity a` 传成 `arity b < k`，中层归纳假设便可应用。
<!--ja-->
ステップ関数は、どの鍵が `b ≺ₙ a` を判定したかで場合分けします。コードが落ちた場合、`qc` は `codeOf b ≺ codeOf a` を `codeOf b ≺ c` へ移し、外側の帰納仮定で終わります。アリティが判定した場合、この先行元の判定は `q : codeOf a ≡ codeOf b` を運ぶので、`sym q ∙ qc : codeOf b ≡ c` が得られます。さらに `ek : arity a ≡ k` に沿って `arity b < arity a` を `arity b < k` へ輸送すれば、中層の帰納仮定を適用できます。
<!--/-->

```agda
      where
      step : (b : Name) → b ≺ₙ a → Acc _≺ₙ_ b
      step b (inl h)           = ihC b (subst (λ v → codeOf b ≺ v) qc h)
      step b (inr (q , inl h)) = ihK b (sym q ∙ qc) (subst (λ j → arity b < j) ek h)
      step b (inr (q , inr (e , h))) =
```

<!--en-->
The remaining case is the parameter key, and it is the only case that recurses in the innermost layer. For a predecessor judgment `b ≺ₙ a`, this branch supplies `e : arity a ≡ arity b`, while `ek : arity a ≡ k` pins the current name to the fixed arity. Thus `eb = sym e ∙ ek` has type `arity b ≡ k`; transporting `params b` along it produces `pb`, the predecessor vector at the fixed length. The code equation is aligned independently as `sym q ∙ qc`.
<!--zh-->
剩下的是参数键，也是最内层中唯一递归的情形。对前驱判断 `b ≺ₙ a`，这一分支给出 `e : arity a ≡ arity b`，而 `ek : arity a ≡ k` 把当前名字固定到元数 `k`。因此 `eb = sym e ∙ ek` 的类型是 `arity b ≡ k`；沿它传输 `params b`，便得到固定长度处的前驱向量 `pb`。码等式则独立地由 `sym q ∙ qc` 对齐。
<!--ja-->
残るのはパラメータの鍵であり、最内層で再帰する唯一の場合です。先行元の判定 `b ≺ₙ a` では、この枝は `e : arity a ≡ arity b` を与え、`ek : arity a ≡ k` は現在の名前を固定アリティに結びます。したがって `eb = sym e ∙ ek` は `arity b ≡ k` をもち、これに沿って `params b` を輸送すると固定長の先行ベクトル `pb` が得られます。コードの等式は独立に `sym q ∙ qc` で揃えます。
<!--/-->

```agda
        accAtParam c ihC k ihK pb (rp pb hb) b (sym q ∙ qc) eb refl
        where
        eb : arity b ≡ k
        eb = sym e ∙ ek
        pb : Vec ⟪ A ⟫ k
```

<!--en-->
The strict comparison `h` was made between `params b` and `params a` at their own lengths, while the accessibility being consumed belongs to `p`. Two moves close the gap: `≺ᵥ-subst-left` and `≺ᵥ-subst-right` say that transporting a vector along an equality of lengths does not change what it is below, so `h` is first rewritten into a comparison at the bound length; then `qp` transports the right endpoint from `params a` to `p`, giving `hb : pb ≺ᵥ p`. The recursive call feeds `hb` into `rp`, the accessibility of `p`, and `b` is returned accessible.
<!--zh-->
严格比较 `h` 是在各自长度上于 `params b` 与 `params a` 之间作出的，而所用的可及性属于 `p`。两步即可弥合差距：`≺ᵥ-subst-left` 与 `≺ᵥ-subst-right` 说沿长度等式的传输不改变向量在谁之下，故先把 `h` 改写成界长度处的比较；再由 `qp` 把右端点从 `params a` 传到 `p`，得 `hb : pb ≺ᵥ p`。递归调用把 `hb` 交给 `rp`，即 `p` 的可及性，并返回 `b` 的可及性。
<!--ja-->
狭義の比較 `h` は `params b` と `params a` の間で各自の長さでなされたもので、用いられる到達可能性は `p` のものです。この隔たりは二つの操作で埋まります。`≺ᵥ-subst-left` と `≺ᵥ-subst-right` は、長さの等式に沿う輸送がベクトルの下辺を変えないと言うので、まず `h` を境界の長さでの比較へ書き換えます。次に `qp` が右端点を `params a` から `p` へ輸送し、`hb : pb ≺ᵥ p` が得られます。再帰呼び出しは `hb` を `p` の到達可能性である `rp` に渡し、`b` の到達可能性を返します。
<!--/-->

```agda
        pb = subst (Vec ⟪ A ⟫) eb (params b)
        hb : pb ≺ᵥ p
        hb = subst (λ v → pb ≺ᵥ v) qp
          (transport (sym (≺ᵥ-subst-right ek pb (params a)))
            (transport (sym (≺ᵥ-subst-left eb (params b) (params a))) h))
```

<!--en-->
The middle layer fixes a code and descends through arities. Its telescope is shorter: the code induction hypothesis `ihC`, a bound `k` with its own accessibility in the natural-number order, and the name with its code pinned at `c` and its arity at `k`. What replaced the vector accessibility is the natural-number accessibility `rk`, since the arity key descends in ℕ.
<!--zh-->
中间一层固定一个码，沿元数下降。它的参数序列更短：码的归纳假设 `ihC`、带自身自然数序可及性的界 `k`、以及码固定在 `c`、元数固定在 `k` 的那个名字。接替向量可及性的正是自然数可及性 `rk`，因为元数键在 ℕ 中下降。
<!--ja-->
中層は一つのコードを固定し、アリティに沿って降ります。引数列は短くなります。コードの帰納仮定 `ihC`、自然数順序での到達可能性をもつ境界 `k`、そしてコードを `c` に、アリティを `k` に固定された名前です。ベクトルの到達可能性の代わりになったのは自然数の到達可能性 `rk` で、アリティの鍵は ℕ の中で降りるからです。
<!--/-->

```agda

    accAtArity : (c : Limit)
               → ((b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b)
               → (k : ℕ) → Acc _<_ k
               → (a : Name) → codeOf a ≡ c → arity a ≡ k → Acc _≺ₙ_ a
    accAtArity c ihC k (acc rk) a qc ek =
```

<!--en-->
The body hands everything to the innermost layer: the parameters are transported to `k`, and their vector accessibility is supplied outright by `≺ᵥ-wf`, which holds for every vector at every length and asks for no recursion here. The only genuine induction is on arities: the local `ihK` unwraps the natural-number accessibility `rk`, so a name with code `c` and strictly smaller arity is handled by a recursive call at that smaller bound. This is the layer where a strictly smaller arity, of any name at all, becomes a smaller bound.
<!--zh-->
主体把一切交给最内层：参数被传输到 `k`，而其向量可及性由 `≺ᵥ-wf` 直接给出，后者对每个长度上的每个向量都成立，此处不需要递归。真正的归纳只在元数上进行：局部的 `ihK` 拆开自然数可及性 `rk`，于是码为 `c` 且元数严格更小的名字由在那个更小界处的递归调用处理。这一层把「任一名字的严格更小的元数」变成「更小的界」。
<!--ja-->
本体はすべてを最内層に委ねます。パラメータ列は `k` へ輸送され、そのベクトル到達可能性は `≺ᵥ-wf` がすべての長さのすべてのベクトルに対して成り立つので、ここでは再帰を要求せずそのまま供給されます。真の帰納はアリティについてだけです。局所的な `ihK` が自然数の到達可能性 `rk` をほどき、コードが `c` でアリティが真に小さい名前はその小さい境界での再帰呼び出しで処理されます。この層が、任意の名前の真に小さいアリティを小さい境界へ変換する場所です。
<!--/-->

```agda
      accAtParam c ihC k ihK (subst (Vec ⟪ A ⟫) ek (params a))
        (≺ᵥ-wf k (subst (Vec ⟪ A ⟫) ek (params a))) a qc ek refl
      where
      ihK : (b : Name) → codeOf b ≡ c → arity b < k → Acc _≺ₙ_ b
      ihK b q h = accAtArity c ihC (arity b) (rk (arity b) h) b q refl
```

<!--en-->
The outer layer descends through codes and needs no equation for the arity at all. Given accessibility of a code `c` and a name whose code is `c`, it invokes the middle layer at the bound `arity a`, supplying the natural-number accessibility that holds unconditionally. The local `ihC` unwraps the code accessibility: a name with strictly smaller code gets a recursive call at its own code. This mirrors the middle layer exactly, one level further out.
<!--zh-->
最外层沿码下降，根本不需要关于元数的等式。给定码 `c` 的可及性以及码为 `c` 的名字，它在界 `arity a` 处调用中间层，并直接供给那个无条件成立的自然数可及性。局部的 `ihC` 拆开码的可及性：码严格更小的名字在它自己的码处得到一次递归调用。这与中间一层完全镜像，只是再往外一层。
<!--ja-->
最外層はコードに沿って降り、アリティについての等式をまったく必要としません。コード `c` の到達可能性と、コードが `c` である名前が与えられると、境界 `arity a` で中層を呼び出し、無条件に成り立つ自然数の到達可能性を供給します。局所的な `ihC` がコードの到達可能性をほどき、コードが真に小さい名前はその名前自身のコードでの再帰呼び出しを得ます。これは中層の正確な写しであり、一段だけ外側です。
<!--/-->

```agda

    accAtCode : (c : Limit) → Acc _≺_ c → (a : Name) → codeOf a ≡ c → Acc _≺ₙ_ a
    accAtCode c (acc rc) a qc =
      accAtArity c ihC (arity a) (<-wellfounded (arity a)) a qc refl
      where
      ihC : (b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b
```

<!--en-->
The final theorem is a one-line composition of the three layers. Given a name `a`, the code order's own well-foundedness provides accessibility of `codeOf a`, and the outer layer converts that into accessibility of `a`, with the code equation holding by reflection. Every name is thus accessible under the three-key comparison, which is the well-foundedness law of a strict well-order.
<!--zh-->
最后的定理是三层的一行复合。给定名字 `a`，码序自身的良基性给出 `codeOf a` 的可及性，最外层把它转换成 `a` 的可及性，其中码等式由反身性成立。于是每个名字在三键比较之下都可及，这正是严格良序的良基性定律。
<!--ja-->
最後の定理は三層の一行の合成です。名前 `a` が与えられると、コード順序自身の整礎性が `codeOf a` の到達可能性を与え、最外層がそれを `a` の到達可能性へ変換します。コードの等式は反射性により成立します。こうしてすべての名前は三つの鍵による比較のもとで到達可能となり、これが狭義整列順序の整礎性の法則です。
<!--/-->

```agda
      ihC b h = accAtCode (codeOf b) (rc (codeOf b) h) b refl

  ≺ₙ-wf : WellFounded _≺ₙ_
  ≺ₙ-wf a = accAtCode (codeOf a) (≺-wf (codeOf a)) a refl
```

<!--en-->
## The bundle, and the least name

The four laws say that the names carry a strict well-order, and packaging them into that structure's record is what lets the general least-element search consume them. Applied to this order, the search turns a merely inhabited family of names into a definite least member: this is precisely the purpose for which the names were built, since a family of sets over one stage becomes a family of names, and a family of names has a least member.
<!--zh-->
## 束，与最小的名字

四条定律说明诸名字带有严格良序，而把它们打包进该结构的记录，就能把这个序交给一般的极小元搜索。把这个序交给搜索，一族仅仅非空的名字就变成一个确定的极小元：构造诸名字的目的正在于此，因为单一层之上的一族集合成为一族名字，而一族名字有极小元。
<!--ja-->
## 整列順序と最小の名前

四つの法則は、名前全体が狭義整列順序を運ぶことを示します。それをその構造のレコードへまとめることで、一般の最小要素探索に渡せるようになります。この順序に探索を適用すると、単に非空な名前の族が確定した最小元へ変わります。名前を構成した目的はまさにここにあります。一つの段階の上の集合の族は名前の族になり、名前の族には最小元があるからです。
<!--/-->

<!--en-->
The record `nameOrder` collects the four laws already proved, field by field: the comparison itself, the trichotomy, irreflexivity, transitivity, and well-foundedness. Nothing new is proved here; the point of the bundle is that downstream constructions can consume a strict well-order without knowing how this one was assembled.
<!--zh-->
记录 `nameOrder` 把已证的四条定律逐场收拢：比较本身、三歧性、非自反性、传递性与良基性。这里没有证明任何新东西；打包的意义在于，后续构造可以直接使用一个严格良序，而无须知道这一个是如何拼装的。
<!--ja-->
レコード `nameOrder` は、すでに証明済みの四つの法則をフィールドごとに集めます。比較そのもの、三歧性、非反射性、推移性、そして整礎性です。ここで新たに証明されるものは何もありません。束の意味は、下流の構成がこの順序の組立方を知らずに狭義整列順序を消費できるようにすることにあります。
<!--/-->

```agda
  nameOrder : SWO (Name)
  nameOrder = record
    { _<∙_   = _≺ₙ_
    ; tri∙   = ≺ₙ-tri
    ; irr∙   = ≺ₙ-irr
```

<!--en-->
The least-element search takes the bundle at its word. Its family argument is a function into `hProp`, so the property is stated at each name; the hypothesis is the truncation `∥ Σ ... ∥₁`, mere inhabitedness, carrying no chosen witness; and the conclusion is an explicit pair of a name and its leastness, a chosen witness after all, extracted by `leastOf` with the module's classical hypothesis `lem`. The truncation may be eliminated because the whole type of a least witness, `Σ[ a ∈ Name ] IsLeast nameOrder P a`, is a proposition: any two least witnesses coincide by trichotomy. Thus classical descent converts mere inhabitation into a definite least name.
<!--zh-->
极小元搜索照字面兑现这份记录。它的族实参是映入 `hProp` 的函数，性质陈述在每个名字上；假设是截断 `∥ Σ ... ∥₁`，即仅仅非空，不携带任何被选出的见证；结论则是一对显式的名字与它的最小性，终究是被选出的见证，由 `leastOf` 借助模块的经典假设 `lem` 抽出。截断之所以能消去，是因为极小见证的整个类型 `Σ[ a ∈ Name ] IsLeast nameOrder P a` 是命题：任意两个极小见证由三歧性得到相等。因此经典下降把名字族的仅仅非空转化为一个确定的极小名字。
<!--ja-->
最小要素探索はこの束をその言葉どおりに使います。族の引数は `hProp` への関数なので、性質は各名前の上で述べられます。仮定は截断 `∥ Σ ... ∥₁`、つまり単に非空であることで、選ばれた証人を運びません。結論は名前とその最小性の明示的な対であり、結局は選ばれた証人で、`leastOf` がこのモジュールの古典的仮定 `lem` とともにこれを取り出します。切り捨てを除去できるのは、最小証人全体の型 `Σ[ a ∈ Name ] IsLeast nameOrder P a` が命題だからです。任意の二つの最小証人は三分性により一致します。したがって古典的降下が単なる非空性を確定した最小の名前へ変換します。
<!--/-->

```agda
    ; trans∙ = ≺ₙ-trans
    ; wf∙    = ≺ₙ-wf }

  leastName : (P : Name → hProp (ℓ-suc ℓ))
            → ∥ Σ[ a ∈ Name ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ Name ] IsLeast nameOrder P a
  leastName = leastOf nameOrder lem
```

<!--en-->
## Recap

Every successor-stage member now has a name, and the names carry a strict well-order, so a least representative can be selected. A `Name`{.Agda} is an arity, a parameter-free formula of one more variable, and a vector of parameters from the stage; `denote`{.Agda} is the subset it carves, and `denote-mem`{.Agda} states this in the inner semantics by which the definable powerset is defined. `names-complete`{.Agda} says every member of the successor stage is denoted by some name, and the existence claim is truncated, because that is how the definable powerset yields its formula in the first place.

`code∈limit`{.Agda} places the first key where the limit-stage order can compare it, and `code-inj`{.Agda} is injective after the arities have been aligned: equal codes then recover equal parameter-free formulas. `_≺ᵥ_`{.Agda} orders the third key across lengths, and `_≺ₙ_`{.Agda} is the three-key comparison itself, with all four strict-well-order laws and `leastName`{.Agda}, which returns the least name of a non-empty family. The combination is what the choice construction ahead consumes: a family of subsets of one stage becomes a family of names, and `leastName` picks a canonical representative without ever choosing a formula from the truncated completeness statement.
<!--zh-->
## 小结

现在，后继层的每个成员都有名字，而诸名字带有严格良序，因而可以选出最小代表。一个 `Name`{.Agda} 由一个元数、一条多一个变量的无参公式，以及一个取自该层的参数向量组成；`denote`{.Agda} 是它所界定的子集，而 `denote-mem`{.Agda} 在可定义幂集据以定义的内层语义中陈述这一点。`names-complete`{.Agda} 说明后继层的每个成员都由某个名字指称；该存在结论是截断的，因为可定义幂集本来就是这样给出它的公式的。

`code∈limit`{.Agda} 把第一个键放到极限层那个序可以比较它的地方，而 `code-inj`{.Agda} 在元数对齐后保证编码单射：此时相等的码还原出相等的无参公式。`_≺ᵥ_`{.Agda} 跨长度地为第三个键排序，而 `_≺ₙ_`{.Agda} 就是三键比较本身，连同严格良序的全部四条定律，以及 `leastName`{.Agda}，即非空族的最小名字。两者的组合正是后续选择构造所消费的：单一层之上的一族子集成为一族名字，而 `leastName` 选出一个典范代表，自始至终不必从截断的完备性陈述里挑选公式。
<!--ja-->
## まとめ

これで後続段階の各要素は名前をもち、名前全体には狭義整列順序が入ったので、最小の代表を選べます。`Name`{.Agda} は、アリティ、変数を一つ多くもつパラメータなし論理式、段階から取ったパラメータ列の三つ組です。`denote`{.Agda} はそれが切り出す部分集合であり、`denote-mem`{.Agda} は定義可能冪集合の基礎となる内側の意味論でこれを述べます。`names-complete`{.Agda} は後続段階の各要素が何らかの名前によって指示されることを言い、その存在主張は截断された形です。定義可能冪集合がそもそもそのように論理式を与えるからです。

`code∈limit`{.Agda} は第一の鍵を、極限段階の順序が比較できる場所へ置き、`code-inj`{.Agda} はアリティを揃えた後の符号化が単射であることを示します。そのとき、等しいコードから等しいパラメータなし論理式が復元されます。`_≺ᵥ_`{.Agda} は第三の鍵を長さを越えて順序づけ、`_≺ₙ_`{.Agda} は三つの鍵による比較そのものであり、狭義整列順序の四つの法則すべてと、非空族の最小の名前を返す `leastName`{.Agda} を伴います。この組み合わせこそ、後の選択構成が用いるものです。一つの段階の上の部分集合の族は名前の族となり、`leastName` が正準な代表を選びます。その間、截断された完全性の主張から論理式を選び出すことは一度もありません。
<!--/-->
