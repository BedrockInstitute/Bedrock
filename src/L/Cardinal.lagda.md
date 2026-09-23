<!--en-->
# Cardinals and coded injections inside L
<!--zh-->
# L 内部的基数与编码单射
<!--ja-->
# L の内部における基数と符号化された単射
<!--/-->

<!--en-->
Cardinality in `L` requires two related kinds of comparison. The host can compare the small types that present sets by actual functions, while a statement made inside `L` must be witnessed by a graph that is itself constructible. This chapter develops both notions and keeps their logical strength visible: concrete functions and graph codes carry data, whereas the cardinal comparisons used later retain only existence.
<!--zh-->
讨论 `L` 内部的基数，需要区分两种相互关联的比较。宿主可以用实际函数比较集合的小呈现类型；在 `L` 内部作出的陈述，则必须由本身可构造的图来见证。本章同时发展这两种概念，并明确保留它们的逻辑强度：具体函数与图码携带数据，后文所用的基数比较则只保留存在性。
<!--ja-->
`L` の内部で基数を論じるには、互いに関係する二種類の比較を区別する必要がある。ホストでは集合を提示する小さな型を実際の関数で比較できるが、`L` の内部で述べる主張は、それ自身が構成可能なグラフによって証されなければならない。本章では両方の概念を展開し、それぞれの論理的な強さを明確に保つ。具体的な関数とグラフの符号はデータを持ち、後で使う基数の比較は存在だけを保持する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
The argument is carried out in the host language described in the prelude. Its one classical resource is excluded middle for propositions in `Type (ℓ-suc ℓ)`. This is a level-bounded assumption, not an unrestricted excluded-middle or choice principle. The definitions of injections and graph codes do not themselves select witnesses; classical reasoning becomes relevant to the ordinal well-order and to the least-element arguments that use it later.
<!--zh-->
论证在基础词汇章所介绍的宿主语言中进行。它唯一的经典资源，是对 `Type (ℓ-suc ℓ)` 中命题的排中律。这是一条受宇宙层级限制的假设，并非不受限制的排中律或选择原理。单射与图码的定义本身并不选取见证；经典推理在构造序数良序，以及后文利用该良序寻找最小元时才发挥作用。
<!--ja-->
議論は基礎語彙の章で説明したホスト言語の中で行う。用いる古典的な原理は、`Type (ℓ-suc ℓ)` にある命題に対する排中律だけである。これは宇宙レベルで制限された仮定であり、無制限の排中律や選択原理ではない。単射やグラフの符号の定義自体は証人を選ばない。古典的な推論が働くのは、順序数の整列順序を構成するときと、後でその順序から最小元を得るときである。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The universe level and this instance of excluded middle are therefore displayed as parameters of the whole chapter. Every construction below is relative to the same `lem`; no additional axiom is introduced along the way. The goal here is to prepare the precise notions and bounded order needed for later cardinal arguments, rather than to assert the existence of a cardinal representative or a successor cardinal already.
<!--zh-->
因此，宇宙层级和这份排中律实例都明列为整章的参数。下面每项构造都相对于同一个 `lem`，途中不再加入其他公理。本章的目标是为后续基数论证准备精确的概念与有界次序，而不是已经断言基数代表或后继基数的存在。
<!--ja-->
そこで、宇宙レベルとこの排中律の実例を章全体のパラメータとして明示する。以下の構成はすべて同じ `lem` に相対しており、途中で別の公理を加えることはない。ここでの目的は、後の基数論に必要な正確な概念と有界な順序を準備することである。基数代表や後続基数の存在を、この時点で主張するわけではない。
<!--/-->

```agda
module L.Cardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
Two mathematical settings will remain in view. The cumulative hierarchy supplies ambient sets and proposition-valued membership. The constructible model will supply the sets that belong to `L` and the relations interpreted over them. The elementary fact `a ∈ sucV a`, saying that every set belongs to its set-theoretic successor `a ∪ {a}`, will later provide a distinguished point in a bounded search.
<!--zh-->
后文始终同时涉及两种数学环境。累积层级提供外围集合以及取命题值的隶属关系；可构造模型则提供属于 `L` 的集合，以及在这些集合上解释的关系。基本事实 `a ∈ sucV a` 表明每个集合都属于其集合论后继 `a ∪ {a}`，它稍后会为一次有界搜索提供一个特定点。
<!--ja-->
以下では二つの数学的な場を同時に扱う。累積階層は周囲の集合と命題値の所属を与え、構成可能モデルは `L` に属する集合と、その上で解釈される関係を与える。基本的な事実 `a ∈ sucV a` は、すべての集合が集合論的後続 `a ∪ {a}` に属すことを表し、後で有界な探索のための特定の点を与える。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
```

<!--en-->
An ambient set also has a canonical small presentation. Its indices name all of its members, `member` turns an index into membership, and `fiber` recovers an index from membership. Ordered pairs let a set represent a relation. On the constructible side, an element of the model pairs an ambient set with a certificate that it belongs to `L`; transitivity of `L` then carries constructibility from a set to each of its members. These facts will connect small presentations with constructible graph codes.
<!--zh-->
每个外围集合还有一个典范的小呈现。呈现中的索引指名该集合的全部成员，`member` 把索引化为隶属证明，`fiber` 则从隶属恢复索引。有序对使一个集合能够表示关系。在可构造一侧，模型元素把外围集合与其属于 `L` 的证书配成一对；`L` 的传递性又把可构造性从集合传给它的每个成员。这些事实将把小呈现与可构造的图码联系起来。
<!--ja-->
周囲の各集合には標準的な小さな提示もある。そのインデックスは集合のすべての要素を名指し、`member` はインデックスを所属証明へ変え、`fiber` は所属からインデックスを復元する。順序対を使えば、集合で関係を表せる。構成可能な側では、モデルの要素は周囲の集合と、それが `L` に属すことの証明を組にしたものである。さらに `L` の推移性により、集合の構成可能性はその各要素へ受け継がれる。これらの事実が、小さな提示と構成可能なグラフの符号を結び付ける。
<!--/-->

```agda
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
```

<!--en-->
The bounded search will use the strict well-order induced by ordinal membership on a presentation. Its trichotomy ultimately uses `lem`, while its well-foundedness comes from regularity of ambient membership. The other ingredients describe graphs inside the object language: single-valuedness, exact domain, and injectivity. Keeping these order-theoretic and logical ingredients distinct will matter when a concrete graph code is later hidden by propositional truncation.
<!--zh-->
有界搜索将使用序数隶属关系在呈现上诱导的严格良序。它的三歧性最终使用 `lem`，良基性则来自外围隶属关系满足正则公理。另一些材料在对象语言中描述图的性质：单值性、恰当定义域与单射性。稍后用命题截断隐藏具体图码时，区分这些序论材料与逻辑材料十分重要。
<!--ja-->
有界な探索には、順序数の所属が提示上に誘導する狭義の整列順序を使う。その三分性は最終的に `lem` を用い、整礎性は周囲の所属の正則性から得られる。ほかの材料は、一価性、正確な定義域、単射性というグラフの性質を対象言語で記述する。後で具体的なグラフの符号を命題的切り詰めによって隠すとき、順序に関する材料と論理式に関する材料を区別することが重要になる。
<!--/-->

```agda
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
```

<!--en-->
For a set `a`, write `⟪ a ⟫` for the small type indexing its members and `⟪ a ⟫↪` for the map sending an index to the member it names. The set-theoretic successor `sucV a` contains every member of `a` and also `a` itself. Thus `⟪ sucV a ⟫` is a small search space containing indices for all smaller ordinals when `a` is an ordinal, together with an index naming `a`.
<!--zh-->
对集合 `a`，以 `⟪ a ⟫` 表示索引其成员的小类型，以 `⟪ a ⟫↪` 表示把索引送到其所指成员的映射。集合论后继 `sucV a` 包含 `a` 的每个成员，也包含 `a` 本身。因此，当 `a` 是序数时，`⟪ sucV a ⟫` 是一个小搜索空间，其中既有指名所有更小序数的索引，也有指名 `a` 的索引。
<!--ja-->
集合 `a` に対し、その要素を添字付ける小さな型を `⟪ a ⟫`、インデックスをそれが名指す要素へ送る写像を `⟪ a ⟫↪` と書く。集合論的後続 `sucV a` は `a` のすべての要素と `a` 自身を含む。したがって `a` が順序数なら、`⟪ sucV a ⟫` は、すべてのより小さい順序数を名指すインデックスと `a` を名指すインデックスを含む、小さな探索空間である。
<!--/-->

```agda

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
```

<!--en-->
Existence inside this development is often deliberately weakened by propositional truncation. A term of `∥ X ∥₁` states that `X` is inhabited but does not reveal an inhabitant. It may be eliminated into a proposition, such as the empty type used for a refutation, but not into arbitrary data. This rule will separate the concrete graph information in `InjCode` from the mere existence asserted by `InjL`.
<!--zh-->
本书常用命题截断有意减弱存在性。`∥ X ∥₁` 的元素断言 `X` 有元素，却不透露具体元素。它可以消去到命题，例如用来表达反驳的空类型，却不能消去到任意数据。这条规则稍后会把 `InjCode` 中的具体图信息与 `InjL` 所断言的单纯存在严格区分开来。
<!--ja-->
本書では、存在を命題的切り詰めによって意図的に弱めることがよくある。`∥ X ∥₁` の要素は `X` に要素があることを主張するが、具体的な要素は明らかにしない。反証を表す空型のような命題へは消去できるが、任意のデータへは消去できない。この規則により、後で `InjCode` に含まれる具体的なグラフの情報と、`InjL` が述べる単なる存在が厳密に区別される。
<!--/-->



<!--en-->
The notation now records which setting a statement belongs to. For the ambient
structure, `_∈ˢ_` is proposition-valued membership between raw hierarchy sets.
By contrast, `S` is the carrier of the constructible structure: an element
`a : S` has an underlying ambient set `fst a` and a proposition-valued
certificate of its constructibility. Thus `⟨ fst x ∈ˢ fst a ⟩` is a host-level
proposition about underlying ambient sets, while a quantifier over `x : S`
ranges only over constructible sets. Object-language syntax enters separately
through the satisfaction relation introduced below.
<!--zh-->
下面的记号标明一条陈述属于哪种环境。对外围结构，`_∈ˢ_` 是层级中裸集合之间取命题值的隶属关系。与此相对，`S` 是可构造结构的载体；元素 `a : S` 由底层外围集合 `fst a` 与其可构造性的命题值证书组成。因此，`⟨ fst x ∈ˢ fst a ⟩` 是关于底层外围集合的宿主层命题，而对 `x : S` 的量化只遍历可构造集合。对象语言的语法则通过下面引入的满足关系另行进入。
<!--ja-->
以下の記法は、主張がどちらの場に属すかを示す。周囲の構造では、`_∈ˢ_` は階層の生の集合どうしの命題値をもつ所属関係である。これに対して `S` は構成可能な構造の台であり、要素 `a : S` は、底にある周囲の集合 `fst a` と、その構成可能性を示す命題値の証明からなる。したがって `⟨ fst x ∈ˢ fst a ⟩` は底の周囲の集合に関するホスト側の命題であり、`x : S` 上の量化は構成可能集合だけにわたる。対象言語の構文は、以下で導入する充足関係を通して別に現れる。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
The constructible structure also has a proposition-valued pointwise subset
relation. A proof of `⟨ a ⊆ˢ b ⟩` takes each `x : S` and sends membership in
`a` to membership in `b`; its quantifier therefore ranges over the
constructible carrier. Transitivity of `L` ensures that this has the expected
subset reading for the underlying sets. When `a` and `b` are ordinals, it is
their non-strict order. That is why the minimality clause for a successor
cardinal concludes by containment, while strict comparison is expressed by
membership.
<!--zh-->
可构造结构还带有取命题值的逐点包含关系。`⟨ a ⊆ˢ b ⟩` 的证明对每个 `x : S`，把 `x` 属于 `a` 的证明送到 `x` 属于 `b` 的证明；其中的量化因此遍历可构造载体。`L` 的传递性保证这与底层集合通常的包含读法一致。当 `a` 与 `b` 都是序数时，这正是它们的非严格次序。因此，后继基数的最小性条款以包含为结论，而严格比较则用隶属关系表达。
<!--ja-->
構成可能な構造には、命題値をもつ点ごとの部分集合関係もある。`⟨ a ⊆ˢ b ⟩` の証明は、各 `x : S` について、`x` が `a` に属するという証明を `x` が `b` に属するという証明へ送る。したがって、その量化は構成可能な台にわたる。`L` の推移性により、これは底にある集合について通常の部分集合関係として読める。`a` と `b` が順序数なら、これは両者の非狭義の順序である。そのため、後続基数の最小性は包含を結論とし、狭義の比較は所属で表す。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )
```

<!--en-->
The satisfaction symbol `_⊨_` is fixed to the interpretation in the constructible structure. In a judgment `γ ⊨ φ`, the environment `γ` lists elements of `S`, so the unbounded quantifiers in `φ` range over constructible sets. This is the semantic content of the first three conditions in `InjCode`; they are object-language statements true inside `L`, even though their proofs are handled in the host.
<!--zh-->
满足记号 `_⊨_` 固定表示可构造结构中的解释。在判断 `γ ⊨ φ` 中，环境 `γ` 列出 `S` 的元素，所以 `φ` 中的无界量词遍历可构造集合。这正是 `InjCode` 前三个条件的语义内容；它们是在 `L` 内部成立的对象语言陈述，尽管其证明由宿主处理。
<!--ja-->
充足の記号 `_⊨_` は、構成可能な構造における解釈を表すものとして固定する。判断 `γ ⊨ φ` では、環境 `γ` は `S` の要素を並べるため、`φ` の非有界量化子は構成可能集合にわたる。これが `InjCode` の最初の三条件の意味である。それらは `L` の内部で成り立つ対象言語の主張であり、その証明自体はホストで扱われる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
We first define an injection entirely at the host level. An element of `X ↪ Y` consists of a function `f : X → Y` together with a proof that equality of `f x` and `f y` implies equality of `x` and `y`. The function is concrete data and can be projected from the pair. No surjectivity or inverse is included, and no set, constructibility certificate, satisfaction judgment, or truncation occurs in this definition. Later its typical endpoints are the small presentation types of two ambient sets.
<!--zh-->
首先在宿主层定义单射。`X ↪ Y` 的元素由函数 `f : X → Y` 及其单射性证明组成；该证明表明，`f x` 与 `f y` 相等便推出 `x` 与 `y` 相等。函数是可以从这对数据中投影出的具体数据。定义不包含满射性或逆函数，也不涉及集合、可构造性证书、满足判断或截断。稍后，它的典型两端是两个外围集合的小呈现类型。
<!--ja-->
まず、ホストレベルだけで単射を定義する。`X ↪ Y` の要素は関数 `f : X → Y` とその単射性の証明からなり、その証明は `f x` と `f y` の等しさから `x` と `y` の等しさが従うことを述べる。関数は具体的なデータなので、この対から射影できる。全射性や逆関数は含まれず、集合、構成可能性の証明、充足の判断、切り詰めもこの定義には現れない。後では、二つの周囲の集合を表す小さな提示型が典型的な始域と終域になる。
<!--/-->

```agda
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)
```

<!--en-->
Now fix a constructible set `α` whose underlying set is an ordinal. To look later for a suitable ordinal no larger than necessary, it suffices to work in the canonical presentation of `sucV (fst α)`. This set contains every member of `α` and `α` itself, so the search is both small and equipped with a natural starting point. The definitions here build this ordered search space; later arguments provide a candidate predicate and perform the least-element selection.
<!--zh-->
现在固定一个可构造集合 `α`，并假设其底层集合是序数。为了稍后寻找大小合适的序数，只需在 `sucV (fst α)` 的典范呈现中搜索。这个集合包含 `α` 的每个成员及 `α` 本身，所以搜索空间既是小类型，又带有一个自然起点。此处的定义只建立这个带序的搜索空间；后续论证才会给出候选谓词并执行最小元选择。
<!--ja-->
ここで、底にある集合が順序数である構成可能集合 `α` を固定する。後で必要な大きさの順序数を探すには、`sucV (fst α)` の標準的な提示の中で探索すれば十分である。この集合は `α` のすべての要素と `α` 自身を含むので、探索空間は小さな型であると同時に自然な始点を持つ。ここでの定義が作るのは、この順序付けられた探索空間である。候補の述語を与えて最小元を選ぶのは後の議論である。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
The first obligation is to show that this set-theoretic successor itself belongs to `L`. From `oα`, two applications of ordinal successor show that `sucV (sucV (fst α))` is an ordinal. The theorem that an ordinal belongs to the next constructible stage places `sucV (fst α)` in that named stage, and membership in a stage yields its constructibility. Thus the proof identifies a specific stage containing the successor; it does not appeal to a general closure of constructibility under `sucV`.
<!--zh-->
第一项任务是证明这个集合论后继本身属于 `L`。由 `oα` 两次应用序数后继，可知 `sucV (sucV (fst α))` 是序数。序数属于下一可构造层的定理把 `sucV (fst α)` 放入这个明确给出的层，而属于某一层便给出其可构造性。因此，证明指明了一个包含该后继的具体层，并未诉诸「可构造性一般地对 `sucV` 封闭」这样的结论。
<!--ja-->
最初に、この集合論的後続自身が `L` に属すことを示す。`oα` に順序数の後続を二度適用すると、`sucV (sucV (fst α))` が順序数だと分かる。順序数が次の構成可能な段階に属すという定理により、`sucV (fst α)` はこの明示された段階に入り、ある段階への所属からその構成可能性が得られる。したがって、この証明は後続を含む具体的な段階を示しており、構成可能性が一般に `sucV` について閉じているという性質を仮定してはいない。
<!--/-->

```agda
  hSucα : ⟨ isL (sucV (fst α)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst α))) (suc-ord (suc-ord oα)) (sucV (fst α))
            (ord∈Lset-suc (sucV (fst α)) (suc-ord oα))
```

<!--en-->
Every index `m` in the presentation names a member of `sucV (fst α)`. Since that successor is constructible and `L` is transitive, the named member is constructible as well. The map `up` therefore keeps the underlying set named by `m` and adds precisely this certificate, producing an element of `S`. It is defined only on this bounded presentation and does not turn arbitrary ambient sets into constructible ones.
<!--zh-->
呈现中的每个索引 `m` 都指名 `sucV (fst α)` 的一个成员。这个后继已经证明可构造，而 `L` 具有传递性，所以被指名的成员也可构造。于是 `up` 保留 `m` 所指名的底层集合，并附上恰好由此得到的证书，从而产生 `S` 的元素。它只定义在这个有界呈现上，并不会把任意外围集合变成可构造集合。
<!--ja-->
提示の各インデックス `m` は `sucV (fst α)` の要素を名指す。この後続は構成可能であり、`L` は推移的なので、名指された要素も構成可能である。そこで `up` は、`m` が名指す底の集合を保ち、この事実から得た証明を添えて `S` の要素を作る。この写像はこの有界な提示上だけで定義され、任意の周囲の集合を構成可能集合へ変えるものではない。
<!--/-->

```agda
  up : ⟪ sucV (fst α) ⟫ → S
  up m = ⟪ sucV (fst α) ⟫↪ m
       , isL-trans (member (sucV (fst α)) m) hSucα
```

<!--en-->
Ordinal membership orders these indices. Applying `ordSWO` to the ordinal `sucV (fst α)` gives a strict well-order `w` on `⟪ sucV (fst α) ⟫`: its comparison follows membership between the named sets, its trichotomy depends on `lem`, and its well-foundedness follows from regularity. Declaring the value opaque controls later unfolding without changing the relation, its laws, or the assumptions on which they rest.
<!--zh-->
序数的隶属关系为这些索引排序。把 `ordSWO` 应用于序数 `sucV (fst α)`，便在 `⟪ sucV (fst α) ⟫` 上得到严格良序 `w`：它依照所指集合之间的隶属关系作比较，三歧性依赖 `lem`，良基性则来自正则公理。把这个值声明为不透明，只控制它在后续证明中是否展开，并不改变该关系、它的定律或这些定律所依赖的假设。
<!--ja-->
順序数の所属によって、これらのインデックスを順序付ける。順序数 `sucV (fst α)` に `ordSWO` を適用すると、`⟪ sucV (fst α) ⟫` 上の狭義の整列順序 `w` が得られる。この比較は名指された集合どうしの所属に従い、三分性は `lem` に依存し、整礎性は正則性から従う。この値を不透明にする指定は、後の証明での展開を制御するだけであり、関係、その法則、あるいは法則が依存する仮定を変えない。
<!--/-->

```agda
  opaque
    w : SWO (⟪ sucV (fst α) ⟫)
    w = ordSWO (sucV (fst α)) (suc-ord oα)
```

<!--en-->
The usable description of this order is the path `w-lt`. For indices `m` and `n`, the proposition that `m` precedes `n` under `w` is identified with the proposition that the set named by `m` belongs to the set named by `n`. This is an equality of proposition types, not an equality of sets. It lets later proofs transport evidence in either direction between an index comparison and ordinal membership without unfolding the construction of the well-order.
<!--zh-->
路径 `w-lt` 给出这个次序的可用描述。对索引 `m` 与 `n`，「`m` 在 `w` 下先于 `n`」这一命题，与「`m` 所指集合属于 `n` 所指集合」这一命题相等。这是命题类型之间的相等，并非集合之间的相等。后续证明可沿这条路径双向传输证据，在索引比较与序数隶属之间往返，同时无需展开良序的构造。
<!--ja-->
パス `w-lt` が、この順序の利用可能な記述を与える。インデックス `m` と `n` に対し、`w` のもとで `m` が `n` に先行するという命題は、`m` が名指す集合が `n` の名指す集合に属すという命題と同一視される。これは命題型どうしの等しさであり、集合どうしの等しさではない。後の証明はこのパスに沿って、インデックスの比較と順序数の所属の間で証拠を両方向に移せる。その際、整列順序を展開する必要はない。
<!--/-->

```agda
  opaque
    unfolding w
    w-lt : (m n : ⟪ sucV (fst α) ⟫)
         → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ ⟪ sucV (fst α) ⟫↪ n ⟩
    w-lt m n = refl
```

<!--en-->
The search space has a distinguished index naming `fst α`. The proof `self∈sucV (fst α)` supplies membership of the ordinal in its set-theoretic successor, and `fiber` turns that membership into an index together with an equation describing its image. Although hierarchy membership is proposition-valued, the fiber of the presentation map is itself a proposition because the map is an embedding; truncation can therefore be eliminated into that unique fiber without invoking a choice principle. The term `self` is the recovered index, not the ordinal.
<!--zh-->
这个搜索空间有一个指名 `fst α` 的特定索引。证明 `self∈sucV (fst α)` 给出该序数属于其集合论后继，而 `fiber` 把这条隶属化为一个索引以及描述其像的等式。层级中的隶属虽然取命题值，但呈现映射是嵌入，所以它的纤维本身是命题；因此可以把截断消去到这个唯一纤维，而无须调用选择原理。`self` 是由此恢复的索引，并不是该序数。
<!--ja-->
この探索空間には、`fst α` を名指す特定のインデックスがある。証明 `self∈sucV (fst α)` は順序数がその集合論的後続に属すことを与え、`fiber` はその所属を、インデックスとその像を記述する等式の組へ変える。階層の所属は命題値であるが、提示写像は埋め込みなので、そのファイバー自体が命題である。したがって選択原理を用いずに、切り詰めをこの一意なファイバーへ消去できる。`self` はこうして復元されたインデックスであり、順序数そのものではない。
<!--/-->

```agda

  self : ⟪ sucV (fst α) ⟫
  self = fiber (sucV (fst α)) (self∈sucV (fst α)) .fst
```

<!--en-->
The companion equation states exactly what `self` names: its image under the presentation map is `fst α`. The equality is between underlying ambient sets. No equality of the corresponding elements of `S` is asserted here, since that would also have to identify their constructibility certificates. Together, `self` and `self-eq` give later searches a concrete index at which a property of `α` can be checked.
<!--zh-->
伴随等式准确说明 `self` 指名什么：它在呈现映射下的像等于 `fst α`。这条相等发生在底层外围集合之间；此处没有断言相应 `S` 元素相等，因为那还需要处理两边的可构造性证书。`self` 与 `self-eq` 合在一起，为后续搜索提供一个可以检验 `α` 之性质的具体索引。
<!--ja-->
付随する等式は、`self` が何を名指すかを正確に述べる。提示写像によるその像は `fst α` に等しくなる。この等式は底にある周囲の集合どうしのものであり、対応する `S` の要素どうしの等しさまでは主張しない。後者には構成可能性の証明も同一視する必要があるからである。`self` と `self-eq` を合わせると、後の探索で `α` の性質を調べるための具体的なインデックスが得られる。
<!--/-->

```agda
  self-eq : ⟪ sucV (fst α) ⟫↪ self ≡ fst α
  self-eq = fiber (sucV (fst α)) (self∈sucV (fst α)) .snd
```
</div>
</details>


<!--en-->
## Internal injections and successor cardinals
<!--zh-->
## 内部单射与后继基数
<!--ja-->
## 内部の単射と後続基数
<!--/-->

<!--en-->
A concrete constructible set `F` begins to code an injection from `a` to `b` through three satisfaction conditions inside `L`. The first says that pair-shaped entries are single-valued: one input cannot have two unequal outputs. The second says that the domain is exactly `a`, in both directions: the first coordinate of every pair-shaped entry belongs to `a`, and every member of `a` merely has an output. The third says that the graph is injective: two entries with the same output have equal inputs. In all three judgments, the environment places `F` first and `a` second, and every unbounded quantifier ranges over `S`.
<!--zh-->
一个具体的可构造集合 `F`，首先通过 `L` 内部的三条满足条件来编码从 `a` 到 `b` 的单射。第一条说成对形状的条目具有单值性：同一输入不能有两个不相等的输出。第二条说定义域恰为 `a`，而且包含两个方向：每个成对形状条目的第一分量属于 `a`，`a` 的每个成员则仅仅存在某个输出。第三条说图具有单射性：输出相同的两个条目必有相等的输入。在三条判断中，环境都把 `F` 放在第一项、`a` 放在第二项，所有无界量词都遍历 `S`。
<!--ja-->
具体的な構成可能集合 `F` は、まず `L` の内部での三つの充足条件によって、`a` から `b` への単射を符号化する。第一の条件は、対の形をした項目が一価であること、つまり同じ入力が異なる二つの出力を持たないことを述べる。第二の条件は、定義域が正確に `a` であることを両方向に述べる。対の形をした各項目の第一成分は `a` に属し、`a` の各要素には出力が単に存在する。第三の条件はグラフの単射性、つまり出力が同じ二つの項目の入力が等しいことを述べる。三つの判断では、環境の第一項が `F`、第二項が `a` であり、すべての非有界量化子は `S` にわたる。
<!--/-->

```agda
InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
```

<!--en-->
The fourth condition is stated directly in the host. For any `x,y : S`, if the ordered pair of their underlying sets belongs to the underlying graph, then the underlying output belongs to `b`. Thus `b` is a codomain bound for the values; the condition does not say that every member of `b` is attained. Nor does `InjCode` assert that every member of `F` is an ordered pair. Its conditions inspect pair-shaped members, so additional members of another shape do not affect the function read from the code. This host-level range condition must therefore be distinguished from the preceding three object-language satisfaction judgments.
<!--zh-->
第四条条件直接在宿主中陈述。对任意 `x,y : S`，若它们的底层集合组成的有序对属于底层图，则底层输出属于 `b`。因此，`b` 是所有取值的陪域上界；条件并不说 `b` 的每个成员都被取到。`InjCode` 也没有断言 `F` 的每个成员都是有序对。它的条件只检查成对形状的成员，所以其他形状的附加成员不会影响从图码读出的函数。这个宿主层的值域约束必须与前三条对象语言满足判断区分开来。
<!--ja-->
第四の条件はホストで直接述べられる。任意の `x,y : S` に対し、底にある集合の順序対が底のグラフに属すなら、底にある出力は `b` に属する。したがって `b` は値の終域となる上界であり、`b` のすべての要素が値として取られるとは述べない。また `InjCode` は、`F` のすべての要素が順序対であるとも主張しない。その条件が調べるのは対の形をした要素だけなので、別の形をした余分な要素は符号から読み出される関数に影響しない。このホストレベルの値域条件は、先の三つの対象言語における充足の判断と区別する必要がある。
<!--/-->

```agda
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)
```

<!--en-->
`InjL a b` forgets which concrete graph supplies these four conditions. It is the propositional truncation of the dependent pair consisting of `F` and `InjCode F a b`, so it states merely that a coded injection from `a` to `b` exists inside `L`. A particular graph or host-level function cannot be projected from it. It may be opened locally only when the target is a proposition; later constructions that compose or transform injections work with the graph inside such a branch and place the resulting graph back under truncation. The direction is part of the statement: `InjL a b` says nothing by itself about `InjL b a`.
<!--zh-->
`InjL a b` 忘去是哪一个具体图满足这四条条件。它是依值对「`F` 与 `InjCode F a b`」的命题截断，所以只断言在 `L` 内部存在从 `a` 到 `b` 的编码单射。无法从中投影出特定图或宿主层函数。只有当目标是命题时，才能在局部分支中打开它；后续对单射作复合或变换的构造，会在这样的分支内使用图，再把所得图放回命题截断。方向也是陈述的一部分：`InjL a b` 本身并不蕴含 `InjL b a`。
<!--ja-->
`InjL a b` は、四つの条件をどの具体的なグラフが満たすかを忘れる。これは `F` と `InjCode F a b` からなる依存対の命題的切り詰めなので、`L` の内部に `a` から `b` への符号化された単射が単に存在することだけを述べる。特定のグラフやホストレベルの関数を射影することはできない。これを局所的に開けるのは目標が命題である場合だけである。後で単射を合成したり変換したりする構成は、そのような枝の中でグラフを使い、得られたグラフを再び命題的切り詰めに入れる。向きも主張の一部であり、`InjL a b` だけから `InjL b a` は何も分からない。
<!--/-->

```agda
InjL : S → S → Type (ℓ-suc ℓ)
InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
```

<!--en-->
For an ordinal `κ`, cardinality is expressed by initiality. Every member `δ`
of a von Neumann ordinal is a smaller ordinal, and `IsCardinalL κ` refutes the
propositionally truncated existence of a constructible graph satisfying
`InjCode F κ δ`. In the notation just defined, it rules out `InjL κ δ`; it
does not rule out `InjL δ κ`. These are internal coded-injection propositions,
not instances of the host-level type `_↪_`, and the latter cannot in general be
extracted from their truncations. The definition can also be formed for a
general constructible set and contains no proof that `κ` is an ordinal; later
uses supply `IsOrd (fst κ)` separately before giving it the initial-ordinal
interpretation. Since a refutation has the empty type as its target, any needed
elimination of the propositional truncation is legitimate.
<!--zh-->
当 `κ` 是序数时，基数性由初始性表达。冯·诺伊曼序数的每个成员 `δ` 都是更小的序数，而 `IsCardinalL κ` 反驳「存在满足 `InjCode F κ δ` 的可构造图」这一命题截断。用刚定义的记号说，它排除 `InjL κ δ`，并不排除 `InjL δ κ`。这两个都是内部编码单射的命题，不是宿主层类型 `_↪_` 的实例；一般也不能从它们的截断中抽取后一种宿主层单射。这一定义也可对一般可构造集合形成，其中没有 `κ` 为序数的证明；后续使用处会另行提供 `IsOrd (fst κ)`，然后才作初始序数的解释。由于反驳以空类型为目标，所需的命题截断消去是正当的。
<!--ja-->
`κ` が順序数であるとき、基数性は始順序数であることによって表される。von Neumann 順序数の各要素 `δ` はより小さい順序数であり、`IsCardinalL κ` は、`InjCode F κ δ` を満たす構成可能なグラフが存在するという命題的切り詰めを反証する。直前の記法で言えば、排除されるのは `InjL κ δ` であり、`InjL δ κ` ではない。これらは内部の符号化された単射を表す命題であって、ホストレベルの型 `_↪_` の実例ではなく、その切り詰めから後者のホストレベルの単射を一般に取り出すこともできない。この定義は一般の構成可能集合についても形成でき、`κ` が順序数であるという証明を含まない。後の使用箇所では `IsOrd (fst κ)` を別に与えてから、始順序数として解釈する。反証の行き先は空型なので、必要となる命題的切り詰めの消去は正当である。
<!--/-->

```agda
IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → ⊥₀)
```

<!--en-->
The arguments of `SuccCardL δ κ` are ordered so that `δ` is the proposed successor cardinal and `κ` is the object it lies above. The first three clauses say that the underlying set of `δ` is an ordinal, that `δ` satisfies the initiality predicate, and that `κ ∈ δ`, hence that `δ` lies strictly above `κ` in the ordinal setting. These clauses describe a property of a given pair and do not produce such a `δ`; they also do not require `κ` itself to be an ordinal or a cardinal. The continuation adds the remaining global minimality clause. No `sucV` occurs here: a successor cardinal is not the set-theoretic successor `κ ∪ {κ}`.
<!--zh-->
`SuccCardL δ κ` 的参数次序规定，`δ` 是候选后继基数，`κ` 是它所超越的对象。前三个条款分别说：`δ` 的底层集合是序数，`δ` 满足初始性谓词，并且 `κ ∈ δ`；在序数语境中，最后一点表示 `δ` 严格大于 `κ`。这些条款只描述给定一对对象的性质，并不产生这样的 `δ`，也不要求 `κ` 本身是序数或基数。定义的最后一个条款还会加入全局最小性。这里没有出现 `sucV`：后继基数不是集合论后继 `κ ∪ {κ}`。
<!--ja-->
`SuccCardL δ κ` の引数の順序では、`δ` が候補となる後続基数であり、`κ` がそれより下にある対象である。最初の三条件は、`δ` の底にある集合が順序数であること、`δ` が始順序数を表す述語を満たすこと、そして `κ ∈ δ`、すなわち順序数の文脈で `δ` が `κ` より真に大きいことを述べる。これらは与えられた対の性質を記述するだけで、そのような `δ` を作るものではなく、`κ` 自身が順序数や基数であることも要求しない。定義の最後の条件が、さらに大域的な最小性を加える。ここに `sucV` は現れない。後続基数は集合論的後続 `κ ∪ {κ}` ではない。
<!--/-->

```agda
SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsOrd (fst δ)
  × IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
```

<!--en-->
The final field expresses minimality among all internal ordinal cardinals above `κ`. Given any `c : S` whose underlying set is an ordinal, which satisfies `IsCardinalL c`, and which contains `κ`, it returns the internal inclusion `δ ⊆ˢ c`. The first field has already established that `δ` is an ordinal, so inclusion is the non-strict ordinal comparison: `δ` lies at or below every such `c`. Inclusion rather than membership is essential here, since the conclusion must also hold when `c` is `δ` itself. Both the quantifier over `S` and `_⊆ˢ_` belong to the constructible carrier, so this is minimality among the candidates visible in `L`. The field assumes only `κ ∈ c`; hypotheses saying that `κ` is itself an ordinal and an internal cardinal are supplied at the theorems that use this predicate.

No injection graph is constructed by this field. `InjCode F a b` retains a particular constructible code `F` together with its four injection conditions, whereas `InjL a b` is the propositional truncation `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`. Thus the hypothesis `IsCardinalL c`, when combined with the ordinal hypothesis on `c`, says that `c` cannot merely admit such a coded injection into any smaller ordinal belonging to it. `SuccCardL δ κ` is itself an untruncated property of the fixed pair `δ, κ`: it neither proves that a suitable `δ` exists nor chooses one. Later, `succCardExists` proves the propositionally truncated existence of such a `δ` when `κ` is an ordinal internal cardinal and is not finite, using only the module's assumption `LEM (ℓ-suc ℓ)`. The set-theoretic successor `sucV` does not occur in this definition.
<!--zh-->
最后一个字段表达 `κ` 之上所有内部序数基数中的最小性。给定任意 `c : S`，若其底层集合是序数，满足 `IsCardinalL c`，且包含 `κ`，该字段就给出内部包含 `δ ⊆ˢ c`。第一个字段已经说明 `δ` 是序数，因此包含关系在此就是序数的非严格比较：`δ` 不大于每个这样的 `c`。结论使用包含而非成员关系，因为它还必须适用于 `c` 就是 `δ` 的情形。对 `S` 的量化与 `_⊆ˢ_` 都作用于可构造载体，所以这是 `L` 中可见候选者之间的最小性。该字段对 `κ` 只假设 `κ ∈ c`；断言 `κ` 本身是序数和内部基数的假设，由使用这个谓词的各定理提供。

这个字段不构造任何单射图。`InjCode F a b` 保留一个特定的可构造码 `F` 及其四项单射条件，而 `InjL a b` 是 `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` 的命题截断。因此，把假设 `IsCardinalL c` 与 `c` 的序数性合在一起，它说的是：不存在从 `c` 到其任一较小序数成员的 `InjL` 单射。`SuccCardL δ κ` 本身是固定之对 `δ, κ` 的未截断性质：它既不证明合适的 `δ` 存在，也不选定一个 `δ`。后文的 `succCardExists` 在 `κ` 是序数内部基数且不是有限序数时，证明这种 `δ` 的命题截断存在性；所用的经典假设仍只是模块参数 `LEM (ℓ-suc ℓ)`。集合论后继 `sucV` 并未出现在这个定义中。
<!--ja-->
最後のフィールドは、`κ` より大きい内部順序数基数全体の中での最小性を表す。基礎集合が順序数で、`IsCardinalL c` を満たし、`κ` を含む任意の `c : S` を与えると、このフィールドは内部の包含 `δ ⊆ˢ c` を返す。第一のフィールドによって `δ` も順序数であることが分かっているので、ここで包含は順序数の非狭義の比較である。すなわち、`δ` はそのようなすべての `c` 以下である。結論が所属ではなく包含になっているのは、`c` が `δ` 自身である場合も扱う必要があるからである。`S` 上の量化と `_⊆ˢ_` はどちらも構成可能な台に対するものなので、これは `L` に見える候補の中での最小性である。このフィールドが `κ` について仮定するのは `κ ∈ c` だけである。`κ` 自身の順序数性と内部基数性は、この述語を用いる各定理で仮定される。

このフィールドは単射のグラフを構成しない。`InjCode F a b` は特定の構成可能な符号 `F` と単射の四条件を保持するが、`InjL a b` は `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` という命題的切り詰めである。したがって、`IsCardinalL c` と `c` の順序数性を合わせた仮定は、`c` からその要素であるより小さな順序数への `InjL` 単射が存在しないことを述べる。`SuccCardL δ κ` 自体は、固定された対 `δ, κ` に関する切り詰められていない性質である。適切な `δ` の存在を証明せず、特定の `δ` も選ばない。後の `succCardExists` は、`κ` が順序数である内部基数であり、有限順序数ではないとき、そのような `δ` の存在を命題的切り詰めの下で証明する。そこで用いる古典的仮定は、このモジュールのパラメータ `LEM (ℓ-suc ℓ)` だけである。集合論的後続 `sucV` はこの定義に現れない。
<!--/-->

```agda
  × ((c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩
             → ⟨ δ ⊆ˢ c ⟩)
```
