<!--en-->
# Well-orders on all stages

For each ordinal `γ`, this chapter constructs in the ambient type theory a strict well-order on the members of `Lset γ`. The construction has two nested parts. A set is first assigned the ordinal over which it is first definable; sets born at different ordinals are ordered by those ordinals, while sets born together are ordered by their least names over the common earlier stage. Membership induction then supplies these stage orders simultaneously. The result is a host-level order at each stage, not yet an internal relation of set theory and not a single well-order of all of `L`.
<!--zh-->
# 各层上的良序

对每个序数 `γ`，本章在宿主类型论中构造 `Lset γ` 的成员上的严格良序。构造分为相互嵌套的两层。先为每个集合指定它最初成为可定义子集时所依据的序数；诞生序数不同的集合按诞生序数排序，同生的集合则按共同前层之上的最小名字排序。随后借隶属归纳同时得到各层的序。所得结果是每一层处的宿主层良序，还不是集合论内部的关系，也不是整个 `L` 上的单一良序。
<!--ja-->
# 各段階上の整列順序

各順序数 `γ` に対して、この章では周囲の型理論において `Lset γ` の要素上の狭義整列順序を構成する。構成は二重になっている。まず各集合に、それが初めて定義可能な部分集合として現れるときの基礎となる順序数を割り当てる。誕生順序数が異なる集合はその順序数で比較し、同時に生まれた集合は共通の直前段階上の最小の名前で比較する。次に所属帰納法によって、各段階の順序を同時に得る。得られるのは各段階における周囲の型理論の整列順序であり、集合論内部の関係でも、`L` 全体の単一の整列順序でもない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
The classical assumption is used at the point where a merely inhabited family of names is turned into its determined least member. For every index, `stepAt` is uniformly obtained from this least-name construction.
<!--zh-->
经典假设用于把仅仅非空的名字族变成其确定的最小成员。对每个指数，`stepAt` 都统一地由这个最小名字构造得到。
<!--ja-->
古典的仮定は、単に非空である名前の族を、その確定した最小要素へ変える箇所で用いられる。どの添字に対しても、`stepAt` はこの最小名の構成から一様に得られる。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
All constructions are carried out at a fixed universe level under the single hypothesis `LEM (ℓ-suc ℓ)`. This same assumption is passed to the construction of the name order and to the least-name search; assembling the stage orders introduces no additional classical premise.
<!--zh-->
全部构造都在固定的宇宙层级与单一假设 `LEM (ℓ-suc ℓ)` 下进行。同一假设既传给名字序的构造，也传给最小名字的搜索；把各层的序装配成族时不再加入其他经典前提。
<!--ja-->
すべての構成は、固定した宇宙レベルと一つの仮定 `LEM (ℓ-suc ℓ)` のもとで行われる。同じ仮定が名前順序の構成と最小名の探索に渡され、段階順序を族へ組み立てる際には新たな古典的前提を加えない。
<!--/-->

```agda
module L.Choice.StageOrders {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The objects ordered here are members of the cumulative hierarchy as seen by the ambient type theory. Their membership proofs travel with them, but those proofs are propositions, so they do not create extra copies of an element. This distinction will matter when the same order is later described and represented inside `L`.
<!--zh-->
此处被排序的对象，是宿主类型论所见的累积层级成员。隶属证明随成员一同携带，但这些证明是命题，因而不会制造同一元素的额外副本。后文在 `L` 内描述并表示同一良序时，这一区分至关重要。
<!--ja-->
ここで順序づける対象は、周囲の型理論から見た累積階層の要素である。所属の証明も要素とともに運ばれるが、それらは命題なので、同じ要素の余分な複製を生じさせない。この区別は、のちに同じ順序を `L` の内部で記述し表現するときに重要になる。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isL; Lset; Lset→isL )
```

<!--en-->
To locate a set's birth, begin with the earliest ordinal stage containing it. That stage is a successor, so it has a predecessor; this predecessor is the stage over which the set first appears as a definable subset. Ordinal trichotomy will later show that this birth lies strictly below every ordinal stage containing the set.
<!--zh-->
为确定集合的诞生序数，先取包含它的最早序数层。该层是后继层，因而有一个前驱；这个前驱就是该集合首次作为可定义子集出现时所依据的层。随后，序数三歧性将说明这个诞生序数严格低于每个包含该集合的序数层。
<!--ja-->
集合の誕生順序数を定めるには、まずそれを含む最も早い順序数段階を取る。その段階は後続段階なので先行者をもち、この先行者が、集合が初めて定義可能な部分集合として現れるときの基礎段階である。のちに順序数の三分性を用いて、この誕生順序数が集合を含むどの順序数段階よりも真に下にあることを示す。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( IsPredOf; predOf; carveAt )
```

<!--en-->
Once a stage is well-ordered, its formulas and parameter lists form well-ordered names for the next stage. A successor-stage member may have many such names, so the construction selects the least one and compares members through these selected representatives. The relevant uniqueness belongs to the least representative, not to names in general.
<!--zh-->
一旦某层已有良序，其公式与参数列便组成下一层的良序名字。一个后继层成员可能有许多这样的名字，因此构造选取其中最小者，并借这些选定代表比较成员。这里的唯一性属于最小代表，而不属于一般的名字。
<!--ja-->
ある段階が整列順序づけられると、その論理式とパラメータ列は次の段階の整列順序づけられた名前をなす。後続段階の一つの要素が多くの名前をもつこともあるので、構成はその最小のものを選び、選ばれた代表を通して要素を比較する。ここで一意なのは最小代表であり、名前一般ではない。
<!--/-->

```agda
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Tri-map )
open import L.Choice.CanonicalNames {ℓ} lem using ( module Naming )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; isPropLeastOf )
```

<!--en-->
Several changes of representation occur in this construction: from a presented index to the set it denotes, from a set to a member paired with its membership proof, and from a member to its least name. Each change is injective, so equality and strict comparison can be transported without identifying distinct elements.
<!--zh-->
本构造会数次改变表示：从呈现索引到它所表示的集合，从集合到集合与其隶属证明组成的成员，以及从成员到其最小名字。每次改变都是单射的，因此可以搬运相等与严格比较，而不会认同不同的元素。
<!--ja-->
この構成では表現を何度か変える。表示の添字からそれが表す集合へ、集合から所属証明を伴う要素へ、さらに要素からその最小名へと移る。どの変更も単射なので、異なる要素を同一視することなく等しさと狭義比較を移せる。
<!--/-->

```agda
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
```

<!--en-->
Name completeness gives only propositional truncation of existence: it says that a denoting name merely exists, without exposing a chosen one. The later least-element argument may eliminate this truncation because the total type of least names is itself a proposition.
<!--zh-->
名字完备性只给出存在性的命题截断：它断言指称该集合的名字仅仅存在，并不展示某个选定名字。后面的极小元论证能够消去这一截断，因为最小名字的总类型本身是命题。
<!--ja-->
名前の完全性が与えるのは存在の命題的切り詰めだけである。すなわち、指示する名前が単に存在すると述べるだけで、選ばれた名前を示さない。後の最小要素の議論がこの切り詰めを除去できるのは、最小名の全体型そのものが命題だからである。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
```

<!--en-->
A hierarchy set has both a small presentation type and an ambient membership type. The presentation map embeds the former into the latter. This bridge lets the construction use small parameters when forming names while retaining an order stated directly on the members of `Lset γ`.
<!--zh-->
层级中的集合既有小呈现类型，也有宿主隶属类型。呈现映射把前者嵌入后者。这座桥使构造能在形成名字时使用小参数，同时保留直接陈述在 `Lset γ` 成员上的序。
<!--ja-->
階層の集合には、小さな表示型と周囲の所属型の両方がある。表示写像は前者を後者へ埋め込む。この橋により、名前を作るときには小さなパラメータを使いながら、`Lset γ` の要素上に直接述べられた順序を保てる。
<!--/-->

```agda
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
```

<!--en-->
From this point on, `S` denotes the ambient carrier of sets. Statements such as `x ∈ˢ Lset γ` are therefore external types expressing membership in a constructible stage; they are not yet formulas evaluated in the object theory.
<!--zh-->
从此处起，`S` 表示集合的宿主载体。因此，`x ∈ˢ Lset γ` 一类陈述是表达可构造层隶属关系的外部类型，还不是在对象理论中求值的公式。
<!--ja-->
ここから `S` は集合の周囲の台を表す。したがって `x ∈ˢ Lset γ` のような主張は、構成可能段階への所属を表す外部の型であり、まだ対象理論で評価される論理式ではない。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The stage a set is carved at
<!--zh-->
## 一个集合被雕出的层
<!--ja-->
## 集合が切り出される段階
<!--/-->

<!--en-->
Apply the general carving argument to the property that `x` belongs to a stage. Since `stage x p` is the earliest stage with this property, the result supplies an ordinal `δ` whose successor is exactly `stage x p`. Thus `δ` is the predecessor of the earliest containing stage, rather than another least stage chosen independently.
<!--zh-->
把一般切取论证用于「`x` 属于某层」这一性质。由于 `stage x p` 是满足该性质的最早层，结果给出序数 `δ`，其后继恰等于 `stage x p`。因此，`δ` 是最早包含层的前驱，并不是另行选出的另一个最早层。
<!--ja-->
一般の切り出しの議論を、「`x` がある段階に属する」という性質に適用する。`stage x p` はこの性質を満たす最も早い段階なので、その結果は、後続がちょうど `stage x p` となる順序数 `δ` を与える。したがって `δ` は最初の包含段階の先行者であり、独立に選ばれた別の最小段階ではない。
<!--/-->

```agda
theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = predOf (λ σ → x ∈ˢ Lset σ) (stage x p) (stage-ord x p)
  (stage-earliest x p)
  (carveAt (λ σ → x ∈ˢ Lset σ) (stage x p) x (stage-mem x p) (λ δ hz → hz))
```

<!--en-->
The ordinal `birth x p` is this predecessor. Mathematically, it records the stage over which `x` first appears as a definable subset. It should not be read as the von Neumann rank of `x`; the only identification made here is between its successor and the earliest constructible stage containing `x`.
<!--zh-->
序数 `birth x p` 就是这个前驱。从数学上说，它记录 `x` 首次作为可定义子集出现时所依据的层。不应把它理解为 `x` 的冯·诺伊曼秩；此处给出的等同仅是：它的后继就是最早包含 `x` 的可构造层。
<!--ja-->
順序数 `birth x p` はこの先行者である。数学的には、`x` が初めて定義可能な部分集合として現れるときの基礎段階を記録する。これを `x` のフォン・ノイマン階数と読んではならない。ここで示される同一視は、その後続が `x` を含む最も早い構成可能段階であることだけである。
<!--/-->

```agda
opaque
  birth : (x : S) → ⟨ isL x ⟩ → S
  birth x p = theCarve x p .fst
```

<!--en-->
The predecessor data in `theCarve x p` contain both a proof that the chosen predecessor is an ordinal and the equation identifying its successor with `stage x p`. The theorem `birth-ord` reads the former component, so `birth x p` may later be compared with other ordinals and used as an index for membership induction.
<!--zh-->
`theCarve x p` 给出的前驱数据同时包含两项：所取前驱是序数，以及它的后继等于 `stage x p`。定理 `birth-ord` 读出前一项，使 `birth x p` 随后可以与其他序数比较，也可以作为隶属归纳的指标。
<!--ja-->
`theCarve x p` の先行者データには、選ばれた先行者が順序数であることの証明と、その後続を `stage x p` と同一視する等式の両方が含まれる。`birth-ord` は前者を読み出すので、後で `birth x p` を他の順序数と比較し、所属帰納法の添字として用いることができる。
<!--/-->

```agda
opaque
  unfolding birth
  birth-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (birth x p)
  birth-ord x p = theCarve x p .snd .fst
```

<!--en-->
The second projection gives the defining equation `sucV (birth x p) ≡ stage x p`. This equation connects the two useful viewpoints: `stage` tells where `x` first belongs, while `birth` tells the earlier stage over which `x` was formed.
<!--zh-->
第二个投影给出定义性等式 `sucV (birth x p) ≡ stage x p`。这条等式连接两种有用观点：`stage` 指出 `x` 首次属于哪一层，而 `birth` 指出 `x` 据哪一前层形成。
<!--ja-->
第二の射影は定義的な等式 `sucV (birth x p) ≡ stage x p` を与える。この等式は二つの有用な見方を結ぶ。`stage` は `x` が初めて属する段階を示し、`birth` は `x` がどの直前段階を基礎として作られたかを示す。
<!--/-->

```agda
  birth-suc : (x : S) (p : ⟨ isL x ⟩) → sucV (birth x p) ≡ stage x p
  birth-suc x p = theCarve x p .snd .snd
```

<!--en-->
Because `x` belongs to its earliest stage and that stage is `sucV (birth x p)`, it belongs to the successor stage over its birth. This is precisely the membership needed to treat `x` as a definable subset of `Lset (birth x p)` and hence to assign it a name there.
<!--zh-->
因为 `x` 属于其最早层，而该层就是 `sucV (birth x p)`，所以 `x` 属于其诞生序数的后继层。正是这条隶属关系，使我们能把 `x` 看作 `Lset (birth x p)` 的可定义子集，并在那里为它指定名字。
<!--ja-->
`x` はその最も早い段階に属し、その段階は `sucV (birth x p)` なので、`x` は誕生順序数の後続段階に属する。この所属こそ、`x` を `Lset (birth x p)` の定義可能な部分集合と見なし、そこで名前を与えるために必要なものである。
<!--/-->

```agda
birth-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (sucV (birth x p)) ⟩
birth-mem x p =
  subst (λ w → ⟨ x ∈ˢ Lset w ⟩) (sym (birth-suc x p)) (stage-mem x p)
```

<!--en-->
The birth ordinal itself lies in its successor ordinal, and the predecessor equation transports this membership to `stage x p`. Consequently the earliest stage containing `x` also contains the ordinal over which `x` was formed.
<!--zh-->
诞生序数自身属于它的后继序数，前驱等式把这条隶属搬运到 `stage x p`。因此，最早包含 `x` 的层也包含 `x` 形成时所依据的序数。
<!--ja-->
誕生順序数自身はその後続順序数に属し、先行者の等式がこの所属を `stage x p` へ移す。したがって `x` を含む最も早い段階は、`x` が作られるときの基礎となった順序数も含む。
<!--/-->

```agda
birth-stage : (x : S) (p : ⟨ isL x ⟩) → ⟨ birth x p ∈ˢ stage x p ⟩
birth-stage x p =
  subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (birth-suc x p) (self∈sucV (birth x p))
```

<!--en-->
Although `birth` receives a proof `p` that `x` is constructible, its value contains no mathematical choice of such a proof. Constructibility is a proposition, so any two proofs `p` and `q` are equal; applying `birth x` to that equality shows that both inputs yield the same ordinal.
<!--zh-->
虽然 `birth` 接收 `x` 可构造的一份证明 `p`，其值并不包含对这类证明的数学选择。可构造性是命题，所以任意两份证明 `p` 与 `q` 都相等；把函数 `birth x` 作用于该等式，即得两种输入产生同一序数。
<!--ja-->
`birth` は `x` が構成可能であることの証明 `p` を受け取るが、その値はそのような証明の数学的な選択を含まない。構成可能性は命題なので、任意の二つの証明 `p` と `q` は等しい。その等式に関数 `birth x` を作用させれば、どちらの入力からも同じ順序数が得られる。
<!--/-->

```agda
birth-proof : (x : S) (p q : ⟨ isL x ⟩) → birth x p ≡ birth x q
birth-proof x p q = cong (birth x) (snd (isL x) p q)
```

<!--en-->
Suppose `x ∈ Lset γ`, with `γ` an ordinal. Trichotomy compares `γ` with the earliest stage `stage x p`. The case `γ ∈ stage x p` is impossible: it would exhibit an earlier ordinal stage that already contains `x`, contradicting the defining minimality of `stage x p`.
<!--zh-->
设 `x ∈ Lset γ`，且 `γ` 是序数。用三歧性比较 `γ` 与最早层 `stage x p`。情形 `γ ∈ stage x p` 不可能成立：它会给出一个更早且已包含 `x` 的序数层，违背 `stage x p` 的定义性最早性。
<!--ja-->
`x ∈ Lset γ` であり、`γ` が順序数であるとする。三分性により `γ` と最初の段階 `stage x p` を比較する。`γ ∈ stage x p` の場合は不可能である。すでに `x` を含む、より早い順序数段階が得られ、`stage x p` の定義上の最小性に反するからである。
<!--/-->

```agda
private
  decideIn : (γ x : S) → IsOrd γ → (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
           → ⟨ γ ∈ˢ stage x p ⟩ ⊎ ((γ ≡ stage x p) ⊎ ⟨ stage x p ∈ˢ γ ⟩)
           → ⟨ birth x p ∈ˢ γ ⟩
  decideIn γ x ordγ p h (inl γ∈) = ⊥₀-rec (stage-earliest x p γ ordγ h γ∈)
```

<!--en-->
If `γ` equals the earliest stage, `birth-stage` gives the desired membership directly after transport. If the earliest stage belongs to `γ`, transitivity of the ordinal `γ` combines `birth x p ∈ stage x p` with `stage x p ∈ γ`. These are the two possible noncontradictory cases.
<!--zh-->
若 `γ` 等于最早层，搬运 `birth-stage` 即直接得到所需隶属。若最早层属于 `γ`，则序数 `γ` 的传递性把 `birth x p ∈ stage x p` 与 `stage x p ∈ γ` 合成。它们是两个不导致矛盾的可能情形。
<!--ja-->
`γ` が最初の段階に等しければ、`birth-stage` を移すことで求める所属が直ちに得られる。最初の段階が `γ` に属するなら、順序数 `γ` の推移性が `birth x p ∈ stage x p` と `stage x p ∈ γ` を合成する。これらが矛盾しない二つの可能な場合である。
<!--/-->

```agda
  decideIn γ x ordγ p h (inr (inl e)) =
    subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (sym e) (birth-stage x p)
  decideIn γ x ordγ p h (inr (inr s∈)) = ordγ .fst (birth-stage x p) s∈
```

<!--en-->
It follows that whenever `x` is a member of an ordinal stage `Lset γ`, its birth ordinal is a member of `γ`. The conclusion is strict. Later, when constructing the order at `γ`, this fact places every member's birth among the smaller ordinals for which the induction hypothesis has already supplied an order.
<!--zh-->
由此，只要 `x` 是序数层 `Lset γ` 的成员，它的诞生序数就属于 `γ`。这个结论是严格的。随后构造 `γ` 处的序时，该事实把每个成员的诞生序数置于更小的序数之中，而归纳假设已经为这些序数提供了层序。
<!--ja-->
したがって `x` が順序数段階 `Lset γ` の要素であれば、その誕生順序数は `γ` に属する。この結論は狭義である。のちに `γ` における順序を構成するとき、この事実によって各要素の誕生順序数は、帰納法の仮定がすでに順序を与えている小さい順序数の中に置かれる。
<!--/-->

```agda
birth-in : (γ : S) → IsOrd γ → (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
         → ⟨ birth x p ∈ˢ γ ⟩
birth-in γ ordγ x p h =
  decideIn γ x ordγ p h (ord-tri γ ordγ (stage x p) (stage-ord x p))
```

<!--en-->
## Moving a well-order along an injection
<!--zh-->
## 沿一个单射搬运良序
<!--ja-->
## 単射に沿って整列順序を移す
<!--/-->

<!--en-->
For an ambient set `A`, the type `Mem A` consists of a set together with evidence that it belongs to `A`. Carrying the evidence makes later order relations well-typed. Since membership is proposition-valued, two inhabitants with the same underlying set cannot differ merely because their membership evidence was obtained in different ways.
<!--zh-->
对宿主集合 `A`，类型 `Mem A` 的元素由一个集合及其属于 `A` 的证据组成。携带这份证据，使后面的序关系具有正确类型。由于隶属关系取值于命题，两个成员只要底层集合相同，就不会仅因隶属证据的取得方式不同而有所区别。
<!--ja-->
周囲の集合 `A` に対し、型 `Mem A` の要素は、集合とそれが `A` に属することの証拠との対である。この証拠を伴わせることで、後の順序関係が正しく型づけられる。所属は命題値なので、基礎となる集合が同じ二つの要素が、所属の証拠の得方だけによって異なることはない。
<!--/-->

```agda
Mem : S → Type (ℓ-suc ℓ)
Mem A = Σ[ x ∈ S ] ⟨ x ∈ˢ A ⟩
```

<!--en-->
Fix a strict well-order `w` on a type `A`. The next construction uses only the relation and laws contained in this structure, so it applies equally to name orders, stage-member orders, and their changes of representation.
<!--zh-->
固定类型 `A` 上的严格良序 `w`。接下来的构造只使用该结构所含的关系与定律，因此同样适用于名字序、层成员序及其不同表示之间的转换。
<!--ja-->
型 `A` 上の狭義整列順序 `w` を固定する。次の構成はこの構造に含まれる関係と法則だけを使うので、名前の順序、段階要素の順序、およびそれらの表現の変更に同じように適用できる。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {ℓc : Level} {A : Type ℓc} (w : SWO A) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open SWO w using () renaming ( _<∙_ to _<ʷ_ )
```

<!--en-->
Writing `relOf w a b` for the strict comparison contained in `w` lets later statements discuss the relation without exposing how the well-order was assembled. In particular, this notation does not turn the relation into an object of the internal set theory; it remains a type-valued relation in the host theory.
<!--zh-->
用 `relOf w a b` 表示 `w` 中所含的严格比较，使后文能讨论该关系而无须展开良序的构造。特别地，这一记法不会把该关系变成对象集合论中的对象；它仍是宿主类型论中的类型值关系。
<!--ja-->
`w` に含まれる狭義比較を `relOf w a b` と書くことで、整列順序の組み立て方を展開せずに関係を論じられる。とくに、この記法によって関係が内部集合論の対象になるわけではない。それは依然として周囲の型理論における型値の関係である。
<!--/-->

```agda
  relOf : A → A → Type (ℓ-suc ℓ)
  relOf a b = a <ʷ b
```
</div>
</details>


<!--en-->
Let `f : B → C` be injective and suppose `C` is strictly well-ordered. Comparing `u` and `v` in `B` by comparing `f u` and `f v` should then inherit a strict well-order. Injectivity is essential only for reflecting the equality case back from `C` to `B`.
<!--zh-->
设 `f : B → C` 为单射，且 `C` 已带严格良序。若通过比较 `f u` 与 `f v` 来比较 `B` 中的 `u` 与 `v`，所得关系应继承一个严格良序。单射性不可缺少之处，正是把 `C` 中的相等情形反映回 `B`。
<!--ja-->
`f : B → C` が単射であり、`C` が狭義整列順序づけられているとする。`B` の `u` と `v` を `f u` と `f v` の比較によって比べれば、その関係は狭義整列順序を受け継ぐはずである。単射性が本質的に必要なのは、`C` における等しい場合を `B` へ反映するときである。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {ℓb ℓc : Level} (B : Type ℓb) (C : Type ℓc) (w : SWO C)
         (f : B → C) (finj : (u v : B) → f u ≡ f v → u ≡ v) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open SWO w using () renaming
    ( _<∙_ to _<ᶜ_ ; tri∙ to triᶜ ; irr∙ to irrᶜ
    ; trans∙ to transᶜ ; wf∙ to wfᶜ )
```

<!--en-->
The pulled-back relation declares `u` smaller than `v` exactly when the image `f u` is smaller than `f v`. Thus it orders `B` as the ordered subcollection represented by its image in `C`; no surjectivity or order isomorphism is claimed.
<!--zh-->
拉回关系规定：`u` 小于 `v`，当且仅当像 `f u` 小于 `f v`。因此，它把 `B` 排成由其在 `C` 中的像所表示的有序子集；这里既不要求满射，也不声称存在序同构。
<!--ja-->
引き戻された関係では、像 `f u` が `f v` より小さいとき、かつそのときに限って `u` が `v` より小さいと定める。したがって `B` は `C` 内の像が表す順序づけられた部分として並べられるのであり、全射性も順序同型も主張しない。
<!--/-->

```agda

  private
    _<ᵇ_ : B → B → Type (ℓ-suc ℓ)
    u <ᵇ v = f u <ᶜ f v
```

<!--en-->
Trichotomy in `C` gives three cases for the two images. The two strict cases are already comparisons in the pulled-back relation, while equality of the images gives equality of the original points by injectivity. Hence the relation on `B` is trichotomous.
<!--zh-->
`C` 中的三歧性为两个像给出三种情形。两个严格情形已经是拉回关系中的比较，而像相等时由单射性得到原点相等。因此，`B` 上的关系满足三歧性。
<!--ja-->
`C` の三分性は二つの像について三つの場合を与える。二つの狭義の場合はそのまま引き戻された関係の比較であり、像が等しい場合には単射性からもとの点の等しさが得られる。したがって `B` 上の関係も三分的である。
<!--/-->

```agda
    pullTri : (u v : B) → Tri (u <ᵇ v) (u ≡ v) (v <ᵇ u)
    pullTri u v = Tri-map id (finj u v) id (triᶜ (f u) (f v))
```

<!--en-->
Well-foundedness also pulls back. If `f u` is accessible in `C`, its accessibility tree contains a subtree for every `f v` below it. A predecessor `v` of `u` supplies exactly such a comparison, and recursively pulling back the corresponding subtree makes `v` accessible in `B`. Thus accessibility, rather than merely the absence of a displayed descending sequence, is transported along `f`.
<!--zh-->
良基性也能拉回。若 `f u` 在 `C` 中可及，它的可及树就为每个低于它的 `f v` 含有一棵子树。`u` 的前驱 `v` 恰好给出这样的比较，递归地拉回相应子树便证明 `v` 在 `B` 中可及。因此沿 `f` 搬运的是可及性本身，而不只是「没有展示出下降序列」这一较弱陈述。
<!--ja-->
整礎性も引き戻せる。`f u` が `C` で到達可能なら、その到達可能性の木は、下にある各 `f v` に対する部分木を含む。`u` の先行元 `v` はまさにその比較を与え、対応する部分木を再帰的に引き戻すことで、`v` が `B` で到達可能だと分かる。したがって `f` に沿って移されるのは、単に下降列が提示されていないという弱い主張ではなく、到達可能性そのものである。
<!--/-->

```agda
    pullAcc : (u : B) → Acc _<ᶜ_ (f u) → Acc _<ᵇ_ u
    pullAcc u (acc r) = acc (λ v h → pullAcc v (r (f v) h))
```

<!--en-->
Irreflexivity transfers immediately: a point below itself in the pulled-back relation would make its image below itself in `C`. Together with the trichotomy just proved, this supplies the first order laws on the source.
<!--zh-->
非自反性直接转移：若某点在拉回关系中小于自身，它的像就会在 `C` 中小于自身。结合刚证明的三歧性，这给出了源类型上的前两条序定律。
<!--ja-->
非反射性は直ちに移る。引き戻された関係で点が自分自身より小さければ、その像も `C` で自分自身より小さくなってしまう。先に示した三分性と合わせて、これで源の上の最初の順序法則が得られる。
<!--/-->

```agda
  pullOrder : SWO B
  pullOrder = record
    { _<∙_   = _<ᵇ_
    ; tri∙   = pullTri
    ; irr∙   = λ u h → irrᶜ (f u) h
```

<!--en-->
Transitivity follows by composing comparisons of the three images in `C`, and the accessibility argument supplies well-foundedness. These laws complete `pullOrder`, the strict well-order on `B` obtained by viewing its elements through the injection `f`.
<!--zh-->
传递性来自在 `C` 中合成三个像之间的比较，而可及性论证给出良基性。这些定律补全 `pullOrder`，即通过单射 `f` 观察 `B` 的元素而得到的严格良序。
<!--ja-->
推移性は `C` における三つの像の比較を合成することで従い、到達可能性の議論が整礎性を与える。これらの法則によって `pullOrder`、すなわち単射 `f` を通して `B` の要素を見ることで得られる狭義整列順序が完成する。
<!--/-->

```agda
    ; trans∙ = λ u v z → transᶜ (f u) (f v) (f z)
    ; wf∙    = λ u → pullAcc u (wfᶜ (f u)) }
```
</div>
</details>


<!--en-->
Every index in the small presentation `⟪ A ⟫` denotes an actual member of `A`. Pairing its image with this membership evidence gives a map from presentation indices into `Mem A`, the form on which stage orders are constructed.
<!--zh-->
小呈现 `⟪ A ⟫` 中的每个索引都表示 `A` 的一个实际成员。把其像与这份隶属证据配对，便得到从呈现索引到 `Mem A` 的映射，而层序正是在后一形式上构造的。
<!--ja-->
小さな表示 `⟪ A ⟫` の各添字は `A` の実際の要素を指す。その像をこの所属の証拠と対にすることで、表示の添字から、段階順序が構成される形 `Mem A` への写像が得られる。
<!--/-->

```agda
memOf : (A : S) (m : ⟪ A ⟫) → ⟨ ⟪ A ⟫↪ m ∈ˢ A ⟩
memOf A m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)
```

<!--en-->
The function `carry` uses this map to pull an order on ambient member pairs back to the small presentation type. This is the direction required by the naming construction, whose parameter vectors range over `⟪ A ⟫`, while the family constructed later naturally orders `Mem A`.
<!--zh-->
函数 `carry` 沿这条映射，把宿主成员对上的序拉回到小呈现类型。这正是命名构造所需的方向：它的参数向量取自 `⟪ A ⟫`，而后文构造的层序自然作用于 `Mem A`。
<!--ja-->
関数 `carry` はこの写像に沿って、周囲の要素対上の順序を小さな表示型へ引き戻す。これは名前の構成が必要とする向きである。そのパラメータ列は `⟪ A ⟫` から取られる一方、のちに構成する段階順序は自然に `Mem A` を順序づけるからである。
<!--/-->

```agda
carry : (A : S) → SWO (Mem A) → SWO ⟪ A ⟫
carry A w = pullOrder ⟪ A ⟫ (Mem A) w (λ m → ⟪ A ⟫↪ m , memOf A m) inj
  where
  inj : (u v : ⟪ A ⟫)
      → _≡_ {A = Mem A} (⟪ A ⟫↪ u , memOf A u) (⟪ A ⟫↪ v , memOf A v) → u ≡ v
```

<!--en-->
The presentation map is an embedding, so equality of the resulting member pairs forces equality of their underlying presented elements and hence of the original indices. This verifies the injectivity needed by `pullOrder`; it does not assert that every arbitrary presentation of a member has been chosen.
<!--zh-->
呈现映射是嵌入，因此所得成员对相等会迫使其底层呈现元素相等，进而迫使原索引相等。这验证了 `pullOrder` 所需的单射性；它并未声称为每个成员选取了任意一种呈现。
<!--ja-->
表示写像は埋め込みなので、得られた要素対が等しければ、その基礎となる表示要素が等しくなり、したがってもとの添字も等しくなる。これで `pullOrder` に必要な単射性が確認されるが、各要素について任意の表示を選んだと主張するものではない。
<!--/-->

```agda
  inj u v q = isEmbedding→Inj isEmb⟪ A ⟫↪ u v (cong fst q)
```

<!--en-->
## The step
<!--zh-->
## 步进
<!--ja-->
## ステップ
<!--/-->

<!--en-->
For a stage index `δ`, `New δ` is the type of all members of `Lset (sucV δ)`, each paired with its membership evidence. The name is convenient for the one-step construction, but it does not mean that every such member is born exactly at `δ`; older members may also persist into this successor stage.
<!--zh-->
对层指数 `δ`，`New δ` 是 `Lset (sucV δ)` 的全部成员所成的类型，每个成员都与其隶属证据配对。这个名字便于表述单步构造，但并不意味着每个这样的成员都恰好诞生于 `δ`；较早的成员也可能继续属于这个后继层。
<!--ja-->
段階の添字 `δ` に対し、`New δ` は `Lset (sucV δ)` のすべての要素を、それぞれ所属の証拠と対にした型である。この名前は一段階の構成を述べるのに便利だが、各要素がちょうど `δ` で生まれたという意味ではない。より早く生まれた要素もこの後続段階に残りうる。
<!--/-->

```agda
New : S → Type (ℓ-suc ℓ)
New δ = Mem (Lset (sucV δ))
```

<!--en-->
Fix an index `δ` and a strict well-order on the small members of `Lset δ`. The naming construction can now compare names over this stage, because its parameter component is compared using precisely that supplied order. This gives the uniform local construction used at every index.
<!--zh-->
固定指数 `δ`，并固定 `Lset δ` 的小成员上的严格良序。此时命名构造可以比较这一层之上的名字，因为名字的参数部分恰按所给的序比较。这就给出用于每个指数处的统一局部构造。
<!--ja-->
添字 `δ` と `Lset δ` の小さな要素上の狭義整列順序を固定する。これで、この段階上の名前を比較できる。名前のパラメータ部分が、まさに与えられた順序によって比較されるからである。これが、どの添字でも用いられる一様な局所構成を与える。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ (δ : S) (w : SWO ⟪ Lset δ ⟫) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    module NM = Naming (Lset δ) w
```

<!--en-->
A name denotes a set `x` when its semantic value is equal to `x`. Equality of hierarchy sets is a proposition, so denotation forms an `hProp`-valued family. This proposition-valued form is what the general least-element construction requires.
<!--zh-->
若一个名字的语义值等于集合 `x`，就说该名字指称 `x`。层级集合的相等是命题，因此指称构成一个取值于 `hProp` 的族。这一命题值形式正是一般极小元构造所要求的。
<!--ja-->
名前の意味値が集合 `x` に等しいとき、その名前は `x` を指示するという。階層の集合の等しさは命題なので、指示は `hProp` 値の族をなす。この命題値の形が、一般の最小要素構成に必要である。
<!--/-->

```agda
  denotesAt : S → NM.Name → hProp (ℓ-suc ℓ)
  denotesAt x n = (NM.denote n ≡ x) , setIsSet (NM.denote n) x
```

<!--en-->
For `a : New δ`, only the underlying set `a.fst` is named. Its membership evidence establishes that the set lies in the successor stage, but it is not part of the denotation equation and therefore cannot affect which name is least.
<!--zh-->
对 `a : New δ`，被命名的只有底层集合 `a.fst`。它的隶属证据证明该集合位于后继层，却不是指称等式的一部分，因而不会影响哪个名字最小。
<!--ja-->
`a : New δ` に対して名前が付けられるのは、基礎となる集合 `a.fst` だけである。その所属の証拠は集合が後続段階にあることを示すが、指示の等式の一部ではなく、どの名前が最小であるかには影響しない。
<!--/-->

```agda
  private
    denotes : New δ → NM.Name → hProp (ℓ-suc ℓ)
    denotes a = denotesAt (a .fst)
```

<!--en-->
Membership in `Lset (sucV δ)` is rewritten by the successor-stage equation as membership in the definable powerset over `Lset δ`. Name completeness then gives the propositional truncation of a pair consisting of a name and evidence that it denotes `a.fst`. At this point there is still no chosen name.
<!--zh-->
借后继层等式，把 `Lset (sucV δ)` 中的隶属改写为 `Lset δ` 上可定义幂集中的隶属。随后名字完备性给出一个二元组的命题截断，其中包含名字及其指称 `a.fst` 的证据。此时仍没有选定任何名字。
<!--ja-->
`Lset (sucV δ)` への所属を、後続段階の等式によって `Lset δ` 上の定義可能冪集合への所属へ書き換える。すると名前の完全性から、名前とそれが `a.fst` を指示する証拠との対の命題的切り詰めが得られる。この時点では、まだ名前は一つも選ばれていない。
<!--/-->

```agda
    hasName : (a : New δ) → ∥ Σ[ n ∈ NM.Name ] ⟨ denotes a n ⟩ ∥₁
    hasName a = NM.names-complete (a .fst)
      (subst (λ v → ⟨ a .fst ∈ˢ v ⟩) (Lset-suc δ) (a .snd))
```

<!--en-->
The name order is a strict well-order, so a merely inhabited family of denoting names has a least member. The least-element construction uses the classical hypothesis for its descent. Eliminating the propositional truncation is legitimate because the total type of a name together with proof that it is least is a proposition: any two such names are equal by trichotomy.
<!--zh-->
名字序是严格良序，因此仅仅非空的指称名字族有极小元。极小元构造在其下降过程中使用经典假设。消去命题截断是正当的，因为由名字及其最小性证明组成的总类型是命题：任意两个这样的名字都由三歧性得到相等。
<!--ja-->
名前の順序は狭義整列順序なので、単に非空である指示名の族には最小要素がある。最小要素の構成は、その降下に古典的仮定を用いる。命題的切り詰めを除去してよいのは、名前とそれが最小であることの証明との全体型が命題だからである。そのような二つの名前は三分性によって等しくなる。
<!--/-->

```agda
    leastOfNew : (a : New δ)
               → Σ[ n ∈ NM.Name ] IsLeast NM.nameOrder (denotes a) n
    leastOfNew a = NM.leastName (fst a) (hasName a)
```

<!--en-->
Define `theName a` to be the name component of this least witness. The construction is canonical in the precise sense supplied by the well-order: although completeness exposed no arbitrary representative, the least representative is uniquely determined.
<!--zh-->
定义 `theName a` 为这个最小见证中的名字分量。该构造在良序所赋予的精确意义下是典范的：完备性虽然没有展示任意代表，但最小代表却被唯一确定。
<!--ja-->
`theName a` を、この最小証人の名前成分として定める。この構成は、整列順序が与える正確な意味で標準的である。完全性は任意の代表を示さなかったが、最小代表は一意に定まる。
<!--/-->

```agda
    theName : New δ → NM.Name
    theName a = leastOfNew a .fst
```

<!--en-->
Leastness includes membership in the family being minimized. Hence the selected name really denotes `a.fst`; minimality alone would not suffice, since a name outside the denoting family could lie anywhere in the ambient name order.
<!--zh-->
最小性包含「属于正在取极小元的族」这一条件。因此，所选名字确实指称 `a.fst`；只有极小性约束还不够，因为不属于指称名字族的名字可以位于外围名字序中的任意位置。
<!--ja-->
最小性には、最小化している族に属するという条件も含まれる。したがって選ばれた名前は実際に `a.fst` を指示する。最小性の制約だけでは足りない。指示名の族に属さない名前は、周囲の名前順序のどこにあってもよいからである。
<!--/-->

```agda
    theName-denote : (a : New δ) → NM.denote (theName a) ≡ a .fst
    theName-denote a = leastOfNew a .snd .fst
```

<!--en-->
If two successor-stage members have the same selected least name, applying denotation shows that their underlying sets are equal. Their membership components are propositions, so this equality lifts to equality of the member pairs. Thus selecting the least name defines an injection, even though denotation on all names need not be injective.
<!--zh-->
若两个后继层成员具有同一个选定的最小名字，对名字取指称便说明它们的底层集合相等。其隶属分量都是命题，所以该等式提升为成员对的相等。因此，选取最小名字定义了一个单射，尽管所有名字上的指称映射不必是单射。
<!--ja-->
二つの後続段階の要素が同じ選ばれた最小名をもつなら、指示を適用することで基礎となる集合が等しいと分かる。所属成分は命題なので、この等しさは要素対の等しさへ持ち上がる。したがって最小名を選ぶ写像は単射であるが、すべての名前上の指示写像が単射である必要はない。
<!--/-->

```agda
    nameInj : (u v : New δ) → theName u ≡ theName v → u ≡ v
    nameInj u v q = Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV δ)))
      (sym (theName-denote u) ∙ cong NM.denote q ∙ theName-denote v)
```

<!--en-->
Pull the strict well-order of names back along this injection. Two members of `Lset (sucV δ)` are then compared by their selected least names. This is the sole construction used by the later `stepAt`: every `δ` follows this same least-name route.
<!--zh-->
沿这条单射拉回名字上的严格良序。于是，`Lset (sucV δ)` 的两个成员按各自选定的最小名字比较。后面的 `stepAt` 只使用这一种构造：每个 `δ` 都遵循同一条最小名字路线。
<!--ja-->
この単射に沿って名前の狭義整列順序を引き戻す。すると `Lset (sucV δ)` の二つの要素は、それぞれ選ばれた最小名によって比較される。後の `stepAt` が用いる構成はこれ一つだけであり、どの `δ` も同じ最小名による道をたどる。
<!--/-->

```agda
  byName : SWO (New δ)
  byName = pullOrder (New δ) NM.Name NM.nameOrder theName nameInj
```

<!--en-->
`IsLeastName t x` says two things: `t` denotes `x`, and no other name that denotes `x` lies strictly below `t` in the name order. The restriction to names that denote `x` matters; names denoting other sets play no role in this leastness assertion.
<!--zh-->
`IsLeastName t x` 包含两项内容：`t` 指称 `x`，并且在名字序中，没有另一个指称 `x` 的名字严格位于 `t` 之下。把范围限制在指称 `x` 的名字上很重要；指称其他集合的名字与这条最小性断言无关。
<!--ja-->
`IsLeastName t x` は二つのことを述べる。`t` が `x` を指示することと、名前の順序において `x` を指示する別の名前が `t` より真に下にはないことである。範囲を `x` を指示する名前に限ることが重要であり、他の集合を指示する名前はこの最小性の主張に関係しない。
<!--/-->

```agda
  IsLeastName : NM.Name → S → Type (ℓ-suc ℓ)
  IsLeastName t x = IsLeast NM.nameOrder (denotesAt x) t
```

<!--en-->
For each member `a : New δ`, the construction supplies a name together with `IsLeastName` evidence for its underlying set. Subsequent proofs can therefore reason with a least name without unfolding how the search found it or replacing propositional truncation by an arbitrary choice.
<!--zh-->
对每个成员 `a : New δ`，该构造给出一个名字，以及它对底层集合满足 `IsLeastName` 的证据。因此，后续证明可以直接使用最小名字推理，而无须展开搜索如何找到它，也无须把命题截断替换成任意选择。
<!--ja-->
各要素 `a : New δ` に対し、この構成は名前と、それが基礎となる集合について `IsLeastName` を満たす証拠を与える。したがって後続の証明は、探索がそれを見つけた方法を展開せず、命題的切り詰めを任意の選択に置き換えることもなく、最小名を用いて推論できる。
<!--/-->

```agda
  leastNameOf : (a : New δ) → Σ[ t ∈ NM.Name ] IsLeastName t (fst a)
  leastNameOf a = leastOfNew a
```

<!--en-->
Suppose `t` is any name satisfying `IsLeastName t (fst c)`. Both `(theName c, leastOfNew c .snd)` and `(t,h)` are least witnesses for the same denotation predicate. The total type of such least witnesses is a proposition: trichotomy rules out either name being strictly below the other and forces the names to be equal. Projecting that equality yields `theName c ≡ t`. Thus the least name is unique, while the set may still have many nonleast names.
<!--zh-->
设 `t` 是满足 `IsLeastName t (fst c)` 的任意名字。`(theName c, leastOfNew c .snd)` 与 `(t,h)` 都是同一指称谓词的最小见证。这类最小见证的总类型是命题：三歧性排除任一名字严格小于另一个的两种情形，并迫使两个名字相等。投影该等式便得到 `theName c ≡ t`。因此唯一的是最小名字，而该集合仍可能有许多非最小名字。
<!--ja-->
`t` が `IsLeastName t (fst c)` を満たす任意の名前であるとする。`(theName c, leastOfNew c .snd)` と `(t,h)` は、同じ指示述語に対する最小証人である。このような最小証人の全体型は命題である。三分性が、一方の名前が他方より真に小さい二つの場合を排除し、二つの名前の等しさを強制する。その等しさを射影すれば `theName c ≡ t` を得る。したがって一意なのは最小名であり、その集合はなお多くの最小でない名前をもちうる。
<!--/-->

```agda
  private
    pin : (c : New δ) (t : NM.Name) → IsLeastName t (fst c) → theName c ≡ t
    pin c t h = cong fst
      (isPropLeastOf NM.nameOrder (denotes c) (leastOfNew c) (t , h))
```

<!--en-->
The comparison fact pins each candidate's least name: if `t₁` is a least name for `a` and `t₂` is a least name for `b`, then the order relation computed by the pullback agrees with the order of the two least names themselves. This follows because each pinned name equals the computed minimum, so the pullback order transports through those equalities.
<!--zh-->
比较事实把每个候选的最小名字钉住：若 `t₁` 是 `a` 的最小名字、`t₂` 是 `b` 的最小名字，则拉回序所算出的关系与两条最小名字自身的序一致。原因在于每个被钉住的名字等于算出的最小值，拉回序沿这些等式搬运。
<!--ja-->
比較の事実が、それぞれの候補の最小の名前を固定する。`t₁` が `a` の最小の名前であり、`t₂` が `b` の最小の名前であるならば、引き戻された順序が計算する関係は、二つの最小の名前の順序そのものである。ピン止めされた名前が、それぞれ計算された最小値に等しいので、引き戻された順序がそれらの等式に沿って運ばれるからである。
<!--/-->

```agda
    byName-least : (a b : New δ) (t₁ t₂ : NM.Name)
                 → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                 → relOf byName a b ≡ NM._≺ₙ_ t₁ t₂
    byName-least a b t₁ t₂ h₁ h₂ = cong₂ NM._≺ₙ_ (pin a t₁ h₁) (pin b t₂ h₂)
```

<!--en-->
For every ordinal `δ`, the step order is the single order `byName`: members of `Lset (sucV δ)` are compared through their uniquely determined least names over `Lset δ`. There is no separate finite-stage or limit-stage branch in this construction.
<!--zh-->
对每个序数 `δ`，步进序都是同一个 `byName`：`Lset (sucV δ)` 的成员通过它们在 `Lset δ` 上唯一确定的最小名字来比较。这个构造不另设有穷层支或极限层支。
<!--ja-->
どの順序数 `δ` に対しても、ステップ順序は一つの `byName` である。`Lset (sucV δ)` の要素は、`Lset δ` 上で一意に定まる最小の名前を通して比較される。この構成には、有限段階用や極限段階用の別の分岐はない。
<!--/-->

```agda
  opaque
    stepAt : SWO (New δ)
    stepAt = byName
```

<!--en-->
The two bridge lemmas let us reason about `stepAt` through any representatives already proved least. For least names `t₁` and `t₂` of two members, comparison in `stepAt` and comparison of `t₁` with `t₂` determine one another. Hence later arguments need the specification of the selected names, not the particular search that produced them.
<!--zh-->
接下来的两条桥接引理使我们能借任意已证为最小的代表来推理 `stepAt`。若 `t₁` 与 `t₂` 分别是两个成员的最小名字，则 `stepAt` 中的成员比较与 `t₁`、`t₂` 的名字比较可以相互推出。因此，后文只需使用所选名字的规格，而不依赖产生它们的具体搜索过程。
<!--ja-->
次の二つの橋渡し補題により、すでに最小だと証明された任意の代表を通して `stepAt` を扱える。二つの要素の最小名をそれぞれ `t₁`、`t₂` とすれば、`stepAt` による要素の比較と `t₁`、`t₂` の名前としての比較は互いを決定する。したがって後の議論に必要なのは選ばれた名前の仕様であり、それを得た探索の具体的な過程ではない。
<!--/-->

```agda
  opaque
    unfolding stepAt
```

<!--en-->
The filling reading says: if two names are least for their respective members, then the order of the names determines the order of the members. The proof transports the name comparison through the agreement between each pinned name and the computed minimum.
<!--zh-->
填充读法说：若两个名字分别是各自成员的最小名字，则名字的序决定成员的序。证明把名字比较沿每个被钉住的名字与算出最小值之间的相合运输。
<!--ja-->
充填の読み出しはこう言う。二つの名前がそれぞれの要素の最小の名前であれば、名前の順序が要素の順序を決める。証明は、ピン止めされた名前と計算された最小値の間の一致に沿って、名前の比較を運ぶ。
<!--/-->

```agda
    stepAt-fill : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → NM._≺ₙ_ t₁ t₂ → relOf stepAt a b
    stepAt-fill a b t₁ t₂ h₁ h₂ =
      transport (sym (byName-least a b t₁ t₂ h₁ h₂))
```

<!--en-->
The reading lemma says the converse: if the step order holds between two members, the least names of those members are ordered the same way.
<!--zh-->
读取引理说其反向：若步进序在两个成员间成立，则这些成员的最小名字也以同样方式排序。
<!--ja-->
読み出しの補題はその逆を言う。ステップの順序が二つの要素の間で成立するならば、それらの要素の最小の名前も同じように順序づけられる。
<!--/-->

```agda

    stepAt-read : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → relOf stepAt a b → NM._≺ₙ_ t₁ t₂
    stepAt-read a b t₁ t₂ h₁ h₂ =
      transport (byName-least a b t₁ t₂ h₁ h₂)
```
</div>
</details>


<!--en-->
## The family
<!--zh-->
## 族
<!--ja-->
## 順序の族
<!--/-->

<!--en-->
The relation `Under δ v x y` records a comparison of the underlying sets `x` and `y` without fixing particular membership proofs in advance. It consists of two certificates placing them in `Lset (sucV δ)`, together with the comparison of the resulting members by `v`. This is an ordinary Sigma type, not a propositional truncation; only the membership certificates themselves are propositionally unique.
<!--zh-->
关系 `Under δ v x y` 记录底层集合 `x` 与 `y` 的比较，而不预先固定具体的隶属证明。它由两份把二者放入 `Lset (sucV δ)` 的证书，以及 `v` 对所得两个成员的比较组成。这是普通的 Sigma 类型，并非命题截断；只有其中的隶属证书因命题性而唯一。
<!--ja-->
関係 `Under δ v x y` は、特定の所属証明をあらかじめ固定せずに、基礎の集合 `x` と `y` の比較を記録する。二つを `Lset (sucV δ)` に置く証明と、それによって得られる要素を `v` で比較した証拠から成る。これは通常の Sigma 型であって命題的切り詰めではなく、命題的に一意なのは所属証明の部分である。
<!--/-->

```agda
Under : (δ : S) → SWO (New δ) → S → S → Type (ℓ-suc ℓ)
Under δ v x y = Σ[ hx ∈ ⟨ x ∈ˢ Lset (sucV δ) ⟩ ]
                Σ[ hy ∈ ⟨ y ∈ˢ Lset (sucV δ) ⟩ ]
                relOf v (x , hx) (y , hy)
```

<!--en-->
Given any chosen membership certificates `hx` and `hy`, `under-at` reads an `Under` comparison at those presentations. The certificates stored by `Under` need not be the same terms as `hx` and `hy`; their equality follows from the propositionality of membership.
<!--zh-->
给定任意选定的隶属证书 `hx` 与 `hy`，`under-at` 在这两个呈现上读出一条 `Under` 比较。`Under` 所携带的证书不必与 `hx`、`hy` 是同一证明项；它们的相等来自隶属的命题性。
<!--ja-->
任意に選んだ所属証明 `hx` と `hy` に対し、`under-at` はその提示で `Under` の比較を読み出す。`Under` が保持する証明は `hx` や `hy` と同じ項である必要はなく、それらの等しさは所属が命題であることから従う。
<!--/-->

```agda
under-at : (δ : S) (v : SWO (New δ)) (x y : S)
           (hx : ⟨ x ∈ˢ Lset (sucV δ) ⟩) (hy : ⟨ y ∈ˢ Lset (sucV δ) ⟩)
         → Under δ v x y → relOf v (x , hx) (y , hy)
under-at δ v x y hx hy (kx , ky , h) =
  subst2 (λ p q → relOf v (x , p) (y , q))
```

<!--en-->
This certificate alignment is what makes `Under` useful in the recursive family. Equal birth ordinals often place the same set in the same successor stage by different proofs; `under-at` lets the local comparison survive those changes of evidence without requiring the comparison type itself to be a proposition.
<!--zh-->
这种证书对齐正是 `Under` 能用于递归序族的原因。诞生序数相等时，同一集合往往由不同证明被放入同一个后继层；`under-at` 使局部比较在更换这些证据后仍可使用，而无须假定比较类型本身是命题。
<!--ja-->
この証明の整合があるからこそ、`Under` を再帰的な順序の族で用いられる。誕生順序数が等しいとき、同じ集合が異なる証明によって同じ後続段階に置かれることがある。`under-at` は、比較の型そのものが命題だと仮定せずに、証拠を取り替えた後も局所比較を使えるようにする。
<!--/-->

```agda
    (snd (x ∈ˢ Lset (sucV δ)) kx hx) (snd (y ∈ˢ Lset (sucV δ)) ky hy) h
```

<!--en-->
Fix an ordinal `γ`. To construct its stage order, assume recursively that every ordinal `δ ∈ γ` already carries a strict well-order on `Mem (Lset δ)`. The module `Family` turns precisely these smaller-stage orders into an order on the members of `Lset γ`.
<!--zh-->
固定一个序数 `γ`。为了构造这一层的序，递归地假定每个 `δ ∈ γ` 都已在 `Mem (Lset δ)` 上带有严格良序。模块 `Family` 恰用这些较小层的序构造 `Lset γ` 诸成员上的序。
<!--ja-->
順序数 `γ` を固定する。この段階の順序を構成するため、各順序数 `δ ∈ γ` について `Mem (Lset δ)` 上の狭義整列順序がすでに得られていると再帰的に仮定する。モジュール `Family` は、まさにこれらの小さい段階の順序から `Lset γ` の要素上の順序を構成する。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Family (γ : S)
              (IH : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
              (ordγ : IsOrd γ) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Member : Type (ℓ-suc ℓ)
```

<!--en-->
The carrier at this stage is `Member = Mem (Lset γ)`: an element of the hierarchy together with evidence that it belongs to the stage `Lset γ`.
<!--zh-->
这一层的载体是 `Member = Mem (Lset γ)`：一个层级中的集合，连同它属于 `Lset γ` 的证据。
<!--ja-->
この段階での台は `Member = Mem (Lset γ)` である。累積階層の集合と、それが段階 `Lset γ` に属するという証拠の組である。
<!--/-->

```agda
    Member = Mem (Lset γ)
```

<!--en-->
Because `γ` is an ordinal, membership in `Lset γ` implies constructibility. Thus every `a : Member` has the constructibility proof required to form its birth ordinal.
<!--zh-->
由于 `γ` 是序数，属于 `Lset γ` 蕴含可构造性。因此每个 `a : Member` 都有定义其诞生序数所需的可构造性证明。
<!--ja-->
`γ` は順序数なので、`Lset γ` に属する集合は構成可能である。したがって各 `a : Member` には、その誕生順序数を作るために必要な構成可能性の証明がある。
<!--/-->

```agda
    memberL : (a : Member) → ⟨ isL (a .fst) ⟩
    memberL a = Lset→isL γ ordγ (a .fst) (a .snd)
```

<!--en-->
Each layer member belongs to the successor of its own birth ordinal, by the membership reading of the birth construction.
<!--zh-->
每个层成员属于其自身诞生序数的后继，由诞生构造的隶属读式而来。
<!--ja-->
層のそれぞれの要素は、自分自身の誕生の順序数の後続に属する。誕生の構成の所属の読み出しによるものである。
<!--/-->

```agda
    newIn : (a : Member) → ⟨ a .fst ∈ˢ Lset (sucV (birth (a .fst) (memberL a))) ⟩
    newIn a = birth-mem (a .fst) (memberL a)
```

<!--en-->
The birth of a member is packaged as a member of the ordinal index `γ`: the birth ordinal together with the proof that it lies below `γ`, which follows from the member being in the layer at `γ`.
<!--zh-->
成员的诞生被打包为序数索引 `γ` 的成员：诞生序数连同「它低于 `γ`」的证明，后者由成员属于 `γ` 处的层而来。
<!--ja-->
要素の誕生は、順序数の添字 `γ` の要素としてまとめられる。誕生の順序数と、それが `γ` より下にあるという証明である。後者は、要素が `γ` での層に属することから従う。
<!--/-->

```agda
  bornAt : Member → Mem γ
  bornAt a = birth (a .fst) (memberL a)
           , birth-in γ ordγ (a .fst) (memberL a) (a .snd)
```

<!--en-->
For `d : Mem γ`, the induction hypothesis supplies an order on the certified members of `Lset (d .fst)`. The operation `carry` moves it to the small presentation used by names, and `stepAt` then well-orders the certified members of `Lset (sucV (d .fst))` by their least names. This is the local order used for sets born over `d .fst`.
<!--zh-->
对 `d : Mem γ`，归纳假设给出 `Lset (d .fst)` 的带证书成员上的序。`carry` 把它搬到名字所用的小表示类型上，随后 `stepAt` 按最小名字良序化 `Lset (sucV (d .fst))` 的带证书成员。这就是比较诞生于 `d .fst` 之上的集合时所用的局部序。
<!--ja-->
`d : Mem γ` に対し、帰納の仮定は `Lset (d .fst)` の証明つき要素上の順序を与える。`carry` はそれを名前が用いる小さい表示型へ移し、続いて `stepAt` が最小の名前によって `Lset (sucV (d .fst))` の証明つき要素を整列する。これが `d .fst` 上で誕生した集合を比較する局所順序である。
<!--/-->

```agda
  stepIn : (d : Mem γ) → SWO (New (d .fst))
  stepIn d = stepAt (d .fst) (carry (Lset (d .fst))
    (IH (d .fst) (d .snd) (mem-ord {A = γ} ordγ (d .fst) (d .snd))))
```

<!--en-->
For a packaged ordinal `d : Mem γ`, `UnderAt d a b` applies the certificate-independent relation `Under` to the local step order at `d`. In the equal-birth branch below, `d` will be the common birth of `a` and `b`.
<!--zh-->
对打包的序数 `d : Mem γ`，`UnderAt d a b` 把不依赖具体证书的关系 `Under` 用于 `d` 处的局部步进序。在下文的同生支中，`d` 将是 `a` 与 `b` 的共同诞生序数。
<!--ja-->
組にされた順序数 `d : Mem γ` に対し、`UnderAt d a b` は、証明の選び方に依存しない関係 `Under` を `d` での局所ステップ順序に適用する。以下の同じ誕生の場合には、`d` は `a` と `b` の共通の誕生順序数になる。
<!--/-->

```agda
  UnderAt : (d : Mem γ) → Member → Member → Type (ℓ-suc ℓ)
  UnderAt d a b = Under (d .fst) (stepIn d) (a .fst) (b .fst)
```

<!--en-->
The main relation is lexicographic. If the birth ordinal of `a` belongs to the birth ordinal of `b`, then `a ≺ b`. When the two birth ordinals are equal, their underlying sets are compared by the local step order at `a`'s birth. The equality is oriented from `b`'s birth to `a`'s so that the second set can be placed directly in that same local order.
<!--zh-->
主关系是字典序。若 `a` 的诞生序数属于 `b` 的诞生序数，则 `a ≺ b`。两条诞生序数相等时，则在 `a` 的诞生序数处用局部步进序比较它们的底层集合。等式从 `b` 的诞生序数指向 `a` 的诞生序数，从而可把第二个集合直接放入同一个局部序。
<!--ja-->
主関係は辞書式である。`a` の誕生順序数が `b` の誕生順序数に属するなら `a ≺ b` である。二つの誕生順序数が等しいときは、`a` の誕生順序数での局所ステップ順序によって基礎の集合を比較する。等式は `b` の誕生から `a` の誕生へ向けてあり、第二の集合を同じ局所順序へ直接置けるようになっている。
<!--/-->

```agda
  _≺_ : Member → Member → Type (ℓ-suc ℓ)
  a ≺ b = ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
        ⊎ ((bornAt b .fst ≡ bornAt a .fst) × UnderAt (bornAt a) a b)
```

<!--en-->
The packaging helper says that two members of the ordinal index with the same underlying ordinal are equal, using the propositionality of membership in the ordinal.
<!--zh-->
打包辅助说：底层序数相同的序数索引的两个成员相等，依据是序数中隶属的命题性。
<!--ja-->
まとめの補助は、同じ基礎の順序数をもつ順序数の添字の二つの要素が等しいと言う。順序数の中の所属が命題だからである。
<!--/-->

```agda
  private
    packBirth : (d z : Mem γ) → d .fst ≡ z .fst → d ≡ z
    packBirth d z = Σ≡Prop (λ v → snd (v ∈ˢ γ))
```

<!--en-->
Irreflexivity follows from the two meanings of the lexicographic relation. An early-birth witness for `a ≺ a` would make the ordinal `birth(a)` a member of itself. An equal-birth witness instead gives a local comparison of `a` with itself; its stored membership certificates may differ from `newIn a`, but `under-at` reads the comparison at the latter certificates so that local irreflexivity applies.
<!--zh-->
主序的非自反性分别来自字典序两支的含义。若 `a ≺ a` 由早生见证给出，就会使序数 `birth(a)` 属于自身。若它由同生见证给出，则得到 `a` 与自身的局部比较；其中保存的隶属证书可能不同于 `newIn a`，但 `under-at` 会在后一组证书处读出同一比较，于是可以应用局部序的非自反性。
<!--ja-->
主順序の非反射性は、辞書式関係の二つの意味から従う。`a ≺ a` が早い誕生の証拠から得られたなら、順序数 `birth(a)` が自分自身に属することになる。同じ誕生の証拠から得られたなら、`a` とそれ自身との局所比較になる。そこに保存された所属証明は `newIn a` と異なりうるが、`under-at` が後者の証明で同じ比較を読み出すので、局所順序の非反射性を適用できる。
<!--/-->

```agda
  private
    ≺-irr : (a : Member) → a ≺ a → ⊥₀
    ≺-irr a (inl h) = ∈-irrefl (bornAt a .fst) h
    ≺-irr a (inr (_ , u)) =
      SWO.irr∙ (stepIn (bornAt a)) (a .fst , newIn a)
```

<!--en-->
Only the membership certificates are replaced in this passage. Their propositionhood identifies the two presentations of `a`, while the local comparison proof is transported unchanged to the presentation at which the strict well-order forbids self-comparison.
<!--zh-->
这里更换的只有隶属证书。证书的命题性认同 `a` 的两种呈现，而局部比较证明则原样搬运到严格良序禁止自比较的那种呈现上。
<!--ja-->
ここで取り替えるのは所属証明だけである。その命題性によって `a` の二つの表示が同一視され、局所比較の証明は、狭義整列順序が自己比較を禁じる表示へそのまま輸送される。
<!--/-->

```agda
        (under-at (bornAt a .fst) (stepIn (bornAt a)) (a .fst) (a .fst)
          (newIn a) (newIn a) u)
```

<!--en-->
Transitivity has four cases. In the early-early case, transitivity of the birth ordinals composes the two strict memberships. In the early-equal case, the equality transports the birth membership past the common birth ordinal.
<!--zh-->
传递性有四种情形。早早情形由诞生序数的传递性复合两条严格隶属；早等情形由等式把诞生隶属搬运过共同诞生序数。
<!--ja-->
推移性には四つの場合がある。早い・早いの場合は、誕生の順序数の推移性が二つの厳密な所属を合成する。早い・等しいの場合は、等式が誕生の所属を共通の誕生の順序数の先へ運ぶ。
<!--/-->

```agda
    ≺-trans : (a b c : Member) → a ≺ b → b ≺ c → a ≺ c
    ≺-trans a b c (inl h) (inl k) =
      inl (birth-ord (c .fst) (memberL c) .fst h k)
    ≺-trans a b c (inl h) (inr (e , _)) =
      inl (subst (λ v → ⟨ bornAt a .fst ∈ˢ v ⟩) (sym e) h)
```

<!--en-->
The remaining mixed case transports the strict inequality between birth ordinals across their equality. When both comparisons use the equal-birth branch, the two equalities identify a single birth ordinal, and transitivity reduces to composing the two comparisons in its local step order.
<!--zh-->
余下的混合情形沿诞生序数的等式搬运它们之间的严格不等关系。当两条比较都走同生支时，两条等式把诞生序数认作同一个，传递性便归结为在该处的局部步进序中复合两条比较。
<!--ja-->
残る混合の場合では、誕生順序数の間の真の大小関係を、それらの等式に沿って移す。二つの比較がともに同じ誕生の場合なら、二つの等式が誕生順序数を一つに同定し、推移性はその局所ステップ順序で二つの比較を合成することに帰着する。
<!--/-->

```agda
    ≺-trans a b c (inr (e , _)) (inl k) =
      inl (subst (λ v → ⟨ v ∈ˢ bornAt c .fst ⟩) e k)
    ≺-trans a b c (inr (e , u)) (inr (eb , v)) = inr (eb ∙ e , joined)
      where
      d : Mem γ
```

<!--en-->
In the equal-equal case, take `d = bornAt a` as the common packaged birth. The first comparison already lives in the local order `stepIn d`. Equality of the packaged births transports the second comparison from the local order indexed by `bornAt b` to that same `stepIn d`; this alignment is necessary because the local order depends on its packaged index.
<!--zh-->
在同生与同生的情形，取 `d = bornAt a` 为共同的打包诞生。第一条比较已经位于局部序 `stepIn d` 中。打包诞生的相等把第二条比较从以 `bornAt b` 为指标的局部序搬到同一个 `stepIn d`；这一步不可省略，因为局部序依赖其打包指标。
<!--ja-->
同じ誕生どうしの場合には、`d = bornAt a` を共通の、証明と組にされた誕生とする。第一の比較はすでに局所順序 `stepIn d` の中にある。組にされた誕生の等しさに沿って、第二の比較を `bornAt b` を添字とする局所順序から同じ `stepIn d` へ移す必要がある。局所順序が組にされた添字に依存するためである。
<!--/-->

```agda
      d = bornAt a
      moved : UnderAt d b c
      moved = subst (λ z → UnderAt z b c) (packBirth (bornAt b) d e) v
      joined : UnderAt d a c
      joined = u .fst , (moved .snd .fst
```

<!--en-->
Both premises can now be read inside one strict well-order. The certificates carried by the two `UnderAt` witnesses are aligned at the middle set `b`, and transitivity of `stepIn d` composes the local comparisons from `a` to `b` and from `b` to `c`.
<!--zh-->
此时两条前提都能在同一严格良序中读取。两份 `UnderAt` 见证所携带的证书在中间集合 `b` 处对齐，`stepIn d` 的传递性便把从 `a` 到 `b` 与从 `b` 到 `c` 的局部比较复合起来。
<!--ja-->
これで二つの前提を一つの狭義整列順序の中で読める。二つの `UnderAt` の証拠が運ぶ所属証明を中間の集合 `b` でそろえ、`stepIn d` の推移性によって `a` から `b`、`b` から `c` への局所比較を合成する。
<!--/-->

```agda
        , SWO.trans∙ (stepIn d) (a .fst , u .fst) (b .fst , moved .fst)
            (c .fst , moved .snd .fst)
            (under-at (d .fst) (stepIn d) (a .fst) (b .fst)
              (u .fst) (moved .fst) u)
            (under-at (d .fst) (stepIn d) (b .fst) (c .fst)
```

<!--en-->
The composite local comparison, together with the endpoint certificates already obtained at the common birth, is an `UnderAt d a c` witness. Thus the equal-birth branch is transitive for the same mathematical reason as the name order beneath it: all three sets are compared in one fixed local order.
<!--zh-->
复合后的局部比较连同共同诞生处已有的两个端点证书，组成一份 `UnderAt d a c` 见证。因此同生支具有传递性，理由与其下的名字序相同：三个集合都在同一个固定局部序中比较。
<!--ja-->
合成した局所比較と、共通の誕生においてすでに得られた両端の所属証明を合わせると、`UnderAt d a c` の証拠になる。したがって同じ誕生の場合が推移的なのは、その下にある名前順序と同じ理由による。三つの集合が一つの固定した局所順序で比較されているからである。
<!--/-->

```agda
              (moved .fst) (moved .snd .fst) moved))
```

<!--en-->
For trichotomy, first compare the two birth ordinals. Their ordinality proofs make ordinal trichotomy applicable, producing exactly the alternatives「the first birth is earlier」，「the births are equal」，and“the second birth is earlier”. Only the middle alternative requires a comparison in a local step order.
<!--zh-->
为证明三歧性，先比较两条诞生序数。它们的序数性证明使序数三歧性可用，从而恰好得到「第一条诞生更早」「两条诞生相等」「第二条诞生更早」三种情形。只有中间情形需要诉诸局部步进序。
<!--ja-->
三分性を示すには、まず二つの誕生順序数を比較する。それぞれの順序数性の証明によって順序数の三分性を適用でき、「第一の誕生が早い」「誕生が等しい」「第二の誕生が早い」という三つの場合が得られる。局所的なステップ順序で比較する必要があるのは、中央の場合だけである。
<!--/-->

```agda
    ≺-tri : (a b : Member) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    ≺-tri a b = byBirth (ord-tri (bornAt a .fst) (birth-ord (a .fst) (memberL a))
                                 (bornAt b .fst) (birth-ord (b .fst) (memberL b)))
      where
      byBirth : ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
```

<!--en-->
When the births differ, their strict ordinal comparison already decides the main order. No name of either set is inspected in these two cases; the least-name order is reserved for sets with a common birth ordinal.
<!--zh-->
诞生序数不同时，它们之间的严格序数比较已经决定主序。这两种情形都不查看任一集合的名字；最小名字序只用于诞生序数相同的集合。
<!--ja-->
誕生が異なる場合、その順序数としての狭義比較だけで主順序が決まる。この二つの場合には、どちらの集合の名前も調べない。最小名の順序を使うのは、共通の誕生順序数をもつ集合に限られる。
<!--/-->

```agda
              ⊎ ((bornAt a .fst ≡ bornAt b .fst) ⊎ ⟨ bornAt b .fst ∈ˢ bornAt a .fst ⟩)
              → Tri (a ≺ b) (a ≡ b) (b ≺ a)
      byBirth (inl h)       = lt (inl h)
      byBirth (inr (inr h)) = gt (inl h)
      byBirth (inr (inl e)) =
```

<!--en-->
In the equal-birth case, the local step order at the common birth ordinal decides the comparison. The two members' certificates are realigned to the common birth ordinal.

The alignment of the first certificate is the member's own successor membership.
<!--zh-->
等诞生情形中，共同诞生序数处的局部步进序决定比较。两个成员的证书被重新对齐到共同诞生序数。

第一条证书的对齐即该成员自身的后继隶属。
<!--ja-->
等しい誕生の場合は、共通の誕生の順序数での局所のステップの順序が比較を決める。二つの要素の証明は、共通の誕生の順序数へと揃え直される。

最初の証明の揃えは、その要素自身の後続の所属である。
<!--/-->

```agda
        bySteps (SWO.tri∙ (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
        where
        same : bornAt b .fst ≡ bornAt a .fst
        same = sym e
        ha : ⟨ a .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
```

<!--en-->
The first set already belongs to the successor of its birth. Equality of births transports the corresponding certificate for the second set to that same successor layer, so the local trichotomy can compare both members in one carrier.
<!--zh-->
第一个集合本来就属于其诞生序数的后继层。诞生序数的相等把第二个集合的相应证书搬到同一个后继层，于是局部三歧可以在同一载体中比较两个成员。
<!--ja-->
第一の集合はもともと自分の誕生順序数の後続段階に属する。誕生順序数の等しさによって、第二の集合の対応する証明も同じ後続段階へ移されるので、局所的な三分性は一つの台の中で両者を比較できる。
<!--/-->

```agda
        ha = newIn a
        hb : ⟨ b .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
        hb = subst (λ v → ⟨ b .fst ∈ˢ Lset (sucV v) ⟩) (sym e) (newIn b)
        bySteps : Tri (relOf (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
                      ((a .fst , ha) ≡ (b .fst , hb))
```

<!--en-->
Local trichotomy supplies comparison in either direction or equality of the two certified successor-stage members. In the equality case, equality of the underlying sets follows immediately; since membership in `Lset γ` is a proposition, that equality lifts to equality of the original members `a` and `b` of the stage.
<!--zh-->
局部三歧性给出两个带证书后继层成员的一个比较方向，或给出二者相等。相等情形立即推出底层集合相等；又因属于 `Lset γ` 是命题，这条等式提升为原层成员 `a` 与 `b` 的相等。
<!--ja-->
局所順序の三分性から、証明つきの二つの後続段階要素について、いずれかの向きの比較または等しさが得られる。等しい場合には基礎の集合の等しさが直ちに従い、`Lset γ` への所属は命題なので、その等しさは元の段階要素 `a` と `b` の等しさへ持ち上がる。
<!--/-->

```agda
                      (relOf (stepIn (bornAt a)) (b .fst , hb) (a .fst , ha))
                → Tri (a ≺ b) (a ≡ b) (b ≺ a)
        bySteps (lt h) = lt (inr (same , (ha , hb , h)))
        bySteps (eq q) = eq (Σ≡Prop (λ v → snd (v ∈ˢ Lset γ)) (cong fst q))
        bySteps (gt h) = gt (inr (sym same
```

<!--en-->
If the local trichotomy places `b` below `a`, the common-birth equality is reoriented and the packaged birth index is transported accordingly. This produces the right-hand alternative `b ≺ a` of the main trichotomy.
<!--zh-->
若局部三歧把 `b` 排在 `a` 之前，就反向使用共同诞生序数的等式，并相应搬运打包的诞生索引。这样便得到主三歧的右侧选项 `b ≺ a`。
<!--ja-->
局所的な三分性が `b` を `a` より下に置く場合、共通の誕生順序数の等式の向きを変え、それに合わせて組にされた誕生の添字を移す。これにより、主な三分性の右側の選択肢 `b ≺ a` が得られる。
<!--/-->

```agda
          , subst (λ z → UnderAt z b a)
              (packBirth (bornAt a) (bornAt b) (sym same)) (hb , ha , h)))
```

<!--en-->
Well-foundedness requires two coordinated descents. Fix a packaged birth ordinal `d`. The outer hypothesis supplies accessibility for members whose births are strictly below `d`, while an accessibility tree for `stepIn d` supplies the inner descent among members born at `d`. The role of `accInside` is to lift this inner tree to accessibility for the full lexicographic relation while retaining access to the outer hypothesis.
<!--zh-->
良基性需要两种相互配合的下降。固定一条打包诞生序数 `d`。外层假设为诞生严格低于 `d` 的成员提供可及性，而 `stepIn d` 的可及树处理同在 `d` 处诞生的成员之间的内层下降。`accInside` 的作用，是在保留外层假设可用的同时，把这棵内层树提升为主字典序下的可及性。
<!--ja-->
整礎性には、連携する二つの降下が必要である。証明と組にされた誕生順序数 `d` を固定する。外側の仮定は、誕生が `d` より真に下にある要素の到達可能性を与え、`stepIn d` の到達可能性の木は、`d` で生まれた要素間の内側の降下を扱う。`accInside` の役割は、外側の仮定を使えるまま、この内側の木を主辞書式関係についての到達可能性へ持ち上げることである。
<!--/-->

```agda
  private
    accInside : (d : Mem γ)
              → ((z : Mem γ) → ⟨ z .fst ∈ˢ d .fst ⟩
                 → (b : Member) → bornAt b ≡ z → Acc _≺_ b)
              → (u : New (d .fst)) → Acc (relOf (stepIn d)) u
```

<!--en-->
Assume that a local element `u` is accessible in `stepIn d`, and that a stage member `b` has birth `d` and the same underlying set as `u`. To prove `b` accessible for the main relation, consider an arbitrary predecessor `c ≺ b`. The definition of the main relation tells us which of the two descent resources applies to `c`.
<!--zh-->
设局部元素 `u` 在 `stepIn d` 中可及，并且层成员 `b` 的诞生为 `d`，其底层集合与 `u` 相同。要证明 `b` 对主关系可及，就考察任意前驱 `c ≺ b`。主关系的定义会指出应当对 `c` 使用两种下降资源中的哪一种。
<!--ja-->
局所要素 `u` が `stepIn d` で到達可能であり、段階要素 `b` の誕生が `d` で、その基礎の集合が `u` と等しいとする。主関係について `b` が到達可能だと示すには、任意の先行元 `c ≺ b` を考える。主関係の定義から、`c` に二つの降下資源のどちらを使うべきかが分かる。
<!--/-->

```agda
              → (b : Member) → bornAt b ≡ d → b .fst ≡ u .fst → Acc _≺_ b
    accInside d ih u (acc r) b q qu = acc step
      where
      step : (c : Member) → c ≺ b → Acc _≺_ c
      step c (inl h) = ih (bornAt c)
```

<!--en-->
If `c` was compared with `b` by an earlier birth, its birth is strictly below `d`, so the outer induction hypothesis makes `c` accessible. If their births agree, `c` is a predecessor of `u` in the fixed local order, and the accessibility tree of `u` supplies the smaller inner subtree. These are precisely the two clauses of the lexicographic relation.
<!--zh-->
若 `c` 因诞生更早而排在 `b` 之前，则它的诞生严格低于 `d`，外层归纳假设由此证明 `c` 可及。若二者同生，则 `c` 是固定局部序中 `u` 的前驱，`u` 的可及树便给出相应的较小内层子树。这恰好对应字典序关系的两项子句。
<!--ja-->
`c` がより早い誕生によって `b` より前に置かれたなら、その誕生は `d` より真に下にあり、外側の帰納仮定から `c` の到達可能性が得られる。誕生が等しいなら、`c` は固定した局所順序における `u` の先行元であり、`u` の到達可能性の木が対応する小さい内側の部分木を与える。これは辞書式関係の二つの条項にちょうど対応する。
<!--/-->

```agda
        (subst (λ v → ⟨ bornAt c .fst ∈ˢ v ⟩) (cong fst q) h) c refl
      step c (inr (eb , v)) =
        accInside d ih (c .fst , hc) (r (c .fst , hc) below) c qc refl
        where
        qc : bornAt c ≡ d
```

<!--en-->
In the equal-birth clause, equality of the underlying birth ordinals is first lifted to equality of their packaged members of `γ`. This permits the `UnderAt` comparison to be transported to the fixed index `d`; its first component then certifies that `c` belongs to the successor stage on which `stepIn d` is defined.
<!--zh-->
在同生子句中，先把底层诞生序数的相等提升为它们作为 `γ` 成员的打包相等。于是可以把 `UnderAt` 比较搬到固定指标 `d`；其第一分量随即证明 `c` 属于 `stepIn d` 所定义在的后继层。
<!--ja-->
同じ誕生の条項では、まず基礎となる誕生順序数の等しさを、それらを `γ` の要素として証明と組にしたものの等しさへ持ち上げる。これにより `UnderAt` の比較を固定した添字 `d` へ輸送でき、その第一成分から、`c` が `stepIn d` の定義域である後続段階に属することが分かる。
<!--/-->

```agda
        qc = packBirth (bornAt c) d (sym eb ∙ cong fst q)
        moved : UnderAt d c b
        moved = subst (λ z → UnderAt z c b) qc v
        hc : ⟨ c .fst ∈ˢ Lset (sucV (d .fst)) ⟩
        hc = moved .fst
```

<!--en-->
Reading the transported `UnderAt` witness with the aligned certificates gives a comparison from the local representative of `c` to that of `b`. The assumed equality between the underlying sets of `b` and `u` changes the right endpoint to `u`. The resulting local predecessor proof selects the subtree below `u`, and recursion lifts that subtree back to accessibility for `c` in the main order.
<!--zh-->
用对齐后的证书读取经搬运的 `UnderAt` 见证，便得到从 `c` 的局部代表到 `b` 的局部代表的比较。由 `b` 与 `u` 底层集合相等，可把右端点改为 `u`。所得局部前驱证明从 `u` 下方选出相应子树，递归再把这棵子树提升为 `c` 对主序的可及性。
<!--ja-->
輸送した `UnderAt` の証拠を、そろえた所属証明で読むと、`c` の局所代表から `b` の局所代表への比較が得られる。`b` と `u` の基礎の集合が等しいという仮定によって右端を `u` に替えると、得られた局所的な先行元の証明が `u` の下の部分木を選ぶ。再帰によって、その部分木が主順序についての `c` の到達可能性へ持ち上げられる。
<!--/-->

```agda
        below : relOf (stepIn d) (c .fst , hc) u
        below = subst (λ z → relOf (stepIn d) (c .fst , hc) z)
          (Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV (d .fst)))) qu)
          (under-at (d .fst) (stepIn d) (c .fst) (b .fst)
            hc (moved .snd .fst) moved)
```

<!--en-->
The outer descent is membership induction on the birth ordinal. Its motive says that every stage member whose packaged birth is `(δ , i)` is accessible for the main relation. Consequently, at the induction step for `δ`, the hypothesis covers exactly the members whose births are packaged over ordinals strictly belonging to `δ`.
<!--zh-->
外层下降是对诞生序数作隶属归纳。其动机断言：每个打包诞生为 `(δ , i)` 的层成员都对主关系可及。因此在 `δ` 处的归纳步中，归纳假设恰好覆盖那些诞生序数严格属于 `δ` 的成员。
<!--ja-->
外側の降下は誕生順序数についての所属帰納法である。その動機は、証明と組にされた誕生が `(δ , i)` であるすべての段階要素が、主関係について到達可能だと述べる。したがって `δ` における帰納段階の仮定は、誕生順序数が真に `δ` に属する要素をちょうど覆う。
<!--/-->

```agda

    accByBirth : (δ : S) (i : ⟨ δ ∈ˢ γ ⟩)
               → (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
    accByBirth = ∈-induction {P = Motive} outer
      where
      Motive : S → Type (ℓ-suc ℓ)
```

<!--en-->
At a fixed birth `δ`, the local strict well-order already makes the corresponding representative of `b` accessible. The outer step feeds this local accessibility and the hypotheses for all smaller births into `accInside`. This is where the inner descent is started inside the outer membership induction.
<!--zh-->
固定诞生序数 `δ` 后，局部严格良序已经保证 `b` 的相应代表可及。外层归纳步把这份局部可及性与所有更早诞生处的归纳假设一同交给 `accInside`。内层下降正是在外层隶属归纳的这一位置启动。
<!--ja-->
誕生順序数 `δ` を固定すると、局所的な狭義整列順序によって、対応する `b` の代表はすでに到達可能である。外側の帰納段階は、この局所的な到達可能性と、より早いすべての誕生に対する帰納仮定とを `accInside` に渡す。ここで外側の所属帰納法の内部に内側の降下が始まる。
<!--/-->

```agda
      Motive δ = (i : ⟨ δ ∈ˢ γ ⟩) (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
      outer : (δ : S) → ((z : S) → ⟨ z ∈ˢ δ ⟩ → Motive z) → Motive δ
      outer δ ih i b q = accInside (δ , i) inner (b .fst , hb)
        (SWO.wf∙ (stepIn (δ , i)) (b .fst , hb)) b q refl
        where
```

<!--en-->
The equality `q` identifies the packaged birth of `b` with `(δ , i)`, so `birth-mem` can be transported to a certificate `hb` placing `b` in `Lset (sucV δ)`. For a smaller packaged birth `z`, its first component lies in `δ`; the outer induction hypothesis at that ordinal, together with `z`'s membership in `γ`, supplies accessibility for every member born at `z`.
<!--zh-->
等式 `q` 把 `b` 的打包诞生认同为 `(δ , i)`，因而可以搬运 `birth-mem`，得到把 `b` 放入 `Lset (sucV δ)` 的证书 `hb`。对更小的打包诞生 `z`，其第一分量属于 `δ`；在该序数处的外层归纳假设，连同 `z` 属于 `γ` 的证明，为每个诞生于 `z` 的成员给出可及性。
<!--ja-->
等式 `q` は、証明と組にされた `b` の誕生を `(δ , i)` と同一視する。そのため `birth-mem` を輸送して、`b` を `Lset (sucV δ)` に置く証明 `hb` を得られる。より小さい、証明と組にされた誕生 `z` については、その第一成分が `δ` に属する。その順序数における外側の帰納仮定と、`z` が `γ` に属することの証明から、`z` で生まれたすべての要素の到達可能性が得られる。
<!--/-->

```agda
        hb : ⟨ b .fst ∈ˢ Lset (sucV δ) ⟩
        hb = subst (λ z → ⟨ b .fst ∈ˢ Lset (sucV (z .fst)) ⟩) q (newIn b)
        inner : (z : Mem γ) → ⟨ z .fst ∈ˢ δ ⟩
              → (c : Member) → bornAt c ≡ z → Acc _≺_ c
        inner z h c qz = ih (z .fst) h (z .snd) c qz
```

<!--en-->
Every member is therefore accessible for the main relation. The conclusion uses both layers: the outer membership induction handles a predecessor with an earlier birth, and at each fixed birth the accessibility tree of the local step order handles a predecessor with the same birth. Neither layer alone proves well-foundedness of the lexicographic order.
<!--zh-->
因此每个成员都对主关系可及。这个结论同时使用两层论证：外层隶属归纳处理诞生更早的前驱，而在每个固定诞生序数处，局部步进序的可及树处理同生前驱。缺少其中任何一层，都不足以证明该字典序良基。
<!--ja-->
したがって、すべての要素は主関係について到達可能である。この結論には二つの層がともに必要である。外側の所属帰納法は誕生がより早い先行元を扱い、各誕生順序数を固定したところでは、局所ステップ順序の到達可能性の木が同じ誕生の先行元を扱う。どちらか一方だけでは、この辞書式順序の整礎性は示せない。
<!--/-->

```agda

    ≺-wf : WellFounded _≺_
    ≺-wf a = accByBirth (bornAt a .fst) (bornAt a .snd) a refl
```

<!--en-->
The lexicographic relation and the proofs just established now form a strict well-order on `Mem (Lset γ)`: birth ordinals give the primary comparison, and the least-name step order resolves equal births.
<!--zh-->
刚才建立的字典序关系及其证明现在组成 `Mem (Lset γ)` 上的严格良序：诞生序数给出第一层比较，最小名字的步进序处理诞生序数相等的情形。
<!--ja-->
ここまでに得た辞書式関係とその証明から、`Mem (Lset γ)` 上の狭義整列順序ができる。誕生順序数が第一の比較を与え、誕生が等しい場合を最小の名前によるステップ順序が決める。
<!--/-->

```agda
  famOrder : SWO (Mem (Lset γ))
  famOrder = record
    { _<∙_   = _≺_
    ; tri∙   = ≺-tri
    ; irr∙   = ≺-irr
```

<!--en-->
Transitivity and the two-level well-foundedness argument complete the order laws, so `famOrder` is available from the assumed orders at all smaller ordinal stages.
<!--zh-->
传递性与双层良基性论证补齐序定律，因此从所有较小序数层处的已知序即可得到 `famOrder`。
<!--ja-->
推移性と二段階の整礎性の議論によって順序法則が揃い、すべての小さい順序数段階で仮定した順序から `famOrder` が得られる。
<!--/-->

```agda
    ; trans∙ = ≺-trans
    ; wf∙    = ≺-wf }
```
</div>
</details>


<!--en-->
The function `famStep` packages this recursive step: at `γ`, it takes the orders already constructed at every member ordinal `δ ∈ γ` and returns the strict well-order of `Mem (Lset γ)` proved above. The same construction applies uniformly to every ordinal; it has no separate zero, successor, or limit clause.
<!--zh-->
函数 `famStep` 封装这次递归步：在 `γ` 处，它接收每个成员序数 `δ ∈ γ` 上已经构造的序，返回上文证明的 `Mem (Lset γ)` 上的严格良序。同一个构造统一适用于每个序数，并无另设的零、后继或极限分支。
<!--ja-->
関数 `famStep` はこの再帰の一段をまとめる。`γ` において、各要素順序数 `δ ∈ γ` ですでに構成された順序を受け取り、上で証明した `Mem (Lset γ)` 上の狭義整列順序を返す。同じ構成がどの順序数にも一様に適用され、零、後続、極限の別々の節はない。
<!--/-->

```agda
famStep : (γ : S) → ((δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
        → IsOrd γ → SWO (Mem (Lset γ))
famStep = Family.famOrder
```

<!--en-->
Membership induction applies `famStep` simultaneously at all ordinal indices. The result `orderAt γ` is a host-level strict well-order on the certified members of the single stage `Lset γ`; it is neither an object-language relation nor one relation on all of `L`.
<!--zh-->
隶属归纳在所有序数索引处同时施用 `famStep`。所得 `orderAt γ` 是宿主层中单个层 `Lset γ` 的带证书成员上的严格良序；它既不是对象语言中的关系，也不是整个 `L` 上的一条关系。
<!--ja-->
所属帰納法によって、すべての順序数添字で `famStep` を同時に適用する。得られる `orderAt γ` は、単一の段階 `Lset γ` の証明つき要素上にあるホスト側の狭義整列順序である。対象言語内の関係でも、`L` 全体の上の一つの関係でもない。
<!--/-->

```agda
opaque
  orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))
  orderAt = ∈-induction famStep
```

<!--en-->
The equation `orderAt-step` exposes one recursive layer: the order at `γ` is `famStep γ` applied to the previously constructed orders `orderAt δ` for `δ ∈ γ`. It permits later arguments to use the birth-first description without unfolding the entire membership recursion.
<!--zh-->
等式 `orderAt-step` 展开一层递归：`γ` 处的序就是把 `famStep γ` 施用于每个 `δ ∈ γ` 处先前构造的 `orderAt δ`。后文由此可以使用诞生优先的描述，而无须展开整个隶属递归。
<!--ja-->
等式 `orderAt-step` は再帰を一段だけ開く。`γ` での順序は、各 `δ ∈ γ` ですでに構成された `orderAt δ` に `famStep γ` を適用したものである。これにより後の議論は、所属再帰全体を展開せずに誕生を先に比較する記述を使える。
<!--/-->

```agda
opaque
  unfolding orderAt
  orderAt-step : (γ : S) → orderAt γ ≡ famStep γ (λ δ _ → orderAt δ)
  orderAt-step = ∈-induction-compute famStep
```

<!--en-->
Finally, `stageOrder γ` presents the same stagewise order on the small index type `⟪ Lset γ ⟫`. The canonical embedding sends each index to its represented member with a membership certificate, and `carry` pulls `orderAt γ` back along this injection. This changes only the representation of the carrier, not the comparison being constructed.
<!--zh-->
最后，`stageOrder γ` 把同一条逐层序呈现在小索引类型 `⟪ Lset γ ⟫` 上。典范嵌入把每个索引送到它所表示的成员及其隶属证书，`carry` 再沿这条单射拉回 `orderAt γ`。这里改变的只是载体的表示，并未另造一种比较。
<!--ja-->
最後に `stageOrder γ` は、同じ段階ごとの順序を小さい添字型 `⟪ Lset γ ⟫` 上に提示する。標準的な埋め込みは各添字を、それが表す要素と所属証明の組へ送り、`carry` はこの単射に沿って `orderAt γ` を引き戻す。変わるのは台の表示だけで、別の比較を構成するわけではない。
<!--/-->

```agda
stageOrder : (γ : S) → IsOrd γ → SWO ⟪ Lset γ ⟫
stageOrder γ oγ = carry (Lset γ) (orderAt γ oγ)
```

<!--en-->
## Recap

For every ordinal `γ`, `orderAt γ` is a host-level strict well-order on the certified members of `Lset γ`. It first compares the predecessors of the members' earliest containing stages, and only for equal births compares their uniquely determined least names over the common earlier stage. The local `stepAt` construction has this one least-name form at every index, while the global well-foundedness proof combines descent of birth ordinals with descent in the local name order. The relation has not yet been turned into an object-language formula or a set belonging to `L`; later chapters perform those internalization steps.
<!--zh-->
## 小结

对每个序数 `γ`，`orderAt γ` 是宿主层中 `Lset γ` 的带证书成员上的严格良序。它先比较各成员最早包含层的前驱；只有诞生序数相等时，才比较它们在共同前层之上唯一确定的最小名字。局部构造 `stepAt` 在每个指标处都只有这一种最小名字形式，而全局良基性证明把诞生序数的下降与局部名字序中的下降结合起来。此处尚未把该关系写成对象语言公式，也未把它构造成 `L` 中的集合；这些内部化步骤留给后续章节。
<!--ja-->
## まとめ

各順序数 `γ` に対し、`orderAt γ` は `Lset γ` の証明つき要素上にある、周囲の型理論での狭義整列順序である。まず各要素を最初に含む段階の先行者を比較し、誕生順序数が等しい場合に限って、共通の前段階上で一意に定まる最小名を比較する。局所構成 `stepAt` はどの添字でもこの一つの最小名による形をとり、大域的な整礎性の証明は、誕生順序数の降下と局所的な名前順序の降下を組み合わせる。この関係はまだ対象言語の論理式にも、`L` に属する集合にもなっていない。それらの内部化は後の章で行う。
<!--/-->
