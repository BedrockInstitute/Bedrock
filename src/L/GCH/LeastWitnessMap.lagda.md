```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The least-witness map inside a constructible stage
<!--zh-->
# 可构造层内的最小见证映射
<!--ja-->
# 構成可能な段階における最小の証人の写像
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and excluded middle for propositions at level `ℓ-suc ℓ`. Every selected witness and every graph constructed below is relative to this single hypothesis and to the fixed stage order introduced later.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上命题的排中律。下文选出的每个见证和构造的每个图，都相对于这一条假设以及稍后固定的层序。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` の命題に対する排中律を固定する。以下で選ぶ各証人と構成する各グラフは、この一つの仮定と、後で固定する段階順序に相対的である。
<!--/-->

```agda
module L.GCH.LeastWitnessMap {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∀̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Semantics
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Choice.StageOrders {ℓ} lem using ( orderAt; relOf ) renaming ( Mem to MemOf )
open import L.Choice.InternalWellOrder {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; leastOfFormula; lt; eq; gt ) renaming ( Tri to Tri∙ )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Graph )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( isL-ord )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )
```

<!--en-->

Suppose that, for each input `x ∈ X`, we know only under propositional truncation that some `w ∈ Lset γ` satisfies `P(w,x)`. Such pointwise existence does not yet give a graph inside `L`, because one formula must determine a unique value. This chapter uses the canonical strict well order of the fixed stage to choose its least satisfying candidate, expresses that choice by a formula, and collects the graph as a set of `L`. The minimum is relative to this stage and this order, and `P` itself may have many witnesses.
<!--zh-->

设对每个输入 `x ∈ X`，我们只在命题截断下知道存在某个 `w ∈ Lset γ` 满足 `P(w,x)`。这种逐点存在还不能给出 `L` 内的函数图，因为必须有同一条公式确定唯一取值。本章利用固定层的典范严格良序，选取其中最小的满足候选，再以公式表达这一选取，并把图收集为 `L` 的集合。这里的最小元只相对于这个层与这条序，而 `P` 本身可以有许多见证。
<!--ja-->

各入力 `x ∈ X` について、`P(w,x)` を満たす `w ∈ Lset γ` があることを、命題的切り詰めのもとでだけ知っているとする。この各点での存在だけでは、`L` の内部にグラフはまだ得られない。一つの論理式が値を一意に定める必要があるからである。この章では、固定された段階の正準な狭義整列順序を使って条件を満たす最小の候補を選び、その選択を論理式で表し、グラフを `L` の集合として集める。最小性はこの段階とこの順序に相対的であり、`P` 自体は多数の証人をもってかまわない。
<!--/-->

<!--en-->
Classical logic enters through the fixed excluded-middle hypothesis, which already underlies the canonical stage order. At the actual least-element search, it has a precise role: during well-founded descent it decides whether a smaller satisfying stage member merely exists. Propositional truncation is eliminated only into the total type of least witnesses, after that type has been proved to be a proposition; this gives no general way to extract arbitrary witnesses.
<!--zh-->
经典逻辑经由固定的排中律假设进入，而层上的典范序本身已经依赖这一假设。在实际搜索最小元时，它承担一个明确职责：沿良基序下降的每一步，判定是否仅仅存在一个更小且满足谓词的层成员。命题截断只在「最小见证的总类型」已经证明为命题之后消去到该类型；这并不提供从任意命题截断中抽取见证的一般方法。
<!--ja-->
古典論理は、固定した排中律の仮定を通して入る。段階上の正準な順序も、すでにこの仮定に依存している。実際の最小要素の探索での役割は明確である。整礎的に降下する各段階で、条件を満たすより小さい段階の要素が単に存在するかを判定する。命題的切り詰めを除去する先は、最小の証人からなる全体型が命題であると示した後の、その型だけである。任意の切り詰めから証人を取り出す一般的方法が得られるわけではない。
<!--/-->



<!--en-->
The desired graph must be expressed in the first-order language of sets. Besides saying that `P(w,x)` holds, its formula must say that `w` lies in the chosen stage and that no smaller member of that stage also satisfies `P`. A bounded universal quantifier expresses the latter condition, while renaming lets the original two-variable formula keep its meaning after the smaller candidate is inserted into the environment.
<!--zh-->
所需的图必须用集合论的一阶对象语言表达。除了断言 `P(w,x)` 成立，其公式还须断言 `w` 位于选定层中，并且该层中没有更小的成员也满足 `P`。后一个条件由有界全称量词表达；把更小候选插入环境后，改名使原二元公式仍保持原义。
<!--ja-->
求めるグラフは、集合論の一階対象言語で表さなければならない。`P(w,x)` が成り立つことに加えて、`w` が選んだ段階に属し、その段階には `P` を満たすより小さい要素がないことも論理式で述べる必要がある。後者は有界の全称量化子で表し、より小さい候補を環境へ挿入した後も、名前替えによってもとの二変数論理式の意味を保つ。
<!--/-->

<!--en-->
Two views of the stage order are needed. The host-level strict well order supports least-element search, while a constructible set `Rγ` of coded ordered pairs lets the same comparison appear inside the object-language graph formula. The representation lemmas pass between these views; they do not identify them by definition.
<!--zh-->
这里需要层序的两种读法。宿主层的严格良序支持最小元搜索；由编码有序对构成的可构造集合 `Rγ` 则让同一比较能出现在对象语言的图公式中。表示引理在两种读法之间转换，但二者并非按定义相同。
<!--ja-->
ここでは段階順序を二通りに読む必要がある。ホスト側の狭義整列順序は最小要素の探索を支え、符号化された順序対からなる構成可能集合 `Rγ` は、同じ比較を対象言語のグラフ論理式に現する。表示補題は二つの読みの間を移るが、両者を定義によって同一視するものではない。
<!--/-->

<!--en-->
The strict well order supplies both a least-element operation and trichotomy. The former selects a value from a merely inhabited family of candidates; the latter proves that any two candidates satisfying the complete leastness specification coincide. Once that specification is expressed by a formula, replacement collects the resulting input-value pairs into a set of `L`.
<!--zh-->
严格良序同时提供最小元操作与三歧性。前者从仅仅非空的候选族中选出一个值；后者证明，任何两个满足完整最小性规格的候选必然重合。把这一规格写成公式后，替换把所得的输入值对收集为 `L` 的集合。
<!--ja-->
狭義整列順序は、最小要素を得る操作と三分性の両方を与える。前者は単に非空な候補族から値を選び、後者は完全な最小性の仕様を満たす二つの候補が一致することを示す。その仕様を論理式で表した後、置換によって得られた入力と値の対を `L` の集合として集める。
<!--/-->

<!--en-->
Propositional truncation deliberately hides which initial candidate exists. The proof may eliminate that truncation only after changing the target to the total type of least elements and proving that this target is itself a proposition. Equality of constructible sets likewise ignores their proof components, so equality of the underlying sets is enough throughout the argument.
<!--zh-->
命题截断有意隐藏初始候选究竟是哪一个。只有先把目标改为「最小元的总类型」并证明该目标本身是命题，证明才能消去这层截断。可构造集合的相等同样不依赖其证明分量，因此整个论证中底层集合相等便已足够。
<!--ja-->
命題的切り詰めは、どの初期候補が存在するかを意図的に隠する。この切り詰めを除去できるのは、目標を最小要素の全体型へ変え、その目標自体が命題であると示した後だけである。構成可能集合の等しさも証明成分には依存しないので、議論全体で底の集合の等しさがあれば十分である。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
```

<!--en-->
The carrier `S` packages an ambient set together with a proof that it is constructible. Inputs and candidates can therefore occupy entries of a satisfaction environment, while the packaged stage `Lγ` and order relation `Rγ` can occur as constants in formulas. First projection returns the underlying sets needed for membership and ordered-pair coding.
<!--zh-->
载体 `S` 把外围集合与其可构造性证明打包在一起。因此，输入与候选可以占据满足环境中的各项，而打包后的层 `Lγ` 与序关系 `Rγ` 可以作为公式常元出现。第一投影则取回隶属关系与有序对编码所需的底层集合。
<!--ja-->
台 `S` は、周囲の集合と、それが構成可能であるという証明を組にする。したがって入力と候補は充足環境の項目となり、包まれた段階 `Lγ` と順序関係 `Rγ` は論理式の定数として現れる。第一射影によって、所属と順序対の符号化に必要な底の集合を取り出せる。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Satisfaction is read in the constructible structure `𝒮ʟ`. In particular, `P` is already an object-language formula; the chapter selects witnesses for this definable relation and does not claim to turn an arbitrary host-level predicate into a definable one.
<!--zh-->
满足关系在可构造结构 `𝒮ʟ` 中读取。特别地，`P` 已经是一条对象语言公式；本章为这条可定义关系选取见证，并不声称能把任意宿主层谓词变成可定义谓词。
<!--ja-->
充足関係は構成可能な構造 `𝒮ʟ` で読む。とくに `P` はすでに対象言語の論理式である。この章はその定義可能な関係の証人を選ぶのであり、任意のホスト側述語を定義可能にするとは主張しない。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
The original formula is evaluated in the two-entry environment `(w,x)`. When leastness introduces a bounded competitor, the environment becomes `(w',w,x)`, so the occurrence of the input must move while the new candidate `w'` occupies the first slot. Compatibility of satisfaction with renaming will justify that shift.
<!--zh-->
原公式在二项环境 `(w,x)` 中求值。最小性引入有界竞争者后，环境变成 `(w',w,x)`，所以输入所在的变元必须移动，而新候选 `w'` 占据第一槽位。满足关系与改名的相容性将证明这次移位正确。
<!--ja-->
もとの論理式は二項環境 `(w,x)` で評価される。最小性のために有界な比較候補を導入すると環境は `(w',w,x)` となるので、入力を指す変数を移し、新しい候補 `w'` を第一スロットに置く必要がある。充足と名前替えの両立性が、この移動を正当化する。
<!--/-->

```agda
module Ren = Sat 𝒮ʟ id using ( Agrees; ⊨-rename )
```

<!--en-->
The indices `i0` and `i1` name the first two available de Bruijn slots. Their mathematical roles depend on the environment: in `(w,x)` they refer to the proposed value and the input, while inside the bounded environment `(w',w,x)` they refer to the competitor and the proposed value.
<!--zh-->
指标 `i0` 与 `i1` 分别指向最前面的两个 De Bruijn 槽位；它们的数学角色随环境而定。在 `(w,x)` 中，二者指向提议的取值与输入；在有界环境 `(w',w,x)` 中，二者则指向竞争者与提议的取值。
<!--ja-->
添字 `i0` と `i1` は、先頭の二つの de Bruijn スロットを指す。その数学的な役割は環境によって変わる。`(w,x)` では値の候補と入力を指し、有界な環境 `(w',w,x)` では比較候補と値の候補を指す。
<!--/-->

```agda
private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
```

<!--en-->
Two constructible sets with equal underlying sets are equal, by the propositionhood of constructibility; every later identification of constructible sets goes through this lift.
<!--zh-->
底层集合相等的两个可构造集合相等，依据是可构造性的命题性；后文对可构造集合的每个同一视都经此提升。
<!--ja-->
底の集合が等しい二つの構成可能な集合は等しくなる。構成可能性が命題だからである。後の構成可能な集合の同一視は、すべてこの持ち上げを通る。
<!--/-->

```agda
  S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
  S≡ = Σ≡Prop (λ v → snd (isL v))
```

<!--en-->
## Selecting the least satisfying member
<!--zh-->
## 选取最小的满足成员
<!--ja-->
## 条件を満たす最小の要素を選ぶ
<!--/-->

<!--en-->
The least-witness module receives four pieces of data. The ordinal index `γ` with its ordinalness determines the stage; the set `X` constrains the inputs; the binary formula `P` is the predicate; and for every input in `X` the hypothesis asserts, merely, that some candidate from the stage satisfies the predicate there. The candidates are drawn from the whole stage `Lset γ`, while the inputs are constrained to `X`.
<!--zh-->
最小见证模块收取四份数据。带序数性的序数指数 `γ` 确定层；集合 `X` 约束输入；二元公式 `P` 是谓词；假设则仅仅地断言：对 `X` 中每个输入，都存在来自该层的候选满足谓词。候选取自整个层 `Lset γ`，而输入被约束在 `X` 之中。
<!--ja-->
最小の証人のモジュールは、四つのデータを受け取る。順序数性をもつ順序数の指数 `γ` が段階を決め、集合 `X` が入力を制約し、二項の論理式 `P` が述語であり、`X` の各入力に対して、段階から来るある候補がそこで述語を充足すると、単に、仮定される。候補は段階 `Lset γ` の全体から取られ、入力は `X` に制約される。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Least (γ : V ℓ) (oγ : IsOrd γ) (X : S) (P : Formula S 2)
  (have : (x : S) → ⟨ fst x ∈ fst X ⟩
        → ∥ Σ[ w ∈ S ] (⟨ fst w ∈ Lset γ ⟩ × ⟨ (w ∷ x ∷ []) ⊨ P ⟩) ∥₁) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The ambient stage `Lset γ` is packaged as an element `Lγ` of the constructible carrier. This package can occur as a constant in the graph formula, so the formula can bound its search to exactly the fixed candidate stage.
<!--zh-->
外围的层 `Lset γ` 被打包为可构造载体中的元素 `Lγ`。这一包可作为图公式中的常元，使公式能把搜索范围精确限制在固定的候选层内。
<!--ja-->
周囲の段階 `Lset γ` を、構成可能な台の要素 `Lγ` としてまとめる。この包みはグラフ論理式の定数として現れ、探索範囲を固定された候補の段階に正確に制限できる。
<!--/-->

```agda
  opaque
    Lγ : S
    Lγ = LsetS γ oγ
```

<!--en-->
The equation `Lγ-fst` exposes the underlying set of this opaque package as `Lset γ`. Later membership proofs cross this equation when moving between the host-level stage and the constant used by the formula.
<!--zh-->
等式 `Lγ-fst` 把这个不透明包的底层集合显式认同为 `Lset γ`。后文在宿主层的层与公式所用常元之间转换时，隶属证明都沿这条等式搬运。
<!--ja-->
等式 `Lγ-fst` は、この不透明な包みの底の集合を `Lset γ` と同一視する。後でホスト側の段階と論理式が使う定数との間を移るとき、所属の証明はこの等式に沿って輸送される。
<!--/-->

```agda
    Lγ-fst : fst Lγ ≡ Lset γ
    Lγ-fst = refl
```

<!--en-->
The internal relation encoder also needs the ordinal index itself as an element of the constructible universe. Every ordinal is constructible, and `oγ` supplies the ordinalness needed to obtain that fact for `γ`.
<!--zh-->
内部关系的编码还需要序数指数本身属于可构造宇宙。每个序数都是可构造的，而 `oγ` 提供了为 `γ` 得到这一事实所需的序数性。
<!--ja-->
内部関係を符号化するには、順序数の添字自体も構成可能宇宙の要素でなければならない。すべての順序数は構成可能であり、`oγ` は `γ` についてその事実を得るために必要な順序数性を与える。
<!--/-->

```agda
    hγ : ⟨ isL γ ⟩
    hγ = isL-ord γ oγ
```

<!--en-->
The internal implementation of the stage order is a constructible set of coded pairs, the relation in which leastness will be expressed.
<!--zh-->
层序的内部实现是由编码对构成的可构造集合；最小性将在这个关系中表达。
<!--ja-->
段階の順序の内部実装は、符号化された対からなる構成可能な集合であり、最小性はこの関係の中で表現される。
<!--/-->

```agda
  Rγ : S
  Rγ = relL γ hγ oγ
```

<!--en-->
The predicate `Mem x` records the restriction on inputs: it is evidence that `x ∈ X`. It imposes no condition on witness candidates, whose separate carrier is the set of members of `Lset γ` introduced next.
<!--zh-->
谓词 `Mem x` 记录对输入的约束，即 `x ∈ X` 的证据。它不对见证候选施加条件；候选的另一载体将在下一步定义为 `Lset γ` 的成员类型。
<!--ja-->
述語 `Mem x` は入力への制約、すなわち `x ∈ X` の証拠を記録する。証人候補には条件を課さない。候補の別の台は、次に `Lset γ` の要素の型として定める。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst X ⟩
```

<!--en-->
The order `orderAt γ oγ` acts on stage members rather than on arbitrary elements of `S`. The subtype `Mγ` builds the bound `c ∈ Lset γ` into every object being compared, so least-element search cannot range outside the fixed candidate stage.
<!--zh-->
序 `orderAt γ oγ` 作用于层成员，而非 `S` 的任意元素。子类型 `Mγ` 把界 `c ∈ Lset γ` 内置于每个被比较的对象中，因此最小元搜索不可能越出固定的候选层。
<!--ja-->
順序 `orderAt γ oγ` が作用するのは段階の要素であり、`S` の任意の要素ではない。部分型 `Mγ` は、比較される各対象に境界 `c ∈ Lset γ` を組み込むので、最小要素の探索が固定された候補の段階の外へ出ることはない。
<!--/-->

```agda
  private
    Mγ : Type (ℓ-suc ℓ)
    Mγ = MemOf (Lset γ)
```

<!--en-->
An element of `Mγ` contains an underlying set together with its membership in `Lset γ`. Every member of a constructible stage is constructible, so `memS` can promote that underlying set to the carrier `S`; the original membership proof remains available as the stage bound on the candidate.
<!--zh-->
`Mγ` 的元素包含一个底层集合及其属于 `Lset γ` 的证明。可构造层的每个成员都是可构造的，因此 `memS` 能把该底层集合提升到载体 `S`；原有的隶属证明仍保留为候选的层界。
<!--ja-->
`Mγ` の要素は、底の集合と、その集合が `Lset γ` に属するという証明を含む。構成可能な段階の各要素は構成可能なので、`memS` はその底の集合を台 `S` へ移せる。もとの所属の証明は、候補に対する段階の境界としてそのまま残る。
<!--/-->

```agda
    memS : Mγ → S
    memS c = fst c , Lset→isL γ oγ (fst c) (snd c)
```

<!--en-->
The predicate at a candidate and an input is the object-language satisfaction of `P` in the environment placing the candidate first and the input second.
<!--zh-->
候选与输入处的谓词，即 `P` 在「候选居前、输入居后」的环境中的对象语言满足。
<!--ja-->
候補と入力のもとでの述語とは、`P` が、候補を先に、入力を後に置いた環境の中で充足されることである。
<!--/-->

```agda
    At : S → S → hProp (ℓ-suc ℓ)
    At w x = (w ∷ x ∷ []) ⊨ P
```

<!--en-->
The predicate `Good x` transfers the original relation to the carrier ordered by `orderAt γ oγ`: a stage member is good exactly when its associated element of `S` satisfies `P` with input `x`. Consequently the forthcoming search orders candidates from `Lset γ`; it does not order the inputs in `X` or restrict candidates to `X`.
<!--zh-->
谓词 `Good x` 把原关系转到 `orderAt γ oγ` 所排序的载体上：一个层成员是合格候选，恰当其对应的 `S` 元素与输入 `x` 一同满足 `P`。因此，接下来的搜索排序的是 `Lset γ` 中的候选；它既不排序 `X` 中的输入，也不把候选限制到 `X` 中。
<!--ja-->
述語 `Good x` は、もとの関係を `orderAt γ oγ` が整列する台へ移す。段階の要素が良い候補であるのは、それに対応する `S` の要素が入力 `x` とともに `P` を満たすとき、ちょうどそのときである。したがって後の探索が並べるのは `Lset γ` の候補であり、`X` の入力を並べたり、候補を `X` に制限したりはしない。
<!--/-->

```agda
    Good : S → Mγ → hProp (ℓ-suc ℓ)
    Good x c = At (memS c) x
```

<!--en-->
For each fixed input, the formula-facing form of this predicate uses the original binary formula `P`. A stage member supplies the first environment entry through `memS`, while the fixed input supplies the second. The checked reading is reflexive, so the package adds no new mathematical assumption; it exposes the syntax already present in `Good`.
<!--zh-->
对每个固定输入，这个谓词面向公式的形式使用原有二元公式 `P`。层成员经 `memS` 供给环境的第一项，固定输入供给第二项。经过检查的读取是自反的，所以这个包不增加任何数学假设，只把 `Good` 中已有的句法显露出来。
<!--ja-->
固定した各入力について、この述語の論理式に面する形は、もとの二項論理式 `P` を使う。段階の要素が `memS` を通して環境の第一成分を、固定入力が第二成分を与える。検査済みの読みは反射的なので、このパッケージは新しい数学的仮定を加えず、`Good` にすでにある構文を露出させるだけである。
<!--/-->

```agda
    definedGood : (x : S) → FOL.Semantics.FormulaPredicate 𝒮ʟ Mγ S id (Good x)
    definedGood x = FOL.Semantics.presented 2 P (λ c → memS c ∷ x ∷ []) (λ c → refl)
```

<!--en-->
The same underlying set may arrive with two proofs that it is constructible. Since constructibility is a proposition, `S≡` identifies the two packaged elements of `S`; transporting satisfaction along that path shows that the repackaged stage member satisfies the same instance of `P` as the original witness.
<!--zh-->
同一个底层集合可能连同两份不同的可构造性证明出现。由于可构造性是命题，`S≡` 认同这两个打包后的 `S` 元素；沿所得路径搬运满足证明，便知重打包的层成员与原见证满足同一个 `P` 实例。
<!--ja-->
同じ底の集合が、構成可能性の二つの証明を伴って現れることがある。構成可能性は命題なので、`S≡` は二つの包まれた `S` の要素を同一視する。得られたパスに沿って充足の証明を輸送すれば、組み直した段階の要素が、もとの証人と同じ `P` の実例を満たすと分かる。
<!--/-->

```agda
    toMem : (x w : S) (hw : ⟨ fst w ∈ Lset γ ⟩) → ⟨ At w x ⟩ → ⟨ Good x (fst w , hw) ⟩
    toMem x w hw = subst (λ v → ⟨ At v x ⟩) (S≡ refl)
```

<!--en-->
Selection is performed after fixing an input `x` and evidence `m : x ∈ X`. The evidence authorizes the use of the pointwise existence hypothesis `have`; it neither puts the candidate in `X` nor equips `X` with an order.
<!--zh-->
选取在固定输入 `x` 及证据 `m : x ∈ X` 后逐点进行。该证据允许使用逐点存在假设 `have`；它既不说明候选属于 `X`，也不给 `X` 配备任何序。
<!--ja-->
選択は、入力 `x` と証拠 `m : x ∈ X` を固定してから各点で行う。この証拠によって各点の存在仮定 `have` を使えるが、候補が `X` に属することも、`X` に順序が入ることも意味しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Sel (x : S) (m : Mem x) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
For the fixed input, the hypothesis is mapped into the type of good stage members. This changes only the representation of each possible witness: the resulting nonemptiness remains propositionally truncated, so no particular starting member has yet been chosen.
<!--zh-->
对固定输入，假设被映到「满足条件的层成员」这一类型中。这一步只改变每个可能见证的表示；所得非空性仍带有命题截断，因此尚未选定任何特定起始成员。
<!--ja-->
固定した入力について、仮定を条件を満たす段階の要素の型へ写す。ここで変わるのは各候補の表現だけである。得られる非空性は命題的切り詰めの中にとどまり、特定の出発要素はまだ選ばれていない。
<!--/-->

```agda
    private
      nonempty : ∥ Σ[ c ∈ Mγ ] ⟨ Good x c ⟩ ∥₁
      nonempty = map₁ (λ { (w , hw , hp) → (fst w , hw) , toMem x w hw hp }) (have x m)
```

<!--en-->
Now `leastOfFormula` descends through `orderAt γ oγ` and returns an actual least good member. Its input `definedGood x` carries the object formula, environment, and reading theorem for the predicate being searched. This is the exceptional elimination step: excluded middle decides whether descent can continue, and propositional truncation may be eliminated because the total type of a least element together with its leastness proof has already been shown to be a proposition. Neither fact alone would justify extracting an arbitrary witness from `nonempty`.
<!--zh-->
此时 `leastOfFormula` 沿 `orderAt γ oγ` 下降，并返回一个实际的最小合格成员。它的输入 `definedGood x` 携带被搜索谓词的对象语言公式、环境与读取定理。这是特殊的消去步骤：排中律判定下降能否继续；而命题截断之所以可被消去，是因为「最小元连同其最小性证明的总类型」已经证明为命题。仅凭其中任一事实，都不足以从 `nonempty` 中抽取任意见证。
<!--ja-->
ここで `leastOfFormula` は `orderAt γ oγ` に沿って降下し、条件を満たす実際の最小要素を返す。その入力 `definedGood x` は、探索される述語の対象言語の論理式、環境、読み取り定理を運ぶ。これは特別な除去の段階である。排中律が降下を続けられるかを判定し、最小要素とその最小性の証明からなる全体型がすでに命題だと示されているため、命題的切り詰めを除去できる。どちらか一方だけでは、`nonempty` から任意の証人を取り出すことは正当化されない。
<!--/-->

```agda
    opaque
      c : Mγ
      c = fst (leastOfFormula (orderAt γ oγ) (definedGood x) lem nonempty)
```

<!--en-->
The result of the search retains the proof that the selected member is good. Thus the passage from mere existence to an actual least element does not lose the original predicate.
<!--zh-->
搜索结果保留被选成员是合格候选的证明。因此，从仅仅存在走到实际最小元的过程中，原谓词并未丢失。
<!--ja-->
探索の結果には、選ばれた要素が良い候補であるという証明も残る。したがって、単なる存在から実際の最小要素へ進んでも、もとの述語は失われない。
<!--/-->

```agda
      c-good : ⟨ Good x c ⟩
      c-good = fst (snd (leastOfFormula (orderAt γ oγ) (definedGood x) lem nonempty))
```

<!--en-->
Its companion clause gives the exact relative leastness needed later: any other good member of this same stage is forbidden from lying strictly below the selected one in `orderAt γ oγ`.
<!--zh-->
与之配套的子句给出后文所需的精确相对最小性：同一层中的任何其他合格成员，都不可能在 `orderAt γ oγ` 中严格低于被选者。
<!--ja-->
対になる条項は、後で必要となる正確な相対的最小性を与える。同じ段階の他の良い要素が、`orderAt γ oγ` において選ばれた要素より真に小さくなることはない。
<!--/-->

```agda
      minimal : (c' : Mγ) → ⟨ Good x c' ⟩ → relOf (orderAt γ oγ) c' c → ⊥₀
      minimal = snd (snd (leastOfFormula (orderAt γ oγ) (definedGood x) lem nonempty))
```

<!--en-->
The order compares objects in `Mγ`, whereas satisfaction environments contain objects of `S`. Repackaging the chosen member as `e` crosses this interface without changing its underlying set.
<!--zh-->
层序比较的是 `Mγ` 中的对象，而满足环境容纳的是 `S` 中的对象。把被选成员重打包为 `e`，便在不改变底层集合的前提下跨过这道接口。
<!--ja-->
段階の順序が比較するのは `Mγ` の対象であるが、充足環境に入るのは `S` の対象である。選ばれた要素を `e` として包み直すことで、底の集合を変えずにこの境界を越える。
<!--/-->

```agda
    e : S
    e = memS c
```

<!--en-->
Because goodness was defined through this same repackaging, the selected element of `S` immediately satisfies `P(e,x)`; no second choice or new search is involved.
<!--zh-->
由于合格性正是经同一重打包定义的，所得 `S` 元素立即满足 `P(e,x)`；这里不涉及第二次选取或新的搜索。
<!--ja-->
良い候補であることは、まさにこの同じ包み直しを通して定義されているので、得られた `S` の要素は直ちに `P(e,x)` を満たす。二度目の選択や新たな探索は必要ない。
<!--/-->

```agda
    e-holds : ⟨ (e ∷ x ∷ []) ⊨ P ⟩
    e-holds = c-good
```

<!--en-->
The membership component carried by the selected stage member also proves `e ∈ Lset γ`. Predicate satisfaction and the stage bound are therefore obtained from the same least candidate.
<!--zh-->
被选层成员携带的隶属分量同时证明 `e ∈ Lset γ`。因此，谓词满足与层界来自同一个最小候选。
<!--ja-->
選ばれた段階の要素がもつ所属の成分は、同時に `e ∈ Lset γ` を証明する。したがって、述語の充足と段階の境界は同じ最小候補から得られる。
<!--/-->

```agda
    e∈Lγ : ⟨ fst e ∈ Lset γ ⟩
    e∈Lγ = snd c
```
</div>
</details>

<!--en-->
For an input `x` equipped with `m : x ∈ X`, the function `fn` returns this selected candidate. Its domain evidence is explicit because the existence hypothesis is available only on `X`.
<!--zh-->
对带有证据 `m : x ∈ X` 的输入 `x`，函数 `fn` 返回这个被选候选。定义域证据显式出现，是因为存在假设只对 `X` 中的输入成立。
<!--ja-->
証拠 `m : x ∈ X` を伴う入力 `x` に対して、関数 `fn` はこの選ばれた候補を返す。存在仮定を使えるのは `X` 上だけなので、定義域の証拠が明示されている。
<!--/-->

```agda
  fn : (x : S) → Mem x → S
  fn x m = Sel.e x m
```

<!--en-->
At every such domain input, the chosen value satisfies the original formula in the environment `(fn(x),x)`.
<!--zh-->
在每个这样的定义域输入处，被选取值都在环境 `(fn(x),x)` 中满足原公式。
<!--ja-->
そのような定義域の各入力について、選ばれた値は環境 `(fn(x),x)` でもとの論理式を満たす。
<!--/-->

```agda
  fn-holds : (x : S) (m : Mem x) → ⟨ (fn x m ∷ x ∷ []) ⊨ P ⟩
  fn-holds x m = Sel.e-holds x m
```

<!--en-->
The same value lies in `Lset γ`. This separate range statement will later place the definable map in codomain `Lγ`; it does not say that the value lies in the input set `X`.
<!--zh-->
同一取值属于 `Lset γ`。这一单独的值域陈述将在后文把可定义映射的陪域置为 `Lγ`；它并不表示取值属于输入集 `X`。
<!--ja-->
同じ値は `Lset γ` に属する。この独立した値域の主張によって、後で定義可能な写像の終域を `Lγ` にできるが、値が入力集合 `X` に属するという意味ではない。
<!--/-->

```agda
  fn-in : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ Lset γ ⟩
  fn-in x m = Sel.e∈Lγ x m
```

<!--en-->
To state leastness in terms that can also be expressed inside `L`, assume that a competitor `w'` is recorded below `fn(x)` by the internal relation `Rγ`. The reading lemma `relL-rep` converts this coded entry into the host-level comparison used by `orderAt γ oγ`, where the minimality of the selected member refutes it. The conclusion excludes only satisfying competitors in `Lset γ` and only with respect to this fixed order.
<!--zh-->
为了用也能在 `L` 内表达的方式陈述最小性，设内部关系 `Rγ` 记录了竞争者 `w'` 低于 `fn(x)`。读出引理 `relL-rep` 把这一编码条目转成 `orderAt γ oγ` 所用的宿主层比较，而被选成员的最小性将其反驳。结论只排除 `Lset γ` 中满足谓词的竞争者，且只相对于这条固定的序。
<!--ja-->
`L` の内部でも表せる形で最小性を述べるため、比較候補 `w'` が `fn(x)` より小さいことを内部関係 `Rγ` が記録していると仮定する。読み出し補題 `relL-rep` は、この符号化された項目を `orderAt γ oγ` が使うホスト側の比較へ移し、選ばれた要素の最小性がそれを反駁する。結論が排除するのは `Lset γ` にある充足候補だけであり、しかもこの固定された順序に関してだけである。
<!--/-->

```agda
  fn-least : (x : S) (m : Mem x) (w' : S) → ⟨ fst w' ∈ Lset γ ⟩ → ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
           → ⟨ pr (fst w') (fst (fn x m)) ∈ fst Rγ ⟩ → ⊥₀
  fn-least x m w' hw' hp hr = Sel.minimal x m (fst w' , hw') (toMem x w' hw' hp)
    (relL-rep γ hγ oγ (fst w' , hw') (Sel.c x m) hr)
```

<!--en-->
The host-level specification `TWit w x` combines the three facts that the graph formula must express: `P(w,x)`, membership of `w` in the fixed stage, and the absence of a stage member satisfying `P` strictly below `w` in `orderAt γ oγ`. This is a specification of a graph value, before the graph is collected as an internal table.
<!--zh-->
宿主层规格 `TWit w x` 合并图公式必须表达的三项事实：`P(w,x)`、`w` 属于固定层，以及在 `orderAt γ oγ` 中不存在严格低于 `w` 且满足 `P` 的层成员。这是图取值的规格，此时图尚未被收集为内部表。
<!--ja-->
ホスト側の仕様 `TWit w x` は、グラフ論理式が表すべき三つの事実をまとめる。すなわち `P(w,x)`、`w` が固定された段階に属すること、そして `orderAt γ oγ` において `w` より真に小さく `P` を満たす段階の要素がないことである。これはグラフの値の仕様であり、この時点ではグラフはまだ内部の表として集められていない。
<!--/-->

```agda
  TWit : (w x : S) → Type (ℓ-suc ℓ)
  TWit w x =
      ⟨ (w ∷ x ∷ []) ⊨ P ⟩
    × ⟨ fst w ∈ Lset γ ⟩
    × ((w' : S) → ⟨ fst w' ∈ Lset γ ⟩ → ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
```

<!--en-->
The last component tests any `w'` that lies in `Lset γ` and satisfies `P(w',x)`. If the coded pair `(w',w)` belonged to `Rγ`, it would say that `w'` is strictly smaller in the fixed stage order, and the specification refutes precisely that possibility.
<!--zh-->
最后一个分量检验任意满足 `w' ∈ Lset γ` 与 `P(w',x)` 的 `w'`。若编码对 `(w',w)` 属于 `Rγ`，它便表示 `w'` 在固定层序中严格更小；这一规格所反驳的正是这种可能。
<!--ja-->
最後の成分は、`w' ∈ Lset γ` と `P(w',x)` を満たす任意の `w'` を調べる。符号化対 `(w',w)` が `Rγ` に属するなら、`w'` が固定された段階順序で真に小さいことを意味し、仕様はまさにその可能性を退ける。
<!--/-->

```agda
        → ⟨ pr (fst w') (fst w) ∈ fst Rγ ⟩ → ⊥₀)
```

<!--en-->
Uniqueness is proved only among candidates satisfying the complete `TWit` specification. The original predicate `P` may have many witnesses in the stage; what cannot happen in a strict total order is that two distinct candidates both satisfy `P` and both have no smaller satisfying candidate. Trichotomy reduces the comparison with the selected value to the three cases handled next.
<!--zh-->
唯一性只在满足完整 `TWit` 规格的候选之间证明。原谓词 `P` 在该层中可以有许多见证；严格全序所排除的是两个不同候选既都满足 `P`，又都没有更小的满足者。三歧性把任意候选与被选值的比较化为下面三种情形。
<!--ja-->
一意性を示す範囲は、完全な `TWit` の仕様を満たす候補に限られる。もとの述語 `P` は段階の中に多数の証人をもってよいのである。狭義全順序が排除するのは、異なる二つの候補がともに `P` を満たし、しかも両方により小さい充足候補がないという状況である。三分性により、任意の候補と選ばれた値との比較は、次の三場合に分かれる。
<!--/-->

```agda
  fn-unique : (x : S) (m : Mem x) (w : S) → TWit w x → fst w ≡ fst (fn x m)
  fn-unique x m w (hp , hw , mn) = go (SWO.tri∙ (orderAt γ oγ) c' (Sel.c x m))
    where
    c' : Mγ
    c' = fst w , hw
```

<!--en-->
If the alternative candidate were strictly below the selected one, leastness would be contradicted; if the two stage members coincided, their underlying sets would be equal.
<!--zh-->
若替代候选严格低于被选者，则与最小性矛盾；若两个层成员重合，则其底层集相等。
<!--ja-->
代替の候補が選ばれたものより真に下なら、最小性と矛盾する。二つの段階の要素が一致すれば、底の集合が等しくなる。
<!--/-->

```agda
    go : Tri∙ (relOf (orderAt γ oγ) c' (Sel.c x m)) (c' ≡ Sel.c x m)
              (relOf (orderAt γ oγ) (Sel.c x m) c')
       → fst w ≡ fst (fn x m)
    go (lt k) = ⊥₀-rec (Sel.minimal x m c' (toMem x w hw hp) k)
    go (eq q) = cong fst q
```

<!--en-->
If the selected candidate were strictly below the alternative, the alternative's own leastness would be contradicted, with the missing comparison supplied by the filling direction of the internal relation.
<!--zh-->
若被选候选严格低于替代候选，便与替代候选自身的最小性矛盾；所需的比较由内部关系的填充方向供给。
<!--ja-->
選ばれた候補が代替の候補より真に下なら、代替の候補自身の最小性と矛盾する。欠けていた比較は、内部の関係の埋めの方向によって供給される。
<!--/-->

```agda
    go (gt k) = ⊥₀-rec (mn (fn x m) (fn-in x m) (fn-holds x m)
      (relL-fill γ hγ oγ (Sel.c x m) c' k))
```

<!--en-->
Under the bounded quantifier the environment is `(w',w,x)`, whereas `P` expects `(candidate,input)`. The renaming therefore sends its variable 0 to slot 0, still `w'`, and its variable 1 to slot 2, now `x`; slot 1 is reserved for the proposed value `w` against which `w'` is compared.
<!--zh-->
进入有界量词后，环境为 `(w',w,x)`，而 `P` 期待 `(候选,输入)`。因此改名把变元 0 送到仍为 `w'` 的槽位 0，把变元 1 送到现为 `x` 的槽位 2；槽位 1 留给提议的取值 `w`，供 `w'` 与之比较。
<!--ja-->
有界量化子の内側では環境が `(w',w,x)` となるが、`P` が期待するのは `(候補,入力)` である。そこで名前替えは変数 0 を、引き続き `w'` であるスロット 0 へ送り、変数 1 を、いま `x` であるスロット 2 へ送る。スロット 1 は、`w'` と比較される値の候補 `w` のために残す。
<!--/-->

```agda
  private
    ρ : Fin 2 → Fin 3
    ρ zero       = zero
    ρ (suc zero) = suc (suc zero)
```

<!--en-->
Agreement records exactly those two identifications: reading variable 0 from `(w',w,x)` gives the first entry of `(w',x)`, and reading variable 1 after renaming gives the second. This pointwise agreement is the premise needed to transport satisfaction of the whole formula `P`.
<!--zh-->
环境一致性精确记录这两项认同：从 `(w',w,x)` 读取变元 0，得到 `(w',x)` 的第一项；改名后读取变元 1，得到其第二项。这种逐变元的一致性正是搬运整条公式 `P` 的满足关系所需的前提。
<!--ja-->
環境の一致は、この二つの対応を正確に記録する。`(w',w,x)` から変数 0 を読むと `(w',x)` の第一項になり、名前替え後に変数 1 を読むとその第二項になる。この変数ごとの一致が、論理式 `P` 全体の充足を輸送するための前提である。
<!--/-->

```agda
    ag : (w' w x : S) → Ren.Agrees ρ (w' ∷ w ∷ x ∷ []) (w' ∷ x ∷ [])
    ag w' w x zero       = refl
    ag w' w x (suc zero) = refl
```

<!--en-->
The leastness formula ranges over `w' ∈ Lγ` and denies the conjunction of two claims: the coded pair `(w',w)` belongs to `Rγ`, and `P(w',x)` holds. Semantically it says that no candidate in the fixed stage lies below `w` in `orderAt γ oγ` while also witnessing the original predicate for the same input.
<!--zh-->
最小性公式遍历 `w' ∈ Lγ`，并否定两项陈述的合取：编码对 `(w',w)` 属于 `Rγ`，且 `P(w',x)` 成立。其语义是：固定层中没有候选既在 `orderAt γ oγ` 中低于 `w`，又对同一输入见证原谓词。
<!--ja-->
最小性の論理式は `w' ∈ Lγ` の上を動き、二つの主張の連言を否定する。すなわち、符号化対 `(w',w)` が `Rγ` に属することと、`P(w',x)` が成り立つことである。その意味は、固定された段階の候補で、`orderAt γ oγ` において `w` より小さく、同じ入力についてもとの述語を証言するものはない、ということである。
<!--/-->

```agda
  opaque
    private
      leastFo : Formula S 2
      leastFo = ∀̇∈ (con Lγ) (¬̇ (appC Rγ i0 i1 ∧̇ renameFo ρ P))
```

<!--en-->
Compatibility with renaming now identifies the two readings of `P`: evaluating `renameFo ρ P` in `(w',w,x)` is the same as evaluating `P` directly in `(w',x)`. The current proposed value `w` is deliberately absent from the predicate test on the competitor; it occurs only in the order comparison `(w',w)`.
<!--zh-->
改名相容性现在认同 `P` 的两种读法：在 `(w',w,x)` 中求值 `renameFo ρ P`，等同于在 `(w',x)` 中直接求值 `P`。当前提议的取值 `w` 有意不出现在对竞争者的谓词检验中；它只出现在序比较 `(w',w)` 中。
<!--ja-->
名前替えとの両立性により、`P` の二つの読みが一致する。`(w',w,x)` で `renameFo ρ P` を評価することは、`(w',x)` で `P` を直接評価することと同じである。現在の値の候補 `w` は、比較候補についての述語の検査には意図的に現れず、順序比較 `(w',w)` にだけ現れる。
<!--/-->

```agda
      ren : (w' w x : S)
          → ⟨ (w' ∷ w ∷ x ∷ []) ⊨ renameFo ρ P ⟩ ≡ ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
      ren w' w x = cong ⟨_⟩ (Ren.⊨-rename ρ P (w' ∷ w ∷ x ∷ []) (w' ∷ x ∷ []) (ag w' w x))
```

<!--en-->
The full graph formula conjoins the original predicate with stage membership and the leastness clause: a value is recorded exactly when it satisfies the predicate, lies in the fixed stage, and is least among stage members that do.
<!--zh-->
完整图公式把原谓词与层隶属、最小性子句合取：一个值被记录，恰当它满足谓词、位于固定层中、且在该层满足谓词的成员中最小。
<!--ja-->
完全なグラフの論理式は、もとの述語に、段階への所属と最小性の節を連言する。値が記録されるのは、述語を充足し、固定された段階に属し、そしてそうする段階の要素の中で最小のとき、ちょうどそのときである。
<!--/-->

```agda
    fo : Formula S 2
    fo = P ∧̇ ((var i0 ∈̇ con Lγ) ∧̇ leastFo)
```

<!--en-->
Reading `fo` outward recovers the three parts of the semantic specification: `P(w,x)`, membership `w ∈ Lset γ`, and the absence of a satisfying member of that stage recorded below `w` by the internal order. The formula `fo` itself does not contain the condition `x ∈ X`; that restriction is imposed when `fo` is used as the graph formula of `Dmap`. Thus `X` controls the inputs on which a value must be defined, while `Lset γ` controls the candidates compared for that input.
<!--zh-->
向外读取 `fo`，可恢复语义规格的三部分：`P(w,x)`、隶属 `w ∈ Lset γ`，以及该层中没有满足谓词且被内部序记录为低于 `w` 的成员。公式 `fo` 本身不含条件 `x ∈ X`；这一限制在 `fo` 被用作 `Dmap` 的图公式时施加。因此，`X` 控制哪些输入必须取得值，而 `Lset γ` 控制为该输入参与比较的候选。
<!--ja-->
`fo` を外向きに読むと、意味論的な仕様の三部分が得られる。すなわち `P(w,x)`、所属 `w ∈ Lset γ`、そして同じ段階に、条件を満たし、内部順序によって `w` より小さいと記録される要素がないことである。論理式 `fo` 自体は条件 `x ∈ X` を含まない。この制限は、`fo` を `Dmap` のグラフ論理式として使うときに課される。したがって `X` は値を定めるべき入力を制御し、`Lset γ` はその入力について比較される候補を制御する。
<!--/-->

```agda
    fo-out : (w x : S) → ⟨ (w ∷ x ∷ []) ⊨ fo ⟩ → TWit w x
    fo-out w x (hp , (hl , hm)) =
        hp
      , subst (λ v → ⟨ fst w ∈ v ⟩) Lγ-fst hl
      , λ w' hw' hp' hr → lower (hm w' (subst (λ v → ⟨ fst w' ∈ v ⟩) (sym Lγ-fst) hw')
```

<!--en-->
To obtain the minimality component of `TWit`, fix a competitor `w'` and assume the semantic facts that `pr(w',w) ∈ Rγ` and `P(w',x)`. The proof uses `appC-adequate` and renaming in the inward direction to turn these facts into satisfaction of the two conjuncts negated by `fo`; the bounded clause then yields the contradiction. The relation entry is an object-language encoding of the stage-order comparison, not a definitional equality with `relOf (orderAt γ oγ)`.
<!--zh-->
为得到 `TWit` 的最小性分量，固定竞争者 `w'`，并假设语义事实 `pr(w',w) ∈ Rγ` 与 `P(w',x)`。证明沿向内方向使用 `appC-adequate` 与改名，把这两项事实变成 `fo` 所否定的两个合取项的满足；有界子句随即导出矛盾。该关系条目是层序比较的对象语言编码，并不与 `relOf (orderAt γ oγ)` 定义相等。
<!--ja-->
`TWit` の最小性の成分を得るため、比較候補 `w'` を固定し、意味論的な事実 `pr(w',w) ∈ Rγ` と `P(w',x)` を仮定する。証明は `appC-adequate` と名前替えを内向きに用いて、この二つの事実を `fo` が否定する二つの連言の充足へ移す。すると有界な条項から矛盾が得られる。この関係の項目は段階順序による比較の対象言語での符号化であり、`relOf (orderAt γ oγ)` と定義的に等しいわけではない。
<!--/-->

```agda
          ( subst ⟨_⟩ (sym (appC-adequate Rγ i0 i1 (w' ∷ w ∷ x ∷ []))) hr
          , transport (sym (ren w' w x)) hp' ))
```

<!--en-->
Conversely, a witness satisfying `TWit` determines a proof of the graph formula. Its first two components establish `P(w,x)` and `w ∈ Lset γ`. For the bounded minimality clause, take any `w'` in that same level and suppose that the encoded order places `w'` before `w` and that `P(w',x)` holds; the last component of `TWit` rules out exactly this conjunction.
<!--zh-->
反过来，一个满足 `TWit` 的见证决定了图公式的证明。其前两个分量给出 `P(w,x)` 与 `w ∈ Lset γ`。对于有界的最小性子句，在同一层中任取 `w'`，并假设编码的序把 `w'` 排在 `w` 之前且 `P(w',x)` 成立；`TWit` 的最后一个分量恰好排除这一合取。
<!--ja-->
逆に、`TWit` を満たす証人からグラフ論理式の証明が定まる。最初の二つの成分は `P(w,x)` と `w ∈ Lset γ` を与える。有界な最小性の条項については、同じ段階の任意の `w'` を取り、符号化された順序で `w'` が `w` より前にあり、かつ `P(w',x)` が成り立つと仮定する。`TWit` の最後の成分が、まさにこの連言を排除する。
<!--/-->

```agda
    fo-in : (w x : S) → TWit w x → ⟨ (w ∷ x ∷ []) ⊨ fo ⟩
    fo-in w x (hp , hl , mn) =
        hp
      , subst (λ v → ⟨ fst w ∈ v ⟩) (sym Lγ-fst) hl
      , λ w' hw' hc → lift (mn w' (subst (λ v → ⟨ fst w' ∈ v ⟩) Lγ-fst hw')
```

<!--en-->
Renaming and application adequacy put those two assumptions into the forms expected by semantic minimality. Together, `fo-out` and `fo-in` show that `fo` expresses exactly the fixed-level least-witness specification. They add neither uniqueness of witnesses for the original predicate nor any comparison with candidates outside `Lset γ`.
<!--zh-->
改名与应用充分性把这两个假设转成语义最小性所需的形式。合起来，`fo-out` 与 `fo-in` 表明 `fo` 恰好表达固定层中的最小见证规格。它们既不要求原谓词的见证唯一，也不比较 `Lset γ` 之外的候选者。
<!--ja-->
改名と適用の妥当性によって、この二つの仮定は意味論的な最小性が受け取る形になる。`fo-out` と `fo-in` を合わせると、`fo` が固定された段階における最小証人の仕様を正確に表すことが分かる。もとの述語の証人が一意であることも、`Lset γ` の外にある候補との比較も、ここには加えられていない。
<!--/-->

```agda
          (transport (ren w' w x) (snd hc))
          (subst ⟨_⟩ (appC-adequate Rγ i0 i1 (w' ∷ w ∷ x ∷ [])) (fst hc)))
```

<!--en-->
This exact correspondence makes the selection definable. The map has input set `X` and codomain `Lγ`: for each proof that `x ∈ X`, its value is `fn x m`, and the earlier level-membership theorem places that value in `Lγ`. The graph formula is read in the environment `(value,input)`, so its first variable denotes the selected witness and its second variable denotes the input.
<!--zh-->
这一精确对应使该选取成为可定义映射。映射的输入集是 `X`，陪域是 `Lγ`：对每个 `x ∈ X` 的证明，其取值为 `fn x m`，而先前的层隶属定理把该值置于 `Lγ` 中。图公式在环境 `(取值,输入)` 中读取，因此第一个变量表示选出的见证，第二个变量表示输入。
<!--ja-->
この正確な対応により、選択は定義可能な写像になる。入力集合は `X`、終域は `Lγ` である。`x ∈ X` の各証明に対する値は `fn x m` であり、先に示した段階への所属によって、その値は `Lγ` に入る。グラフ論理式は環境 `(値,入力)` で読まれるので、第一変数が選ばれた証人を、第二変数が入力を表す。
<!--/-->

```agda
  Dmap : DefinableMap
  Dmap = record
    { dom = X ; cod = Lγ ; fn = fn
    ; into = λ x m → subst (λ v → ⟨ fst (fn x m) ∈ v ⟩) (sym Lγ-fst) (fn-in x m)
    ; graph = fo
```

<!--en-->
At the selected value, the three facts already proved supply a proof of `fo`: the value satisfies `P`, lies in the candidate level, and has no smaller satisfying competitor there. Conversely, any value satisfying `fo` carries this full least-witness specification and is therefore equal to the selected value. This uniqueness comes from the two candidates' leastness and trichotomy of `orderAt γ oγ`, not from uniqueness of `P`-witnesses; equality of their underlying sets lifts to equality in `S` because constructibility evidence is propositional.
<!--zh-->
在选出的取值处，已经证明的三项事实给出 `fo` 的证明：该值满足 `P`、属于候选层，并且其中没有更小的满足候选。反过来，任何满足 `fo` 的取值都携带这份完整的最小见证规格，因而等于选出的取值。这一唯一性来自两个候选各自的最小性及 `orderAt γ oγ` 的三歧性，而非 `P` 的见证唯一；由于可构造性证据是命题，底层集合的相等可提升为 `S` 中的相等。
<!--ja-->
選ばれた値については、すでに示した三つの事実から `fo` の証明が得られる。その値は `P` を満たし、候補の段階に属し、その段階にはそれより小さく `P` を満たす候補がない。逆に、`fo` を満たす値はこの最小証人の仕様をすべて備えるので、選ばれた値と等しくなる。この一意性は二つの候補がともに最小であることと `orderAt γ oγ` の三分律から従うのであり、`P` の証人の一意性から従うのではない。構成可能性の証拠は命題なので、基礎となる集合の等しさは `S` での等しさへ持ち上がる。
<!--/-->

```agda
    ; defines = λ x m → fo-in (fn x m) x (fn-holds x m , fn-in x m , fn-least x m)
    ; only = λ x m w h → S≡ (fn-unique x m w (fo-out w x h)) }
```

<!--en-->
Once a formula defines one value for every input in `X`, replacement can collect those values inside `L`. Applied to `Dmap`, the graph construction provides a constructible set of ordered pairs together with the two directions needed to use its membership relation.
<!--zh-->
一旦一条公式为 `X` 中每个输入定义唯一取值，替换便能在 `L` 内收集这些取值。把图构造用于 `Dmap`，可得到由有序对组成的可构造集，以及使用其隶属关系所需的两个方向。
<!--ja-->
一つの論理式が `X` の各入力にただ一つの値を定めれば、置換によってそれらの値を `L` の内部に集められる。グラフの構成を `Dmap` に適用すると、順序対からなる構成可能集合と、その所属関係を利用するための二方向の読みが得られる。
<!--/-->

```agda
  private module Gr = Graph Dmap using ( F; F-in; pair-out )
```

<!--en-->
Call this collected set `T`. Its entries are ordered pairs `(x,fn(x))`, with the input first and the selected value second. This reverses the order used by formula satisfaction, whose environment was `(value,input)`; keeping the two conventions distinct prevents the graph formula from being mistaken for the internal table itself.
<!--zh-->
把这个收集所得的集合记为 `T`。它的条目是有序对 `(x,fn(x))`，输入在前，选出的取值在后。这与公式满足所用的环境 `(取值,输入)` 次序相反；区分这两种约定，可避免把图公式误认成内部表本身。
<!--ja-->
こうして集めた集合を `T` と呼ぶ。その項目は順序対 `(x,fn(x))` であり、入力が先、選ばれた値が後である。これは論理式の充足に用いた環境 `(値,入力)` と逆の順序である。二つの規約を区別することで、グラフ論理式を内部の表そのものと取り違えずに済む。
<!--/-->

```agda
  T : S
  T = Gr.F
```

<!--en-->
For every `x ∈ X`, the table contains the pair `(x,fn(x))`. Hence later arguments may refer to the choices through membership in one constructible set, rather than making a separate choice from the merely inhabited family for each input.
<!--zh-->
对每个 `x ∈ X`，表都包含有序对 `(x,fn(x))`。因此，后续论证可以通过同一个可构造集的隶属关系引用这些选择，而无须对每个输入分别从仅仅非空的族中作选择。
<!--ja-->
各 `x ∈ X` について、表は順序対 `(x,fn(x))` を含む。したがって後の議論では、入力ごとに単に非空な族から別々に選ぶのではなく、一つの構成可能集合への所属を通して、これらの選択を参照できる。
<!--/-->

```agda
  T-in : (x : S) (m : Mem x) → ⟨ pr (fst x) (fst (fn x m)) ∈ fst T ⟩
  T-in = Gr.F-in
```

<!--en-->
Conversely, an entry `(x,w) ∈ T` yields evidence `x ∈ X` and equality of the underlying set of `w` with that of the selected value `fn(x)`. Table membership does not return the leastness proof itself. In `HullCounting`, this table is used to synchronize choices that were previously available only under propositional truncation. When an injection is needed, a separate reverse-functionality hypothesis for the underlying relation proves that a fixed related candidate cannot correspond to two different inputs; injectivity is not a consequence of least selection alone.
<!--zh-->
反过来，条目 `(x,w) ∈ T` 给出证据 `x ∈ X`，并给出 `w` 的底层集合与被选取值 `fn(x)` 的底层集合相等。表隶属本身不返回最小性证明。在 `HullCounting` 中，这张表用于同步此前只在命题截断下可得的诸选择。需要单射时，还须另有底层关系的反向函数性假设，证明一个固定的相关候选不能对应两个不同输入；单射性并不单由最小选取得出。
<!--ja-->
逆に、項目 `(x,w) ∈ T` からは、証拠 `x ∈ X` と、`w` の底の集合が選ばれた値 `fn(x)` の底の集合に等しいことが得られる。表への所属そのものは、最小性の証明を返さない。`HullCounting` では、この表を使って、それまでは命題的切り詰めのもとでしか得られなかった選択をそろえる。単射が必要な場合には、基礎となる関係について逆向きの関数性を別に仮定し、一つの関係する候補が異なる二つの入力に対応しないことを示す。単射性は最小選択だけから従うものではない。
<!--/-->

```agda
  T-out : (x w : S) → ⟨ pr (fst x) (fst w) ∈ fst T ⟩
        → Σ[ m ∈ Mem x ] (fst w ≡ fst (fn x m))
  T-out = Gr.pair-out
```
</div>
</details>
