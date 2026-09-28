```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Turning a definable injection into an internal code
<!--zh-->
# 把可定义单射化为内部编码
<!--ja-->
# 定義可能な単射を内部コードにする
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and this instance of excluded middle. The mathematical problem is to pass from a host-level rule to a set that `L` can quantify over. The rule itself is not inserted into `L`. Instead, a formula describes its values on a set of `L`, Replacement forms a constructible graph, and an injectivity proof equips that graph with the code used for internal cardinal comparisons.
<!--zh-->
固定宇宙层级 `ℓ` 与这一排中律实例。这里的数学问题，是怎样从宿主层的取值规则得到一个可由 `L` 量化的集合。取值规则本身不会被放入 `L`；一条公式在 `L` 的某个集合上描述它的值，替换据此形成可构造的函数图，再由单射性证明为该图配上内部基数比较所需的编码。
<!--ja-->
宇宙レベル `ℓ` と、この排中律のインスタンスを固定する。ここでの数学的な問題は、ホスト側の値を定める規則から、`L` が量化できる集合を得ることである。その規則自体が `L` に入るのではない。論理式が `L` のある集合上でその値を記述し、置換が構成可能な関数グラフを作り、単射性の証明がそのグラフに内部の基数比較で用いる符号を与える。
<!--/-->

```agda
module L.DefinableInjection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion )
open import L.Recursion.Graph {ℓ} lem
  using () renaming ( module Graph to RecursionGraph )
open import L.Coding.Model {ℓ}
  using ( svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro
        ; valuesInAt; valuesInAt-in; valuesInAt-out )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-in; injAt-out )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL; IsCardinalL )
```

<!--en-->
A rule described outside `L` is not yet an object over which `L` can quantify. To compare cardinalities internally, we need a constructible set of ordered pairs recording the rule's values. The central question is therefore how definability and pointwise uniqueness let Replacement collect that graph.
<!--zh-->
在 `L` 外部描述一条取值规则，并不等于已经有了一个可供 `L` 量化的对象。要在模型内部比较基数，需要一个由有序对组成的可构造集合来记录这些取值。因此，本章的中心问题是：可定义性与逐点唯一性怎样使替换定理能够收集这张函数图。
<!--ja-->
`L` の外側で値を定める規則を記述しても、それだけでは `L` が量化できる対象にはならない。モデルの内部で基数を比較するには、その値を順序対として記録する構成可能集合が必要である。そこで本章では、定義可能性と各点での一意性から、置換によってそのグラフを集める方法を考える。
<!--/-->

<!--en-->
The sole classical parameter is excluded middle at level `ℓ-suc ℓ`. The elementary steps in this chapter, such as proving uniqueness, transporting membership, and eliminating a propositional truncation into a proposition, are constructive. The parameter matters when the general Replacement theorem collects the graph as an element of `L`; no form of choice is used.
<!--zh-->
唯一的经典参数是层级 `ℓ-suc ℓ` 上的排中律。本章中的初等步骤，例如证明唯一性、运输成员关系，以及把命题截断消去到命题中，都是构造性的。这个参数在一般替换定理把函数图收集成 `L` 的元素时起作用；全程不使用任何形式的选择公理。
<!--ja-->
唯一の古典的パラメータは、水準 `ℓ-suc ℓ` における排中律である。本章の初等的な段階、たとえば一意性の証明、所属の輸送、命題的切り詰めを命題へ消去する操作は構成的である。このパラメータが必要になるのは、一般の置換定理によって関数グラフを `L` の要素として集めるときである。選択公理はどの形でも用いない。
<!--/-->



<!--en-->
Three kinds of object must be kept distinct. A formula belongs to the first-order language whose constants are elements of the constructible carrier; satisfaction interprets it in the structure on `L`; and `pr` is the ambient Kuratowski code for an ordered pair of underlying sets. Later the defining formula will be read with the value first and the input second, while an entry of the collected graph is `pr(input,value)`.
<!--zh-->
这里须区分三类对象。公式属于一阶语言，其常元是可构造论域的元素；满足关系在 `L` 上的结构中解释该公式；`pr` 则是在外围层级中编码底层集合有序对的柯拉托夫斯基对。稍后读取定义公式时，值在前、输入在后；收集所得函数图的条目则是 `pr(输入,值)`。
<!--ja-->
ここでは三種類の対象を区別する必要がある。論理式は、構成可能な台の要素を定数とする一階言語に属する。充足関係は、その論理式を `L` 上の構造で解釈する。そして `pr` は、基礎集合の順序対を周囲の階層で表すクラトフスキー符号である。後で定義の論理式を読むときは値が先、入力が後であるが、集められた関数グラフの項目は `pr(入力,値)` となる。
<!--/-->

<!--en-->
The proof passes through three mathematical forms. A recursion consists of a domain, a value formula, and a proof that the satisfying-value fiber at each domain point is contractible. Its graph construction uses Replacement to collect ordered pairs and proves single-valuedness and the exact domain. Finally, `injAt` expresses the remaining injectivity condition: two entries with the same output have equal inputs.
<!--zh-->
证明依次经过三种数学形式。递归由定义域、取值公式，以及定义域每一点的满足值纤维可缩这一证明组成。函数图构造用替换收集有序对，并证明单值性与恰当定义域。最后，`injAt` 表达尚缺的单射条件：两个条目若有相同输出，其输入便相等。
<!--ja-->
証明は三つの数学的な形を順に通る。再帰は、定義域、値を定める論理式、そして定義域の各点で充足する値のファイバーが可縮であることの証明からなる。そのグラフ構成は置換によって順序対を集め、一価性と正確な定義域を証明する。最後に `injAt` が、残る単射性の条件、すなわち同じ出力をもつ二つの項目の入力が等しいことを表す。
<!--/-->

<!--en-->
For sets `a` and `b`, `InjCode F a b` has exactly four components. The graph `F` is single-valued, has domain exactly `a`, is injective, and every value appearing in it belongs to `b`. The four conditions have matching object-language formulas, including the previously developed `valuesInAt` formula for the range condition. `InjL a b` propositionally truncates the existence of such an `F` and its code.
<!--zh-->
对集合 `a` 与 `b`，`InjCode F a b` 恰有四个分量：函数图 `F` 是单值的，其定义域恰为 `a`，它满足单射性，并且其中出现的每个值都属于 `b`。四个条件都有对应的对象语言公式，其中取值范围条件使用此前构造的 `valuesInAt` 公式。`InjL a b` 则把这样的 `F` 及其编码之存在作命题截断。
<!--ja-->
集合 `a` と `b` に対して、`InjCode F a b` はちょうど四つの成分をもつ。グラフ `F` が一価であること、その定義域が正確に `a` であること、単射的であること、そしてそこに現れるすべての値が `b` に属することである。四条件にはいずれも対応する対象言語の論理式があり、値域条件には先に構成した `valuesInAt` を用いる。`InjL a b` は、そのような `F` と符号の存在を命題的切り詰めに入れる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Reading injection codes as one formula

The four clauses of `InjCode` can be presented by one object-language formula with three designated slots: the graph, its domain, and its codomain. The first three conjuncts reuse the formulas for single-valuedness, exact domain, and injectivity. The last conjunct quantifies over an input and output and says that whenever the graph relates them, the output belongs to the codomain slot. Thus the host-level range field is not assumed invisible; it is tied to a checked formula at this interface.
<!--zh-->
## 把单射码读作一条公式

`InjCode` 的四个条款可以由一条带三个指定槽位的对象语言公式呈现：函数图、定义域和陪域。前三个合取支复用单值性、精确定义域与单射性的公式；最后一支量化实参和取值，并断言函数图一旦联系二者，取值就属于陪域槽。因此，宿主层的值域字段并未被假定为不可见，而是在此接口处与一条经过检查的公式绑定。
<!--ja-->
## 単射符号を一つの論理式として読む

`InjCode` の四条件は、グラフ、定義域、終域という三つの指定位置をもつ一つの対象論理式で表せる。最初の三つの連言は、一価性、正確な定義域、単射性の論理式を再利用する。最後の連言は入力と出力を量化し、グラフが両者を関係づけるなら出力が終域の位置に属すと述べる。したがってホスト層の値域フィールドを不可視と仮定するのではなく、このインターフェースで検査済みの論理式に結び付ける。
<!--/-->

```agda
injCodeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
injCodeAt f A B = svAt f ∧̇ domAt f A ∧̇ injAt f
                  ∧̇ valuesInAt f B
```

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module InjCodeAt {n : ℕ} (f A B : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    F D C : S
    F = lookup f γ
    D = lookup A γ
    C = lookup B γ

  read : ⟨ γ ⊨ injCodeAt f A B ⟩ → InjCode F D C
  read (sv , dm , ij , ran) =
      svAt-in zero (F ∷ D ∷ []) (λ x y y' p q → svAt-out f γ sv x y y' p q)
    , domAt-intro zero (suc zero) (F ∷ D ∷ []) (λ x →
          (λ h → rec₁ (snd (fst x ∈ fst D))
                   (λ { (y , p) → domAt-out f A γ dm x y p }) h)
        , (λ hx → domAt-in f A γ dm x hx))
    , injAt-in zero (F ∷ D ∷ []) (λ y x x' p q → injAt-out f γ ij y x x' p q)
    , valuesInAt-out f B γ ran

  fill : InjCode F D C → ⟨ γ ⊨ injCodeAt f A B ⟩
  fill (sv , dm , ij , ran) =
      svAt-in f γ (λ x y y' p q → svAt-out zero (F ∷ D ∷ []) sv x y y' p q)
    , domAt-intro f A γ (λ x →
          (λ h → rec₁ (snd (fst x ∈ fst D))
                   (λ { (y , p) → domAt-out zero (suc zero) (F ∷ D ∷ []) dm x y p }) h)
        , (λ hx → domAt-in zero (suc zero) (F ∷ D ∷ []) dm x hx))
    , injAt-in f γ (λ y x x' p q → injAt-out zero (F ∷ D ∷ []) ij y x x' p q)
    , valuesInAt-in f B γ ran
```
</div>
</details>

<!--en-->
Existentially binding the graph slot yields the formula for `InjL`: the remaining two slots name the domain and codomain. Its semantic existential is already propositionally truncated, exactly as `InjL` is. Mapping the preceding `read` and `fill` functions under that truncation gives both directions without choosing a graph.
<!--zh-->
对函数图槽作存在量化便得到 `InjL` 的公式，余下两个槽分别指名定义域与陪域。其语义存在量词本来就带命题截断，恰与 `InjL` 相同。把上面的 `read` 与 `fill` 函数映入该截断，就得到两个方向而无需选出函数图。
<!--ja-->
グラフの位置を存在量化すると `InjL` の論理式が得られ、残る二つの位置が定義域と終域を名指す。その意味論的な存在は初めから命題的に切り詰められており、`InjL` とちょうど一致する。先の `read` と `fill` をその切り詰めの内側で写せば、グラフを選ばずに両方向が得られる。
<!--/-->

```agda
injLAt : ∀ {n} → Fin n → Fin n → Formula S n
injLAt A B = ∃̇ (injCodeAt zero (suc A) (suc B))
```

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module InjLAt {n : ℕ} (A B : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    D C : S
    D = lookup A γ
    C = lookup B γ

  read : ⟨ γ ⊨ injLAt A B ⟩ → InjL D C
  read = map₁ (λ { (F , code) → F , InjCodeAt.read zero (suc A) (suc B) (F ∷ γ) code })

  fill : InjL D C → ⟨ γ ⊨ injLAt A B ⟩
  fill = map₁ (λ { (F , code) → F , InjCodeAt.fill zero (suc A) (suc B) (F ∷ γ) code })
```
</div>
</details>

<!--en-->
Internal cardinality is the assertion that no member of a candidate receives an injection from the candidate. The formula below says exactly this: after binding a possible smaller member, membership in the candidate implies the negation of the `injLAt` formula. Its reading converts only the formula for the injection; the outer universal quantifier, implication, and negation compute to the function type already used by `IsCardinalL`.
<!--zh-->
内部基数性断言：候选者的任何成员都不能接受一条从候选者出发的单射。下式准确表达这一点：约束一个可能的较小成员后，「它属于候选者」蕴含 `injLAt` 公式的否定。其读取只需转换单射公式；外围的全称量词、蕴涵与否定会直接计算成 `IsCardinalL` 已使用的函数类型。
<!--ja-->
内部の基数性とは、候補のどの要素にも候補からの単射が存在しないという主張である。次の論理式はそれをそのまま述べる。より小さいかもしれない要素を束縛した後、その候補への所属から `injLAt` 論理式の否定を導く。読み取りで変換する必要があるのは単射の論理式だけであり、外側の全称量化、含意、否定は `IsCardinalL` がすでに使う関数型へ計算される。
<!--/-->

```agda
cardinalAt : ∀ {n} → Fin n → Formula S n
cardinalAt K = ∀̇ ((var zero ∈̇ var (suc K))
                  ⇒̇ ¬̇ injLAt (suc K) zero)
```

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CardinalAt {n : ℕ} (K : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    κ : S
    κ = lookup K γ

  read : ⟨ γ ⊨ cardinalAt K ⟩ → IsCardinalL κ
  read h δ δ∈κ inj = lower
    (h δ δ∈κ (InjLAt.fill (suc K) zero (δ ∷ γ) inj))

  fill : IsCardinalL κ → ⟨ γ ⊨ cardinalAt K ⟩
  fill c δ δ∈κ sat = lift
    (c δ δ∈κ (InjLAt.read (suc K) zero (δ ∷ γ) sat))
```
</div>
</details>

<!--en-->
Two type-theoretic facts govern the proof. When the second component of a dependent pair is proposition-valued, `Σ≡Prop` lifts a path between first components to a path between the pairs. A propositional truncation retains only inhabitedness. The graph reader `pair-out` may eliminate a truncated origin because its target fiber is a proposition, while the final step uses `∣_∣₁` to hide the particular graph and code. Neither operation selects a global family of witnesses.
<!--zh-->
两项类型论事实控制着这段证明。若依值对的第二分量取值于命题，`Σ≡Prop` 就能把第一分量之间的路径提升为整对之间的路径。命题截断只保留是否有元素。函数图的读回引理 `pair-out` 可以消去一个经命题截断的来源见证，因为它的目标纤维是命题；最后一步则用 `∣_∣₁` 隐去具体的函数图与编码。这两次操作都没有全局选出一族见证。
<!--ja-->
二つの型理論上の事実がこの証明を支える。依存対の第二成分が命題値なら、`Σ≡Prop` は第一成分の間のパスを対全体の間のパスへ持ち上げる。命題的切り詰めは、要素が存在するという事実だけを残す。グラフを読み戻す補題 `pair-out` は、行き先のファイバーが命題なので、命題的切り詰めに入った由来の証人をそこへ消去できる。最後の段階では `∣_∣₁` を用いて、具体的なグラフと符号を隠する。どちらの操作も、証人の族を大域的に選ばない。
<!--/-->

<!--en-->
The carrier `S` comes from the structure on `L`: an element `x : S` consists of an ambient set `fst x` together with a propositional certificate that it is constructible. Membership notation is taken from the ambient hierarchy, so expressions in the record explicitly compare underlying sets, such as `fst x ∈ˢ fst dom`. The certificates remain available in the second components whenever a construction must return an element of `L`.
<!--zh-->
论域 `S` 来自 `L` 上的结构：元素 `x : S` 由外围集合 `fst x` 与它可构造的命题性证书组成。成员记号取自外围层级，所以记录中的表达式明确比较底层集合，例如 `fst x ∈ˢ fst dom`。当构造必须返回 `L` 的元素时，可构造性证书仍保留在第二分量中。
<!--ja-->
台 `S` は `L` 上の構造から来る。要素 `x : S` は、周囲の集合 `fst x` と、それが構成可能であることを示す命題値の証明からなる。所属の記法は周囲の階層から取るため、レコード内の式は `fst x ∈ˢ fst dom` のように基礎集合を明示的に比較する。構成が `L` の要素を返す必要があるときには、構成可能性の証明が第二成分として残っている。
<!--/-->

<!--en-->
The notation `_⊨_` is satisfaction in the structure obtained by restricting the ambient hierarchy to constructible sets. Thus `(y ∷ x ∷ []) ⊨ graph` evaluates `graph` with elements of `L` in its two free slots. The name `AbsL` does not assert that arbitrary formulas are absolute between `L` and the ambient hierarchy; this chapter uses the restricted semantics and the already proved Replacement theorem.
<!--zh-->
记号 `_⊨_` 表示外围层级限制到可构造集合所得结构中的满足关系。因此，`(y ∷ x ∷ []) ⊨ graph` 用 `L` 的元素填入 `graph` 的两个自由槽位来解释它。名称 `AbsL` 并不声称任意公式在 `L` 与外围层级之间绝对；本章使用的是限制结构的语义与已经证明的替换定理。
<!--ja-->
記法 `_⊨_` は、周囲の階層を構成可能集合に制限して得られる構造での充足関係を表す。したがって `(y ∷ x ∷ []) ⊨ graph` は、`L` の要素を `graph` の二つの自由な位置に入れて解釈する。`AbsL` という名前は、任意の論理式が `L` と周囲の階層との間で絶対的だと主張するものではない。本章で使うのは制限された構造の意味論と、すでに証明された置換定理である。
<!--/-->

<!--en-->
## What it means for a function to be definable
<!--zh-->
## 函数可定义的含义
<!--ja-->
## 関数が定義可能であるとは何か
<!--/-->

<!--en-->
A `DefinableMap` first specifies two elements `dom` and `cod` of `L`, with no assumption that they are ordinals or cardinals. Its host-level rule `fn` is defined only for a pair consisting of `x : S` and evidence `m` that `x` belongs to `dom`; no value outside the domain is required. The type permits `fn x m` to mention `m`. Since membership is a proposition, any two such proofs are equal, and congruence identifies the corresponding values. The field `into` proves that every selected value belongs to `cod`.
<!--zh-->
一项 `DefinableMap` 首先指定 `L` 的两个元素 `dom` 与 `cod`，并不假设它们是序数或基数。宿主层取值规则 `fn` 只对一对数据有定义：`x : S` 以及 `x` 属于 `dom` 的证据 `m`；定义域之外无需给出值。类型允许 `fn x m` 提及 `m`。由于成员关系是命题，任意两份此类证明都相等，再由合同性可知相应取值相等。字段 `into` 证明每个选定值都属于 `cod`。
<!--ja-->
`DefinableMap` はまず `L` の二つの要素 `dom` と `cod` を指定し、それらが順序数や基数であるとは仮定しない。ホスト側の値を定める規則 `fn` は、`x : S` と `x` が `dom` に属する証拠 `m` の組に対してだけ定義される。定義域の外で値を与える必要はない。この型では `fn x m` が `m` に言及してもかまわない。所属は命題なので、そのような二つの証明は等しく、合同性によって対応する値も等しくなる。フィールド `into` は、選ばれた各値が `cod` に属することを証明する。
<!--/-->

```agda
record DefinableMap : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom cod : S
    fn      : (x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → S
    into    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) → ⟨ fst (fn x m) ∈ˢ fst cod ⟩
```

<!--en-->
The remaining fields connect the host-level values to an object-language formula. `graph` has two free slots and may contain constants from `S`; it need not be Δ₀. At every `x ∈ dom`, `defines` proves that the environment has the chosen value first and `x` second, while `only` proves that every satisfying `y` equals that chosen value in `S`. These conditions say nothing about inputs outside `dom`, and `only` does not assume that its candidate `y` belongs to `cod`. The separate field `into` supplies codomain containment for the selected values.
<!--zh-->
其余字段把宿主层取值与对象语言公式联系起来。`graph` 有两个自由槽位，可以含有来自 `S` 的常元，并不要求是 Δ₀ 公式。对每个 `x ∈ dom`，`defines` 证明以所选值在前、`x` 在后的环境满足该公式；`only` 则证明任何满足公式的 `y` 都在 `S` 中等于该所选值。这些条件不约束 `dom` 之外的输入，`only` 也不假设候选 `y` 属于 `cod`。所选值落入陪域由独立的字段 `into` 给出。
<!--ja-->
残るフィールドは、ホスト側の値を対象言語の論理式に結びつける。`graph` は二つの自由な位置をもち、`S` の要素を定数として含むことができ、Δ₀ 論理式である必要はない。各 `x ∈ dom` に対して、`defines` は選ばれた値を先、`x` を後に置いた環境で論理式が成り立つことを証明し、`only` は論理式を満たす任意の `y` がその選ばれた値と `S` の中で等しいことを証明する。これらの条件は `dom` の外の入力を制約せず、`only` は候補 `y` が `cod` に属するとも仮定しない。選ばれた値が終域に入ることは、別のフィールド `into` が与える。
<!--/-->

```agda
    graph   : Formula S 2
    defines : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩)
            → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
```

<!--en-->
## Encoding graph entries as ordered pairs
<!--zh-->
## 把图的表项编码成有序对
<!--ja-->
## グラフの項目を順序対として符号化する
<!--/-->

<!--en-->
The graph is represented as a set, so each input-output entry must first be expressed as an ordered pair. The defining formula reads the value in its first semantic slot and the input in its second, whereas the set encoding stores the corresponding entry as `pr(input,value)`. Keeping these two orders distinct is essential when the graph is constructed and later read back.
<!--zh-->
函数图由一个集合表示，因此每个输入输出表项都要先表示为有序对。定义公式在第一个语义槽位中读取函数值，在第二个槽位中读取输入；集合编码则把相应表项存为 `pr(输入,函数值)`。构造函数图并在随后读回其内容时，必须始终区分这两种次序。
<!--ja-->
関数グラフは集合として表すため、各入出力項目をまず順序対として表す。定義論理式は第一の意味論的な位置で値を、第二の位置で入力を読むが、集合による符号化は対応する項目を `pr(入力,値)` として格納する。グラフを構成し、後でその内容を読み戻すには、この二つの順序を区別し続ける必要がある。
<!--/-->

<!--en-->
## Constructing the graph inside L
<!--zh-->
## 在 L 内部构造函数图
<!--ja-->
## L の内部でグラフを構成する
<!--/-->

<!--en-->
The first construction assumes only definability and functionality. From `M` it will form the complete graph as an element of `L` and obtain precise ways to insert and read its ordered-pair entries. Injectivity is deliberately postponed: the same graph construction also applies to definable maps, such as a table of least witnesses, whose purpose does not require them to be injective.
<!--zh-->
第一项构造只假设可定义性与函数性。它从 `M` 形成一个属于 `L` 的完整函数图，并给出准确写入与读取有序对条目的方法。单射性留到下一阶段：同一函数图构造也适用于无需单射的可定义映射，例如最小见证表。
<!--ja-->
最初の構成が仮定するのは、定義可能性と関数性だけである。`M` から `L` の要素である完全な関数グラフを作り、その順序対の項目を正確に入れ、読み取る方法を得る。単射性は次の段階まで保留する。同じグラフ構成は、最小証人の表のように、目的上単射である必要のない定義可能な写像にも適用できるからである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Graph (M : DefinableMap) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open DefinableMap M public
```

<!--en-->
To meet the recursion hypothesis, retain `dom` and `graph` and prove that the satisfying-value fiber at each domain point has a center. The center is the pair `(fn x m, defines x m)`: the given value together with its satisfaction proof. The membership evidence `m` is passed directly to `fn`, so this construction does not extend the rule beyond `dom`. Neither `into` nor injectivity is needed at this stage.
<!--zh-->
为满足递归所需的假设，保留 `dom` 与 `graph`，并证明定义域每一点的满足值纤维都有中心。该中心是 `(fn x m, defines x m)`，即给定取值及其满足证明。成员证据 `m` 直接传给 `fn`，所以这一步不会把取值规则扩张到 `dom` 之外。此处既不需要 `into`，也不需要单射性。
<!--ja-->
再帰に必要な仮定を満たすため、`dom` と `graph` をそのまま用い、定義域の各点で充足する値のファイバーに中心があることを証明する。その中心は `(fn x m, defines x m)`、すなわち与えられた値とその充足の証明である。所属の証拠 `m` はそのまま `fn` に渡されるので、この構成は値を定める規則を `dom` の外へ拡張しない。この段階では `into` も単射性も必要ない。
<!--/-->

```agda
  private
    R : Recursion
    R = record
      { dom = dom ; graph = graph
      ; funct = λ x m → (fn x m , defines x m)
```

<!--en-->
It remains to contract every candidate `(y,h)` to that center. The field `only` gives `y ≡ fn x m`, but contractibility asks for a path from the center to the candidate, hence the use of `sym`. The second component is a satisfaction proof and therefore a proposition. `Σ≡Prop` consequently lifts the reversed equality of values to equality of the whole dependent pairs. This establishes the required unique existence constructively.
<!--zh-->
还须把每个候选 `(y,h)` 收缩到该中心。字段 `only` 给出 `y ≡ fn x m`，而可缩性要求一条从中心到候选的路径，因此代码使用 `sym`。第二分量是满足证明，因而为命题；所以 `Σ≡Prop` 能把反向后的取值相等提升为整个依值对的相等。这样便构造性地证明了所需的唯一存在。
<!--ja-->
残る仕事は、各候補 `(y,h)` をその中心へ収縮することである。フィールド `only` は `y ≡ fn x m` を与えるが、可縮性には中心から候補へのパスが必要なので `sym` を用いる。第二成分は充足の証明であり、したがって命題である。そこで `Σ≡Prop` が、向きを反転した値の等しさを依存対全体の等しさへ持ち上げる。これにより、必要な一意存在が構成的に証明される。
<!--/-->

```agda
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ graph)) (sym (only x m y h)) } }
```

<!--en-->
Replacement now collects the ordered-pair values into a constructible set `F`. The auxiliary pairing formula reconciles the two conventions: the original relation is evaluated as `(value,input)`, while members of `F` are `pr(input,value)`. `F-in` inserts every prescribed entry, and `F-out` says under propositional truncation that every member has such an origin. For fixed `x` and `y`, `pair-out` strengthens membership of `pr(x,y)` to a domain proof and an equality `y = fn(x)`. This elimination is valid because `Fib x y` is a proposition, using proof irrelevance of membership and the fact that equality in `V` is proposition-valued. These readings prove `sv`, single-valuedness, and `dm`, that the domain is exactly `dom`. Forming `F` is the step that uses the Replacement theorem and hence the given excluded middle; the subsequent readings introduce no choice.
<!--zh-->
现在由替换把有序对取值收集成可构造集合 `F`。辅助配对公式协调两种次序：原关系按 `(值,输入)` 解释，而 `F` 的成员是 `pr(输入,值)`。`F-in` 写入每个指定条目，`F-out` 则在命题截断下说明每个成员都来自这样的条目。固定 `x` 与 `y` 后，`pair-out` 把 `pr(x,y)` 属于 `F` 加强为一份定义域证明与等式 `y = fn(x)`。这次消去是合法的，因为 `Fib x y` 是命题，其中用到成员证明的证明无关性以及 `V` 中相等取值于命题。由这些读式可证明 `sv` 所表达的单值性，以及 `dm` 所表达的定义域恰为 `dom`。形成 `F` 的步骤使用替换定理，因而依赖给定的排中律；后续读取没有引入选择。
<!--ja-->
ここで置換により、順序対としての値を構成可能集合 `F` に集める。補助的な対の論理式が二つの順序を調整する。もとの関係は `(値,入力)` として解釈されるが、`F` の要素は `pr(入力,値)` である。`F-in` は指定された各項目を入れ、`F-out` は命題的切り詰めのもとで、すべての要素がそのような項目に由来することを述べる。`x` と `y` を固定すると、`pair-out` は `pr(x,y)` が `F` に属することから、定義域の証明と等式 `y = fn(x)` を得る。この除去が正当なのは、`Fib x y` が命題だからである。ここでは所属の証明無関係性と、`V` における等しさが命題値であることを用いる。これらの読み取りから、`sv` が表す一価性と、`dm` が表す定義域が正確に `dom` であることが従う。`F` の形成には置換定理が使われるため、与えられた排中律に依存する。その後の読み取りに選択は入らない。
<!--/-->

```agda
  open RecursionGraph R public
    using ( Mem; isPropMem; F; F-in; F-out; Fib; isPropFib; pair-out; γ; sv; dm )
```

<!--en-->
The fourth condition for the eventual code is containment in the codomain. Given an actual graph entry `pr(fst x,fst y) ∈ fst F`, `pair-out` yields `m : x ∈ dom` and `e : fst y ≡ fst(fn x m)`. The field `into x m` proves membership of `fst(fn x m)` in `fst cod`. Transport must therefore follow `sym e`, from the chosen value back to `y`, to conclude `y ∈ cod`. This proves only that the image is contained in the codomain, not that every codomain element occurs.
<!--zh-->
最终编码的第四项条件是取值落入陪域。给定实际函数图条目 `pr(fst x,fst y) ∈ fst F`，`pair-out` 给出 `m : x ∈ dom` 与 `e : fst y ≡ fst(fn x m)`。字段 `into x m` 证明 `fst(fn x m)` 属于 `fst cod`。因此，成员关系必须沿 `sym e` 从所选值运输回 `y`，从而得到 `y ∈ cod`。这只证明像包含于陪域，并不证明陪域的每个元素都会出现。
<!--ja-->
最終的な符号の第四条件は、値が終域に入ることである。実際のグラフ項目 `pr(fst x,fst y) ∈ fst F` が与えられると、`pair-out` は `m : x ∈ dom` と `e : fst y ≡ fst(fn x m)` を返す。フィールド `into x m` は `fst(fn x m)` が `fst cod` に属することを証明する。したがって所属は `sym e` に沿って、選ばれた値から `y` へ輸送し、`y ∈ cod` を得る。これは像が終域に含まれることだけを示し、終域の各要素が現れるとは主張しない。
<!--/-->

```agda
  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst cod ⟩
  ran x y h = subst (λ w → ⟨ w ∈ fst cod ⟩) (sym e) (into x m)
    where
    m = fst (pair-out x y h)
    e = snd (pair-out x y h)
```
</div>
</details>

<!--en-->
## From external injectivity to a coded injection
<!--zh-->
## 从外部单射性得到编码单射
<!--ja-->
## 外部の単射性から符号化された単射へ
<!--/-->

<!--en-->
To turn this graph into an injection code, add the genuinely new hypothesis of injectivity. For two inputs equipped with proofs of membership in `dom`, it says that equality of the underlying sets of their selected values implies equality of the underlying input sets. The membership arguments remain explicit because `fn` is dependently typed in them. Their proof irrelevance guarantees coherence between different proofs, but the hypothesis is stated with the exact evidence supplied at the two inputs. Its conclusion has precisely the strength required by the equality clause of `injAt`.
<!--zh-->
要把这张函数图变成单射编码，还须加入真正新的单射性假设。对两个各自带有 `dom` 成员证明的输入，它断言：若所选取值的底层集合相等，则输入的底层集合相等。成员实参仍然显式出现，因为 `fn` 的类型依值地依赖于它们。证明无关性保证不同成员证明之间相容，但这条假设仍按两个输入处实际给出的证据陈述。其结论的强度恰好符合 `injAt` 的相等条款。
<!--ja-->
このグラフを単射の符号にするには、実質的に新しい仮定として単射性を加える必要がある。`dom` への所属の証明を伴う二つの入力について、選ばれた値の基礎集合が等しければ、入力の基礎集合も等しいと仮定する。`fn` の型は所属の証明に依存しているので、その引数は明示されたままである。証明無関係性は異なる所属の証明の間の整合性を保証するが、仮定自体は二つの入力で実際に与えられた証拠について述べられる。その結論は `injAt` の等号の条項が要求する強さと正確に一致する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Inj (M : DefinableMap)
           (inj : (x : S) (m : ⟨ fst x ∈ˢ fst (DefinableMap.dom M) ⟩)
                  (x' : S) (m' : ⟨ fst x' ∈ˢ fst (DefinableMap.dom M) ⟩)
                → fst (DefinableMap.fn M x m) ≡ fst (DefinableMap.fn M x' m')
                → fst x ≡ fst x') where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Opening `Graph M` makes the already constructed `F` and its proved properties available in the injective case. This keeps two mathematically useful conclusions at hand. One may retain the particular graph `F` together with its code when a later construction must name or combine graphs. One may instead use `injL`, which remembers only that some coded injection exists. The distinction is between concrete data and its propositional existence.
<!--zh-->
打开 `Graph M` 后，已经构造出的 `F` 及其性质可用于单射情形。于是同时保留两种数学上有用的结论：当后续构造必须指名或组合函数图时，可以保留这个具体的 `F` 及其编码；也可以使用 `injL`，只记住某个编码单射存在。两者的区别在于具体数据与其命题性存在。
<!--ja-->
`Graph M` を開くことで、すでに構成した `F` と証明済みの性質を単射の場合にも使えるようにする。これにより、数学的に有用な二種類の結論が同時に得られる。後の構成でグラフを名指したり組み合わせたりする必要があるなら、具体的な `F` とその符号を保てる。一方 `injL` を使えば、符号化された単射が何か存在することだけを残せる。この違いは、具体的なデータとその命題的な存在との違いである。
<!--/-->

```agda
  open Graph M public
```

<!--en-->
The formula `injAt zero` fixes an output `y` and compares two inputs `x` and `x'`: if both `pr(x,y)` and `pr(x',y)` lie in `F`, then the inputs are equal. Applying `pair-out` to the first entry gives `e : y = fn(x)`, and applying it to the second gives `e' : y = fn(x')`, together with the two required domain proofs. Hence `sym e ∙ e'` is the path `fn(x) = fn(x')`; the host-level hypothesis `inj` turns it into `x = x'`, and `injAt-in` translates this property into the satisfaction judgment `ij`. This argument uses injectivity, not merely `only`: `only` compares outputs at one fixed input and is what underlies single-valuedness.
<!--zh-->
公式 `injAt zero` 固定输出 `y`，比较两个输入 `x` 与 `x'`：若 `pr(x,y)` 和 `pr(x',y)` 都属于 `F`，则两个输入相等。对第一条目应用 `pair-out` 得到 `e : y = fn(x)`，对第二条目应用它则得到 `e' : y = fn(x')`，并同时得到所需的两份定义域证明。因此，`sym e ∙ e'` 正是路径 `fn(x) = fn(x')`；宿主层假设 `inj` 把它化为 `x = x'`，`injAt-in` 再把这一性质转成满足判断 `ij`。这段论证使用的是单射性，而不仅是 `only`；`only` 比较固定输入处的输出，它支持的是单值性。
<!--ja-->
論理式 `injAt zero` は出力 `y` を固定し、二つの入力 `x` と `x'` を比較する。`pr(x,y)` と `pr(x',y)` がともに `F` に属するなら、入力が等しいと述べる。最初の項目に `pair-out` を適用すると `e : y = fn(x)` が得られ、二番目からは `e' : y = fn(x')` が得られる。同時に、必要な二つの定義域の証明も得られる。したがって `sym e ∙ e'` はパス `fn(x) = fn(x')` であり、ホスト側の仮定 `inj` がこれを `x = x'` に変え、`injAt-in` がその性質を充足判断 `ij` に移す。この議論が使うのは単射性であって、`only` だけではない。`only` は一つの固定された入力で出力を比較し、一価性を支えるものである。
<!--/-->

```agda
  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x' y q
    in inj x m x' m' (sym e ∙ e'))
```

<!--en-->
The tuple `sv , dm , ij , ran` fills the four fields of `InjCode F dom cod` in order. Here `sv` proves single-valuedness, `dm` proves that the graph domain is exactly `dom`, and `ij` proves object-language injectivity, all in the environment `F ∷ dom ∷ []`. The final field `ran` states at host level that values occurring in `F` belong to `cod`. Nothing in this code asserts surjectivity, so it describes an injection into `cod`, not a bijection.
<!--zh-->
四元组 `sv , dm , ij , ran` 依次填入 `InjCode F dom cod` 的四个字段。其中，`sv` 证明单值性，`dm` 证明函数图的定义域恰为 `dom`，`ij` 证明对象语言中的单射性；三者都在环境 `F ∷ dom ∷ []` 中陈述。最后的 `ran` 在宿主层断言 `F` 中出现的值属于 `cod`。这份编码没有断言满射性，所以它描述的是到 `cod` 的单射，而不是双射。
<!--ja-->
四つ組 `sv , dm , ij , ran` は、`InjCode F dom cod` の四つのフィールドを順に満たす。`sv` は一価性を、`dm` はグラフの定義域が正確に `dom` であることを、`ij` は対象言語での単射性を証明し、三つとも環境 `F ∷ dom ∷ []` で述べられる。最後の `ran` は、`F` に現れる値が `cod` に属することをホスト側で述べる。この符号は全射性を主張しないので、`cod` への単射を表し、全単射を表すものではない。
<!--/-->

```agda
  code : InjCode F dom cod
  code = sv , dm , ij , ran
```

<!--en-->
Finally, the concrete pair `(F,code)` is inserted into a propositional truncation. The resulting term `injL : InjL dom cod` states that a constructible graph carrying an injection code exists, while forgetting which graph was constructed. This is the proposition needed in cardinal comparisons and can be eliminated when the desired conclusion is again a proposition. The particular `F` and `code` remain separately available within the instantiated module when a construction needs them. Thus it is the coded graph, not the external rule itself, that has been internalized in `L`.
<!--zh-->
最后，把具体的对 `(F,code)` 放入命题截断。所得项 `injL : InjL dom cod` 断言存在一张带单射编码的可构造函数图，同时忘去所构造的是哪一张图。基数比较需要的正是这个命题，并可在目标仍为命题时对它作消去。若某项构造需要具体数据，实例化后的模块中仍可分别使用 `F` 与 `code`。因此，被内化到 `L` 中的是编码后的函数图，而不是外部取值规则本身。
<!--ja-->
最後に、具体的な対 `(F,code)` を命題的切り詰めに入れる。得られる項 `injL : InjL dom cod` は、単射の符号をもつ構成可能な関数グラフが存在することを述べ、どのグラフを構成したかは忘れる。基数比較に必要なのはこの命題であり、求める結論が再び命題であるときに消去できる。具体的なデータが必要な構成では、具体化したモジュールの中で `F` と `code` をそれぞれ引き続き使える。したがって `L` に内部化されたのは符号化された関数グラフであり、外部の規則そのものではない。
<!--/-->

```agda
  injL : InjL dom cod
  injL = ∣ F , code ∣₁
```
</div>
</details>
