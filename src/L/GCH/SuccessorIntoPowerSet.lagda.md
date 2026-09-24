```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Injecting the successor cardinal into the power set
<!--zh-->
# 把后继基数单射到幂集
<!--ja-->
# 後続基数を冪集合へ単射する
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The excluded-middle assumption is indexed at `ℓ-suc ℓ`, the level at which the relevant propositions about sets and coded graphs live. Every classical comparison used below is consequently traceable to this one parameter.
<!--zh-->
排中律假设取在 `ℓ-suc ℓ`，相关的集合命题与编码图命题正位于这一层级。因此，下文每次经典比较都可追溯到这个参数。
<!--ja-->
排中律の仮定は `ℓ-suc ℓ` のレベルに置かれる。集合と符号化されたグラフに関する必要な命題が、このレベルに属するためである。したがって、以下の古典的な比較はすべて、この一つのパラメータに遡れる。
<!--/-->

```agda
module L.GCH.SuccessorIntoPowerSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∃̇_; ∃̇∈ )
import FOL.ZFModel
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; isL-trans; isTransV; isPropIsTransV )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL; SuccCardL )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate; inclusion-coded; injl-trans; module Relation )
open import L.Coding.Model {ℓ} using ( svAt-out; domAt-in )
open import L.Coding.Injection {ℓ} lem using ( injAt-out )
open import L.GCH.BelowSuccessorCardinal {ℓ} lem using ( below-succ-injects )
open import L.GCH.Assembly {ℓ} lem using ( SuccIntoPower )
open import L.DefinableInjection {ℓ} lem using ( module Inj )
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )
```

<!--en-->

Cantor's theorem inside `L` rules out an internally coded injection from `𝒫 κ` into `κ`. Starting from a successor cardinal `δ` of `κ` and a separately supplied comparison `InjL (𝒫 κ) δ`, this chapter constructs the reverse comparison `InjL δ (𝒫 κ)`. Here `InjL a b` is the propositional truncation of the existence of a graph in `L` coding an injection from `a` to `b`. The proof transfers the ordinal order on `δ` back to `𝒫 κ`, collapses that order to an ordinal `μ`, and uses Cantor's obstruction to show that `μ` cannot lie below `δ`.
<!--zh-->

`L` 内部的 Cantor 定理排除了从 `𝒫 κ` 到 `κ` 的内部编码单射。本章从 `κ` 的后继基数 `δ` 以及另行给出的比较 `InjL (𝒫 κ) δ` 出发，构造反方向的比较 `InjL δ (𝒫 κ)`。这里，`InjL a b` 是「存在一张 `L` 中的图，编码从 `a` 到 `b` 的单射」的命题截断。证明先把 `δ` 上的序数次序沿给定单射拉回到 `𝒫 κ`，再把所得次序塌缩为序数 `μ`，最后用 Cantor 障碍证明 `μ` 不可能属于 `δ`。
<!--ja-->

`L` の内部での Cantor の定理は、`𝒫 κ` から `κ` への内部的に符号化された単射を排除する。この章では、`κ` の後続基数 `δ` と、別に与えられた比較 `InjL (𝒫 κ) δ` から、逆向きの比較 `InjL δ (𝒫 κ)` を構成する。ここで `InjL a b` は、`a` から `b` への単射を符号化する `L` のグラフが存在することの命題的切り詰めである。証明では、`δ` 上の順序数の順序を与えられた単射に沿って `𝒫 κ` へ引き戻し、その順序を順序数 `μ` へ崩壊して、Cantor の障害から `μ` が `δ` に属しえないことを示す。
<!--/-->

<!--en-->
Classical reasoning enters through the explicit parameter `lem`. Ordinal trichotomy supplies the visible case splits, while the separation and coded-injection results used in the argument are also instantiated with the same assumption. Thus the chapter records its classical dependence in one place.
<!--zh-->
经典推理通过显式参数 `lem` 引入。序数三歧性给出证明中可见的分类讨论，而这里使用的分离定理与编码单射结果也以同一个假设实例化。因此，本章把经典依赖统一记录在一处。
<!--ja-->
古典的推論は、明示的なパラメータ `lem` を通して導入される。順序数の三分法が証明中の目に見える場合分けを与え、ここで用いる分出定理と符号化された単射に関する結果も、同じ仮定のもとで具体化されている。したがって、この章の古典的な依存は一箇所に明記されている。
<!--/-->



<!--en-->
The diagonal subset and the later pullback order must be sets of `L`, so both are described by first-order formulas interpreted in the constructible model. The available syntax expresses membership, conjunction, negation, and the bounded or unbounded existential witnesses needed to describe those relations.
<!--zh-->
对角子集与稍后的拉回序都必须是 `L` 中的集合，因此二者都由在可构造模型中解释的一阶公式描述。这里的语法可表达隶属、合取、否定，以及描述这些关系所需的有界或无界存在见证。
<!--ja-->
対角部分集合と後で用いる引き戻し順序は、ともに `L` の集合でなければならない。そこで、構成可能モデルで解釈される一階の論理式によって両者を記述する。ここで用意される構文は、所属・連言・否定と、これらの関係を表すために必要な有界または非有界の存在証人を表現できる。
<!--/-->

<!--en-->
The pullback order will be proved well-founded by sending every descending step to a membership step in the ambient cumulative hierarchy and applying regularity there. Facts about constructible ordinals then turn membership below an ordinal into the ordinal structure needed for comparison.
<!--zh-->
为证明拉回序良基，证明把它的每个下降步骤送到外围累积层级中的一个隶属步骤，再在那里应用正则公理。关于可构造序数的事实随后把序数以下的隶属转化为比较所需的序数结构。
<!--ja-->
引き戻し順序の整礎性は、その下降の各段階を周囲の累積階層における所属の一段階へ移し、そこで正則性を適用して証明する。続いて、構成可能な順序数についての事実により、順序数の下への所属から比較に必要な順序数構造を得る。
<!--/-->

<!--en-->
An internal size comparison has two levels. `InjCode F a b` retains a particular constructible graph and its injection laws, whereas `InjL a b` retains only the propositionally truncated existence of such a code. Successor-cardinal minimality, coded inclusions, and composition will let the proof combine these comparisons without exposing a global graph.
<!--zh-->
内部大小比较分为两个层次。`InjCode F a b` 保留一张特定的可构造图及其单射律，而 `InjL a b` 只保留这种码存在的命题截断。后继基数的最小性、编码包含与单射复合使证明能够组合这些比较，而不暴露一张全局选定的图。
<!--ja-->
内部の大きさの比較には二つの層がある。`InjCode F a b` は特定の構成可能なグラフとその単射の法則を保持するが、`InjL a b` はそのような符号が存在するという命題的切り詰めだけを保持する。後続基数の最小性、符号化された包含、単射の合成により、大域的なグラフを取り出さずにこれらの比較を組み合わせられる。
<!--/-->

<!--en-->
Two earlier results control the final comparison. Every ordinal strictly below the successor cardinal `δ` injects into its base `κ`, and a coded well-order can be collapsed to a constructible ordinal together with coded maps to and from its collapse image. The third ingredient, `InjL (𝒫 κ) δ`, is an assumption of this chapter's conditional theorem; it is not a consequence of the successor-cardinal record alone.
<!--zh-->
前面的两项结果控制最终比较。每个严格低于后继基数 `δ` 的序数都可单射到其基数 `κ`；另一方面，编码良序可以塌缩为可构造序数，并得到通往塌缩像及从塌缩像返回的编码映射。第三项材料 `InjL (𝒫 κ) δ` 是本章条件定理的假设，不能仅由后继基数记录推出。
<!--ja-->
先の二つの結果が最終的な比較を支える。後続基数 `δ` より真に小さい順序数はすべて、その基数 `κ` へ単射する。また、符号化された整列順序は構成可能な順序数へ崩壊でき、崩壊像への符号化写像と、そこから戻る符号化写像が得られる。第三の材料 `InjL (𝒫 κ) δ` は、この章の条件付き定理の仮定であり、後続基数の記録だけからは従わない。
<!--/-->

<!--en-->
Several equalities below identify dependent pairs whose second components are proofs. Since those proof components are propositions, equality of the underlying sets suffices; transport then moves membership and graph facts along the resulting identifications.
<!--zh-->
下文若干等式要认同第二分量为证明的依值对。由于这些证明分量都是命题，只需证明底层集合相等；随后便可沿所得同一视搬运隶属与图成立的事实。
<!--ja-->
以下では、第二成分が証明である依存対をいくつか同一視する。その証明成分は命題なので、底の集合の等しさだけで十分である。得られた同一視に沿って、所属やグラフについての事実を輸送できる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
Accessibility records express the well-founded recursion used for the pulled-back order. Propositional truncation expresses mere existence throughout the chapter, and its eliminations will always have a proposition, such as the empty type or another `InjL` statement, as their target.
<!--zh-->
可达性记录表达拉回序所需的良基递归。命题截断在全章中表达仅仅存在；每次从中消去时，目标始终是命题，例如空类型或另一个 `InjL` 陈述。
<!--ja-->
到達可能性の記録は、引き戻した順序に対する整礎再帰を表す。命題的切り詰めは、この章全体で単なる存在を表し、そこからの消去先は常に、空の型や別の `InjL` の主張のような命題である。
<!--/-->

```agda
import Cubical.Induction.WellFounded as WF
open WF using ( Acc; acc; WellFounded )
```

<!--en-->
Membership of underlying sets is read in the ambient hierarchy when regularity and transitivity are applied. This ambient relation must be distinguished from membership between elements packaged with their constructibility proofs.
<!--zh-->
应用正则公理与传递性时，底层集合的隶属在外围层级中读取。这个外围关系必须与「连同可构造性证明打包的元素」之间的隶属相区分。
<!--ja-->
正則性と推移性を適用するとき、底の集合の所属は周囲の階層で読む。この周囲の関係は、構成可能性の証明と組にされた要素どうしの所属とは区別しなければならない。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
Write `SV.S` for an ambient set. It is used when a claim, such as pointwise containment between underlying ordinals, ranges over the cumulative hierarchy itself.
<!--zh-->
以 `SV.S` 表示外围集合。当逐点包含等陈述直接量化累积层级中的底层对象时，就使用这个论域。
<!--ja-->
周囲の集合を `SV.S` と書く。順序数の底の集合どうしの逐点包含のように、累積階層そのものの対象を動く主張で、この台を用いる。
<!--/-->

```agda
module SV = hPropStructure 𝒮ᵥ using ( S )
```

<!--en-->
Write `SL.S` for a set together with its certificate of constructibility. The internal power set, successor-cardinal predicate, and coded-injection relation all take their arguments in this carrier.
<!--zh-->
以 `SL.S` 表示集合连同其可构造性证书。内部幂集、后继基数谓词与编码单射关系都以这个论域中的元素为参数。
<!--ja-->
集合とその構成可能性の証明との組を `SL.S` と書く。内部の冪集合、後続基数の述語、符号化された単射の関係は、いずれもこの台の要素を引数に取る。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
```

<!--en-->
The ZF structure on `L` determines its internal power set. Its specification identifies membership in `𝒫 κ` with the internal subset relation, where the quantification ranges over constructible model elements.
<!--zh-->
`L` 上的 ZF 结构确定其内部幂集。相应规格把 `𝒫 κ` 中的隶属与内部子集关系等同起来，其中量化范围是可构造模型的元素。
<!--ja-->
`L` 上の ZF 構造が、その内部の冪集合を定める。その仕様は、`𝒫 κ` への所属を内部の部分集合関係と同一視し、そこでの量化は構成可能モデルの要素を動く。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ using ( isZFModel; module isZFModel; ℩-spec )
```

<!--en-->
Object-language formulas will be evaluated in environments of constructible sets. Absoluteness supplies the semantic reading that connects those satisfaction statements to the host-level predicates used in the proof.
<!--zh-->
对象语言公式将在可构造集合组成的环境中求值。绝对性给出语义读法，把这些满足陈述与证明所用的宿主层谓词连接起来。
<!--ja-->
対象言語の論理式は、構成可能な集合からなる環境で評価される。絶対性が、その充足の主張と証明で用いる台の水準の述語とを結ぶ意味論的な読みを与える。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
An element of `SL.S` consists of an underlying set and a proof of constructibility. Because constructibility is a proposition, equality of the underlying sets lifts to equality in `SL.S`; no additional choice of equality between certificates is required.
<!--zh-->
`SL.S` 的元素由底层集合与可构造性证明组成。由于可构造性是命题，底层集合的相等可提升为 `SL.S` 中的相等，无须另行选择证书之间的相等。
<!--ja-->
`SL.S` の要素は、底の集合と構成可能性の証明からなる。構成可能性は命題なので、底の集合の等しさを `SL.S` における等しさへ持ち上げられ、証明どうしの等しさを別に選ぶ必要はない。
<!--/-->

```agda
S≡ : {x y : SL.S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

<!--en-->
## Internal subsets belong to the model's power set
<!--zh-->
## 内部子集属于模型的幂集
<!--ja-->
## 内部部分集合はモデルの冪集合に属する
<!--/-->

<!--en-->
The first construction converts pointwise internal containment into membership in the model's power set. It applies to arbitrary constructible sets `κ` and `y`: if every constructible element of `y` belongs to `κ`, then `y` is an internal subset of `κ` and hence a member of `𝒫 κ`.
<!--zh-->
第一个构造把逐点的内部包含转化为模型幂集中的隶属。它适用于任意可构造集合 `κ` 与 `y`：若 `y` 的每个可构造元素都属于 `κ`，则 `y` 是 `κ` 的内部子集，因而属于 `𝒫 κ`。
<!--ja-->
最初の構成は、点ごとの内部包含をモデルの冪集合への所属へ変える。これは任意の構成可能集合 `κ` と `y` に適用できる。`y` の構成可能な要素がすべて `κ` に属するなら、`y` は `κ` の内部部分集合であり、したがって `𝒫 κ` に属する。
<!--/-->

```agda
into-power :
    (zf : ModelL.isZFModel) (κ y : SL.S)
  → ((z : SL.S) → ⟨ fst z ∈ˢ fst y ⟩ → ⟨ fst z ∈ˢ fst κ ⟩)
  → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
into-power zf κ y sub =
```

<!--en-->
The power-set specification states that membership of `y` in `𝒫 κ` is equivalent to the pointwise internal subset condition. Rewriting by this equivalence leaves exactly the supplied containment proof.
<!--zh-->
幂集规格断言：`y` 属于 `𝒫 κ`，当且仅当逐点的内部子集条件成立。沿这一等价改写后，目标恰好就是已经给出的包含证明。
<!--ja-->
冪集合の仕様は、`y` が `𝒫 κ` に属することと、点ごとの内部部分集合条件とが同値であると述べる。この同値性に沿って書き換えると、目標はちょうど与えられた包含の証明になる。
<!--/-->

```agda
  subst ⟨_⟩ (sym (ModelL.℩-spec (hasPower κ) y)) sub
  where open ModelL.isZFModel zf using ( hasPower )
```

<!--en-->
## Cantor's diagonal argument inside L
<!--zh-->
## L 内部的 Cantor 对角论证
<!--ja-->
## L の内部での Cantor の対角線論法
<!--/-->

<!--en-->
We now fix an arbitrary constructible set `κ` and prove the internal Cantor obstruction for its model power set. No cardinality or infinitude hypothesis on `κ` is needed for this part.
<!--zh-->
现在固定任意可构造集合 `κ`，并对它的模型幂集证明内部 Cantor 障碍。这一部分不需要假设 `κ` 是基数或无穷集。
<!--ja-->
ここで任意の構成可能集合 `κ` を固定し、そのモデル内の冪集合について内部の Cantor の障害を証明する。この部分では、`κ` が基数であることも無限であることも仮定しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Cantor (zf : ModelL.isZFModel) (κ : SL.S) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Throughout the diagonal argument, `𝒫 κ` means the power set supplied by the fixed ZF model on `L`. Thus its elements are precisely the subsets recognized inside that model.
<!--zh-->
在整个对角论证中，`𝒫 κ` 指固定的 `L` 上 ZF 模型所给出的幂集。因此，它的成员恰是该模型内部所识别的子集。
<!--ja-->
対角線論法を通して、`𝒫 κ` は固定した `L` 上の ZF モデルが与える冪集合を意味する。したがって、その要素は、まさにこのモデルの内部で認識される部分集合である。
<!--/-->

```agda
  open ModelL.isZFModel zf using ( 𝒫 )
```

<!--en-->
The diagonal argument is carried out for one explicitly given graph `F` together with its coding. All later statements concern this fixed graph.
<!--zh-->
对角论证针对一条显式给定的图 `F` 及其编码展开。后文一切陈述都只关于这条固定的图。
<!--ja-->
対角の議論は、明示的に与えられた一つのグラフ `F` とその符号について展開される。後の主張はすべて、この固定されたグラフに関するものである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Diag (F : SL.S) (code : InjCode F (𝒫 κ) κ) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The environment of the graph pairs the graph with the power set over which it is total.
<!--zh-->
图的环境把图与其全域所及的幂集配对。
<!--ja-->
グラフの環境は、グラフと、それが全域的である冪集合とを対にする。
<!--/-->

```agda
    γF : SL.S ^ 2
    γF = F ∷ 𝒫 κ ∷ []
```

<!--en-->
The range clause of the coding says that every value recorded by the graph belongs to `κ`.
<!--zh-->
编码的值域条款说：图记录的每个值都属于 `κ`。
<!--ja-->
符号の値域の条項は、グラフに記録されたすべての値が `κ` に属することを言う。
<!--/-->

```agda
    ranF : (x y : SL.S) → Holds F x y → ⟨ fst y ∈ fst κ ⟩
    ranF = code .snd .snd .snd
```

<!--en-->
The totality clause says that every member of `𝒫 κ` has some value under `F`. The value witness remains under propositional truncation, so this statement supplies existence without choosing a value globally.
<!--zh-->
全域性条款断言：`𝒫 κ` 的每个成员在 `F` 下都有某个值。值的见证仍处于命题截断之下，因此这里只给出存在性，而不全局选定一个值。
<!--ja-->
全域性の条項は、`𝒫 κ` の各要素が `F` による何らかの値をもつことを述べる。値の証人は命題的切り詰めの内側に留まるので、ここでは存在だけが得られ、大域的に値を選ぶことはない。
<!--/-->

```agda
    valF : (x : SL.S) → ⟨ fst x ∈ fst (𝒫 κ) ⟩
         → ∥ Σ[ y ∈ SL.S ] Holds F x y ∥₁
    valF = domAt-in zero (suc zero) γF (code .snd .fst)
```

<!--en-->
The injectivity clause recovers the input from the value: two members with the same recorded value have equal underlying sets.
<!--zh-->
单射性条款由值恢复输入：记录值相同的两个成员，其底层集合相等。
<!--ja-->
単射性の条項は、値から入力を復元する。同じ記録された値をもつ二つの要素は、底の集合が等しくなる。
<!--/-->

```agda
    injF : (y x x' : SL.S) → Holds F x y → Holds F x' y → fst x ≡ fst x'
    injF = injAt-out zero γF (code .snd .snd .fst)
```

<!--en-->
The diagonal predicate says, merely, that some member `A` of the power set has its recorded value equal to `ξ`, while `ξ` does not belong to `A`. Existence is truncated; no such set is chosen.
<!--zh-->
对角谓词说：仅仅地存在幂集的某个成员 `A`，其被记录的值等于 `ξ`，而 `ξ` 不属于 `A`。存在是截断的；并不选定这样的集合。
<!--ja-->
対角の述語は、単に、冪集合のある要素 `A` で、記録された値が `ξ` に等しく、しかも `ξ` が `A` に属さないものが存在する、と言う。存在は切り詰められており、そのような集合は選ばれない。
<!--/-->

```agda
    Diagonal : SL.S → Type (ℓ-suc ℓ)
    Diagonal ξ = ∥ Σ[ A ∈ SL.S ] ( ⟨ fst A ∈ fst (𝒫 κ) ⟩ × Holds F A ξ
                                 × (⟨ fst ξ ∈ fst A ⟩ → ⊥₀) ) ∥₁
```

<!--en-->
Satisfaction of the application atom is literally the host-level graph holding, by the adequacy of the application coding.
<!--zh-->
应用原子的满足，依应用编码的充分性，字面上就是宿主层图成立。
<!--ja-->
適用のアトムの充足は、適用の符号化の妥当性により、文字どおり、台の水準でのグラフの成立である。
<!--/-->

```agda
    private
      a1 : (ξ A : SL.S)
         → ⟨ (A ∷ ξ ∷ []) ⊨ appC F zero (suc zero) ⟩ ≡ Holds F A ξ
      a1 ξ A = cong ⟨_⟩ (appC-adequate F zero (suc zero) (A ∷ ξ ∷ []))
```

<!--en-->
The formula defining the diagonal condition searches within `𝒫 κ` for a set `A` such that `F` records the pair `(A, ξ)` and `ξ` does not belong to `A`. The bounded quantifier records exactly that the witness is an internal subset of `κ`; separation over `κ` then forms the set of all `ξ∈κ` satisfying this condition.
<!--zh-->
定义对角条件的公式在 `𝒫 κ` 内寻找集合 `A`，使 `F` 记录配对 `(A, ξ)`，且 `ξ` 不属于 `A`。有界量词准确记录见证是 `κ` 的内部子集；随后在 `κ` 上应用分离，得到所有满足这一条件的 `ξ∈κ` 所组成的集合。
<!--ja-->
対角条件を定める論理式は、`𝒫 κ` の中から、`F` が対 `(A, ξ)` を記録し、かつ `ξ` が `A` に属さないような集合 `A` を探する。有界量化は、その証人が `κ` の内部部分集合であることを正確に記録する。続いて `κ` 上で分出を適用し、この条件を満たす `ξ∈κ` 全体の集合を作る。
<!--/-->

```agda
    opaque
      φD : Formula SL.S 1
      φD = ∃̇∈ (con (𝒫 κ))
             (appC F zero (suc zero) ∧̇ ¬̇ (var (suc zero) ∈̇ var zero))
```

<!--en-->
Adequacy of the application coding identifies the formula atom for applying `F` to `A` with the semantic statement `Holds F A ξ`. This equality is what allows the diagonal formula and the coded graph to be used interchangeably in the two directions below.
<!--zh-->
应用编码的充分性把「将 `F` 应用于 `A`」这一公式原子与语义陈述 `Holds F A ξ` 认同起来。正是这条等式使下文能够在两个方向上互换使用对角公式与编码图。
<!--ja-->
適用の符号化の妥当性により、`F` を `A` に適用する論理式のアトムは、意味論的な主張 `Holds F A ξ` と同一視される。この等式によって、以下の二方向で対角論理式と符号化されたグラフを相互に読み替えられる。
<!--/-->

```agda
      φD-out : (ξ : SL.S) → ⟨ (ξ ∷ []) ⊨ φD ⟩ → Diagonal ξ
      φD-out ξ = map₁ (λ { (A , (mA , (h , n))) →
        A , mA , transport (a1 ξ A) h , (λ k → lower (n k)) })
```

<!--en-->
Conversely, a chosen `A ∈ 𝒫 κ`, a graph fact `Holds F A ξ`, and a proof that `ξ ∉ A` satisfy the diagonal formula. These data are packaged under the formula's truncated bounded existential.
<!--zh-->
反过来，给定 `A ∈ 𝒫 κ`、图事实 `Holds F A ξ` 与 `ξ ∉ A` 的证明，就可满足对角公式。这些数据被封装在公式的有界存在量化所带的命题截断中。
<!--ja-->
逆に、`A ∈ 𝒫 κ`、グラフについての事実 `Holds F A ξ`、および `ξ ∉ A` の証明が与えられれば、対角論理式を充足できる。これらのデータは、論理式の有界存在量化に伴う命題的切り詰めの中にまとめられる。
<!--/-->

```agda
      φD-in : (ξ A : SL.S) → ⟨ fst A ∈ fst (𝒫 κ) ⟩ → Holds F A ξ
            → (⟨ fst ξ ∈ fst A ⟩ → ⊥₀) → ⟨ (ξ ∷ []) ⊨ φD ⟩
      φD-in ξ A mA h n =
        ∣ A , (mA , (transport (sym (a1 ξ A)) h , (λ k → lift (n k)))) ∣₁
```

<!--en-->
The diagonal set is separated out of `κ` by the bounded formula.
<!--zh-->
对角集合由该有界公式从 `κ` 中分离而出。
<!--ja-->
対角の集合は、この有界の論理式によって `κ` から分出される。
<!--/-->

```agda
    D₀ : SL.S
    D₀ = fst (fst (hasSeparationL κ φD))
```

<!--en-->
Its membership specification is the separation's own reading: membership in the diagonal set is membership in `κ` conjoined with satisfaction of the diagonal formula.
<!--zh-->
其隶属规格即分离自身的读法：属于对角集合，当且仅当属于 `κ` 且满足对角公式。
<!--ja-->
その所属の仕様は、分出自身の読みである。対角の集合に属するとは、`κ` に属し、かつ対角の論理式を充足することの連言である。
<!--/-->

```agda
    D₀-spec : (ξ : SL.S) → (ξ SL.∈ˢ D₀) ≡ ((ξ SL.∈ˢ κ) ⊓ ((ξ ∷ []) ⊨ φD))
    D₀-spec = snd (fst (hasSeparationL κ φD))
```

<!--en-->
The diagonal set is a member of the internal power set: the pointwise reading proves that every model element of it belongs to `κ`.
<!--zh-->
对角集合是内部幂集的成员：逐点读取证明其每个模型元素都属于 `κ`。
<!--ja-->
対角の集合は内部の冪集合の要素である。逐点の読みが、そのすべてのモデルの要素が `κ` に属することを証明する。
<!--/-->

```agda
    D₀∈𝒫κ : ⟨ fst D₀ ∈ fst (𝒫 κ) ⟩
    D₀∈𝒫κ = into-power zf κ D₀ (λ z h → fst (subst ⟨_⟩ (D₀-spec z) h))
```

<!--en-->
To derive the contradiction, suppose the graph assigns the diagonal set `D₀` some value `ξ`. The range clause will show `ξ ∈ κ`, while the definition of `D₀` will force both `ξ ∈ D₀` and `ξ ∉ D₀`.
<!--zh-->
为导出矛盾，假设图把对角集合 `D₀` 映到某个值 `ξ`。值域条款将给出 `ξ ∈ κ`，而 `D₀` 的定义将同时迫使 `ξ ∈ D₀` 与 `ξ ∉ D₀`。
<!--ja-->
矛盾を導くため、グラフが対角集合 `D₀` にある値 `ξ` を割り当てると仮定する。値域の条項から `ξ ∈ κ` が得られ、`D₀` の定義から `ξ ∈ D₀` と `ξ ∉ D₀` の両方が強制される。
<!--/-->

```agda
    absurd : Σ[ ξ ∈ SL.S ] Holds F D₀ ξ → ⊥₀
    absurd (ξ , h₀) = out inside
      where
```

<!--en-->
Assume `ξ ∈ D₀`. The diagonal formula then supplies, under truncation, a set `A ∈ 𝒫 κ` such that `F` sends `A` to `ξ` and `ξ ∉ A`. Since `F` also sends `D₀` to `ξ`, injectivity identifies the underlying sets of `A` and `D₀`; transporting the assumed membership into `A` contradicts `ξ ∉ A`.
<!--zh-->
假设 `ξ ∈ D₀`。对角公式便在命题截断下给出集合 `A ∈ 𝒫 κ`，使 `F` 把 `A` 映到 `ξ`，且 `ξ ∉ A`。由于 `F` 也把 `D₀` 映到 `ξ`，单射性认同 `A` 与 `D₀` 的底层集合；把所假设的隶属搬运到 `A` 中，便与 `ξ ∉ A` 矛盾。
<!--ja-->
`ξ ∈ D₀` と仮定する。対角論理式は、命題的切り詰めのもとで、`F` が `A` を `ξ` へ送り、かつ `ξ ∉ A` となる集合 `A ∈ 𝒫 κ` を与える。`F` は `D₀` も `ξ` へ送るので、単射性により `A` と `D₀` の底の集合が同一視される。仮定した所属を `A` へ輸送すると、`ξ ∉ A` と矛盾する。
<!--/-->

```agda
      out : ⟨ fst ξ ∈ fst D₀ ⟩ → ⊥₀
      out hm = rec₁ isProp⊥
        (λ { (A , _ , hA , n) →
          n (subst (λ w → ⟨ fst ξ ∈ w ⟩) (injF ξ D₀ A h₀ hA) hm) })
        (φD-out ξ (snd (subst ⟨_⟩ (D₀-spec ξ) hm)))
```

<!--en-->
The converse direction uses that refutation as data. The range clause gives `ξ ∈ κ`, and choosing `A = D₀` witnesses the diagonal formula because `F` sends `D₀` to `ξ` and the preceding function proves `ξ ∉ D₀`. Separation therefore yields `ξ ∈ D₀`, to which the refutation is applied.
<!--zh-->
反方向把刚才的反驳作为数据使用。值域条款给出 `ξ ∈ κ`；取 `A = D₀`，再用 `F` 把 `D₀` 映到 `ξ` 以及前一步证明的 `ξ ∉ D₀`，即可见证对角公式。分离规格于是给出 `ξ ∈ D₀`，再把反驳应用于它便得到矛盾。
<!--ja-->
逆向きでは、先ほどの反証をデータとして用いる。値域の条項から `ξ ∈ κ` が得られる。`A = D₀` と取り、`F` が `D₀` を `ξ` へ送ることと、前段で証明した `ξ ∉ D₀` を使えば、対角論理式を証せる。したがって分出の仕様から `ξ ∈ D₀` が得られ、これにその反証を適用して矛盾を得る。
<!--/-->

```agda
      inside : ⟨ fst ξ ∈ fst D₀ ⟩
      inside = subst ⟨_⟩ (sym (D₀-spec ξ))
        (ranF D₀ ξ h₀ , φD-in ξ D₀ D₀∈𝒫κ h₀ out)
```
</div>
</details>

<!--en-->
The two halves refute any internal coded injection from the power set into `κ`: the injection is eliminated into a graph, and the graph's value at the diagonal set is eliminated into the contradiction. The target is the empty type, so both eliminations are legitimate.
<!--zh-->
两半反驳任何从幂集到 `κ` 的内部编码单射：该单射被消去为图，而图在对角集处的值被消去为矛盾。目标是空类型，故两次消去都合法。
<!--ja-->
この二つの半分が、冪集合から `κ` への内部の符号化された単射をすべて反証する。単射はグラフへ消去され、グラフの対角の集合における値が矛盾へ消去される。目標が空の型なので、どちらの消去も正当である。
<!--/-->

```agda
  no-inj : InjL (𝒫 κ) κ → ⊥₀
  no-inj = rec₁ isProp⊥ step
    where
    step : Σ[ F ∈ SL.S ] InjCode F (𝒫 κ) κ → ⊥₀
    step (F , code) = rec₁ isProp⊥ D.absurd (D.valF D.D₀ D.D₀∈𝒫κ)
```

<!--en-->
For the chosen graph `F`, the diagonal construction supplies both the internal subset `D₀` and the proof that no value can be assigned to it. Totality assigns such a value nevertheless, completing the contradiction for this graph.
<!--zh-->
对所选图 `F`，对角构造同时给出内部子集 `D₀`，并证明图不可能为它指派任何值。然而全域性仍为它指派一个值，于是这张图导致矛盾。
<!--ja-->
選んだグラフ `F` に対して、対角構成は内部部分集合 `D₀` と、そこに値を割り当てることが不可能であるという証明を与える。それでも全域性は値を割り当てるので、このグラフについて矛盾が完成する。
<!--/-->

```agda
      where module D = Diag F code
```
</div>
</details>

<!--en-->
## Ordering the power set and comparing its order type
<!--zh-->
## 良序化幂集并比较其序型
<!--ja-->
## 冪集合を整列してその順序型を比較する
<!--/-->

<!--en-->
For the reverse comparison, fix a successor cardinal `δ` of `κ` and one particular graph `G` coding the assumed injection `𝒫 κ ↪ δ`. This graph is available only inside a local branch obtained from the propositional truncation; the final result will again be an `InjL` statement.
<!--zh-->
为构造反方向比较，固定 `κ` 的后继基数 `δ`，并固定一张编码所假设单射 `𝒫 κ ↪ δ` 的具体图 `G`。这张图只在从命题截断取得的局部分支内可用；最终结果仍将是一个 `InjL` 陈述。
<!--ja-->
逆向きの比較を構成するため、`κ` の後続基数 `δ` と、仮定された単射 `𝒫 κ ↪ δ` を符号化する特定のグラフ `G` を固定する。このグラフは命題的切り詰めから得られる局所的な分岐の中でだけ利用でき、最終結果は再び `InjL` の主張になる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Build (zf : ModelL.isZFModel) (κ δ : SL.S) (sc : SuccCardL δ κ)
             (G : SL.S)
             (code : InjCode G (ModelL.isZFModel.𝒫 zf κ) δ) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The source `𝒫 κ` is again the internal power set determined by the fixed ZF model. The construction never replaces it by the ambient power set of the underlying set.
<!--zh-->
这里的源 `𝒫 κ` 仍是固定 ZF 模型所确定的内部幂集。构造始终不会把它换成底层集合的外围幂集。
<!--ja-->
ここで始域となる `𝒫 κ` も、固定した ZF モデルが定める内部の冪集合である。この構成で、それを底の集合の周囲の冪集合に置き換えることはない。
<!--/-->

```agda
  open ModelL.isZFModel zf using ( 𝒫 )
```

<!--en-->
The ordinality of the successor is the first component of its record.
<!--zh-->
后继的序数性是其记录的第一分量。
<!--ja-->
後続の順序数性は、その記録の最初の成分である。
<!--/-->

```agda
  ordδ : IsOrd (fst δ)
  ordδ = sc .fst
```

<!--en-->
The power set is named as the source of the comparison.
<!--zh-->
幂集被命名为比较的源。
<!--ja-->
冪集合が、比較の源として名付けられる。
<!--/-->

```agda
  P : SL.S
  P = 𝒫 κ
```

<!--en-->
The environment of the graph pairs the graph with the power set.
<!--zh-->
图的环境把图与幂集配对。
<!--ja-->
グラフの環境は、グラフと冪集合を対にする。
<!--/-->

```agda
  γG : SL.S ^ 2
  γG = G ∷ P ∷ []
```

<!--en-->
The range clause of the coding says every value lands in the successor.
<!--zh-->
编码的值域条款说：每个值都落在后继中。
<!--ja-->
符号の値域の条項は、すべての値が後続の中に着地することを言う。
<!--/-->

```agda
  ranG : (x y : SL.S) → Holds G x y → ⟨ fst y ∈ fst δ ⟩
  ranG = code .snd .snd .snd
```

<!--en-->
Single-valuedness concerns one fixed input: if `G` records both `G(x)=y` and `G(x)=y'`, then the underlying sets of `y` and `y'` are equal. This uniqueness will make the type of possible values of `x` a proposition.
<!--zh-->
单值性针对同一个固定输入：若 `G` 同时记录 `G(x)=y` 与 `G(x)=y'`，则 `y` 与 `y'` 的底层集合相等。这一唯一性将使 `x` 的可能值所组成的类型成为命题。
<!--ja-->
一価性は一つの固定した入力についての性質である。`G` が `G(x)=y` と `G(x)=y'` の両方を記録するなら、`y` と `y'` の底の集合は等しくなる。この一意性により、`x` の可能な値からなる型が命題になる。
<!--/-->

```agda
  svG : (x y y' : SL.S) → Holds G x y → Holds G x y' → fst y ≡ fst y'
  svG = svAt-out zero γG (code .fst)
```

<!--en-->
Totality gives a propositionally truncated value witness for every `x ∈ P`. It does not yet choose a value. Shortly, single-valuedness will show that the fibre of possible values is a proposition, which permits elimination of this truncation and yields a locally readable value.
<!--zh-->
全域性为每个 `x ∈ P` 给出经过命题截断的值见证，此时尚未选定一个值。稍后，单值性将证明可能值组成的纤维是命题，从而可以从这层命题截断消去并在局部读出值。
<!--ja-->
全域性は、各 `x ∈ P` に対して命題的に切り詰められた値の証人を与える。この時点では、値はまだ選ばれていない。すぐ後で一価性から可能な値のファイバーが命題であることを示し、この切り詰めから消去して局所的に値を読み出す。
<!--/-->

```agda
  valG : (x : SL.S) → ⟨ fst x ∈ fst P ⟩ → ∥ Σ[ y ∈ SL.S ] Holds G x y ∥₁
  valG = domAt-in zero (suc zero) γG (code .snd .fst)
```

<!--en-->
The injectivity clause for the coded injection `G` recovers a source member from its value: if two source members have the same recorded value, then their underlying sets are equal.
<!--zh-->
编码单射 `G` 的单射性子句由值恢复源端成员：若两个源端成员具有相同的记录值，则它们的底层集合相等。
<!--ja-->
符号化された単射 `G` の単射性の条項は、値から始域の要素を復元する。二つの始域の要素が同じ記録値をもつなら、それらの底の集合は等しくなる。
<!--/-->

```agda
  injG : (y x x' : SL.S) → Holds G x y → Holds G x' y → fst x ≡ fst x'
  injG = injAt-out zero γG (code .snd .snd .fst)
```

<!--en-->
For a fixed input `x`, any two graph values of `G` must coincide by single-valuedness. Since constructibility proofs are propositions, equality of the underlying values lifts to equality of the complete witnesses. Thus the fibre of possible values is itself a proposition.
<!--zh-->
固定输入 `x` 后，`G` 的任意两个图取值都因单值性而相等。由于可构造性证明是命题，底层取值的相等可提升为完整见证的相等。因此，所有可能取值组成的纤维本身也是命题。
<!--ja-->
入力 `x` を固定すると、`G` のグラフが与える任意の二つの値は、一価性によって等しくなる。構成可能性の証明は命題なので、基礎にある値の等しさは証人全体の等しさへ持ち上がる。したがって、可能な値からなるファイバー自身が命題である。
<!--/-->

```agda
  isPropVal : (x : SL.S) → isProp (Σ[ y ∈ SL.S ] Holds G x y)
  isPropVal x (y , h) (y' , h') =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst G)) (S≡ (svG x y y' h h'))
```

<!--en-->
The domain clause initially supplies a value of `G` only under propositional truncation. The preceding uniqueness result makes the target fibre proposition-valued, so the truncation may be eliminated and the unique value used in the rest of the construction. This step uses uniqueness, not a general choice principle.
<!--zh-->
定义域子句起初只在命题截断下给出 `G` 的取值。上一步的唯一性使目标纤维取值于命题，因此可以消去截断，并在后续构造中使用这个唯一取值。这一步依赖唯一性，而不是一般的选择原理。
<!--ja-->
定義域の条項が最初に与える `G` の値は、命題的切り詰めの内側にある。直前に示した一意性によって行き先のファイバーは命題値になるので、切り詰めを除去し、その一意な値を以後の構成で使える。この段階で用いるのは一意性であり、一般の選択原理ではない。
<!--/-->

```agda
  val : (x : SL.S) → ⟨ fst x ∈ fst P ⟩ → Σ[ y ∈ SL.S ] Holds G x y
  val x m = rec₁ (isPropVal x) (λ z → z) (valG x m)
```

<!--en-->
Define `a` to precede `b` when they both belong to `P` and there merely exist graph values `x` and `y` with `G(a)=x`, `G(b)=y` and `x∈y`. Propositional truncation records that suitable images exist without retaining a choice of witnesses.
<!--zh-->
定义 `a` 先于 `b`，意思是二者都属于 `P`，并且在命题截断下存在图取值 `x` 与 `y`，满足 `G(a)=x`、`G(b)=y` 及 `x∈y`。命题截断只记录合适的像存在，而不保留对见证的选取。
<!--ja-->
`a` が `b` に先行するとは、両者が `P` に属し、`G(a)=x`、`G(b)=y`、`x∈y` を満たすグラフの値 `x` と `y` が命題的切り詰めのもとで存在することだと定める。命題的切り詰めは、適切な像が存在することだけを記録し、証人の選択は保持しない。
<!--/-->

```agda
  Read : SL.S → SL.S → Type (ℓ-suc ℓ)
  Read a b = ∥ Σ[ x ∈ SL.S ] Σ[ y ∈ SL.S ]
               ( ⟨ fst a ∈ fst P ⟩ × ⟨ fst b ∈ fst P ⟩
               × Holds G a x × Holds G b y × ⟨ fst x ∈ fst y ⟩ ) ∥₁
```

<!--en-->
To express this relation in the object language, the environment places `A`, `B` and their candidate images `x`, `y` where the two applications of `G` can read them. This lets one formula speak simultaneously about `G(A)=x`, `G(B)=y` and `x∈y`.
<!--zh-->
为了在对象语言中表达这条关系，环境把 `A`、`B` 及其候选像 `x`、`y` 放在两次应用 `G` 都能读取的位置。这样，同一条公式便能同时陈述 `G(A)=x`、`G(B)=y` 与 `x∈y`。
<!--ja-->
この関係を対象言語で表すため、環境は `A`、`B` と、その像の候補 `x`、`y` を、`G` の二つの適用から読める位置に置く。これにより、一つの論理式で `G(A)=x`、`G(B)=y`、`x∈y` を同時に述べられる。
<!--/-->

```agda
  private
    env5 : SL.S → SL.S → SL.S → SL.S → SL.S → SL.S ^ 5
    env5 p A B x y = y ∷ x ∷ B ∷ A ∷ p ∷ []
```

<!--en-->
The first adequacy equality identifies the encoded application with the graph statement `Holds G A x`. It is the bridge between the object-language formula and the assertion that `x` is the value assigned to `A` by the coded graph.
<!--zh-->
第一条充分性等式把编码后的应用认同为图陈述 `Holds G A x`。它在对象语言公式与「编码图把 `A` 送到 `x`」这一断言之间建立桥梁。
<!--ja-->
最初の妥当性の等式は、符号化された適用をグラフの主張 `Holds G A x` と同一視する。これは、対象言語の論理式と、符号化されたグラフが `A` を `x` へ送るという主張を結ぶ橋である。
<!--/-->

```agda
    b1 : (p A B x y : SL.S)
       → ⟨ env5 p A B x y ⊨ appC G (suc (suc (suc zero))) (suc zero) ⟩
       ≡ Holds G A x
    b1 p A B x y = cong ⟨_⟩
      (appC-adequate G (suc (suc (suc zero))) (suc zero) (env5 p A B x y))
```

<!--en-->
The second adequacy equality performs the same translation for `B` and `y`. Together the two equalities allow the pullback relation to be proved either through formula satisfaction or through ordinary statements about the graph of `G`.
<!--zh-->
第二条充分性等式对 `B` 与 `y` 作同样的转换。两条等式合在一起，使拉回关系既可通过公式满足来证明，也可通过关于 `G` 的图的通常陈述来证明。
<!--ja-->
二つ目の妥当性の等式は、`B` と `y` について同じ変換を行う。二つの等式を合わせることで、引き戻した関係を、論理式の充足からも、`G` のグラフについての通常の主張からも証明できる。
<!--/-->

```agda
    b2 : (p A B x y : SL.S)
       → ⟨ env5 p A B x y ⊨ appC G (suc (suc zero)) zero ⟩ ≡ Holds G B y
    b2 p A B x y = cong ⟨_⟩
      (appC-adequate G (suc (suc zero)) zero (env5 p A B x y))
```

<!--en-->
The defining formula first restricts both endpoints to the internal power set, then quantifies over two model elements that serve as their images. Together with the two application atoms and the membership comparison between the images, this gives a first-order description of a relation on `P`; the relation construction represents that description by a set in `L`.
<!--zh-->
定义公式先把两个端点限制在内部幂集内，再量化两个模型元素作为它们的像。两条应用原子与两个像之间的隶属比较合在一起，给出 `P` 上一条关系的一阶描述；关系构造随后把这一描述表示为 `L` 中的集合。
<!--ja-->
定義する論理式は、まず二つの端点を内部冪集合に制限し、続いてそれらの像となる二つのモデル要素を量化する。二つの適用のアトムと、像の間の所属比較を合わせることで、`P` 上の関係の一階的な記述が得られ、関係の構成はその記述を `L` の集合として表す。
<!--/-->

```agda
  private
    opaque
      φR : Formula SL.S 3
      φR = (var (suc zero) ∈̇ con P) ∧̇ ((var zero ∈̇ con P) ∧̇ ∃̇ (∃̇
        (appC G (suc (suc (suc zero))) (suc zero)
```

<!--en-->
Inside the two existential binders, the remaining clauses say that the witnesses are respectively the `G`-images of the endpoints and that the first image belongs to the second. This is precisely the membership order on `δ` pulled back along `G`.
<!--zh-->
在两层存在绑定之内，其余子句分别断言两个见证是两端点的 `G` 像，并且第一像属于第二像。这正是沿 `G` 拉回的 `δ` 上的隶属次序。
<!--ja-->
二つの存在束縛の内側で、残りの条項は、二つの証人がそれぞれ端点の `G` による像であり、最初の像が二つ目の像に属することを述べる。これはまさに、`δ` 上の所属順序を `G` に沿って引き戻したものである。
<!--/-->

```agda
          ∧̇ (appC G (suc (suc zero)) zero ∧̇ (var (suc zero) ∈̇ var zero)))))
```

<!--en-->
Reading the formula outward first retains the two image witnesses under propositional truncation. The two adequacy equalities then turn the encoded applications into graph facts, yielding exactly the semantic data in `Read`: endpoint membership, the two values and their membership comparison.
<!--zh-->
向外读取公式时，首先把两个像的见证保留在命题截断之下。随后，两条充分性等式把编码应用转换成图事实，恰好得到 `Read` 中的语义数据：端点隶属、两个取值及二者的隶属比较。
<!--ja-->
論理式を外向きに読むと、まず二つの像の証人が命題的切り詰めのもとに保たれる。次に、二つの妥当性の等式が符号化された適用をグラフの事実へ変え、`Read` の意味論的データ、すなわち端点の所属、二つの値、その間の所属比較をちょうど与える。
<!--/-->

```agda
      read : (a b p : SL.S) → ⟨ (b ∷ a ∷ p ∷ []) ⊨ φR ⟩ → Read a b
      read a b p (ma , mb , h) = rec₁ squash₁
        (λ { (x , hx) → map₁ (λ { (y , ha , hb , hxy) → x , y , ma , mb
          , transport (b1 p a b x y) ha , transport (b2 p a b x y) hb , hxy }) hx }) h
```

<!--en-->
The inward reading transports each host-side fact back through the reversed adequacy equations, filling the existential and application slots to reconstruct the formula satisfaction.
<!--zh-->
向内读法沿反向的充分性等式把每条宿主侧事实运回，填充存在与应用槽位以重建公式满足。
<!--ja-->
内向きの読み出しは、逆向きの妥当性の等式に沿って、それぞれのホスト側の事実を運び戻し、存在量化子と適用の枠を満たして、論理式の充足を再構築する。
<!--/-->

```agda
      fill : (a b p : SL.S) → Read a b → ⟨ (b ∷ a ∷ p ∷ []) ⊨ φR ⟩
      fill a b p = rec₁ (snd ((b ∷ a ∷ p ∷ []) ⊨ φR))
        (λ { (x , y , ma , mb , ha , hb , hxy) → ma , mb , ∣ x , ∣ y
          , transport (sym (b1 p a b x y)) ha
          , transport (sym (b2 p a b x y)) hb , hxy ∣₁ ∣₁ })
```

<!--en-->
The bounded-relation construction now turns this definable predicate into an actual relation set in `L`. The two readings proved above ensure that membership in the coded relation has exactly the intended truncated content `Read`.
<!--zh-->
有界关系构造现在把这个可定义谓词化为 `L` 中实际的关系集合。上面证明的两个方向保证，编码关系中的隶属恰好具有 `Read` 所表达的命题截断内容。
<!--ja-->
有界関係の構成は、この定義可能な述語を `L` にある実際の関係集合へ変える。上で示した二方向の読み替えにより、符号化された関係への所属は、`Read` が表す命題的に切り詰められた内容とちょうど一致する。
<!--/-->

```agda
    module Pullback = Relation P P φR (λ a b → Read a b , squash₁) read fill
```

<!--en-->
For the converse reading, the two adequacy equalities turn the graph facts `Holds G A x` and `Holds G B y` back into application atoms. Packaging `x` and `y` as the two existential witnesses then reconstructs satisfaction of the defining formula.
<!--zh-->
在反方向读取中，两条充分性等式把图事实 `Holds G A x` 与 `Holds G B y` 转回应用原子。再把 `x` 与 `y` 封装为两层存在量词的见证，便重建定义公式的满足。
<!--ja-->
逆向きに読むときは、二つの妥当性の等式によって、グラフの事実 `Holds G A x` と `Holds G B y` を適用のアトムへ戻す。続いて `x` と `y` を二つの存在量化の証人としてまとめると、定義論理式の充足が再構成される。
<!--/-->

```agda
  R : SL.S
  R = Pullback.rel
```

<!--en-->
An entry of `R` can be read back as the truncated data defining the pullback: the two endpoints lie in the power set, they have `G`-images, and the first image belongs to the second.
<!--zh-->
从 `R` 的一条关系项可以读回定义拉回关系的命题截断数据：两个端点属于幂集，它们具有 `G` 像，并且第一像属于第二像。
<!--ja-->
`R` の一つの関係項から、引き戻しを定義する命題的に切り詰められたデータを読み戻せる。すなわち、二つの端点は冪集合に属し、それぞれ `G` による像をもち、最初の像は二つ目の像に属する。
<!--/-->

```agda
  R-out : (a b : SL.S) → Holds R a b → Read a b
  R-out = Pullback.pair-out
```

<!--en-->
The inward reading constructs the relation entry from the two endpoint memberships, the two `G`-image facts and the membership between the images.
<!--zh-->
向内读式由两个端点隶属、两条 `G` 像事实及二像间的隶属构造关系条目。
<!--ja-->
内向きの読み出しは、二つの端点の所属、`G` の像の二つの事実、そして像の間の所属から、関係の項目を作る。
<!--/-->

```agda
  R-in : (a b x y : SL.S) → ⟨ fst a ∈ fst P ⟩ → ⟨ fst b ∈ fst P ⟩
       → Holds G a x → Holds G b y → ⟨ fst x ∈ fst y ⟩ → Holds R a b
  R-in a b x y ma mb ha hb hxy = Pullback.into a b ma mb ∣ x , y , ma , mb , ha , hb , hxy ∣₁
```

<!--en-->
Every entry of the coded relation has endpoints in `P`. The proof reads its truncated witnesses and discards the image data, retaining only the two endpoint-membership facts; this elimination is allowed because their product is a proposition.
<!--zh-->
编码关系的每条关系项，其两个端点都属于 `P`。证明读取命题截断下的见证，舍去像的数据，只保留两条端点隶属事实；由于二者的积是命题，这样消去命题截断是允许的。
<!--ja-->
符号化された関係の各項目では、二つの端点がとも `P` に属する。証明は命題的切り詰めのもとにある証人を読み、像のデータを捨てて、二つの端点の所属だけを残す。その積は命題なので、この切り詰めの除去が許される。
<!--/-->

```agda
  Rsub : (a b : SL.S) → Holds R a b
       → ⟨ fst a ∈ fst P ⟩ × ⟨ fst b ∈ fst P ⟩
  Rsub a b h = rec₁
    (isProp× (snd (fst a ∈ fst P)) (snd (fst b ∈ fst P)))
    (λ { (_ , _ , ma , mb , _) → ma , mb })
```

<!--en-->
Applying the outward reading supplies the witnesses needed by the extraction. Eliminating their truncation is legitimate because the conclusion, the pair of endpoint-membership propositions, is itself a proposition.
<!--zh-->
应用向外读法即可取得提取所需的见证。由于结论是两个端点隶属命题组成的命题，对这些见证的命题截断作消去是合法的。
<!--ja-->
外向きの読み出しを適用すると、抽出に必要な証人が得られる。その切り詰めを除去できるのは、結論である二つの端点の所属命題の組もまた命題だからである。
<!--/-->

```agda
    (R-out a b h)
```

<!--en-->
The order-type construction replaces members of `P` by a small presented domain `Dom`. Its relation `a ≺ b` records exactly the coded fact that the represented members are related by `R`; the following proof can therefore study the pullback order on indices and later collapse it.
<!--zh-->
序型构造用一个小的呈现域 `Dom` 表示 `P` 的成员。关系 `a ≺ b` 恰好记录相应成员被 `R` 关联这一编码事实；因此，后续证明可以在索引上研究拉回序，并最终将其塌缩。
<!--ja-->
順序型の構成は、`P` の要素を小さい提示領域 `Dom` で表す。関係 `a ≺ b` は、表された要素どうしが `R` で関係づけられるという符号化された事実をちょうど記録する。そこで以下では、添字上の引き戻し順序を調べ、のちにそれを崩壊できる。
<!--/-->

```agda
  module OT = Code P R Rsub
    using ( Dom; Dom≡; toDom; up; up-mem; up-toDom; ↪; _≺_; ≺-in; ≺-out
          ; module Conjuncts )
```

<!--en-->
For an index `b` in this domain, let `v b` be the unique value that `G` assigns to the represented member of `P`. The next steps show that these representatives are ordinals below `δ`.
<!--zh-->
对这个域中的索引 `b`，令 `v b` 为 `G` 赋给其所表示的 `P` 成员的唯一取值。接下来将证明这些代表都是 `δ` 以下的序数。
<!--ja-->
この領域の添字 `b` に対し、`v b` を、`b` が表す `P` の要素へ `G` が割り当てる一意な値とする。次に、これらの代表が `δ` より下の順序数であることを示す。
<!--/-->

```agda
  v : OT.Dom → SL.S
  v b = fst (val (OT.up b) (OT.up-mem b))
```

<!--en-->
The second component of the chosen value records the corresponding graph fact `Holds G (up b) (v b)`. It will connect comparisons among the representatives with entries of the pulled-back relation.
<!--zh-->
所取值的第二分量记录相应的图事实 `Holds G (up b) (v b)`。它将把代表之间的比较与拉回关系中的关系项连接起来。
<!--ja-->
選んだ値の第二成分は、対応するグラフの事実 `Holds G (up b) (v b)` を記録する。これは、代表どうしの比較を引き戻した関係の項目へ結びつける。
<!--/-->

```agda
  v-holds : (b : OT.Dom) → Holds G (OT.up b) (v b)
  v-holds b = snd (val (OT.up b) (OT.up-mem b))
```

<!--en-->
Every value of `G` belongs to the successor cardinal `δ`, by the range clause of the injection code. This places all representatives inside one ordinal, where membership comparisons and ordinal trichotomy are available.
<!--zh-->
由单射码的值域子句，`G` 的每个取值都属于后继基数 `δ`。因此，所有代表都位于同一个序数内，可以在其中使用隶属比较与序数三歧性。
<!--ja-->
単射の符号の値域の条項により、`G` の各値は後続基数 `δ` に属する。したがって、すべての代表が一つの順序数の中にあり、そこで所属による比較と順序数の三分法を用いられる。
<!--/-->

```agda
  v∈δ : (b : OT.Dom) → ⟨ fst (v b) ∈ fst δ ⟩
  v∈δ b = ranG (OT.up b) (v b) (v-holds b)
```

<!--en-->
Each `G`-value is an ordinal, inherited from the ordinality of `δ`.
<!--zh-->
每个 `G` 取值是序数，承继自 `δ` 的序数性。
<!--ja-->
それぞれの `G` の値は順序数である。`δ` の順序数性から受け継がれる。
<!--/-->

```agda
  ord-v : (b : OT.Dom) → IsOrd (fst (v b))
  ord-v b = mem-ord {A = fst δ} ordδ (fst (v b)) (v∈δ b)
```

<!--en-->
The forward comparison turns a predecessor step in the pulled-back relation into membership between the two representative ordinals. Reading the relation entry gives two possible image witnesses; single-valuedness of `G` identifies them with the fixed values `v a` and `v b`.
<!--zh-->
向前比较把拉回关系中的一步前驱关系转化为两个代表序数之间的隶属。读取关系条目会得到两个像见证；`G` 的单值性把它们分别认同为固定取值 `v a` 与 `v b`。
<!--ja-->
前向きの比較は、引き戻された関係の一つの先行段階を、二つの代表順序数の間の所属へ移す。関係の項目を読むと二つの像の証人が得られ、`G` の一価性によって、それぞれが固定した値 `v a` と `v b` に同一視される。
<!--/-->

```agda
  ≺-fwd : (a b : OT.Dom) → a OT.≺ b → ⟨ fst (v a) ∈ fst (v b) ⟩
  ≺-fwd a b k = rec₁ (snd (fst (v a) ∈ fst (v b)))
    (λ { (x , y , _ , _ , ha , hb , hxy) →
      subst2 (λ s t → ⟨ s ∈ t ⟩)
        (svG (OT.up a) x (v a) ha (v-holds a))
```

<!--en-->
The two single-valuedness equalities replace the image witnesses read from `R` by the fixed representatives `v a` and `v b`. Transporting `x∈y` along both equalities yields the required comparison `v a ∈ v b`.
<!--zh-->
两条单值性等式把从 `R` 读出的像见证分别换成固定代表 `v a` 与 `v b`。沿这两条等式搬运 `x∈y`，便得到所需比较 `v a ∈ v b`。
<!--ja-->
二つの一価性の等式により、`R` から読み出した像の証人を、固定した代表 `v a` と `v b` にそれぞれ置き換える。`x∈y` を両方の等式に沿って輸送すると、必要な比較 `v a ∈ v b` が得られる。
<!--/-->

```agda
        (svG (OT.up b) y (v b) hb (v-holds b)) hxy })
    (R-out (OT.up a) (OT.up b) (OT.≺-out a b k))
```

<!--en-->
The backward comparison constructs the pulled-back relation from the membership of the two representative ordinals, by reintroducing the two graph facts and the membership between their images.
<!--zh-->
向后比较由两个代表序数的隶属重新引入两条图事实及二像间的隶属，构造拉回关系。
<!--ja-->
後ろ向きの比較は、二つの代表の順序数の所属から、引き戻された関係を構成する。二つのグラフの事実と、像の間の所属を、改めて導入することによるものである。
<!--/-->

```agda
  ≺-bwd : (a b : OT.Dom) → ⟨ fst (v a) ∈ fst (v b) ⟩ → a OT.≺ b
  ≺-bwd a b h = OT.≺-in a b
    (R-in (OT.up a) (OT.up b) (v a) (v b)
      (OT.up-mem a) (OT.up-mem b) (v-holds a) (v-holds b) h)
```

<!--en-->
To prove well-foundedness, fix a hierarchy element `u` and consider every domain index whose representative value is `u`. The predicate `Pacc u` asks that each such index be accessible in the pullback order, setting up induction on ambient membership.
<!--zh-->
为证明良基性，固定一个层级元素 `u`，并考察代表值为 `u` 的所有域索引。谓词 `Pacc u` 要求每个这样的索引在拉回序中可达，从而为对外围隶属关系作归纳做好准备。
<!--ja-->
整礎性を示すため、階層の要素 `u` を固定し、代表の値が `u` であるすべての領域の添字を考える。述語 `Pacc u` は、その各添字が引き戻し順序でアクセス可能であることを要求し、周囲の所属関係に関する帰納を準備する。
<!--/-->

```agda
  private
    Pacc : V ℓ → Type (ℓ-suc ℓ)
    Pacc u = (b : OT.Dom) → fst (v b) ≡ u → Acc OT._≺_ b
```

<!--en-->
The induction step constructs accessibility for a predecessor whose representative ordinal lies strictly below `u`: the forward comparison carries the membership to the representative, and the induction hypothesis supplies accessibility there.
<!--zh-->
归纳步为代表序数严格低于 `u` 的前驱构造可达性：向前比较把隶属运到代表，归纳假设在该处供给可达性。
<!--ja-->
帰納のステップは、代表の順序数が `u` より厳密に下にある先行者のアクセス可能性を構成する。前向きの比較が所属を代表へ運び、帰納の仮定がそこでアクセス可能性を供給する。
<!--/-->

```agda
    accStep : (u : V ℓ) → (∀ u' → ⟨ u' ∈ˢ u ⟩ → Pacc u') → Pacc u
    accStep u IH b e = acc (λ a k →
      IH (fst (v a)) (subst (λ w → ⟨ fst (v a) ∈ˢ w ⟩) e (≺-fwd a b k))
         a refl)
```

<!--en-->
Accessibility at every hierarchy element is proved by the regularity induction of the ambient hierarchy, which is the well-foundedness of its membership.
<!--zh-->
每个层级元素处的可达性由环境层级中正则公理所给的良基归纳证明，后者即其隶属的良基性。
<!--ja-->
すべての階層の要素でのアクセス可能性は、周囲の階層の正則性の帰納で証明される。それは、所属の整礎性である。
<!--/-->

```agda
    accAt : (u : V ℓ) → Pacc u
    accAt = WF.WFI.induction regularityV {P = Pacc} accStep
```

<!--en-->
Well-foundedness of the pulled-back order is assembled from the accessibility at each representative ordinal.
<!--zh-->
拉回序的良基性由每个代表序数处的可达性装配而成。
<!--ja-->
引き戻された順序の整礎性は、代表の順序数ごとのアクセス可能性から組み立てられる。
<!--/-->

```agda
  wf : WellFounded OT._≺_
  wf b = accAt (fst (v b)) b refl
```

<!--en-->
Transitivity of the pulled-back order composes the two forward comparisons through the transitivity of the ordinal `δ` applied to the two representative memberships.
<!--zh-->
拉回序的传递性复合两条向前比较，经由序数 `δ` 的传递性施于两条代表隶属。
<!--ja-->
引き戻された順序の推移性は、二つの前向きの比較を、順序数 `δ` の推移性を二つの代表の所属に適用して合成する。
<!--/-->

```agda
  ≺-trans : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
  ≺-trans {a} {b} {c} k k' = ≺-bwd a c
    (ordδ .snd (fst (v c)) (v∈δ c) (≺-fwd a b k) (≺-fwd b c k'))
```

<!--en-->
Trichotomy of the pulled-back order is transported from ordinal trichotomy for the representative values in `δ`: for any `a` and `b`, either `v a ∈ v b`, the two values are equal, or `v b ∈ v a`.
<!--zh-->
拉回序的三歧性来自 `δ` 中代表取值的序数三歧性：对任意 `a` 与 `b`，或者 `v a ∈ v b`，或者两个取值相等，或者 `v b ∈ v a`。
<!--ja-->
引き戻された順序の三分法は、`δ` にある代表値についての順序数の三分法から移される。任意の `a` と `b` に対して、`v a ∈ v b`、二つの値が等しい、`v b ∈ v a` のいずれかが成り立つ。
<!--/-->

```agda
  tri : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  tri a b = go (ord-tri (fst (v a)) (ord-v a) (fst (v b)) (ord-v b))
    where
    go : Tri (fst (v a)) (fst (v b))
       → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
```

<!--en-->
The strict-below case produces the pulled-back comparison directly. The equal case identifies the two domain members through the injectivity of `G` applied to the equal representative values. The strictly-above case reverses the comparison.
<!--zh-->
严格低于情形直接产出拉回比较。相等情形通过 `G` 的单射性施于相等的代表取值认同两个域成员。严格高于情形反转比较。
<!--ja-->
厳密に下の場合は、引き戻された比較を直接作る。等しい場合は、等しい代表の値に `G` の単射性を適用して、二つの定義域の要素を同一視する。厳密に上の場合は比較を逆向きにする。
<!--/-->

```agda
    go (inl h)       = inl (≺-bwd a b h)
    go (inr (inl e)) = inr (inl (OT.Dom≡
      (injG (v a) (OT.up a) (OT.up b) (v-holds a)
        (subst (λ w → ⟨ pr (OT.↪ b) w ∈ fst G ⟩) (sym e) (v-holds b)))))
    go (inr (inr h)) = inr (inr (≺-bwd b a h))
```

<!--en-->
Well-foundedness and transitivity now support the collapse map `col` and its image `otL`. Trichotomy adds injectivity of the collapse: distinct domain indices cannot have the same collapse value. These facts provide both the collapse table and the data needed to reverse it later.
<!--zh-->
良基性与传递性现在支持构造塌缩映射 `col` 及其像 `otL`。三歧性进一步给出塌缩的单射性：不同的域索引不可能具有相同的塌缩值。这些事实既给出塌缩表，也提供稍后反转它所需的数据。
<!--ja-->
整礎性と推移性から、崩壊写像 `col` とその像 `otL` が得られる。三分法を加えると崩壊の単射性も従い、異なる領域の添字が同じ崩壊値をもつことはない。これらの事実は、崩壊の表と、あとでそれを逆向きに読むためのデータの両方を与える。
<!--/-->

```agda
  module C = OT.Conjuncts wf ≺-trans
    using ( module Inj; col; col-ord; col-out; colTable; colTable-in
          ; colTable-pair; otL; otL-in; otL-out )
  module I = C.Inj tri using ( code; col-inj; module Inverse )
```

<!--en-->
The collapse table is a coded injection from the internal power set `P` into its collapse image `otL`. Wrapping that particular table and its injection proof in propositional truncation gives the internal statement `InjL P otL`.
<!--zh-->
塌缩表是从内部幂集 `P` 到其塌缩像 `otL` 的编码单射。把这张特定的表及其单射性证明放入命题截断，便得到内部陈述 `InjL P otL`。
<!--ja-->
崩壊の表は、内部の冪集合 `P` からその崩壊像 `otL` への符号化された単射である。その特定の表と単射性の証明を命題的に切り詰めることで、内部の主張 `InjL P otL` が得られる。
<!--/-->

```agda
  power-into-ot : InjL P C.otL
  power-into-ot = ∣ C.colTable , I.code ∣₁
```

<!--en-->
To prove that the collapse image is an ordinal, one must show both that the image is transitive and that each of its members is transitive. For the second condition, membership in `otL` gives, under propositional truncation, an index `b` whose collapse value presents the given member.
<!--zh-->
要证明塌缩像是序数，需要同时证明该像传递，并且它的每个成员都是传递集。对于第二项条件，属于 `otL` 的事实会在命题截断下给出一个索引 `b`，其塌缩值呈现给定成员。
<!--ja-->
崩壊像が順序数であることを示すには、像自身の推移性と、その各要素が推移的集合であることの両方が必要である。後者について、`otL` への所属から、命題的切り詰めのもとで、与えられた要素を崩壊値として提示する添字 `b` が得られる。
<!--/-->

```agda
  ot-ord : IsOrd (fst C.otL)
  ot-ord = tr , mem
    where
    mem : (x : V ℓ) → ⟨ x ∈ˢ fst C.otL ⟩ → isTransV x
    mem x h = rec₁ (isPropIsTransV x)
```

<!--en-->
Every collapse value `col b` is already known to be an ordinal, hence transitive. Transporting this transitivity along the equation `col b = x` proves that the arbitrary member `x` of the image is transitive.
<!--zh-->
每个塌缩值 `col b` 已知都是序数，因而是传递集。沿等式 `col b = x` 搬运这一传递性，便证明像的任意成员 `x` 都传递。
<!--ja-->
各崩壊値 `col b` はすでに順序数だと分かっているので、推移的である。この推移性を等式 `col b = x` に沿って輸送すれば、像の任意の要素 `x` が推移的であることが従う。
<!--/-->

```agda
      (λ { (b , e) → subst isTransV e (C.col-ord b .fst) })
      (C.otL-out x h)
```

<!--en-->
It remains to show that the image itself is transitive. Given `y∈x` and `x∈otL`, the outward description of `otL` presents `x`, under propositional truncation, as a collapse value `col b`; the target membership `y∈otL` is a proposition, so this witness may be used locally.
<!--zh-->
还需证明像本身是传递集。给定 `y∈x` 与 `x∈otL`，`otL` 的向外描述会在命题截断下把 `x` 呈现为某个塌缩值 `col b`；目标隶属 `y∈otL` 是命题，因此可以局部使用这个见证。
<!--ja-->
残るのは、像自身が推移的であることである。`y∈x` と `x∈otL` が与えられると、`otL` の外向きの記述は、命題的切り詰めのもとで `x` をある崩壊値 `col b` として提示する。目標の所属 `y∈otL` は命題なので、この証人を局所的に使える。
<!--/-->

```agda
    tr : isTransV (fst C.otL)
    tr {x} {y} y∈x x∈ot =
      rec₁ (snd (y ∈ˢ fst C.otL)) outer (C.otL-out x x∈ot)
      where
      outer : Σ[ b ∈ OT.Dom ] (C.col b ≡ x) → ⟨ y ∈ˢ fst C.otL ⟩
```

<!--en-->
After replacing `x` by `col b`, the collapse equation for membership in `col b` yields, again under propositional truncation, a predecessor `r≺b` whose collapse value is `y`. This is the smaller collapse value needed to place `y` back in the image.
<!--zh-->
把 `x` 换成 `col b` 后，关于 `col b` 中隶属关系的塌缩等式再次在命题截断下给出一个前驱 `r≺b`，其塌缩值为 `y`。这个更小的塌缩值正是把 `y` 放回像中所需的见证。
<!--ja-->
`x` を `col b` に置き換えると、`col b` への所属を述べる崩壊の等式から、再び命題的切り詰めのもとで、崩壊値が `y` である先行者 `r≺b` が得られる。この小さい崩壊値が、`y` を像へ戻すために必要な証人である。
<!--/-->

```agda
      outer (b , e) = rec₁ (snd (y ∈ˢ fst C.otL)) inner
        (C.col-out b y (subst (λ w → ⟨ y ∈ˢ w ⟩) (sym e) y∈x))
        where
        inner : Σ[ r ∈ OT.Dom ] ((r OT.≺ b) × (C.col r ≡ y))
              → ⟨ y ∈ˢ fst C.otL ⟩
```

<!--en-->
The predecessor's collapse is transported to `y` along its equation, completing the transitivity proof by placing `y` inside the image.
<!--zh-->
前驱的塌缩沿其等式运到 `y`，把 `y` 放进像内，完成传递性证明。
<!--ja-->
先行者の崩壊がその等式に沿って `y` へ運ばれ、`y` を像の中に置くことで、推移性の証明が完成する。
<!--/-->

```agda
        inner (r , _ , e2) =
          subst (λ w → ⟨ w ∈ˢ fst C.otL ⟩) e2 (C.otL-in r)
```

<!--en-->
For a hierarchy element `w`, the fibre `Fib w` consists of an index `b` together with an equality `col b = w`. Thus an inhabitant of this fibre is precisely a preimage of `w` under the collapse.
<!--zh-->
对层级元素 `w`，纤维 `Fib w` 由一个索引 `b` 与等式 `col b = w` 组成。因此，这个纤维的元素恰是 `w` 在塌缩映射下的原像。
<!--ja-->
階層の要素 `w` に対し、ファイバー `Fib w` は添字 `b` と等式 `col b = w` からなる。したがって、このファイバーの要素は、崩壊写像による `w` の原像そのものである。
<!--/-->

```agda
  Fib : V ℓ → Type (ℓ-suc ℓ)
  Fib w = Σ[ b ∈ OT.Dom ] (C.col b ≡ w)
```

<!--en-->
Injectivity of `col` makes each fibre a proposition. If `b` and `b'` both collapse to `w`, their equations identify `col b` with `col b'`, so injectivity identifies the indices. The ambient hierarchy `V ℓ` is a set, hence each equality type `col b = w` is a proposition and its proofs add no further distinction.
<!--zh-->
`col` 的单射性使每个纤维成为命题。若 `b` 与 `b'` 都塌缩到 `w`，两条等式就把 `col b` 与 `col b'` 认同，单射性继而认同两个索引。外围层级 `V ℓ` 是集合，因此每个等式类型 `col b = w` 都是命题，其中的证明不会造成进一步区别。
<!--ja-->
`col` の単射性により、各ファイバーは命題になる。`b` と `b'` がともに `w` へ崩壊するなら、それらの等式から `col b` と `col b'` が等しくなり、単射性によって添字も等しくなる。周囲の階層 `V ℓ` は集合なので、各等式型 `col b = w` は命題であり、その証明が新たな違いを生むこともない。
<!--/-->

```agda
  isPropFib : (w : V ℓ) → isProp (Fib w)
  isPropFib w (b , e) (b' , e') =
    Σ≡Prop (λ _ → setIsSet _ _) (I.col-inj b b' (e ∙ sym e'))
```

<!--en-->
Membership `w∈otL` supplies a preimage index only under propositional truncation. Since `Fib w` has just been shown to be a proposition, the truncation can be eliminated to recover the unique index whose collapse value is `w`.
<!--zh-->
隶属 `w∈otL` 起初只在命题截断下给出一个原像索引。由于刚刚证明了 `Fib w` 是命题，可以消去这一截断，恢复塌缩值为 `w` 的唯一索引。
<!--ja-->
所属 `w∈otL` が最初に与える原像の添字は、命題的切り詰めの内側にある。`Fib w` が命題であることを直前に示したので、この切り詰めを除去し、崩壊値が `w` である一意な添字を取り出せる。
<!--/-->

```agda
  fib : (w : V ℓ) → ⟨ w ∈ˢ fst C.otL ⟩ → Fib w
  fib w h = rec₁ (isPropFib w) (λ z → z) (C.otL-out w h)
```

<!--en-->
The unique preimage just obtained lets the collapse table be read in reverse on all of `otL`. The represented source member lies in `P`, so the inverse construction produces a graph in `L` and, in particular, the internal coded injection `Back.injL : InjL otL P` used below.
<!--zh-->
刚得到的唯一原像使塌缩表可以在整个 `otL` 上反向读取。该索引所表示的原成员属于 `P`，因此逆向构造会产生 `L` 中的一张图，尤其给出下文所用的内部编码单射 `Back.injL : InjL otL P`。
<!--ja-->
いま得た一意な原像により、崩壊の表を `otL` 全体で逆向きに読める。その添字が表すもとの要素は `P` に属するので、逆向きの構成は `L` にあるグラフを作り、とくに以下で用いる内部の符号化された単射 `Back.injL : InjL otL P` を与える。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Back where
```
</summary>
<div class="submodule-fold-content">

```agda
    open I.Inverse C.otL P (λ w mw → fib (fst w) mw)
      (λ w mw → OT.up-mem (fib (fst w) mw .fst)) public
      using ( fn; graph; at; only; M; inj; injL ) renaming ( SourceMem to Mem )
```
</div>
</details>

<!--en-->
Let `μ` denote the collapse ordinal `otL`. Ordinal trichotomy compares `μ` with the successor cardinal `δ`. The helper `from-sub` isolates the common construction for the equality and `δ∈μ` branches: whenever every member of `δ` is also a member of `μ`, it will produce the desired `InjL δ P`.
<!--zh-->
把塌缩序数 `otL` 记作 `μ`。序数三歧性比较 `μ` 与后继基数 `δ`。辅助函数 `from-sub` 提取出相等分支与 `δ∈μ` 分支共有的构造：只要 `δ` 的每个成员也属于 `μ`，它就会产生所需的 `InjL δ P`。
<!--ja-->
崩壊順序数 `otL` を `μ` と書く。順序数の三分法によって `μ` と後続基数 `δ` を比較する。補助関数 `from-sub` は、等しい場合と `δ∈μ` の場合に共通する構成を取り出す。`δ` のすべての要素が `μ` にも属するなら、必要な `InjL δ P` を作る。
<!--/-->

```agda
  result : InjL δ P
  result = go (ord-tri (fst C.otL) ot-ord (fst δ) ordδ)
    where
    from-sub : ((z : SV.S) → ⟨ z ∈ˢ fst δ ⟩ → ⟨ z ∈ˢ fst C.otL ⟩)
             → InjL δ P
```

<!--en-->
The inclusion coding packages the subset fact into a coded injection from `δ` into the collapse image, and the reverse-collapse injection composes it into the power set.
<!--zh-->
包含编码把子集事实打包为从 `δ` 到塌缩像的编码单射，逆塌缩单射再把它复合入幂集。
<!--ja-->
包含の符号が、部分集合の事実を、`δ` から崩壊の像への符号化された単射としてまとめ、逆崩壊の単射がそれを冪集合の中へ合成する。
<!--/-->

```agda
    from-sub sub =
      injl-trans δ C.otL P (inclusion-coded δ C.otL sub) Back.injL
```

<!--en-->
Trichotomy first considers `μ∈δ`. In this branch, `below-succ-injects` applies the successor-cardinal facts to obtain `InjL μ κ`. Composing it with `InjL P μ` gives `InjL P κ`, contradicting the internal Cantor theorem. This rules out exactly the case in which the collapse ordinal is strictly below `δ`.
<!--zh-->
三歧性首先考察 `μ∈δ`。在这一分支中，`below-succ-injects` 利用后继基数事实得到 `InjL μ κ`。将它与 `InjL P μ` 复合便得到 `InjL P κ`，这与内部 Cantor 定理矛盾。因此，被排除的恰好是塌缩序数严格低于 `δ` 的情形。
<!--ja-->
三分法では、まず `μ∈δ` の場合を考える。この場合、`below-succ-injects` は後続基数の事実を用いて `InjL μ κ` を与える。これを `InjL P μ` と合成すると `InjL P κ` が得られ、内部の Cantor の定理に反する。したがって排除されるのは、崩壊順序数が `δ` より真に小さい場合だけである。
<!--/-->

```agda
    go : Tri (fst C.otL) (fst δ) → InjL δ P
    go (inl ot∈δ)       = ⊥₀-rec (Cantor.no-inj zf κ
      (injl-trans P C.otL κ power-into-ot
        (below-succ-injects κ δ sc C.otL ot-ord ot∈δ)))
    go (inr (inl e))    =
```

<!--en-->
Both remaining cases give the containment needed by `from-sub`. If `μ=δ`, transport sends every membership in `δ` to membership in `μ`. If `δ∈μ`, transitivity of the ordinal `μ` gives the same containment `δ⊆μ`. Coding this inclusion and composing it with the reverse-collapse injection yields `InjL δ P` in either case.
<!--zh-->
余下两种情形都给出 `from-sub` 所需的包含。若 `μ=δ`，沿等式搬运便把 `δ` 中的每个隶属变为 `μ` 中的隶属。若 `δ∈μ`，序数 `μ` 的传递性同样给出 `δ⊆μ`。在任一情形中，把这个包含编码为单射并与逆塌缩单射复合，便得到 `InjL δ P`。
<!--ja-->
残る二つの場合は、どちらも `from-sub` に必要な包含を与える。`μ=δ` なら、等式に沿う輸送によって、`δ` への各所属が `μ` への所属になる。`δ∈μ` なら、順序数 `μ` の推移性から同じ包含 `δ⊆μ` が得られる。いずれの場合も、この包含を単射として符号化し、逆崩壊の単射と合成することで `InjL δ P` を得る。
<!--/-->

```agda
      from-sub (λ z h → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) h)
    go (inr (inr δ∈ot)) =
      from-sub (λ z h → ot-ord .fst h δ∈ot)
```
</div>
</details>

<!--en-->
## The successor cardinal reaches the power set
<!--zh-->
## 后继基数到达幂集
<!--ja-->
## 後続基数から冪集合へ到達する
<!--/-->

<!--en-->
The theorem receives a successor-cardinal witness `sc` and a propositionally truncated injection `InjL (𝒫 κ) δ`. It may inspect a particular graph `G` only within a local branch, because the target `InjL δ (𝒫 κ)` is itself a proposition. The additional hypothesis `κ∉ω` occurs in the statement of `SuccIntoPower` but is not used by this proof. In the GCH assembly, `succCardExists` supplies only a truncated choice of `δ` together with `sc`; `power-into-succ` separately constructs `pis : InjL (𝒫 κ) δ`, which is then passed to `succ-into-power`. The result records two truncated coded-injection existences. It does not select either graph or produce a bijection, a set equality, or a cardinal equation.
<!--zh-->
该定理接收后继基数见证 `sc` 与命题截断下的单射 `InjL (𝒫 κ) δ`。由于目标 `InjL δ (𝒫 κ)` 本身是命题，证明只能在局部分支中考察一张具体图 `G`。附加假设 `κ∉ω` 出现在 `SuccIntoPower` 的陈述中，但本证明没有使用它。在 GCH 的装配中，`succCardExists` 只在命题截断下给出 `δ` 及其见证 `sc`；`power-into-succ` 另行构造 `pis : InjL (𝒫 κ) δ`，再把它交给 `succ-into-power`。所得结论只记录两个方向的编码单射在命题截断下存在，并未选定任何一张图，也未产生双射、集合相等或基数等式。
<!--ja-->
この定理は、後続基数の証人 `sc` と、命題的に切り詰められた単射 `InjL (𝒫 κ) δ` を受け取る。目標 `InjL δ (𝒫 κ)` 自身が命題なので、特定のグラフ `G` を調べられるのは局所的な分岐の中だけである。追加の仮定 `κ∉ω` は `SuccIntoPower` の主張に現れるが、この証明では使われない。GCH の組み立てでは、`succCardExists` は命題的切り詰めのもとで `δ` とその証人 `sc` だけを与える。`power-into-succ` が別に `pis : InjL (𝒫 κ) δ` を構成し、それを `succ-into-power` に渡す。得られる結論が記録するのは、二方向の符号化された単射が命題的切り詰めのもとで存在することだけである。どちらのグラフも選ばず、全単射、集合の等しさ、基数の等式も与えない。
<!--/-->

```agda
succ-into-power : (zf : ModelL.isZFModel) → SuccIntoPower zf
succ-into-power zf κ δ κ∉ω sc =
  rec₁ squash₁ (λ { (G , code) → Build.result zf κ δ sc G code })
```
