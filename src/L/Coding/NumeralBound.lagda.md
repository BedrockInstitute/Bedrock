<!--en-->
# Numerals in a successor-closed ordinal stage

Finite ordinals supply the numerals used in formula codes. This chapter shows that every numeral belongs to a stage indexed by an ordinal that contains zero and is closed under successors. The argument first treats any monotone stage family containing each ordinal at its successor stage, then applies it to the constructible hierarchy.
<!--zh-->
# 对后继封闭的序数层中的数码

有限序数提供公式码所用的数码。本章证明，当层的序数指标包含零且对后继封闭时，每个数码都属于该层。我们先处理任意单调且在后继层包含原序数的层族，再将结论应用于可构造层级。
<!--ja-->
# 後者演算について閉じた順序数段階の数項

有限順序数は論理式コードに用いる数項を与えます。本章では、段階の順序数添字が零を含み、後者演算について閉じていれば、すべての数項がその段階に属することを示します。まず各順序数をその後者の段階に含む単調な段階族を扱い、その結果を構成可能階層に適用します。
<!--/-->

<!--en-->
The chapter fixes a universe level ℓ and takes excluded middle at level ℓ-suc ℓ as an explicit parameter `lem`. The elementary induction putting numerals inside an ordinal will not use it; the assumption is carried here because one ingredient of the constructible specialization, the theorem that an ordinal appears at the stage indexed by its successor, comes from the classical ordinal-stage development.
<!--zh-->
本章固定一个宇宙层级 ℓ，并把层级 ℓ-suc ℓ 上的排中律作为显式参数 `lem`。把数码放进序数的初等归纳并不使用它；这里之所以携带这个假设，是因为可构造特化的一项原料，即序数出现在以其后继为指标的层这一定理，来自经典的序数层章节。
<!--ja-->
本章は宇宙レベル ℓ を固定し、レベル ℓ-suc ℓ の排中律を明示的なパラメータ `lem` として受け取ります。数項を順序数の内部へ入れる初等的な帰納法はこれを用いません。この仮定を持ち回るのは、構成可能な場合への特化に必要な素材、すなわち順序数がその後者を添字とする段階に現れるという定理が、古典的な順序数段階の章に由来するからです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Coding.NumeralBound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
Two presentations of a numeral must be kept apart. The ambient numeral `# k` is the finite von Neumann ordinal in `V ℓ`; the model numeral `numeralL k` is an element of `L` whose underlying set is `# k`. The first part proves the bound for the ambient ordinal. Only after that does the projection equation `numeralL-fst` transfer the result to the model presentation.
<!--zh-->
必须区分数码的两种呈现。周遭数码 `# k` 是 `V ℓ` 中的有穷 von Neumann 序数；模型数码 `numeralL k` 是 `L` 的元素，其底层集合为 `# k`。论证先为周遭序数证明界，随后才用投影等式 `numeralL-fst` 把结论转到模型呈现。
<!--ja-->
数項の二つの表現を区別します。周囲の数項 `# k` は `V ℓ` の有限 von Neumann 順序数であり、模型の数項 `numeralL k` は底集合が `# k` である `L` の要素です。まず周囲の順序数について上界を証明し、その後で射影等式 `numeralL-fst` により模型での表現へ結果を移します。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
```

<!--en-->
The ambient numerals live in the cumulative hierarchy itself: `∅` is its empty set, `# k` is the finite von Neumann ordinal with k members, and `sucV` is the successor step a ↦ a ∪ {a}. Note that `# (suc k)` is definitionally `sucV (# k)`, so closing λ under `sucV` automatically covers every numeral after zero. The truth values here are propositions at level ℓ-suc ℓ, packaged directly in `hProp`, so each membership claim is a proposition.
<!--zh-->
周遭数码就生活在累积层级自身之中：`∅` 是其中的空集，`# k` 是有 k 个成员的有限冯·诺伊曼序数，`sucV` 是后继步骤 a ↦ a ∪ {a}。注意 `# (suc k)` 定义地就是 `sucV (# k)`，因此 λ 对 `sucV` 封闭就自动覆盖零之后的每个数码。这里的真值是层级 ℓ-suc ℓ 上的命题，直接打包在 `hProp` 中，所以每条隶属断言都是命题。
<!--ja-->
周囲の数項は累積階層そのものの中に住んでいます。`∅` はその空集合、`# k` は要素を k 個持つ有限のフォン・ノイマン順序数、`sucV` は a ↦ a ∪ {a} という後者の操作です。`# (suc k)` は定義上 `sucV (# k)` に等しいので、λ が `sucV` について閉じていれば零以降のすべての数項が自動的に覆われます。ここでの真理値は `hProp` に直接まとめられたレベル ℓ-suc ℓ の命題であり、各所属の主張は命題です。
<!--/-->

```agda
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; sucV )

```

<!--en-->
All three memberships in the argument have different roles: `# k ∈ λ` places a finite ordinal below the index; `# k ∈ T (sucV (# k))` places it in its canonical successor stage; and `# k ∈ T λ` is the desired bound. Writing each as a proposition makes the induction and the later transport proof-irrelevant, but the implication between them still comes from the stated closure, ordinal-stage, and monotonicity hypotheses.
<!--zh-->
论证中的三种隶属各有作用：`# k ∈ λ` 把有穷序数置于指标之下；`# k ∈ T (sucV (# k))` 把它置于自身的后继层；`# k ∈ T λ` 才是所求的界。它们都作为命题陈述，因而归纳与后续搬运不依赖证明的选择；三者之间的推导仍分别依靠后继封闭、序数层性质与单调性假设。
<!--ja-->
議論に現れる三つの所属は役割が異なります。`# k ∈ λ` は有限順序数を添字の下に置き、`# k ∈ T (sucV (# k))` はそれを自身の後者段階に置き、`# k ∈ T λ` が求める上界です。いずれも命題として述べられるため、帰納と後の輸送は証明の選び方に依存しませんが、それらを結ぶ推論には後者閉包、順序数段階の性質、単調性の各仮定が必要です。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
```

<!--en-->
## A bound for monotone stage families

Let λ contain zero and be closed under successors. Induction puts every numeral `# k` in λ. To place that same numeral in `T λ`, use `numeral-ord k` with the successor-stage hypothesis to obtain `# k ∈ T (sucV (# k))`; successor closure gives the index relation `sucV (# k) ∈ λ`, and monotonicity then yields `# k ∈ T λ`.
<!--zh-->
## 单调层族的界

设 λ 包含零且对后继封闭。归纳法先把每个数码 `# k` 放入 λ。要把同一个数码放入 `T λ`，先以 `numeral-ord k` 和后继层假设得到 `# k ∈ T (sucV (# k))`；后继封闭给出指标关系 `sucV (# k) ∈ λ`，单调性随即推出 `# k ∈ T λ`。
<!--ja-->
## 単調な段階族に対する上界

λ が零を含み後者演算について閉じているとします。帰納法で各数項 `# k` を λ に入れます。同じ数項を `T λ` に入れるには、`numeral-ord k` と後者段階の仮定から `# k ∈ T (sucV (# k))` を得ます。後者閉包が添字の関係 `sucV (# k) ∈ λ` を与え、単調性から `# k ∈ T λ` が従います。
<!--/-->

<!--en-->
The section works over the fixed carrier S with membership `⟨_∈ˢ_⟩`, an arbitrary map T on it, and two hypotheses about T. The first, `T-mono`, converts a membership of stage indices β ∈ α together with x ∈ T β into x ∈ T α. The second, `T-ord`, is the anchor: an ordinal δ belongs to T (sucV δ), the stage indexed by its own successor.
<!--zh-->
本节在固定载体 S 及其隶属 `⟨_∈ˢ_⟩` 上、其上的任意映射 T 以及关于 T 的两条假设来陈述。第一条 `T-mono` 把层指标的隶属 β ∈ α 连同 x ∈ T β 转换为 x ∈ T α。第二条 `T-ord` 是锚点：序数 δ 属于以其自身后继为指标的层 T (sucV δ)。
<!--ja-->
本節は、所属 `⟨_∈ˢ_⟩` を備えた固定された台 S、その上の任意の写像 T、および T に関する二つの仮定に対して述べられます。第一の `T-mono` は、段階添字の所属 β ∈ α と x ∈ T β とから x ∈ T α を導きます。第二の `T-ord` が錨です。順序数 δ は、その自身の後者を添字とする段階 T (sucV δ) に属します。
<!--/-->

```agda
module BoundOver
  (T : S → S)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-ord : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ T (sucV δ) ⟩)
  (lam : S) (ordλ : IsOrd lam)
```

<!--en-->
The remaining parameters describe the index λ: it is a set, certified to be an ordinal, containing ∅, and closed under `sucV`. The certification `ordλ` records that λ itself is a legitimate ordinal stage index; the two closure facts are the only ones the induction will consume.
<!--zh-->
其余参数刻画指标 λ：它是一个集合，被证明为序数，包含 ∅，且对 `sucV` 封闭。证书 `ordλ` 记录 λ 自身是合法的序数层指标；两条封闭事实则是归纳法将要消耗的全部。
<!--ja-->
残りのパラメータは添字 λ を記述します。λ は集合であり、順序数であることの証明を持ち、∅ を含み、`sucV` について閉じています。証明 `ordλ` は λ 自身が正当な順序数段階の添字であることを記録します。帰納法が消費するのは二つの閉包の事実だけです。
<!--/-->

```agda
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
```

<!--en-->
Every ambient numeral lands in λ, and the proof uses only the two closure facts just assumed. This is the purely inductive half of the argument: no excluded middle, no property of T, and not even the ordinal certificate of λ enter it.
<!--zh-->
每个周遭数码都落入 λ，其证明只使用刚才假设的两条封闭事实。这是论证中纯粹归纳的一半：不用排中律，不用 T 的任何性质，甚至连 λ 的序数证书也不参与。
<!--ja-->
周囲の数項はすべて λ に入ります。その証明は直前に仮定した二つの閉包の事実だけを用います。これが議論の純粋に帰納的な半分です。排中律も、T の性質も、さらには λ の順序数であることの証明さえも入りません。
<!--/-->

<!--en-->
Induction on k. The base case is exactly the hypothesis ∅∈λ, since `# 0` is ∅. For the step, `# (suc k)` is definitionally `sucV (# k)`, so succλ applied to the induction hypothesis `# k ∈ λ` yields `# (suc k) ∈ λ`. The small cases show the shape: 0 = ∅ ∈ λ, then {∅} = sucV ∅ ∈ λ, then the numeral 2 = sucV (sucV ∅) ∈ λ, each step consuming one use of successor closure.
<!--zh-->
对 k 归纳。基例恰是假设 ∅∈λ，因为 `# 0` 就是 ∅。归纳步中，`# (suc k)` 定义地就是 `sucV (# k)`，故把归纳假设 `# k ∈ λ` 交给 succλ 即得 `# (suc k) ∈ λ`。小情形显出形状：0 = ∅ ∈ λ，接着 {∅} = sucV ∅ ∈ λ，再接着数码 2 = sucV (sucV ∅) ∈ λ，每一步消耗一次后继封闭。
<!--ja-->
k についての帰納法です。基底の場合は、`# 0` が ∅ そのものなので仮定 ∅∈λ がそのまま答えます。帰納の段では、`# (suc k)` は定義上 `sucV (# k)` に等しいので、帰納仮説 `# k ∈ λ` に succλ を適用して `# (suc k) ∈ λ` が得られます。小さい場合は形を示します。0 = ∅ ∈ λ、次に {∅} = sucV ∅ ∈ λ、さらに数項 2 = sucV (sucV ∅) ∈ λ と、各段階で後者についての閉包を一度ずつ使います。
<!--/-->

```agda
  #∈λ : (k : ℕ) → ⟨ (# k) ∈ˢ lam ⟩
  #∈λ zero    = ∅∈λ
  #∈λ (suc k) = succλ (# k) (#∈λ k)
```

<!--en-->
Membership in λ is an index-level statement; membership in the stage T λ is a different statement, and it needs the two properties of T rather than only the closure of λ. The route runs through the successor stage of the numeral itself.
<!--zh-->
属于 λ 是指标层面的陈述；属于层 T λ 是另一条不同的陈述，它需要 T 的两条性质，而不仅是 λ 的封闭性。路径要经过数码自身的后继层。
<!--ja-->
λ への所属は添字のレベルでの主張ですが、段階 T λ への所属は別の主張であり、λ の閉包だけでなく T の二つの性質を必要とします。道は数項自身の後者の段階を経由します。
<!--/-->

<!--en-->
Two steps compose. First, T-ord at δ = # k, together with `numeral-ord k` certifying the numeral is an ordinal, places # k in T (sucV (# k)). Second, T-mono moves the membership from the index sucV (# k) up to the index λ: the needed premise # (suc k) ∈ λ is exactly #∈λ (suc k), and #∈λ (suc k) unfolds to sucV (# k) ∈ λ, precisely the membership of indices T-mono asks for. So the element # k ends in T λ, with the ordinal certificate doing real work in the first step.
<!--zh-->
两步复合而成。第一步，在 δ = # k 处使用 T-ord，并以 `numeral-ord k` 证明该数码是序数，把 # k 放进 T (sucV (# k))。第二步，T-mono 把隶属从指标 sucV (# k) 提升到指标 λ：所需前提 # (suc k) ∈ λ 正是 #∈λ (suc k)，而它展开后就是 sucV (# k) ∈ λ，恰好是 T-mono 要求的指标间隶属。于是元素 # k 落入 T λ，序数证书在第一步中发挥了实际作用。
<!--ja-->
二つの段階が合成されます。まず δ = # k に対して T-ord を用い、数項が順序数であることを `numeral-ord k` が証明していれば、# k は T (sucV (# k)) に入ります。次に T-mono が所属を添字 sucV (# k) から添字 λ へ引き上げます。必要な前提 # (suc k) ∈ λ はまさに #∈λ (suc k) であり、それは sucV (# k) ∈ λ に展開され、T-mono が要求する添字間の所属に一致します。こうして要素 # k は T λ に収まり、最初の段階では順序数であることの証明が実質的な仕事を果たします。
<!--/-->

```agda
  #∈Tλ : (k : ℕ) → ⟨ (# k) ∈ˢ T lam ⟩
  #∈Tλ k = T-mono {α = lam} {β = sucV (# k)} (#∈λ (suc k))
    {x = # k} (T-ord (# k) (numeral-ord k))
```

<!--en-->
## Numerals in the constructible hierarchy

Constructible stages are monotone, and each ordinal belongs to the stage indexed by its successor. The general bound therefore applies to L. We also express this membership using the numerals already regarded as elements of the model.
<!--zh-->
## 可构造层级中的数码

可构造层具有单调性，每个序数也属于以后继为指标的层，因此一般的界适用于 L。我们还用模型内部的数码来表述这一隶属关系。
<!--ja-->
## 構成可能階層における数項

構成可能な段階は単調であり、各順序数はその後者を添字とする段階に属します。したがって一般の上界の議論を L に適用できます。この所属関係を、モデルの要素として与えた数項についても述べます。
<!--/-->

<!--en-->
Instantiating the abstraction only requires naming the witnesses. The family T becomes `Lset`, `Lset-mono` supplies monotonicity along membership of ordinal indices, and `ord∈Lset-suc` supplies the anchor that each ordinal sits in `Lset (sucV α)`. The theorem `ord∈Lset-suc` carries the classical assumption required for this specialization; the induction on numerals itself remains the elementary closure argument already given. The hypotheses about λ are passed through unchanged, so everything proved inside `BoundOver` about T λ becomes available about `Lset lam`.
<!--zh-->
把抽象实例化只需指名见证。层族 T 取为 `Lset`，`Lset-mono` 提供沿序数指标隶属的单调性，`ord∈Lset-suc` 提供锚点：每个序数属于 `Lset (sucV α)`。定理 `ord∈Lset-suc` 携带这一特化所需的经典假设；数码归纳本身仍是前面给出的初等封闭论证。关于 λ 的假设原样传入，因此 `BoundOver` 内部关于 T λ 证明的一切，对 `Lset lam` 都同样可用。
<!--ja-->
抽象の実体化は、証人を指名するだけで済みます。段階族 T には `Lset` を与え、`Lset-mono` が順序数添字の所属に沿う単調性を供給し、`ord∈Lset-suc` が「各順序数は `Lset (sucV α)` に属する」という錨を供給します。定理 `ord∈Lset-suc` がこの特殊化に必要な古典的仮定を担います。数項についての帰納そのものは、先に示した初等的な閉包の議論のままです。λ に関する仮定はそのまま渡されるので、`BoundOver` の内部で T λ について証明されたことはすべて `Lset lam` についても使えます。
<!--/-->

```agda
module Bound (lam : S) (ordλ : IsOrd lam)
             (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  open BoundOver Lset Lset-mono ord∈Lset-suc lam ordλ succλ ∅∈λ public
```

<!--en-->
Inside the model, a numeral is not the ambient ordinal itself but a pair `numeralL k` whose first component denotes it. The bound transfers to that presentation by one transport, not by repeating the induction.
<!--zh-->
在模型内部，数码不是环境序数本身，而是一个序对 `numeralL k`，其第一分量指称该序数。这条界通过一次搬运转移到该呈现上，而不必重做归纳。
<!--ja-->
モデルの内部では、数項は周囲の順序数そのものではなく、その順序数を指し示す第一成分を持つ対 `numeralL k` です。この上界は、帰納法を繰り返すのではなく、一度の輸送でこの提示へ移ります。
<!--/-->

<!--en-->
The equation `numeralL-fst k` is a path `fst (numeralL k) ≡ # k` in the host theory. Transporting the membership family along this path turns the proof for # k into a proof for fst (numeralL k). Using `sym` orients the path from the established membership of `# k` to the desired membership of `fst (numeralL k)`, so `#∈Tλ k` becomes the required statement about the model numeral.
<!--zh-->
等式 `numeralL-fst k` 是宿主理论中的一条路径 `fst (numeralL k) ≡ # k`。沿这条路径搬运隶属类型族，即可把关于 # k 的隶属证明变为关于 fst (numeralL k) 的证明。使用 `sym` 把路径定向为：从已经证明的 `# k` 的隶属，得到所求的 `fst (numeralL k)` 的隶属；于是 `#∈Tλ k` 化为关于模型数码的陈述。
<!--ja-->
等式 `numeralL-fst k` はホスト理論における経路 `fst (numeralL k) ≡ # k` です。この経路に沿って所属の型族を輸送すると、# k に関する証明が fst (numeralL k) に関する証明へ移ります。`sym` は、既に得た `# k` の所属から、求める `fst (numeralL k)` の所属へ向かうようにパスを整えます。これにより `#∈Tλ k` が模型の数項についての主張に変わります。
<!--/-->

```agda
  num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  num∈λ k = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (numeralL-fst k)) (#∈Tλ k)
```
