<!--en-->
# An ordinal L-cardinal above every L-cardinal

Given an infinite cardinal of `L`, this chapter constructs a strictly larger cardinal, represented by an ordinal of `L`. The construction builds one explicit candidate above the given cardinal; it does not select the least such candidate, which is the task of the later assembly.
<!--zh-->
# 任意 L 基数之上的序数 L 基数

给定 `L` 中的一个无限基数，本章构造一个严格更大的基数，并由 `L` 中的序数表示。该构造只给出给定基数之上的一个显式候选；并不选取最小候选，那是后续装配工作的任务。
<!--ja-->
# 任意の L 基数より大きい順序数 L 基数

`L` の無限基数が与えられたとき、この章は真に大きい基数を構成し、それを `L` の順序数で表します。構成は、与えられた基数より上の一つの明示的な候補を作るだけで、最小の候補を選ぶのは後の組み立ての仕事です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
The base library is opened, and excluded middle is received at the raised level and also lowered to the inner level, where a Bool-valued relation will be decided by it.
<!--zh-->
打开基础库，并在抬升层级取得排中律，再把它降到内层。后文有一条布尔值关系需要由它判定。
<!--ja-->
基礎ライブラリを開き、上げられたレベルで排中律を受け取り、さらに内側のレベルへ降ろします。後で、ブール値の関係をこれで判定するためです。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM; lowerLEM )

```

<!--en-->
The argument is parameterized by excluded middle one universe level above the sets under discussion. Later, the same assumption will be lowered to decide a small proposition when the Hartogs relation is encoded by Booleans. No choice principle is assumed.
<!--zh-->
本论证以高于所讨论集合一个宇宙层级的排中律为参数。稍后会把同一假设降到较低层级，用来判定一个小命题，并将 Hartogs 关系编码为布尔值。这里不假设选择公理。
<!--ja-->
この議論は、対象となる集合より一つ高い宇宙レベルの排中律を引数に取ります。後で同じ仮定を低いレベルへ移し、小さな命題を判定して Hartogs の関係をブール値で符号化します。選択公理は仮定しません。
<!--/-->

```agda
module L.CardinalAbove {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Two properties of the ambient cumulative hierarchy drive the later contradictions. Membership is well-founded, and no set is a member of itself. A presentation supplies indices for a set's members, while `self∈sucV` places a set in its ordinal successor.
<!--zh-->
环境累积层级的两条性质推动后面的反证：隶属关系是良基的，而且集合不属于自身。呈现为集合的成员提供索引，而 `self∈sucV` 把集合放入它的序数后继。
<!--ja-->
周囲の累積階層における二つの性質が、後の背理法を支えます。所属は整礎的であり、どの集合も自分自身には属しません。提示は集合の要素に添字を与え、`self∈sucV` は集合をその順序数としての後続に入れます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
```

<!--en-->
The constructible side supplies its carrier, transitive constructibility, the ordinal predicate, the stage reading of constructible sets, ordinal facts, and the internal cardinality predicate with its injections.
<!--zh-->
可构造一侧供给：其载体、传递的可构造性、序数谓词、可构造集合的层读取、序数事实，以及内部基数性谓词与其单射。
<!--ja-->
構成可能な側は、その台、推移的な構成可能性、順序数の述語、構成可能な集合の段階の読み、順序数の事実、そして内部の基数性の述語とその単射を供給します。
<!--/-->

```agda
  using ( 𝒮ʟ; IsOrd; Lset→isL; isTransV; isPropIsTransV )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; boundingOrd )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; _↪_ )
```

<!--en-->
Two bridges will connect the construction. The reading lemma turns a coded injection inside `L` into an actual injection between presentations, and the Mostowski development collapses a transitive well-founded relation to sets. These bridges let an ambient Hartogs argument yield an internal cardinal statement.
<!--zh-->
两座桥梁将连接整个构造。读取引理把 `L` 内部的编码单射变为呈现之间的实际单射，Mostowski 塌缩则把传递良基关系化为集合。借助二者，环境中的 Hartogs 论证最终给出内部基数陈述。
<!--ja-->
二つの橋渡しが構成を結びます。読み取り補題は `L` 内部の符号化された単射を提示の間の実際の単射に変え、Mostowski 崩壊は推移的で整礎的な関係を集合へ移します。これらにより、周囲での Hartogs の議論から内部の基数に関する主張が得られます。
<!--/-->

```agda
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.Mostowski {ℓ} using ( module Mostowski )

```

<!--en-->
The hierarchy contributes membership bridges, presentations, embedding machinery, the separation construction with its axiom, and the union operation.
<!--zh-->
层级贡献隶属桥、呈现、嵌入机制、带公理的分离构造，以及并运算。
<!--ja-->
階層は、所属の橋、提示、埋め込みの仕組み、公理を伴う分出の構成、そして和の演算を供給します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _∈ₛ_; extensionality; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; module SeparationSet; ⋃_ )
```

<!--en-->
The proof uses `ω` only in the public statement and uses ordinal successors to create bounds. Sums express the cases of ordinal trichotomy, while Booleans encode the small relation used in the Hartogs construction; the proposition-level lemmas justify the later eliminations from truncated existence.
<!--zh-->
证明只在公开陈述中使用 `ω`，并用序数后继建立上界。和类型表达序数三分法的各个分支，布尔值编码 Hartogs 构造所用的小关系；关于命题性的引理则保证稍后可以从截断存在中消去。
<!--ja-->
証明で `ω` を使うのは公開された主張だけであり、上界を作る際には順序数の後続を使います。直和は順序数の三分性の場合分けを表し、ブール値は Hartogs の構成で用いる小さな関係を符号化します。命題性に関する補題は、後で切り詰められた存在から除去できることを保証します。
<!--/-->

```agda
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
```

<!--en-->
Accessibility and well-foundedness, together with the embedding machinery of the cubical library, support the pullback argument of the Hartogs section.
<!--zh-->
可达性与良基性，连同立方库的嵌入机制，支撑 Hartogs 一节的拉回论证。
<!--ja-->
到達可能性と整礎性、そして Cubical ライブラリの埋め込みの仕組みが、Hartogs の節の引き戻しの議論を支えます。
<!--/-->

```agda
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded )
open import Cubical.Functions.Embedding
  using ( isEmbedding; injEmbedding; isEmbedding→hasPropFibers
        ; Embedding-into-isSet→isSet )
```

<!--en-->
The empty type refutes impossible cases, and truncated existence is the form in which the chapter's main result is stated.
<!--zh-->
空类型反驳不可能情形，而截断存在正是本章主结果的陈述形式。
<!--ja-->
空の型は不可能な場合を反証し、切り詰められた存在が、この章の主な結果の述べ方です。
<!--/-->

```agda

```

<!--en-->
The ambient and constructible structures are opened as modules, since both are used throughout.
<!--zh-->
外围结构与可构造结构都作为模块打开，因为两者贯穿全章。
<!--ja-->
周囲の構造と構成可能な構造の両方が、全章を通して使われるため、モジュールとして開かれます。
<!--/-->

```agda

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

```

<!--en-->
The ambient membership is opened under its plain name.
<!--zh-->
外围隶属以朴素名字打开。
<!--ja-->
周囲の所属が、そのままの名前で開かれます。
<!--/-->

```agda
open SV using ( _∈ˢ_ )
```

<!--en-->
Ambient cardinality says that `κ` admits no injection into the presentation of any member `δ ∈ κ`. Here an injection is a function equipped with ordinary injectivity, rather than a Cubical embedding record. Ordinality is a separate property and will be proved independently for the candidate constructed below.
<!--zh-->
环境基数性断言：对每个成员 `δ ∈ κ`，`κ` 的呈现都不能单射到 `δ` 的呈现。这里的单射是一个函数及其通常的单射性证明，并不是 Cubical 的嵌入记录。序数性是另一项性质，后文会为所构造的候选另行证明。
<!--ja-->
周囲での基数性は、各要素 `δ ∈ κ` に対して、`κ` の提示から `δ` の提示への単射が存在しないことを述べます。ここでいう単射は、通常の単射性の証明を伴う関数であり、Cubical の埋め込みレコードではありません。順序数性は別の性質であり、後で構成する候補について独立に証明します。
<!--/-->

```agda
IsCardinal : SV.S → Type (ℓ-suc ℓ)
IsCardinal κ = (δ : SV.S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → ⊥₀)

```

<!--en-->
Injections between types compose by composing the maps and transporting the injectivity proofs through the composite.
<!--zh-->
类型之间的单射通过复合映射并沿复合搬运单射性证明而复合。
<!--ja-->
型の間の単射は、写像を合成し、単射性の証明を合成を通して運ぶことで合成されます。
<!--/-->

```agda
comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

```

<!--en-->
If `a ∈ b` and `b` is an ordinal, every member of `a` is also a member of `b` by transitivity. An index presenting a member of `a` can therefore be sent to the fiber of the presentation of `b` over that same set, defining an injection `⟪a⟫ ↪ ⟪b⟫`.
<!--zh-->
若 `a ∈ b` 且 `b` 是序数，则由传递性，`a` 的每个成员也是 `b` 的成员。因此，可把呈现 `a` 的一个成员的索引送到 `b` 的呈现在同一集合上的纤维，从而定义单射 `⟪a⟫ ↪ ⟪b⟫`。
<!--ja-->
`a ∈ b` であり `b` が順序数なら、推移性により `a` の各要素は `b` の要素でもあります。そこで、`a` の要素を提示する添字を、同じ集合の上にある `b` の提示のファイバーへ送り、単射 `⟪a⟫ ↪ ⟪b⟫` を定めます。
<!--/-->

```agda
ord-emb : (a b : SV.S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
```

<!--en-->
The embedding is injective, because the fiber identifications of two indices are chained through the equality of their images.
<!--zh-->
该嵌入是单射的：两个索引的纤维同一视经由其像的等式串联。
<!--ja-->
埋め込みは単射です。二つの索引の繊維の同一視が、像の等式を通して連鎖するからです。
<!--/-->

```agda
  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
      ∙ cong (⟪ b ⟫↪) e
      ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)
```

<!--en-->
## The target statement
<!--zh-->
## 目标陈述
<!--ja-->
## 目標となる主張
<!--/-->

<!--en-->
The public goal takes a constructible `κ`, together with proofs that its underlying set is an ordinal, is an internal cardinal, and is not a member of `ω`. It asks only for the propositionally truncated existence of a constructible `θ`; no particular witness may be extracted from the theorem.
<!--zh-->
公开目标给定可构造集合 `κ`，并假设其底层集合是序数、是内部基数且不属于 `ω`。结论只要求某个可构造集合 `θ` 的命题截断存在；不能从该定理中抽取特定见证。
<!--ja-->
公開された目標は、構成可能な `κ` と、その台となる集合が順序数であり、内部の基数であり、`ω` の要素ではないという証明を受け取ります。結論が要求するのは構成可能な `θ` の命題的に切り詰められた存在だけであり、定理から特定の証人を取り出すことはできません。
<!--/-->

```agda
CardAboveLᵀ : Type (ℓ-suc ℓ)
CardAboveLᵀ =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  → ∥ Σ[ θ ∈ SL.S ]
```

<!--en-->
The produced `θ` must be an ordinal, an internal cardinal, and strictly above `κ`, the last membership expressing the strict inequality of von Neumann ordinals.
<!--zh-->
产出的 `θ` 必须是序数、内部基数，且严格大于 `κ`；最后的成员关系表达的正是 von Neumann 序数的严格不等。
<!--ja-->
産み出される `θ` は順序数であり、内部の基数であり、`κ` より真に大きくなければなりません。最後の所属が、von Neumann 順序数としての狭義の不等号を表します。
<!--/-->

```agda
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁
```

<!--en-->
## Ordinals as elements of L
<!--zh-->
## 序数作为 L 的元素
<!--ja-->
## L の要素としての順序数
<!--/-->

<!--en-->
An ambient ordinal becomes an element of `L` by being presented at its own successor stage: the stage `Lset (sucV x)` contains `x`, is indexed by an ordinal, and carries the constructibility of `x`. This is a natural representative; the chapter does not claim it to be the earliest stage containing `x`.
<!--zh-->
外围序数通过「在其自身后继层处呈现」而成为 `L` 的元素：层 `Lset (sucV x)` 包含 `x`，其指数是序数，并携带 `x` 的可构造性。这是一个自然代表；本章不主张它是最早包含 `x` 的层。
<!--ja-->
周囲の順序数は、その自身の後続の段階で提示されることで、`L` の要素になります。段階 `Lset (sucV x)` は `x` を含み、その指数は順序数であり、`x` の構成可能性を運びます。これは自然な代表であり、`x` を含む最も早い段階だと主張するものではありません。
<!--/-->

```agda
ordL : (x : SV.S) → IsOrd x → SL.S
ordL x ox = x , Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)
```

<!--en-->
## From ambient to internal cardinality
<!--zh-->
## 从环境基数性到内部基数性
<!--ja-->
## 周囲の基数性から内部の基数性へ
<!--/-->

<!--en-->
Ambient cardinality implies internal cardinality, in one direction only. A coded injection is read as an ambient injection by its own reading lemma, so the ambient refutation eliminates the truncated coding; the elimination is legitimate because the target is the empty type.
<!--zh-->
环境基数性蕴涵内部基数性，且只有这一个方向。编码单射可由其读取引理读成环境单射，因此环境中的反驳消去截断的编码；由于目标是空类型，消去合法。
<!--ja-->
周囲の基数性は内部の基数性を含意します。ただし一方向だけです。符号化された単射はその読みの補題によって周囲の単射として読めるので、周囲での反証が切り詰められた符号を消去します。目標が空の型であるため、この消去は正当です。
<!--/-->

```agda
ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
ambient→internal κ c δ δ∈κ h =
  rec₁ isProp⊥ (λ w → c (fst δ) δ∈κ (readL κ δ w)) h
```

<!--en-->
## Separating smaller cardinals
<!--zh-->
## 分出较小基数
<!--ja-->
## より小さい基数を分出する
<!--/-->

<!--en-->
Fix a set `a` and an ordinal bound `β`. The construction separates from `β` those members whose presentations inject into the presentation of `a`. In the later application `a` is also an ordinal, but only the ordinality of the bound is needed inside this module.
<!--zh-->
固定集合 `a` 与序数界 `β`。这个构造从 `β` 中分出呈现可单射到 `a` 的呈现的那些成员。后续应用中的 `a` 也是序数，但在本模块内部只需要界的序数性。
<!--ja-->
集合 `a` と順序数の上界 `β` を固定します。この構成は、提示から `a` の提示への単射をもつ要素を `β` から分出します。後の適用では `a` も順序数ですが、このモジュールの内部で必要なのは上界の順序数性だけです。
<!--/-->

```agda
module Sep (a : SV.S) (β : SV.S) (oβ : IsOrd β) where

```

<!--en-->
The separating predicate asks whether a set embeds into `a`, and is stated as a truncated existence. Since it lives in `hProp ℓ` by construction, it can be handed to separation directly, with no resizing step in between.
<!--zh-->
分离谓词问：一个集合是否嵌入 `a`；它被陈述为截断的存在。由于它按构造居于 `hProp ℓ`，可直接交给分离，中间无需任何命题换级。
<!--ja-->
分出の述語は、ある集合が `a` へ埋め込めるかを問い、切り詰められた存在として述べられます。それは構成によって `hProp ℓ` に住むので、中間の命題リサイズなしに、そのまま分出に渡せます。
<!--/-->

```agda
  ϕ : SV.S → hProp ℓ
  ϕ x = ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ , squash₁

```

<!--en-->
The separation construction of the hierarchy is opened at the ordinal bound with this predicate.
<!--zh-->
层级分离构造在该序数界处以这一谓词打开。
<!--ja-->
階層の分出の構成が、この述語とともに、順序数の上界のもとで開かれます。
<!--/-->

```agda
  open SeparationSet β ϕ using ( SEPAREE; separation-ax )

```

<!--en-->
The separated set is named `θ`: it collects exactly those members of the bound that embed into `a`.
<!--zh-->
分离所得集合命名为 `θ`：它恰好收集界中那些可嵌入 `a` 的成员。
<!--ja-->
分出された集合は `θ` と名付けられます。それは、上界の要素のうち `a` へ埋め込めるものをちょうど集めた集合です。
<!--/-->

```agda
  θ : SV.S
  θ = SEPAREE

```

<!--en-->
Membership in `θ` is introduced from membership in the bound together with a truncated embedding into `a`, through the separation axiom.
<!--zh-->
`θ` 中的隶属由「属于界」连同「截断的到 `a` 嵌入」经分离公理引入。
<!--ja-->
`θ` の中の所属は、上界への所属と、`a` への切り詰められた埋め込みとを、分出の公理を通して導入されます。
<!--/-->

```agda
  θ-in : (x : SV.S) → ⟨ x ∈ˢ β ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ → ⟨ x ∈ˢ θ ⟩
  θ-in x x∈β h =
    ∈∈ₛ {a = x} {b = θ} .snd
      (separation-ax x .snd (∈∈ₛ {a = x} {b = β} .fst x∈β , h))

```

<!--en-->
Conversely, membership in `θ` forgets the separating condition and keeps only membership in the bound.
<!--zh-->
反过来，`θ` 中的隶属忘掉分离条件，只保留界中的隶属。
<!--ja-->
逆に、`θ` の中の所属は分出の条件を忘れ、上界への所属だけを残します。
<!--/-->

```agda
  θ⊆β : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ⟨ x ∈ˢ β ⟩
  θ⊆β x x∈θ =
    ∈∈ₛ {a = x} {b = β} .snd
      (separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .fst)

```

<!--en-->
The separating condition is recovered only as a truncated existence of an embedding; no concrete embedding is selected from it.
<!--zh-->
分离条件只以「嵌入的截断存在」被恢复；并不从中选定任何具体嵌入。
<!--ja-->
分出の条件は、埋め込みの切り詰められた存在としてのみ復元されます。具体的な埋め込みが選ばれることはありません。
<!--/-->

```agda
  θ-inj : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁
  θ-inj x x∈θ = separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .snd
```

<!--en-->
The separated set `θ` is an ordinal. Its transitivity is proved below. Each of its members is transitive because it is also a member of the ordinal `β`; together these are the two parts of `IsOrd θ`.
<!--zh-->
分离所得集合 `θ` 是序数。下文先证明它自身的传递性；它的每个成员又因同时属于序数 `β` 而是传递集。这两点合起来正是 `IsOrd θ`。
<!--ja-->
分出された集合 `θ` は順序数です。`θ` 自身の推移性は以下で示します。また、その各要素は順序数 `β` の要素でもあるため推移的です。この二つを合わせると `IsOrd θ` が得られます。
<!--/-->

```agda
  θ-ord : IsOrd θ
  θ-ord = trans , (λ x x∈θ → oβ .snd x (θ⊆β x x∈θ))
    where
    trans : isTransV θ
    trans {x} {y} y∈x x∈θ =
```

<!--en-->
To prove transitivity, take `y ∈ x ∈ θ`. Since `x` is a member of the ordinal bound, it is itself an ordinal, so membership gives an injection from `y` into `x`. Composing this with the merely existing injection from `x` into `a` yields the merely existing injection from `y` into `a`; transitivity of the bound also gives `y ∈ β`, so `θ-in` returns `y ∈ θ`.
<!--zh-->
为证传递性，取 `y ∈ x ∈ θ`。由于 `x` 是序数界的成员，它本身也是序数，所以隶属关系给出从 `y` 到 `x` 的单射。把它与仅仅存在的 `x` 到 `a` 的单射复合，得到仅仅存在的 `y` 到 `a` 的单射；界的传递性还给出 `y ∈ β`，于是 `θ-in` 得到 `y ∈ θ`。
<!--ja-->
推移性を示すため、`y ∈ x ∈ θ` とします。`x` は順序数である上界の要素なので、それ自身も順序数であり、所属から `y` から `x` への単射が得られます。これを、単に存在する `x` から `a` への単射と合成すると、単に存在する `y` から `a` への単射が得られます。また上界の推移性から `y ∈ β` も得られるため、`θ-in` により `y ∈ θ` となります。
<!--/-->

```agda
      θ-in y (oβ .fst y∈x (θ⊆β x x∈θ))
        (map₁
          (comp-inj (ord-emb y x (mem-ord {A = β} oβ x (θ⊆β x x∈θ)) y∈x))
          (θ-inj x x∈θ))
```

<!--en-->
The parameter `a` itself belongs to `θ` as soon as it belongs to the bound: the identity map witnesses its embedding into itself.
<!--zh-->
参数 `a` 一旦属于界，它就属于 `θ`：恒等映射见证它嵌入自身。
<!--ja-->
引数 `a` は、上界に属すれば `θ` にも属します。恒等写像が、自分自身への埋め込みを証明するからです。
<!--/-->

```agda
  a∈θ : ⟨ a ∈ˢ β ⟩ → ⟨ a ∈ˢ θ ⟩
  a∈θ a∈β = θ-in a a∈β ∣ (λ m → m) , (λ m n e → e) ∣₁
```

<!--en-->
Assume now that `θ ∈ β`. If `θ` injected into some `δ ∈ θ`, the separating condition for `δ` would merely supply an injection `δ ↪ a`. Composing inside the truncation gives an injection `θ ↪ a`; together with `θ ∈ β`, the separation rule would then place `θ` in itself, contradicting irreflexivity. Thus `θ` is an ambient cardinal.
<!--zh-->
现在假设 `θ ∈ β`。若 `θ` 能单射到某个 `δ ∈ θ`，则 `δ` 的分离条件仅仅给出单射 `δ ↪ a` 的存在。两者在截断内复合，得到单射 `θ ↪ a` 的存在；再结合 `θ ∈ β`，分离规则便推出 `θ ∈ θ`，与反自反性矛盾。因此 `θ` 是环境基数。
<!--ja-->
ここで `θ ∈ β` と仮定します。`θ` からある `δ ∈ θ` への単射があれば、`δ` の分出条件から、単射 `δ ↪ a` が単に存在することが得られます。切り詰めの中で両者を合成すると、単射 `θ ↪ a` が単に存在します。これと `θ ∈ β` を分出の規則に入れると `θ ∈ θ` となり、非反射性に矛盾します。したがって `θ` は周囲の基数です。
<!--/-->

```agda
  θ-card : ⟨ θ ∈ˢ β ⟩ → IsCardinal θ
  θ-card θ∈β δ δ∈θ f =
    ∈-irrefl θ (θ-in θ θ∈β (map₁ (comp-inj f) (θ-inj δ δ∈θ)))
```

<!--en-->
It remains to prove `θ ∈ β`, and one ordinal `γ ∈ β` with no injection into `a` is enough. Trichotomy compares the two ordinals `θ` and `β`; the next clauses eliminate equality and the case in which `β` lies below `θ`.
<!--zh-->
还需证明 `θ ∈ β`，而界内只要有一个不能单射到 `a` 的序数 `γ ∈ β` 即已足够。三分法比较序数 `θ` 与 `β`；接下来的分支将排除相等情形以及 `β` 位于 `θ` 之下的情形。
<!--ja-->
残る課題は `θ ∈ β` の証明であり、`a` へ単射できない順序数 `γ ∈ β` が一つあれば十分です。三分性によって二つの順序数 `θ` と `β` を比較し、次の各場合で等しい場合と `β` が `θ` より下にある場合を退けます。
<!--/-->

```agda
  θ∈β : (γ : SV.S) → ⟨ γ ∈ˢ β ⟩ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → ⊥₀)
      → ⟨ θ ∈ˢ β ⟩
  θ∈β γ γ∈β noinj = go (ord-tri θ θ-ord β oβ)
    where
    go : Tri θ β → ⟨ θ ∈ˢ β ⟩
```

<!--en-->
Trichotomy leaves only `θ ∈ β`. That case gives the result directly. If `θ ≡ β`, transporting `γ ∈ β` makes `γ` a member of `θ`; its separating condition then contradicts the assumed absence of an injection `γ ↪ a`. If `β ∈ θ`, the inclusion `θ ⊆ β` gives `β ∈ β`, again a contradiction. This locates `θ` below the chosen bound without asserting that it is the least ordinal with any property.
<!--zh-->
三分法中只有 `θ ∈ β` 能够成立，此时结论直接得到。若 `θ ≡ β`，沿等式运输 `γ ∈ β` 会使 `γ` 成为 `θ` 的成员；其分离条件随即与「不存在单射 `γ ↪ a`」的假设矛盾。若 `β ∈ θ`，包含关系 `θ ⊆ β` 又会推出 `β ∈ β`。因此这里只把 `θ` 定位在所选上界之下，并未断言它是满足某种性质的最小序数。
<!--ja-->
三分性のうち成立しうるのは `θ ∈ β` だけで、この場合は結論が直ちに得られます。`θ ≡ β` なら、`γ ∈ β` を等式に沿って運ぶことで `γ ∈ θ` となり、その分出条件が単射 `γ ↪ a` は存在しないという仮定に反します。`β ∈ θ` なら、包含 `θ ⊆ β` から `β ∈ β` が従い、やはり矛盾します。ここで示したのは `θ` が選んだ上界より下にあることだけで、何らかの性質をもつ最小の順序数だとは述べていません。
<!--/-->

```agda
    go (inl θ∈β')      = θ∈β'
    go (inr (inl e))   =
      ⊥₀-rec (rec₁ isProp⊥ noinj
        (θ-inj γ (subst (λ v → ⟨ γ ∈ˢ v ⟩) (sym e) γ∈β)))
    go (inr (inr β∈θ)) = ⊥₀-rec (∈-irrefl β (θ⊆β β β∈θ))
```

<!--en-->
## Reducing to an ambient bound
<!--zh-->
## 归结为环境上界
<!--ja-->
## 周囲の上界へ帰着する
<!--/-->

<!--en-->
The Hartogs input is stated in its weakest form: for every ordinal, some ordinal does not inject into it. No constructibility, no coding, and no leastness is carried by this type; the truncated existential names an ordinal and its non-injectivity alone.
<!--zh-->
Hartogs 输入以其最弱形式陈述：对每个序数，都存在某个序数不能单射入它。该类型不携带可构造性、编码或最小性；截断存在只命名一个序数及其不可注入性。
<!--ja-->
Hartogs の入力は、最も弱い形で述べられます。すべての順序数に対して、それに単射しない順序数が存在する、ということです。この型は構成可能性も符号化も最小性も運びません。切り詰められた存在が名指すのは、順序数とその非単射性だけです。
<!--/-->

```agda
NoInjOrd : Type (ℓ-suc ℓ)
NoInjOrd = (x : SV.S) → IsOrd x
         → ∥ Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ x ⟫ → ⊥₀)) ∥₁
```

<!--en-->
The positional lemma compares two ordinals and concludes that the first belongs to the second. Trichotomy decides three cases, and two of them are contradictory.
<!--zh-->
位置性引理比较两个序数并断言前者属于后者。三分法判定三种情形，其中两种矛盾。
<!--ja-->
位置づけの補題は、二つの順序数を比較し、最初のものが二つ目に属することを結論します。三岐性が三つの場合を判定し、そのうち二つは矛盾します。
<!--/-->

```agda
above : (a γ : SV.S) → IsOrd a → IsOrd γ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → ⊥₀)
      → ⟨ a ∈ˢ γ ⟩
above a γ oa oγ noinj = go (ord-tri γ oγ a oa)
  where
  idInj : ⟪ γ ⟫ ↪ ⟪ γ ⟫
```

<!--en-->
The identity injection of the ordinal into itself is named first. If the second ordinal were below the first, or equal to it, the transported injection would contradict the non-injectivity hypothesis.
<!--zh-->
先命名序数到其自身的恒等单射。若第二序数低于或等于第一序数，经搬运的单射将与不可注入假设矛盾。
<!--ja-->
まず、順序数から自分自身への恒等単射に名前を付けます。二つ目の順序数が一つ目より下か等しいなら、運ばれた単射が非単射性の仮定と矛盾します。
<!--/-->

```agda
  idInj = (λ m → m) , (λ m n e → e)
  go : Tri γ a → ⟨ a ∈ˢ γ ⟩
  go (inl γ∈a)      = ⊥₀-rec (noinj (ord-emb γ a oa γ∈a))
  go (inr (inl e))  =
    ⊥₀-rec (noinj (subst (λ v → ⟪ γ ⟫ ↪ ⟪ v ⟫) e idInj))
```

<!--en-->
Only the third case of the trichotomy survives, which is the announced membership.
<!--zh-->
只有三分法的第三种情形存留，即所宣告的隶属。
<!--ja-->
三岐性の三つ目の場合だけが残り、それが宣言された所属です。
<!--/-->

```agda
  go (inr (inr a∈γ)) = a∈γ
```

<!--en-->
Suppose an explicit ordinal `γ` with no injection into `a` has been given. The separated set formed from this witness is explicitly available and is proved to be an ordinal, an ambient cardinal, and strictly above `a`. The surrounding existence claim may still be truncated; this lemma itself maps an unpacked witness to an unpacked result.
<!--zh-->
设已显式给出一个不能单射到 `a` 的序数 `γ`。由该见证形成的分离集是显式可得的，并被证明是序数、环境基数且严格位于 `a` 之上。外围的存在陈述仍可带有命题截断；本引理只是把已拆出的见证映为已拆出的结果。
<!--ja-->
`a` へ単射できない順序数 `γ` が明示的に与えられたとします。この証人から作る分出集合は明示的に得られ、順序数であり、周囲の基数であり、`a` より真に大きいことが証明されます。外側の存在の主張は切り詰められていてもよく、この補題は取り出された証人を取り出された結果へ写します。
<!--/-->

```agda
cardAboveAt : (a : SV.S) → IsOrd a
  → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → ⊥₀))
  → Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
cardAboveAt a oa (γ , oγ , noinj) =
  S.θ , S.θ-ord , S.θ-card θ∈sγ , S.a∈θ a∈sγ
```

<!--en-->
Use the ordinal successor `sucV γ` as the bound for separation. The witness lies in its own successor. The lemma `above` gives `a ∈ γ`, and transitivity of the successor ordinal then also places `a` inside the bound.
<!--zh-->
取序数后继 `sucV γ` 作为分离所用的界。见证 `γ` 属于它自己的后继；引理 `above` 给出 `a ∈ γ`，再由后继序数的传递性得到 `a` 也属于该界。
<!--ja-->
分出の上界として順序数の後続 `sucV γ` を使います。証人 `γ` は自分自身の後続に属します。補題 `above` から `a ∈ γ` が得られ、後続順序数の推移性により `a` もこの上界に属します。
<!--/-->

```agda
  where
  module S = Sep a (sucV γ) (suc-ord oγ)
  γ∈sγ : ⟨ γ ∈ˢ sucV γ ⟩
  γ∈sγ = self∈sucV γ
  a∈sγ : ⟨ a ∈ˢ sucV γ ⟩
```

<!--en-->
The two needed side conditions now follow. From `a ∈ γ ∈ sucV γ` we obtain `a ∈ sucV γ`, so the identity injection places `a` in the separated set. The witness `γ ∈ sucV γ` and its failure to inject into `a` force the separated set itself to lie below the bound, enabling the cardinal proof.
<!--zh-->
所需的两个旁条件现在都可得到。由 `a ∈ γ ∈ sucV γ` 推出 `a ∈ sucV γ`，所以恒等单射把 `a` 放入分离集。另一方面，见证满足 `γ ∈ sucV γ` 且不能单射到 `a`，因而迫使分离集本身位于界内，使基数性证明得以应用。
<!--ja-->
必要な二つの条件がそろいます。`a ∈ γ ∈ sucV γ` から `a ∈ sucV γ` が得られるので、恒等単射によって `a` は分出集合に入ります。また、証人は `γ ∈ sucV γ` を満たし、`a` へ単射できないため、分出集合自身が上界の中にあることが強制され、基数性の証明を適用できます。
<!--/-->

```agda
  a∈sγ = suc-ord oγ .fst (above a γ oa oγ noinj) γ∈sγ
  θ∈sγ : ⟨ S.θ ∈ˢ sucV γ ⟩
  θ∈sγ = S.θ∈β γ γ∈sγ noinj

```

<!--en-->
The ambient existence theorem restores the truncation: from the Hartogs input, which supplies a witness for every ordinal, it produces, for the given ordinal `a`, the truncated ambient cardinal above it.
<!--zh-->
环境存在定理恢复截断：由对每个序数都供给见证的 Hartogs 输入，它为给定序数 `a` 产出其上方的环境基数的截断存在。
<!--ja-->
周囲の存在定理が切り詰めを回復します。すべての順序数に証人を供給する Hartogs の入力から、与えられた順序数 `a` の上の周囲の基数の、切り詰められた存在を産み出します。
<!--/-->

```agda
ambientCardAbove : NoInjOrd → (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁
ambientCardAbove ni a oa = map₁ (cardAboveAt a oa) (ni a oa)
```

<!--en-->
The ambient existence theorem is now transferred to `L`. Of the three mathematical hypotheses on `κ`, this construction uses its ordinality to invoke the ambient theorem. Its internal cardinality and its being outside `ω` are stronger assumptions of the stated result, appropriate to the later application to infinite cardinals, but no step of this existence proof consumes them.
<!--zh-->
现在把环境中的存在定理转入 `L`。关于 `κ` 的三项数学假设中，这个构造使用其序数性来调用环境定理。内部基数性以及 `κ` 不属于 `ω` 是所陈述结果保留的较强假设，适合稍后对无限基数的应用，但本存在性证明的步骤并未使用它们。
<!--ja-->
ここで、周囲での存在定理を `L` へ移します。`κ` に関する三つの数学的仮定のうち、この構成が周囲の定理を適用するために使うのは順序数性です。内部での基数性と `ω` に属さないことは、後で無限基数に適用するのに適した、定理のより強い仮定ですが、この存在証明の各段階では使われません。
<!--/-->

```agda
noInjOrd→CardAboveLᵀ : NoInjOrd → CardAboveLᵀ
noInjOrd→CardAboveLᵀ ni κ oκ cκ κ∉ω =
  map₁ build (ambientCardAbove ni (fst κ) oκ)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩)
```

<!--en-->
The ambient cardinal is presented as an element of `L` at its own successor stage, its cardinality is transported into the internal predicate by the one-directional comparison, and the membership of `κ` below it passes through unchanged.
<!--zh-->
环境基数在其自身后继层处呈现为 `L` 的元素，其基数性经单向比较转入内部谓词，而 `κ` 位于其下的隶属原样通过。
<!--ja-->
周囲の基数は、その自身の後続の段階で `L` の要素として提示され、その基数性は一方向の比較によって内部の述語へ運ばれ、`κ` がその下に属することはそのまま通ります。
<!--/-->

```agda
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , κ∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , κ∈θ
```

<!--en-->
## The Hartogs ordinal
<!--zh-->
## Hartogs 序数
<!--ja-->
## Hartogs 順序数
<!--/-->

<!--en-->
The Hartogs construction is organized in a module over an arbitrary ambient set `a`. It produces an ordinal that cannot inject into `a` without assuming that `a` is itself an ordinal; ordinality is required only later, when non-injectivity is converted into the strict comparison `a ∈ γ`.
<!--zh-->
Hartogs 构造在任意环境集合 `a` 上组织成一个模块。它不要求 `a` 本身是序数，就能产生一个不能单射到 `a` 的序数；只有稍后把不可注入性转成严格比较 `a ∈ γ` 时，才需要 `a` 的序数性。
<!--ja-->
Hartogs の構成は、任意の周囲の集合 `a` を引数とするモジュールにまとめられます。`a` 自身が順序数であると仮定せずに、`a` へ単射できない順序数を作ります。`a` の順序数性が必要になるのは、後で非単射性を厳密な比較 `a ∈ γ` へ変えるときだけです。
<!--/-->

```agda
module Hartogs (a : SV.S) where

```

<!--en-->
A relation on the presentation of `a` is a Boolean-valued function of two arguments.
<!--zh-->
`a` 的呈现上的关系是一个二元布尔值函数。
<!--ja-->
`a` の提示の上の関係は、二つの引数をもつブール値の関数です。
<!--/-->

```agda
  Rel : Type ℓ
  Rel = ⟪ a ⟫ → ⟪ a ⟫ → Bool

```

<!--en-->
A Boolean relation holds of two arguments when its value is the Boolean true; the reading is a proposition, since Booleans form a set.
<!--zh-->
布尔关系对其两个参数成立，当其取值为布尔真；由于布尔值构成集合，这一读取是命题。
<!--ja-->
ブールの関係が二つの引数について成立するのは、その値がブールの真であるときです。ブール値は集合を作るので、この読みは命題です。
<!--/-->

```agda
  Holds : Rel → ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ-zero
  Holds R x y = R x y ≡ true
```

<!--en-->
A well-founded relation on the presentation of `a` is a Boolean relation that is transitive and well-founded. It is not required to be linear or trichotomous, so a member of this type is not yet a well order.
<!--zh-->
`a` 的呈现上的良基关系是一个传递且良基的布尔关系。它不要求线性或三歧性，因此该类型的成员还不是良序。
<!--ja-->
`a` の提示の上の整礎的な関係とは、推移的かつ整礎的なブールの関係です。線形性や三岐性は要求されないので、この型の要素はまだ整列順序ではありません。
<!--/-->

```agda
  WFR : Type ℓ
  WFR = Σ[ R ∈ Rel ]
          ( ({x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z)
          × WellFounded (λ x y → Holds R x y) )

```

<!--en-->
Each well-founded Boolean relation is given its own collapse module.
<!--zh-->
每条良基布尔关系都配有自己的塌缩模块。
<!--ja-->
整礎的なブールの関係のそれぞれに、固有の崩壊のモジュールが用意されます。
<!--/-->

```agda
  module Col (w : WFR) where

```

<!--en-->
Fix one such relation `w`. Its first component is the Boolean relation `R`; the remaining components certify transitivity and well-foundedness. The collapse argument keeps these roles separate because the relation determines membership, while the proofs justify recursion and ordinal transitivity.
<!--zh-->
固定这样一条关系 `w`。它的第一分量是布尔关系 `R`，其余分量分别证明传递性与良基性。塌缩论证将这些作用分开：关系决定隶属，而证明保证递归有效并给出序数的传递性。
<!--ja-->
このような関係 `w` を一つ固定します。第一成分はブール関係 `R` であり、残りの成分が推移性と整礎性を保証します。崩壊の議論ではこれらの役割を分けます。関係が所属を定め、証明が再帰の正当性と順序数の推移性を与えるからです。
<!--/-->

```agda
    R : Rel
    R = fst w
```

<!--en-->
On the collapsed side, the relation is read through a lifted form of the Boolean holds, so that it lives at the level the Mostowski development expects.
<!--zh-->
在塌缩一侧，该关系以布尔成立的提升形式读取，从而居于 Mostowski 一章所期望的层级。
<!--ja-->
崩壊の側では、関係は、ブールが成立することを持ち上げた形で読まれます。これで、Mostowski の展開が期待するレベルに合うのです。
<!--/-->

```agda
    _≺_ : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ
    x ≺ y = Lift (Holds R x y)

```

<!--en-->
The lifted relation inherits transitivity from the original Bool-valued relation. Lowering the two lifted hypotheses exposes Boolean equalities that can be composed by the transitivity stored in `w`, and lifting the result returns it at the universe level required by the collapse.
<!--zh-->
提升后的关系继承原 Bool 值关系的传递性。先降低两条提升后的假设，便得到可由 `w` 中所存传递性复合的布尔等式；再提升结果，即回到塌缩所要求的宇宙层级。
<!--ja-->
持ち上げた関係は、もとの Bool 値関係から推移性を受け継ぎます。二つの仮定をいったん下ろすと、`w` に収められた推移性で合成できるブール等式が得られ、その結果を再び持ち上げれば、崩壊が要求する宇宙レベルに戻ります。
<!--/-->

```agda
    ≺-trans : {x y z : ⟪ a ⟫} → x ≺ y → y ≺ z → x ≺ z
    ≺-trans p q = lift (fst (snd w) (lower p) (lower q))

```

<!--en-->
Well-foundedness is preserved by the same change of universe. Starting from the accessibility tree for the Bool-valued relation, `go` recursively replaces every predecessor edge by its lifted counterpart, producing an accessibility tree for `_≺_`.
<!--zh-->
同样的宇宙层级变换也保持良基性。`go` 从 Bool 值关系的可及性树出发，递归地把每条前驱边换成其提升版本，从而得到 `_≺_` 的可及性树。
<!--ja-->
同じ宇宙レベルの変更によって整礎性も保たれます。`go` は Bool 値関係の到達可能性の木から出発し、各前者の辺を持ち上げた辺に再帰的に置き換えて、`_≺_` の到達可能性の木を作ります。
<!--/-->

```agda
    ≺-wf : WellFounded _≺_
    ≺-wf x = go x (snd (snd w) x)
      where
      go : (y : ⟪ a ⟫) → Acc (λ u v → Holds R u v) y → Acc _≺_ y
      go y (acc h) = acc (λ z k → go z (h z (lower k)))
```

<!--en-->
The lifted relation now meets the two hypotheses of the Mostowski construction: it is transitive and well founded. We may therefore use its collapse `col`; the accompanying laws describe membership in each collapse value and prove that every such value is an ordinal.
<!--zh-->
提升后的关系现已满足 Mostowski 构造的两项假设：它既传递又良基。因此可以使用其塌缩 `col`；配套定律刻画各塌缩值中的隶属关系，并证明每个塌缩值都是序数。
<!--ja-->
持ち上げた関係は、Mostowski の構成に必要な二つの仮定、すなわち推移性と整礎性を満たしました。そこで、その崩壊 `col` を使えます。付随する法則は各崩壊値の所属を記述し、すべての崩壊値が順序数であることを示します。
<!--/-->

```agda

    open Mostowski ⟪ a ⟫ _≺_ ≺-wf ≺-trans public
      using ( col; col-eq; col-in; col-out; col-ord )
```

<!--en-->
Collect all collapse values into their image `ot`. Although the name suggests an order type, an arbitrary member of `WFR` need not be a well order, and no uniqueness or isomorphism theorem is asserted here. What matters is simply that this image can be proved to be an ordinal.
<!--zh-->
把所有塌缩值收集为其像 `ot`。名称虽暗示序型，但 `WFR` 的任意成员未必是良序，此处也没有断言唯一性或同构定理。论证所需的只是证明这个像为序数。
<!--ja-->
すべての崩壊値を像 `ot` として集めます。この名前は順序型を思わせますが、`WFR` の任意の要素が整列順序であるとは限らず、ここでは一意性や同型に関する定理も主張しません。必要なのは、この像が順序数であることだけです。
<!--/-->

```agda
    ot : SV.S
    ot = sett ⟪ a ⟫ col

```

<!--en-->
Each `col p` belongs to the image. The displayed witness is the index `p` together with reflexivity, wrapped in propositional truncation because membership in an image remembers only that some preimage exists.
<!--zh-->
每个 `col p` 都属于该像。这里给出的见证是索引 `p` 与自反等式，并包在命题截断中，因为像中的隶属只保留某个原像存在这一事实。
<!--ja-->
各 `col p` はこの像に属します。ここで与える証人は添字 `p` と反射律であり、像への所属は逆像が存在することだけを残すため、命題的切り詰めで包まれています。
<!--/-->

```agda
    ot-in : (p : ⟪ a ⟫) → ⟨ col p ∈ˢ ot ⟩
    ot-in p = ∣ p , refl ∣₁

```

<!--en-->
The image is an ordinal. First, a member of the image is merely equal to some collapse value, hence is transitive because that collapse value is an ordinal. Second, the image itself is transitive: if `y ∈ x` and `x` is represented by `col p`, `col-out` merely presents `y` as `col r` for a predecessor `r`; the canonical image witness for `r` then puts `y` in `ot`. Both truncated existences are eliminated only into proposition-valued membership or transitivity goals.
<!--zh-->
这个像是序数。首先，像的成员仅仅等于某个塌缩值，而该塌缩值是序数，所以该成员传递。其次，像自身传递：若 `y ∈ x` 且 `x` 由 `col p` 表示，`col-out` 仅仅把 `y` 表示成某个前驱 `r` 的 `col r`；随后 `r` 的典范像见证便给出 `y ∈ ot`。两次截断存在都只消去到命题值的隶属或传递性目标中。
<!--ja-->
この像は順序数です。まず、像の要素はある崩壊値と単に等しく、その崩壊値が順序数なので、その要素は推移的です。次に、像そのものも推移的です。`y ∈ x` で、`x` が `col p` によって表されるなら、`col-out` は `y` をある前者 `r` の `col r` として命題的切り詰めのもとで提示します。そこで `r` に対する正準な像の証人から `y ∈ ot` が得られます。二つの切り詰められた存在はいずれも、命題値の所属または推移性の目標にだけ除去されます。
<!--/-->

```agda
    ot-ord : IsOrd ot
    ot-ord = tr , mem
      where
      mem : (x : SV.S) → ⟨ x ∈ˢ ot ⟩ → isTransV x
      mem x x∈ = rec₁ (isPropIsTransV x)
```

<!--en-->
The member's transitivity is transported from the collapse's ordinality along the presentation equation, and the outer elimination consumes the truncated decomposition of the member inside the image.
<!--zh-->
成员的传递性沿呈现等式从塌缩的序数性运输而来，而外层消去消耗该成员在像内截断的分解。
<!--ja-->
要素の推移性は、崩壊の順序数性から、提示の等式に沿って運ばれ、外側の消去が、像の中のその要素の切り詰められた分解を消費します。
<!--/-->

```agda
        (λ z → subst isTransV (snd z) (col-ord (fst z) .fst)) x∈
      tr : isTransV ot
      tr {x} {y} y∈x x∈ot = rec₁ (snd (y ∈ˢ ot)) outer x∈ot
        where
        outer : Σ[ p ∈ ⟪ a ⟫ ] (col p ≡ x) → ⟨ y ∈ˢ ot ⟩
```

<!--en-->
The truncated decomposition names an index `r` whose collapse is `y` and proves that `r` precedes `p`. The collapse law places `col r` in `col p`, while the canonical image witness `ot-in r` places `col r` in `ot`. Transport along the equation `col r ≡ y` therefore gives `y ∈ ot`.
<!--zh-->
截断的分解给出索引 `r`，使其坍缩为 `y`，并证明 `r` 先于 `p`。坍缩定律把 `col r` 放入 `col p`，而典范像见证 `ot-in r` 把 `col r` 放入 `ot`。沿等式 `col r ≡ y` 运输，便得到 `y ∈ ot`。
<!--ja-->
切り詰められた分解から、崩壊が `y` であり、かつ `p` に先行する添字 `r` が得られます。崩壊の法則は `col r` を `col p` に入れ、正準な像の証人 `ot-in r` は `col r` を `ot` に入れます。したがって、等式 `col r ≡ y` に沿って運べば `y ∈ ot` が得られます。
<!--/-->

```agda
        outer (p , e) =
          rec₁ (snd (y ∈ˢ ot))
            (λ z → subst (λ v → ⟨ v ∈ˢ ot ⟩) (snd (snd z)) (ot-in (fst z)))
            (col-out p y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))
```

<!--en-->
The Hartogs candidate `μ` is the union of the successors of all collapse images arising from `WFR`. Including each successor, rather than only the image itself, ensures that every `Col.ot w` is a strict member of the common bound. This construction bounds all such images without claiming that any of them is a uniquely determined order type.
<!--zh-->
Hartogs 候选 `μ` 是 `WFR` 所产生全部塌缩像的后继之并。纳入每个像的后继，而非仅纳入像本身，保证每个 `Col.ot w` 都严格属于这一公共上界。该构造界住所有这些像，却不声称其中任何一个是唯一确定的序型。
<!--ja-->
Hartogs の候補 `μ` は、`WFR` から得られるすべての崩壊像の後続の和集合です。像そのものだけでなく各像の後続を入れることで、すべての `Col.ot w` がこの共通上界に真に属することが保証されます。この構成はそれらの像を一括して抑えますが、どの像についても一意に定まる順序型だとは主張しません。
<!--/-->

```agda
  μ : SV.S
  μ = ⋃ (sett WFR (λ w → sucV (Col.ot w)))

```

<!--en-->
The bounding ordinal is an ordinal, proved by the bounding lemma from the fact that every member of the family is itself an ordinal.
<!--zh-->
上界序数是序数，由界引理从族中每个成员皆为序数这一事实证明。
<!--ja-->
上界の順序数は順序数です。族のすべての要素が順序数であるという事実から、上界の補題によって証明されます。
<!--/-->

```agda
  μ-ord : IsOrd μ
  μ-ord = boundingOrd WFR Col.ot Col.ot-ord .snd .fst

```

<!--en-->
For every `w : WFR`, its collapse image `Col.ot w` is a member of `μ`. This strict bound is the half of the final contradiction supplied in advance: once the opposite inclusion `μ ⊆ Col.ot w` is obtained for a relation pulled back from a hypothetical injection, self-membership follows.
<!--zh-->
对每个 `w : WFR`，其塌缩像 `Col.ot w` 都属于 `μ`。这个严格上界预先提供最终矛盾的一半：一旦对从假设单射拉回的关系得到反向包含 `μ ⊆ Col.ot w`，便会推出自隶属。
<!--ja-->
各 `w : WFR` について、その崩壊像 `Col.ot w` は `μ` に属します。この厳密な上界は、最後の矛盾の半分をあらかじめ与えます。仮定した単射から引き戻した関係について逆向きの包含 `μ ⊆ Col.ot w` が得られれば、自己所属が従います。
<!--/-->

```agda
  ot∈μ : (w : WFR) → ⟨ Col.ot w ∈ˢ μ ⟩
  ot∈μ = boundingOrd WFR Col.ot Col.ot-ord .snd .snd

```

<!--en-->
For any set `x` in the ambient cumulative hierarchy, its presentation type `⟪ x ⟫` embeds into the hierarchy itself. Since the hierarchy is an h-set, the presentation type is also an h-set. This lets ordinary injectivity into `⟪ a ⟫` be upgraded to proposition-valued fibres.
<!--zh-->
对环境累积层级中的任意集合 `x`，其呈现类型 `⟪ x ⟫` 都嵌入层级本身。层级是 h-集合，因此呈现类型也是 h-集合。于是，到 `⟪ a ⟫` 的普通单射性可以提升为纤维具有命题性。
<!--ja-->
周囲の累積階層の任意の集合 `x` について、その提示型 `⟪ x ⟫` は階層そのものへ埋め込まれます。階層は h-集合なので、提示型も h-集合です。これにより、`⟪ a ⟫` への通常の単射性を、ファイバーが命題であるという性質へ引き上げられます。
<!--/-->

```agda
  isSet⟪⟫ : (x : SV.S) → isSet ⟪ x ⟫
  isSet⟪⟫ x = Embedding-into-isSet→isSet (⟪ x ⟫↪ , isEmb⟪ x ⟫↪) setIsSet

```

<!--en-->
The decider converts a classical case split into a Boolean value, encoding the two branches as `true` and `false`.
<!--zh-->
判定器把经典情形分裂转为布尔值，将两支编码为 `true` 与 `false`。
<!--ja-->
判定器は、古典的な場合分けをブール値に変え、二つの分岐を `true` と `false` に符号化します。
<!--/-->

```agda
  decB : {A : Type ℓ} → (A ⊎ (A → ⊥₀)) → Bool
  decB (inl _) = true
  decB (inr _) = false

```

<!--en-->
The excluded-middle instance is lowered from the successor level to the working level, so that propositions living at the working level can be decided.
<!--zh-->
排中律实例从后继层级降到工作层级，使工作层级上的命题可被判定。
<!--ja-->
排中律の実例は、後続のレベルから作業のレベルへ降ろされ、作業のレベルに住む命題を判定できるようにします。
<!--/-->

```agda
  lemℓ : LEM ℓ
  lemℓ = lowerLEM lem
```

<!--en-->
Assume for contradiction an injection `f : ⟪ μ ⟫ ↪ ⟪ a ⟫`. The next construction transports membership among the presented members of `μ` to the image of this injection, producing one of the relations already included in the family `WFR`.
<!--zh-->
为导出矛盾，假设有单射 `f : ⟪ μ ⟫ ↪ ⟪ a ⟫`。接下来的构造把 `μ` 的呈现成员之间的隶属关系运到该单射的像上，从而得到一个已包含在 `WFR` 族中的关系。
<!--ja-->
矛盾を導くため、単射 `f : ⟪ μ ⟫ ↪ ⟪ a ⟫` があると仮定します。以下では、`μ` の提示された要素間の所属をこの単射の像へ移し、すでに族 `WFR` に含まれる関係を作ります。
<!--/-->

```agda
  module NoInj (f : ⟪ μ ⟫ ↪ ⟪ a ⟫) where

```

<!--en-->
The underlying function of the embedding is named once for the subsequent constructions.
<!--zh-->
嵌入的底层函数为后续构造只命名一次。
<!--ja-->
埋め込みの基礎となる関数が、以降の構成のために一度だけ名づけられます。
<!--/-->

```agda
    F : ⟪ μ ⟫ → ⟪ a ⟫
    F = fst f

```

<!--en-->
Because both the source and the target are h-sets, the injective function is an embedding: each fibre is a proposition.
<!--zh-->
由于源与目标都是 h-集合，单射函数是嵌入：每个纤维是命题。
<!--ja-->
源も目標も h-集合なので、単射な関数は埋め込みです。それぞれのファイバーは命題です。
<!--/-->

```agda
    F-emb : isEmbedding F
    F-emb = injEmbedding (isSet⟪⟫ a) (λ {x} {y} e → snd f x y e)

```

<!--en-->
The fibre over a point consists of an index of a member of `μ` together with an equation saying that `F` maps that index to the point. Thus an inhabitant of `Fib x` is precisely a presentation of `x` as lying in the image of `F`.
<!--zh-->
一点上的纤维由 `μ` 的成员索引以及一条等式组成，该等式说明 `F` 把这个索引映到该点。因此，`Fib x` 的元素恰好是 `x` 位于 `F` 的像中的一种呈现。
<!--ja-->
ある点上のファイバーは、`μ` の要素の添字と、`F` がその添字をその点へ写すことを示す等式からなります。したがって、`Fib x` の要素は、`x` が `F` の像に属することの提示にほかなりません。
<!--/-->

```agda
    Fib : ⟪ a ⟫ → Type ℓ
    Fib x = Σ[ m ∈ ⟪ μ ⟫ ] (F m ≡ x)

```

<!--en-->
Every fibre of `F` is a proposition. Consequently, whenever two pulled-back relation proofs present the same image point by possibly different indices, those fibre elements are equal. This uniqueness aligns their representatives; it does not choose a representative for points outside the image.
<!--zh-->
`F` 的每个纤维都是命题。因此，两条拉回关系证明即使以可能不同的索引表示同一个像点，这两个纤维元素也必然相等。这种唯一性用于对齐代表；它不会为像外的点选择代表。
<!--ja-->
`F` の各ファイバーは命題です。したがって、二つの引き戻し関係の証明が同じ像の点を異なるかもしれない添字で提示しても、それらのファイバー要素は等しくなります。この一意性は代表を揃えるために使われ、像の外の点に代表を選ぶものではありません。
<!--/-->

```agda
    isPropFib : (x : ⟪ a ⟫) → isProp (Fib x)
    isPropFib = isEmbedding→hasPropFibers F-emb

```

<!--en-->
The relation `PreT x y` first requires actual fibres witnessing that both `x` and `y` lie in the image of `F`. It then declares `x` to precede `y` exactly when the corresponding presented members of `μ` stand in the small membership relation. Points outside the image therefore have no predecessors in this relation.
<!--zh-->
关系 `PreT x y` 首先要求实际的纤维见证，说明 `x` 与 `y` 都在 `F` 的像中；随后规定，当且仅当相应的 `μ` 呈现成员满足小隶属关系时，`x` 先于 `y`。因此，像外的点在该关系中没有前驱。
<!--ja-->
関係 `PreT x y` はまず、`x` と `y` がともに `F` の像にあることを示す実際のファイバーを要求します。そのうえで、対応する `μ` の提示要素が小所属関係にあるとき、ちょうどそのときに `x` が `y` に先行すると定めます。したがって、像の外の点にはこの関係での前者がありません。
<!--/-->

```agda
    PreT : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ
    PreT x y = Σ[ p ∈ Fib x ] Σ[ q ∈ Fib y ]
                 ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q) ⟩

```

<!--en-->
The pulled-back predecessor relation is a proposition: it is built from two proposition fibres and one membership proposition.
<!--zh-->
拉回前驱关系是命题：由两个命题纤维与一个隶属命题构成。
<!--ja-->
引き戻された前者の関係は命題です。二つの命題であるファイバーと一つの所属の命題からできています。
<!--/-->

```agda
    isPropPreT : (x y : ⟪ a ⟫) → isProp (PreT x y)
    isPropPreT x y = isPropΣ (isPropFib x) λ p →
                     isPropΣ (isPropFib y) λ q →
                       snd (⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q))

```

<!--en-->
The Bool relation is the decidable encoding of the pulled-back predecessor relation, obtained by applying excluded middle to the proposition-valued relation.
<!--zh-->
布尔关系是拉回前驱关系的可判定编码，由对命题值关系应用排中律而得。
<!--ja-->
ブールの関係は、引き戻された前者の関係の、判定可能な符号化です。命題値の関係に排中律を適用することで得られます。
<!--/-->

```agda
    R : Rel
    R x y = decB (lemℓ (PreT x y , isPropPreT x y))

```

<!--en-->
If the Boolean relation holds, its value is `true`. Inspecting the excluded-middle decision then recovers `PreT x y`: the positive branch contains the desired proof, while the negative branch would force the Boolean value to be `false` and is therefore contradictory.
<!--zh-->
若布尔关系成立，其值便等于 `true`。检查排中律给出的判定即可恢复 `PreT x y`：肯定支含有所需证明；否定支会迫使布尔值为 `false`，因而导致矛盾。
<!--ja-->
ブール関係が成り立つなら、その値は `true` です。排中律による判定を調べると `PreT x y` を復元できます。肯定側には求める証明があり、否定側ではブール値が `false` になるため矛盾します。
<!--/-->

```agda
    R→Pre : (x y : ⟪ a ⟫) → Holds R x y → PreT x y
    R→Pre x y e = go (lemℓ (PreT x y , isPropPreT x y)) e
      where
      go : (d : PreT x y ⊎ (PreT x y → ⊥₀)) → decB d ≡ true → PreT x y
      go (inl h) _  = h
```

<!--en-->
The refutation branch is impossible: if the predecessor fact does not hold, the decider would have returned `false`, contradicting the `true` membership.
<!--zh-->
反驳支不可能：若前驱事实不成立，判定器将返回 `false`，与 `true` 隶属矛盾。
<!--ja-->
反駁の分岐は不可能です。前の事実が成立しなければ、判定器は `false` を返し、`true` の所属と矛盾します。
<!--/-->

```agda
      go (inr _) e' = ⊥₀-rec (false≢true e')

```

<!--en-->
The backward reading constructs the Boolean membership from the pulled-back predecessor fact, by the same classical decision.
<!--zh-->
向后读法由同一经典判定，从拉回前驱事实构造布尔隶属。
<!--ja-->
後ろ向きの読み出しは、同じ古典的な判定によって、引き戻された前者の事実からブールの所属を作ります。
<!--/-->

```agda
    Pre→R : (x y : ⟪ a ⟫) → PreT x y → Holds R x y
    Pre→R x y h = go (lemℓ (PreT x y , isPropPreT x y))
      where
      go : (d : PreT x y ⊎ (PreT x y → ⊥₀)) → decB d ≡ true
      go (inl _) = refl
```

<!--en-->
The empty branch is impossible: the predecessor fact holds by assumption.
<!--zh-->
空支不可能：前驱事实由假设成立。
<!--ja-->
空の分岐は不可能です。前の事実は仮定によって成立するからです。
<!--/-->

```agda
      go (inr n) = ⊥₀-rec (n h)
```

<!--en-->
To prove transitivity, decode `x R y` and `y R z` into two `PreT` witnesses. They contain four fibre witnesses: one over `x`, two over the shared middle point `y`, and one over `z`. Since the fibre over `y` is a proposition, its two witnesses are equal, so the corresponding members of `μ` can be aligned. Transitivity of the final represented member then composes the two membership steps, producing a `PreT` witness for `x R z`.
<!--zh-->
为证明传递性，先把 `x R y` 与 `y R z` 解读为两条 `PreT` 见证。它们共含四条纤维见证：`x` 上一条、共同中点 `y` 上两条、`z` 上一条。由于 `y` 上的纤维是命题，其中两条见证相等，因而可以对齐它们所表示的 `μ` 成员。随后利用最后一个表示成员的传递性复合两步隶属关系，得到 `x R z` 的 `PreT` 见证。
<!--ja-->
推移性を示すため、`x R y` と `y R z` を二つの `PreT` の証人として読み取ります。そこには四つのファイバーの証人があります。`x` 上に一つ、共通の中間点 `y` 上に二つ、`z` 上に一つです。`y` 上のファイバーは命題なので二つの証人は等しく、対応する `μ` の要素を揃えられます。そこで最後の提示要素の推移性を使って二段階の所属を合成すると、`x R z` に対する `PreT` の証人が得られます。
<!--/-->

```agda
    R-trans : {x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z
    R-trans {x} {y} {z} e1 e2 = Pre→R x z (p , r , goal)
      where
      d1 : PreT x y
      d1 = R→Pre x y e1
```

<!--en-->
Decoding the first relation gives indices `p` and `q` over `x` and `y`; decoding the second gives `q'` and `r` over `y` and `z`. Propositionality of the fibre over `y` identifies `q` with `q'`, allowing the membership represented by the first relation to be rewritten with the same middle index as the second.
<!--zh-->
解读第一条关系得到 `x` 与 `y` 上的索引 `p`、`q`；解读第二条关系得到 `y` 与 `z` 上的索引 `q'`、`r`。`y` 上纤维的命题性把 `q` 与 `q'` 认同，因而可将第一条关系所表示的隶属改写为使用与第二条关系相同的中间索引。
<!--ja-->
第一の関係を読み取ると、`x` と `y` 上の添字 `p`、`q` が得られ、第二の関係からは `y` と `z` 上の添字 `q'`、`r` が得られます。`y` 上のファイバーが命題であることから `q` と `q'` が同一視され、第一の関係が表す所属を、第二の関係と同じ中間の添字を使う形に書き換えられます。
<!--/-->

```agda
      d2 : PreT y z
      d2 = R→Pre y z e2
      p  = fst d1
      q  = fst (snd d1)
      q' = fst d2
```

<!--en-->
The final member `r` is named, and its transitivity is read from the ordinality of `μ`.
<!--zh-->
最终成员 `r` 被命名，其传递性由 `μ` 的序数性读取。
<!--ja-->
最後の要素 `r` が名づけられ、その推移性は `μ` の順序数性から読まれます。
<!--/-->

```agda
      r  = fst (snd d2)
      h1' : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q') ⟩
      h1' = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
              (isPropFib y q q') (snd (snd d1))
      rTr : isTransV (⟪ μ ⟫↪ (fst r))
```

<!--en-->
The composition of the two membership relations through the transitivity of `r` produces the goal: the first member is inside the third member, which is what the pulled-back relation requires.
<!--zh-->
两条隶属关系经 `r` 的传递性复合产出目标：第一成员在第三成员之内，这正是拉回关系所需的。
<!--ja-->
二つの所属の関係を、`r` の推移性を通して合成すると、目標が作られます。第一の要素が第三の要素の中にあること、これが引き戻された関係の要求です。
<!--/-->

```agda
      rTr = μ-ord .snd (⟪ μ ⟫↪ (fst r)) (member μ (fst r))
      goal : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst r) ⟩
      goal = ∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst r)} .fst
        (rTr (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst q')} .snd h1')
             (∈∈ₛ {a = ⟪ μ ⟫↪ (fst q')} {b = ⟪ μ ⟫↪ (fst r)} .snd (snd (snd d2))))
```

<!--en-->
Well-foundedness is transported along the injection from the ambient hierarchy's regularity. The auxiliary lemma handles the case where the target is known to equal a specific hierarchy element.

The auxiliary proof constructs accessibility for each predecessor of the given member.
<!--zh-->
良基性由环境层级中正则公理所给的良基性沿嵌入搬运。辅助引理处理目标已知等于特定层级元素的情形。

辅助证明为给定成员的每个前驱构造可达性。
<!--ja-->
整礎性は、周囲の階層の正則性から、埋め込みに沿って運ばれます。補助の補題は、目標が特定の階層の要素と等しい場合を扱います。

補助の証明は、与えられた要素のそれぞれの前者に対して、アクセス可能性を構成します。
<!--/-->

```agda
    wfAux : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
          → Acc (λ x y → Holds R x y) (F m)
    wfAux v (acc rec) m e = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r (F m) → Acc (λ x y → Holds R x y) r
```

<!--en-->
Each predecessor `r` of the member is decomposed into two `μ` members connected by the pulled-back relation, and the accessibility is transported to the first component.
<!--zh-->
成员的每个前驱 `r` 被分解为由拉回关系连接的两个 `μ` 成员，可达性被运到第一分量。
<!--ja-->
要素のそれぞれの前者 `r` は、引き戻された関係で結ばれた二つの `μ` の要素に分解され、アクセス可能性は第一の成分へ運ばれます。
<!--/-->

```agda
      go r rr = subst (Acc (λ x y → Holds R x y)) (snd p)
                  (wfAux (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below)
                     (fst p) refl)
        where
        d : PreT r (F m)
```

<!--en-->
The predecessor fact is decomposed to name two internal indices: `p` presents the predecessor `r` inside `μ`, and `q` presents the target `F m` inside `μ`. The transported equation identifies the two presentations of the middle member.
<!--zh-->
前驱事实给出 `p` 与 `q`：`p` 是 `r` 在 `μ` 中的代表，`q` 是 `F m` 在 `μ` 中的代表。
<!--ja-->
前の事実から、`p` と `q` が得られます。`p` は `r` の `μ` の中の代表であり、`q` は `F m` の `μ` の中の代表です。
<!--/-->

```agda
        d = R→Pre r (F m) rr
        p = fst d
        q = fst (snd d)
        h : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
        h = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
```

<!--en-->
The two fibre witnesses over `F m` are equal because that fibre is a proposition. Transporting along this equality rewrites the decoded relation as membership of the predecessor represented by `p` in the member represented by `m`. The equation identifying that latter member with `v` then places the predecessor strictly below `v`, where the accessibility recursion applies.
<!--zh-->
`F m` 上的两条纤维见证相等，因为该纤维是命题。沿这一等式运输，可把解读出的关系改写为：`p` 所表示的前驱属于 `m` 所表示的成员。再利用后一个成员与 `v` 的等式，便把前驱严格置于 `v` 之下，从而可以应用可达性递归。
<!--ja-->
`F m` 上の二つのファイバーの証人は、そのファイバーが命題なので等しくなります。この等式に沿って運ぶと、読み取った関係は、`p` が表す先行要素が `m` の表す要素に属するという形に書き換えられます。後者を `v` と同定する等式によって先行要素は `v` より真に下に置かれ、そこで到達可能性の再帰を適用できます。
<!--/-->

```agda
              (isPropFib (F m) q (m , refl)) (snd (snd d))
        below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                  (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd h)

```

<!--en-->
Well-foundedness of the pulled-back relation follows from the regularity of the ambient hierarchy: each predecessor of any member lies strictly below some hierarchy element, and the auxiliary lemma produces accessibility there.
<!--zh-->
拉回关系的良基性来自环境层级的正则公理：任何成员的每个前驱都严格低于某个层级元素，辅助引理在该处产出可达性。
<!--ja-->
引き戻された関係の整礎性は、周囲の階層の正則性から従います。ある要素のそれぞれの前者は、ある階層の要素より厳密に下にあり、補助の補題がそこでアクセス可能性を作ります。
<!--/-->

```agda
    R-wf : WellFounded (λ x y → Holds R x y)
    R-wf x = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r x → Acc (λ u v → Holds R u v) r
      go r rr = subst (Acc (λ u v → Holds R u v)) (snd p)
```

<!--en-->
For an arbitrary predecessor `r` of `x`, decoding the relation supplies a fibre witness `p` over `r`. Regularity gives accessibility of the hierarchy element represented by its index, and `wfAux` transfers that accessibility back to the point `F (fst p)`. The fibre equation identifies this point with `r`, completing the required accessibility proof.
<!--zh-->
对 `x` 的任意前驱 `r`，解读该关系会给出 `r` 上的纤维见证 `p`。正则公理给出其索引所表示的层级元素的可达性，`wfAux` 再把这份可达性传回点 `F (fst p)`。纤维等式把该点与 `r` 认同，从而完成所需的可达性证明。
<!--ja-->
`x` の任意の先行要素 `r` に対して、関係を読み取ると `r` 上のファイバーの証人 `p` が得られます。正則性は、その添字が表す階層の要素の到達可能性を与え、`wfAux` がその到達可能性を点 `F (fst p)` へ移します。ファイバーの等式がこの点を `r` と同定し、必要な到達可能性の証明が完成します。
<!--/-->

```agda
                  (wfAux (⟪ μ ⟫↪ (fst p)) (regularityV (⟪ μ ⟫↪ (fst p)))
                     (fst p) refl)
        where
        p = fst (R→Pre r x rr)

```

<!--en-->
The well-founded transitive relation is packaged with its two proofs, completing the well-founded relation family that the bounding ordinal ranges over.
<!--zh-->
良基传递关系连同其两条证明被打包，完成上界序数所遍历的良基关系族。
<!--ja-->
整礎で推移的な関係が、その二つの証明とともにまとめられ、上界の順序数がわたる整礎な関係の族が完成します。
<!--/-->

```agda
    w : WFR
    w = R , R-trans , R-wf

```

<!--en-->
Apply the collapse construction to the particular relation `w` obtained from the hypothetical injection. Its collapse values and their image will now be compared directly with the presented members of `μ`; no claim that `w` is a well order is needed.
<!--zh-->
把塌缩构造应用于由假设单射得到的特定关系 `w`。下文将直接比较其塌缩值及其像与 `μ` 的呈现成员；论证不需要声称 `w` 是良序。
<!--ja-->
仮定した単射から得た特定の関係 `w` に崩壊の構成を適用します。以下では、その崩壊値と像を `μ` の提示要素と直接比較します。`w` が整列順序であるという主張は必要ありません。
<!--/-->

```agda
    open Col w using ( col; col-in; col-out; ot; ot-in; _≺_ )
```

<!--en-->
The key lemma says that the collapse of the pullback relation reproduces the members of the bounding ordinal: for each `μ` member presented as a hierarchy element, the collapse of its image equals that element. The proof is by well-founded induction on the hierarchy element.

The proof compares members by extensionality in two directions.
<!--zh-->
关键引理说：拉回关系的塌缩重现了上界序数的成员。对呈现为层级元素的每个 `μ` 成员，其像的塌缩等于该元素。证明是对层级元素的良基归纳。

证明在两个方向上以外延性比较成员。
<!--ja-->
重要な補題はこう言います。引き戻された関係の崩壊は、上界の順序数の要素を再現します。階層の要素として提示された `μ` の各要素について、その像の崩壊はその要素に等しい、と。証明は、階層の要素の上の整礎帰納です。

証明は、二方向で外延性によって要素を比較します。
<!--/-->

```agda
    key : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
        → col (F m) ≡ ⟪ μ ⟫↪ m
    key v (acc rec) m e =
      extensionality (col (F m)) (⟪ μ ⟫↪ m) (fwd , bwd)
      where
```

<!--en-->
For the forward inclusion, suppose `b` belongs to `col (F m)`. The elimination law `col-out` says merely that `b` is the collapse of some predecessor `r` of `F m`. Decoding that predecessor through `PreT` reveals an index below `m`; the induction hypothesis will identify its represented member with `col r` and hence with `b`.
<!--zh-->
先证向前包含。设 `b` 属于 `col (F m)`。消去定律 `col-out` 仅仅断言：`b` 是 `F m` 的某个前驱 `r` 的塌缩值。经 `PreT` 解码此前驱，可得到一个位于 `m` 之下的索引；归纳假设将把该索引所表示的成员与 `col r`，继而与 `b` 认同。
<!--ja-->
まず順方向の包含を示します。`b` が `col (F m)` に属するとします。除去則 `col-out` は、`b` が `F m` のある前者 `r` の崩壊値であることを命題的切り詰めのもとで述べます。その前者を `PreT` で読み取ると `m` より下の添字が得られ、帰納の仮定が、その添字の表す要素を `col r`、したがって `b` と同一視します。
<!--/-->

```agda
      fwd : (b : SV.S) → ⟨ b ∈ₛ col (F m) ⟩ → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
      fwd b b∈ = rec₁ (snd (b ∈ₛ ⟪ μ ⟫↪ m)) go
                   (col-out (F m) b (∈∈ₛ {a = b} {b = col (F m)} .snd b∈))
        where
        go : Σ[ r ∈ ⟪ a ⟫ ] ((r ≺ F m) × (col r ≡ b))
```

<!--en-->
The predecessor witness consists of `r ≺ F m` and an equation `col r ≡ b`. Reading the relation proof back through `R→Pre` yields fibres for `r` and `F m`; their indices identify the corresponding presented members of `μ`, while the final component records membership between them.
<!--zh-->
前驱见证由 `r ≺ F m` 与等式 `col r ≡ b` 组成。经 `R→Pre` 读回关系证明，可得到 `r` 与 `F m` 的纤维；其中的索引标识相应的 `μ` 呈现成员，最后一个分量则记录二者之间的隶属。
<!--ja-->
前者の証人は `r ≺ F m` と等式 `col r ≡ b` からなります。関係の証明を `R→Pre` で読み戻すと、`r` と `F m` のファイバーが得られます。その添字は対応する `μ` の提示要素を示し、最後の成分はそれらの間の所属を記録します。
<!--/-->

```agda
           → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
        go (r , rr , cr) = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (cpr ∙ cr) hh
          where
          d = R→Pre r (F m) (lower rr)
          p = fst d
```

<!--en-->
The fibre over `F m` is proposition-valued, so the representative `q` obtained from the relation proof equals the evident representative `(m , refl)`. Transport along this equality turns the decoded membership into the statement that the predecessor index lies inside the set represented by `m`.
<!--zh-->
`F m` 上的纤维具有命题性，所以由关系证明得到的代表 `q` 等于显然的代表 `(m , refl)`。沿此等式运输，解码后的隶属便成为「前驱索引属于 `m` 所表示的集合」这一陈述。
<!--ja-->
`F m` 上のファイバーは命題なので、関係の証明から得た代表 `q` は明らかな代表 `(m , refl)` と等しくなります。この等式に沿って輸送すると、読み取った所属は、前者の添字が `m` の表す集合に属すという主張になります。
<!--/-->

```agda
          q = fst (snd d)
          hh : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
          hh = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
                 (isPropFib (F m) q (m , refl)) (snd (snd d))
          below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
```

<!--en-->
Using the equation `⟪ μ ⟫↪ m ≡ v`, this membership places the predecessor's represented set below `v` in ambient membership. The recursive hypothesis is therefore available at that predecessor and identifies its collapse with its represented set.
<!--zh-->
利用等式 `⟪ μ ⟫↪ m ≡ v`，上述隶属把前驱所表示的集合置于环境隶属中的 `v` 之下。因此可以在此前驱处使用递归假设，把其塌缩值与其所表示的集合认同。
<!--ja-->
等式 `⟪ μ ⟫↪ m ≡ v` を使うと、この所属は前者の表す集合を周囲の所属における `v` の下に置きます。したがって、その前者で再帰の仮定を使い、その崩壊値を提示された集合と同一視できます。
<!--/-->

```agda
          below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                    (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd hh)
          ih : col (F (fst p)) ≡ ⟪ μ ⟫↪ (fst p)
          ih = key (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below) (fst p) refl
          cpr : ⟪ μ ⟫↪ (fst p) ≡ col r
```

<!--en-->
The induction hypothesis identifies the collapse of the decoded index with the member represented by that index. Since the fibre equation also identifies its image with `r`, congruence of `col` yields the required equation between the represented member and `col r`; composing with `col r ≡ b` completes the forward inclusion.
<!--zh-->
归纳假设把解码索引的塌缩值与该索引所表示的成员认同。纤维等式又把该索引的像与 `r` 认同，因此对 `col` 使用同余便得到呈现成员与 `col r` 之间所需的等式；再与 `col r ≡ b` 复合，即完成向前包含。
<!--ja-->
帰納の仮定は、復号された添字の崩壊値を、その添字が表す要素と同一視します。ファイバーの等式はさらに、その添字の像を `r` と同一視します。そこで `col` の合同性を使うと、提示要素と `col r` の間の必要な等式が得られ、これを `col r ≡ b` と合成すれば順方向の包含が完了します。
<!--/-->

```agda
          cpr = sym ih ∙ cong col (snd p)

```

<!--en-->
For the reverse inclusion, begin with `b` as a member of the set represented by `m`. The aim is to exhibit `b` as a member of `col (F m)`. Transitivity of the ordinal `μ` first promotes `b` to membership in `μ`, allowing its canonical presentation to supply an index `k` for `b`.
<!--zh-->
再证反向包含。现从 `b` 属于索引 `m` 所表示的集合出发，目标是证明 `b ∈ col (F m)`。序数 `μ` 的传递性先把 `b` 提升为 `μ` 的成员，于是 `μ` 的典范呈现可以给出表示 `b` 的索引 `k`。
<!--ja-->
次に逆方向の包含を示します。`b` が添字 `m` の表す集合に属すると仮定し、`b ∈ col (F m)` を目指します。まず順序数 `μ` の推移性により `b` は `μ` の要素でもあるので、`μ` の正準な提示から `b` を表す添字 `k` が得られます。
<!--/-->

```agda
      bwd : (b : SV.S) → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩ → ⟨ b ∈ₛ col (F m) ⟩
      bwd b b∈ = ∈∈ₛ {a = b} {b = col (F m)} .fst
                   (subst (λ t → ⟨ t ∈ˢ col (F m) ⟩) (ihk ∙ ek) inCol)
        where
        b∈ˢ : ⟨ b ∈ˢ ⟪ μ ⟫↪ m ⟩
```

<!--en-->
Here `fiber μ b∈μ` returns an actual index `k` and an equation `⟪ μ ⟫↪ k ≡ b`. This is possible because small membership `_∈ₛ_` is based on the proposition-valued fibre of the canonical presentation. It is a local inverse to that presentation, not a choice from an arbitrary truncated existence.
<!--zh-->
这里 `fiber μ b∈μ` 返回实际索引 `k` 与等式 `⟪ μ ⟫↪ k ≡ b`。这是因为小隶属 `_∈ₛ_` 基于典范呈现中具有命题性的纤维。它是该呈现的局部逆过程，并非从任意截断存在中作选择。
<!--ja-->
ここで `fiber μ b∈μ` は、実際の添字 `k` と等式 `⟪ μ ⟫↪ k ≡ b` を返します。小所属 `_∈ₛ_` が正準な提示の命題値ファイバーに基づくためです。これはその提示に対する局所的な逆操作であり、任意の切り詰められた存在からの選択ではありません。
<!--/-->

```agda
        b∈ˢ = ∈∈ₛ {a = b} {b = ⟪ μ ⟫↪ m} .snd b∈
        b∈μ : ⟨ b ∈ˢ μ ⟩
        b∈μ = μ-ord .fst b∈ˢ (member μ m)
        fb = fiber μ b∈μ
        k = fst fb
```

<!--en-->
The equation returned by `fiber` lets us rewrite the original membership `b ∈ ⟪ μ ⟫↪ m` as membership of the represented element `⟪ μ ⟫↪ k`. The evident fibres `(k , refl)` and `(m , refl)`, together with this membership, then establish `PreT (F k) (F m)`.
<!--zh-->
`fiber` 返回的等式把原有隶属 `b ∈ ⟪ μ ⟫↪ m` 改写为呈现元素 `⟪ μ ⟫↪ k` 的隶属。随后，显然的两个纤维 `(k , refl)`、`(m , refl)` 与这条隶属共同建立 `PreT (F k) (F m)`。
<!--ja-->
`fiber` が返す等式により、もとの所属 `b ∈ ⟪ μ ⟫↪ m` を、提示要素 `⟪ μ ⟫↪ k` の所属として書き換えられます。そこで、明らかな二つのファイバー `(k , refl)`、`(m , refl)` とこの所属から `PreT (F k) (F m)` が得られます。
<!--/-->

```agda
        ek : ⟪ μ ⟫↪ k ≡ b
        ek = snd fb
        k∈m : ⟨ ⟪ μ ⟫↪ k ∈ₛ ⟪ μ ⟫↪ m ⟩
        k∈m = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (sym ek) b∈
        pre : PreT (F k) (F m)
```

<!--en-->
Encoding this `PreT` fact as the Bool relation gives `F k ≺ F m`. The collapse introduction law therefore places `col (F k)` inside `col (F m)`. At the same time, the membership of the represented element below `m` places it below the induction parameter `v`, so the recursive hypothesis applies to `k`.
<!--zh-->
把这条 `PreT` 事实编码为 Bool 关系，可得 `F k ≺ F m`。因此，塌缩引入定律把 `col (F k)` 放入 `col (F m)`。与此同时，呈现元素属于 `m` 所表示集合这一事实把它置于归纳参数 `v` 之下，所以递归假设可用于 `k`。
<!--ja-->
この `PreT` の事実を Bool 関係に符号化すると `F k ≺ F m` が得られます。したがって、崩壊の導入則により `col (F k)` は `col (F m)` に属します。同時に、提示要素が `m` の表す集合に属すことから、それは帰納の引数 `v` より下にあるので、再帰の仮定を `k` に適用できます。
<!--/-->

```agda
        pre = (k , refl) , ((m , refl) , k∈m)
        inCol : ⟨ col (F k) ∈ˢ col (F m) ⟩
        inCol = col-in (F m) (F k) (lift (Pre→R (F k) (F m) pre))
        below : ⟪ μ ⟫↪ k SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ k ∈ˢ t ⟩) e
```

<!--en-->
The recursive hypothesis gives `col (F k) ≡ ⟪ μ ⟫↪ k`. Composing this with the fibre equation `⟪ μ ⟫↪ k ≡ b` transports the membership just constructed to `b ∈ col (F m)`, completing the reverse inclusion.
<!--zh-->
递归假设给出 `col (F k) ≡ ⟪ μ ⟫↪ k`。把它与纤维等式 `⟪ μ ⟫↪ k ≡ b` 复合，便可把刚构造的隶属运输为 `b ∈ col (F m)`，从而完成反向包含。
<!--ja-->
再帰の仮定から `col (F k) ≡ ⟪ μ ⟫↪ k` が得られます。これをファイバーの等式 `⟪ μ ⟫↪ k ≡ b` と合成し、先ほど作った所属を `b ∈ col (F m)` へ輸送すれば、逆方向の包含が完了します。
<!--/-->

```agda
                  (∈∈ₛ {a = ⟪ μ ⟫↪ k} {b = ⟪ μ ⟫↪ m} .snd k∈m)
        ihk : col (F k) ≡ ⟪ μ ⟫↪ k
        ihk = key (⟪ μ ⟫↪ k) (rec (⟪ μ ⟫↪ k) below) k refl

```

<!--en-->
Regularity supplies the accessibility proof needed to specialize the induction to every index `m` of `μ`. Thus `key'` identifies `col (F m)` with the member represented by `m`. The next part of the proof will use these pointwise equalities to establish the inclusion `μ ⊆ Col.ot w`; that inclusion has not yet been asserted here.
<!--zh-->
正则公理为 `μ` 的每个索引 `m` 提供专门化该归纳所需的可及性证明。因此，`key'` 把 `col (F m)` 与 `m` 所表示的成员认同。证明的下一部分才会用这些逐点等式建立包含 `μ ⊆ Col.ot w`；此处尚未断言该包含。
<!--ja-->
正則性は、`μ` の各添字 `m` で帰納を特殊化するための到達可能性の証明を与えます。したがって `key'` は `col (F m)` を `m` が表す要素と同一視します。証明の次の部分で、これらの各点の等式から包含 `μ ⊆ Col.ot w` を導きます。この時点ではまだその包含を主張していません。
<!--/-->

```agda
    key' : (m : ⟪ μ ⟫) → col (F m) ≡ ⟪ μ ⟫↪ m
    key' m = key (⟪ μ ⟫↪ m) (regularityV (⟪ μ ⟫↪ m)) m refl
```

<!--en-->
Every member `b` of `μ` also belongs to the collapse image `ot`. The canonical fibre of `μ` at `b` supplies an index `m` with `⟪ μ ⟫↪ m ≡ b`. The lemma `key'` identifies that representative with `col (F m)`, while `ot-in` places this collapse value in `ot`; transport along the two equalities yields `b ∈ ot`.

Thus the argument establishes only the inclusion `μ ⊆ ot`. Together with `ot ∈ μ`, this inclusion will already be enough for the contradiction, so no equality or order isomorphism between `μ` and `ot` is required.
<!--zh-->
`μ` 的每个成员 `b` 也属于坍缩像 `ot`。`μ` 在 `b` 处的典范纤维给出索引 `m`，满足 `⟪ μ ⟫↪ m ≡ b`。引理 `key'` 把这个代表与 `col (F m)` 识别，而 `ot-in` 把该坍缩值放入 `ot`；沿这两个等式传输，便得到 `b ∈ ot`。

因此，这段论证只建立包含关系 `μ ⊆ ot`。结合 `ot ∈ μ`，这一包含关系已经足以导出矛盾，无须证明 `μ` 与 `ot` 相等或序同构。
<!--ja-->
`μ` の各要素 `b` は崩壊像 `ot` にも属します。`b` における `μ` の正準なファイバーから、`⟪ μ ⟫↪ m ≡ b` を満たす添字 `m` が得られます。補題 `key'` はこの代表を `col (F m)` と同定し、`ot-in` はその崩壊値を `ot` に入れます。二つの等式に沿って輸送すれば `b ∈ ot` が得られます。

したがって、ここで示されるのは包含 `μ ⊆ ot` だけです。これと `ot ∈ μ` を合わせれば矛盾には十分であり、`μ` と `ot` の等しさや順序同型を示す必要はありません。
<!--/-->

```agda
    μ⊆ot : (b : SV.S) → ⟨ b ∈ˢ μ ⟩ → ⟨ b ∈ˢ ot ⟩
    μ⊆ot b b∈μ =
      subst (λ t → ⟨ t ∈ˢ ot ⟩) (key' (fst fb) ∙ snd fb)
        (ot-in (F (fst fb)))
      where
```

<!--en-->
The canonical presentation has proposition-valued fibres, so the representative recovered for `b` is uniquely determined. Keeping that representative and its equation together as `fb` supplies exactly the index used by both `key'` and `ot-in` in the preceding inclusion proof.
<!--zh-->
典范呈现的纤维具有命题性，因此为 `b` 恢复出的代表唯一确定。把这个代表及其等式合记为 `fb`，便同时为前述包含证明中的 `key'` 与 `ot-in` 提供所需索引。
<!--ja-->
正準な提示のファイバーは命題なので、`b` に対して復元される代表は一意に定まります。その代表と等式をまとめて `fb` として保持することで、直前の包含証明における `key'` と `ot-in` の両方に必要な添字が得られます。
<!--/-->

```agda
      fb = fiber μ b∈μ
```

<!--en-->
By construction of the bound, `ot` is a member of `μ`. Applying the inclusion `μ ⊆ ot` to that particular member gives `ot ∈ ot`, contradicting the irreflexivity of membership. This closes the contradiction generated by the assumed injection `μ ↪ a`.
<!--zh-->
由上界的构造，`ot` 是 `μ` 的成员。把包含关系 `μ ⊆ ot` 用于这个特定成员，便得到 `ot ∈ ot`，与隶属关系的非自反性矛盾。这样，由假设的单射 `μ ↪ a` 所引出的矛盾便告完成。
<!--ja-->
上界の構成により、`ot` は `μ` の要素です。この要素に包含 `μ ⊆ ot` を適用すると `ot ∈ ot` が得られ、所属関係の非反射性に反します。これで、仮定した単射 `μ ↪ a` から生じる矛盾が完成します。
<!--/-->

```agda
    absurd : ⊥₀
    absurd = ∈-irrefl ot (μ⊆ot ot (ot∈μ w))
```

<!--en-->
The local contradiction was proved under an arbitrary injection `f : ⟪ μ ⟫ ↪ ⟪ a ⟫`. The theorem `noInj` now exposes that conclusion at the boundary of the Hartogs module: every proposed injection supplies the pullback relation above and therefore leads to `⊥*`.
<!--zh-->
上述局部矛盾是在任意单射 `f : ⟪ μ ⟫ ↪ ⟪ a ⟫` 的假设下证明的。定理 `noInj` 现在把这一结论带到 Hartogs 模块的接口上：每一条候选单射都会给出上面的拉回关系，因而导出 `⊥*`。
<!--ja-->
上の局所的な矛盾は、任意の単射 `f : ⟪ μ ⟫ ↪ ⟪ a ⟫` を仮定して証明されました。定理 `noInj` はこの結論を Hartogs モジュールの外部へ提示します。どの単射を仮定しても、上で用いた引き戻し関係が得られ、したがって `⊥*` に至ります。
<!--/-->

```agda
  noInj : (⟪ μ ⟫ ↪ ⟪ a ⟫) → ⊥₀
  noInj f = NoInj.absurd f
```

<!--en-->
## The larger L-cardinal
<!--zh-->
## 所得的更大 L 基数
<!--ja-->
## 得られた大きい L 基数
<!--/-->

<!--en-->
For each ordinal `x`, the explicit object `Hartogs.μ x` is an ordinal and admits no injection into `x`. These three pieces are then placed under propositional truncation to satisfy `NoInjOrd`. The construction therefore provides a definite witness before packaging it, while callers receive only its truncated existence.
<!--zh-->
对每个序数 `x`，显式对象 `Hartogs.μ x` 是序数，并且不能单射入 `x`。随后把这个对象及其序数性和不可注入性置于命题截断之下，便得到 `NoInjOrd`。因此，打包之前已有确定的见证，而调用者只取得它的截断存在性。
<!--ja-->
各順序数 `x` に対して、明示的な対象 `Hartogs.μ x` は順序数であり、`x` への単射を持ちません。この対象、その順序数性、単射が存在しないことの三つを命題的切り詰めの中に収めると、`NoInjOrd` が得られます。したがって、包装する前には定まった証人があり、呼び出し側が受け取るのはその切り詰められた存在だけです。
<!--/-->

```agda
noInjOrd : NoInjOrd
noInjOrd x ox = ∣ Hartogs.μ x , Hartogs.μ-ord x , Hartogs.noInj x ∣₁
```

<!--en-->
Finally, `noInjOrd→CardAboveLᵀ` turns the Hartogs witness into a strictly larger ambient ordinal cardinal, places that ordinal in `L`, and transfers its ambient cardinality to internal cardinality. The result is propositionally truncated: for the given ordinal cardinal `κ`, some constructible internal cardinal `θ` satisfies `κ ∈ θ`.

This theorem supplies the nonempty collection needed for the later successor-cardinal construction. It does not choose its least member; `L.GCH.Assembly` performs that minimisation after using this witness to bound the search.
<!--zh-->
最后，`noInjOrd→CardAboveLᵀ` 把 Hartogs 见证变成一个严格更大的环境序数基数，把该序数放入 `L`，再将其环境基数性传递为内部基数性。所得存在性经过命题截断：对给定的序数基数 `κ`，存在某个可构造的内部基数 `θ`，满足 `κ ∈ θ`。

这个定理为后续的后继基数构造保证所需候选非空，但并不选出其中的最小者。`L.GCH.Assembly` 先用这里的见证限定搜索范围，再完成最小化。
<!--ja-->
最後に、`noInjOrd→CardAboveLᵀ` は Hartogs の証人から真に大きい周囲の順序数基数を作り、その順序数を `L` に入れ、周囲での基数性を内部の基数性へ移します。得られる存在は命題的に切り詰められています。すなわち、与えられた順序数基数 `κ` に対して、`κ ∈ θ` を満たす構成可能な内部基数 `θ` が存在します。

この定理は、後の後続基数の構成に必要な候補が空でないことを保証しますが、その最小要素を選びません。`L.GCH.Assembly` が、ここで得た証人によって探索範囲を定めた後に最小化を行います。
<!--/-->

```agda
CardAboveL : CardAboveLᵀ
CardAboveL = noInjOrd→CardAboveLᵀ noInjOrd
```
