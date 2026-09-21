<!--en-->
# Transferring structure through condensation
<!--zh-->
# 通过凝聚搬运结构
<!--ja-->
# 凝縮を通して構造を移す
<!--/-->

<!--en-->
This chapter asks what becomes of an elementary Skolem hull after its Mostowski collapse. Under the stated hypotheses at an ordinal index `lam`, the collapse image is identified with `Lset β` for some ordinal `β`. No comparison between `β` and `lam`, no least such index, and no cardinal estimate is part of this conclusion. The proof begins by giving the constructible-stage relation a bounded first-order description that can be read before and after the collapse.
<!--zh-->
本章研究初等 Skolem 壳经过 Mostowski 塌缩后会变成什么。在序数索引 `lam` 处给定所需假设后，塌缩像将被认同为某个序数 `β` 所索引的 `Lset β`。这个结论不比较 `β` 与 `lam`，不选取最小的此类索引，也不给出基数估计。证明首先用一条有界一阶公式描述可构造层关系，使这项关系能在塌缩前后读取。
<!--ja-->
本章では、初等的な Skolem 包が Mostowski 崩壊の後にどのような集合になるかを調べる。順序数の添字 `lam` において必要な仮定を与えると、崩壊像はある順序数 `β` が添字づける `Lset β` と同一視される。この結論は `β` と `lam` を比較せず、そのような添字の最小のものを選ばず、基数評価も与えない。証明はまず、構成可能段階の関係を有界な一階論理式で記述し、崩壊の前後で読めるようにする。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The theorem is parameterized by excluded middle at `ℓ-suc ℓ`. That single classical hypothesis is passed to the preceding results about ordinal stages, hulls, hierarchy descriptions, and adequate stages. The present argument introduces no choice principle: existential satisfaction and the local stage witnesses supplied by superadequacy remain propositionally truncated, so they may be used only when the target is again a proposition.
<!--zh-->
定理以 `ℓ-suc ℓ` 层级上的排中律为参数。这一条经典假设被传给前文关于序数层、Skolem 壳、层级描述与充分层的结果。本章的论证不引入选择原理：存在公式的满足以及超充分性给出的局部层见证都保持为命题截断，因此只能在目标仍是命题时使用。
<!--ja-->
定理は `ℓ-suc ℓ` における排中律をパラメータとする。この一つの古典的仮定は、順序数段階、Skolem 包、階層の記述、十分な段階について先に得られた結果へ渡される。ここでの議論は選択原理を導入しない。存在論理式の充足と、強化された十分さが与える局所的な段階の証人は命題的切り詰めのままなので、行き先が再び命題である場合にだけ使われる。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix the universe level and this classical parameter. All sets below belong to the ambient cumulative hierarchy at level `ℓ`; the constructible stages, the hull, and the collapse image are sets in that same hierarchy. Full elementarity transports the formulas with unbounded existential quantifiers. The bounded interfaces, built from stage absoluteness, elementarity, and the collapse isomorphism, expose Δ₀ transport through the collapse. Keeping these two uses separate is essential to the condensation proof.
<!--zh-->
现在固定宇宙层级与这一个经典参数。下文所有集合都属于层级 `ℓ` 上的外围累积层级；可构造层、Skolem 壳与塌缩像也是同一累积层级中的集合。完整初等性负责搬运带无界存在量词的公式。由层绝对性、初等性与塌缩同构构成的有界接口，则对外提供沿塌缩的 Δ₀ 搬运。区分这两种用法，是凝聚证明的关键。
<!--ja-->
ここで宇宙レベルとこの古典的パラメータを固定する。以下の集合はすべて、レベル `ℓ` の周囲の累積階層に属する。構成可能段階、Skolem 包、崩壊像も同じ累積階層の集合である。完全な初等性は、非有界な存在量化を含む論理式を移す。段階の絶対性、初等性、崩壊同型から作られた有界なインターフェースは、崩壊を通る Δ₀ の移送を外に示す。この二つの使い方を分けることが、凝縮の証明では欠かせない。
<!--/-->

```agda
module L.GCH.CondensationTransfer {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The object language needs only membership, equality, conjunction, and unbounded existence for the two queries built below. Its constant alphabet changes as a formula moves between the ambient hierarchy, the stage, and the hull. The operation `mapFo` relabels existing constants, while `embed` regards a constant-free formula as a formula over a new constant alphabet. Neither operation changes the variable positions or logical structure of the formula.
<!--zh-->
下文两条查询只需对象语言中的隶属、相等、合取与无界存在量词。公式在外围层级、层与 Skolem 壳之间移动时，其常元字母表会随之改变。运算 `mapFo` 重标已有常元，而 `embed` 把一条无常元公式视为新常元字母表上的公式；两者都不改变公式的变元位置与逻辑结构。
<!--ja-->
以下で作る二つの問い合わせに必要なのは、対象言語の所属、等号、連言、非有界な存在量化だけである。論理式を周囲の階層、段階、Skolem 包の間で移すとき、その定数のアルファベットは変わる。`mapFo` は既存の定数を付け替え、`embed` は定数を含まない論理式を新しい定数アルファベット上の論理式とみなす。どちらも変数の位置や論理構造を変えない。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.ConstantMapping using ( mapFo; embed )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The constructible hierarchy requires a persistent distinction between an ordinal index `d` and the stage `Lset d` that it indexes. A member of `Lset lam` is constructible when `lam` is ordinal. Conversely, if an ordinal `d` is a member of `Lset lam`, rank comparison places `d` in `lam`. The downward description `Lset-out` says only that a member of a stage merely comes from `𝒟ₒ (Lset c)` for some `c` in its index; it retains no chosen birth stage. Monotonicity then transports membership from `Lset β` to `Lset α` when the strict index relation `β ∈ α` is available.
<!--zh-->
可构造层级要求始终区分序数索引 `d` 与它所索引的层 `Lset d`。当 `lam` 是序数时，`Lset lam` 的成员都是可构造的。反过来，若序数 `d` 属于 `Lset lam`，则秩比较把 `d` 放入 `lam`。向下刻画 `Lset-out` 只说一层的成员仅仅来自某个 `c ∈ lam` 处的 `𝒟ₒ (Lset c)`，并不保留选定的出生层。若有严格的索引关系 `β ∈ α`，单调性再把 `Lset β` 中的成员搬到 `Lset α`。
<!--ja-->
構成可能階層では、順序数の添字 `d` と、それが添字づける段階 `Lset d` を常に区別しなければならない。`lam` が順序数なら、`Lset lam` の要素は構成可能である。逆に、順序数 `d` が `Lset lam` に属するなら、階数の比較によって `d ∈ lam` が得られる。下向きの特徴づけ `Lset-out` が述べるのは、段階の要素が、ある `c ∈ lam` に対する `𝒟ₒ (Lset c)` から単に来るということだけであり、誕生段階を一つ選んで保持するわけではない。さらに、厳密な添字関係 `β ∈ α` があれば、単調性によって `Lset β` の要素を `Lset α` へ移せる。
<!--/-->

```agda
open import L.Constructible {ℓ} using
  ( IsOrd; isL; Lset; Lset-out; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
```

<!--en-->
The central formula is `levelFo(a,p,z)`. Its Δ₀ certificate allows bounded absoluteness and transport through the collapse. Soundness says that, when `a`, `p`, and `z` are constructible, satisfaction implies `a ≡ Lset p`; the auxiliary bound `z` need not be uniquely determined. Completeness supplies satisfaction at the particular triple `(Lset p,p,Lset γ)` when `γ` is adequate, `p` is ordinal, and `p ∈ γ`. The surrounding theory provides the hull transfer and the local adequate indices required to construct such triples.
<!--zh-->
这里的核心公式是 `levelFo(a,p,z)`。它的 Δ₀ 证书允许使用有界绝对性，并可沿塌缩搬运。可靠性说明：当 `a`、`p`、`z` 都可构造时，满足该公式可推出 `a ≡ Lset p`；辅助界 `z` 不必唯一。完备性则在 `γ` 充分、`p` 是序数且 `p ∈ γ` 时，给出特定三元组 `(Lset p,p,Lset γ)` 对公式的满足。周围理论提供 Skolem 壳上的搬运，以及构造这类三元组所需的局部充分索引。
<!--ja-->
中心となる論理式は `levelFo(a,p,z)` である。その Δ₀ の証拠により、有界絶対性を使い、崩壊に沿って移送できる。健全性は、`a`、`p`、`z` が構成可能であるとき、充足から `a ≡ Lset p` が従うことを述べる。補助的な上界 `z` は一意である必要がない。完全性は、`γ` が十分で、`p` が順序数であり、`p ∈ γ` であるとき、特定の三つ組 `(Lset p,p,Lset γ)` が論理式を満たすことを与える。周囲の理論は、Skolem 包上の移送と、そのような三つ組を作るための局所的な十分な添字を供給する。
<!--/-->

```agda
open import L.GCH.SkolemHull {ℓ} lem using
  ( module HullStage; Δ₀-isOrdAt; module Amb
  ; module Frame; _⊨ₚ_; embed-map; isOrd-at-p )
open import L.GCH.HierarchyDescription {ℓ} lem using ( levelFo; Δ₀-levelFo; level-sound; level-complete )
open import L.GCH.AdequateStages {ℓ} lem using ( Superadequate; Adequate; Lset∈suc )
```

<!--en-->
Finite vectors record the environments in which formulas are evaluated, while products combine the membership and equality facts used in the proof. Several existences in this chapter are propositionally truncated. The constructor `∣_∣₁` places an explicit local witness under truncation; `rec₁` and `map₁` may then use it only to produce another proposition. In particular, the local adequate indices supplied by superadequacy never become a globally chosen family.
<!--zh-->
有穷向量记录公式求值所用的环境，乘积则组合证明中需要的隶属事实与相等事实。本章有若干存在性处于命题截断之下。构造子 `∣_∣₁` 把一份显式的局部见证放入截断；`rec₁` 与 `map₁` 随后只能用它产生另一个命题。特别地，超充分性给出的局部充分索引不会变成一族全局选定的数据。
<!--ja-->
有限ベクトルは論理式を評価する環境を記録し、積は証明で必要となる所属と等しさの事実を組み合わせる。この章に現れるいくつかの存在は、命題的切り詰めのもとにある。構成子 `∣_∣₁` は明示的な局所証人を切り詰めの中へ入れ、`rec₁` と `map₁` はそれを別の命題を得るためにだけ使う。とくに、強化された十分さが与える局所的な十分な添字が、大域的に選ばれた族になることはない。
<!--/-->

```agda
```

<!--en-->
The set-theoretic successor `sucV d` is the next ordinal index when `d` is ordinal, and it is also the index used by the successor-stage equation `Lset (sucV d) ≡ 𝒟ₒ (Lset d)`. These are related facts, but the successor index and the stage at that index remain different sets. The empty set appears separately because the hull construction requires a fallback member already present in the ambient index.
<!--zh-->
当 `d` 是序数时，集合论后继 `sucV d` 是下一个序数索引；后继层等式 `Lset (sucV d) ≡ 𝒟ₒ (Lset d)` 也使用这个索引。这两项事实彼此相关，但后继索引与该索引处的层仍是不同的集合。空集另行出现，是因为 Skolem 壳构造需要一个已经属于外围索引的回退成员。
<!--ja-->
`d` が順序数なら、集合論的後続 `sucV d` は次の順序数添字である。また、後続段階の等式 `Lset (sucV d) ≡ 𝒟ₒ (Lset d)` もこの添字を使う。この二つの事実は関係しているが、後続の添字と、その添字における段階は別の集合である。空集合が別に現れるのは、Skolem 包の構成が、周囲の添字にすでに属する予備の要素を必要とするためである。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

```

<!--en-->
Opening the proposition-valued hierarchy structure fixes the carrier `S` and the ambient membership notation `_∈ˢ_`. Brackets `⟨_⟩` expose the type of proofs carried by one of its truth values. Thus `d ∈ˢ lam`, membership in a constructible stage, and membership in the collapse image are ambient set-theoretic statements, distinct from the object-language atom `_∈̇_` used inside a formula.
<!--zh-->
打开取值为命题的层级结构后，载体 `S` 与外围隶属记号 `_∈ˢ_` 得到固定。尖括号 `⟨_⟩` 取出一个真值所承载的证明类型。因此，`d ∈ˢ lam`、可构造层中的隶属以及塌缩像中的隶属，都是外围集合论陈述，应与公式内部的对象语言原子 `_∈̇_` 区分。
<!--ja-->
命題値の階層構造を開くと、台 `S` と周囲の所属の記法 `_∈ˢ_` が定まる。山括弧 `⟨_⟩` は、その真理値が運ぶ証明の型を取り出す。したがって、`d ∈ˢ lam`、構成可能段階への所属、崩壊像への所属は周囲の集合論における主張であり、論理式の内部で使う対象言語の原子 `_∈̇_` とは区別される。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ

```

<!--en-->
The ambient semantics supplies the notation `S ^ n` for environments of length `n`. Formula slots are read from such vectors; each newly bound existential witness is placed at the front, shifting the older slots outward. This convention explains why the three nested witnesses used later are finally read in the order `(a,p,z)`, even though they are introduced from the outside as `z`, then `p`, then `a`.
<!--zh-->
外围语义给出长度为 `n` 的环境记号 `S ^ n`。公式的槽位从这种向量中读取；每个新绑定的存在见证都放在向量前端，把旧槽位向外推移。因此，后文三层嵌套的见证虽然从外到内依次引入 `z`、`p`、`a`，最终却按 `(a,p,z)` 的顺序读取。
<!--ja-->
周囲の意味論は、長さ `n` の環境を表す記法 `S ^ n` を与える。論理式のスロットはこのようなベクトルから読まれ、新しく束縛された存在の証人は先頭に置かれて、以前のスロットを外側へずらす。そのため、後で三重に入れ子になった証人は、外側から `z`、`p`、`a` の順に導入されても、最終的には `(a,p,z)` の順に読まれる。
<!--/-->

```agda
module SemVᵃ = FOL.Semantics 𝒮ᵥ
open SemVᵃ using ( _^_ )
```

<!--en-->
## Formulas that identify the level witnesses
<!--zh-->
## 识别层见证的公式
<!--ja-->
## 階層の証人を特定する論理式
<!--/-->

<!--en-->
The formula `isOrd-at-p` uses only the middle slot of a three-entry environment. Its first conjunct says that `p` is transitive, and its second says that every member of `p` is transitive. The two functions displayed here unpack those bounded clauses into the two fields of `IsOrd p`. The neighbouring values `a` and `z` play no role in this lemma, and the lemma does not read the rest of `levelFo` or identify `a` with a constructible stage.
<!--zh-->
公式 `isOrd-at-p` 只使用三项环境的中间槽位。它的第一个合取支说明 `p` 传递，第二个合取支说明 `p` 的每个成员都传递。这里的两个函数把这两条有界子句拆成 `IsOrd p` 的两个字段。相邻的 `a` 与 `z` 在这条引理中不起作用；该引理既不读取 `levelFo` 的其余部分，也不把 `a` 认同为某个可构造层。
<!--ja-->
論理式 `isOrd-at-p` は、三項環境の中央のスロットだけを使う。第一の連言支は `p` が推移的であることを述べ、第二の連言支は `p` の各要素が推移的であることを述べる。ここに示す二つの関数は、その二つの有界な節を `IsOrd p` の二つの成分へ展開する。隣の値 `a` と `z` はこの補題では何の役割も果たさない。また、この補題は `levelFo` の残りを読み取らず、`a` を構成可能段階と同一視することもない。
<!--/-->

```agda
isOrd-at-p-out : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ isOrd-at-p ⟩ → IsOrd p
isOrd-at-p-out a p z h =
    ( λ {x₁} {y} y∈x₁ x₁∈p → h .fst x₁ x₁∈p y y∈x₁ )
  , ( λ b b∈p {x₁} {y} y∈x₁ x₁∈b → h .snd b b∈p x₁ x₁∈b y y∈x₁ )
```

<!--en-->
## Transferring hierarchy information through the collapse
<!--zh-->
## 沿塌缩搬运层级信息
<!--ja-->
## 崩壊を通して階層の情報を移す
<!--/-->

<!--en-->
Fix an ordinal `lam` and the ambient constructible stage `Lset lam` that contains the hull. The index is closed under set-theoretic successor, every generator in `X` belongs to this stage, and `∅ ∈ lam` supplies the default element needed in the hull construction. The last hypothesis in this first group is full elementarity: every formula, including formulas with unbounded quantifiers, has the same truth value in the hull and in the surrounding stage when its parameters come from the hull.
<!--zh-->
固定序数 `lam`，以及容纳 Skolem 壳的外围可构造层 `Lset lam`。该索引对集合论后继封闭，生成集 `X` 的每个成员都属于这一层，而 `∅ ∈ lam` 提供构造 Skolem 壳时所需的默认元素。这组假设的最后一项是完整初等性：只要参数来自 Skolem 壳，每条公式在壳中与外围层中便有相同真值，其中也包括带无界量词的公式。
<!--ja-->
順序数 `lam` と、Skolem 包を含む周囲の構成可能段階 `Lset lam` を固定する。この添字は集合論的後続について閉じ、生成集合 `X` の各要素はこの段階に属する。また `∅ ∈ lam` は、Skolem 包の構成に必要な既定の要素を与える。この最初の仮定群の最後は完全な初等性である。パラメータが包から取られるなら、非有界量化子を含む論理式も含め、すべての論理式は包と周囲の段階で同じ真理値をもつ。
<!--/-->

```agda
module Condense (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
```

<!--en-->
Two further hypotheses provide local stages and constructible collapse values. `Superadequate lam` says that every `d ∈ lam` is merely contained in some adequate ordinal index `γ` with `γ ∈ lam`; propositional truncation retains neither a selected `γ` nor a least one. The hypothesis `pixL` is pointwise: each member of the collapse image is constructible. It does not yet say that the collapse image itself is a constructible set, much less identify that image with a particular stage.
<!--zh-->
另外两项假设分别提供局部层与可构造的塌缩值。`Superadequate lam` 说明：每个 `d ∈ lam` 仅仅包含于某个满足 `γ ∈ lam` 的充分序数索引 `γ`；命题截断既不保留选定的 `γ`，也不保留最小者。假设 `pixL` 是逐点的：塌缩像的每个成员都可构造。它尚未说明塌缩像本身是可构造集，更没有把该像认同为某个特定的层。
<!--ja-->
さらに二つの仮定が、局所的な段階と構成可能な崩壊値を与える。`Superadequate lam` は、各 `d ∈ lam` が、`γ ∈ lam` を満たすある十分な順序数添字 `γ` に単に含まれることを述べる。命題的切り詰めは、特定の `γ` も最小のものも保持しない。仮定 `pixL` は各点についての主張である。崩壊像の各要素が構成可能であると言うだけで、崩壊像そのものが構成可能な集合であることも、それを特定の段階と同一視することも、まだ述べていない。
<!--/-->

```agda
  (sup : Superadequate lam)
  (pixL : (x : S) → ⟨ x ∈ˢ HullStage.C.πX lam ordλ succλ X X⊆L ∅∈λ ⟩
        → ⟨ isL x ⟩)
  where

```

<!--en-->
Three structures are now used together: the ambient structure on `Lset lam`, the structure whose carrier consists of hull members, and the transitive collapse image. A hull element carries both an underlying set and its proof of membership in `M`. Bounded formulas can be read between the first two structures and can be transported in either direction through the collapse; individual membership facts can also be pushed through the collapse. These Δ₀ interfaces will be used only after the unbounded existential queries have been handled by full elementarity.
<!--zh-->
下面同时使用三个结构：`Lset lam` 上的外围结构、以 Skolem 壳成员为载体的结构，以及传递的塌缩像。一个壳元素同时携带底层集合及其属于 `M` 的证明。有界公式可以在前两个结构之间读取，也可以沿塌缩双向搬运；单条成员关系同样可以推过塌缩。这些 Δ₀ 接口只在完整初等性处理完无界存在查询以后使用。
<!--ja-->
ここからは三つの構造を同時に使う。`Lset lam` 上の周囲の構造、Skolem 包の要素を台とする構造、そして推移的な崩壊像である。包の要素は、基礎となる集合と、それが `M` に属するという証明をともに携える。有界な論理式は最初の二つの構造の間で読め、崩壊を通して双方向に移せる。個々の所属の事実も崩壊の向こうへ送れる。これらの Δ₀ インターフェースを使うのは、完全な初等性によって非有界な存在問い合わせを処理した後だけである。
<!--/-->

```agda
  module F = Frame lam ordλ succλ X X⊆L ∅∈λ using (module A; module Carry; module HS)
  module A = F.A using (SM; module SemM; inL)
  module Mse = A.SemM.At A.SM id using (_⊨_)
  module HS = F.HS using (module ASt; module C; module Condense; module H; M)
  module Cy = F.Carry elem using (atL; atM; member-push; push; pull)
```

<!--en-->
The inclusion `Hull⊆L` is the basic bridge from a hull member to the ambient stage: if `x ∈ M`, then `x ∈ Lset lam`. This fact supplies the stage-membership evidence used by `A.inL`, and it will also turn each returned hull witness into a constructible set through `isLλ`. It is a pointwise inclusion of the hull in the stage, not a statement that the hull itself is an element of that stage.
<!--zh-->
包含 `Hull⊆L` 是从 Skolem 壳成员通往外围层的基本桥梁：若 `x ∈ M`，则 `x ∈ Lset lam`。这条事实提供 `A.inL` 所需的层隶属证据，稍后还会经由 `isLλ` 把壳中返回的每个见证转为可构造集。它是 Skolem 壳逐点包含于该层的陈述，并不说明壳本身是该层的元素。
<!--ja-->
包含 `Hull⊆L` は、Skolem 包の要素から周囲の段階へ渡る基本的な橋である。`x ∈ M` ならば `x ∈ Lset lam` が成り立つ。この事実は `A.inL` が必要とする段階への所属の証拠を与え、後では `isLλ` を通して、包から返された各証人を構成可能な集合にする。これは包が段階に各点で含まれるという主張であり、包そのものが段階の要素であるという主張ではない。
<!--/-->

```agda

  open HS.H using ( Hull⊆L )

```

<!--en-->
Let `M` denote the Skolem hull determined by the preceding data. Its members lie in `Lset lam` by `Hull⊆L`, but neither the constructibility of `M` as a whole nor any additional closure property follows from this notation. Every later use of the collapse will therefore keep the premise that its argument belongs to `M`.
<!--zh-->
以 `M` 表示由前述数据确定的 Skolem 壳。由 `Hull⊆L`，它的每个成员都属于 `Lset lam`；但这项记号本身既不说明整个 `M` 可构造，也不增添任何封闭性质。因此，后文每次使用塌缩时都会保留「其自变量属于 `M`」这一前提。
<!--ja-->
以上のデータから定まる Skolem 包を `M` と書く。`Hull⊆L` により、その各要素は `Lset lam` に属する。しかし、この記法だけから `M` 全体の構成可能性や新たな閉性が従うわけではない。したがって、以下で崩壊を使うたびに、その引数が `M` に属するという前提を保つ。
<!--/-->

```agda
  M : S
  M = HS.M

```

<!--en-->
Let `π` be the Mostowski collapse map and let `πX` be its transitive image. On hull members, `π` preserves the membership relation and identifies bounded truths with their readings in the image. The problem is now to prove enough closure and covering for `πX` to show that this transitive set is exactly one stage `Lset β`.
<!--zh-->
以 `π` 表示 Mostowski 塌缩映射，以 `πX` 表示它的传递像。在 Skolem 壳成员上，`π` 保持成员关系，并把有界真值认同为它们在像中的读法。接下来的问题是为 `πX` 证明足够的层闭合性质与覆盖性质，从而说明这个传递集恰好是某一层 `Lset β`。
<!--ja-->
Mostowski 崩壊写像を `π`、その推移的な像を `πX` と書く。Skolem 包の要素上で、`π` は所属関係を保存し、有界な真理を像における読みに移す。ここからの課題は、`πX` に十分な段階の閉性と被覆の性質を示し、この推移的集合がちょうど一つの段階 `Lset β` であることを導くことである。
<!--/-->

```agda
  π : S → S
  π = HS.C.π

```

<!--en-->
Because `lam` is ordinal, membership in `Lset lam` supplies constructibility. The helper `isLλ` packages exactly this implication. It will be applied to all three entries returned by a hull query before `level-sound` is invoked, since satisfaction of `levelFo` alone does not provide the constructibility assumptions required by its soundness theorem.
<!--zh-->
由于 `lam` 是序数，属于 `Lset lam` 足以推出可构造性。辅助函数 `isLλ` 恰好封装这条蕴涵。Skolem 壳查询返回三个分量后，证明会在调用 `level-sound` 之前分别对三者应用它，因为仅仅满足 `levelFo` 并不会给出可靠性定理所要求的可构造性假设。
<!--ja-->
`lam` が順序数なので、`Lset lam` への所属から構成可能性が得られる。補助関数 `isLλ` は、まさにこの含意をまとめたものである。Skolem 包の問い合わせから返された三つの成分すべてにこれを適用してから `level-sound` を使う。`levelFo` の充足だけでは、その健全性定理が要求する構成可能性の仮定は得られないからである。
<!--/-->

```agda
  isLλ : (x : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ isL x ⟩
  isLλ = Lset→isL lam ordλ

```

<!--en-->
Two elementary membership lemmas now prepare witnesses for the ambient stage. First suppose `d ∈ lam`. Successor closure gives `sucV d ∈ lam`; the entire stage `Lset d` is an element of `Lset (sucV d)`; and `Lset-mono` transports that single element into `Lset lam`. The conclusion `Lset d ∈ Lset lam` is membership between sets, not the pointwise inclusion of one stage in another.
<!--zh-->
下面两条基本隶属引理为外围层准备见证。先设 `d ∈ lam`。后继封闭给出 `sucV d ∈ lam`；整个层 `Lset d` 作为一个元素属于 `Lset (sucV d)`；`Lset-mono` 再把这个元素搬入 `Lset lam`。结论 `Lset d ∈ Lset lam` 是集合之间的隶属关系，并非一层逐点包含于另一层。
<!--ja-->
次の二つの基本的な所属の補題が、周囲の段階に置く証人を準備する。まず `d ∈ lam` とする。後続についての閉性から `sucV d ∈ lam` が得られ、段階全体 `Lset d` は `Lset (sucV d)` の一つの要素であり、`Lset-mono` がその要素を `Lset lam` へ移す。結論 `Lset d ∈ Lset lam` は集合の間の所属であり、一つの段階が別の段階に各点で含まれるという意味ではない。
<!--/-->

```agda
  Lset∈Lλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩
  Lset∈Lλ d d∈λ = Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (Lset∈suc d)

```

<!--en-->
If `d` is also ordinal, then `ord∈Lset-suc` places the index `d` itself in `Lset (sucV d)`, and the same monotonicity step carries it into `Lset lam`. Together, the two lemmas provide two distinct stage elements, `d` and `Lset d`. Both are needed when the level formula is witnessed inside the ambient stage, and neither membership should be confused with the index relation `d ∈ lam` from which it was derived.
<!--zh-->
若 `d` 还是序数，则 `ord∈Lset-suc` 把索引 `d` 本身放入 `Lset (sucV d)`，再由同一次单调性搬运进入 `Lset lam`。两条引理合起来给出两个不同的层成员，即 `d` 与 `Lset d`。在外围层中见证层公式时，二者都要使用；它们的隶属都不能与推导起点的索引关系 `d ∈ lam` 混同。
<!--ja-->
さらに `d` が順序数なら、`ord∈Lset-suc` は添字 `d` 自身を `Lset (sucV d)` に入れ、同じ単調性の一歩がそれを `Lset lam` へ移す。二つの補題を合わせると、`d` と `Lset d` という別々の段階要素が得られる。周囲の段階の内部で階層の論理式を証明するときには両方が必要であり、どちらの所属も、その出発点となった添字関係 `d ∈ lam` と混同してはならない。
<!--/-->

```agda
  ord∈Lλ : (d : S) → IsOrd d → ⟨ d ∈ˢ lam ⟩ → ⟨ d ∈ˢ Lset lam ⟩
  ord∈Lλ d od d∈λ =
    Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (ord∈Lset-suc d od)
```

<!--en-->
For a hull member `d`, ordinality can be sent through the collapse. `Amb.isOrdAt-in` expresses `IsOrd d` by the constant-free bounded formula `isOrdAt`; `Cy.push` transports that Δ₀ truth from the hull environment to the environment containing `π d`; and `Amb.isOrdAt-out` reads the result as `IsOrd (π d)`. The boundedness certificate controls this transfer, while the comparison embodied in `Cy.push` ultimately rests on the elementary hull inclusion and the collapse isomorphism.
<!--zh-->
对 Skolem 壳成员 `d`，序数性可以正向穿过塌缩。`Amb.isOrdAt-in` 用无常元有界公式 `isOrdAt` 表达 `IsOrd d`；`Cy.push` 把这个 Δ₀ 真值从壳环境搬到含有 `π d` 的环境；`Amb.isOrdAt-out` 再把结果读成 `IsOrd (π d)`。有界性证书控制这次搬运，而 `Cy.push` 所封装的比较最终依赖 Skolem 壳的初等包含与塌缩同构。
<!--ja-->
Skolem 包の要素 `d` について、順序数性を崩壊の向こうへ送れる。`Amb.isOrdAt-in` は、定数を含まない有界な論理式 `isOrdAt` によって `IsOrd d` を表す。`Cy.push` はこの Δ₀ の真理を包の環境から `π d` を含む環境へ移し、`Amb.isOrdAt-out` が結果を `IsOrd (π d)` として読み取る。有界性の証拠がこの移送を制御し、`Cy.push` がまとめている比較は、最終的には Skolem 包の初等的な包含と崩壊同型に基づく。
<!--/-->

```agda
  ord-push : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd d → IsOrd (π d)
  ord-push d d∈M od =
    Amb.isOrdAt-out (π d)
      (Cy.push Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in d od))

```

<!--en-->
The same bounded description also travels backward. Starting from `IsOrd (π d)`, `Cy.pull` returns truth of `isOrdAt` at the original hull member, which is then read as `IsOrd d`. Hence the collapse preserves and reflects ordinality on members of `M`. This is a local equivalence with the hypothesis `d ∈ M`; it says nothing about the behaviour of `π` on arbitrary ambient sets.
<!--zh-->
同一条有界描述也能反向搬运。从 `IsOrd (π d)` 出发，`Cy.pull` 把 `isOrdAt` 的真值带回原来的 Skolem 壳成员，再读成 `IsOrd d`。因此，塌缩在 `M` 的成员上保持并反映序数性。这是带有假设 `d ∈ M` 的局部等价，并不说明 `π` 对任意外围集合如何作用。
<!--ja-->
同じ有界な記述は逆向きにも移せる。`IsOrd (π d)` から出発すると、`Cy.pull` が `isOrdAt` の真理をもとの Skolem 包の要素へ戻し、それを `IsOrd d` として読み取れる。したがって、崩壊は `M` の要素について順序数性を保存し、反映する。これは仮定 `d ∈ M` のもとでの局所的な同値であり、任意の周囲の集合に対する `π` の振る舞いを述べるものではない。
<!--/-->

```agda
  ord-pull : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd (π d) → IsOrd d
  ord-pull d d∈M oπd =
    Amb.isOrdAt-out d
      (Cy.pull Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in (π d) oπd))
```

<!--en-->
The first existential query is designed to recover the particular stage `Lset d` inside the hull. Its three unbounded existential quantifiers produce an environment `(a,d′,z)`. The embedded core requires `levelFo(a,d′,z)`, while the equation in the second conjunct fixes the returned middle coordinate by `d′ ≡ dM`. Only `levelFo` is Δ₀. The surrounding query `findA` is not bounded, so full elementarity, rather than Δ₀ absoluteness alone, will be used to bring its witnesses from the ambient stage into the hull. This equality is the feature that distinguishes `findA` from the later query `findP`, whose returned index `p′` need not equal the externally prepared `p`.
<!--zh-->
第一条存在查询用于在 Skolem 壳中找回指定的层 `Lset d`。它的三个无界存在量词产生环境 `(a,d′,z)`。嵌入的核心要求 `levelFo(a,d′,z)`，第二个合取支中的等式则把返回的中间坐标固定为 `d′ ≡ dM`。只有 `levelFo` 是 Δ₀；外围查询 `findA` 并非有界公式，因此要把见证从外围层带入 Skolem 壳，必须使用完整初等性，不能仅靠 Δ₀ 绝对性。正是这条等式把 `findA` 与稍后的查询 `findP` 区分开来；后者返回的索引 `p′` 不必等于外围预备的 `p`。
<!--ja-->
最初の存在問い合わせは、指定された段階 `Lset d` を Skolem 包の内部で取り戻すためのものである。三つの非有界な存在量化によって環境 `(a,d′,z)` が得られる。埋め込まれた核は `levelFo(a,d′,z)` を要求し、第二の連言支の等式が、返された中央の座標を `d′ ≡ dM` として固定する。Δ₀ なのは `levelFo` だけである。その外側の問い合わせ `findA` は有界ではないので、証人を周囲の段階から Skolem 包へ移すには、Δ₀ 絶対性だけでなく完全な初等性を使う。この等式が `findA` と後の問い合わせ `findP` を分ける。後者が返す添字 `p′` は、外側で準備した `p` と等しい必要がない。
<!--/-->

```agda
  findA : A.SM → Formula A.SM 0
  findA dM = ∃̇ (∃̇ (∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM))))

```

<!--en-->
The lemma `stageA` builds the ambient witness that elementarity will later pull into the hull. It takes an adequate index `γ` containing the ordinal `d`, a hull representative `dM` whose underlying set is `d`, and separate evidence that `d`, `Lset d`, and `Lset γ` are elements of `Lset lam`. Completeness supplies `levelFo(Lset d,d,Lset γ)`. Bounded absoluteness reads this core in the stage structure, and the object-language equality uses the path from `dM` to `d`. The three unbounded existential clauses are then witnessed, under propositional truncation, by `Lset γ`, `d`, and `Lset d`; no claim that `γ` is least is made.
<!--zh-->
引理 `stageA` 构造一个外围见证，稍后由初等性把它拉回 Skolem 壳。它接收一个包含序数 `d` 的充分索引 `γ`、一个底层集合等于 `d` 的壳代表 `dM`，以及 `d`、`Lset d`、`Lset γ` 分别属于 `Lset lam` 的证据。完备性给出 `levelFo(Lset d,d,Lset γ)`；有界绝对性在层结构中读取这个核心，对象语言中的等式则使用从 `dM` 底层集合到 `d` 的路径。随后，三个无界存在子句在命题截断下分别由 `Lset γ`、`d`、`Lset d` 见证；这里没有声称 `γ` 是最小者。
<!--ja-->
補題 `stageA` は、後で初等性によって Skolem 包へ引き戻す周囲の証人を作る。順序数 `d` を含む十分な添字 `γ`、基礎にある集合が `d` に等しい包の代表 `dM`、そして `d`、`Lset d`、`Lset γ` がそれぞれ `Lset lam` の要素であるという証拠を受け取る。完全性が `levelFo(Lset d,d,Lset γ)` を与え、有界絶対性がこの核を段階の構造で読み、対象言語の等式には `dM` の基礎にある集合から `d` へのパスを使う。その後、三つの非有界な存在の節は、命題的切り詰めのもとで `Lset γ`、`d`、`Lset d` によって順に証明される。ここでは `γ` が最小であるとは主張しない。
<!--/-->

```agda
  stageA : (d γ : S) (od : IsOrd d) (adγ : Adequate γ) (d∈γ : ⟨ d ∈ˢ γ ⟩)
         → (dM : A.SM) → fst dM ≡ d
         → ⟨ d ∈ˢ Lset lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ mapFo A.inL (findA dM) ⟩
  stageA d γ od adγ d∈γ dM ed d∈ Ld∈ Lγ∈ =
```

<!--en-->
The external witnesses are the adequate bound `Lset γ`, the prescribed index `d`, and its stage `Lset d`. Their final environment is `(Lset d,d,Lset γ)`, so completeness supplies the level-description conjunct. The equality conjunct needs `sym ed`: the query asks for the returned index to equal the interpretation of `dM`, whereas `ed` identifies that interpretation with `d`. Each existential witness is placed under propositional truncation, preserving existence without designating this triple as a canonical choice.
<!--zh-->
外围见证分别是充分界 `Lset γ`、指定索引 `d` 及其所索引的层 `Lset d`。它们最终组成环境 `(Lset d,d,Lset γ)`，因此完备性给出层描述这一合取支。等式合取支需要 `sym ed`：查询要求返回索引等于 `dM` 的解释，而 `ed` 把该解释认同为 `d`。每个存在见证都被放在命题截断之下，所以这里只保留三元组的存在性，并未把这一个三元组选作典范数据。
<!--ja-->
周囲で用いる証人は、十分な上界 `Lset γ`、指定された添字 `d`、そしてその段階 `Lset d` である。最終的な環境は `(Lset d,d,Lset γ)` となるので、完全性が段階の記述の連言支を与える。等式の連言支には `sym ed` が必要である。問い合わせは返された添字が `dM` の解釈に等しいことを求めるが、`ed` はその解釈を `d` と同一視する逆向きのパスだからである。各存在証人は命題的切り詰めのもとに置かれ、この三つ組を正準的に選ぶことなく、その存在だけを保つ。
<!--/-->

```agda
    ∣ (Lset γ , Lγ∈) , ∣ (d , d∈) , ∣ (Lset d , Ld∈) , (sat , sym ed) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset d , Ld∈) ∷ (d , d∈) ∷ (Lset γ , Lγ∈) ∷ []

```

<!--en-->
Completeness of the level description supplies the mathematical core. Since `γ` is adequate, `d` is ordinal, and `d ∈ γ`, the triple `(Lset d,d,Lset γ)` satisfies `levelFo` in the ambient hierarchy. The adequate-stage hypothesis places the tables used by the description inside the common bound, ordinality makes `d` a legitimate stage index, and `d ∈ γ` places that index below the bound. The remaining task is to read this same Δ₀ fact in the structure on `Lset lam`.
<!--zh-->
层描述的完备性给出这里的数学核心。由于 `γ` 充分、`d` 是序数且 `d ∈ γ`，三元组 `(Lset d,d,Lset γ)` 在外围层级中满足 `levelFo`。充分性把描述所用的各张表放进共同的界，序数性使 `d` 成为合法的层索引，而 `d ∈ γ` 则把该索引置于界下。余下的问题，是在 `Lset lam` 上的结构中读取同一条 Δ₀ 事实。
<!--ja-->
段階の記述に関する完全性が、ここでの数学的な核を与える。`γ` が十分であり、`d` が順序数で、`d ∈ γ` なので、三つ組 `(Lset d,d,Lset γ)` は周囲の階層で `levelFo` を満たす。十分さは記述に使う表を共通の上界に入れ、順序数性は `d` を正当な段階の添字にし、`d ∈ γ` はその添字を上界の下に置く。残る課題は、この同じ Δ₀ の事実を `Lset lam` 上の構造で読むことである。
<!--/-->

```agda
    amb : ⟨ (Lset d ∷ d ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
    amb = level-complete γ adγ d od d∈γ

```

<!--en-->
The ambient truth must next be expressed in the stage structure on
`Lset lam`, not yet in the hull. Used backward, `Cy.atL` reads the Δ₀ formula
`levelFo` at the three displayed members of that stage. The path `embed-map`
then identifies its vacuous constant relabelling with `embed levelFo`:
`levelFo` has an empty constant domain, although the surrounding query uses
hull elements as constants. Thus `sat` supplies exactly the embedded core
needed by `stageA`; full elementarity will act only after the complete
unbounded query has been assembled.
<!--zh-->
接下来必须把外围真值改写成 `Lset lam` 上的层结构中的真值，此时还没有进入 Skolem 壳。反向使用 `Cy.atL`，可在该层的三个已给成员处读取 Δ₀ 公式 `levelFo`。随后，路径 `embed-map` 把无内容的常元改名认同为 `embed levelFo`：`levelFo` 的常元域为空，尽管外围查询以 Skolem 壳元素为常元。这样，`sat` 恰好给出 `stageA` 所需的嵌入核心；完整初等性要等整个无界查询装配完毕后才会使用。
<!--ja-->
次に、周囲での真理を `Lset lam` 上の段階構造での真理として表す。この時点ではまだ Skolem 包へ移していない。`Cy.atL` を逆向きに使うと、Δ₀ 論理式 `levelFo` を、その段階の三つの要素のもとで読める。続いてパス `embed-map` が、内容を持たない定数の改名を `embed levelFo` と同一視する。周囲の問い合わせは Skolem 包の要素を定数として使うが、`levelFo` 自身の定数域は空だからである。したがって `sat` は `stageA` が必要とする埋め込まれた核をちょうど与える。完全な初等性を使うのは、非有界な問い合わせ全体を組み立てた後である。
<!--/-->

```agda
    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ mapFo A.inL (embed levelFo) ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym (embed-map A.inL levelFo))
            (subst ⟨_⟩ (sym (Cy.atL Δ₀-levelFo δ)) amb)
```

<!--en-->
The second query also asks for a triple `(u,a,z)` satisfying the level description, but it imposes a different additional condition. Instead of identifying the middle coordinate with a prescribed index, it requires the named hull element `yM` to belong to the first coordinate `u`. Thus it asks for some correctly described constructible stage containing `y`. Its index remains free, which is exactly what the covering argument needs.
<!--zh-->
第二条查询同样寻找满足层描述的三元组 `(u,a,z)`，但附加条件不同。它不把中间坐标认同为指定索引，而是要求名为 `yM` 的 Skolem 壳元素属于第一坐标 `u`。因此，它寻找的是某个包含 `y` 且得到正确描述的可构造层，而该层的索引保持未定。这正是覆盖论证所需的条件。
<!--ja-->
第二の問い合わせも段階の記述を満たす三つ組 `(u,a,z)` を求めるが、付加条件が異なる。中央の座標を指定された添字と同一視する代わりに、`yM` と名づけられた Skolem 包の要素が第一座標 `u` に属することを要求する。したがって求めるのは、`y` を含む正しく記述された構成可能段階であり、その添字は固定されない。被覆の議論に必要なのは、まさにこの条件である。
<!--/-->

```agda
  findP : A.SM → Formula A.SM 0
  findP yM = ∃̇ (∃̇ (∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero))))

```

<!--en-->
The lemma `stageP` prepares an ambient witness to this membership query. It
starts with an ordinal `p`, an adequate `γ` containing `p`, a hull element
`yM` naming `y`, and the fact `y ∈ Lset p`. Separate membership hypotheses
place `p`, `Lset p`, and `Lset γ` inside `Lset lam`, so all three existential
witnesses are available in the stage structure. Here `p` serves only to
construct one external witness. Because `findP` contains no equation fixing
its middle coordinate, the internal index later returned by elementarity may
be a different `p′`.
<!--zh-->
引理 `stageP` 为这条成员查询准备外围见证。它从序数 `p`、包含 `p` 的充分层 `γ`、命名 `y` 的 Skolem 壳元素 `yM`，以及 `y ∈ Lset p` 出发。另有三条成员关系分别把 `p`、`Lset p` 与 `Lset γ` 放进 `Lset lam`，从而使三个存在见证都能在层结构中使用。这里的 `p` 只用于构造一份外围见证。由于 `findP` 没有用等式固定中间坐标，初等性稍后返回的内部索引可以是另一个 `p′`。
<!--ja-->
補題 `stageP` は、この所属の問い合わせに対する周囲の証人を準備する。順序数 `p`、`p` を含む十分な段階 `γ`、`y` を名づける Skolem 包の要素 `yM`、および `y ∈ Lset p` から始める。さらに三つの所属の仮定が `p`、`Lset p`、`Lset γ` をそれぞれ `Lset lam` に入れるので、三つの存在証人をすべて段階構造で使える。ここで `p` は、一つの外部証人を作るためだけに使われる。`findP` には中央の座標を固定する等式がないため、後で初等性が返す内部の添字は別の `p′` でもかまわない。
<!--/-->

```agda
  stageP : (y p γ : S) (op : IsOrd p) (adγ : Adequate γ) (p∈γ : ⟨ p ∈ˢ γ ⟩)
         → (yM : A.SM) → fst yM ≡ y → ⟨ y ∈ˢ Lset p ⟩
         → ⟨ p ∈ˢ Lset lam ⟩ → ⟨ Lset p ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ mapFo A.inL (findP yM) ⟩
  stageP y p γ op adγ p∈γ yM ey y∈Lp p∈ Lp∈ Lγ∈ =
```

<!--en-->
The same external triple `(Lset p,p,Lset γ)` witnesses the level description, but the final conjunct now records that `yM` is interpreted by an element of `Lset p`. This parallel construction isolates the mathematical difference between the queries: `findA` preserves a prescribed index, whereas `findP` preserves the membership of a prescribed point. Full elementarity may therefore return a different internal index in the second case.
<!--zh-->
同一个外围三元组 `(Lset p,p,Lset γ)` 见证层描述，但最后的合取支现在记录 `yM` 的解释属于 `Lset p`。这种平行构造凸显两条查询的数学差别：`findA` 保留指定索引，`findP` 则保留指定点的成员关系。因此，在第二种情形中，完整初等性可以返回另一个内部索引。
<!--ja-->
同じ周囲の三つ組 `(Lset p,p,Lset γ)` が段階の記述を証明するが、最後の連言支は今度は `yM` の解釈が `Lset p` に属することを記録する。この平行な構成により、二つの問い合わせの数学的な違いが明確になる。`findA` は指定された添字を保ち、`findP` は指定された点の所属を保つ。したがって第二の場合、完全な初等性は別の内部添字を返してもかまわない。
<!--/-->

```agda
    ∣ (Lset γ , Lγ∈) , ∣ (p , p∈) , ∣ (Lset p , Lp∈) , (sat , mem) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset p , Lp∈) ∷ (p , p∈) ∷ (Lset γ , Lγ∈) ∷ []

```

<!--en-->
Completeness supplies the common core. Since `γ` is adequate, `p` is ordinal,
and `p ∈ γ`, completeness proves that `(Lset p,p,Lset γ)` satisfies `levelFo` in
the ambient hierarchy. Notice what completeness does and does not establish:
it validates this particular externally prepared triple, but it neither says
that every satisfying triple uses `p` nor makes the later internal index
unique.
<!--zh-->
完备性给出两条查询共用的核心。由 `γ` 的充分性、`p` 的序数性与 `p ∈ γ`，它证明 `(Lset p,p,Lset γ)` 在外围层级中满足 `levelFo`。这里应区分完备性给出什么与不给出什么：它验证这一个在外围备好的三元组，却不声称每个满足公式的三元组都使用 `p`，也不使稍后得到的内部索引唯一。
<!--ja-->
完全性が、二つの問い合わせに共通する核を与える。`γ` の十分さ、`p` の順序数性、および `p ∈ γ` から、三つ組 `(Lset p,p,Lset γ)` が周囲の階層で `levelFo` を満たすことを示す。完全性が何を示し、何を示さないかを区別する必要がある。この外側で準備した特定の三つ組を検証するが、公式を満たすすべての三つ組が `p` を使うとは述べず、後で得る内部の添字を一意にもしない。
<!--/-->

```agda
    amb : ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
    amb = level-complete γ adγ p op p∈γ

```

<!--en-->
As before, the transfer at this point is only between the ambient hierarchy
and the structure on `Lset lam`. The backward direction of `Cy.atL` uses the
Δ₀ certificate for `levelFo` to read ambient satisfaction at the three
underlying sets as satisfaction at their stage representatives. The
`embed-map` path then puts the constant-free core into the constant domain of
the surrounding hull query. The result is the first conjunct required by
`stageP`; no unbounded quantifier has been transported by this bounded step.
<!--zh-->
与前一条查询相同，此处的搬运只发生在外围层级与 `Lset lam` 上的层结构之间。反向使用 `Cy.atL`，凭 `levelFo` 的 Δ₀ 证书，把三个底层集合处的外围满足读成它们的层代表处的满足。路径 `embed-map` 再把无常元核心放进外围 Skolem 壳查询的常元域。所得正是 `stageP` 所需的第一个合取支；这次有界搬运并未搬运任何无界量词。
<!--ja-->
前の問い合わせと同じく、この時点での移送は周囲の階層と `Lset lam` 上の段階構造との間だけで行われる。`Cy.atL` の逆向きは、`levelFo` の Δ₀ の証拠を使い、三つの基礎集合での周囲の充足を、それらの段階内の表示での充足として読む。続いて `embed-map` のパスが、定数を持たない核を、周囲の Skolem 包の問い合わせが使う定数域へ移す。これは `stageP` が必要とする第一の連言支である。この有界な一歩では、非有界な量化子を一つも移していない。
<!--/-->

```agda
    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ mapFo A.inL (embed levelFo) ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym (embed-map A.inL levelFo))
            (subst ⟨_⟩ (sym (Cy.atL Δ₀-levelFo δ)) amb)

```

<!--en-->
The remaining conjunct says that the interpretation of `yM` belongs to
`Lset p`. Its underlying set is `fst yM`, and the path `ey : fst yM ≡ y`
allows the given membership `y ∈ Lset p` to be transported backward to that
interpretation. This small rewrite is what places the fixed point into the
query while leaving the index unfixed. When elementarity later returns a
triple `(u,p′,z)`, the retained conclusion will be `y ∈ u`, with no equation
between `p′` and the present `p`.
<!--zh-->
余下的合取支断言 `yM` 的解释属于 `Lset p`。它的底层集合是 `fst yM`，而路径 `ey : fst yM ≡ y` 可把给定的成员关系 `y ∈ Lset p` 反向搬到这个解释上。正是这次小改写把指定的点放进查询，同时不固定索引。初等性稍后返回三元组 `(u,p′,z)` 时，保留下来的结论将是 `y ∈ u`，并没有 `p′` 与此处 `p` 之间的等式。
<!--ja-->
残る連言支は、`yM` の解釈が `Lset p` に属することを述べる。その基礎集合は `fst yM` であり、パス `ey : fst yM ≡ y` によって、与えられた所属 `y ∈ Lset p` を逆向きにその解釈へ移せる。この小さな書き換えが、添字を固定せずに指定された点を問い合わせへ入れる。後で初等性が三つ組 `(u,p′,z)` を返すとき、保持される結論は `y ∈ u` であり、`p′` と現在の `p` の間の等式はない。
<!--/-->

```agda
    mem : ⟨ fst (A.inL yM) ∈ˢ Lset p ⟩
    mem = subst (λ w → ⟨ w ∈ˢ Lset p ⟩) (sym ey) y∈Lp
```

<!--en-->
For a set `d`, `Witness d` records under propositional truncation three
facts: some bound `z` belongs to the hull, the prescribed stage `Lset d`
belongs to the hull, and `(Lset d,d,z)` satisfies `levelFo` in the ambient
hierarchy. The type itself can be formed for any `d`; the construction below
requires both `IsOrd d` and `d ∈ M`. Keeping the package truncated is enough
for the later proposition-valued closure and equality conclusions, and it
prevents the proof from treating the adequate bound as chosen data.
<!--zh-->
对集合 `d`，`Witness d` 在命题截断下记录三项事实：某个界 `z` 属于 Skolem 壳，指定的层 `Lset d` 属于 Skolem 壳，并且 `(Lset d,d,z)` 在外围层级中满足 `levelFo`。这个类型可对任意 `d` 写下，但下文的构造同时需要 `IsOrd d` 与 `d ∈ M`。保留命题截断已经足以支持后面取命题值的闭合与等式结论，也避免把充分界误当作选定的数据。
<!--ja-->
集合 `d` に対して、`Witness d` は命題的切り詰めのもとで三つの事実を記録する。ある上界 `z` が Skolem 包に属し、指定された段階 `Lset d` が Skolem 包に属し、さらに `(Lset d,d,z)` が周囲の階層で `levelFo` を満たすことである。この型自体は任意の `d` に対して作れるが、以下の構成には `IsOrd d` と `d ∈ M` の両方が必要である。包みを切り詰めたままにしても、後で必要となる命題値の閉性と等式の結論には十分であり、十分な上界を選択済みのデータとして扱うこともない。
<!--/-->

```agda
  Witness : S → Type (ℓ-suc ℓ)
  Witness d = ∥ Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                           × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ ) ∥₁

```

<!--en-->
The construction first places the hull member `d` in the ambient stage:
`Hull⊆L` gives `d ∈ Lset lam`. Superadequacy, however, is indexed by members
of the ordinal `lam`, rather than by arbitrary members of its constructible
stage. The local fact `d∈λ` established next bridges precisely this gap.
Once it is available, `sup d d∈λ` merely supplies an adequate stage above `d`;
the outer `rec₁` may use that truncated supply because its target
`Witness d` is itself a proposition.
<!--zh-->
构造首先把 Skolem 壳成员 `d` 放进外围层：`Hull⊆L` 给出 `d ∈ Lset lam`。然而，超充分性接收的是序数 `lam` 的成员，而不是其可构造层的任意成员。下一步建立的局部事实 `d∈λ` 恰好跨过这道差别。得到它以后，`sup d d∈λ` 只在 `d` 之上给出一个充分层；由于目标 `Witness d` 本身是命题，外层 `rec₁` 可以使用这份被命题截断的供给。
<!--ja-->
構成はまず、Skolem 包の要素 `d` を周囲の段階へ入れる。`Hull⊆L` から `d ∈ Lset lam` が得られる。しかし強化された十分さが受け取るのは、構成可能段階の任意の要素ではなく、順序数 `lam` の要素である。次に示す局所的な事実 `d∈λ` が、まさにこの隔たりを埋める。それが得られると、`sup d d∈λ` は `d` より上の十分な段階を供給するだけである。行き先の `Witness d` 自体が命題なので、外側の `rec₁` はこの命題的に切り詰められた供給を利用できる。
<!--/-->

```agda
  witness : (d : S) → IsOrd d → ⟨ d ∈ˢ M ⟩ → Witness d
  witness d od d∈M = rec₁ squash₁ step1 (sup d d∈λ)
    where
    d∈Lλ : ⟨ d ∈ˢ Lset lam ⟩
    d∈Lλ = Hull⊆L d d∈M
```

<!--en-->
To recover index membership, apply the stage reflection lemma to
`d ∈ Lset lam`. Its hypotheses expose the exact reason the step works:
`lam` is ordinal by the module parameter and `d` is ordinal by the caller.
Only under those ordinal hypotheses does membership of `d` in the stage at
`lam` imply `d ∈ lam`. This is a comparison of ordinal indices, not a general
rank principle for arbitrary sets.
<!--zh-->
为了恢复索引成员关系，对 `d ∈ Lset lam` 应用层反映引理。它的前提准确揭示这一步为何成立：模块参数说明 `lam` 是序数，调用方则说明 `d` 是序数。只有在这两项序数性前提下，`d` 属于 `lam` 处之层才能推出 `d ∈ lam`。这是序数索引之间的比较，并非任意集合都适用的一般秩原理。
<!--ja-->
添字への所属を取り戻すため、`d ∈ Lset lam` に段階の反映補題を適用する。その仮定を見ると、この一歩が成り立つ理由が明確である。モジュールのパラメータにより `lam` は順序数であり、呼び出し側の仮定により `d` も順序数である。この二つの順序数性のもとでのみ、`lam` での段階への `d` の所属から `d ∈ lam` が従う。これは順序数の添字どうしの比較であり、任意の集合に対する一般的な階数原理ではない。
<!--/-->

```agda

    d∈λ : ⟨ d ∈ˢ lam ⟩
    d∈λ = ord∈Lset→∈ lam ordλ d od d∈Lλ

```

<!--en-->
Now successor closure converts the index relation into the second stage
membership needed by `stageA`. From `d ∈ lam`, the earlier lemma
`Lset∈Lλ` yields `Lset d ∈ Lset lam`, with the whole stage occurring as one
element of the outer stage. Together with `d∈Lλ`, this prepares the two
coordinates tied to `d`. Membership of the eventual bound `Lset γ` will be
derived separately after superadequacy supplies `γ`.
<!--zh-->
现在，后继封闭把索引关系转成 `stageA` 所需的第二条层成员关系。由 `d ∈ lam`，前面的引理 `Lset∈Lλ` 给出 `Lset d ∈ Lset lam`，这里整个 `Lset d` 是外层的一个元素。它与 `d∈Lλ` 合起来备好与 `d` 有关的两个坐标。最终的界 `Lset γ` 的成员资格要等超充分性给出 `γ` 后另行推出。
<!--ja-->
ここで後続についての閉性により、添字の関係を `stageA` が必要とする第二の段階所属へ変える。`d ∈ lam` から、先の補題 `Lset∈Lλ` は `Lset d ∈ Lset lam` を与える。このとき段階 `Lset d` 全体が、外側の段階の一つの要素として現れる。これと `d∈Lλ` を合わせると、`d` に関係する二つの座標が準備できる。最後の上界 `Lset γ` の所属は、強化された十分さが `γ` を供給した後で別に導く。
<!--/-->

```agda
    Ld∈Lλ : ⟨ Lset d ∈ˢ Lset lam ⟩
    Ld∈Lλ = Lset∈Lλ d d∈λ

```

<!--en-->
Superadequacy returns, under propositional truncation, an index `γ` with
`γ ∈ lam`, `d ∈ γ`, and `Adequate γ`. For any such triple, `step1` will build
`Witness d`: it first constructs the full query in the ambient stage, uses
elementarity to obtain its truncated existential answer in the hull, and
eliminates that answer only into the truncated witness goal. Thus the proof
may reason with a temporary `γ` inside the eliminator, but no choice of `γ`
escapes into the theorem's data.
<!--zh-->
超充分性在命题截断下返回一个索引 `γ`，满足 `γ ∈ lam`、`d ∈ γ` 与 `Adequate γ`。对任意这样的三元组，`step1` 都会构造 `Witness d`：先在外围层中建立整条查询，再用初等性取得该查询在 Skolem 壳中的被截断存在回答，最后只把这个回答消去到被截断的见证目标。因此，证明可以在消去器内部临时使用 `γ`，却不会让某个 `γ` 的选择逸出成为定理数据。
<!--ja-->
強化された十分さは、命題的切り詰めのもとで、`γ ∈ lam`、`d ∈ γ`、`Adequate γ` を満たす添字 `γ` を返す。そのような三つ組ごとに `step1` は `Witness d` を構成する。まず周囲の段階で問い合わせ全体を立て、初等性によってその切り詰められた存在の答えを Skolem 包の中で得て、その答えを切り詰められた証人の目標へだけ除去する。したがって、除去子の内部では一時的な `γ` を使えるが、`γ` の選択が定理のデータとして外へ出ることはない。
<!--/-->

```agda
    step1 : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ d ∈ˢ γ ⟩ × Adequate γ) → Witness d
    step1 (γ , γ∈λ , d∈γ , adγ) =
      rec₁ squash₁ takeZ hullSat
      where
      Lγ∈Lλ : ⟨ Lset γ ∈ˢ Lset lam ⟩
```

<!--en-->
The supplied relation `γ ∈ lam` gives the last ambient-stage membership.
Applying `Lset∈Lλ` at `γ` yields `Lset γ ∈ Lset lam`. The three entries
`Lset d`, `d`, and `Lset γ` are now all legitimate elements of the stage
structure, so the completeness witness from `stageA` can be stated there.
This use of `γ` needs no claim that it is least or uniquely determined.
<!--zh-->
给定的关系 `γ ∈ lam` 产生最后一条外围层成员关系。在 `γ` 处应用 `Lset∈Lλ`，得到 `Lset γ ∈ Lset lam`。至此，`Lset d`、`d` 与 `Lset γ` 都是层结构中的合法元素，因而可在该结构中陈述 `stageA` 的完备性见证。这里既不需要 `γ` 最小，也不需要它唯一确定。
<!--ja-->
与えられた関係 `γ ∈ lam` から、最後の周囲の段階への所属が得られる。`γ` に `Lset∈Lλ` を適用すると `Lset γ ∈ Lset lam` となる。これで `Lset d`、`d`、`Lset γ` はすべて段階構造の正当な要素となり、`stageA` の完全性の証人をそこで述べられる。この `γ` の使用には、最小性も一意性も必要ない。
<!--/-->

```agda
      Lγ∈Lλ = Lset∈Lλ γ γ∈λ

```

<!--en-->
The constant named by the fixed-index query must be an element of the hull's
carrier, not merely an ambient set. Pairing `d` with the given proof
`d ∈ M` produces `dM : A.SM`. Its underlying set is definitionally `d`, so
the equality argument passed to `stageA` is reflexivity. This packaging does
not create a new representative or invoke the collapse; it presents the
existing hull member in the language in which elementarity is stated.
<!--zh-->
固定索引查询所命名的常元必须是 Skolem 壳载体的元素，不能只是一个外围集合。把 `d` 与给定的 `d ∈ M` 证明配对，得到 `dM : A.SM`。它的底层集合依定义就是 `d`，所以传给 `stageA` 的等式证明是自反性。这次打包既不产生新的代表，也不调用塌缩；它只是把已有的 Skolem 壳成员呈现在初等性所使用的语言中。
<!--ja-->
固定添字の問い合わせが名づける定数は、単なる周囲の集合ではなく、Skolem 包の台の要素でなければならない。`d` と、与えられた `d ∈ M` の証明を組にすると `dM : A.SM` が得られる。その基礎集合は定義により `d` そのものなので、`stageA` に渡す等式の証明は反射律である。この包装は新しい代表を作らず、崩壊も使わない。既存の Skolem 包の要素を、初等性が述べられている言語で提示するだけである。
<!--/-->

```agda
      dM : A.SM
      dM = d , d∈M

```

<!--en-->
Full elementarity now acts on `findA`. The preceding call to `stageA` proves
the relabelled query in the stage structure on `Lset lam`; the symmetric
direction of `elem` transports that satisfaction to the hull structure.
This step may carry the three unbounded existential quantifiers because
`elem` applies to arbitrary formulas. It must therefore be distinguished
from `Cy.atL`, which was used only on the Δ₀ core `levelFo`. The result
`hullSat` says merely that a suitable triple exists in the hull.
<!--zh-->
现在对 `findA` 使用完整初等性。前面对 `stageA` 的调用证明了改名后的查询在 `Lset lam` 上的层结构中成立；`elem` 的对称方向把这份满足搬到 Skolem 壳结构。因为 `elem` 适用于任意公式，这一步可以连同三个无界存在量词一起搬运。因此必须把它与 `Cy.atL` 区分开，后者只用于 Δ₀ 核心 `levelFo`。所得 `hullSat` 只说明 Skolem 壳中存在合适的三元组。
<!--ja-->
ここで `findA` に完全な初等性を使う。先の `stageA` の呼び出しは、改名された問い合わせが `Lset lam` 上の段階構造で成り立つことを示した。`elem` の対称方向は、その充足を Skolem 包の構造へ移す。`elem` は任意の論理式に適用できるため、この一歩では三つの非有界な存在量化子も一緒に移せる。したがって、Δ₀ の核 `levelFo` にだけ用いた `Cy.atL` とは区別しなければならない。得られる `hullSat` は、適切な三つ組が Skolem 包に存在することだけを述べる。
<!--/-->

```agda
      hullSat : ⟨ [] Mse.⊨ findA dM ⟩
      hullSat = subst ⟨_⟩ (sym (elem 0 (findA dM) []))
        (stageA d γ od adγ d∈γ dM refl d∈Lλ Ld∈Lλ Lγ∈Lλ)

```

<!--en-->
To turn an answer to `findA` into the desired witness, suppose its outer two
coordinates `z` and `d′` have been exposed. The innermost existential then
provides a hull element `a`, satisfaction of the embedded core at
`(a,d′,z)`, and the equation `fst d′ ≡ d`. The helper `finishA` converts this
untruncated branch into a bound in `M`, membership of the prescribed
`Lset d` in `M`, and ambient satisfaction at `(Lset d,d,fst z)`. The
conversion will rely on soundness, not on uniqueness of the existential
witnesses.
<!--zh-->
为了把 `findA` 的回答转成所需见证，先设它外面的两个坐标 `z` 与 `d′` 已在消去器中展开。最内层存在量词于是给出 Skolem 壳元素 `a`、嵌入核心在 `(a,d′,z)` 处的满足，以及等式 `fst d′ ≡ d`。辅助函数 `finishA` 把这个未截断的分支转换成三项数据：`M` 中的一个界、指定的 `Lset d` 对 `M` 的成员资格，以及 `(Lset d,d,fst z)` 处的外围满足。这次转换依赖可靠性，并不依赖存在见证的唯一性。
<!--ja-->
`findA` の答えを必要な証人へ変えるため、外側の二つの座標 `z` と `d′` が除去子の中ですでに展開されたとする。すると最も内側の存在量化子は、Skolem 包の要素 `a`、`(a,d′,z)` での埋め込まれた核の充足、および等式 `fst d′ ≡ d` を与える。補助関数 `finishA` は、この切り詰められていない分岐を、`M` 内の上界、指定された `Lset d` の `M` への所属、および `(Lset d,d,fst z)` での周囲の充足へ変換する。この変換が使うのは健全性であり、存在証人の一意性ではない。
<!--/-->

```agda
      finishA : (z d' : A.SM)
              → Σ[ a ∈ A.SM ]
                  ( ⟨ (a ∷ d' ∷ z ∷ []) Mse.⊨ embed levelFo ⟩
                  × (fst d' ≡ d) )
              → Σ[ w ∈ S ] ( ⟨ w ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
```

<!--en-->
The embedded core is first read back in the ambient hierarchy. Because
`levelFo` is Δ₀, the bounded comparison `Cy.atM` identifies its satisfaction in the hull structure
at `(a,d′,z)` with ambient satisfaction at the underlying sets
`(fst a,fst d′,fst z)`. This bounded step acts only on the core
already obtained after the existential witnesses were exposed. It does not
eliminate the unbounded query or by itself identify the first coordinate as
a constructible stage.
<!--zh-->
首先把嵌入核心读回外围层级。由于 `levelFo` 是 Δ₀，有界比较 `Cy.atM` 把它在 Skolem 壳结构中于 `(a,d′,z)` 处的满足，认同为它在底层集合 `(fst a,fst d′,fst z)` 处的外围满足。这次有界步骤只作用于存在见证已经展开后取得的核心；它既不消去无界查询，也不会独自把第一坐标认同为可构造层。
<!--ja-->
まず、埋め込まれた核を周囲の階層で読み直す。`levelFo` は Δ₀ なので、有界な比較 `Cy.atM` は Skolem 包の構造における `(a,d′,z)` での充足を、基礎集合 `(fst a,fst d′,fst z)` での周囲の充足と同一視する。この有界な一歩は、存在証人を展開した後に得られた核だけに作用する。非有界な問い合わせを除去するものでも、それだけで第一の座標を構成可能段階と同一視するものでもない。
<!--/-->

```agda
                           × ⟨ (Lset d ∷ d ∷ w ∷ []) ⊨ₚ levelFo ⟩ )
      finishA z d' (a , sat , ed) = fst z , snd z , Ld∈M , amb'
        where
        amb : ⟨ (fst a ∷ fst d' ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
        amb = subst ⟨_⟩ (Cy.atM Δ₀-levelFo (a ∷ d' ∷ z ∷ [])) sat
```

<!--en-->
The soundness theorem for `levelFo` requires all three underlying sets to be
constructible. Each is a member of the hull, hence belongs to `Lset lam` by
`Hull⊆L`; since `lam` is ordinal, `isLλ` turns those three memberships into
the required constructibility proofs. With these separate hypotheses and
the ambient satisfaction `amb`, `level-sound` identifies
`fst a` with `Lset (fst d′)`. Satisfaction alone would not justify this
identification.
<!--zh-->
`levelFo` 的可靠性定理要求三个底层集合分别可构造。三者都是 Skolem 壳的成员，所以由 `Hull⊆L` 分别属于 `Lset lam`；又因为 `lam` 是序数，`isLλ` 把这三条成员关系转成所需的可构造性证明。将这些独立前提与外围满足 `amb` 一同交给 `level-sound`，便得到 `fst a` 与 `Lset (fst d′)` 的认同。仅有公式满足并不足以推出这项认同。
<!--ja-->
`levelFo` の健全性定理は、三つの基礎集合がそれぞれ構成可能であることを要求する。三つとも Skolem 包の要素なので、`Hull⊆L` によりそれぞれ `Lset lam` に属する。さらに `lam` が順序数であるため、`isLλ` がこれら三つの所属を必要な構成可能性の証明へ変える。この別々の仮定と周囲での充足 `amb` を `level-sound` に渡すと、`fst a` は `Lset (fst d′)` と同一視される。公式の充足だけでは、この同一視を正当化できない。
<!--/-->

```agda

        ea : fst a ≡ Lset d
        ea = level-sound (fst a) (fst d') (fst z)
               (isLλ (fst a) (Hull⊆L (fst a) (snd a)))
               (isLλ (fst d') (Hull⊆L (fst d') (snd d')))
               (isLλ (fst z) (Hull⊆L (fst z) (snd z))) amb
```

<!--en-->
The equality conjunct of `findA` now does the work for which it was designed.
Soundness gave `fst a ≡ Lset (fst d′)`, and applying `Lset` to
`ed : fst d′ ≡ d` gives `Lset (fst d′) ≡ Lset d`. Composing the two paths
yields `ea : fst a ≡ Lset d`. Thus the returned first coordinate is the
stage at the original prescribed index. Without the equality conjunct, the
same soundness argument would identify it only as the stage at some returned
index.
<!--zh-->
现在，`findA` 的等式合取支兑现了它的用途。可靠性已经给出 `fst a ≡ Lset (fst d′)`；把 `Lset` 作用于 `ed : fst d′ ≡ d`，又得到 `Lset (fst d′) ≡ Lset d`。复合两条路径便得 `ea : fst a ≡ Lset d`。因此，返回的第一坐标正是原先指定索引处的层。若没有这个等式合取支，同样的可靠性论证只能把它认同为某个返回索引处的层。
<!--ja-->
ここで `findA` の等式の連言支が、意図された役割を果たす。健全性から `fst a ≡ Lset (fst d′)` が得られ、`ed : fst d′ ≡ d` に `Lset` を作用させると `Lset (fst d′) ≡ Lset d` が得られる。二つのパスを合成すれば `ea : fst a ≡ Lset d` である。したがって、返された第一の座標は、もともと指定した添字での段階である。この等式の連言支がなければ、同じ健全性の議論から分かるのは、返された何らかの添字での段階だということだけである。
<!--/-->

```agda
             ∙ cong Lset ed

```

<!--en-->
The returned coordinate `a` already carries `snd a`, its membership in the
hull. Transporting that proposition along `ea` yields
`Lset d ∈ M`. This is the closure fact sought for the prescribed hull
ordinal `d`. It is derived from the hypothesis `sup`, full elementarity, bounded
absoluteness, and soundness of the level description; no additional closure
axiom for `M` is assumed, and the Mostowski collapse has not yet entered this
part of the argument.
<!--zh-->
返回的坐标 `a` 已经带有 `snd a`，即它属于 Skolem 壳的证明。沿 `ea` 搬运这个命题，得到 `Lset d ∈ M`。这就是对指定 Skolem 壳序数 `d` 所需的闭合事实。它由超充分性、完整初等性、有界绝对性与层描述的可靠性共同推出，并未为 `M` 另设闭合公理；这部分论证也尚未使用 Mostowski 塌缩。
<!--ja-->
返された座標 `a` は、Skolem 包への所属 `snd a` をすでに伴っている。この命題を `ea` に沿って移すと `Lset d ∈ M` が得られる。これが、指定された Skolem 包の順序数 `d` に対して求めていた閉性である。これは、強化された十分さ、完全な初等性、有界絶対性、および段階の記述の健全性から導かれる。`M` に対する別の閉性公理を仮定しておらず、この部分の議論では Mostowski 崩壊もまだ使っていない。
<!--/-->

```agda
        Ld∈M : ⟨ Lset d ∈ˢ M ⟩
        Ld∈M = subst (λ w → ⟨ w ∈ˢ M ⟩) ea (snd a)

```

<!--en-->
The witness package also retains a correctly oriented copy of the level
description. Starting with ambient satisfaction at
`(fst a,fst d′,fst z)`, transport the middle coordinate along `ed` and the
first coordinate along `ea`. The result is satisfaction at
`(Lset d,d,fst z)`, exactly the third field of `Witness d`. Together with
`snd z` and the newly obtained `Lset d ∈ M`, it forms the untruncated branch
that will be placed back under propositional truncation.
<!--zh-->
见证包还要保留一份方向正确的层描述。从 `(fst a,fst d′,fst z)` 处的外围满足出发，先沿 `ed` 搬运中间坐标，再沿 `ea` 搬运第一坐标，得到 `(Lset d,d,fst z)` 处的满足，恰是 `Witness d` 的第三个字段。它与 `snd z` 以及刚得到的 `Lset d ∈ M` 合在一起，形成一个未截断分支，随后再放回命题截断之下。
<!--ja-->
証人の包みには、向きの整った段階の記述も残す必要がある。`(fst a,fst d′,fst z)` での周囲の充足から始め、中央の座標を `ed` に沿って移し、第一の座標を `ea` に沿って移す。すると `(Lset d,d,fst z)` での充足が得られ、これはちょうど `Witness d` の第三のフィールドである。これを `snd z` および新しく得た `Lset d ∈ M` と合わせると、切り詰められていない一つの分岐ができ、後で命題的切り詰めの中へ戻される。
<!--/-->

```agda
        amb' : ⟨ (Lset d ∷ d ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
        amb' = subst (λ v → ⟨ (v ∷ d ∷ fst z ∷ []) ⊨ₚ levelFo ⟩) ea
          (subst (λ p → ⟨ (fst a ∷ p ∷ fst z ∷ []) ⊨ₚ levelFo ⟩) ed amb)

```

<!--en-->
After `z` and `d′` are fixed, the innermost existential asserts only the mere existence of a suitable `a`. Every explicit `a` determines, through `finishA`, the desired truncated witness for `d`; mapping under the truncation therefore preserves exactly the existence needed. The construction never exposes a selected `a`, and the remaining coordinates will be treated with the same propositional restriction.
<!--zh-->
固定 `z` 与 `d′` 后，最内层存在量词只保留某个合适的 `a` 仅仅存在。每个显式的 `a` 都可经 `finishA` 产生所需的 `d` 的截断见证，因此在截断内部作映射恰好保留了所需的存在性。构造不会暴露一个选定的 `a`，其余坐标也将服从同样的命题性限制。
<!--ja-->
`z` と `d′` を固定すると、最も内側の存在量化子が保つのは、適切な `a` が単に存在することだけである。明示的な各 `a` から `finishA` によって `d` に対する必要な切り詰められた証人が得られるので、切り詰めの内部で写すことで必要な存在性だけを保てる。選ばれた `a` が外へ現れることはなく、残る座標も同じ命題的な制限のもとで扱われる。
<!--/-->

```agda
      takeD : (z : A.SM)
            → Σ[ d' ∈ A.SM ]
                ⟨ (d' ∷ z ∷ []) Mse.⊨ ∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM)) ⟩
            → Witness d
      takeD z (d' , hd) = map₁ (finishA z d') hd
```

<!--en-->
With the outer witness `z` already fixed, the next truncation hides the middle coordinate `d′`. Eliminating it into the proposition `Witness d` passes each local `d′` to the preceding construction. The enclosing elimination, already used in `step1`, handles the outer witness `z`. Consequently the witnesses from superadequacy and all three existential quantifiers remain local to propositional conclusions; neither an adequate bound nor a triple of hull witnesses is selected as global data.
<!--zh-->
最外层见证 `z` 已经固定以后，下一层截断隐藏的是中间坐标 `d′`。把它消去到命题 `Witness d`，就是把每个局部的 `d′` 交给前面的构造。`step1` 中已经出现的外层消去则处理见证 `z`。因此，超充分性以及三个存在量词给出的见证都只局限于命题结论；充分界与壳中三元组都没有被选成全局数据。
<!--ja-->
最も外側の証人 `z` がすでに固定された後、次の切り詰めが隠しているのは中央の座標 `d′` である。これを命題 `Witness d` へ除去し、局所的な各 `d′` を先の構成へ渡す。`step1` ですでに用いた外側の除去が、証人 `z` を処理する。したがって、強化された十分さと三つの存在量化子から得られる証人は、すべて命題である結論の内部にとどまる。十分な上界も包内の三つ組も、大域的なデータとして選ばれない。
<!--/-->

```agda

      takeZ : Σ[ z ∈ A.SM ]
                ⟨ (z ∷ []) Mse.⊨ ∃̇ (∃̇ (embed levelFo ∧̇ (var (suc zero) ≐ con dM))) ⟩
            → Witness d
      takeZ (z , hz) = rec₁ squash₁ (takeD z) hz
```

<!--en-->
We can now state the local compatibility between the collapse and constructible stages. If `d` is an ordinal in the hull, `commute` proves both that `Lset d` is again in the hull and that collapsing this stage gives `Lset (π d)`. The proof eliminates `Witness d` into a product of propositions. Hull membership is proposition-valued, and equality between the two ambient sets is a proposition because the ambient cumulative hierarchy is an h-set. Their product is therefore a valid target for eliminating propositional truncation.
<!--zh-->
现在可以陈述塌缩与可构造层之间的局部相容性。若 `d` 是 Skolem 壳中的序数，则 `commute` 同时证明 `Lset d` 仍在壳中，并且塌缩这一层得到 `Lset (π d)`。证明把 `Witness d` 消去到两个命题的乘积中。壳成员关系取值于命题，而两个外围集合之间的等式也是命题，因为外围累积层级是 h-集合。因此，两者的乘积是消去命题截断的合法目标。
<!--ja-->
ここで、崩壊と構成可能段階の局所的な整合性を述べられる。`d` が Skolem 包の順序数なら、`commute` は `Lset d` が再び包に属することと、この段階を崩壊すると `Lset (π d)` が得られることを同時に証明する。証明は `Witness d` を命題の積へ除去する。包への所属は命題を値にとり、周囲の二つの集合の等しさも、周囲の累積階層が h-集合であるため命題である。したがって、その積は命題的切り詰めを除去できる正当な目標である。
<!--/-->

```agda
  commute : (d : S) → IsOrd d → (d∈M : ⟨ d ∈ˢ M ⟩)
          → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
  commute d od d∈M =
    rec₁ (isProp× (snd (Lset d ∈ˢ M)) (isSetS (π (Lset d)) (Lset (π d))))
           go (witness d od d∈M)
```

<!--en-->
After opening the witness locally, its hull-membership component for `Lset d` supplies the first conclusion unchanged. The other two pieces, a hull member `z` and satisfaction of `levelFo(Lset d,d,z)`, are retained for the equality. This division mirrors the two conclusions of `commute`: closure of the hull at the stage indexed by `d` comes directly from `Witness d`, whereas compatibility with the collapse still has to be proved from the bounded description of that stage.
<!--zh-->
在局部打开见证后，其中关于 `Lset d` 的壳成员资格原样给出第一个结论。其余两项数据，即壳成员 `z` 与 `levelFo(Lset d,d,z)` 的满足关系，则留给等式证明使用。这一区分正好对应 `commute` 的两个结论：Skolem 壳在由 `d` 索引的层处闭合，直接来自 `Witness d`；而该层与塌缩的相容性，仍须由这层的有界描述推出。
<!--ja-->
証人を局所的に開くと、`Lset d` が包に属するという成分が、最初の結論をそのまま与える。残る二つのデータ、包の要素 `z` と `levelFo(Lset d,d,z)` の充足は、等式の証明に使うために残す。この分担は `commute` の二つの結論に対応している。`d` が添字づける段階について Skolem 包が閉じていることは `Witness d` から直接得られるが、その段階と崩壊との整合性は、段階の有界な記述からさらに証明する必要がある。
<!--/-->

```agda
    where
    go : Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                    × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ )
       → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
    go (z , z∈M , Ld∈M , amb) = Ld∈M , eq
```

<!--en-->
The equality proof first transports the bounded description through the collapse. The environment consists of the three hull members `Lset d`, `d`, and `z`, together with their membership proofs. Since `levelFo` is Δ₀ and has no constants, `Cy.push` replaces every coordinate by its collapsed value and yields satisfaction of `levelFo(π (Lset d),π d,π z)`. This is the same local Δ₀ transport used earlier for ordinality, now applied to the three-variable description of a constructible stage.
<!--zh-->
等式证明首先把有界描述沿塌缩搬运。环境由三个 Skolem 壳成员 `Lset d`、`d`、`z` 及其成员资格证明组成。由于 `levelFo` 是无常元的 Δ₀ 公式，`Cy.push` 可把每个坐标换成其塌缩值，得到 `levelFo(π (Lset d),π d,π z)` 的满足关系。这与前文搬运序数性时使用的是同一种局部 Δ₀ 搬运，只是此处施用于描述可构造层的三变元公式。
<!--ja-->
等式の証明では、まず有界な記述を崩壊の向こうへ移す。環境は、Skolem 包の三つの要素 `Lset d`、`d`、`z` と、それぞれの所属の証明からなる。`levelFo` は定数を含まない Δ₀ 論理式なので、`Cy.push` は各座標をその崩壊値で置き換え、`levelFo(π (Lset d),π d,π z)` の充足を与える。これは先に順序数性へ使ったのと同じ局所的な Δ₀ 移送を、今度は構成可能段階を記述する三変数の論理式へ適用したものである。
<!--/-->

```agda
      where
      pushed : ⟨ (π (Lset d) ∷ π d ∷ π z ∷ []) ⊨ₚ levelFo ⟩
      pushed = Cy.push Δ₀-levelFo ((Lset d , Ld∈M) ∷ (d , d∈M) ∷ (z , z∈M) ∷ []) amb

```

<!--en-->
To read this transported formula by soundness, all three collapsed coordinates must be constructible. Each coordinate belongs to the collapse image by `πX-intro`, since it is the collapse of a hull member; the pointwise hypothesis `pixL` then supplies the required constructibility proofs. Soundness can therefore identify the first collapsed coordinate with the constructible stage indexed by the second:

`π (Lset d) ≡ Lset (π d)`.

The auxiliary value `π z` is needed to validate the description, but it does not occur in the resulting equality.
<!--zh-->
要用可靠性读取搬运后的公式，三个塌缩坐标都必须可构造。每个坐标都是某个 Skolem 壳成员的塌缩，故由 `πX-intro` 属于塌缩像；逐点假设 `pixL` 随即给出所需的可构造性证明。因此，可靠性可把第一个塌缩坐标认同为由第二个坐标索引的可构造层：

`π (Lset d) ≡ Lset (π d)`。

辅助值 `π z` 用于验证这项描述，但不出现在所得等式中。
<!--ja-->
移送された論理式を健全性によって読むには、崩壊された三つの座標がすべて構成可能でなければならない。各座標は Skolem 包の要素の崩壊なので、`πX-intro` によって崩壊像に属し、点ごとの仮定 `pixL` が必要な構成可能性の証明を与える。これにより健全性は、崩壊された第一座標を、第二座標が添字づける構成可能段階と同一視できる。

`π (Lset d) ≡ Lset (π d)`。

補助的な値 `π z` はこの記述を検証するために必要であるが、得られる等式には現れない。
<!--/-->

```agda
      eq : π (Lset d) ≡ Lset (π d)
      eq = level-sound (π (Lset d)) (π d) (π z)
             (pixL (π (Lset d)) (HS.C.πX-intro (Lset d) Ld∈M))
             (pixL (π d) (HS.C.πX-intro d d∈M))
             (pixL (π z) (HS.C.πX-intro z z∈M))
```

<!--en-->
The transported satisfaction is the final premise of that soundness argument. Its conclusion must be read with the hypotheses of `commute`: the equation holds for an ordinal `d` that belongs to the hull. It is not a global equation between the two operations `π` and `Lset`. This precise locality is sufficient, because the two applications below first recover a relevant hull ordinal and only then invoke the compatibility equation.
<!--zh-->
搬运后的满足关系是上述可靠性论证的最后一个前提。读取其结论时必须保留 `commute` 的假设：该等式只对属于 Skolem 壳的序数 `d` 成立。它不是运算 `π` 与 `Lset` 之间的全局等式。这样的局部性已经足够，因为下面两处应用都会先找回一个相关的壳中序数，然后才调用这条相容等式。
<!--ja-->
移送された充足は、以上の健全性の議論における最後の前提である。その結論は `commute` の仮定とともに読む必要がある。この等式が成り立つのは、Skolem 包に属する順序数 `d` についてである。これは演算 `π` と `Lset` の間の大域的な等式ではない。この局所性で十分なのは、以下の二つの適用では、まず関係する包内の順序数を取り戻し、その後で整合性の等式を使うからである。
<!--/-->

```agda
             pushed
```

<!--en-->
The first property required by the abstract condensation argument is closure at the image's own ordinals. Given an ordinal `δ` in the collapse image, `levelIn` must show that `Lset δ` also belongs to that image. The membership description `πX-member` provides, under propositional truncation, a hull member `d` with `π d ≡ δ`. Since the target is itself the membership proposition `Lset δ ∈ πX`, this truncated preimage may be opened locally.
<!--zh-->
抽象凝聚论证要求的第一项性质，是塌缩像在自身序数处的层闭合。给定塌缩像中的序数 `δ`，`levelIn` 必须证明 `Lset δ` 也属于该像。成员刻画 `πX-member` 在命题截断下给出一个 Skolem 壳成员 `d`，满足 `π d ≡ δ`。目标本身是成员命题 `Lset δ ∈ πX`，所以可以在局部打开这个带命题截断的原像。
<!--ja-->
抽象的な凝縮の議論が要求する第一の性質は、崩壊像が自身の順序数に対応する段階について閉じていることである。崩壊像の順序数 `δ` が与えられたとき、`levelIn` は `Lset δ` もその像に属することを示さなければならない。要素の特徴づけ `πX-member` は、命題的切り詰めのもとで、`π d ≡ δ` を満たす Skolem 包の要素 `d` を与える。目標そのものが所属命題 `Lset δ ∈ πX` なので、この命題的に切り詰められた原像を局所的に開ける。
<!--/-->

```agda
  levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
  levelIn δ oδ δ∈πX =
    rec₁ (snd (Lset δ ∈ˢ HS.C.πX)) go (HS.C.πX-member δ δ∈πX)
    where
    go : Σ[ d ∈ S ] (⟨ d ∈ˢ M ⟩ × (π d ≡ δ)) → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
```

<!--en-->
Once such a preimage `d` is available, the desired image membership will come from `Lset d`. Indeed, `πX-intro` sends a proof that `Lset d` lies in the hull to a proof that `π (Lset d)` lies in the image. The final transport follows the compatibility equation `π (Lset d) ≡ Lset (π d)` and then applies `Lset` to the preimage equation `π d ≡ δ`. What remains is to justify that `d` is an ordinal and that `Lset d` lies in the hull.
<!--zh-->
取得这样的原像 `d` 后，所求的像成员资格将来自 `Lset d`。确实，若有 `Lset d` 属于 Skolem 壳的证明，`πX-intro` 就给出 `π (Lset d)` 属于塌缩像的证明。最后依次沿相容等式 `π (Lset d) ≡ Lset (π d)`，以及把 `Lset` 施于原像等式 `π d ≡ δ` 所得的等式作传输。余下要说明的是 `d` 为序数，并且 `Lset d` 属于壳。
<!--ja-->
このような原像 `d` が得られれば、求める像への所属は `Lset d` から導ける。実際、`Lset d` が Skolem 包に属するという証明を `πX-intro` に渡すと、`π (Lset d)` が崩壊像に属するという証明が得られる。最後の輸送では、整合性の等式 `π (Lset d) ≡ Lset (π d)` に続いて、原像の等式 `π d ≡ δ` に `Lset` を施した等式を使う。残る課題は、`d` が順序数であり、`Lset d` が包に属することを示すことである。
<!--/-->

```agda
    go (d , d∈M , e) =
      subst (λ w → ⟨ w ∈ˢ HS.C.πX ⟩) (cm .snd ∙ cong Lset e)
            (HS.C.πX-intro (Lset d) (cm .fst))
      where
      od : IsOrd d
```

<!--en-->
Ordinality is recovered before the compatibility lemma is used. Transporting the assumed `IsOrd δ` backward along `π d ≡ δ` gives `IsOrd (π d)`, and `ord-pull` reflects this fact through the collapse to `IsOrd d`. Notice the order of the argument: the preimage description alone says only that `d` is a hull member. Its ordinality comes from the ordinality of `δ` together with reflection for the bounded ordinal formula.
<!--zh-->
调用相容引理之前，先恢复原像的序数性。沿 `π d ≡ δ` 反向传输假设 `IsOrd δ`，得到 `IsOrd (π d)`；`ord-pull` 再把这项事实穿过塌缩反映为 `IsOrd d`。这里的论证次序不可省略：原像刻画本身只说明 `d` 是 Skolem 壳成员；它的序数性来自 `δ` 的序数性与有界序数公式的反映性。
<!--ja-->
整合性の補題を使う前に、原像の順序数性を復元する。仮定 `IsOrd δ` を `π d ≡ δ` に沿って逆向きに輸送すると `IsOrd (π d)` が得られ、`ord-pull` がこの事実を崩壊の手前へ反映して `IsOrd d` を与える。議論の順序に注意してほしい。原像の記述だけから分かるのは、`d` が Skolem 包の要素だということである。その順序数性は、`δ` の順序数性と、有界な順序数論理式に対する反映から得られる。
<!--/-->

```agda
      od = ord-pull d d∈M (subst IsOrd (sym e) oδ)

```

<!--en-->
The hypotheses for `commute` are now complete. Its first component places `Lset d` in the hull, and its second gives `π (Lset d) ≡ Lset (π d)`. Composing the latter with `cong Lset e`, where `e : π d ≡ δ`, identifies this collapsed stage with `Lset δ`; transport then gives the required image membership. Hence the collapse image contains `Lset δ` for every ordinal `δ` that it contains. No closure claim is made for nonordinals or for ordinals outside the image.
<!--zh-->
此时 `commute` 的各项前提已经齐备。它的第一分量把 `Lset d` 放入 Skolem 壳，第二分量给出 `π (Lset d) ≡ Lset (π d)`。把后一个等式与 `cong Lset e` 复合，其中 `e : π d ≡ δ`，便把这个塌缩层认同为 `Lset δ`；再作传输即得所求的像成员资格。因此，塌缩像对其所含的每个序数 `δ` 都包含 `Lset δ`。这里没有对非序数或像外序数作闭合断言。
<!--ja-->
これで `commute` の仮定がすべて揃った。その第一成分は `Lset d` を Skolem 包に入れ、第二成分は `π (Lset d) ≡ Lset (π d)` を与える。後者を、`e : π d ≡ δ` に `Lset` を施した `cong Lset e` と合成すると、この崩壊された段階は `Lset δ` と同一視され、輸送によって求める像への所属が得られる。したがって、崩壊像が順序数 `δ` を含むなら `Lset δ` も含む。順序数でない集合や像の外の順序数について、閉性を主張しているわけではない。
<!--/-->

```agda
      cm : ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
      cm = commute d od d∈M

```

<!--en-->
The second property is covering. For every hull member `y`, it asks merely for an ordinal `γ` in the collapse image such that `π y ∈ Lset γ`. The ordinal, its membership in the image, and this level membership remain under one propositional truncation. Thus a covering stage exists for each `y`, but the theorem chooses no family of such stages and asserts neither minimality nor any comparison of their indices with `lam`.
<!--zh-->
第二项性质是覆盖。对每个 Skolem 壳成员 `y`，它只要求塌缩像中仅仅存在一个序数 `γ`，使 `π y ∈ Lset γ`。该序数、它属于塌缩像的证明以及这条层成员关系，都保留在同一个命题截断之下。因此，每个 `y` 都有覆盖层，但定理没有选出这样的一族层，也不断言其索引最小或与 `lam` 有任何大小关系。
<!--ja-->
第二の性質は被覆である。Skolem 包の各要素 `y` に対して、`π y ∈ Lset γ` を満たす順序数 `γ` が崩壊像の中に単に存在することを求める。その順序数、像への所属、そしてこの段階への所属は、一つの命題的切り詰めのもとに保たれる。したがって各 `y` には被覆する段階が存在するが、そのような段階の族を選ぶことも、添字の最小性や `lam` との大小関係を主張することもない。
<!--/-->

```agda
  cover : (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁
  cover y y∈M = rec₁ squash₁ go (Lset-out lam y (Hull⊆L y y∈M))
    where
    Goal : Type (ℓ-suc ℓ)
```

<!--en-->
The target `Goal` is itself a propositional truncation. This matters twice: the decomposition of `y` supplied by `Lset-out` and the adequate index supplied by superadequacy can both be used locally because their common destination is a proposition. Neither step fixes the final covering index. That index will instead come from the internal answer to the membership query `findP`.
<!--zh-->
目标 `Goal` 本身就是命题截断。这一点会使用两次：`Lset-out` 给出的 `y` 的分解，以及超充分性给出的充分索引，都能在局部使用，因为它们共同到达一个命题。两步都不固定最终的覆盖索引；该索引将来自成员查询 `findP` 的内部回答。
<!--ja-->
目標 `Goal` 自体が命題的切り詰めである。この点は二度使われる。`Lset-out` が与える `y` の分解と、強化された十分さが与える十分な添字は、共通の行き先が命題なので、ともに局所的に利用できる。どちらの段階でも最終的な被覆の添字は固定されない。その添字は、所属の問い合わせ `findP` に対する内部の答えから得られる。
<!--/-->

```agda
    Goal = ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁

```

<!--en-->
The construction starts by locating `y` in the constructible hierarchy. Since every hull member lies in `Lset lam`, `Lset-out` yields, under propositional truncation, an index `c ∈ lam` such that `y` is a definable subset of `Lset c`. Set `p = sucV c`. After successor closure puts `p` back in `lam`, superadequacy supplies, again only under truncation, an adequate `γ ∈ lam` containing `p`. The prepared index `p` provides an external stage that contains `y`; it is not yet the index that the hull will return.
<!--zh-->
构造先在可构造层级中定位 `y`。每个 Skolem 壳成员都属于 `Lset lam`，所以 `Lset-out` 在命题截断下给出一个索引 `c ∈ lam`，使 `y` 是 `Lset c` 的可定义子集。令 `p = sucV c`。后继闭合把 `p` 放回 `lam` 后，超充分性再次仅在命题截断下给出一个包含 `p` 的充分索引 `γ ∈ lam`。预备的索引 `p` 提供一个含有 `y` 的外围层；它尚不是 Skolem 壳随后返回的索引。
<!--ja-->
構成は、まず構成可能階層の中で `y` の位置を定めることから始まる。Skolem 包の各要素は `Lset lam` に属するので、`Lset-out` は命題的切り詰めのもとで、`y` が `Lset c` の定義可能部分集合となる添字 `c ∈ lam` を与える。`p = sucV c` と置く。後続に関する閉性によって `p` を `lam` に戻すと、強化された十分さは、`p` を含む十分な添字 `γ ∈ lam` を、やはり切り詰めのもとで与える。準備した添字 `p` は `y` を含む外側の段階を用意するが、Skolem 包が後で返す添字そのものではない。
<!--/-->

```agda
    go : Σ[ c ∈ S ] (⟨ c ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset c) ⟩) → Goal
    go (c , c∈λ , y∈D) = rec₁ squash₁ go₂ (sup p p∈λ)
      where
      p : S
      p = sucV c
```

<!--en-->
The first auxiliary fact applies the assumed successor closure of `lam` to `c ∈ lam`. It yields `p ∈ lam` for `p = sucV c`. This relation is needed twice: superadequacy is invoked at `p`, and the later ambient witness must place both the ordinal `p` and the stage `Lset p` inside `Lset lam`. The one closure hypothesis on indices supports all of these uses.
<!--zh-->
第一项辅助事实把 `lam` 的后继闭合假设施于 `c ∈ lam`，从而对 `p = sucV c` 得到 `p ∈ lam`。这项关系有两类用途：一方面要在 `p` 处调用超充分性，另一方面，稍后的外围见证必须把序数 `p` 与层 `Lset p` 都放入 `Lset lam`。关于索引的这一条闭合假设支撑了所有这些步骤。
<!--ja-->
最初の補助事実は、`lam` の後続に関する閉性の仮定を `c ∈ lam` に適用し、`p = sucV c` に対する `p ∈ lam` を得る。この関係には二つの用途がある。一方では `p` に強化された十分さを適用し、他方では、後で作る周囲の証人において、順序数 `p` と段階 `Lset p` の両方を `Lset lam` の中へ置く。添字に関するこの一つの閉性の仮定が、これらすべてを支えている。
<!--/-->

```agda

      p∈λ : ⟨ p ∈ˢ lam ⟩
      p∈λ = succλ c c∈λ

```

<!--en-->
The prepared index must also be ordinal. Because `lam` is ordinal and `c ∈ lam`, `mem-ord` gives `IsOrd c`; closure of ordinals under von Neumann successor then gives `IsOrd (sucV c)`, hence `IsOrd p`. This proof keeps two uses of successor distinct: `succλ` places the successor inside the outer index, while `suc-ord` proves that the successor is itself an ordinal.
<!--zh-->
预备的索引还必须是序数。由于 `lam` 是序数且 `c ∈ lam`，`mem-ord` 给出 `IsOrd c`；序数对 von Neumann 后继的闭合再给出 `IsOrd (sucV c)`，也就是 `IsOrd p`。这里区分了后继的两种用途：`succλ` 把后继放入外围索引，`suc-ord` 则证明该后继本身是序数。
<!--ja-->
準備した添字は順序数でもなければならない。`lam` は順序数で `c ∈ lam` なので、`mem-ord` から `IsOrd c` が得られ、フォン・ノイマン後続についての順序数の閉性から `IsOrd (sucV c)`、すなわち `IsOrd p` が従う。ここでは後続の二つの役割を区別している。`succλ` は後続を外側の添字に入れ、`suc-ord` はその後続自体が順序数であることを示す。
<!--/-->

```agda
      op : IsOrd p
      op = suc-ord (mem-ord {A = lam} ordλ c c∈λ)

```

<!--en-->
The birth-stage information says `y ∈ 𝒟ₒ (Lset c)`. The successor-stage equation identifies this definable-power-set stage with `Lset (sucV c)`, so transport gives `y ∈ Lset p`. This is the reason for passing from `c` to its successor: the decomposition locates `y` as a definable subset over the stage at `c`, while `findP` needs ordinary membership in a constructible stage.
<!--zh-->
诞生层信息给出 `y ∈ 𝒟ₒ (Lset c)`。后继层等式把这个可定义幂集层认同为 `Lset (sucV c)`，因此传输得到 `y ∈ Lset p`。这正是从 `c` 转到其后继的原因：分解把 `y` 定位为 `c` 处之层上的可定义子集，而 `findP` 需要的是对某个可构造层的普通成员关系。
<!--ja-->
誕生段階の情報は `y ∈ 𝒟ₒ (Lset c)` を与える。後続段階の等式は、この定義可能冪集合の段階を `Lset (sucV c)` と同一視するので、輸送によって `y ∈ Lset p` が得られる。これが `c` からその後続へ進む理由である。分解によって `y` は `c` の段階上の定義可能部分集合として位置づけられるが、`findP` が必要とするのは構成可能段階への通常の所属である。
<!--/-->

```agda
      y∈Lp : ⟨ y ∈ˢ Lset p ⟩
      y∈Lp = subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc c)) y∈D

```

<!--en-->
Opening the superadequacy witness locally gives an index `γ ∈ lam` with `p ∈ γ` and `Adequate γ`. These are precisely the hypotheses needed for completeness at the externally prepared index `p`. The pair `yM = (y,y∈M)` now regards `y` as an element of the hull's carrier, so it can occur as the constant parameter of `findP`. From this point onward the construction uses the query that fixes membership of `y`, rather than the earlier query that fixed a prescribed index.
<!--zh-->
在局部打开超充分性见证，得到索引 `γ ∈ lam`、关系 `p ∈ γ` 与性质 `Adequate γ`。这些正是对外围预备索引 `p` 使用完备性所需的前提。二元组 `yM = (y,y∈M)` 此时把 `y` 视为壳载体的元素，使其能作为常元参数出现在 `findP` 中。从这里起，构造使用的是固定 `y` 之成员关系的查询，而不是前面固定指定索引的查询。
<!--ja-->
強化された十分さの証人を局所的に開くと、添字 `γ ∈ lam`、関係 `p ∈ γ`、性質 `Adequate γ` が得られる。これらは、外側で準備した添字 `p` に完全性を適用するために必要な仮定そのものである。組 `yM = (y,y∈M)` はここで `y` を包の台の要素とみなし、`findP` の定数パラメータとして使えるようにする。ここからの構成では、先のように指定された添字を固定する問い合わせではなく、`y` の所属を固定する問い合わせを使う。
<!--/-->

```agda
      go₂ : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ p ∈ˢ γ ⟩ × Adequate γ) → Goal
      go₂ (γ , γ∈λ , p∈γ , adγ) = rec₁ squash₁ takeZ hullSat
        where
        yM : A.SM
        yM = y , y∈M
```

<!--en-->
Completeness at the adequate `γ` constructs an ambient answer to `findP` using the triple `(Lset p,p,Lset γ)`, and the previously proved membership places `y` in its first coordinate. The three required carrier memberships are supplied by `ord∈Lλ p`, `Lset∈Lλ p`, and `Lset∈Lλ γ`. Since `findP` contains unbounded existential quantifiers, the passage of this whole answer into the hull uses full elementarity. The result is an internal existential assertion that `yM` belongs to some correctly described stage.
<!--zh-->
在充分索引 `γ` 处，完备性以三元组 `(Lset p,p,Lset γ)` 构造 `findP` 的外围回答，而前一步所得的成员关系把 `y` 放入其第一坐标。所需的三项载体成员资格分别由 `ord∈Lλ p`、`Lset∈Lλ p` 与 `Lset∈Lλ γ` 给出。由于 `findP` 含有无界存在量词，把整个回答送入 Skolem 壳必须使用完整初等性。所得结论是一条内部存在断言：`yM` 属于某个被正确描述的层。
<!--ja-->
十分な添字 `γ` における完全性は、三つ組 `(Lset p,p,Lset γ)` を使って `findP` の周囲での答えを作り、先に得た所属が `y` をその第一座標に入れる。必要な三つの台への所属は、`ord∈Lλ p`、`Lset∈Lλ p`、`Lset∈Lλ γ` がそれぞれ与える。`findP` は非有界な存在量化を含むので、この答え全体を Skolem 包へ移すには完全な初等性を使う。その結果、`yM` が正しく記述されたある段階に属するという、包内部の存在主張が得られる。
<!--/-->

```agda

        hullSat : ⟨ [] Mse.⊨ findP yM ⟩
        hullSat = subst ⟨_⟩ (sym (elem 0 (findP yM) []))
          (stageP y p γ op adγ p∈γ yM refl y∈Lp
            (ord∈Lλ p op p∈λ) (Lset∈Lλ p p∈λ) (Lset∈Lλ γ γ∈λ))

```

<!--en-->
Opening the internal assertion locally gives three hull elements `u`, `a`, and `z`. Their underlying sets satisfy `levelFo(fst u,fst a,fst z)`, and the same answer records `y ∈ fst u`. From these facts one must obtain an ordinal in the collapse image whose level contains `π y`. The construction may form an explicit dependent sum for each local answer, but that sum is immediately returned beneath propositional truncation, so no covering index escapes as chosen data.
<!--zh-->
在局部打开内部断言，得到三个 Skolem 壳元素 `u`、`a`、`z`。它们的底层集合满足 `levelFo(fst u,fst a,fst z)`，同一回答还记录 `y ∈ fst u`。现在要由这些事实取得塌缩像中的一个序数，使其所索引的层包含 `π y`。构造可以为每份局部回答形成显式依值和，但这份依值和立即被送回命题截断之下，所以覆盖索引不会作为选定数据逸出。
<!--ja-->
内部の主張を局所的に開くと、Skolem 包の三つの要素 `u`、`a`、`z` が得られる。それらの基礎集合は `levelFo(fst u,fst a,fst z)` を満たし、同じ答えは `y ∈ fst u` も記録している。ここから、崩壊像に属し、その段階が `π y` を含む順序数を得なければならない。局所的な各答えから明示的な依存和を作れるが、その和はただちに命題的切り詰めのもとへ戻されるので、被覆の添字が選択済みのデータとして外へ出ることはない。
<!--/-->

```agda
        finishP : (z a : A.SM)
                → Σ[ u ∈ A.SM ]
                    ( ⟨ (u ∷ a ∷ z ∷ []) Mse.⊨ embed levelFo ⟩
                    × ⟨ y ∈ˢ fst u ⟩ )
                → Σ[ β ∈ S ] (IsOrd β × ⟨ β ∈ˢ HS.C.πX ⟩
```

<!--en-->
The output witness is chosen locally as `β = π p′`, where `p′` is the underlying set of the middle hull coordinate `a`. Once `p′` is shown ordinal, `ord-push` proves that `π p′` is ordinal, and `πX-intro` places it in the collapse image because `a` certifies `p′ ∈ M`. The remaining component is `π y ∈ Lset (π p′)`. Establishing it requires first reading the formula answer in the ambient hierarchy and then relating membership to the local compatibility equation.
<!--zh-->
输出见证在局部取为 `β = π p′`，其中 `p′` 是中间壳坐标 `a` 的底层集合。一旦证明 `p′` 为序数，`ord-push` 就证明 `π p′` 为序数，而 `a` 所带的证明给出 `p′ ∈ M`，故 `πX-intro` 把 `π p′` 放入塌缩像。余下的分量是 `π y ∈ Lset (π p′)`。要得到它，必须先在外围层级中读取公式回答，再把成员关系与局部相容等式结合起来。
<!--ja-->
出力の証人は、局所的に `β = π p′` とする。ここで `p′` は、包の中央の座標 `a` の基礎にある集合である。`p′` が順序数だと分かれば、`ord-push` により `π p′` も順序数となり、`a` が持つ `p′ ∈ M` の証明から、`πX-intro` によって `π p′` が崩壊像に入る。残る成分は `π y ∈ Lset (π p′)` である。これを得るには、まず論理式への答えを周囲の階層で読み、その後で所属を局所的な整合性の等式と結びつける。
<!--/-->

```agda
                              × ⟨ π y ∈ˢ Lset β ⟩)
        finishP z a (u , sat , y∈u) =
          π p′ , ord-push p′ (snd a) op′ , HS.C.πX-intro p′ (snd a) , πy∈
          where
          amb : ⟨ (fst u ∷ fst a ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
```

<!--en-->
The internal satisfaction proof concerns `embed levelFo` in the hull structure. Because its core `levelFo` is Δ₀, `Cy.atM` reads that proof as ambient satisfaction of `levelFo` at the same three underlying sets `(fst u,fst a,fst z)`. No coordinate is collapsed in this step. Its role is to leave the internal semantics of the hull and recover an ambient statement to which `isOrd-at-p-out` and `level-sound` can be applied.
<!--zh-->
内部满足关系证明讨论的是壳结构中的 `embed levelFo`。由于其核心 `levelFo` 是 Δ₀ 公式，`Cy.atM` 把这项证明读成 `levelFo` 在同三个底层集合 `(fst u,fst a,fst z)` 处的外围满足关系。此步没有塌缩任何坐标；它的作用是离开 Skolem 壳的内部语义，恢复一条可供 `isOrd-at-p-out` 与 `level-sound` 使用的外围陈述。
<!--ja-->
内部の充足の証明が扱うのは、包の構造における `embed levelFo` である。その核 `levelFo` は Δ₀ 論理式なので、`Cy.atM` はこの証明を、同じ三つの基礎集合 `(fst u,fst a,fst z)` における `levelFo` の周囲での充足として読む。この段階では、どの座標も崩壊されない。その役割は、Skolem 包の内部意味論を離れ、`isOrd-at-p-out` と `level-sound` を適用できる周囲での主張を取り戻すことである。
<!--/-->

```agda
          amb = subst ⟨_⟩ (Cy.atM Δ₀-levelFo (u ∷ a ∷ z ∷ [])) sat

```

<!--en-->
Let `p′ = fst a` be the middle coordinate returned inside the hull. It need not equal the externally prepared successor `p = sucV c`. The external triple established that `findP yM` was satisfiable, but `findP` fixes only the membership of `yM` in its first coordinate; it contains no equation fixing the middle coordinate. Full elementarity therefore supplies merely some internal index `p′` under propositional truncation, and the remainder of the proof uses this returned index.
<!--zh-->
令 `p′ = fst a` 为 Skolem 壳内部返回的中间坐标。它不必等于外围预备的后继 `p = sucV c`。外围三元组证明 `findP yM` 可满足，但 `findP` 只固定 `yM` 对第一坐标的成员关系，其中没有固定中间坐标的等式。因此，完整初等性只在命题截断下给出某个内部索引 `p′`，余下证明使用的是这个返回的索引。
<!--ja-->
Skolem 包の内部で返された中央の座標を `p′ = fst a` とする。これは、周囲で準備した後続 `p = sucV c` と等しい必要がない。周囲の三つ組は `findP yM` が充足可能であることを示したが、`findP` が固定するのは `yM` の第一座標への所属だけであり、中央の座標を固定する等式は含まない。したがって完全な初等性が命題的切り詰めのもとで与えるのは、ある内部添字 `p′` にすぎず、残りの証明はこの返された添字を使う。
<!--/-->

```agda
          p′ : S
          p′ = fst a

```

<!--en-->
The returned index is nevertheless known to be ordinal. The ambient satisfaction `amb` contains, as the first conjunct of `levelFo`, the three-slot ordinal description at its middle coordinate. Applying the reading lemma `isOrd-at-p-out` to that conjunct gives `IsOrd p′`. This conclusion concerns the internal preimage index `p′`; the ordinal used in `Goal` is its collapse `π p′`, whose ordinality is obtained separately by `ord-push`.
<!--zh-->
不过，仍可证明返回的索引是序数。外围满足关系 `amb` 的第一个合取支，是在中间坐标处读取的三槽序数描述。把读式引理 `isOrd-at-p-out` 施于该合取支，便得到 `IsOrd p′`。这一结论讨论的是内部原像索引 `p′`；`Goal` 中使用的序数是它的塌缩 `π p′`，后者的序数性另由 `ord-push` 得到。
<!--ja-->
ただし、返された添字が順序数であることは分かる。周囲での充足 `amb` の第一の連言支は、中央の座標について読む三つの枠を持つ順序数の記述である。その連言支に読みの補題 `isOrd-at-p-out` を適用すると、`IsOrd p′` が得られる。この結論が述べるのは内部の原像の添字 `p′` である。`Goal` で使う順序数はその崩壊 `π p′` であり、こちらの順序数性は別に `ord-push` から得る。
<!--/-->

```agda
          op′ : IsOrd p′
          op′ = isOrd-at-p-out (fst u) p′ (fst z) (amb .fst)

```

<!--en-->
Soundness now identifies the first coordinate of the internal answer. Since `u`, `a`, and `z` are hull elements, `Hull⊆L` places their underlying sets in `Lset lam`, and `isLλ` proves each one constructible. Together with `amb`, these three premises give `fst u ≡ Lset p′`. Thus the recorded fact `y ∈ fst u` can be transported to `y ∈ Lset p′`. The auxiliary bound `fst z` need not be unique, and no equality between `p′` and the prepared `p` is used; soundness determines the stage value solely from the returned ordinal index.
<!--zh-->
现在由可靠性识别内部回答的第一坐标。由于 `u`、`a`、`z` 都是 Skolem 壳元素，`Hull⊆L` 把它们的底层集合放入 `Lset lam`，`isLλ` 再分别证明三者可构造。结合 `amb`，这三个前提给出 `fst u ≡ Lset p′`。因此，回答中记录的 `y ∈ fst u` 可以传输为 `y ∈ Lset p′`。辅助界 `fst z` 不必唯一，证明也没有使用 `p′` 与预备索引 `p` 之间的等式；可靠性只凭返回的序数索引确定层的取值。
<!--ja-->
ここで健全性により、内部の答えの第一座標を特定する。`u`、`a`、`z` はいずれも Skolem 包の要素なので、`Hull⊆L` はそれらの基礎にある集合を `Lset lam` に入れ、`isLλ` がそれぞれの構成可能性を証明する。これら三つの前提を `amb` と合わせると、`fst u ≡ Lset p′` が得られる。したがって、答えに記録された `y ∈ fst u` を `y ∈ Lset p′` へ輸送できる。補助的な上界 `fst z` は一意である必要がなく、`p′` と準備した `p` の間の等式も使わない。健全性は、返された順序数の添字だけから段階の値を定める。
<!--/-->

```agda
          u≡ : fst u ≡ Lset p′
          u≡ = level-sound (fst u) p′ (fst z)
                 (isLλ (fst u) (Hull⊆L (fst u) (snd u)))
                 (isLλ p′ (Hull⊆L p′ (snd a)))
                 (isLλ (fst z) (Hull⊆L (fst z) (snd z))) amb
```

<!--en-->
The returned level value `fst u` is identified with `Lset p′` by `u≡`. Transporting the recorded membership `y∈u` along this equality therefore gives `y ∈ Lset p′`. This step uses only substitution in the set being joined; it does not impose any relation between the returned index `p′` and the previously prepared index `p`.
<!--zh-->
可靠性等式 `u≡` 把返回的层值 `fst u` 认同为 `Lset p′`。沿这条等式搬运已取得的成员关系 `y∈u`，便得到 `y ∈ Lset p′`。这里仅替换成员关系右侧的集合，并未在返回指标 `p′` 与先前预备的指标 `p` 之间建立任何关系。
<!--ja-->
健全性から得た等式 `u≡` は、返された段階の値 `fst u` を `Lset p′` と同一視する。この等式に沿って、すでに得られた所属 `y∈u` を移せば、`y ∈ Lset p′` が従う。ここで行うのは所属の右辺にある集合の置換だけであり、返された添字 `p′` と先に用意した添字 `p` の間には何の関係も課していない。
<!--/-->

```agda

          y∈Lp′ : ⟨ y ∈ˢ Lset p′ ⟩
          y∈Lp′ = subst (λ v → ⟨ y ∈ˢ v ⟩) u≡ y∈u

```

<!--en-->
The returned middle coordinate supplies exactly the data needed by the local commutation theorem. Its underlying set is `p′`; `op′` proves that this set is an ordinal, and `snd a` proves that it belongs to the hull. Hence `commute p′ op′ (snd a)` yields both `Lset p′ ∈ M` and the equation `π (Lset p′) ≡ Lset (π p′)`. The theorem is local to ordinals in the hull, which is precisely the situation established here.
<!--zh-->
返回的中间坐标恰好给出局部交换定理所需的数据。它的底层集合是 `p′`，`op′` 证明该集合是序数，`snd a` 证明它属于壳。因此，`commute p′ op′ (snd a)` 同时给出 `Lset p′ ∈ M` 与等式 `π (Lset p′) ≡ Lset (π p′)`。该定理只针对壳中的序数，而这里已经满足这一适用条件。
<!--ja-->
返された中央の座標は、局所的な交換定理に必要なデータをちょうど与える。その基礎集合が `p′` であり、`op′` はそれが順序数であることを、`snd a` はそれが包に属することを示す。したがって `commute p′ op′ (snd a)` から、`Lset p′ ∈ M` と等式 `π (Lset p′) ≡ Lset (π p′)` の両方が得られる。この定理は包の中の順序数に対する局所的な主張であり、ここではその条件が満たされている。
<!--/-->

```agda
          cm : ⟨ Lset p′ ∈ˢ M ⟩ × (π (Lset p′) ≡ Lset (π p′))
          cm = commute p′ op′ (snd a)

```

<!--en-->
Both endpoints of `y∈Lp′` are hull members: `y∈M` gives the first, while `cm .fst` gives the second for `Lset p′`. The collapse therefore preserves this membership, producing `π y ∈ π (Lset p′)` through `member-push`. Substitution along `cm .snd` then changes the containing set to `Lset (π p′)`. Together with the preceding ordinal and image-membership proofs for `π p′`, this is the covering witness required by `finishP`.
<!--zh-->
关系 `y∈Lp′` 的两端都是壳成员：`y∈M` 给出 `y` 的壳成员资格，`cm .fst` 给出 `Lset p′` 的壳成员资格。于是 `member-push` 保持这条成员关系，得到 `π y ∈ π (Lset p′)`；再沿 `cm .snd` 替换右侧集合，便得到 `π y ∈ Lset (π p′)`。结合前面关于 `π p′` 的序数性与像中成员资格，这正是 `finishP` 所需的覆盖见证。
<!--ja-->
`y∈Lp′` の両端は包の要素である。`y` については `y∈M` が、`Lset p′` については `cm .fst` がその所属を与える。そこで `member-push` によりこの所属を崩壊の後へ移し、`π y ∈ π (Lset p′)` を得る。さらに `cm .snd` に沿って右辺の集合を置換すると、`π y ∈ Lset (π p′)` となる。先に示した `π p′` の順序数性と像への所属と合わせれば、これは `finishP` が求める覆いの証人である。
<!--/-->

```agda
          πy∈ : ⟨ π y ∈ˢ Lset (π p′) ⟩
          πy∈ = subst (λ w → ⟨ π y ∈ˢ w ⟩) (cm .snd)
                  (Cy.member-push (Lset p′) y (cm .fst) y∈M y∈Lp′)

```

<!--en-->
For fixed `z` and `a`, the last existential states merely that a suitable `u` exists. Every explicit answer determines the ordinal `π p′`, its membership in the collapse image, and the proof `π y ∈ Lset (π p′)` constructed above. Mapping this construction under propositional truncation preserves the existence of a covering ordinal without selecting a particular answer to the query.
<!--zh-->
固定 `z` 与 `a` 后，最后一个存在量词只断言某个合适的 `u` 仅仅存在。每份显式回答都确定上面构造出的序数 `π p′`、它对塌缩像的成员资格，以及证明 `π y ∈ Lset (π p′)`。在命题截断内部作这项映射，便保留覆盖序数的存在性，而不选定查询的某份特定回答。
<!--ja-->
`z` と `a` を固定すると、最後の存在量化子は適切な `u` が単に存在することだけを述べる。明示的な各答えから、上で構成した順序数 `π p′`、その崩壊像への所属、および `π y ∈ Lset (π p′)` の証明が定まる。この構成を命題的切り詰めの内部で写すことにより、問い合わせへの特定の答えを選ぶことなく、被覆する順序数の存在を保てる。
<!--/-->

```agda
        takeA : (z : A.SM)
              → Σ[ a ∈ A.SM ]
                  ⟨ (a ∷ z ∷ []) Mse.⊨ ∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero)) ⟩
              → Goal
        takeA z (a , ha) = map₁ (finishP z a) ha
```

<!--en-->
The two remaining existential layers obey the same restriction. After `z` is fixed, the middle witness `a` may be used because the destination `Goal` is a proposition; the enclosing elimination treats `z` in the same way. All three coordinates of the internal answer are therefore available only locally. The result proves a covering ordinal exists for each hull member, without producing a choice function of such ordinals.
<!--zh-->
余下两层存在量词服从同一限制。固定 `z` 后，可以使用中间见证 `a`，因为目标 `Goal` 是命题；外层消去以同样方式处理 `z`。因此，内部回答的三个坐标都只能在局部使用。所得结论证明每个 Skolem 壳成员都有覆盖序数，却不产生选择这类序数的函数。
<!--ja-->
残る二つの存在の層も同じ制限に従う。`z` を固定した後、行き先 `Goal` が命題なので中央の証人 `a` を使える。外側の除去も同様に `z` を扱う。したがって内部の答えの三つの座標は、すべて局所的にだけ利用できる。結果は各 Skolem 包の要素に被覆する順序数が存在することを示すが、そのような順序数を選ぶ関数は作らない。
<!--/-->

```agda

        takeZ : Σ[ z ∈ A.SM ]
                  ⟨ (z ∷ []) Mse.⊨ ∃̇ (∃̇ (embed levelFo ∧̇ (con yM ∈̇ var zero))) ⟩
              → Goal
        takeZ (z , hz) = rec₁ squash₁ (takeA z) hz
```

<!--en-->
The two established properties now determine the collapse image. Let `β` be the set of its ordinal members. Transitivity of the image, together with the fact that members of ordinals are ordinal, makes `β` an ordinal. If `x ∈ πX`, covering places `x` in some `Lset γ` with the ordinal `γ ∈ πX`; hence `γ ∈ β`, and monotonicity gives `x ∈ Lset β`. Conversely, decompose `x ∈ Lset β` at some `δ ∈ β`. Applying covering to the image member `δ` yields an ordinal `γ ∈ β` with `δ ∈ γ`. Then `x ∈ Lset γ`, while `levelIn` places `Lset γ` in the transitive image, so `x ∈ πX`. Extensionality gives `πX ≡ Lset β`.
<!--zh-->
已经证明的两项性质现在确定塌缩像。令 `β` 为该像的序数成员所成的集合。像的传递性，加上序数成员的成员仍为序数这一事实，使 `β` 成为序数。若 `x ∈ πX`，覆盖性质把 `x` 放入某个 `Lset γ`，其中序数 `γ ∈ πX`；于是 `γ ∈ β`，单调性给出 `x ∈ Lset β`。反过来，把 `x ∈ Lset β` 分解到某个 `δ ∈ β` 处。对像中成员 `δ` 使用覆盖性质，得到序数 `γ ∈ β` 且 `δ ∈ γ`。于是 `x ∈ Lset γ`，而 `levelIn` 把 `Lset γ` 放进传递的塌缩像，故 `x ∈ πX`。外延性最终给出 `πX ≡ Lset β`。
<!--ja-->
ここまでで示した二つの性質が、崩壊像を決定する。その順序数要素全体の集合を `β` とする。像の推移性と、順序数の要素も順序数であることから、`β` は順序数である。`x ∈ πX` なら、被覆によって、順序数 `γ ∈ πX` を添字とするある `Lset γ` に `x` が属する。したがって `γ ∈ β` であり、単調性から `x ∈ Lset β` が従う。逆に `x ∈ Lset β` をある `δ ∈ β` のところで分解する。像の要素 `δ` に被覆を適用すると、`δ ∈ γ` を満たす順序数 `γ ∈ β` が得られる。すると `x ∈ Lset γ` であり、`levelIn` は `Lset γ` を推移的な崩壊像に入れるので、`x ∈ πX` である。外延性から `πX ≡ Lset β` が得られる。
<!--/-->

```agda
  module Cn = HS.Condense levelIn cover using (condenses)

```

<!--en-->
Thus there is an explicit set `β` with `IsOrd β` and `HS.C.πX ≡ Lset β`. The witness is not propositionally truncated: it is the set of ordinal members of the collapse image. This conclusion uses all the structural hypotheses of `Condense`, while its only classical parameter is `LEM (ℓ-suc ℓ)`. It makes no comparison between `β` and the outer index `lam`, and gives no cardinal estimate or injection; those require the additional constructions of later chapters.
<!--zh-->
于是得到显式集合 `β`，并有 `IsOrd β` 与 `HS.C.πX ≡ Lset β`。这个见证不在命题截断之下，因为它就是塌缩像的所有序数成员所成的集合。该结论使用 `Condense` 的全部结构性假设，而其唯一的经典参数是 `LEM (ℓ-suc ℓ)`。它不比较 `β` 与外层索引 `lam`，也不给出基数估计或单射；这些结论还需要后续章节中的附加构造。
<!--ja-->
こうして、`IsOrd β` と `HS.C.πX ≡ Lset β` を満たす明示的な集合 `β` が得られる。この証人は命題的切り詰めの中にはない。崩壊像の順序数要素全体からなる集合そのものだからである。この結論は `Condense` の構造的な仮定をすべて使い、その古典的なパラメータは `LEM (ℓ-suc ℓ)` だけである。`β` と外側の添字 `lam` の比較、基数評価、単射は与えない。それらには後の章で導入する追加の構成が必要である。
<!--/-->

```agda
  condenses : Σ[ β ∈ S ] (IsOrd β × (HS.C.πX ≡ Lset β))
  condenses = Cn.condenses
```
