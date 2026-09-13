<!--en-->
# Locating ordinals in the constructible hierarchy

An ordinal's position in the constructible hierarchy is controlled by membership: it appears by its successor stage and cannot appear before its own rank. This chapter proves both directions and gives a bounded formula for recognizing ordinals inside a stage.

One question about the tower is still open, and it is the one the axiom of infinity turns on: given a stage, exactly which ordinals have appeared by then? The answer is as clean as it could be. The ordinals in `Lset α` are precisely the members of `α`, so the tower's index and its ordinal content agree, level for level, and an ordinal first appears at the stage after itself.

Both directions require real work. One direction says an ordinal cannot appear early: if it is in `Lset α` then it is a member of `α`. That is the harder one, and it goes through rank, which is why the rank construction is needed here. A set in `Lset α` is a definable subset of some earlier stage, its members therefore have rank below that stage by induction, and so its own rank is bounded; being an ordinal, it is its own rank.

The other direction says an ordinal cannot appear late: every member of `α` is already in `Lset α`. That one is a straight induction, given that an ordinal appears at the stage after itself, which is the theorem being proved. The circularity is only apparent: the induction hypothesis supplies the statement for the members, and the members are the only thing needed.

With both halves the ordinals of a stage are carved out of it by a single formula, "is an ordinal", which is Δ₀ because transitivity can be said with bounded quantifiers alone. So `α` is a definable subset of `Lset α`, and the definable-power-set clause for the successor stage then applies.
<!--zh-->
# 在可构造层级中定位序数

序数在可构造层级中的位置由隶属关系控制：它会在自身的后继层出现，却不会早于自身的秩出现。本章证明两个方向，并给出在层内部识别序数的有界公式。

关于塔还有一个问题悬而未决，而无穷公理正系于此：给定一层，到那时为止究竟出现了哪些序数？答案十分简洁。`Lset α` 中的序数恰是 `α` 的成员，故塔的索引与它的序数内容逐层一致，而序数首次现身于自身之后的那一层。

两个方向都有实质难度。一个方向说序数不会提前现身：若它在 `Lset α` 中，则它是 `α` 的成员。这是较难的一半，要经过秩，而这正是这里需要秩构造的原因。`Lset α` 中的集合是某个更早层的可定义子集，依归纳其成员的秩低于那一层，故它自身的秩有界；而作为序数，它就是自身的秩。

另一个方向说明序数不会延迟出现：`α` 的每个成员都已经在 `Lset α` 中。这一半由直接归纳证明，所用陈述正是序数会在自身之后的层出现。这里没有循环：归纳假设为各个成员提供该陈述，而证明所需的也只有这些成员。

两半齐备，一层中的序数便由单一公式「是序数」从中选出，该公式是 Δ₀ 的，因为传递性只用有界量词就能表述。于是 `α` 是 `Lset α` 的可定义子集，后继层的可定义幂集子句随即可以应用。
<!--ja-->
# 構成可能階層の中で順序数を位置付ける

順序数が構成可能階層に現れる位置は所属によって制御されます。順序数は自身の後者段階までに現れ、自身の階数より前には現れない。本章では両方向を示し、段階の内部で順序数を認識する有界論理式を与えます。

塔について残された問い、そして無限公理が掛かっている問いはこうです。段階を一つ与えたとき、その時点までにどの順序数が現れているのか。答えはこれ以上なく簡潔です。`Lset α` に属する順序数はまさに `α` の要素であり、したがって塔の添字とその順序数的内容は一つ一つの段階で一致し、順序数は自身の直後の段階に初めて現れます。

両方向に実質的な仕事があります。一方は、順序数が早く現れないことを述べます。すなわち `Lset α` に属するなら `α` の要素である。こちらが難しい方向で、階数を経由します。ここで階数の構成が必要になる理由です。`Lset α` の集合はより早い段階のある `Lset β` の定義可能部分集合であり、帰納法によりその要素の階数は `β` 未満に抑えられるので、その集合自身の階数も有界です。順序数は自身の階数と一致するからです。

もう一方は、順序数が遅く現れないことを述べます。すなわち `α` の各要素はすでに `Lset α` に属する。これは、順序数が自身の直後の段階に現れるという証明すべき主張そのものを前提にすれば、直ちに帰納法で従います。循環は見かけだけです。帰納仮説は要素に対してこの主張を与え、必要なのはその要素だけです。

両者の揃うところ、段階の順序数は単一の論理式「順序数であること」で切り出せます。この式は Δ₀ です。推移性は有界量化だけで表せるからです。よって `α` は `Lset α` の定義可能部分集合であり、後者段階を与える定義可能冪集合の節を直ちに適用できます。
<!--/-->

<!--en-->
The chapter works inside a fixed universe level ℓ, and everything that follows speaks about sets, membership, and stages of L at that level. We assume excluded middle at level ℓ-suc ℓ. Its sole mathematical use is ordinal trichotomy: for two ordinals, one of membership in either direction or equality is returned. Every later conclusion inherits this classicality through the two comparison lemmas built in the next section.
<!--zh-->
本章在一个固定的宇宙层级 ℓ 内工作，以下关于集合、隶属与 L 的层的全部论述都在这一层级上。我们假设层级 ℓ-suc ℓ 上的排中律。它在数学上的唯一用途是序数三歧：对两个序数，返回两个方向的隶属关系之一或相等这一情形。后文的所有结论都经下一节建立的两次比较引理继承这种经典性。
<!--ja-->
本章は固定された宇宙レベル ℓ の内部で働き、集合・所属・L の段階に関するすべての議論はこのレベルで行われます。レベル ℓ-suc ℓ における排中律を仮定します。その数学的な用途は順序数の三分法だけです。二つの順序数に対し、いずれかの向きの所属または等号という場合を一つ返します。以降の結論はすべて、次節で組み立てる二つの比較補題を通じてこの古典性を受け継ぎます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Ordinal.Stages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
Two kinds of vocabulary meet here. From the ambient hierarchy V come the basic moves: membership ∈ˢ on the set S, the von Neumann successor `sucV`, induction and irreflexivity along membership. From the constructible side come the stages `Lset α` themselves, the definable-subset layer `𝒟ₒ`, and the two directions `Lset-in` and `Lset-out` relating membership in a stage to membership in its definable power set. The chapter's statement lives entirely in this intersection: it asks where an ordinal sits among the `Lset α`.
<!--zh-->
这里交汇了两类词汇。来自环境层级 V 的是基本动作：集合 S 上的隶属 ∈ˢ、冯·诺伊曼后继 `sucV`、沿隶属的归纳法与隶属的非自反性。来自可构造一侧的是层 `Lset α` 本身、可定义子集层 `𝒟ₒ`，以及把某层中的隶属与它的可定义幂集中的隶属联系起来的两个方向 `Lset-in` 与 `Lset-out`。本章的陈述完全落在这个交集里：它问的是序数在各个 `Lset α` 之间的位置。
<!--ja-->
ここで二種類の語彙が出会います。周囲の階層 V からは基本の操作が来ます。集合 S 上の所属 ∈ˢ、フォン・ノイマンの後者 `sucV`、所属に沿った帰納法と所属の非反射性です。構成可能な側からは、段階 `Lset α` 自身、定義可能部分集合の層 `𝒟ₒ`、そして段階への所属とその定義可能冪集合への所属を結ぶ二方向 `Lset-in` と `Lset-out` が来ます。本章の主張は完全にこの交わりの中にあります。すなわち、順序数が `Lset α` の間のどこに位置するかを問うのです。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-irrefl )
```

<!--en-->
Ordinals enter as the predicate `IsOrd`: a set is an ordinal exactly when it is transitive and all of its members are transitive. This is the von Neumann reading, where the ordinal α is the set of all smaller ordinals, so asking whether an ordinal has appeared at a stage is literally a membership question. Also from earlier chapters come `mem-ord` and `suc-ord`, the closure facts that a member of an ordinal is an ordinal and that the successor of an ordinal is an ordinal; they keep every stage index in the argument an honest ordinal.
<!--zh-->
序数以谓词 `IsOrd` 进入：一个集合是序数，当且仅当它是传递的且它的每个成员都是传递的。这是冯·诺伊曼式的读法，其中序数 α 就是所有更小序数的集合，因此问序数是否已在某层出现，字面上就是隶属问题。相应的闭包事实是 `mem-ord` 与 `suc-ord`：序数的成员是序数，序数的后继是序数。它们保证论证中的每层指标都是序数。
<!--ja-->
順序数は述語 `IsOrd` として登場します。集合が順序数であるのは、それが伝播的であり、かつそのすべての要素が伝播的であるとき、そのときに限ります。これはフォン・ノイマンの読み方で、順序数 α はより小さい順序数全体の集合なので、順序数がある段階に現れたかを問うことは文字どおり所属の問題です。さらに前の章からは `mem-ord` と `suc-ord` という閉包の事実、すなわち順序数の要素は順序数であり順序数の後者は順序数であることが来ます。これにより議論中の各段階の添字が必ず真の順序数であることが保たれます。
<!--/-->

```agda
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( IsOrd; isTransV; Lset; Lset-layer; layer-trans
        ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; Lset-mono; Lset-in; Lset-out )
```

<!--en-->
The decision procedure behind everything is `ord-tri`: given two ordinals, each certified to be one, it returns which of the three cases holds, a ∈ b, a = b, or b ∈ a. It uses the stated excluded-middle assumption. The comparison returns a sum of three cases; impossible branches land in the empty type. Separately, propositional truncation ∣_∣₁ records that the earlier stage witnessing a stage decomposition merely exists.
<!--zh-->
一切背后的判定程序是 `ord-tri`：给定两个各自被证明为序数的序数，它回答三种情形中的哪一种成立，即 a ∈ b、a = b 或 b ∈ a。它使用上述排中律假设。三歧比较以和类型返回三个情形，不可能的分支落入空类型。另一方面，命题截断 ∣_∣₁ 记录层分解所需的较早层仅仅存在。
<!--ja-->
すべての背後にある判定の手続きが `ord-tri` です。それぞれ順序数であると証明された二つの順序数を与えると、三つの場合のうちどれが成り立つか、すなわち a ∈ b、a = b、b ∈ a のいずれかを答えます。これは上述の排中律の仮定です。三分法は三つの場合を直和として返し、不可能な枝は空型に入ります。一方、命題的切り捨て ∣_∣₁ は、段階の分解を与える先行段階が単に存在することを記録します。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rank {ℓ} using ( rank; rank-upper; rank-ord; rank-fix )

open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
```

<!--en-->
The rank construction supplies three properties. For a set x, `rank x` is an ordinal collecting how deep x sits in the cumulative hierarchy; `rank-ord` certifies it is an ordinal, `rank-fix` identifies the rank of an ordinal with the ordinal itself, and `rank-upper` bounds the rank of a set from bounds on the ranks of its members. These are the facts needed for the harder direction.
<!--zh-->
秩构造提供如下三条性质。对集合 x，`rank x` 是一个序数，刻画 x 在累积层级中所处的深度；`rank-ord` 证明它是序数，`rank-fix` 把序数的秩等同于该序数本身，`rank-upper` 由各成员秩的上界给出该集合秩的上界。这三条正是较难方向所需的事实。
<!--ja-->
階数は、それを構築した章から入ってきます。集合 x に対して `rank x` は、累積階層の中で x がどの深さに位置するかを集めた順序数です。`rank-ord` がそれが順序数であることを証明し、`rank-fix` が順序数の階数をその順序数自身と同一視し、`rank-upper` がその要素の階数の上界からその集合の階数の上界を与えます。この三つの事実こそ、本章の難しい方向が消費するすべてです。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; extensionality; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
```

<!--en-->
To connect ambient membership with formulas over a stage, a set A has a chosen presentation ⟪ A ⟫, and `∈-asFiber` passes from membership in A to an index naming that member. Mutual inclusion gives equality through `extensionality`. Formula satisfaction is interpreted directly in `hProp`: each formula denotes an hProp. These identifications let the argument pass between sets, their indices and bounded formulas.
<!--zh-->
为了把外围隶属与层上的公式联系起来，集合 A 有一个选定的呈现 ⟪ A ⟫，`∈-asFiber` 把 A 中的成员转为指名该成员的指标。互相包含则通过 `extensionality` 给出集合相等。公式的满足解释直接在 `hProp` 中：每个公式表示一个 hProp。这些对应使论证可以在集合、其指标与有界公式之间转换。
<!--ja-->
周囲での所属と段階上の論理式を結ぶために、集合 A には選ばれた提示 ⟪ A ⟫ があり、`∈-asFiber` は A への所属から、その要素を指す添字を与えます。相互包含からは `extensionality` によって集合の等号が得られます。論理式の充足は `hProp` で直接解釈され、各論理式が表す hProp です。これらの対応により、集合、その添字、有界論理式の間を行き来できます。
<!--/-->

```agda
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## Comparison, twice

Trichotomy leaves exactly three mathematical possibilities. If a belongs to b, it belongs to the successor of b; if a = b, then a belongs to that successor as its new top element. The only remaining possibility, b ∈ a, will be ruled out by the inclusion a ⊆ b.
<!--zh-->
## 两次比较

三歧比较只留下三个数学情形。若 a ∈ b，则 a 也属于 b 的后继；若 a = b，则 a 作为新增的顶端元素属于该后继。余下的 b ∈ a 将由包含关系 a ⊆ b 排除。
<!--ja-->
## 二つの比較原理

三分法で残る数学的な場合は三つです。a ∈ b なら a は b の後者にも属し、a = b なら a は新たな最上要素としてその後者に属します。残る b ∈ a は包含 a ⊆ b によって排除されます。
<!--/-->

<!--en-->
Suppose a ⊆ b for sets a and b, and compare them by trichotomy. If a is a member of b, the first helper applies `∈sucV-inl`: a member of b is automatically a member of `sucV b`, since the successor is b together with its singleton. If a equals b, the second helper transports the fact `self∈sucV b`, that b belongs to its own successor, along the path a ≡ b. Two of the three cases are already closed.
<!--zh-->
设集合 a 与 b 满足 a ⊆ b，用三歧性比较二者。若 a 是 b 的成员，第一个辅助件调用 `∈sucV-inl`：b 的成员自动是 `sucV b` 的成员，因为后继是 b 连同它的单点集。若 a 等于 b，第二个辅助件沿路径 a ≡ b 传递事实 `self∈sucV b`，即 b 属于自身的后继。三种情形中两种已经关闭。
<!--ja-->
集合 a と b が a ⊆ b を満たすとし、三分性で両者を比較します。a が b の要素なら、最初の補題は `∈sucV-inl` を適用します。後者は b とその一元集合の合併なので、b の要素は自動的に `sucV b` の要素です。a が b と等しいなら、二番目の補題は、b が自身の後者に属するという事実 `self∈sucV b` をパス a ≡ b に沿って輸送します。三つの場合のうち二つはすでに閉じました。
<!--/-->

```agda
private
  ∈-case : (a b : S) → ⟨ a ∈ˢ b ⟩ → ⟨ a ∈ˢ sucV b ⟩
  ∈-case a b a∈b = ∈sucV-inl a∈b

  ≡-case : (a b : S) → a ≡ b → ⟨ a ∈ˢ sucV b ⟩
  ≡-case a b a≡b = subst (λ w → ⟨ w ∈ˢ sucV b ⟩) (sym a≡b) (self∈sucV b)
```

<!--en-->
The remaining case is b ∈ a, which inclusion rules out: b ∈ a and a ⊆ b would give b ∈ b, contradicting `∈-irrefl`. From this contradiction the desired conclusion a ∈ sucV b follows. Hence for ordinals a and b, inclusion a ⊆ b forces a ∈ sucV b.
<!--zh-->
余下情形是 b ∈ a，而包含关系将它排除：由 b ∈ a 与 a ⊆ b 可得 b ∈ b，这与 `∈-irrefl` 矛盾。由此矛盾可推出目标 a ∈ sucV b。因此，对序数 a 与 b，包含 a ⊆ b 强制 a ∈ sucV b。
<!--ja-->
残る場合は b ∈ a ですが、包含関係がこれを排除します。b ∈ a と a ⊆ b から b ∈ b が得られ、`∈-irrefl` に反するからです。この矛盾から目標 a ∈ sucV b が従います。したがって順序数 a、b について、包含 a ⊆ b は a ∈ sucV b を導きます。
<!--/-->

```agda

  wit-case : (a b : S) → ((y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩)
           → ⟨ b ∈ˢ a ⟩ → ⟨ a ∈ˢ sucV b ⟩
  wit-case a b a⊆b b∈a = Empty.rec (∈-irrefl b (a⊆b b b∈a))

⊆→∈suc : (a b : S) → IsOrd a → IsOrd b
       → ((y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩) → ⟨ a ∈ˢ sucV b ⟩
```

<!--en-->
This is the first use of the classical comparison. Everything done after the trichotomy result is returned is constructive; the second successor comparison below uses the same principle once more.
<!--zh-->
这是第一次使用经典的序数比较。三歧结果返回之后的推理都是构造性的；下面关于后继的第二个比较会再使用同一原理。
<!--ja-->
ここが古典的な順序数比較の最初の使用箇所です。三分法の結果を得た後の推論は構成的であり、下の後者に関する二つ目の比較でも同じ原理を使います。
<!--/-->

```agda
⊆→∈suc a b orda ordb a⊆b = Sum.rec
  (∈-case a b)
  (Sum.rec (≡-case a b) (wit-case a b a⊆b))
  (ord-tri a orda b ordb)
```

<!--en-->
Now suppose β ∈ α. Trichotomy compares sucV β with α, so either the successor still lies inside α, it equals α, or α lies inside sucV β. The type `Out β α` records the first two alternatives; the third will contradict β ∈ α.
<!--zh-->
现在设 β ∈ α。用三歧性比较 sucV β 与 α，结果要么后继仍位于 α 内，要么它等于 α，要么 α 位于 sucV β 内。类型 `Out β α` 记录前两种可能；第三种将与 β ∈ α 矛盾。
<!--ja-->
ここで β ∈ α とします。sucV β と α を三分法で比較すると、後者が α の中にあるか、α と等しいか、または α が sucV β の中にあります。型 `Out β α` は最初の二つを記録し、三つ目は β ∈ α と矛盾します。
<!--/-->

<!--en-->
The impossible case is discharged inside `overshoot`, whose premises are exactly the two facts that cannot hold at once: α belongs to `sucV β` while β belongs to the ordinal α. Unfolding a member of `sucV β` with `∈sucV-elim` gives two subcases: α ∈ β, or α = β. The elimination principle demands that the target be a proposition, and the empty type `⊥*` is one, so both branches may end in a contradiction.
<!--zh-->
不可能的情形在 `overshoot` 内部排除，它的前提恰是两个不能同时成立的事实：α 属于 `sucV β`，而 β 属于序数 α。用 `∈sucV-elim` 展开 `sucV β` 中成员的事实，得到两个子情形：α ∈ β，或 α = β。该消去原则要求目标是命题，而空类型 `⊥*` 正是命题，于是两个分支都可以终止于矛盾。
<!--ja-->
ありえない場合は `overshoot` の内部で排除されます。その前提は同時には成り立たない二つの事実、すなわち α が `sucV β` に属し、しかも β が順序数 α に属するというものです。`∈sucV-elim` で `sucV β` の要素という事実を展開すると、α ∈ β か α = β の二つの場合が出ます。この消去原理は目標が命題であることを要求しますが、空型 `⊥*` はまさに命題なので、どちらの分岐も矛盾で終えることができます。
<!--/-->

```agda
private
  Out : S → S → Type (ℓ-suc ℓ)
  Out β α = ⟨ sucV β ∈ˢ α ⟩ ⊎ (sucV β ≡ α)

  overshoot : (β α : S) → IsOrd α → ⟨ β ∈ˢ α ⟩ → ⟨ α ∈ˢ sucV β ⟩ → Out β α
  overshoot β α ordα β∈α α∈sβ = Empty.rec*
```

<!--en-->
In the first subcase we have the membership chain α ∈ β ∈ α. Transitivity of α, its first component `ordα .fst`, composes the chain to α ∈ α. In the second, α = β transports β ∈ α along the reversed path and again yields α ∈ α. Both contradict `∈-irrefl`, so the impossible third alternative entails the required conclusion `Out β α`.
<!--zh-->
第一个子情形给出隶属链 α ∈ β ∈ α。α 的传递性，即其第一分量 `ordα .fst`，将这条链复合为 α ∈ α。第二个子情形中，α = β 沿反向路径传递 β ∈ α，同样得到 α ∈ α。两者都与 `∈-irrefl` 矛盾，因此这个不可能的第三种情形推出所需结论 `Out β α`。
<!--ja-->
最初の小場合では所属の鎖 α ∈ β ∈ α が得られます。α の推移性、すなわち第一成分 `ordα .fst` はこの鎖を合成して α ∈ α を与えます。次の場合は α = β に沿って β ∈ α を逆向きに輸送し、やはり α ∈ α を得ます。どちらも `∈-irrefl` に反するので、不可能な第三の場合から必要な結論 `Out β α` が従います。
<!--/-->

```agda
    (∈sucV-elim {A = β} {x = α} {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* α∈sβ
      (λ α∈β → lift (∈-irrefl α (ordα .fst α∈β β∈α)))
      (λ α≡β → lift (∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) (sym α≡β) β∈α))))

suc∈or≡ : (β α : S) → IsOrd β → IsOrd α → ⟨ β ∈ˢ α ⟩
        → ⟨ sucV β ∈ˢ α ⟩ ⊎ (sucV β ≡ α)
```

<!--en-->
The lemma proper now runs the trichotomy between `sucV β` and α, both certified ordinals, `sucV β` via `suc-ord`. The first two cases already have the required shape, membership or equality, and are returned directly.
<!--zh-->
引理本身接着在 `sucV β` 与 α 之间运行三歧性，二者都被证明为序数，`sucV β` 经 `suc-ord`。前两种情形已经具有所需形状，隶属或相等，直接返回即可。
<!--ja-->
本命の補題は、`sucV β` と α の間で三分性を回します。両者とも順序数であることが証明されており、`sucV β` は `suc-ord` によるものです。最初の二つの場合はすでに求められる形、所属か相等かを備えているので、そのまま返せます。
<!--/-->

```agda
suc∈or≡ β α ordβ ordα β∈α = go (ord-tri (sucV β) (suc-ord ordβ) α ordα)
  where
  go : (⟨ sucV β ∈ˢ α ⟩ ⊎ ((sucV β ≡ α) ⊎ ⟨ α ∈ˢ sucV β ⟩)) → Out β α
  go (inl s∈α)        = inl s∈α
  go (inr (inl s≡α))  = inr s≡α
```

<!--en-->
The third case, α ∈ sucV β, is precisely the premise of `overshoot`, and feeding it the standing hypothesis β ∈ α closes the analysis. The conclusion `suc∈or≡` is the sharp form of "no overshoot": below α, the successor stages of members of α are never strictly beyond α.
<!--zh-->
第三种情形 α ∈ sucV β 恰是 `overshoot` 的前提，代入已有假设 β ∈ α 即完成分析。结论 `suc∈or≡` 是「不越头」的锐利形式：在 α 之下，α 各成员的后继层从不停留在严格超出 α 的位置。
<!--ja-->
三つ目の場合 α ∈ sucV β はまさに `overshoot` の前提であり、仮定の β ∈ α を渡せば場合分けは閉じます。結論 `suc∈or≡` は「行き過ぎない」ことの鋭い形です。α の下では、α の要素の後者段階が α を厳しく超えることは決してありません。
<!--/-->

```agda
  go (inr (inr α∈sβ)) = overshoot β α ordα β∈α α∈sβ
```

<!--en-->
And the cumulation lemma it is used for: an ordinal that has appeared at its own successor stage has appeared at every later stage, where later means the index is above it.

This is the bridge between the pointwise statement "β appears at sucV β" and the stage-level statement "every member of α is in Lset α". Given β ∈ α, the successor sucV β sits inside α or coincides with it, and either way membership in the smaller stage transports into membership in `Lset α`.
<!--zh-->
而它所服务的累积引理则是：在自身后继层现身过的序数，在此后每层都已现身，其中「此后」指索引在其之上。

这是「β 在 sucV β 现身」这一逐点陈述与「α 的每个成员都在 Lset α 中」这一层陈述之间的桥。给定 β ∈ α，后继 sucV β 或位于 α 内部、或与之重合，无论哪种情形，较小层中的隶属都会转化为 `Lset α` 中的隶属。
<!--ja-->
そしてこれが奉仕する先が累積の補題です。自身の後者段階に現れた順序数は、それより後のすべての段階に現れます。ここで「後」とは、添字がその順序数の上にあることを意味します。

これは「β は sucV β に現れる」という各点ごとの主張と「α の各要素は Lset α に属する」という段階ごとの主張を結ぶ橋です。β ∈ α が与えられると、後者 sucV β は α の内部にあるか α と一致し、いずれの場合もより小さい段階への所属が `Lset α` への所属に運ばれます。
<!--/-->

<!--en-->
The membership branch uses monotonicity of stages: `Lset-mono` says that if γ ∈ δ then `Lset γ` is included in `Lset δ`, so a member of the earlier stage is a member of the later one. Here γ = sucV β and δ = α, exactly the first case of `suc∈or≡`.
<!--zh-->
隶属分支使用层的单调性：`Lset-mono` 说若 γ ∈ δ 则 `Lset γ` 包含于 `Lset δ`，于是较早层的成员是较晚层的成员。此处 γ = sucV β、δ = α，恰是 `suc∈or≡` 的第一种情形。
<!--ja-->
所属の場合は段階の単調性を使います。`Lset-mono` は、γ ∈ δ なら `Lset γ` が `Lset δ` に含まれることを述べるので、より早い段階の要素はより後の段階の要素です。ここでは γ = sucV β、δ = α で、まさに `suc∈or≡` の最初の場合です。
<!--/-->

```agda
private
  cumul-∈ : (β α : S) → ⟨ sucV β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset (sucV β) ⟩
          → ⟨ β ∈ˢ Lset α ⟩
  cumul-∈ β α s∈α = Lset-mono {α = α} {β = sucV β} s∈α {x = β}

  cumul-≡ : (β α : S) → sucV β ≡ α → ⟨ β ∈ˢ Lset (sucV β) ⟩ → ⟨ β ∈ˢ Lset α ⟩
```

<!--en-->
The equality branch is the degenerate one: when sucV β is not strictly below but equal to α, membership in `Lset (sucV β)` is already membership in `Lset α`, and the transport along the path makes this literally so. The statement of `Lset-cumul` takes the two ordinal certificates and the appearance hypothesis, and dispatches on `suc∈or≡`.
<!--zh-->
相等分支是退化情形：当 sucV β 不严格在下而是等于 α 时，`Lset (sucV β)` 中的隶属已经是 `Lset α` 中的隶属，沿该路径的传递把这一点变成字面事实。`Lset-cumul` 的陈述取两个序数证书与现身假设，并按 `suc∈or≡` 分派。
<!--ja-->
相等の場合は退化したものです。sucV β が厳密には下にない、つまり α と等しいときには、`Lset (sucV β)` への所属はすでに `Lset α` への所属であり、パスに沿った輸送がこれを文字どおりのものにします。`Lset-cumul` は二つの順序数の証明と出現の仮定を受け取り、`suc∈or≡` で場合分けをします。
<!--/-->

```agda
  cumul-≡ β α s≡α = subst (λ w → ⟨ β ∈ˢ Lset w ⟩) s≡α

Lset-cumul : (β α : S) → IsOrd β → IsOrd α → ⟨ β ∈ˢ α ⟩
           → ⟨ β ∈ˢ Lset (sucV β) ⟩ → ⟨ β ∈ˢ Lset α ⟩
Lset-cumul β α ordβ ordα β∈α β∈Lsβ =
  Sum.rec (λ s∈α → cumul-∈ β α s∈α β∈Lsβ)
```

<!--en-->
Note the shape of the result: it does not say that β ∈ Lset α for all β ∈ α outright, since that appearance at the successor stage is still a hypothesis. The final theorem will supply that hypothesis by induction, and this lemma is exactly the step that turns it into stage content.
<!--zh-->
注意结果的形状：它并未直接断言对所有 β ∈ α 都有 β ∈ Lset α，因为在后继层的现身仍是假设。最后的定理将用归纳给出该假设，而这条引理恰是把假设转化为层内容的那一步。
<!--ja-->
結果の形に注意してください。これはすべての β ∈ α に対して β ∈ Lset α と無条件に述べているのではありません。後者段階での出現は依然として仮定だからです。最後の定理がその仮定を帰納法で供給し、この補題は仮定を段階の内容へ変えるまさにその一歩です。
<!--/-->

```agda
          (λ s≡α → cumul-≡ β α s≡α β∈Lsβ)
          (suc∈or≡ β α ordβ ordα β∈α)
```

<!--en-->
## Nothing appears before its rank

If a set belongs to `Lset α`, its rank is bounded by `α`. Applied to an ordinal, whose rank agrees with itself, this shows that the ordinal cannot occur at an earlier stage.

The harder half. By induction on the stage index: a set in `Lset α` lies in the definable subsets of `Lset β` for some `β` in `α`, so it is a subset of `Lset β`; each of its members therefore has rank in `β` by the inductive hypothesis; so its own rank, which is the union of the successors of those ranks, is included in `β`; comparison puts it inside the successor of `β`, and that is inside `α`.

One notational point about the induction: membership in a truncated existential is itself truncated, and the induction is stated over the truncated form β ∈ᵗ α rather than over explicit members. The goal, a membership statement, is a proposition, so eliminating that truncation with `PT.rec` is legitimate.
<!--zh-->
## 没有东西早于自身的秩现身

若一个集合属于 `Lset α`，其秩便以 `α` 为界。对于秩等于自身的序数，这说明它不能在更早层出现。

这是较难的一半。沿层索引归纳：`Lset α` 中的集合落在某个 `β ∈ α` 的 `Lset β` 的可定义子集里，故它是 `Lset β` 的子集；于是依归纳假设它的每个成员的秩都在 `β` 中；故它自身的秩，即那些秩的后继之并，包含于 `β`；三歧比较给出它属于 `β` 的后继，从而属于 `α`。

关于归纳的一点记法说明：截断存在式中的成员关系本身也是截断的，归纳按截断形式 β ∈ᵗ α 陈述，而非按显式成员。目标是一个隶属陈述，因而是命题，所以用 `PT.rec` 消去该截断是合法的。
<!--ja-->
## 自身の階数より前に現れるものはない

集合が `Lset α` に属すれば、その階数は `α` で抑えられます。階数が自身と一致する順序数に適用すると、その順序数がより早い段階には現れないことが分かります。

こちらが難しい方向です。段階の添字についての帰納法で示します。`Lset α` の集合は、ある β ∈ α に対する `Lset β` の定義可能部分集合の中にあり、したがって `Lset β` の部分集合です。すると帰納仮説によりその各要素の階数は `β` の中にあります。その集合自身の階数、すなわちそれらの階数の後者の合併は `β` に含まれ、比較により `β` の後者の内部、ひいては `α` の内部に置かれます。

帰納についての記法上の一点を述べると、切り詰められた存在の要素であることはそれ自体切り詰められており、帰納は明示的な要素ではなく切り詰められた形 β ∈ᵗ α の上で述べられます。目標は所属の主張、つまり命題なので、`PT.rec` によるこの切り詰めの消去は正当です。
<!--/-->

<!--en-->
The statement quantifies over all ordinals α at once, and ∈-induction is applied to the whole predicate as a function of α, with the ordinal certificate carried along as an argument. The induction is on membership in α, so the inductive hypothesis at α speaks about members β of α, not about earlier stages by any list order.
<!--zh-->
陈述同时对所有序数 α 量化，∈-induction 施加于作为 α 之函数的整个谓词，序数证书作为参数一路携带。归纳是沿 α 上的隶属进行的，故在 α 处的归纳假设谈论的是 α 的成员 β，而不是按任何次序排列的「更早层」。
<!--ja-->
主張はすべての順序数 α にわたって量化されており、∈-induction は α の関数としての述語全体に適用され、順序数の証明は引数として携行されます。帰納は α への所属に沿って行われるので、α における帰納仮説が語るのは α の要素 β であって、何らかの順序による「より早い段階」ではありません。
<!--/-->

```agda
rank-Lset : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩
rank-Lset = ∈-induction
  {P = λ α → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩} step
  where
  step : (α : S)
```

<!--en-->
The key step exposes what x ∈ Lset α means: by `Lset-out`, x merely belongs to a definable-subset layer over some β ∈ α. The layer membership is again truncated, but the conclusion rank x ∈ α is a proposition, so `PT.rec` may eliminate the truncation and work with the fiber β, β∈α, x∈𝒟ₒLβ as if it were given.
<!--zh-->
关键一步揭示 x ∈ Lset α 的含义：由 `Lset-out`，x 仅仅 (merely) 属于某个 β ∈ α 之上的可定义子集层。层中的成员关系同样是截断的，但结论 rank x ∈ α 是命题，故 `PT.rec` 可以消去截断，并把纤维 β、β∈α、x∈𝒟ₒLβ 当作已经给出而加以使用。
<!--ja-->
鍵となる一歩は、x ∈ Lset α が何を意味するかを明かすことです。`Lset-out` により、x はある β ∈ α の上の定義可能部分集合の層に単に (merely) 属するにすぎません。層への所属もまた切り詰められていますが、結論 rank x ∈ α は命題なので、`PT.rec` が切り詰めを消去し、繊維 β、β∈α、x∈𝒟ₒLβ を与えられたものとして扱えます。
<!--/-->

```agda
       → (∀ β → β ∈ᵗ α → IsOrd β → (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ rank x ∈ˢ β ⟩)
       → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩
  step α IH ordα x x∈Lα = PT.rec (snd (rank x ∈ˢ α)) fromStage (Lset-out α x x∈Lα)
    where
    fromStage : Σ[ β ∈ S ] (⟨ β ∈ˢ α ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩) → ⟨ rank x ∈ˢ α ⟩
```

<!--en-->
Inside the fiber, everything needed to run the induction hypothesis is recovered. The member β of the ordinal α is itself an ordinal by `mem-ord`, which is what lets the inductive hypothesis fire at β.
<!--zh-->
在纤维内部，运行归纳假设所需的一切都被恢复。序数 α 的成员 β 经 `mem-ord` 本身就是序数，正是这一点让归纳假设得以在 β 处启用。
<!--ja-->
繊維の内部では、帰納仮説を動かすのに必要なものがすべて取り戻されます。順序数 α の要素 β は `mem-ord` によってそれ自身順序数であり、これこそが帰納仮説を β で発火させるものです。
<!--/-->

```agda
    fromStage (β , β∈α , x∈𝒟ₒLβ) = rankx∈α
      where
      ordβ : IsOrd β
      ordβ = mem-ord {A = α} ordα β β∈α
      x⊆Lβ : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ Lset β ⟩
```

<!--en-->
Definability of x over `Lset β` means x is a subset of it: `𝒟ₒ-inv` unpacks the certificate and `DefOf.Def∋⊆A` turns it into the inclusion x ⊆ Lset β. Composing with the inductive hypothesis, every member y of x has rank in β. Then `rank-upper`, given exactly such bounds on member ranks, includes `rank x` itself into β.
<!--zh-->
x 在 `Lset β` 上的可定义性意味着 x 是它的子集：`𝒟ₒ-inv` 拆开证书，`DefOf.Def∋⊆A` 把它变成包含关系 x ⊆ Lset β。与归纳假设结合，x 的每个成员 y 的秩都在 β 中。随后 `rank-upper` 在恰有这些成员秩上界的前提下，把 `rank x` 本身包含进 β。
<!--ja-->
`Lset β` の上での x の定義可能性は、x がその部分集合であることを意味します。`𝒟ₒ-inv` が証明書をほどき、`DefOf.Def∋⊆A` がそれを包含 x ⊆ Lset β に変えます。これを帰納仮説と組み合わせると、x の各要素 y の階数は β の中にあります。そして `rank-upper` は、まさにこのような要素の階数の上界を与えられれば、`rank x` 自身を β に含めます。
<!--/-->

```agda
      x⊆Lβ = DefOf.Def∋⊆A (Lset β) x (𝒟ₒ-inv (Lset β) x x∈𝒟ₒLβ)
      ry∈β : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ rank y ∈ˢ β ⟩
      ry∈β y y∈x = IH β β∈α ordβ y (x⊆Lβ y y∈x)

      rankx⊆β : (z : S) → ⟨ z ∈ˢ rank x ⟩ → ⟨ z ∈ˢ β ⟩
      rankx⊆β = rank-upper x β ordβ ry∈β
```

<!--en-->
What remains is to lift rank x ∈ sucV β into rank x ∈ α. Both rank x and β are ordinals, the former by `rank-ord`, and `⊆→∈suc` from the first section applies to their inclusion, placing rank x in the successor of β. The elimination `∈sucV-elim` then compares with the known β ∈ α: if rank x is a member of β, transitivity of α lifts the membership one step; if rank x equals β, the path transports β ∈ α directly. Either way the rank lands in α, completing the induction.
<!--zh-->
剩下的是把 rank x ∈ sucV β 提升为 rank x ∈ α。rank x 与 β 都是序数，前者由 `rank-ord` 保证，于是第一节建立的 `⊆→∈suc` 施于二者的包含关系，把 rank x 放进 β 的后继。随后 `∈sucV-elim` 与已知的 β ∈ α 比较：若 rank x 是 β 的成员，α 的传递性把隶属再推一步；若 rank x 等于 β，路径直接传递 β ∈ α。无论哪种情形，秩都落入 α，归纳完成。
<!--ja-->
残るのは、rank x ∈ sucV β を rank x ∈ α へ持ち上げることです。rank x と β はどちらも順序数で、前者は `rank-ord` によるものなので、最初の節の `⊆→∈suc` が両者の包含に適用され、rank x は β の後者の中に置かれます。続いて `∈sucV-elim` が既知の β ∈ α と比較します。rank x が β の要素なら、α の伝播性が所属を一段押し上げ、rank x が β と等しいなら、パスが β ∈ α を直接輸送します。いずれの場合も階数は α に着地し、帰納は完成します。
<!--/-->

```agda

      rankx∈α : ⟨ rank x ∈ˢ α ⟩
      rankx∈α = ∈sucV-elim {A = β} {x = rank x} (snd (rank x ∈ˢ α))
        (⊆→∈suc (rank x) β (rank-ord x) ordβ rankx⊆β)
        (λ rx∈β → ordα .fst rx∈β β∈α)
        (λ rx≡β → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym rx≡β) β∈α)
```

<!--en-->
For an ordinal the conclusion simplifies, because rank fixes it: an ordinal in `Lset α` is a member of `α`. This is the lower bound of the chapter's characterization in its usable form.
<!--zh-->
对序数，结论更简单，因为秩完全确定它：`Lset α` 中的序数是 `α` 的成员。这就是本章刻画中以下界形式呈现的可用版本。
<!--ja-->
順序数に対しては結論が単純になります。階数は順序数を固定するからです。`Lset α` に属する順序数は `α` の要素です。これが本章の特徴付けの下界を、使える形にしたものです。
<!--/-->

<!--en-->
The step is a transport: `rank-fix x ordx` gives the path rank x ≡ x, and substituting along it converts the rank bound rank x ∈ α into the membership x ∈ α. Note the direction, which the induction above guarantees: appearance in a stage forces membership in the index, not the converse.
<!--zh-->
这一步是一次传递：`rank-fix x ordx` 给出路径 rank x ≡ x，沿它替换即把秩上界 rank x ∈ α 转化为隶属 x ∈ α。注意方向，这正是上述归纳所保证的：在层中的现身强制对索引的隶属，而非相反。
<!--ja-->
この一歩は輸送です。`rank-fix x ordx` がパス rank x ≡ x を与え、それに沿った代入が階数の上界 rank x ∈ α を所属 x ∈ α に変えます。方向に注意してください。上の帰納法が保証するのは、段階への出現が添字への所属を強いるということで、その逆ではありません。
<!--/-->

```agda
ord∈Lset→∈ : (α : S) → IsOrd α → (x : S) → IsOrd x → ⟨ x ∈ˢ Lset α ⟩
           → ⟨ x ∈ˢ α ⟩
ord∈Lset→∈ α ordα x ordx x∈Lα =
  subst (λ w → ⟨ w ∈ˢ α ⟩) (rank-fix x ordx) (rank-Lset α ordα x x∈Lα)
```

<!--en-->
## Being an ordinal, said with bounded quantifiers

Being a transitive set all of whose members are transitive can be expressed with bounded quantifiers. The formula therefore recognizes ordinals absolutely between a transitive stage and the ambient universe.

The predicate is two clauses, and both are already bounded: a set is transitive when every member of every member of it is a member of it, and its members are transitive when the same holds one level down. No unbounded quantifier appears, so the formula is Δ₀, and no constant appears either, which spares the whole relabelling apparatus.

The indices are de Bruijn: each bounded quantifier binds a fresh variable `0` and pushes the earlier ones outward, so after two binders the candidate ordinal is at index 2.
<!--zh-->
## 用有界量词表达序数性质

一个集合是传递的，且其每个成员也都是传递的，这一性质可以用有界量词表达。因此，该公式在传递层与外围宇宙之间绝对地识别序数。

这个谓词由两条子句构成，两条都已有界：集合传递，指其成员的成员也都是其成员；成员皆传递，指同一条性质在低一层成立。没有无界量词出现，故公式是 Δ₀；也没有常元出现，从而免去了一整套常元改名操作。

索引采用 de Bruijn：每个有界量词约束一个新的变元 `0`，并把先前已有的变元向外推移一位，故两层约束之后，候选序数位于索引 2。
<!--ja-->
## 順序数であることを有界量化で表す

集合が推移的で、そのすべての要素も推移的であるという性質は、有界量化子だけで表せます。したがってこの論理式は、推移的な段階と周囲の宇宙の間で順序数を絶対的に認識します。

この述語は二つの節からなり、どちらもすでに有界です。集合が推移的であるとは、その要素の要素がすべてその要素であることであり、その要素がすべて推移的であるとは、同じ性質が一段下で成り立つことです。無界な量化子は現れないので論理式は Δ₀ であり、定数も現れないため、定数の改名の一連の操作はすべて不要になります。

添字は de Bruijn 方式です。各有界量化子は新しい変数 `0` を束縛し、既存の変数を外側へ押しやるので、二つの束縛子の後では候補の順序数は添字 2 にあります。
<!--/-->

<!--en-->
The first clause says transitivity. Its bounded quantifier ∀̇∈ ranges over members of the value bound one step out; reading the de Bruijn indices, after one binder the members live at index 0 and the candidate at index 1, and inside the second binder the atomic formula demands y ∈ x with y at 0 and x pushed to 2. The formula is polymorphic in the alphabet K of constants but uses none, so the same syntax serves every interpretation.
<!--zh-->
第一条子句说的是传递性。其有界量词 ∀̇∈ 在外一层所约束值的成员上取遍；按 de Bruijn 索引来读，第一层约束后成员位于索引 0、候选序数位于索引 1，而第二层约束内的原子公式要求 y ∈ x，y 在 0，x 被推到 2。公式对常元字母表 K 多态但不使用任何常元，故同一语法可服务于任何解释。
<!--ja-->
最初の節は伝播性を述べます。その有界量化子 ∀̇∈ は、一段外で束縛された値の要素を渡ります。de Bruijn 添字で読むと、一つの束縛子の後では要素は添字 0、候補は添字 1 にあり、二つ目の束縛子の内部では原子式が y ∈ x を要求し、y は 0、x は 2 へ押しやられています。論理式は定数のアルファベット K について多形ですがどの定数も使わないので、同じ構文があらゆる解釈に奉仕します。
<!--/-->

```agda
φ-ord : ∀ {ℓk} {K : Type ℓk} → Formula K 1
φ-ord =
  (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
  ∧̇
  (∀̇∈ (var zero)
```

<!--en-->
The second clause stacks one more quantifier: a member x of the candidate, a member y of x, and a member z of y must land back in the candidate, which says each member of the candidate is transitive. Three binders later, the innermost variable is at 0 and the candidate at 3. The certificate `φ-ord-Δ₀` is built from the same three primitive certificates, δ-∈ for atomic membership, δ-∀∈ for bounded quantifiers, and δ-∧ for the conjunction, mirroring the formula's construction step by step.
<!--zh-->
第二条子句多叠一层量词：候选序数的成员 x、x 的成员 y、y 的成员 z 必须落回候选序数，这正说明候选序数的每个成员都是传递的。三层约束之后，最内层变元在索引 0，候选序数在索引 3。证书 `φ-ord-Δ₀` 由同样的三种基本证书拼成，原子隶属的 δ-∈、有界量词的 δ-∀∈ 与合取的 δ-∧，一步对一步地映照公式的构造。
<!--ja-->
二番目の節はもう一段量化子を重ねます。候補の要素 x、x の要素 y、y の要素 z は候補へ戻らねばならず、これは候補の各要素が伝播的であることを述べます。三つの束縛子の後では、最内の変数は 0、候補は 3 にあります。証明書 `φ-ord-Δ₀` は同じ三種の基本的な証明書、原子式の所属に対する δ-∈、有界量化子に対する δ-∀∈、連言に対する δ-∧ から、論理式の構成に一歩ずつ対応して組み上げられます。
<!--/-->

```agda
    (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

φ-ord-Δ₀ : ∀ {ℓk} {K : Type ℓk} → Δ₀ (φ-ord {K = K})
φ-ord-Δ₀ = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))
```

<!--en-->
## The ordinals of a stage

Separation by the bounded ordinal formula collects exactly the ordinals belonging to a stage. Its membership specification is available both internally and in the ambient universe.

Fix a stage. Using bounded absoluteness for the transitive stage, satisfaction of the formula in the ambient hierarchy unfolds to exactly the two clauses of the ordinal predicate, so the two are interchangeable by reshuffling arguments. Then the definable subset it carves is `α` itself: a member of it is an ordinal of the stage, hence a member of `α` by the rank half; and a member of `α` is an ordinal that has already appeared, by cumulation, so it satisfies the formula.

Cumulation needs, for each member of `α`, that it appears at its own successor stage. That is the theorem itself, so it enters here as a hypothesis, and the induction below is what supplies it.
<!--zh-->
## 一层中的序数

用有界序数公式作分离，恰好收集属于某一层的全部序数。其成员规格在内部与外围宇宙中都可使用。

固定一层。利用传递层上的有界绝对性，公式在环境层级中的满足恰好展开成序数谓词的两条子句，故二者只需重排参数即可互换。于是它作分离所得的可定义子集就是 `α` 自身：其成员是该层的序数，故经秩那一半是 `α` 的成员；而 `α` 的成员是已经现身过的序数，经累积引理，它们满足该公式。

累积引理需要 `α` 的每个成员都在自身的后继层现身。这恰是本定理的结论本身，故在此把它作为假设引入，而下面的归纳正是给出这一假设的论证。
<!--ja-->
## 一つの段階に属する順序数

有界な順序数論理式による分出は、ある段階に属する順序数をちょうど集めます。その所属の仕様は、内部と周囲の宇宙の両方で使えます。

段階を一つ固定します。推移的な段階についての有界絶対性を使うと、周囲の階層における論理式の充足は順序数述語の二つの節にちょうど展開され、二者は引数を並べ替えるだけで交換できます。すると、この式が切り出す定義可能部分集合は `α` 自身です。その要素はその段階の順序数なので、階数の方向により `α` の要素であり、逆に `α` の要素は、累積によってすでに現れた順序数なので、この式を充足します。

累積には、`α` の各要素が自身の後者段階で現れることが必要です。それはこの定理自身の結論なので、ここでは仮定として入り、次の節の帰納法がまさにそれを供給します。
<!--/-->

<!--en-->
Fix the ordinal α with its certificate. The stage A = `Lset α` is a layer, and `layer-trans` upgrades that to transitivity of A as a set, the only hypothesis under which the Δ₀ formula will be absolute between A's internal satisfaction and the ambient universe. The definability machinery of the chapter on L.Definability is opened relative to A, so `defSet φ` below always means the subset φ defines out of A.
<!--zh-->
固定序数 α 及其证书。层 A = `Lset α` 是一层，`layer-trans` 把它升级为集合 A 的传递性，这是 Δ₀ 公式在 A 的内部满足与外围宇宙之间保持绝对的唯一前提。L.Definability 那章的可定义性机制相对于 A 打开，故下文的 `defSet φ` 总指 φ 从 A 中定出的子集。
<!--ja-->
順序数 α とその証明を固定します。段階 A = `Lset α` は層であり、`layer-trans` がそれを集合としての A の伝播性へ引き上げます。Δ₀ 論理式が A の内部の充足と周囲の宇宙の間で絶対的であるための前提は、これが唯一です。L.Definability の章の定義可能性の機構は A に対して開かれているので、以下の `defSet φ` は常に φ が A から定義する部分集合を意味します。
<!--/-->

```agda
module OrdAt (α : S) (ordα : IsOrd α) where
  private
    A = Lset α
    Atrans = layer-trans (Lset-layer α)
    module DefA = DefOf A
```

<!--en-->
Members of A present themselves through the fiber ⟪ A ⟫: an index m names the element ⟪ A ⟫↪ m of A. The formula φ is our φ-ord instantiated at the carrier ⟪ A ⟫, so it has one free-variable slot, occupied by the environment ⟪ A ⟫↪ m ∷ []. Because φ has no constants, `mapFo DefA.ι φ` merely relabels through the constant interpretation ι, which for this formula changes nothing syntactically. The satisfaction sign ⊨ᵛ here is the ambient one, from the absoluteness refinement.
<!--zh-->
A 的成员通过纤维 ⟪ A ⟫ 自我呈现：指标 m 命名 A 中的元素 ⟪ A ⟫↪ m。公式 φ 是 φ-ord 在载体 ⟪ A ⟫ 上的实例，它有一个自由变元槽，由环境 ⟪ A ⟫↪ m ∷ [] 占据。由于 φ 不含常元，`mapFo DefA.ι φ` 只是经常元解释 ι 改名，就这条公式而言在语法上没有改变任何东西。此处的满足号 ⊨ᵛ 是绝对性细化所给的、外围层面的满足。
<!--ja-->
A の要素は繊維 ⟪ A ⟫ を通して現れます。添字 m が A の要素 ⟪ A ⟫↪ m を名指すのです。論理式 φ は φ-ord を台 ⟪ A ⟫ 上に実例化したもので、自由変数の枠を一つ持ち、環境 ⟪ A ⟫↪ m ∷ [] がそれを占めます。φ は定数を含まないので、`mapFo DefA.ι φ` は定数の解釈 ι を通した改名にすぎず、この論理式については構文的には何も変えません。ここの充足記号 ⊨ᵛ は、絶対性の精緻化が与える周囲の充足です。
<!--/-->

```agda
    module RefA = DefA.Refine Atrans
    open RefA.Abs using ( _⊨ᵛ_ )

    φ : Formula ⟪ A ⟫ 1
    φ = φ-ord {K = ⟪ A ⟫}

  ⊨ᵛ→ord : (m : ⟪ A ⟫) → ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
```

<!--en-->
The first direction reads satisfaction into the ordinal predicate. The satisfaction of a conjunction is a pair, and its first component is exactly the first bounded clause applied to x = B, the presented element: every y ∈ x with x ∈ B lands back in B. That is the transitivity condition for B, so the pair's first projection is a certificate that B is transitive.
<!--zh-->
第一个方向把满足关系读成序数谓词。合取的满足是一个有序对，其第一个分量恰是第一条有界子句施于 x = B (所呈现的元素) 的结果：凡 y ∈ x 且 x ∈ B 者，都落回 B。这正是 B 的传递性条件，故该对的第一个投影就是 B 传递的证书。
<!--ja-->
最初の方向は、充足を順序数述語へと読み込みます。連言の充足は対であり、その第一成分は、提示された要素 x = B に対する最初の有界節の適用にほかなりません。x ∈ B かつ y ∈ x なるすべての y が B へ戻る、というものです。これは B の伝播性の逐語的な表述なので、この対の第一射影は B が伝播的である証明になります。
<!--/-->

```agda
         → IsOrd (⟪ A ⟫↪ m)
  ⊨ᵛ→ord m sat = transB , memTransB
    where
    B = ⟪ A ⟫↪ m
    transB : isTransV B
```

<!--en-->
The second component is the second clause, with the quantifiers nested one deeper: for x ∈ B, y ∈ x and z ∈ y, the element z lands in B. That says precisely that every member x of B is itself transitive, so together with the first projection the satisfaction data is exactly an IsOrd certificate for B.
<!--zh-->
第二个分量是第二条子句，量词更深一层嵌套：对 x ∈ B、y ∈ x、z ∈ y，元素 z 落回 B。这恰好说明 B 的每个成员 x 自身都是传递的，于是连同第一个投影，满足数据恰是 B 的 IsOrd 证书。
<!--ja-->
第二成分は二番目の節で、量化子がもう一段深く入れ子になります。x ∈ B、y ∈ x、z ∈ y に対して要素 z は B へ戻る。これは B の各要素 x がそれ自身伝播的であることをまさに述べるので、第一射影と合わせて、充足のデータは B に対する IsOrd の証明にほかなりません。
<!--/-->

```agda
    transB {x} {y} y∈x x∈B = sat .fst x x∈B y y∈x
    memTransB : (x : S) → ⟨ x ∈ˢ B ⟩ → isTransV x
    memTransB x x∈B {y} {z} z∈y y∈x = sat .snd x x∈B y y∈x z z∈y

  ord→⊨ᵛ : (m : ⟪ A ⟫) → IsOrd (⟪ A ⟫↪ m)
         → ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
```

<!--en-->
The converse direction assembles a satisfaction from an ordinal certificate. Its first component must accept x ∈ B and y ∈ x and return y ∈ B, and transitivity of B, the first component of the IsOrd pair, does exactly that with the arguments in the right order.
<!--zh-->
逆方向由序数证书组装出一个满足。其第一个分量须接受 x ∈ B 与 y ∈ x 并返回 y ∈ B，而 IsOrd 有序对的第一个分量，即 B 的传递性，恰以正确的参数顺序完成此事。
<!--ja-->
逆向きの方向は、順序数の証明から充足を組み立てます。その第一成分は x ∈ B と y ∈ x を受け取り y ∈ B を返さねばなりませんが、IsOrd の対の第一成分、つまり B の伝播性が、引数を正しい順に並べてまさにそれを行います。
<!--/-->

```agda
  ord→⊨ᵛ m ord = c1 , c2
    where
    B = ⟪ A ⟫↪ m
    c1 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ B ⟩
    c1 x x∈B y y∈x = ord .fst y∈x x∈B
```

<!--en-->
The second component must chain three memberships back into B, and the second clause of the IsOrd pair is exactly that chain. So satisfaction of φ and the ordinal predicate are interchangeable in both directions; the two formulations express the same mathematical condition. With this equivalence established, the main statement takes shape: the definable subset selected by φ equals α, proved by `extensionality` from two inclusions, and stated under the explicit hypothesis α⊆A that every member of α has already appeared in A.
<!--zh-->
第二个分量须把三个隶属串回 B，而 IsOrd 有序对的第二条子句正是这个串联条件。于是 φ 的满足与序数谓词在两个方向都可互换；二者表达同一数学条件。有了这一等价，主要陈述成形：φ 所选出的可定义子集等于 α，由 `extensionality` 经两个包含证明，并陈述于显式假设 α⊆A 之下，即 α 的每个成员已在 A 中现身。
<!--ja-->
第二成分は三つの所属を B へとつなげる必要があり、IsOrd の対の二番目の節はこの連鎖そのものです。したがって φ の充足と順序数述語は両方向で交換可能です。二つの表現は同じ数学的条件を述べています。この同値を得ると、主張が形を成します。φ が選ぶ定義可能部分集合は α に等しい、というもので、二つの包含から `extensionality` で証明され、α の各要素がすでに A に現れているという明示的な仮定 α⊆A のもとで述べられます。
<!--/-->

```agda
    c2 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩
       → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    c2 x x∈B y y∈x z z∈y = ord .snd x x∈B z∈y y∈x

  defSet-φ-ord : ((β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ A ⟩) → DefA.defSet φ ≡ α
  defSet-φ-ord α⊆A = extensionality (DefA.defSet φ) α (sub₁ , sub₂)
```

<!--en-->
The inclusion from the definable subset to α is where the rank half of the chapter earns its keep. Membership in a definable subset unfolds by `∈∈ₛ` into a presentation-level fact, so sub₁ takes y with a proof that y belongs to `defSet φ` and must produce y ∈ α.
<!--zh-->
从可定义子集到 α 的包含，是本章秩那一半发挥作用的所在。可定义子集中的隶属经 `∈∈ₛ` 展开为呈现层面的事实，故 sub₁ 取一个 y 及「y 属于 `defSet φ`」的证明，须产出 y ∈ α。
<!--ja-->
定義可能部分集合から α への包含は、本章の階数の方向が真価を発揮する場所です。定義可能部分集合への所属は `∈∈ₛ` によって提示のレベルの事実へ展開されるので、sub₁ は、y が `defSet φ` に単に (merely) 属するという証明とともに y を受け取り、y ∈ α を作り出さねばなりません。
<!--/-->

```agda
    where
    sub₁ : ⟨ DefA.defSet φ ⊆ α ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = α} .fst
      (y∈α (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ))
      where
```

<!--en-->
Three conversions stack here. Membership of y in the definable subset yields membership in A by `defSet⊆A`, since the subset is contained in the stage. The chosen presentation turns this membership proof, via `∈-asFiber`, into an index m and a path q identifying y with the element named by m.
<!--zh-->
这里叠加了三次转换。y 属于可定义子集，由 `defSet⊆A` 得出 y 属于 A，因为子集包含于层。随后，选定的呈现通过 `∈-asFiber` 把这个隶属证明变成指标 m 与路径 q；该路径把 y 与 m 所指名的元素等同起来。
<!--ja-->
ここでは三つの変換が積み重なります。定義可能部分集合への y の所属は、部分集合が段階に含まれるため `defSet⊆A` によって A への所属を与えます。次に繊維 `∈-asFiber` がその周囲の所属をその表示に置き換えます。添字 m とパス q で、これらは単に (merely) 存在するにすぎません。
<!--/-->

```agda
      y∈α : ⟨ y ∈ˢ DefA.defSet φ ⟩ → ⟨ y ∈ˢ α ⟩
      y∈α y∈def = ord∈Lset→∈ α ordα y ordy y∈A
        where
        y∈A = DefA.defSet⊆A φ y y∈def
        fib = ∈-asFiber {a = y} {b = A} y∈A
```

<!--en-->
The path q transports membership from y to the presented element ⟪ A ⟫↪ m. Because φ is Δ₀ and A is transitive, `abs-defSet` identifies the hProp of membership in `defSet φ` with the hProp of ambient satisfaction of `mapFo ι φ` at the one-element environment. Substitution along these paths yields the required inhabitant sat; path transport itself imposes no propositionality condition.
<!--zh-->
路径 q 把 y 的隶属传递为所呈现元素 ⟪ A ⟫↪ m 的隶属。由于 φ 是 Δ₀ 且 A 传递，`abs-defSet` 等同了「该元素属于 `defSet φ`」与「`mapFo ι φ` 在单元环境处外围满足」这两个 hProp。沿这些路径替换便得到所需的 sat；路径传递本身不要求目标具有命题性。
<!--ja-->
パス q は y の所属を提示された要素 ⟪ A ⟫↪ m の所属へ輸送します。φ は Δ₀ で A は推移的なので、`abs-defSet` は `defSet φ` への所属という hProp と、一要素の環境における `mapFo ι φ` の周囲での充足という hProp を同一視します。これらのパスに沿った置換から必要な sat が得られます。パス輸送そのものは、対象が命題であることを要求しません。
<!--/-->

```agda
        m = fib .fst
        q = fib .snd
        sat : ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
        sat = subst ⟨_⟩ (RefA.abs-defSet φ φ-ord-Δ₀ m)
                (subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) (sym q) y∈def)
```

<!--en-->
From sat, the implication `⊨ᵛ→ord` returns an IsOrd certificate for the presented element, and transporting along q turns it into one for y itself. Then `ord∈Lset→∈`, the rank half, places y inside α. So an arbitrary member of the definable subset is an ordinal of the stage, and the stage index contains it.
<!--zh-->
由 sat，蕴涵 `⊨ᵛ→ord` 返回所呈现元素的 IsOrd 证书，沿 q 传递后便得到 y 自身的证书。随后 `ord∈Lset→∈`，即秩那一半，把 y 放进 α。于是可定义子集的任意成员都是该层的序数，而层索引包含它。
<!--ja-->
sat から、含意 `⊨ᵛ→ord` が提示された要素の IsOrd 証明を返し、q に沿った輸送がそれを y 自身の証明に変えます。次に `ord∈Lset→∈`、つまり階数の方向が、y を α の中に置きます。よって定義可能部分集合の任意の要素はその段階の順序数であり、段階の添字がそれを含みます。
<!--/-->

```agda
        ordy : IsOrd y
        ordy = subst IsOrd q (⊨ᵛ→ord m sat)

    sub₂ : ⟨ α ⊆ DefA.defSet φ ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DefA.defSet φ} .fst
      (y∈def (∈∈ₛ {a = y} {b = α} .snd y∈ₛ))
```

<!--en-->
The reverse inclusion runs the same circuit backward. A member y of α arrives with its ordinal certificate already in hand, from `mem-ord`. The hypothesis α⊆A presents y inside the stage via a fiber m, q, and `ord→⊨ᵛ` gives ambient satisfaction of φ at that environment.
<!--zh-->
反向包含把同一回路倒着走。α 的成员 y 到手时已带着序数证书，由 `mem-ord` 给出。假设 α⊆A 经纤维 m、q 把 y 呈现在层内，`ord→⊨ᵛ` 便给出 φ 在该环境处的外围满足。
<!--ja-->
逆向きの包含は、同じ回路を逆にたどります。α の要素 y は、`mem-ord` による順序数の証明をすでに手にした状態でやって来ます。仮定 α⊆A が繊維 m、q を通して y を段階の内部に提示し、`ord→⊨ᵛ` がその環境における φ の周囲の充足を与えます。
<!--/-->

```agda
      where
      y∈def : ⟨ y ∈ˢ α ⟩ → ⟨ y ∈ˢ DefA.defSet φ ⟩
      y∈def y∈α = subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) q
        (subst ⟨_⟩ (sym (RefA.abs-defSet φ φ-ord-Δ₀ m)) sat)
        where
```

<!--en-->
Absoluteness now converts in the other direction: ambient satisfaction of the Δ₀ formula is membership of ⟪ A ⟫↪ m in `defSet φ`, and transporting along q lands the membership on y itself, inside the definable subset. No choice is made anywhere: each fiber m, q is used locally, on the very y that produced it.
<!--zh-->
绝对性现在朝另一方向换算：Δ₀ 公式的外围满足等于 ⟪ A ⟫↪ m 属于 `defSet φ`，沿 q 传递便把隶属落在 y 自身，即可定义子集之内。全程未做任何选择：每个纤维 m、q 都只在产生它的那个 y 上局部使用。
<!--ja-->
絶対性が今度は逆方向へ変換します。Δ₀ 論理式の周囲の充足は ⟪ A ⟫↪ m の `defSet φ` への所属であり、q に沿った輸送がその所属を y 自身の上に、定義可能部分集合の内部に着地させます。どの場所でも選択は行われません。各繊維 m、q は、それを生んだまさにその y の上で、局所的に使われるだけです。
<!--/-->

```agda
        ordy = mem-ord {A = α} ordα y y∈α
        y∈A = α⊆A y y∈α
        fib = ∈-asFiber {a = y} {b = A} y∈A
        m = fib .fst
        q = fib .snd
```

<!--en-->
The two inclusions close, and `defSet-φ-ord` states the conclusion: the subset the bounded formula carves out of `Lset α` is exactly α. Everything so far is conditional on α⊆A; the next section removes the condition, and with it the chapter's main theorem falls into place.
<!--zh-->
两个包含合拢，`defSet-φ-ord` 陈述结论：有界公式从 `Lset α` 中切出的子集恰是 α。至此一切都以 α⊆A 为条件；下一节将移除这个条件，本章的主定理随之就位。
<!--ja-->
二つの包含が閉じ、`defSet-φ-ord` が結論を述べます。有界論理式が `Lset α` から切り出す部分集合は、まさに α である、と。ここまでのすべては α⊆A を条件とします。次の節がこの条件を取り除き、本章の主定理がそこに収まります。
<!--/-->

```agda
        sat : ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
        sat = ord→⊨ᵛ m (subst IsOrd (sym q) ordy)
```

<!--en-->
## An ordinal appears at its successor

Every ordinal is a definable subset of itself, selected by the bounded ordinal formula. Hence `α` belongs to the definable power set of `Lset α`, which is the successor stage.

The remaining gap is the inclusion `α ⊆ Lset α`, which the previous section had to assume. It is filled by induction on membership: the induction hypothesis states the theorem for each member `β` of `α`, so `β` appears in `Lset (sucV β)`, and cumulation from the first section raises it into `Lset α`. Once every member has accumulated, `α` is carved out of `Lset α` by the formula, and one branch of the union in the definition of the next stage contains it. The circularity is only apparent, because the induction hypothesis concerns the members, not `α` itself.
<!--zh-->
## 序数现身于其后继

每个序数都是自身的可定义子集，由有界序数公式选出。因此 `α` 属于 `Lset α` 的可定义幂集，也就是后继层。

剩下的缺口正是上一节不得不假设的包含关系 `α ⊆ Lset α`。它由对隶属关系的归纳填补：归纳假设陈述的是定理对 `α` 的每个成员 `β` 的情形，于是 `β` 出现在 `Lset (sucV β)` 中，再经第一节的累积引理被提升到 `Lset α` 中。一旦所有成员都累积进来，公式便从 `Lset α` 中分离出 `α`，而下一层定义中的并包含这一项。这里没有循环：归纳假设关心的是成员，而非 `α` 自身。
<!--ja-->
## 順序数は自身の後者段階に現れる

各順序数は、有界な順序数論理式によって選ばれる自身の定義可能部分集合である。したがって `α` は `Lset α` の定義可能冪集合、すなわち後者段階に属する。

残る溝は、前節で仮定せざるを得なかった包含 `α ⊆ Lset α` である。これは所属に関する帰納法で埋める。帰納法の仮定は、`α` の各要素 `β` に対して定理そのものを与える。すなわち `β` は `Lset (sucV β)` に現れ、第一節の累積補題によって `Lset α` へ持ち上げられる。すべての要素が累積し終えると、論理式が `Lset α` から `α` を分出し、次の段階の定義における和の一つの枝がこれを含む。循環は見かけにすぎない。帰納法の仮定が扱うのは `α` 自身ではなく要素だからである。
<!--/-->

<!--en-->
Two small facts are packaged before the induction. The first is a one-way bridge from definable power set to stage: a certificate that `α` lies in `𝒟ₒ (Lset α)`, meaning `α` is a definable subset of `Lset α`, is exactly the data `Lset-in` needs, once combined with `self∈sucV α`, which says `α` belongs to its own successor. The second line begins the theorem itself, and the induction principle for membership is applied directly: the statement being proved by induction is the theorem, relativized to each ordinal.
<!--zh-->
归纳之前先打包两个小事实。其一是从可定义幂集到层的单向桥：一个说明 `α` 属于 `𝒟ₒ (Lset α)` 的证书，即 `α` 是 `Lset α` 的可定义子集，与 `self∈sucV α` (它说 `α` 属于自身的后继) 合在一起，恰是 `Lset-in` 所需的全部数据。第二行开始定理本身，直接应用对隶属关系的归纳原理：被归纳证明的陈述就是定理本身，相对化到每个序数上。
<!--ja-->
帰納法の前に二つの小事実をまとめておく。一つ目は定義可能冪集合から段階への一方通行の橋である。`α` が `𝒟ₒ (Lset α)` に属する、すなわち `α` が `Lset α` の定義可能部分集合であるという証明は、`α` が自身の後者に属することを述べる `self∈sucV α` と合わせて、`Lset-in` が必要とするデータそのものである。二行目からは定理そのものが始まり、所属に関する帰納法の原理を直接適用する。帰納法で示される命題は、各順序数へ相対化された定理そのものだ。
<!--/-->

```agda
private
  𝒟ₒ→Lset-suc : (α : S) → ⟨ α ∈ˢ 𝒟ₒ (Lset α) ⟩ → ⟨ α ∈ˢ Lset (sucV α) ⟩
  𝒟ₒ→Lset-suc α α∈𝒟ₒ = Lset-in (sucV α) α α (self∈sucV α) α∈𝒟ₒ

ord∈Lset-suc : (α : S) → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩
ord∈Lset-suc = ∈-induction
```

<!--en-->
The induction step receives, for every member `β` of `α`, the theorem's conclusion at `β`, and must produce it at `α`. Since the previous section already reduced the goal to the single hypothesis `α ⊆ Lset α`, all the step does is assemble that inclusion and hand the result to the bridge lemma. Nothing about `α` beyond its ordinalhood and the induction hypothesis is used.
<!--zh-->
归纳步对 `α` 的每个成员 `β` 收到定理在 `β` 处的结论，并须给出在 `α` 处的结论。由于上一节已把目标化归为唯一的假设 `α ⊆ Lset α`，这一步要做的只是组装这个包含关系，并把结果交给桥引理。除了 `α` 是序数与归纳假设之外，别无所用。
<!--ja-->
帰納段は、`α` の各要素 `β` に対して定理の `β` における結論を受け取り、`α` における結論を組み立てなければならない。前節がすでに目標を唯一の仮定 `α ⊆ Lset α` に帰着させているため、この段がするのはその包含を組み立てて橋の補題に渡すことだけである。`α` が順序数であることと帰納法の仮定のほかには何も使わない。
<!--/-->

```agda
  {P = λ α → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩} step
  where
  step : (α : S) → (∀ β → β ∈ᵗ α → IsOrd β → ⟨ β ∈ˢ Lset (sucV β) ⟩)
       → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩
  step α IH ordα = 𝒟ₒ→Lset-suc α α∈𝒟ₒ
```

<!--en-->
The inclusion is built member-by-member. For each `β` in `α`, being a member of the ordinal `α` makes `β` an ordinal in its own right, and the induction hypothesis places it in `Lset (sucV β)`; the cumulation lemma of the first section, whose second comparison was designed for exactly this shape, then lifts it to `Lset α`. This is where the earlier comparison lemmas pay off: a single case split on whether `sucV β` lies in `α` or equals it covers every member at once.
<!--zh-->
包含关系逐个成员地组装。对 `α` 中的每个 `β`，作为序数 `α` 的成员使 `β` 自己也是序数，归纳假设把它放进 `Lset (sucV β)`；而第一节的累积引理，正是为其后继或落入 `α`、或与之相等这两种情形而设，随即把它提升到 `Lset α`。前面那两个比较引理在此兑现：一次分情形就同时覆盖了所有成员。
<!--ja-->
包含は要素ごとに組み立てられる。`α` の各 `β` に対し、順序数 `α` の要素であることで `β` 自身も順序数となり、帰納法の仮定がそれを `Lset (sucV β)` に置く。第一節の累積補題は、`sucV β` が `α` に属するか等しいかというちょうどこの形のために設計されたもので、それによって `β` は `Lset α` へ持ち上げられる。前の二つの比較補題がここで効いてくる。場合分けは一度で全要素を同時に扱う。
<!--/-->

```agda
    where
    α⊆A : (β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset α ⟩
    α⊆A β β∈α = Lset-cumul β α ordβ ordα β∈α (IH β β∈α ordβ)
      where
      ordβ = mem-ord {A = α} ordα β β∈α
```

<!--en-->
With `α ⊆ Lset α` in hand, the previous section's conclusion applies verbatim: the definable subset of `Lset α` selected by `φ-ord` is `α` itself. The certificate is supplied merely, by truncation, since a member of `𝒟ₒ` needs only some defining formula and proof of agreement, and the pair of `φ-ord` with the extensionality argument from `OrdAt` is exactly such a witness. The bridge lemma then moves `α` into `Lset (sucV α)`, completing the induction and the theorem.
<!--zh-->
有了 `α ⊆ Lset α`，上一节的结论原样适用：由 `φ-ord` 从 `Lset α` 中选出的可定义子集正是 `α` 自身。证书以截断的方式仅仅给出，因为 `𝒟ₒ` 的成员只需要某个定义公式及一致性证明，而 `φ-ord` 与 `OrdAt` 中的外延性论证组成的对恰是这样的见证。桥引理随后把 `α` 移入 `Lset (sucV α)`，归纳与定理同时完成。
<!--ja-->
`α ⊆ Lset α` が手に入れば、前節の結論がそのまま使える。`φ-ord` が `Lset α` から選び出す定義可能部分集合は `α` 自身である。証明は切り詰めによって単に与えられればよい。`𝒟ₒ` の要素は何らかの定義論理式と一致の証明を必要とするだけであり、`φ-ord` と `OrdAt` の外延性の議論の対がまさにそのような証拠になる。橋の補題が続いて `α` を `Lset (sucV α)` へ移し、帰納法と定理が同時に完成する。
<!--/-->

```agda
    α∈𝒟ₒ : ⟨ α ∈ˢ 𝒟ₒ (Lset α) ⟩
    α∈𝒟ₒ = 𝒟ₒ-intro (Lset α) α
      ∣ φ-ord {K = ⟪ Lset α ⟫} , OrdAt.defSet-φ-ord α ordα α⊆A ∣₁
```

<!--en-->
## Recap

Ordinals now have exact stage bounds: `α` appears in `Lset (sucV α)`, and appearance in `Lset β` forces `α ∈ β`. The bounded ordinal formula makes these facts available to later internal arguments.

`ord∈Lset-suc`{.Agda} says an ordinal appears at the stage after itself, and `ord∈Lset→∈`{.Agda} says it appears no earlier. Together the ordinals of `Lset α` are exactly the members of `α`. The chapter is classical, through the two comparisons of its first section, and everything else it uses was constructive. The module `L.Stage` applies this result to `ω`, completing the proof of the axiom of infinity.
<!--zh-->
## 小结

序数现在具有准确的层界：`α` 出现在 `Lset (sucV α)` 中，而若它出现在 `Lset β` 中，则必有 `α ∈ β`。有界序数公式使后续内部论证能够使用这些事实。

`ord∈Lset-suc`{.Agda} 说序数现身在自身之后的那一层中，`ord∈Lset→∈`{.Agda} 说它不会更早现身。二者合起来，`Lset α` 中的序数恰是 `α` 的成员。经由第一节那两次比较，本章是经典的，而它用到的其余一切都是构造性的。模块 `L.Stage` 将这一结果应用于 `ω`，从而完成无穷公理的证明。
<!--ja-->
## まとめ

これで順序数の段階の上限が正確になった。`α` は `Lset (sucV α)` に現れ、`Lset β` に現れるなら `α ∈ β` である。有界な順序数論理式により、後の内部議論でこれらの事実を利用できる。

`ord∈Lset-suc`{.Agda} は順序数が自身の後者の段階に現れることを述べ、`ord∈Lset→∈`{.Agda} はそれより早くは現れないことを述べる。二者を合わせると、`Lset α` の順序数は `α` の要素ちょうどである。本章は第一節の二つの比較を通して古典的であり、それ以外に使ったものはすべて構成的であった。モジュール `L.Stage` はこの結果を `ω` に適用し、無限公理の証明を完成させる。
<!--/-->
