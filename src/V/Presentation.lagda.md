<!--en-->
# Small presentations of sets

Every set of the cumulative hierarchy `V`{.Agda} comes with a canonical small presentation: an index type and an embedding whose image is the set. This chapter records the elementary lemmas that move back and forth between an index and a proof of membership, together with the injectivity of the embedding and the small-membership form of canonical membership. The small presentation plays a structural role throughout later constructions, where reasoning about the elements of a set means reasoning about its indices.
<!--zh-->
# 集合的小呈现

累积层级 `V`{.Agda} 中的每个集合都自带一个典范的小呈现：一个索引类型和一张嵌入，其像正是该集合。本章记录在索引与隶属证明之间往返的基本引理，并记下嵌入的单射性以及典范隶属的小隶属形式。小呈现是后续构造反复依赖的结构性工具：讨论一个集合的元素，就是在讨论它的索引。
<!--ja-->
# 集合の小さな提示

累積階層 `V`{.Agda} の各集合には、標準的な小さな提示が備わっています。インデックス型と埋め込みであり、その像こそがその集合です。本章では、インデックスと所属証明の間を行き来する初等的な補題、埋め込みの単射性、そして標準的な所属の小所属としての形を記録します。集合の要素について論じることは、そのインデックスについて論じることであるため、この小さな提示は後の構成で繰り返し依拠される構造的な道具です。
<!--/-->

<!--en-->
A set in the hierarchy is an image: the higher inductive constructor `sett`{.Agda} builds, from a small index type and a family into `V`{.Agda}, the set of values that family takes. Membership `y ∈ sett X ix` holds merely when some index `i : X` satisfies `ix i ≡ y`, and the path constructor identifies two presentations with the same members. So the primitive notion of set here is already a notion of presentation, and the following lemmas make that presentation usable in membership arguments. The universe parameter `ℓ` fixes how large the index types are allowed to be; everything below is relative to that fixed level.
<!--zh-->
层级中的集合就是像：高阶归纳构造子 `sett`{.Agda} 从一个小索引类型和指向 `V`{.Agda} 的族，造出该族取值组成的集合。成员关系 `y ∈ sett X ix` 仅当某个索引 `i : X` 满足 `ix i ≡ y` 时成立，而路径构造子把成员一致的两个呈现视为同一个集合。所以这里的原始集合概念本身就是一种呈现概念，下面的引理使这份呈现可以直接用于隶属论证。宇宙参数 `ℓ` 规定索引类型允许的大小；以下一切都在这个固定的层级上进行。
<!--ja-->
階層における集合とは像のことです。高階帰納型の構成子 `sett`{.Agda} は、小さなインデックス型と `V`{.Agda} への族から、その族の値のなす集合を形作ります。所属 `y ∈ sett X ix` は、`ix i ≡ y` となるインデックス `i : X` が切り詰められた形で存在するときに成り立ち、パス構成子は要素の一致する二つの表示を同一視します。つまりここでの原始的な集合概念は、それ自体が提示の概念であり、以下の補題により、この提示を所属の議論で直接使えるようになります。宇宙パラメータ `ℓ` がインデックス型に許される大きさを定め、以下はすべてこの固定されたレベルに相対的です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Presentation {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The same membership fact appears in two forms, and the lemmas below move between them. The ambient structure `𝒮ᵥ`{.Agda} takes paths as equality and the native membership as its relation, read as the proposition `x ∈ˢ y`; a proof of it is a truncated existence statement, so no index comes with it. Alongside this, the small membership `a ∈ₛ b` is an equivalent proposition at level `ℓ` rather than `ℓ-suc ℓ`: its underlying type asks for an index of `b` together with a bisimulation proof. For each set `a` there is a chosen presentation: a small type `⟪ a ⟫`, an embedding `⟪ a ⟫↪` into the hierarchy whose embedding property is recorded by `isEmb⟪ a ⟫↪`, and a proof `∈ₛ⟪ a ⟫↪ _` of small membership for each of its own indices. The lemmas below combine exactly these ingredients.
<!--zh-->
同一个隶属事实有两种形式，下面的引理正是在它们之间往返。环境结构 `𝒮ᵥ`{.Agda} 以路径为等式、以原生隶属为关系，读作命题 `x ∈ˢ y`；它的证明是截断后的存在性陈述，因此不附带任何索引。与之并行，小隶属 `a ∈ₛ b` 是一个等价的命题，取值于层级 `ℓ` 而非 `ℓ-suc ℓ`：其底层类型要求 `b` 的一个索引以及一个双模拟证明。对每个集合 `a` 有一份选定的呈现：小类型 `⟪ a ⟫`、到层级中的嵌入 `⟪ a ⟫↪` (其嵌入性质由 `isEmb⟪ a ⟫↪` 记录)，以及对其自身每个索引的小隶属证明 `∈ₛ⟪ a ⟫↪ _`。下面的引理组合的正是这些成分。
<!--ja-->
同じ所属の事実には二つの形があり、以下の補題はその間を行き来します。周囲の構造 `𝒮ᵥ`{.Agda} はパスを等号とし、本来の所属を関係として採り、それを命題 `x ∈ˢ y` として読みます。その証明は切り詰められた存在言明であり、インデックスを伴いません。これに対して小所属 `a ∈ₛ b` は同値な命題であり、`ℓ-suc ℓ` ではなくレベル `ℓ` に住みます。その基礎型は `b` のインデックスと双シミュレーション証明の組を要求します。各集合 `a` には選ばれた提示があります。小さな型 `⟪ a ⟫`、階層への埋め込み `⟪ a ⟫↪` (その埋め込みの性質は `isEmb⟪ a ⟫↪` が記録します)、そしてそのインデックスそれぞれへの小所属の証明 `∈ₛ⟪ a ⟫↪ _` です。以下の補題はまさにこれらの材料を組み合わせます。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )

open hPropStructure 𝒮ᵥ
```

<!--en-->
The first two lemmas convert between indices and membership proofs. To see the direction each takes, note that `∈∈ₛ` states that native and small membership of `a` in `b` are equivalent, packaged as a pair of implications. Since `∈ˢ` in `𝒮ᵥ`{.Agda} is the native membership, `member` applies the right-to-left implication to the small-membership certificate `∈ₛ⟪ a ⟫↪ m` and thus produces an inhabitant of the type `⟪ a ⟫↪ m ∈ˢ a`: an explicit proof that the set a contains the element named by the index `m`. The converse is `fiber`: given a proof `x ∈ˢ a`, it returns an actual index `m : ⟪ a ⟫` together with a path `⟪ a ⟫↪ m ≡ x`. This is not the truncated existence of an index but an explicitly constructed one; it works because the embedding has proposition-valued fibers, so the truncated membership statement can be eliminated into the type of fibers.
<!--zh-->
前两条引理在索引与隶属证明之间转换。注意 `∈∈ₛ` 说明 `a` 对 `b` 的原生隶属与小隶属等价，打包成一双向蕴含。由于 `𝒮ᵥ`{.Agda} 中的 `∈ˢ` 就是原生隶属，`member` 把右往左的蕴含应用于小成员证书 `∈ₛ⟪ a ⟫↪ m`，从而得到类型 `⟪ a ⟫↪ m ∈ˢ a` 的一个元素：索引 `m` 所指名的元素确实属于集合 `a` 的显式证明。反向的是 `fiber`：给定证明 `x ∈ˢ a`，它返回一个实际的索引 `m : ⟪ a ⟫` 连同路径 `⟪ a ⟫↪ m ≡ x`。这不是索引的截断存在性，而是显式构造出的索引；之所以可行，是因为该嵌入的原像都是命题，截断的隶属陈述得以消去到原像类型中。
<!--ja-->
最初の二つの補題は、インデックスと所属証明を相互に変換します。鍵となるのは `∈∈ₛ` で、`a` の `b` への本来の所属と小所属が同値であることを、二つの含意の組として述べます。`𝒮ᵥ`{.Agda} の `∈ˢ` は本来の所属そのものなので、`member` は右から左への含意を小所属証明 `∈ₛ⟪ a ⟫↪ m` に適用し、型 `⟪ a ⟫↪ m ∈ˢ a` の要素、すなわちインデックス `m` の指す要素が集合 `a` に属することの明示的な証明を生み出します。逆が `fiber` です。証明 `x ∈ˢ a` が与えられると、実際のインデックス `m : ⟪ a ⟫` とパス `⟪ a ⟫↪ m ≡ x` の組を返します。これはインデックスの切り詰められた存在ではなく、明示的に構成されたインデックスです。埋め込みのファイバーが命題値であるため、切り詰められた所属述語をファイバー型へと消去できるからです。
<!--/-->

```agda

member : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ a ⟩
member a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

fiber : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ ⟪ a ⟫ ] (⟪ a ⟫↪ m ≡ x)
fiber a {x} x∈ = ∈-asFiber {a = x} {b = a} x∈

↪-inj : {a : S} {m n : ⟪ a ⟫} → ⟪ a ⟫↪ m ≡ ⟪ a ⟫↪ n → m ≡ n
```

<!--en-->
Two short facts complete the picture. The embedding property is exactly injectivity on indices: an embedding into an h-set has proposition-valued fibers, and the standard lemma `isEmbedding→Inj` turns that into the statement that equal values have equal indices, which `↪-inj` records. Finally `∈ₛ↪` states small membership directly: for every index `m`, the element `⟪ a ⟫↪ m` belongs to `a` in the small relation, with certificate `∈ₛ⟪ a ⟫↪ m`. Together with `member`, this shows the canonical presentation is faithful in both the native and the small membership, and that its indexing map neither loses nor duplicates elements.
<!--zh-->
两条简短的事实补全全貌。嵌入性质正是索引上的单射性：到 h-集合的嵌入有命题值的原像，标准引理 `isEmbedding→Inj` 由此得出「值相等则索引相等」，`↪-inj` 记录了这一点。最后 `∈ₛ↪` 直接陈述小隶属：对每个索引 `m`，元素 `⟪ a ⟫↪ m` 以证书 `∈ₛ⟪ a ⟫↪ m` 按小关系属于 `a`。与 `member` 合看，这表明典范呈现对原生隶属与小隶属都是忠实的，且其索引映射既不丢失也不重复元素。
<!--ja-->
短い二つの事実が全体を完成させます。埋め込みの性質とは、インデックス上の単射性のことです。h-集合への埋め込みは命題値のファイバーを持ち、標準補題 `isEmbedding→Inj` はそこから「値が等しければインデックスも等しい」を導きます。これを `↪-inj` が記録します。最後に `∈ₛ↪` は小所属を直接述べます。各インデックス `m` に対し、要素 `⟪ a ⟫↪ m` は証明 `∈ₛ⟪ a ⟫↪ m` とともに小所属の意味で `a` に属します。`member` と併せて、標準的な提示が本来の所属と小所属のどちらに対しても忠実であり、そのインデックス写像が要素を失わず複製しないことが示されます。
<!--/-->

```agda
↪-inj {a} {m} {n} = isEmbedding→Inj isEmb⟪ a ⟫↪ m n

∈ₛ↪ : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ₛ a ⟩
∈ₛ↪ a m = ∈ₛ⟪ a ⟫↪ m
```
