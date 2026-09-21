<!--en-->
# Small presentations of sets

Membership in a set of the cumulative hierarchy is index-based, but only in a weakened sense: the statement `x ∈ a` records that some index merely exists, and it lives one universe above the index types themselves. Doing set theory inside the hierarchy therefore asks for a way to pass between indices and membership proofs, and for a supply of indices that is small, concrete and unique. This chapter records the elementary lemmas that provide both. Every set comes with a canonical small presentation, an index type and an embedding whose image is the set, and the lemmas move back and forth between an index and a proof of membership, record the injectivity of the embedding, and restate canonical membership in the small relation. Later constructions rely on this package: reasoning about the elements of a set becomes reasoning about its indices.
<!--zh-->
# 集合的小呈现

累积层级中集合的隶属以索引为基础，却只是弱化的形式：陈述 `x ∈ a` 只记录某个索引单纯存在，而且它住在比索引类型本身高一层的宇宙。因此，要在层级内部做集合论，就需要在索引与隶属证明之间往返的方法，也需要一份小而具体、且唯一的索引供给。本章记录提供这两者的基本引理。每个集合都带有典范的小呈现：一个索引类型和一张嵌入，其像正是该集合；这些引理在索引与隶属证明之间往返，记录嵌入的单射性，并把典范隶属改写成小关系的形式。后续构造依赖这套工具：讨论一个集合的元素，由此成为讨论它的索引。
<!--ja-->
# 集合の小さな提示

累積階層の集合への所属はインデックスを基礎とするが、弱められた形にすぎない。主張 `x ∈ a` はあるインデックスが単に存在することを記録するだけで、しかもインデックス型そのものより一つ上の宇宙に住む。したがって階層の中で集合論を行うには、インデックスと所属証明の間を行き来する方法と、小さく、具体的で、一意なインデックスの供給が必要になる。本章はその両方を与える初等的な補題を記録する。すべての集合は正準的な小さな提示、すなわちその像がその集合であるインデックス型と埋め込みを伴い、補題はインデックスと所属証明の間を行き来し、埋め込みの単射性を記録し、正準的な所属を小関係の形で言い直す。後の構成はこの一式に依拠する。集合の要素について論じることは、そのインデックスについて論じることになるのである。
<!--/-->

<!--en-->
The primitive notion of set is here already a notion of presentation. The constructor `sett`{.Agda} builds, from a small index type and a family into `V`{.Agda}, the set of values that family takes; membership `y ∈ sett X ix` holds merely when some index `i : X` satisfies `ix i ≡ y`; and the path constructor identifies two presentations with the same members. A presentation is thus built into every set, and the following lemmas make it usable in membership arguments. The universe parameter `ℓ` fixes how large the index types are allowed to be, and everything below is relative to that fixed level.
<!--zh-->
这里的原始集合概念本身就是一种呈现概念。构造子 `sett`{.Agda} 从一个小索引类型和指向 `V`{.Agda} 的族，造出该族取值组成的集合；成员关系 `y ∈ sett X ix` 仅当某个索引 `i : X` 满足 `ix i ≡ y` 时成立；路径构造子把成员一致的两个呈现视为同一个集合。呈现由此内建于每个集合，下面的引理使它可以直接用于隶属论证。宇宙参数 `ℓ` 规定索引类型允许的大小，以下一切都在这个固定的层级上进行。
<!--ja-->
ここでの原始的な集合概念は、それ自体がすでに提示の概念である。構成子 `sett`{.Agda} は、小さなインデックス型と `V`{.Agda} への族から、その族の値のなす集合を形作る。所属 `y ∈ sett X ix` は、`ix i ≡ y` となるインデックス `i : X` が切り詰められた形で存在するときに成り立つ。そしてパス構成子は、要素の一致する二つの表示を同一視する。提示はこのようにすべての集合に組み込まれており、以下の補題はそれを所属の議論で直接使えるようにする。宇宙パラメータ `ℓ` がインデックス型に許される大きさを定め、以下はすべてこの固定されたレベルに相対的である。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Presentation {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The same membership fact appears in two forms, and the lemmas below move between them. In the structure `𝒮ᵥ`{.Agda}, membership is read as the proposition `x ∈ˢ y`; a proof of it is a truncated existence statement, so no index comes with it. Alongside this, the small membership `a ∈ₛ b` is an equivalent proposition at level `ℓ` rather than `ℓ-suc ℓ`: its underlying type asks for an index of `b` together with a proof that the named element agrees with `a` under bisimulation. For each set `a` there is a chosen presentation: a small type `⟪ a ⟫` of indices, an embedding `⟪ a ⟫↪` into the hierarchy whose embedding property is recorded by `isEmb⟪ a ⟫↪`, and a proof `∈ₛ⟪ a ⟫↪ _` of small membership for each of its own indices. The presentation is canonical in a strong sense: a set cannot carry two different presentations of this kind. The lemmas below combine exactly these ingredients.
<!--zh-->
同一个隶属事实有两种形式，下面的引理正是在它们之间往返。在结构 `𝒮ᵥ`{.Agda} 中，隶属读作命题 `x ∈ˢ y`；它的证明是截断后的存在性陈述，因此不附带任何索引。与之并行，小隶属 `a ∈ₛ b` 是一个等价的命题，取值于层级 `ℓ` 而非 `ℓ-suc ℓ`：其底层类型要求 `b` 的一个索引，以及所指元素与 `a` 在双模拟意义上一致的证明。对每个集合 `a` 有一份选定的呈现：小索引类型 `⟪ a ⟫`、到层级中的嵌入 `⟪ a ⟫↪` (其嵌入性质由 `isEmb⟪ a ⟫↪` 记录)，以及对其自身每个索引的小隶属证明 `∈ₛ⟪ a ⟫↪ _`。这份呈现是强意义下的典范：一个集合不可能带有两份这样的不同呈现。下面的引理组合的正是这些成分。
<!--ja-->
同じ所属の事実には二つの形があり、以下の補題はその間を行き来する。構造 `𝒮ᵥ`{.Agda} では、所属は命題 `x ∈ˢ y` として読まれる。その証明は切り詰められた存在言明であり、インデックスを伴わない。これに対して小所属 `a ∈ₛ b` は同値な命題であり、`ℓ-suc ℓ` ではなくレベル `ℓ` に住む。その基礎型は、`b` のインデックスと、名指された要素が `a` と双シミュレーションの意味で一致することの証明の組を要求する。各集合 `a` には選ばれた提示がある。小さなインデックス型 `⟪ a ⟫`、階層への埋め込み `⟪ a ⟫↪` (その埋め込みの性質は `isEmb⟪ a ⟫↪` が記録する)、そしてそのインデックスそれぞれへの小所属の証明 `∈ₛ⟪ a ⟫↪ _` である。この提示は強い意味で正準的である。ひとつの集合が、この種の異なる提示を二つ持つことはない。以下の補題はまさにこれらの材料を組み合わせる。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )

open hPropStructure 𝒮ᵥ
```

<!--en-->
The first two lemmas convert between indices and membership proofs. The hinge is `∈∈ₛ`, which states that native and small membership agree, packaged as a pair of implications. The lemma `member` takes an index `m : ⟪ a ⟫` and applies the small-to-native implication to the certificate `∈ₛ⟪ a ⟫↪ m`, producing an inhabitant of `⟪ a ⟫↪ m ∈ˢ a`: an explicit proof that `a` contains the element named by `m`. The converse `fiber` starts from a proof of `x ∈ˢ a` and returns an actual index `m : ⟪ a ⟫` together with a path `⟪ a ⟫↪ m ≡ x`. This is not the truncated existence of an index but an explicitly constructed one. The step is legitimate because the embedding has proposition-valued fibers: the truncated membership statement may then be eliminated into the type of such fibers, and there the index can be read off.
<!--zh-->
前两条引理在索引与隶属证明之间转换。枢纽是 `∈∈ₛ`：它说明原生隶属与小隶属一致，并打包成一双向蕴含。引理 `member` 取索引 `m : ⟪ a ⟫`，把「小到原生」方向的蕴含应用于证书 `∈ₛ⟪ a ⟫↪ m`，得到 `⟪ a ⟫↪ m ∈ˢ a` 的一个元素：索引 `m` 所指名的元素确实属于集合 `a` 的显式证明。反向的 `fiber` 从 `x ∈ˢ a` 的证明出发，返回一个实际的索引 `m : ⟪ a ⟫` 连同路径 `⟪ a ⟫↪ m ≡ x`。这不是索引的截断存在性，而是显式构造出的索引。这一步之所以合法，是因为该嵌入的原像都是命题：截断的隶属陈述得以消去到这种原像的类型中，索引便可在其中读出。
<!--ja-->
最初の二つの補題は、インデックスと所属証明を相互に変換する。鍵となるのは `∈∈ₛ` で、本来の所属と小所属が一致することを、二つの含意の組として述べる。補題 `member` はインデックス `m : ⟪ a ⟫` を取り、小から本来への含意を証明 `∈ₛ⟪ a ⟫↪ m` に適用し、`⟪ a ⟫↪ m ∈ˢ a` の要素を生み出す。これは、インデックス `m` の指す要素が集合 `a` に属することの明示的な証明である。逆の `fiber` は `x ∈ˢ a` の証明から出発し、実際のインデックス `m : ⟪ a ⟫` とパス `⟪ a ⟫↪ m ≡ x` の組を返す。これはインデックスの切り詰められた存在ではなく、明示的に構成されたインデックスである。この一段階が正当なのは、埋め込みのファイバーが命題値だからである。切り詰められた所属の主張はこのファイバーの型へ消去でき、そこでインデックスを読み取れる。
<!--/-->

```agda

member : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ a ⟩
member a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

fiber : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ ⟪ a ⟫ ] (⟪ a ⟫↪ m ≡ x)
fiber a {x} x∈ = ∈-asFiber {a = x} {b = a} x∈

↪-inj : {a : S} {m n : ⟪ a ⟫} → ⟪ a ⟫↪ m ≡ ⟪ a ⟫↪ n → m ≡ n
```

<!--en-->
Two short facts complete the picture. The embedding property is exactly injectivity on indices: an embedding into an h-set has proposition-valued fibers, and the standard lemma `isEmbedding→Inj` turns that into the statement that equal values have equal indices, which `↪-inj` records. Finally `∈ₛ↪` states small membership directly: for every index `m`, the element `⟪ a ⟫↪ m` belongs to `a` in the small relation, with certificate `∈ₛ⟪ a ⟫↪ m`. Together with `member`, this shows that the canonical presentation is faithful in both the native and the small membership, and that its indexing map neither loses nor duplicates elements.
<!--zh-->
两条简短的事实补全全貌。嵌入性质正是索引上的单射性：到 h-集合的嵌入有命题值的原像，标准引理 `isEmbedding→Inj` 由此得出「值相等则索引相等」，`↪-inj` 记录了这一点。最后 `∈ₛ↪` 直接陈述小隶属：对每个索引 `m`，元素 `⟪ a ⟫↪ m` 以证书 `∈ₛ⟪ a ⟫↪ m` 按小关系属于 `a`。与 `member` 合看，这表明典范呈现对原生隶属与小隶属都是忠实的，且其索引映射既不丢失也不重复元素。
<!--ja-->
短い二つの事実が全体を完成させる。埋め込みの性質とは、インデックス上の単射性のことである。h-集合への埋め込みは命題値のファイバーを持ち、標準補題 `isEmbedding→Inj` はそこから「値が等しければインデックスも等しい」を導く。これを `↪-inj` が記録する。最後に `∈ₛ↪` は小所属を直接述べる。各インデックス `m` に対し、要素 `⟪ a ⟫↪ m` は証明 `∈ₛ⟪ a ⟫↪ m` とともに小所属の意味で `a` に属する。`member` と併せて、正準的な提示が本来の所属と小所属のどちらに対しても忠実であり、そのインデックス写像が要素を失わず複製しないことが示される。
<!--/-->

```agda
↪-inj {a} {m} {n} = isEmbedding→Inj isEmb⟪ a ⟫↪ m n

∈ₛ↪ : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ₛ a ⟩
∈ₛ↪ a m = ∈ₛ⟪ a ⟫↪ m
```
