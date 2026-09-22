<!--en-->
# Choosing a cardinal representative for an ordinal

Counting inside `L` is expressed in terms of cardinals, while a construction often produces an arbitrary ordinal. For an ordinal `α` of `L`, this chapter finds an internal cardinal `μ` contained in `α`, together with internal injections in both directions. Thus `μ` represents the cardinality of `α` inside the model. The representative is obtained by searching the successor of `α` for the least ordinal into which `α` internally injects.
<!--zh-->
# 为序数选取基数代表

`L` 内部的计数以基数表述，而具体构造往往只产生任意序数。对 `L` 中的序数 `α`，本章找出包含于 `α` 的内部基数 `μ`，并给出两个方向的内部单射。因此，`μ` 在模型内部代表 `α` 的基数。构造在 `α` 的后继中搜索，选取 `α` 能够内部单射到的最小序数。
<!--ja-->
# 順序数の基数代表を選ぶ

`L` の内部での計数は基数によって述べるが、具体的な構成が与えるのは任意の順序数であることが少なくない。`L` の順序数 `α` に対し、本章では `α` に含まれる内部基数 `μ` と、両方向の内部単射を構成する。したがって `μ` はモデルの内部で `α` の濃度を代表する。この代表は、`α` の後続の中から、`α` が内部単射する最小の順序数を探して得られる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.GCH.CardinalRepresentative {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Fix excluded middle at level `ℓ-suc ℓ`. It is used by the well-order search and by ordinal trichotomy. All injections in the conclusion remain internal to `L`: their graphs are constructible sets rather than external functions.
<!--zh-->
假设在层级 `ℓ-suc ℓ` 上成立排中律。良序搜索与序数三分法都会使用这个假设。结论中的单射全部位于 `L` 内部：它们由可构造的图见证，并非外部函数。
<!--ja-->
レベル `ℓ-suc ℓ` における排中律を仮定する。この仮定は整列順序上の探索と順序数の三分法で使われる。結論の単射はすべて `L` の内部にあり、そのグラフは外部関数ではなく構成可能集合である。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
```

<!--en-->
Two structures are present. The ambient hierarchy supplies membership and the small presentations used for search. The constructible structure supplies the ordinal, cardinal and internal-injection predicates. Constructibility descends along membership, allowing a member found in the ambient hierarchy to be returned to the carrier of `L`.
<!--zh-->
这里同时出现两个结构。外围层级提供成员关系以及搜索所用的小呈现；可构造结构提供序数、基数与内部单射谓词。可构造性沿成员关系向下传递，所以在外围层级中找到的成员可以重新进入 `L` 的论域。
<!--ja-->
ここでは二つの構造を使う。周囲の階層は所属関係と探索に用いる小さな表示を与え、構成可能構造は順序数、基数、内部単射の述語を与える。構成可能性は所属に沿って下方へ伝わるので、周囲の階層で見つけた要素を `L` の論域へ戻せる。
<!--/-->

```agda
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL; module LeastCardInjL )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( IsLeast; leastOfFormula; module SWO )
open import L.DefinableInjection {ℓ} lem using ( injLAt; module InjLAt )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )

```

<!--en-->
The search rests on the well-order of the indices presenting an ordinal. Its order agrees with membership between the represented elements. Inclusion coding turns containment into an internal injection, and transitivity composes successive internal injections.
<!--zh-->
搜索建立在呈现序数的索引良序之上；这个次序与所指元素之间的成员关系一致。包含关系的编码把包含化为内部单射，单射的传递性则复合连续的内部单射。
<!--ja-->
探索は、順序数を表示するインデックスの整列順序に基づく。この順序は、表示される要素の間の所属と一致する。包含の符号化が包含を内部単射に変え、単射の推移性が内部単射を合成する。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
```

<!--en-->
The candidate set is the successor `sucV α`. Propositional truncation expresses the existence of a suitable representative without choosing one externally; sums and the empty type support the later trichotomy argument.
<!--zh-->
候选集合取为后继 `sucV α`。命题截断表达适当代表的存在，而不在外部选择一个代表；和类型与空类型用于后面的三分法论证。
<!--ja-->
候補集合は後続 `sucV α` である。命題的切り詰めは、外部で代表を選ぶことなく適切な代表の存在を表す。和型と空型は後の三分法の議論で使われる。
<!--/-->

```agda

```

<!--en-->
Write `SV.S` for ambient sets and `SL.S` for constructible sets. An element of `SL.S` pairs an ambient set with its constructibility certificate. Membership comparisons occur on first components, whereas `InjL` and `IsCardinalL` concern the complete constructible elements.
<!--zh-->
以 `SV.S` 表示外围集合，以 `SL.S` 表示可构造集合。`SL.S` 的元素由外围集合及其可构造性证书组成。成员关系比较作用于第一分量，而 `InjL` 与 `IsCardinalL` 以完整的可构造元素为对象。
<!--ja-->
周囲の集合を `SV.S`、構成可能集合を `SL.S` と書く。`SL.S` の要素は周囲の集合と構成可能性の証明の対である。所属の比較は第一成分について行い、`InjL` と `IsCardinalL` は完全な構成可能要素について述べる。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
module SV = hPropStructure 𝒮ᵥ using ( S )
module SL = hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Given an ordinal `α`, the theorem merely asserts the existence of `μ` with five properties: `μ` is an ordinal, `μ` is an internal cardinal, `μ ⊆ α`, and there are internal injections `α ↪ μ` and `μ ↪ α`. The truncation makes the conclusion a proposition.
<!--zh-->
给定序数 `α`，定理仅仅断言存在满足五项性质的 `μ`：`μ` 是序数，是内部基数，满足 `μ ⊆ α`，并且存在内部单射 `α ↪ μ` 与 `μ ↪ α`。截断使整个结论成为命题。
<!--ja-->
順序数 `α` に対し、定理は五つの性質を持つ `μ` が単に存在することを述べる。`μ` は順序数かつ内部基数で、`μ ⊆ α` であり、内部単射 `α ↪ μ` と `μ ↪ α` がある。切り詰めにより結論全体は命題になる。
<!--/-->

```agda
cardOf :
    (α : SL.S) → IsOrd (fst α)
  → ∥ Σ[ μ ∈ SL.S ]
       ( IsOrd (fst μ) × IsCardinalL μ
```

<!--en-->
The final witness is assembled from the representative `μ` and the five proofs constructed below. Since the target is truncated, producing this single tuple closes the theorem once its components are available.
<!--zh-->
最终见证由代表 `μ` 与下面构造的五项证明组成。由于目标已经截断，只要这些分量齐备，放入这个依值对即可完成定理。
<!--ja-->
最終的な証人は、代表 `μ` と以下で構成する五つの証明からなる。目標は切り詰められているので、成分がそろえばこの一つの依存対を入れることで定理が閉じる。
<!--/-->

```agda
       × ((z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩)
       × InjL α μ × InjL μ α ) ∥₁
```

<!--en-->
The auxiliary search setup for `α` supplies the successor's constructibility, the index naming `α` itself, the corresponding equality, and a well-order `w` on the presentation indices. The order relation of `w` is membership between the named ordinals.
<!--zh-->
关于 `α` 的辅助搜索准备提供后继的可构造性、指名 `α` 自身的索引及相应等式，还提供呈现索引上的良序 `w`。`w` 的次序关系就是所指序数之间的成员关系。
<!--ja-->
`α` に対する補助的な探索の準備は、後続の構成可能性、`α` 自身を名指すインデックスとその等式、表示インデックス上の整列順序 `w` を与える。`w` の順序関係は、名指された順序数の間の所属である。
<!--/-->

```agda
cardOf α oα = ∣ μ , oμ , cardμ , μ⊆α , α↪μ , μ↪α ∣₁
  where
  module LC = LeastCardInjL α oα using ( hSucα; self; self-eq; w; w-lt )

```

<!--en-->
Let `T` be the successor of the underlying ordinal `α`. The successor is again an ordinal, so every member of `T` is an ordinal and the order inherited from membership is available throughout the search.
<!--zh-->
令 `T` 为序数 `α` 的底层集合的后继。后继仍是序数，因此 `T` 的每个成员都是序数，搜索全程都可使用由成员关系给出的次序。
<!--ja-->
`T` を、順序数 `α` の基礎集合の後続とする。後続も順序数なので、`T` の各要素は順序数であり、探索の全体で所属から得られる順序を使える。
<!--/-->

```agda
  T : SV.S
  T = sucV (fst α)

  oT : IsOrd T
  oT = suc-ord oα
```

<!--en-->
The set `T` is constructible. This certificate is needed because a search index names only an ambient member of `T`; downward closure of constructibility will turn that member into an element of `SL.S`.
<!--zh-->
集合 `T` 是可构造的。这个证书不可或缺，因为搜索索引最初只指名 `T` 的外围成员；可构造性的向下封闭把该成员化为 `SL.S` 的元素。
<!--ja-->
集合 `T` は構成可能である。この証明が必要なのは、探索インデックスが最初に名指すのは `T` の周囲の要素にすぎず、構成可能性の下方閉性によって初めてその要素を `SL.S` の要素にできるからである。
<!--/-->

```agda
  opaque
    hT : ⟨ isL T ⟩
    hT = LC.hSucα
```

<!--en-->
For an index `b` of the presentation of `T`, `upL b` pairs the represented member with its constructibility proof. The latter follows from membership in `T` and the constructibility of `T`.
<!--zh-->
对 `T` 的呈现索引 `b`，`upL b` 把所指成员与其可构造性证明配成依值对。后一个证明由该成员属于 `T` 以及 `T` 的可构造性得到。
<!--ja-->
`T` の表示インデックス `b` に対し、`upL b` は名指された要素とその構成可能性の証明を対にする。後者は、その要素が `T` に属することと `T` の構成可能性から従う。
<!--/-->

```agda
  upL : ⟪ T ⟫ → SL.S
  upL b = ⟪ T ⟫↪ b , isL-trans (member T b) hT
  Good : ⟪ T ⟫ → hProp (ℓ-suc ℓ)
  Good b = InjL α (upL b) , squash₁

  definedGood : FOL.Semantics.FormulaPredicate 𝒮ʟ ⟪ T ⟫ SL.S id Good
  definedGood = FOL.Semantics.presented 2 (injLAt zero (suc zero))
    (λ b → α ∷ upL b ∷ [])
    (λ b → ⇔toPath
      (InjLAt.fill zero (suc zero) (α ∷ upL b ∷ []))
      (InjLAt.read zero (suc zero) (α ∷ upL b ∷ [])))
```

<!--en-->
Call an index `b` good when there is an internal coded injection from `α` to the constructible member `upL b` that it names. The package `definedGood` exposes this property through `injLAt`: its two environment slots contain `α` and `upL b`, while `InjLAt.fill` and `InjLAt.read` prove the two semantic directions. Thus the later least search sees a fixed object-language formula rather than an arbitrary host predicate.
<!--zh-->
若存在从 `α` 到索引 `b` 所指可构造成员 `upL b` 的内部编码单射，就称 `b` 为好索引。包 `definedGood` 通过 `injLAt` 显露这个性质：两个环境槽分别放入 `α` 与 `upL b`，而 `InjLAt.fill` 和 `InjLAt.read` 证明语义的两个方向。因此，后续最小元搜索看到的是一条固定的对象语言公式，而不是任意宿主谓词。
<!--ja-->
`α` からインデックス `b` が名指す構成可能要素 `upL b` への内部符号化単射があるとき、`b` を良いインデックスと呼ぶ。パッケージ `definedGood` はこの性質を `injLAt` によって公開する。二つの環境位置には `α` と `upL b` が入り、`InjLAt.fill` と `InjLAt.read` が意味論の両方向を証明する。したがって後の最小要素探索が見るのは、任意のホスト述語ではなく固定された対象論理式である。
<!--/-->

```agda
  selfGood : ⟨ Good LC.self ⟩
  selfGood = inclusion-coded α α (λ z z∈α → z∈α)

  nonempty : ∥ Σ[ b ∈ ⟪ T ⟫ ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ LC.self , selfGood ∣₁
```

<!--en-->
The index naming `α` is good: its represented member equals `α`, and the identity inclusion codes an internal injection from `α` to itself. Hence the type of good indices is merely inhabited.
<!--zh-->
指名 `α` 的索引是好的：它所指成员等于 `α`，恒等包含则编码出从 `α` 到自身的内部单射。因此，好索引的类型仅仅非空。
<!--ja-->
`α` を名指すインデックスは良いものである。名指された要素は `α` に等しく、恒等的な包含が `α` から自身への内部単射を符号化する。したがって良いインデックスの型には単に要素が存在する。
<!--/-->

```agda

  least : Σ[ b ∈ ⟪ T ⟫ ] IsLeast LC.w Good b
  least = leastOfFormula LC.w definedGood lem nonempty

  m : ⟪ T ⟫
  m = fst least
```

<!--en-->
Apply the formula-facing least-element search to the well-order `w` and `definedGood`. Excluded middle decides satisfaction of the displayed injection formula, and nonemptiness guarantees a least good index. Denote that index by `m`.
<!--zh-->
对良序 `w` 与 `definedGood` 应用面向公式的最小元搜索。排中律判定所展示单射公式的满足关系，非空性保证存在最小的好索引；把它记作 `m`。
<!--ja-->
整列順序 `w` と `definedGood` に、論理式に面する最小要素探索を適用する。排中律が表示された単射論理式の充足を判定し、非空性が最小の良いインデックスを保証する。そのインデックスを `m` と書く。
<!--/-->

```agda

  μ : SL.S
  μ = upL m

  μ∈T : ⟨ fst μ ∈ˢ T ⟩
  μ∈T = member T m
```

<!--en-->
Lift the chosen index `m` to the constructible carrier and call the result `μ`. By construction its underlying set is the member of `T` named by `m`.
<!--zh-->
把选中的索引 `m` 提升到可构造论域，并把所得元素记作 `μ`。依定义，`μ` 的底层集合就是 `m` 在 `T` 中指名的成员。
<!--ja-->
選んだインデックス `m` を構成可能な論域へ持ち上げ、その結果を `μ` と呼ぶ。定義により、`μ` の基礎集合は `m` が `T` の中で名指す要素である。
<!--/-->

```agda

  oμ : IsOrd (fst μ)
  oμ = mem-ord {A = T} oT (fst μ) μ∈T
```

<!--en-->
The presentation theorem gives `μ ∈ T`. Since `T` is an ordinal, every member of it is an ordinal; consequently `μ` is an ordinal as required.
<!--zh-->
呈现定理给出 `μ ∈ T`。由于 `T` 是序数，其每个成员仍是序数，所以 `μ` 具有所需的序数性。
<!--ja-->
表示の定理から `μ ∈ T` が得られる。`T` は順序数なので、その各要素も順序数である。したがって `μ` は必要な順序数性を持つ。
<!--/-->

```agda
  α↪μ : InjL α μ
  α↪μ = fst (snd least)
```

<!--en-->
Goodness of the least index is now stated directly as the formula-defined proposition `InjL α μ`, because `μ` is the constructible member named by `m`. Thus the selected candidate immediately supplies the forward injection.
<!--zh-->
最小索引的合格性如今直接表述为由公式定义的命题 `InjL α μ`，因为 `μ` 正是 `m` 指名的可构造成员。因此，选中的候选立即给出正向单射。
<!--ja-->
最小インデックスの良さは、今では論理式で定義された命題 `InjL α μ` として直接述べられる。`μ` は `m` が名指す構成可能な要素だからである。したがって、選ばれた候補から前向きの単射が直ちに得られる。
<!--/-->

```agda
  cardμ : IsCardinalL μ
  cardμ δ δ∈μ μ↪δ = snd (snd least) b bGood b<m
    where
    δ∈T : ⟨ fst δ ∈ˢ T ⟩
    δ∈T = oT .fst {x = fst μ} {y = fst δ} δ∈μ μ∈T
```

<!--en-->
To prove that `μ` is a cardinal, suppose a member `δ ∈ μ` admitted an internal injection `μ ↪ δ`. Transitivity of the ordinal `T` places `δ` in `T`, so its presentation yields an index `b`.
<!--zh-->
为证明 `μ` 是基数，假设某个成员 `δ ∈ μ` 允许内部单射 `μ ↪ δ`。序数 `T` 的传递性给出 `δ ∈ T`，于是 `T` 的呈现产生一个指名 `δ` 的索引 `b`。
<!--ja-->
`μ` が基数であることを示すため、ある要素 `δ ∈ μ` に内部単射 `μ ↪ δ` があると仮定する。順序数 `T` の推移性から `δ ∈ T` となり、`T` の表示が `δ` を名指すインデックス `b` を与える。
<!--/-->

```agda
    b : ⟪ T ⟫
    b = fiber T δ∈T .fst
    bδ : ⟪ T ⟫↪ b ≡ fst δ
```

<!--en-->
The fibre theorem gives both the index `b` and the equality identifying its represented member with `δ`. These data let membership and injection statements be transported between the indexed member and the constructible element `δ`.
<!--zh-->
纤维定理同时给出索引 `b` 以及把它所指成员识别为 `δ` 的等式。这些数据使成员关系与单射陈述可以在索引成员和可构造元素 `δ` 之间搬运。
<!--ja-->
ファイバーの定理は、インデックス `b` と、その表示要素を `δ` と同一視する等式を与える。このデータにより、所属と単射の主張を、インデックスで表された要素と構成可能要素 `δ` の間で移送できる。
<!--/-->

```agda
    bδ = fiber T δ∈T .snd
    bS : upL b ≡ δ
    bS = Σ≡Prop (λ x → snd (isL x)) bδ
    bGood : ⟨ Good b ⟩
    bGood = subst (InjL α) (sym bS) (injl-trans α μ δ α↪μ μ↪δ)
```

<!--en-->
The index `b` is good: compose `α ↪ μ` with the assumed `μ ↪ δ`, and use the fibre equality to match the indexed member. Thus `b` is another candidate in the same search.
<!--zh-->
索引 `b` 是好的：把 `α ↪ μ` 与假设的 `μ ↪ δ` 复合，再用纤维等式匹配索引所指的成员。于是 `b` 是同一次搜索中的另一个候选。
<!--ja-->
インデックス `b` は良いものである。`α ↪ μ` と仮定した `μ ↪ δ` を合成し、ファイバーの等式でインデックスの表示要素に合わせる。したがって `b` は同じ探索の別の候補である。
<!--/-->

```agda
    b<m : SWO._<∙_ LC.w b m
    b<m = transport (λ i → sym (LC.w-lt b m) i)
            (subst (λ z → ⟨ z ∈ˢ fst μ ⟩) (sym bδ) δ∈μ)
```

<!--en-->
Moreover `b < m`. The relation of `w` is membership between represented ordinals, and the assumed `δ ∈ μ` transports to precisely this comparison. A good index strictly below the least good index is impossible, so no such injection `μ ↪ δ` exists. Hence `μ` is an internal cardinal.
<!--zh-->
而且 `b < m`。良序 `w` 的关系就是所指序数之间的成员关系，假设 `δ ∈ μ` 搬运后恰好给出这个比较。最小好索引之下不可能再有好索引，所以这样的单射 `μ ↪ δ` 不存在；因此 `μ` 是内部基数。
<!--ja-->
さらに `b < m` である。`w` の関係は表示された順序数の間の所属であり、仮定 `δ ∈ μ` を移送すると、まさにこの比較が得られる。最小の良いインデックスより下に良いインデックスがあることは不可能なので、そのような単射 `μ ↪ δ` は存在しない。したがって `μ` は内部基数である。
<!--/-->

```agda
  μ⊆α : (z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩
  μ⊆α = go (ord-tri (fst μ) oμ (fst α) oα)
    where
    go : Tri (fst μ) (fst α) → (z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst α ⟩
```

<!--en-->
It remains to show `μ ⊆ α`. Ordinal trichotomy compares their underlying ordinals. If `μ ∈ α`, transitivity of `α` gives the inclusion; if `μ = α`, transport gives it.
<!--zh-->
还需证明 `μ ⊆ α`。序数三分法比较二者的底层序数。若 `μ ∈ α`，由 `α` 的传递性得到包含；若 `μ = α`，沿等式搬运即可。
<!--ja-->
残るのは `μ ⊆ α` である。順序数の三分法で二つの基礎順序数を比較する。`μ ∈ α` なら `α` の推移性から包含が従い、`μ = α` なら等式に沿う移送で得られる。
<!--/-->

```agda
    go (inl μ∈α)       z z∈μ = oα .fst z∈μ μ∈α
    go (inr (inl e))   z z∈μ = subst (λ v → ⟨ z ∈ˢ v ⟩) e z∈μ
```

<!--en-->
The third case `α ∈ μ` contradicts minimality. The index naming `α` is good, and the membership `α ∈ μ` says that this index lies strictly below `m` in `w`. Thus only the first two trichotomy cases remain.
<!--zh-->
第三种情形 `α ∈ μ` 与最小性矛盾。指名 `α` 的索引是好的，而 `α ∈ μ` 表明这个索引在良序 `w` 中严格位于 `m` 之前。因此只剩三分法的前两种情形。
<!--ja-->
第三の場合 `α ∈ μ` は最小性に反する。`α` を名指すインデックスは良く、`α ∈ μ` はそのインデックスが `w` で `m` より真に小さいことを意味する。したがって三分法の最初の二つの場合だけが残る。
<!--/-->

```agda
    go (inr (inr α∈μ)) z z∈μ =
      ⊥₀-rec (snd (snd least) LC.self selfGood
        (transport (λ i → sym (LC.w-lt LC.self m) i)
          (subst (λ v → ⟨ v ∈ˢ fst μ ⟩) (sym LC.self-eq) α∈μ)))
```

<!--en-->
The inclusion `μ ⊆ α` codes an internal injection `μ ↪ α`. Together with `α ↪ μ`, ordinalhood and cardinality of `μ`, it completes the promised representative. Any argument about the size of an ordinal may now pass to this internal cardinal without leaving `L`.
<!--zh-->
包含 `μ ⊆ α` 编码出内部单射 `μ ↪ α`。连同 `α ↪ μ` 以及 `μ` 的序数性和基数性，这就完成了所承诺的代表。此后关于序数大小的论证可以在不离开 `L` 的前提下转到这个内部基数上。
<!--ja-->
包含 `μ ⊆ α` は内部単射 `μ ↪ α` を符号化する。`α ↪ μ`、`μ` の順序数性と基数性を合わせると、約束した代表が完成する。順序数の大きさに関する議論は、`L` を離れずにこの内部基数へ移せる。
<!--/-->

```agda

  μ↪α : InjL μ α
  μ↪α = inclusion-coded μ α μ⊆α
```

<!--en-->
The representative `μ` is an ordinal cardinal internally injectable into `α` and receiving an internal injection from `α`, and it lies inside `α`. This reduces cardinal arithmetic on arbitrary constructible ordinals to cardinal arithmetic on internal cardinals.
<!--zh-->
代表 `μ` 是一个序数基数；它可以内部单射到 `α`，`α` 也可以内部单射到它，并且包含于 `α`。由此，任意可构造序数上的基数算术都可以化归为内部基数上的基数算术。
<!--ja-->
代表 `μ` は順序数基数であり、`α` へ内部単射でき、`α` からも内部単射でき、`α` の中に含まれる。これにより、任意の構成可能順序数に関する基数算術を、内部基数に関する基数算術へ帰着できる。
<!--/-->
