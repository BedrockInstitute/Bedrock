<!--en-->
# Choosing a cardinal representative for an ordinal

Counting inside `L` is expressed in terms of cardinals, while a construction often produces an arbitrary ordinal. For an ordinal `α` of `L`, this chapter finds an internal cardinal `μ` contained in `α`, together with internal injections in both directions. Thus `μ` represents the cardinality of `α` inside the model. The representative is obtained by searching the successor of `α` for the least ordinal into which `α` internally injects.
<!--zh-->
# 为序数选取基数代表

`L` 内部的计数以基数表述，而具体构造往往只产生任意序数。对 `L` 中的序数 `α`，本章找出包含于 `α` 的内部基数 `μ`，并给出两个方向的内部单射。因此，`μ` 在模型内部代表 `α` 的基数。构造在 `α` 的后继中搜索，选取 `α` 能够内部单射到的最小序数。
<!--ja-->
# 順序数の基数代表を選ぶ

`L` の内部での計数は基数によって述べますが、具体的な構成が与えるのは任意の順序数であることが少なくありません。`L` の順序数 `α` に対し、本章では `α` に含まれる内部基数 `μ` と、両方向の内部単射を構成します。したがって `μ` はモデルの内部で `α` の濃度を代表します。この代表は、`α` の後続の中から、`α` が内部単射する最小の順序数を探して得られます。
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
レベル `ℓ-suc ℓ` における排中律を仮定します。この仮定は整列順序上の探索と順序数の三分法で使われます。結論の単射はすべて `L` の内部にあり、そのグラフは外部関数ではなく構成可能集合です。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
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
ここでは二つの構造を使います。周囲の階層は所属関係と探索に用いる小さな表示を与え、構成可能構造は順序数、基数、内部単射の述語を与えます。構成可能性は所属に沿って下方へ伝わるので、周囲の階層で見つけた要素を `L` の論域へ戻せます。
<!--/-->

```agda
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( InjL; IsCardinalL; module LeastCardInjL )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( IsLeast; leastOf; module SWO )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )

```

<!--en-->
The search rests on the well-order of the indices presenting an ordinal. Its order agrees with membership between the represented elements. Inclusion coding turns containment into an internal injection, and transitivity composes successive internal injections.
<!--zh-->
搜索建立在呈现序数的索引良序之上；这个次序与所指元素之间的成员关系一致。包含关系的编码把包含化为内部单射，单射的传递性则复合连续的内部单射。
<!--ja-->
探索は、順序数を表示するインデックスの整列順序に基づきます。この順序は、表示される要素の間の所属と一致します。包含の符号化が包含を内部単射に変え、単射の推移性が内部単射を合成します。
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
候補集合は後続 `sucV α` です。命題的切り詰めは、外部で代表を選ぶことなく適切な代表の存在を表します。和型と空型は後の三分法の議論で使われます。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

```

<!--en-->
Write `SV.S` for ambient sets and `SL.S` for constructible sets. An element of `SL.S` pairs an ambient set with its constructibility certificate. Membership comparisons occur on first components, whereas `InjL` and `IsCardinalL` concern the complete constructible elements.
<!--zh-->
以 `SV.S` 表示外围集合，以 `SL.S` 表示可构造集合。`SL.S` 的元素由外围集合及其可构造性证书组成。成员关系比较作用于第一分量，而 `InjL` 与 `IsCardinalL` 以完整的可构造元素为对象。
<!--ja-->
周囲の集合を `SV.S`、構成可能集合を `SL.S` と書きます。`SL.S` の要素は周囲の集合と構成可能性の証明の対です。所属の比較は第一成分について行い、`InjL` と `IsCardinalL` は完全な構成可能要素について述べます。
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
順序数 `α` に対し、定理は五つの性質を持つ `μ` が単に存在することを述べます。`μ` は順序数かつ内部基数で、`μ ⊆ α` であり、内部単射 `α ↪ μ` と `μ ↪ α` があります。切り詰めにより結論全体は命題になります。
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
最終的な証人は、代表 `μ` と以下で構成する五つの証明からなります。目標は切り詰められているので、成分がそろえばこの一つの依存対を入れることで定理が閉じます。
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
`α` に対する補助的な探索の準備は、後続の構成可能性、`α` 自身を名指すインデックスとその等式、表示インデックス上の整列順序 `w` を与えます。`w` の順序関係は、名指された順序数の間の所属です。
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
`T` を、順序数 `α` の基礎集合の後続とします。後続も順序数なので、`T` の各要素は順序数であり、探索の全体で所属から得られる順序を使えます。
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
集合 `T` は構成可能です。この証明が必要なのは、探索インデックスが最初に名指すのは `T` の周囲の要素にすぎず、構成可能性の下方閉性によって初めてその要素を `SL.S` の要素にできるからです。
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
`T` の表示インデックス `b` に対し、`upL b` は名指された要素とその構成可能性の証明を対にします。後者は、その要素が `T` に属することと `T` の構成可能性から従います。
<!--/-->

```agda
  upL : ⟪ T ⟫ → SL.S
  upL b = ⟪ T ⟫↪ b , isL-trans (member T b) hT
  Good : ⟪ T ⟫ → hProp (ℓ-suc ℓ)
  Good b = ∥ Σ[ δ ∈ SL.S ] ((fst δ ≡ ⟪ T ⟫↪ b) × InjL α δ) ∥₁ , squash₁
```

<!--en-->
Call an index `b` good when the member it names is the underlying set of some constructible `δ` and there is an internal injection `α ↪ δ`. The equality in `Good b` connects the indexed presentation with the constructible witness; truncation keeps goodness proposition-valued.
<!--zh-->
若索引 `b` 所指的成员是某个可构造集合 `δ` 的底层集合，并且存在内部单射 `α ↪ δ`，就称 `b` 为好索引。`Good b` 中的等式连接索引呈现与可构造见证，截断则使好索引性取值于命题。
<!--ja-->
インデックス `b` が名指す要素が、ある構成可能集合 `δ` の基礎集合であり、内部単射 `α ↪ δ` があるとき、`b` を良いインデックスと呼びます。`Good b` の等式はインデックス表示と構成可能な証人を結び、切り詰めは良さを命題値にします。
<!--/-->

```agda
  selfGood : ⟨ Good LC.self ⟩
  selfGood = ∣ α , sym LC.self-eq , inclusion-coded α α (λ z z∈α → z∈α) ∣₁

  nonempty : ∥ Σ[ b ∈ ⟪ T ⟫ ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ LC.self , selfGood ∣₁
```

<!--en-->
The index naming `α` is good: its represented member equals `α`, and the identity inclusion codes an internal injection from `α` to itself. Hence the type of good indices is merely inhabited.
<!--zh-->
指名 `α` 的索引是好的：它所指成员等于 `α`，恒等包含则编码出从 `α` 到自身的内部单射。因此，好索引的类型仅仅非空。
<!--ja-->
`α` を名指すインデックスは良いものです。名指された要素は `α` に等しく、恒等的な包含が `α` から自身への内部単射を符号化します。したがって良いインデックスの型には単に要素が存在します。
<!--/-->

```agda

  least : Σ[ b ∈ ⟪ T ⟫ ] IsLeast LC.w Good b
  least = leastOf LC.w lem Good nonempty

  m : ⟪ T ⟫
  m = fst least
```

<!--en-->
Apply least-element search to the well-order `w` and the proposition-valued predicate `Good`. Excluded middle decides goodness, and nonemptiness guarantees a least good index. Denote that index by `m`.
<!--zh-->
对良序 `w` 与命题值谓词 `Good` 应用最小元搜索。排中律判定好索引性，非空性保证存在最小的好索引；把它记作 `m`。
<!--ja-->
整列順序 `w` と命題値の述語 `Good` に最小元探索を適用します。排中律が良さを判定し、非空性が最小の良いインデックスを保証します。そのインデックスを `m` と書きます。
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
選んだインデックス `m` を構成可能な論域へ持ち上げ、その結果を `μ` と呼びます。定義により、`μ` の基礎集合は `m` が `T` の中で名指す要素です。
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
表示の定理から `μ ∈ T` が得られます。`T` は順序数なので、その各要素も順序数です。したがって `μ` は必要な順序数性を持ちます。
<!--/-->

```agda
  α↪μ : InjL α μ
  α↪μ = PT.rec squash₁ from (fst (snd least))
    where
    from : Σ[ δ ∈ SL.S ] ((fst δ ≡ ⟪ T ⟫↪ m) × InjL α δ) → InjL α μ
```

<!--en-->
Goodness of the least index supplies, under truncation, a constructible `δ`, an equality between its underlying set and the member named by `m`, and an injection `α ↪ δ`. The goal `InjL α μ` is a proposition, so the truncated witness may be eliminated into it.
<!--zh-->
最小索引的好索引性在截断之下给出可构造集合 `δ`、其底层集合与 `m` 所指成员之间的等式，以及单射 `α ↪ δ`。目标 `InjL α μ` 是命题，所以可以把截断见证消去到这个目标中。
<!--ja-->
最小インデックスの良さは、切り詰めの下で、構成可能集合 `δ`、その基礎集合と `m` が名指す要素との等式、単射 `α ↪ δ` を与えます。目標 `InjL α μ` は命題なので、切り詰められた証人をそこへ消去できます。
<!--/-->

```agda
    from (δ , e , α↪δ) =
      injl-trans α δ μ α↪δ
        (inclusion-coded δ μ (λ z z∈δ → subst (λ v → ⟨ z ∈ˢ v ⟩) e z∈δ))
```

<!--en-->
Transport along the indexed equality shows that `δ` is included in `μ`; inclusion coding turns this into an internal injection `δ ↪ μ`. Composing it with the supplied `α ↪ δ` proves `α ↪ μ`.
<!--zh-->
沿索引等式搬运可知 `δ` 包含于 `μ`；包含关系的编码把它化为内部单射 `δ ↪ μ`。再与已有的 `α ↪ δ` 复合，便得到 `α ↪ μ`。
<!--ja-->
インデックスの等式に沿って移送すると `δ` が `μ` に含まれることが分かり、包含の符号化により内部単射 `δ ↪ μ` を得ます。これを与えられた `α ↪ δ` と合成して `α ↪ μ` を証明します。
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
`μ` が基数であることを示すため、ある要素 `δ ∈ μ` に内部単射 `μ ↪ δ` があると仮定します。順序数 `T` の推移性から `δ ∈ T` となり、`T` の表示が `δ` を名指すインデックス `b` を与えます。
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
ファイバーの定理は、インデックス `b` と、その表示要素を `δ` と同一視する等式を与えます。このデータにより、所属と単射の主張を、インデックスで表された要素と構成可能要素 `δ` の間で移送できます。
<!--/-->

```agda
    bδ = fiber T δ∈T .snd
    bGood : ⟨ Good b ⟩
    bGood = ∣ δ , sym bδ , injl-trans α μ δ α↪μ μ↪δ ∣₁
```

<!--en-->
The index `b` is good: compose `α ↪ μ` with the assumed `μ ↪ δ`, and use the fibre equality to match the indexed member. Thus `b` is another candidate in the same search.
<!--zh-->
索引 `b` 是好的：把 `α ↪ μ` 与假设的 `μ ↪ δ` 复合，再用纤维等式匹配索引所指的成员。于是 `b` 是同一次搜索中的另一个候选。
<!--ja-->
インデックス `b` は良いものです。`α ↪ μ` と仮定した `μ ↪ δ` を合成し、ファイバーの等式でインデックスの表示要素に合わせます。したがって `b` は同じ探索の別の候補です。
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
さらに `b < m` です。`w` の関係は表示された順序数の間の所属であり、仮定 `δ ∈ μ` を移送すると、まさにこの比較が得られます。最小の良いインデックスより下に良いインデックスがあることは不可能なので、そのような単射 `μ ↪ δ` は存在しません。したがって `μ` は内部基数です。
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
残るのは `μ ⊆ α` です。順序数の三分法で二つの基礎順序数を比較します。`μ ∈ α` なら `α` の推移性から包含が従い、`μ = α` なら等式に沿う移送で得られます。
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
第三の場合 `α ∈ μ` は最小性に反します。`α` を名指すインデックスは良く、`α ∈ μ` はそのインデックスが `w` で `m` より真に小さいことを意味します。したがって三分法の最初の二つの場合だけが残ります。
<!--/-->

```agda
    go (inr (inr α∈μ)) z z∈μ =
      Empty.rec (snd (snd least) LC.self selfGood
        (transport (λ i → sym (LC.w-lt LC.self m) i)
          (subst (λ v → ⟨ v ∈ˢ fst μ ⟩) (sym LC.self-eq) α∈μ)))
```

<!--en-->
The inclusion `μ ⊆ α` codes an internal injection `μ ↪ α`. Together with `α ↪ μ`, ordinalhood and cardinality of `μ`, it completes the promised representative. Any argument about the size of an ordinal may now pass to this internal cardinal without leaving `L`.
<!--zh-->
包含 `μ ⊆ α` 编码出内部单射 `μ ↪ α`。连同 `α ↪ μ` 以及 `μ` 的序数性和基数性，这就完成了所承诺的代表。此后关于序数大小的论证可以在不离开 `L` 的前提下转到这个内部基数上。
<!--ja-->
包含 `μ ⊆ α` は内部単射 `μ ↪ α` を符号化します。`α ↪ μ`、`μ` の順序数性と基数性を合わせると、約束した代表が完成します。順序数の大きさに関する議論は、`L` を離れずにこの内部基数へ移せます。
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
代表 `μ` は順序数基数であり、`α` へ内部単射でき、`α` からも内部単射でき、`α` の中に含まれます。これにより、任意の構成可能順序数に関する基数算術を、内部基数に関する基数算術へ帰着できます。
<!--/-->
