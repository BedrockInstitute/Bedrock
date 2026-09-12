<!--en-->
# An ordinal L-cardinal above every L-cardinal

For an infinite cardinal of `L`, this chapter constructs a strictly larger cardinal that is also represented by an ordinal of `L`. The proof uses Hartogs' argument in the ambient cumulative hierarchy, turns the resulting ordinal into an element of `L`, and transfers cardinality back through the coded injections available inside `L`.
<!--zh-->
# 任意 L 基数之上的序数 L 基数

给定 `L` 中的一个无限基数，本章构造一个严格更大的基数，并让它由 `L` 中的序数表示。证明在环境累积层级中使用 Hartogs 论证，把所得序数变成 `L` 的元素，再通过 `L` 内部已有的编码注入把基数性质传回去。
<!--ja-->
# 任意の L 基数より大きい順序数 L 基数

`L` の無限基数が与えられたとき、本章ではそれより真に大きく、しかも `L` の順序数で表される基数を構成します。周囲の累積階層で Hartogs の議論を行い、得られた順序数を `L` の要素にし、`L` 内部の符号化された単射を通して基数性を移します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

One ordinal L-cardinal of L, above every L-cardinal.

`[LJ-1.526]` delivered `reduction : CardAboveL → SuccCardExists`
(agents/tasks/LJ-1-526/Probe526.agda:285-292).  `CardAboveL` is the
one input that reduction still wants.

Nothing is postulated.

```agda
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module L.CardinalAbove {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset→isL; isTransV; isPropIsTransV )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; boundingOrd )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; _↪_ )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.Mostowski {ℓ} using ( module Mostowski )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _∈ₛ_; extensionality; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; module SeparationSet; ⋃_ )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΣ )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded )
open import Cubical.Functions.Embedding
  using ( isEmbedding; injEmbedding; isEmbedding→hasPropFibers
        ; Embedding-into-isSet→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )
```

The ambient cardinal at `L.Cardinal`'s injection type, and the two
injection facts the Hartogs argument reads: injections compose, and
a member of an ordinal embeds into it.

```agda
IsCardinal : SV.S → Type (ℓ-suc ℓ)
IsCardinal κ = (δ : SV.S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

ord-emb : (a b : SV.S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
      ∙ cong (⟪ b ⟫↪) e
      ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)
```

<!--en-->
## The target statement

`CardAboveLᵀ`{.Agda} isolates the exact result: every infinite ordinal cardinal of `L` has a strictly larger ordinal cardinal in `L`.
<!--zh-->
## 目标陈述

`CardAboveLᵀ`{.Agda} 单独写出精确目标：`L` 中每个无限序数基数之上，都有一个严格更大的序数基数仍在 `L` 中。
<!--ja-->
## 目標となる主張

`CardAboveLᵀ`{.Agda} は正確な目標を切り出します。`L` の無限な順序数基数には、`L` に属する真に大きい順序数基数があります。
<!--/-->

The type, named apart so that the reductions can quantify over it.
THE OBLIGATION ITSELF IS THE TERM `CardAboveL` AT THE FOOT OF THIS
FILE, and this is its type.

```agda
CardAboveLᵀ : Type (ℓ-suc ℓ)
CardAboveLᵀ =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁
```

<!--en-->
## Ordinals as elements of L

Every ordinal belongs to the constructible stage immediately after itself, so it has a canonical representative in the carrier of `L`.
<!--zh-->
## 序数作为 L 的元素

每个序数都属于紧随自身之后的可构造层，因此在 `L` 的载体中有一个典范代表。
<!--ja-->
## L の要素としての順序数

各順序数は自分自身の直後の構成可能段階に属するので、`L` の台に正準な代表を持ちます。
<!--/-->

`[LJ-1.526]`'s report lists "the construction must produce an L-ELEMENT θ, so
whatever set is collected must be shown constructible" as one of the two things
it could not price (agents/tasks/LJ-1-526/lj-1.526-report.md,
`## What CardAboveL is`).

FOR AN ORDINAL THAT DEMAND IS FREE. `ord∈Lset-suc`
(src/L/Ordinal/Stages.lagda.md:434) puts an ordinal at the stage after itself,
and `Lset→isL` (src/L/Constructible.lagda.md:395) reads membership of a stage as
level-hood. The pair is already written inside `LeastCardInjL`
(src/L/Cardinal.lagda.md:70-74) for ONE ordinal; nothing in the tree names it
generally.

```agda
ordL : (x : SV.S) → IsOrd x → SL.S
ordL x ox = x , Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)
```

<!--en-->
## From ambient to internal cardinality

An injection coded inside `L` can be read as an ambient injection. Therefore an ambient cardinal remains a cardinal when viewed inside `L`.
<!--zh-->
## 从环境基数性到内部基数性

`L` 内部编码的注入可以读成环境注入。因此，环境中的基数在 `L` 内部看来仍是基数。
<!--ja-->
## 周囲の基数性から内部の基数性へ

`L` 内部で符号化された単射は、周囲の単射として読めます。したがって、周囲で基数である集合は `L` の内部でも基数です。
<!--/-->

`[LJ-1.526]` built it at agents/tasks/LJ-1-526/Probe526.agda:105-107; three
lines, so this file states its own rather than importing a 14 s module.

```agda
ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
ambient→internal κ c δ δ∈κ h =
  PT.rec Empty.isProp⊥ (λ w → c (fst δ) δ∈κ (readL κ δ w)) h
```

<!--en-->
## Separating smaller cardinals

For an ordinal `a`, separation collects the ordinals below a bound that inject into `a`. This set is the input to the Hartogs construction.
<!--zh-->
## 分出较小基数

对序数 `a`，收集在某个上界之下能够注入 `a` 的序数，构成一个集合。该集合将作为 Hartogs 构造的输入。
<!--ja-->
## より小さい基数を分出する

順序数 `a` に対し、ある上界より下で `a` に単射を持つ順序数を分出します。この集合を Hartogs の構成に用います。
<!--/-->

Fix an ordinal `a` and an ordinal `β`. Separate out of `β` the members that
inject into `a`. THE PREDICATE IS ALREADY SMALL: `⟪ x ⟫` and `⟪ a ⟫` both live
in `Type ℓ`, so the cubical library's `SeparationSet` takes it with no resizing
and no impredicativity parameter.

```agda
module Sep (a : SV.S) (β : SV.S) (oβ : IsOrd β) where

  ϕ : SV.S → hProp ℓ
  ϕ x = ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ , squash₁

  open SeparationSet β ϕ using ( SEPAREE; separation-ax )

  θ : SV.S
  θ = SEPAREE

  θ-in : (x : SV.S) → ⟨ x ∈ˢ β ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ → ⟨ x ∈ˢ θ ⟩
  θ-in x x∈β h =
    ∈∈ₛ {a = x} {b = θ} .snd
      (separation-ax x .snd (∈∈ₛ {a = x} {b = β} .fst x∈β , h))

  θ⊆β : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ⟨ x ∈ˢ β ⟩
  θ⊆β x x∈θ =
    ∈∈ₛ {a = x} {b = β} .snd
      (separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .fst)

  θ-inj : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁
  θ-inj x x∈θ = separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .snd
```

`θ` IS AN ORDINAL. Its members are members of `β`, so they are transitive; and
it is transitive itself because a member of a member of `θ` embeds into that
member (`ord-emb`) and so into `a` (`comp-inj`), both above.

```agda
  θ-ord : IsOrd θ
  θ-ord = trans , (λ x x∈θ → oβ .snd x (θ⊆β x x∈θ))
    where
    trans : isTransV θ
    trans {x} {y} y∈x x∈θ =
      θ-in y (oβ .fst y∈x (θ⊆β x x∈θ))
        (PT.map
          (comp-inj (ord-emb y x (mem-ord {A = β} oβ x (θ⊆β x x∈θ)) y∈x))
          (θ-inj x x∈θ))
```

`a ∈ θ`, as soon as `a` is inside the ambient bound.

```agda
  a∈θ : ⟨ a ∈ˢ β ⟩ → ⟨ a ∈ˢ θ ⟩
  a∈θ a∈β = θ-in a a∈β ∣ (λ m → m) , (λ m n e → e) ∣₁
```

THE CARDINAL CLAUSE, and it is the one place the bound is spent. If `θ` is
itself a member of `β`, then an injection of `θ` into one of its own members
would put `θ` into `θ`.

```agda
  θ-card : ⟨ θ ∈ˢ β ⟩ → IsCardinal θ
  θ-card θ∈β δ δ∈θ f =
    ∈-irrefl θ (θ-in θ θ∈β (PT.map (comp-inj f) (θ-inj δ δ∈θ)))
```

AND THE BOUND IS SPENT BY ONE WITNESS: any member of `β` that does NOT inject
into `a` forces `θ ∈ β` through trichotomy.

```agda
  θ∈β : (γ : SV.S) → ⟨ γ ∈ˢ β ⟩ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ θ ∈ˢ β ⟩
  θ∈β γ γ∈β noinj = go (ord-tri θ θ-ord β oβ)
    where
    go : Tri θ β → ⟨ θ ∈ˢ β ⟩
    go (inl θ∈β')      = θ∈β'
    go (inr (inl e))   =
      Empty.rec (PT.rec Empty.isProp⊥ noinj
        (θ-inj γ (subst (λ v → ⟨ γ ∈ˢ v ⟩) (sym e) γ∈β)))
    go (inr (inr β∈θ)) = Empty.rec (∈-irrefl β (θ⊆β β β∈θ))
```

<!--en-->
## Reducing to an ambient bound

Once an ambient cardinal above the given one is available, its ordinal representative supplies the required member of `L`; the remaining work is the ambient existence theorem.
<!--zh-->
## 归结为环境上界

一旦得到高于给定基数的环境基数，其序数代表就给出所需的 `L` 元素；余下工作是证明环境中的存在定理。
<!--ja-->
## 周囲の上界へ帰着する

与えられた基数より大きい周囲の基数が得られれば、その順序数代表が必要な `L` の要素になります。残る課題は周囲での存在定理です。
<!--/-->

`NoInjOrd` carries NO constructibility, NO code, NO cardinal predicate and NO
leastness: for every ordinal, some ordinal does not inject into it. That is the
Hartogs fact in its weakest form.

```agda
NoInjOrd : Type (ℓ-suc ℓ)
NoInjOrd = (x : SV.S) → IsOrd x
         → ∥ Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ x ⟫ → Empty.⊥)) ∥₁
```

An ordinal that does not inject into `a` is automatically ABOVE `a`:
the other two legs of trichotomy each hand back an injection.

```agda
above : (a γ : SV.S) → IsOrd a → IsOrd γ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ a ∈ˢ γ ⟩
above a γ oa oγ noinj = go (ord-tri γ oγ a oa)
  where
  idInj : ⟪ γ ⟫ ↪ ⟪ γ ⟫
  idInj = (λ m → m) , (λ m n e → e)
  go : Tri γ a → ⟨ a ∈ˢ γ ⟩
  go (inl γ∈a)      = Empty.rec (noinj (ord-emb γ a oa γ∈a))
  go (inr (inl e))  =
    Empty.rec (noinj (subst (λ v → ⟪ γ ⟫ ↪ ⟪ v ⟫) e idInj))
  go (inr (inr a∈γ)) = a∈γ
```

The ambient half at one ordinal, untruncated. This is the whole construction;
everything after it is plumbing.

```agda
cardAboveAt : (a : SV.S) → IsOrd a
  → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))
  → Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
cardAboveAt a oa (γ , oγ , noinj) =
  S.θ , S.θ-ord , S.θ-card θ∈sγ , S.a∈θ a∈sγ
  where
  module S = Sep a (sucV γ) (suc-ord oγ)
  γ∈sγ : ⟨ γ ∈ˢ sucV γ ⟩
  γ∈sγ = self∈sucV γ
  a∈sγ : ⟨ a ∈ˢ sucV γ ⟩
  a∈sγ = suc-ord oγ .fst (above a γ oa oγ noinj) γ∈sγ
  θ∈sγ : ⟨ S.θ ∈ˢ sucV γ ⟩
  θ∈sγ = S.θ∈β γ γ∈sγ noinj

ambientCardAbove : NoInjOrd → (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁
ambientCardAbove ni a oa = PT.map (cardAboveAt a oa) (ni a oa)
```

The whole obligation, given `NoInjOrd`. Green, no holes.

NEITHER `IsCardinalL κ` NOR `κ ∉ ω` IS CONSUMED.  Both hypotheses of
`CardAboveL` are dead on this route, and the report says so.

```agda
noInjOrd→CardAboveLᵀ : NoInjOrd → CardAboveLᵀ
noInjOrd→CardAboveLᵀ ni κ oκ cκ κ∉ω =
  PT.map build (ambientCardAbove ni (fst κ) oκ)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩)
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , κ∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , κ∈θ
```

<!--en-->
## The Hartogs ordinal

Hartogs' construction produces an ordinal that cannot inject into the given set. It uses well-founded collapse rather than assuming a pre-existing order type.
<!--zh-->
## Hartogs 序数

Hartogs 构造产生一个不能注入给定集合的序数。这里使用良基坍缩，而不预设已有的序型。
<!--ja-->
## Hartogs 順序数

Hartogs の構成は、与えられた集合へ単射を持たない順序数を作ります。既存の順序型を仮定せず、整礎な崩壊を使います。
<!--/-->

`[LJ-1.94]` built the ambient Hartogs at ω in 1058 lines
(archive/dev/LJ-dispatch-index.md:170) through order types: the collapse of a
well-order, its uniqueness under isomorphism, and initial segments. NONE OF THAT
IS NEEDED HERE, and the reason is section 6's contradiction shape.

The classical construction wants `ot w ≡ μ`, which forces
uniqueness-under-isomorphism. THIS ONE WANTS ONLY `μ ⊆ ot w`, because
`ot w ∈ μ` already holds by construction and the two together give
`ot w ∈ ot w`. A subset claim needs no order isomorphism, so trichotomy, initial
segments and the uniqueness theorem all drop out, and the relation may be an
arbitrary TRANSITIVE WELL-FOUNDED one rather than a well-order.

THE INDEX IS `Bool`-VALUED AND SO IT IS ALREADY SMALL.
`⟪ a ⟫ → ⟪ a ⟫ → Bool` lives in `Type ℓ`, so this file needs no small classifier
`Ω'`, no `HPropSmallness` and no `Impredicativity` parameter. `[LJ-1.94]` paid
for that classifier (agents/tasks/LJ-1-94/ProbeLJ194A.agda:29); this does not.

```agda
module Hartogs (a : SV.S) where

  Rel : Type ℓ
  Rel = ⟪ a ⟫ → ⟪ a ⟫ → Bool

  Holds : Rel → ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ-zero
  Holds R x y = R x y ≡ true
```

A transitive well-founded relation on `⟪ a ⟫`. NOT a well-order: no trichotomy,
no irreflexivity clause.

```agda
  WFR : Type ℓ
  WFR = Σ[ R ∈ Rel ]
          ( ({x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z)
          × WellFounded (λ x y → Holds R x y) )

  module Col (w : WFR) where

    R : Rel
    R = fst w
```

Lifted to `Type ℓ`, the level the shared collapse indexes at.

```agda
    _≺_ : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ
    x ≺ y = Lift (Holds R x y)

    ≺-trans : {x y z : ⟪ a ⟫} → x ≺ y → y ≺ z → x ≺ z
    ≺-trans p q = lift (fst (snd w) (lower p) (lower q))

    ≺-wf : WellFounded _≺_
    ≺-wf x = go x (snd (snd w) x)
      where
      go : (y : ⟪ a ⟫) → Acc (λ u v → Holds R u v) y → Acc _≺_ y
      go y (acc h) = acc (λ z k → go z (h z (lower k)))

    open Mostowski ⟪ a ⟫ _≺_ ≺-wf ≺-trans public
      using ( col; col-eq; col-in; col-out; col-ord )
```

The order type, as a bare image. No union, no successor.

```agda
    ot : SV.S
    ot = sett ⟪ a ⟫ col

    ot-in : (p : ⟪ a ⟫) → ⟨ col p ∈ˢ ot ⟩
    ot-in p = ∣ p , refl ∣₁

    ot-ord : IsOrd ot
    ot-ord = tr , mem
      where
      mem : (x : SV.S) → ⟨ x ∈ˢ ot ⟩ → isTransV x
      mem x x∈ = PT.rec (isPropIsTransV x)
        (λ z → subst isTransV (snd z) (col-ord (fst z) .fst)) x∈
      tr : isTransV ot
      tr {x} {y} y∈x x∈ot = PT.rec (snd (y ∈ˢ ot)) outer x∈ot
        where
        outer : Σ[ p ∈ ⟪ a ⟫ ] (col p ≡ x) → ⟨ y ∈ˢ ot ⟩
        outer (p , e) =
          PT.rec (snd (y ∈ˢ ot))
            (λ z → subst (λ v → ⟨ v ∈ˢ ot ⟩) (snd (snd z)) (ot-in (fst z)))
            (col-out p y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))
```

THE CANDIDATE: the sup of every order type this family reaches.

```agda
  μ : SV.S
  μ = ⋃ (sett WFR (λ w → sucV (Col.ot w)))

  μ-ord : IsOrd μ
  μ-ord = boundingOrd WFR Col.ot Col.ot-ord .snd .fst

  ot∈μ : (w : WFR) → ⟨ Col.ot w ∈ˢ μ ⟩
  ot∈μ = boundingOrd WFR Col.ot Col.ot-ord .snd .snd

```

`⟪ x ⟫` is an h-set: it embeds into `V ℓ`, which is one.

```agda
  isSet⟪⟫ : (x : SV.S) → isSet ⟪ x ⟫
  isSet⟪⟫ x = Embedding-into-isSet→isSet (⟪ x ⟫↪ , isEmb⟪ x ⟫↪) setIsSet

  decB : {A : Type ℓ} → (A ⊎ (A → Empty.⊥)) → Bool
  decB (inl _) = true
  decB (inr _) = false

  lemℓ : LEM ℓ
  lemℓ = lowerLEM lem
```

Suppose `μ` DID inject into `a`. Pull the membership order on `⟪ μ ⟫` back along
the injection, and the pullback is one of the relations `μ` was built from.

```agda
  module NoInj (f : ⟪ μ ⟫ ↪ ⟪ a ⟫) where

    F : ⟪ μ ⟫ → ⟪ a ⟫
    F = fst f

    F-emb : isEmbedding F
    F-emb = injEmbedding (isSet⟪⟫ a) (λ {x} {y} e → snd f x y e)

    Fib : ⟪ a ⟫ → Type ℓ
    Fib x = Σ[ m ∈ ⟪ μ ⟫ ] (F m ≡ x)

    isPropFib : (x : ⟪ a ⟫) → isProp (Fib x)
    isPropFib = isEmbedding→hasPropFibers F-emb

    PreT : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ
    PreT x y = Σ[ p ∈ Fib x ] Σ[ q ∈ Fib y ]
                 ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q) ⟩

    isPropPreT : (x y : ⟪ a ⟫) → isProp (PreT x y)
    isPropPreT x y = isPropΣ (isPropFib x) λ p →
                     isPropΣ (isPropFib y) λ q →
                       snd (⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q))

    R : Rel
    R x y = decB (lemℓ (PreT x y , isPropPreT x y))

    R→Pre : (x y : ⟪ a ⟫) → Holds R x y → PreT x y
    R→Pre x y e = go (lemℓ (PreT x y , isPropPreT x y)) e
      where
      go : (d : PreT x y ⊎ (PreT x y → Empty.⊥)) → decB d ≡ true → PreT x y
      go (inl h) _  = h
      go (inr _) e' = Empty.rec (false≢true e')

    Pre→R : (x y : ⟪ a ⟫) → PreT x y → Holds R x y
    Pre→R x y h = go (lemℓ (PreT x y , isPropPreT x y))
      where
      go : (d : PreT x y ⊎ (PreT x y → Empty.⊥)) → decB d ≡ true
      go (inl _) = refl
      go (inr n) = Empty.rec (n h)
```

Transitivity comes from the members of `μ` being transitive sets.

```agda
    R-trans : {x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z
    R-trans {x} {y} {z} e1 e2 = Pre→R x z (p , r , goal)
      where
      d1 : PreT x y
      d1 = R→Pre x y e1
      d2 : PreT y z
      d2 = R→Pre y z e2
      p  = fst d1
      q  = fst (snd d1)
      q' = fst d2
      r  = fst (snd d2)
      h1' : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q') ⟩
      h1' = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
              (isPropFib y q q') (snd (snd d1))
      rTr : isTransV (⟪ μ ⟫↪ (fst r))
      rTr = μ-ord .snd (⟪ μ ⟫↪ (fst r)) (member μ (fst r))
      goal : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst r) ⟩
      goal = ∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst r)} .fst
        (rTr (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst q')} .snd h1')
             (∈∈ₛ {a = ⟪ μ ⟫↪ (fst q')} {b = ⟪ μ ⟫↪ (fst r)} .snd (snd (snd d2))))
```

Well-foundedness is regularity, transported along the injection. A point outside
the image has no predecessor at all.

```agda
    wfAux : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
          → Acc (λ x y → Holds R x y) (F m)
    wfAux v (acc rec) m e = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r (F m) → Acc (λ x y → Holds R x y) r
      go r rr = subst (Acc (λ x y → Holds R x y)) (snd p)
                  (wfAux (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below)
                     (fst p) refl)
        where
        d : PreT r (F m)
        d = R→Pre r (F m) rr
        p = fst d
        q = fst (snd d)
        h : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
        h = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
              (isPropFib (F m) q (m , refl)) (snd (snd d))
        below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                  (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd h)

    R-wf : WellFounded (λ x y → Holds R x y)
    R-wf x = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r x → Acc (λ u v → Holds R u v) r
      go r rr = subst (Acc (λ u v → Holds R u v)) (snd p)
                  (wfAux (⟪ μ ⟫↪ (fst p)) (regularityV (⟪ μ ⟫↪ (fst p)))
                     (fst p) refl)
        where
        p = fst (R→Pre r x rr)

    w : WFR
    w = R , R-trans , R-wf

    open Col w using ( col; col-in; col-out; ot; ot-in; _≺_ )
```

THE ONE INDUCTION. The collapse of the pullback REPRODUCES the members of `μ`.
This is where `[LJ-1.94]` needed the order type of an ordinal's own membership
order plus uniqueness under isomorphism; here it is one `∈`-induction, because
the target is a set equality proved by extensionality and not an order iso.

```agda
    key : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
        → col (F m) ≡ ⟪ μ ⟫↪ m
    key v (acc rec) m e =
      extensionality (col (F m)) (⟪ μ ⟫↪ m) (fwd , bwd)
      where
      fwd : (b : SV.S) → ⟨ b ∈ₛ col (F m) ⟩ → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
      fwd b b∈ = PT.rec (snd (b ∈ₛ ⟪ μ ⟫↪ m)) go
                   (col-out (F m) b (∈∈ₛ {a = b} {b = col (F m)} .snd b∈))
        where
        go : Σ[ r ∈ ⟪ a ⟫ ] ((r ≺ F m) × (col r ≡ b))
           → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
        go (r , rr , cr) = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (cpr ∙ cr) hh
          where
          d = R→Pre r (F m) (lower rr)
          p = fst d
          q = fst (snd d)
          hh : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
          hh = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
                 (isPropFib (F m) q (m , refl)) (snd (snd d))
          below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
          below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                    (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd hh)
          ih : col (F (fst p)) ≡ ⟪ μ ⟫↪ (fst p)
          ih = key (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below) (fst p) refl
          cpr : ⟪ μ ⟫↪ (fst p) ≡ col r
          cpr = sym ih ∙ cong col (snd p)

      bwd : (b : SV.S) → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩ → ⟨ b ∈ₛ col (F m) ⟩
      bwd b b∈ = ∈∈ₛ {a = b} {b = col (F m)} .fst
                   (subst (λ t → ⟨ t ∈ˢ col (F m) ⟩) (ihk ∙ ek) inCol)
        where
        b∈ˢ : ⟨ b ∈ˢ ⟪ μ ⟫↪ m ⟩
        b∈ˢ = ∈∈ₛ {a = b} {b = ⟪ μ ⟫↪ m} .snd b∈
        b∈μ : ⟨ b ∈ˢ μ ⟩
        b∈μ = μ-ord .fst b∈ˢ (member μ m)
        fb = fiber μ b∈μ
        k = fst fb
        ek : ⟪ μ ⟫↪ k ≡ b
        ek = snd fb
        k∈m : ⟨ ⟪ μ ⟫↪ k ∈ₛ ⟪ μ ⟫↪ m ⟩
        k∈m = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (sym ek) b∈
        pre : PreT (F k) (F m)
        pre = (k , refl) , ((m , refl) , k∈m)
        inCol : ⟨ col (F k) ∈ˢ col (F m) ⟩
        inCol = col-in (F m) (F k) (lift (Pre→R (F k) (F m) pre))
        below : ⟪ μ ⟫↪ k SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ k ∈ˢ t ⟩) e
                  (∈∈ₛ {a = ⟪ μ ⟫↪ k} {b = ⟪ μ ⟫↪ m} .snd k∈m)
        ihk : col (F k) ≡ ⟪ μ ⟫↪ k
        ihk = key (⟪ μ ⟫↪ k) (rec (⟪ μ ⟫↪ k) below) k refl

    key' : (m : ⟪ μ ⟫) → col (F m) ≡ ⟪ μ ⟫↪ m
    key' m = key (⟪ μ ⟫↪ m) (regularityV (⟪ μ ⟫↪ m)) m refl
```

`μ ⊆ ot w`. THE SUBSET IS ALL THE ARGUMENT NEEDS. Nothing here claims `ot w ≡
μ`, and that is why no uniqueness theorem appears in this file.

```agda
    μ⊆ot : (b : SV.S) → ⟨ b ∈ˢ μ ⟩ → ⟨ b ∈ˢ ot ⟩
    μ⊆ot b b∈μ =
      subst (λ t → ⟨ t ∈ˢ ot ⟩) (key' (fst fb) ∙ snd fb)
        (ot-in (F (fst fb)))
      where
      fb = fiber μ b∈μ
```

`ot w ∈ μ` by construction, `μ ⊆ ot w` by the induction.

```agda
    absurd : Empty.⊥
    absurd = ∈-irrefl ot (μ⊆ot ot (ot∈μ w))
```

THE HARTOGS FACT AT `a`.

```agda
  noInj : (⟪ μ ⟫ ↪ ⟪ a ⟫) → Empty.⊥
  noInj f = NoInj.absurd f
```

<!--en-->
## The larger L-cardinal

The least cardinal at or above the Hartogs ordinal is strictly above the original cardinal. Converting it to an element of `L` completes `CardAboveL`.
<!--zh-->
## 所得的更大 L 基数

Hartogs 序数之上最小的基数严格大于原基数。把它变成 `L` 的元素便完成 `CardAboveL`。
<!--ja-->
## 得られた大きい L 基数

Hartogs 順序数以上の最小の基数は、元の基数より真に大きくなります。それを `L` の要素に変換して `CardAboveL` を完成します。
<!--/-->

```agda
noInjOrd : NoInjOrd
noInjOrd x ox = ∣ Hartogs.μ x , Hartogs.μ-ord x , Hartogs.noInj x ∣₁
```

The obligation, at `[LJ-1.526]`'s own type. Green, no holes, no postulate, no
choice.

```agda
CardAboveL : CardAboveLᵀ
CardAboveL = noInjOrd→CardAboveLᵀ noInjOrd
```
