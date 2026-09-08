<!--en-->
# Assembling GCH from four internal bounds

The final cardinal comparison becomes transparent once four facts inside `L` are available. This chapter states those facts, shows how they locate every subset of a cardinal below its successor, and derives GCH from them.
<!--zh-->
# 从四条内部界装配 GCH

一旦在 `L` 内部取得四条事实，最终的基数比较便清晰可见。本章陈述这些事实，说明它们如何把基数的每个子集定位到其后继以下，并由此推出 GCH。
<!--ja-->
# 四つの内部上界から GCH を組み立てる

`L` の内部で四つの事実が得られれば、最後の基数比較は明快になる。本章ではそれらを述べ、基数の各部分集合がその後続基数より下に現れることを示し、そこから GCH を導く。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Assembly {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.Axioms.Basic {ℓ} using ( isL-Lset )
open import L.Cardinal {ℓ} lem
  using ( InjL; SuccCardL; IsCardinalL; module LeastCardInjL )
open import L.CardinalAbove {ℓ} lem using ( CardAboveL )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: `Lset` and the ambient membership live here.

```agda
module SV = hPropStructure 𝒮ᵥ
```

The L-carrier: `GCHStatement` lives here.

```agda
module SL = hPropStructure 𝒮ʟ
```

The instance src/L/GCH.lagda.md names, at the same 𝒮ʟ.

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
```

<!--en-->
## Four internal estimates

The assembly starts from four estimates stated wholly inside `L`: stages can be counted, subsets are bounded, successor cardinals reach power sets, and larger cardinals exist.
<!--zh-->
## 四条内部估计

装配从四条完全在 `L` 内部陈述的估计开始：阶段可以计数，子集受到约束，后继基数可以到达幂集，并且更大的基数存在。
<!--ja-->
## 四つの内部評価

組み立ては、すべて `L` の内部で述べられる四つの評価から始まる。段階を数えられること、部分集合が有界であること、後続基数から冪集合へ到達できること、そしてより大きな基数が存在することである。
<!--/-->

1.  The stage at an INFINITE ordinal δ is coded into δ.  The row is
    false at finite δ, so the infinity premise is part of the type.

```agda
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
  → fst Lδ ≡ Lset (fst δ) → InjL Lδ δ
```

2.  The bounded subset theorem, internally: a subset y of an infinite
    L-cardinal κ appears at a stage whose index injects into κ.

```agda
InternalBoundedSubset : Type (ℓ-suc ℓ)
InternalBoundedSubset =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (y : SL.S) → ((z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩)
  → ∥ Σ[ β ∈ SL.S ]
       (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ) ∥₁
```

3.  The successor cardinal injects into the power set, GIVEN the
    injection section 5 pays out of hypotheses 1 and 2.  The extra
    premise is what makes the row a theorem rather than an axiom:
    src/L/GCH/SuccessorIntoPowerSet.lagda.md inverts that injection through
    an order type and refutes the remaining case by Cantor.

```agda
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥) → SuccCardL δ κ
  → InjL (𝒫 κ) δ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )
```

4.  The successor cardinal exists.  Section 2 proves it.

```agda
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁
```

<!--en-->
## Larger internal cardinals exist

The fourth estimate follows from the earlier construction of a cardinal above any ordinal. Taking the least such cardinal supplies the exact successor-cardinal interface needed here.
<!--zh-->
## 更大的内部基数存在

第四条估计来自此前在任意序数之上构造基数的结果。取其中最小者，便得到此处所需的后继基数接口。
<!--ja-->
## より大きな内部基数の存在

第四の評価は、任意の順序数より上に基数を構成した先の結果から従う。そのうち最小のものを取れば、ここで必要な後続基数のインターフェースが得られる。
<!--/-->

`CardAboveL` (src/L/CardinalAbove.lagda.md) gives SOME ordinal L-cardinal above
`κ`; the least one is selected along the ordinal well-order on the tower at
`sucV θ`, and its minimality is the leastness clause of `SuccCardL`
(src/L/GCH.lagda.md:50-53).

```agda
module Reduce (κ : SL.S) (oκ : IsOrd (fst κ))
              (θ : SL.S) (oθ : IsOrd (fst θ))
              (cθ : IsCardinalL θ) (κ∈θ : ⟨ fst κ ∈ˢ fst θ ⟩) where

  open LeastCardInjL θ oθ using ( up; self; self-eq )

  A : Type ℓ
  A = ⟪ sucV (fst θ) ⟫
```

Sealed: unsealed, this selection is measured at over a hundred seconds at the
same site (agents/tasks/LJ-1-526/runs/s4-2.out).

```agda
  opaque
    w : SWO A
    w = ordSWO (sucV (fst θ)) (suc-ord oθ)

  opaque
    unfolding w
    w-lt : (m n : A) → SWO._<∙_ w m n
         ≡ ⟨ ⟪ sucV (fst θ) ⟫↪ m ∈ˢ ⟪ sucV (fst θ) ⟫↪ n ⟩
    w-lt m n = refl

  isPropIsCardinalL : (x : SL.S) → isProp (IsCardinalL x)
  isPropIsCardinalL x =
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → Empty.isProp⊥)))

  Good : A → hProp (ℓ-suc ℓ)
  Good b = (IsCardinalL (up b) × ⟨ fst κ ∈ˢ fst (up b) ⟩)
         , isProp× (isPropIsCardinalL (up b)) (snd (fst κ ∈ˢ fst (up b)))

  upSelf : up self ≡ θ
  upSelf = Σ≡Prop (λ x → snd (isL x)) self-eq

  nonempty : ∥ Σ[ b ∈ A ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ self
            , subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upSelf) (cθ , κ∈θ) ∣₁

  least : Σ[ b ∈ A ] IsLeast w Good b
  least = leastOf w lem Good nonempty

  δ : SL.S
  δ = up (fst least)

  δ∈sθ : ⟨ fst δ ∈ˢ sucV (fst θ) ⟩
  δ∈sθ = member (sucV (fst θ)) (fst least)

  oδ : IsOrd (fst δ)
  oδ = mem-ord {A = sucV (fst θ)} (suc-ord oθ) (fst δ) δ∈sθ

  cδ : IsCardinalL δ
  cδ = fst (fst (snd least))

  κ∈δ : ⟨ fst κ ∈ˢ fst δ ⟩
  κ∈δ = snd (fst (snd least))

  δ-min : (b : A) → ⟨ Good b ⟩ → (SWO._<∙_ w b (fst least) → Empty.⊥)
  δ-min = snd (snd least)

  leastness : (c : SL.S) → IsOrd (fst c) → IsCardinalL c
            → ⟨ fst κ ∈ˢ fst c ⟩
            → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
  leastness c oc cc κ∈c = go (ord-tri (fst δ) oδ (fst c) oc)
    where
    go : Tri (fst δ) (fst c)
       → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
    go (inl δ∈c)       x x∈δ = oc .fst x∈δ δ∈c
    go (inr (inl e))   x x∈δ = subst (λ v → ⟨ fst x ∈ˢ v ⟩) e x∈δ
    go (inr (inr c∈δ)) x x∈δ = Empty.rec (δ-min b bGood b<δ)
      where
      c∈sθ : ⟨ fst c ∈ˢ sucV (fst θ) ⟩
      c∈sθ = suc-ord oθ .fst c∈δ δ∈sθ
      b : A
      b = fiber (sucV (fst θ)) c∈sθ .fst
      be : ⟪ sucV (fst θ) ⟫↪ b ≡ fst c
      be = fiber (sucV (fst θ)) c∈sθ .snd
      upb : up b ≡ c
      upb = Σ≡Prop (λ v → snd (isL v)) be
      bGood : ⟨ Good b ⟩
      bGood = subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upb) (cc , κ∈c)
      b<δ : SWO._<∙_ w b (fst least)
      b<δ = transport (λ i → sym (w-lt b (fst least)) i)
              (subst (λ v → ⟨ v ∈ˢ fst δ ⟩) (sym be) c∈δ)

succCardExists : SuccCardExists
succCardExists κ oκ cκ κ∉ω = PT.map build (CardAboveL κ oκ cκ κ∉ω)
  where
  build : Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
        → Σ[ δ ∈ SL.S ] SuccCardL δ κ
  build (θ , oθ , cθ , κ∈θ) = R.δ , R.oδ , R.cδ , R.κ∈δ , R.leastness
    where module R = Reduce κ oκ θ oθ cθ κ∈θ
```

<!--en-->
## Discharging the structural estimates

Earlier chapters already show that ordinal-indexed stages belong to `L`, that bounded subsets appear in controlled stages, and that infinite stages inject into their indices. We package those results in the precise shapes required by the assembly.
<!--zh-->
## 兑现结构性估计

此前章节已经证明：以序数为指标的阶段属于 `L`，有界子集出现在受控阶段，并且无穷阶段单射到其指标。本节把这些结果封装成装配所需的准确形式。
<!--ja-->
## 構造に関する評価を満たす

先の章で、順序数を添字とする段階が `L` に属すること、有界部分集合が制御された段階に現れること、無限段階がその添字へ単射することを示した。本節では、それらを組み立てに必要な形へまとめる。
<!--/-->

The stage at an ordinal is constructible (src/L/Axioms/Basic.lagda.md).

```agda
stage-is-L : (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩
stage-is-L δ ordδ = isL-Lset (fst δ) ordδ
```

A member `z` of a member `y` of the internal power set of an ordinal `κ`: `z` is
constructible, a member of `κ`, and an ordinal.

`𝒫 κ = ℩ (hasPower κ)` and `hasPower` realizes the class `λ x → x ⊆ˢ κ`
(src/FOL/ZFModel.lagda.md), where `⊆ˢ` is the INTERNAL subset relation: it
quantifies over `SL.S` only. So the power-set hypothesis only speaks about
CONSTRUCTIBLE members of `y`, and `z` arrives ambient. The bridge is
transitivity of the class `isL` (src/L/Constructible.lagda.md).

```agda
zStrongest : ModelL.isZFModel → Type (ℓ-suc ℓ)
zStrongest zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩
  → (⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z)
  where open ModelL.isZFModel zf using ( 𝒫 )

z-strongest : (zf : ModelL.isZFModel) → zStrongest zf
z-strongest zf κ y ordκ y∈𝒫κ z z∈y = isLz , z∈κ , mem-ord {A = fst κ} ordκ z z∈κ
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )
```

`z` is constructible, because `y` is and L is transitive.

```agda
  isLz : ⟨ isL z ⟩
  isLz = isL-trans z∈y (snd y)
```

The power-set specification, read off `℩-spec`; `𝒫 κ` IS `℩ (hasPower κ)` by
definition, so no transport is needed.

```agda
  y⊆κ : ⟨ y ModelL.⊆ˢ κ ⟩
  y⊆κ = subst ⟨_⟩ (ModelL.℩-spec (hasPower κ) y) y∈𝒫κ
```

`z` re-enters the internal subset relation as the L-element `(z , isLz)`.

```agda
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = y⊆κ (z , isLz) z∈y
```

<!--en-->
## Every subset lands before the successor

Let `δ` be the successor cardinal of `κ`. The bounded-subset estimate first places a subset at some stage indexed by `β`; cardinal minimality then forces `β ∈ δ`, so monotonicity lifts the subset into the stage at `δ`.
<!--zh-->
## 每个子集都在后继之前落定

令 `δ` 为 `κ` 的后继基数。有界子集估计先把一个子集放入某个以 `β` 为指标的阶段；随后基数的最小性迫使 `β ∈ δ`，故单调性把该子集提升到 `δ` 处的阶段。
<!--ja-->
## 各部分集合は後続基数までに現れる

`δ` を `κ` の後続基数とする。有界部分集合の評価により、まず部分集合はある `β` を添字とする段階に入る。基数の最小性から `β ∈ δ` が従い、単調性によってその部分集合を `δ` の段階へ持ち上げられる。
<!--/-->

Hypothesis 2 places `y` at some stage `β` with `β` injecting into `κ`. By
trichotomy `β ∈ δ`, since `β ≡ δ` or `δ ∈ β` would inject `δ` into `κ` against
`IsCardinalL δ` at `κ ∈ δ`. Then `Lset-mono` lifts `y` to `δ`.

```agda
stage-landing :
    (zf : ModelL.isZFModel) → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (δ : SL.S) → SuccCardL δ κ
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
  → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
stage-landing zf ibs κ ordκ cardκ κ∉ω δ (ordδ , cardδ , κ∈δ , _) y y∈𝒫κ =
  PT.rec (snd (fst y ∈ˢ Lset (fst δ))) place (ibs κ ordκ cardκ κ∉ω y y⊆κ)
  where
  y⊆κ : (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩
  y⊆κ z z∈y = z-strongest zf κ y ordκ y∈𝒫κ z z∈y .snd .fst
```

An internal injection of `δ` into `κ` is absurd: `δ` is an L-cardinal and `κ` is
a member of it.

```agda
  no-δ↪κ : InjL δ κ → Empty.⊥
  no-δ↪κ = cardδ κ κ∈δ

  place : Σ[ β ∈ SL.S ]
            (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ)
        → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  place (β , ordβ , y∈Lβ , β↪κ) = go (ord-tri (fst β) ordβ (fst δ) ordδ)
    where
    go : Tri (fst β) (fst δ) → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
    go (inl β∈δ)       = Lset-mono β∈δ y∈Lβ
    go (inr (inl e))   = Empty.rec (no-δ↪κ (subst (λ b → InjL b κ) β≡δ β↪κ))
      where
      β≡δ : β ≡ δ
      β≡δ = Σ≡Prop (λ x → snd (isL x)) e
    go (inr (inr δ∈β)) = Empty.rec (no-δ↪κ
      (injl-trans δ β κ (inclusion-coded δ β δ⊆β) β↪κ))
      where
      δ⊆β : (z : SV.S) → ⟨ z ∈ˢ fst δ ⟩ → ⟨ z ∈ˢ fst β ⟩
      δ⊆β z z∈δ = ordβ .fst z∈δ δ∈β
```

<!--en-->
## Coding the power set below the successor

Since every subset of `κ` lies in the stage at its successor cardinal and that stage injects into its index, the model's power set of `κ` injects into the successor cardinal.
<!--zh-->
## 把幂集编码到后继以下

因为 `κ` 的每个子集都属于其后继基数处的阶段，而该阶段单射到自身指标，所以模型中的 `κ` 之幂集单射到后继基数。
<!--ja-->
## 冪集合を後続基数の下へコード化する

`κ` の各部分集合はその後続基数の段階に属し、その段階は添字自身へ単射する。したがって、モデルにおける `κ` の冪集合は後続基数へ単射する。
<!--/-->

```agda
power-into-succ :
    (zf : ModelL.isZFModel) → StageCountedCoded → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (δ : SL.S) → SuccCardL δ κ
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc@(ordδ , _ , κ∈δ , _) =
  injl-trans (𝒫 κ) Lδ δ (inclusion-coded (𝒫 κ) Lδ into)
    (scc δ Lδ ordδ δ∉ω refl)
  where
  open ModelL.isZFModel zf using ( 𝒫 )

  Lδ : SL.S
  Lδ = Lset (fst δ) , stage-is-L δ ordδ
```

`ω` is transitive, so `κ ∈ δ ∈ ω` would put `κ` in `ω`.

```agda
  δ∉ω : ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
  δ∉ω δ∈ω = κ∉ω (ω-ord .fst {x = fst δ} {y = fst κ} κ∈δ δ∈ω)
```

Every member of the model's power set is constructible, because L is transitive,
and then it lands at δ by section 4.

```agda
  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ =
    stage-landing zf ibs κ ordκ cardκ κ∉ω δ sc (z , isL-trans z∈ (snd (𝒫 κ))) z∈
```

<!--en-->
## The generalized continuum hypothesis

The injection just obtained and the reverse injection supplied by the successor-cardinal construction identify the cardinality of the power set. This is GCH inside the model.
<!--zh-->
## 广义连续统假设

刚得到的单射与后继基数构造给出的反向单射共同确定了幂集的基数。这正是模型内部的 GCH。
<!--ja-->
## 一般連続体仮説

今得た単射と、後続基数の構成が与える逆向きの単射により、冪集合の基数が定まる。これがモデル内部の GCH である。
<!--/-->

```agda
gch-from-internal-bill :
    (zf : ModelL.isZFModel)
  → StageCountedCoded → InternalBoundedSubset → SuccIntoPower zf
  → GCHStatement zf
gch-from-internal-bill zf scc ibs sip κ ordκ cardκ κ∉ω =
  PT.map step (succCardExists κ ordκ cardκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) = δ , sc , pis , sip κ δ κ∉ω sc pis
    where
    pis : InjL (𝒫 κ) δ
    pis = power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc
```
