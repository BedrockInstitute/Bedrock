<!--en-->
# Adequate stages for the GCH argument

The internal descriptions used by condensation require four witness sets to be present together. This chapter defines an adequate stage, constructs one above any ordinal, and then builds a strengthened adequate stage in which every member lies inside a smaller adequate member.
<!--zh-->
# GCH 论证所需的充分层

凝聚所用的内部描述要求四个见证集合同时出现。本章定义充分层，在任意序数之上构造一个充分层，再构造一个强化版本，使其中每个成员都落在一个更小的充分成员之内。
<!--ja-->
# GCH の議論に必要な十分な段階

凝縮で用いる内部記述には、四つの証人集合が同時に存在する必要がある。本章では十分な段階を定義し、任意の順序数より上にそのような段階を構成する。さらに、各要素がより小さい十分な要素の内側に入る、強化された十分な段階を構成する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.AdequateStages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( union-family-in; union-family-out )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; isL; IsOrd; isPropIsOrd; Lset; Lset-mono; Lset→isL; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( boundingOrd; bound2; setUnion-ord; mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.EnvironmentTower {ℓ} lem using ( module Tower )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

The 𝒮ʟ carrier.

```agda
module CS = hPropStructure 𝒮ʟ using (S)
```

<!--en-->
## The four witnesses held by an adequate stage

At an ordinal `c`, the hierarchy description names four sets over `Lset c`: the hierarchy table, the set of formula codes, the graph of the uniform satisfaction table, and the environment tower. An adequate stage is closed under successor, contains `ω`, and contains these four witnesses for every earlier ordinal.
<!--zh-->
## 充分层所容纳的四个见证

在序数 `c` 处，层级描述为 `Lset c` 上的四个集合命名：层级表、公式码集合、统一满足关系表的图，以及环境塔。一个充分层对后继闭合，包含 `ω`，并为每个更早的序数备齐这四个见证。
<!--ja-->
## 十分な段階が含む四つの証人

順序数 `c` において、階層の記述は `Lset c` 上の四つの集合、すなわち階層表、論理式コードの集合、一様な充足関係表のグラフ、環境の塔を指定する。十分な段階は後者について閉じ、`ω` を含み、各々のより小さい順序数についてこの四つの証人を含む。
<!--/-->

At an ordinal `c` the level description (src/L/GCH/HierarchyDescription.lagda.md) names
four sets over the carrier `w = Lset c`: the hierarchy table on `c`, the code
set, the graph of the uniform satisfaction table and the environment tower.
Every other set its rows bound is a member of one of these, a numeral, or a
stage below, and the closures of an adequate stage reach it.

```agda
module At (c : V ℓ) (oc : IsOrd c) where

  A : CS.S
  A = LsetS c oc

  cL : ⟨ isL c ⟩
  cL = Lset→isL (sucV c) (suc-ord oc) c (ord∈Lset-suc c oc)

  hier : CS.S
  hier = hierL c cL oc

  codes : CS.S
  codes = AllCodes A

  table : CS.S
  table = SatGraph.pairs A

  tower : CS.S
  tower = Tower.tower A
```

The four witnesses at `c` lie in `K`, at whatever proof of ordinality.

```agda
Witnesses : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Witnesses K c = (oc : IsOrd c)
  → ⟨ fst (At.hier c oc) ∈ K ⟩
  × ⟨ fst (At.codes c oc) ∈ K ⟩
  × ⟨ fst (At.table c oc) ∈ K ⟩
  × ⟨ fst (At.tower c oc) ∈ K ⟩

isPropWitnesses : (K c : V ℓ) → isProp (Witnesses K c)
isPropWitnesses K c = isPropΠ λ oc →
  isProp× (snd (fst (At.hier c oc) ∈ K))
    (isProp× (snd (fst (At.codes c oc) ∈ K))
      (isProp× (snd (fst (At.table c oc) ∈ K)) (snd (fst (At.tower c oc) ∈ K))))
```

Adequacy. `γ` is an ordinal closed under successor, holds `ω`, and `Lset γ`
holds the four witnesses of every `c ∈ γ`.

```agda
Adequate : V ℓ → Type (ℓ-suc ℓ)
Adequate γ =
    IsOrd γ
  × ((x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩)
  × ⟨ ω ∈ γ ⟩
  × ((c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c)

module Adequate (γ : V ℓ) (ad : Adequate γ) where
  ord = ad .fst
  succ = ad .snd .fst
  ω∈ = ad .snd .snd .fst
  wit = ad .snd .snd .snd
```

<!--en-->
## Constructing an adequate stage above any ordinal

One bounding step collects the birth stages of all four witnesses, the successors of the current members, the current ordinal, and `ω`. Iterating that step through `ω` and taking the union produces an ordinal that contains the starting point and satisfies every condition for an adequate stage.
<!--zh-->
## 在任意序数之上构造充分层

一次取界同时收集四个见证的诞生层、当前成员的后继、当前序数本身与 `ω`。沿 `ω` 迭代这一步并取并集，便得到一个包含起点且满足全部充分条件的序数。
<!--ja-->
## 任意の順序数より上に十分な段階を構成する

一回の上界構成で、四つの証人の誕生段階、現在の要素の後者、現在の順序数そのもの、そして `ω` をまとめて収める。この操作を `ω` 回反復して合併を取ると、出発点を含み、十分性のすべての条件を満たす順序数が得られる。
<!--/-->

One step bounds the birth stages of the witnesses of every member of `α`, the
successors of the members, `α` itself and `ω` (src/L/Ordinal.lagda.md
`boundingOrd`, `bound2`); `ω` steps from `p+1` and the union of the chain is
adequate: a member of the union is a member of some step, and whatever that step
owes is in the next.

The members of a set as a family of stages, and the union of a chain.

```agda
private
  ι : (α : V ℓ) → ⟪ α ⟫ → V ℓ
  ι α = ⟪ α ⟫↪

  ι∈ : (α : V ℓ) (m : ⟪ α ⟫) → ⟨ ι α m ∈ α ⟩
  ι∈ α m = ∈∈ₛ {a = ι α m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
```

Membership in an ordinal is transitive, spelled at the values.

```agda
  tr : (β : V ℓ) → IsOrd β → (x y : V ℓ) → ⟨ x ∈ β ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ β ⟩
  tr β oβ x y x∈ y∈ = oβ .fst {x = x} {y = y} y∈ x∈
```

One step.

```agda
module Bound1 (α : V ℓ) (oα : IsOrd α) where

  private
    W : ⟪ α ⟫ → (c : V ℓ) → IsOrd c → CS.S → V ℓ
    W m c oc s = stage (fst s) (snd s)

    oc : (m : ⟪ α ⟫) → IsOrd (ι α m)
    oc m = mem-ord {A = α} oα (ι α m) (ι∈ α m)

    st : (f : (c : V ℓ) (o : IsOrd c) → CS.S) → ⟪ α ⟫ → V ℓ
    st f m = stage (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))

    st-ord : (f : (c : V ℓ) (o : IsOrd c) → CS.S) (m : ⟪ α ⟫) → IsOrd (st f m)
    st-ord f m = stage-ord (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))

    b1 = boundingOrd ⟪ α ⟫ (st At.hier) (st-ord At.hier)
    b2 = boundingOrd ⟪ α ⟫ (st At.codes) (st-ord At.codes)
    b3 = boundingOrd ⟪ α ⟫ (st At.table) (st-ord At.table)
    b4 = boundingOrd ⟪ α ⟫ (st At.tower) (st-ord At.tower)
    b5 = boundingOrd ⟪ α ⟫ (λ m → sucV (ι α m)) (λ m → suc-ord (oc m))
    b6 = bound2 α ω oα ω-ord
    b7 = bound2 (b1 .fst) (b2 .fst) (b1 .snd .fst) (b2 .snd .fst)
    b8 = bound2 (b3 .fst) (b4 .fst) (b3 .snd .fst) (b4 .snd .fst)
    b9 = bound2 (b5 .fst) (b6 .fst) (b5 .snd .fst) (b6 .snd .fst)
    b10 = bound2 (b7 .fst) (b8 .fst) (b7 .snd .fst) (b8 .snd .fst)
    b11 = bound2 (b9 .fst) (b10 .fst) (b9 .snd .fst) (b10 .snd .fst)

  β : V ℓ
  β = b11 .fst

  oβ : IsOrd β
  oβ = b11 .snd .fst

  private
    b9∈ : ⟨ b9 .fst ∈ β ⟩
    b9∈ = b11 .snd .snd .fst
    b10∈ : ⟨ b10 .fst ∈ β ⟩
    b10∈ = b11 .snd .snd .snd
    b5∈ : ⟨ b5 .fst ∈ β ⟩
    b5∈ = tr β oβ (b9 .fst) (b5 .fst) b9∈ (b9 .snd .snd .fst)
    b6∈ : ⟨ b6 .fst ∈ β ⟩
    b6∈ = tr β oβ (b9 .fst) (b6 .fst) b9∈ (b9 .snd .snd .snd)
    b7∈ : ⟨ b7 .fst ∈ β ⟩
    b7∈ = tr β oβ (b10 .fst) (b7 .fst) b10∈ (b10 .snd .snd .fst)
    b8∈ : ⟨ b8 .fst ∈ β ⟩
    b8∈ = tr β oβ (b10 .fst) (b8 .fst) b10∈ (b10 .snd .snd .snd)
    b1∈ : ⟨ b1 .fst ∈ β ⟩
    b1∈ = tr β oβ (b7 .fst) (b1 .fst) b7∈ (b7 .snd .snd .fst)
    b2∈ : ⟨ b2 .fst ∈ β ⟩
    b2∈ = tr β oβ (b7 .fst) (b2 .fst) b7∈ (b7 .snd .snd .snd)
    b3∈ : ⟨ b3 .fst ∈ β ⟩
    b3∈ = tr β oβ (b8 .fst) (b3 .fst) b8∈ (b8 .snd .snd .fst)
    b4∈ : ⟨ b4 .fst ∈ β ⟩
    b4∈ = tr β oβ (b8 .fst) (b4 .fst) b8∈ (b8 .snd .snd .snd)

  α∈β : ⟨ α ∈ β ⟩
  α∈β = tr β oβ (b6 .fst) α b6∈ (b6 .snd .snd .fst)

  ω∈β : ⟨ ω ∈ β ⟩
  ω∈β = tr β oβ (b6 .fst) ω b6∈ (b6 .snd .snd .snd)

  suc∈β : (x : V ℓ) → ⟨ x ∈ α ⟩ → ⟨ sucV x ∈ β ⟩
  suc∈β x x∈ = subst (λ u → ⟨ sucV u ∈ β ⟩) (fib .snd)
    (tr β oβ (b5 .fst) (sucV (ι α (fib .fst))) b5∈ (b5 .snd .snd (fib .fst)))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ x)
    fib = ∈-asFiber {a = x} {b = α} x∈

  private
```

A witness at an indexed member lies in `Lset β`, through its stage and the bound
of the stages.

```agda
    land : (f : (c : V ℓ) (o : IsOrd c) → CS.S)
           (b : Σ[ σ ∈ V ℓ ] (IsOrd σ × ((m : ⟪ α ⟫) → ⟨ st f m ∈ σ ⟩)))
         → ⟨ b .fst ∈ β ⟩
         → (m : ⟪ α ⟫) → ⟨ fst (f (ι α m) (oc m)) ∈ Lset β ⟩
    land f b b∈ m =
      Lset-mono {α = β} {β = b .fst} b∈
        (Lset-mono {α = b .fst} {β = st f m} (b .snd .snd m)
          (stage-mem (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))))
```

At the indexed member, at any proof of its ordinality.

```agda
    witAt : (m : ⟪ α ⟫) → Witnesses (Lset β) (ι α m)
    witAt m o =
        subst (λ u → ⟨ fst (At.hier (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
          (land At.hier b1 b1∈ m)
      , ( subst (λ u → ⟨ fst (At.codes (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
            (land At.codes b2 b2∈ m)
        , ( subst (λ u → ⟨ fst (At.table (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.table b3 b3∈ m)
          , subst (λ u → ⟨ fst (At.tower (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.tower b4 b4∈ m) ))

  wit : (c : V ℓ) → ⟨ c ∈ α ⟩ → Witnesses (Lset β) c
  wit c c∈ = subst (Witnesses (Lset β)) (fib .snd) (witAt (fib .fst))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ c)
    fib = ∈-asFiber {a = c} {b = α} c∈
```

The union of an `ω`-chain of ordinals, with its two membership directions. The
chain is any family; the consumers below supply one whose every step lies in the
next.

```agda
module Union (ch : ℕ → V ℓ) (och : (n : ℕ) → IsOrd (ch n)) where

  private
    F : Lift {ℓ-zero} {ℓ} ℕ → V ℓ
    F n = ch (lower n)

  γ : V ℓ
  γ = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) F)

  oγ : IsOrd γ
  oγ = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) F (λ n → och (lower n))

  into : (n : ℕ) (x : V ℓ) → ⟨ x ∈ ch n ⟩ → ⟨ x ∈ γ ⟩
  into n x = union-family-in (Lift {ℓ-zero} {ℓ} ℕ) F (lift n) x

  outof : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ ch n ⟩ ∥₁
  outof x h = PT.map (λ { (n , hn) → lower n , hn })
    (union-family-out (Lift {ℓ-zero} {ℓ} ℕ) F x h)
```

The stage above `p`.

```agda
module Above (p : V ℓ) (op : IsOrd p) where

  private
    base = bound2 p ω op ω-ord

  ch : ℕ → Σ[ β ∈ V ℓ ] IsOrd β
  ch zero = base .fst , base .snd .fst
  ch (suc n) = Bound1.β (ch n .fst) (ch n .snd) , Bound1.oβ (ch n .fst) (ch n .snd)

  module C = Union (λ n → ch n .fst) (λ n → ch n .snd) using (into; outof; oγ; γ)

  γ : V ℓ
  γ = C.γ

  oγ : IsOrd γ
  oγ = C.oγ

  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = Bound1.α∈β (ch n .fst) (ch n .snd)

    ch∈γ : (n : ℕ) → ⟨ ch n .fst ∈ γ ⟩
    ch∈γ n = C.into (suc n) (ch n .fst) (up n)

  p∈γ : ⟨ p ∈ γ ⟩
  p∈γ = C.into zero p (base .snd .snd .fst)

  ω∈γ : ⟨ ω ∈ γ ⟩
  ω∈γ = C.into zero ω (base .snd .snd .snd)

  succ : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩
  succ x x∈ = PT.rec (snd (sucV x ∈ γ))
    (λ { (n , x∈n) → C.into (suc n) (sucV x) (Bound1.suc∈β (ch n .fst) (ch n .snd) x x∈n) })
    (C.outof x x∈)

  wit : (c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c
  wit c c∈ = PT.rec (isPropWitnesses (Lset γ) c)
    (λ { (n , c∈n) → λ oc →
      let w = Bound1.wit (ch n .fst) (ch n .snd) c c∈n oc
          mono = Lset-mono {α = γ} {β = ch (suc n) .fst} (ch∈γ (suc n))
      in mono (w .fst) , ( mono (w .snd .fst) , ( mono (w .snd .snd .fst) , mono (w .snd .snd .snd) )) })
    (C.outof c c∈)

  adequate : Adequate γ
  adequate = oγ , ( succ , ( ω∈γ , wit ))

adequate-above : (p : V ℓ) → IsOrd p
               → Σ[ γ ∈ V ℓ ] (IsOrd γ × ⟨ p ∈ γ ⟩ × Adequate γ)
adequate-above p op = Above.γ p op , ( Above.oγ p op , ( Above.p∈γ p op , Above.adequate p op ))
```

<!--en-->
## Strengthening the conditions throughout a stage

A strengthened adequate stage requires every member to lie in an adequate member of the same stage. Iterating `adequate-above` through `ω` supplies this local reservoir while ensuring that the union is itself an adequate stage.
<!--zh-->
## 在整个层中强化充分性

一个超充分层要求每个成员都属于同一层中的某个充分成员。沿 `ω` 迭代 `adequate-above`，既为每个成员提供这样的充分层，又保持并集本身的充分性。
<!--ja-->
## 段階全体で十分性を強化する

強化された十分な段階では、各要素が同じ段階に属する十分な要素の中に入る。`adequate-above` を `ω` 回反復すると、このような十分な段階を各要素に用意しながら、その合併自身の十分性も保てる。
<!--/-->

`λ` is superadequate when every member lies in an adequate member. Iterating
`adequate-above` `ω` times from `α` and taking the union gives a stage that is
adequate and superadequate at once: a member of the union lies in some step, and
every step is adequate and lies in the next.

NOTE. src/L/Ordinal.lagda.md:205-213 `IsLimit` asks closure under EVERY
small-indexed union. No `ω`-union has that property: the chain itself, indexed
by `ℕ`, is a small family in the union whose union is the union. So the stage
below is delivered with the two closure facts an `ω`-union does have (successor
closure, and `ω` as a member), as `Adequate` states them, and not with
`IsLimit`.

```agda
Superadequate : V ℓ → Type (ℓ-suc ℓ)
Superadequate lam = (d : V ℓ) → ⟨ d ∈ lam ⟩
  → ∥ Σ[ γ ∈ V ℓ ] (⟨ γ ∈ lam ⟩ × ⟨ d ∈ γ ⟩ × Adequate γ) ∥₁

module Super (α : V ℓ) (oα : IsOrd α) where

  ch : ℕ → Σ[ γ ∈ V ℓ ] (IsOrd γ × Adequate γ)
  ch zero =
    adequate-above α oα .fst
    , ( adequate-above α oα .snd .fst , adequate-above α oα .snd .snd .snd )
  ch (suc n) =
    adequate-above (ch n .fst) (ch n .snd .fst) .fst
    , ( adequate-above (ch n .fst) (ch n .snd .fst) .snd .fst
      , adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .snd )

  module U = Union (λ n → ch n .fst) (λ n → ch n .snd .fst) using (into; outof; oγ; γ)

  lam : V ℓ
  lam = U.γ

  olam : IsOrd lam
  olam = U.oγ

  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .fst

    ch∈λ : (n : ℕ) → ⟨ ch n .fst ∈ lam ⟩
    ch∈λ n = U.into (suc n) (ch n .fst) (up n)

  α∈λ : ⟨ α ∈ lam ⟩
  α∈λ = U.into zero α (adequate-above α oα .snd .snd .fst)

  succ : (x : V ℓ) → ⟨ x ∈ lam ⟩ → ⟨ sucV x ∈ lam ⟩
  succ x x∈ = PT.rec (snd (sucV x ∈ lam))
    (λ { (n , x∈n) → U.into n (sucV x) (Adequate.succ (ch n .fst) (ch n .snd .snd) x x∈n) })
    (U.outof x x∈)

  ω∈λ : ⟨ ω ∈ lam ⟩
  ω∈λ = U.into zero ω (Adequate.ω∈ (ch zero .fst) (ch zero .snd .snd))

  wit : (c : V ℓ) → ⟨ c ∈ lam ⟩ → Witnesses (Lset lam) c
  wit c c∈ = PT.rec (isPropWitnesses (Lset lam) c)
    (λ { (n , c∈n) → λ oc →
      let w = Adequate.wit (ch n .fst) (ch n .snd .snd) c c∈n oc
      in  Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .fst)
        , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .fst)
          , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .fst)
            , Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .snd) )) })
    (U.outof c c∈)

  adequate : Adequate lam
  adequate = olam , ( succ , ( ω∈λ , wit ))

  super : Superadequate lam
  super d d∈ = PT.map
    (λ { (n , d∈n) → ch n .fst , ( ch∈λ n , ( d∈n , ch n .snd .snd )) })
    (U.outof d d∈)

superadequate-above : (α : V ℓ) → IsOrd α
                    → Σ[ lam ∈ V ℓ ] (IsOrd lam × ⟨ α ∈ lam ⟩ × Adequate lam × Superadequate lam)
superadequate-above α oα =
  Super.lam α oα , ( Super.olam α oα , ( Super.α∈λ α oα , ( Super.adequate α oα , Super.super α oα )))
```

<!--en-->
## A stage belongs to its successor stage

The whole stage `Lset β` is the subset of itself selected by the always-true formula. It is therefore definable over itself and belongs to `Lset (sucV β)`.
<!--zh-->
## 一层属于其后继层

整个层 `Lset β` 正是恒真公式从自身选出的子集。因此它在自身之上可定义，并属于 `Lset (sucV β)`。
<!--ja-->
## 段階はその後者段階に属する

段階 `Lset β` 全体は、恒真な論理式がそれ自身から切り出す部分集合である。したがって、それは自身の上で定義可能であり、`Lset (sucV β)` に属する。
<!--/-->

It is the definable subset of itself that `⊤̇` carves out.

```agda
Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)
```
