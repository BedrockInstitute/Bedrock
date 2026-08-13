# The Mostowski collapse

<!--en-->
The condensation lemma is the recognition step of constructibility theory,
and it has two halves: the elementary substructure, and the device that
recognizes it, the **Mostowski collapse**. This chapter delivers the collapse
half. The carrier is a transitive set `X` inside the hierarchy, the collapse is
defined by the hierarchy's own membership recursion, filtered to the members of
`X`, and the classical package follows: the range is a set, it is transitive,
the collapse is one-to-one on the carrier, and membership is preserved both
ways, so the carrier and its image are isomorphic structures. The probe priced
all four decisive pieces green and carrier-neutral; this chapter builds them at
the generality the condensation chapter consumes, a transitive set carrier,
with the range formed as a set and the uniqueness half added, the two
production items the miniature deliberately left out.

One design note fixes the level picture before the code. The carrier `X` is a
set, not a class, and every construction stays at the small member type
`⟪ x ⟫`, so the whole development is assumption-free. The transitivity of `X`
is consumed only where the classical proof consumes it, in the injectivity and
the backward direction of the iso, and it is a module parameter there, not a
global hypothesis.
<!--zh-->
凝聚引理是可构造性理论的识别一步，它有两半：初等子结构，以及识别它的装置，即 **Mostowski 坍缩**。本章交付坍缩这一半。载体是层级内的传递集 `X`，坍缩由层级自身的成员递归定义，过滤到 `X` 的成员上，随后是经典包：像是一集、它是传递的、坍缩在载体上单射，且成员关系双向保持，于是载体与其像是同构的结构。探针把四个决定性部件全部测得绿灯且与载体无关；本章在凝聚章所消费的普遍度，即传递集载体，处建造它们，并把探针刻意留白的两个生产件补上：像形成为集，以及唯一性半边。

一处设计注记先钉下层级图景。载体 `X` 是集而非类，而下面每个构造都停留在小成员类型 `⟪ x ⟫` 处，故整个开发无需任何假设。`X` 的传递性只在经典证明消费它的两处被消费，即单射性与同构的向后方向，且在那里是模块参数，而非全局假设。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Collapse {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-induction-compute )
open import V.Presentation {ℓ} using ( member; fiber )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; seteq )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; extensionality; _⊆_ )

open hPropStructure 𝒮ᵥ

-- transitivity of a set, in the absoluteness-chapter shape; definitionally the
-- same predicate as the constructible chapter's isTransV, so a consumer's
-- transitivity witness passes through unchanged
isTrans : S → Type (ℓ-suc ℓ)
isTrans u = Transitive 𝒮ᵥ (λ x → x ∈ˢ u)
```

<!--en-->
## The collapse map
<!--zh-->
## 坍缩映射
<!--/-->

<!--en-->
The collapse is defined by ∈-recursion over the whole hierarchy, one step per
set: `π x` is the set of the `π`-images of the members of `x` that lie in the
carrier `X`. The index is the **filtered small member type** `Fiber x`, the
small members of `x` that are also small members of `X`, exactly the index
discipline the tower uses; the small membership `∈ₛ` is the free smallness
atom, so no resizing and no choice enters. The step reads `π x` as the
`sett`{.Agda} over that index.
<!--zh-->
坍缩沿整个层级用成员递归定义，每个集合一步：`π x` 是 `x` 中落在载体 `X` 内的那些成员之 `π` 像的集合。索引是**过滤后的小成员类型** `Fiber x`，即既是 `x` 的小成员、又是 `X` 的小成员的指标，恰是塔所用的索引纪律；小成员关系 `∈ₛ` 是免费的小性原子，故无需降层也无需选择。步长把 `π x` 读作该索引上的 `sett`{.Agda}。
<!--/-->

```agda
module Collapse (X : S) where

  -- the filtered small index: the small members of x that are small members
  -- of the carrier.  The filter uses the small membership, so Fiber x is
  -- small and no resizing or impredicativity is spent.
  Fiber : S → Type ℓ
  Fiber x = Σ[ m ∈ ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ m ∈ₛ X ⟩

  step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
  step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (member x (p .fst)))
```

<!--en-->
The recursor is the hierarchy's own `∈-induction`{.Agda} at `P x = S`,
set-valued. It is sealed `opaque`{.Agda} at birth because it unfolds to an
accessibility eliminator, and the computation law is a read lemma inside the
seal, a propositional path in the h-set codomain; everything below consumes
the law through `subst`{.Agda}, never the unfolding.
<!--zh-->
递归器本身是层级自己的 `∈-induction`{.Agda}，取 `P x = S`，即集值递归。它一出生就 `opaque`{.Agda} 封起，因为它展开成可及性消去子；计算律是封内的读引理，是 h-集值域中的命题路径，下面的一切都经 `subst`{.Agda} 消费该律，绝不展开定义。
<!--/-->

```agda
  -- perf: the recursion unfolds to an accessibility eliminator; seal at
  -- birth, computation law as the read lemma (R-36)
  opaque
    π : S → S
    π = ∈-induction step

  opaque
    unfolding π
    π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
    π-compute = ∈-induction-compute step
```

<!--en-->
## The range as a set
<!--zh-->
## 作为集的像
<!--/-->

<!--en-->
First the image lemma: every member of a collapse value is a collapse value of
a member of the carrier, so the range of `π` is transitive as a class. The
proof is one truncation recovery over the computation law, and it needs no
hypothesis on `X`: the filter carries the carrier-membership witness.
<!--zh-->
先取像引理：坍缩像的每个成员都是载体的某个成员的坍缩像，故 `π` 的值域作为类是传递的。证明是对计算律的一次截断恢复，且不需要对 `X` 的任何假设：过滤项本身就携带载体成员见证。
<!--/-->

```agda
  π-member : (x z : S) → ⟨ z ∈ˢ π x ⟩
           → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z)) ∥₁
  π-member x z z∈ = PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (π-compute x) z∈)
    where
    mk : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ z)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = X} .snd (p .snd)
                 , q )
```

<!--en-->
The range is formed as a set: `πX` indexes the small members of the carrier and
collects their collapse values. Its members are exactly the collapse values of
the carrier's members, merely, as membership is a truncation; and the collapse
value of every carrier member is a member of `πX`. Transitivity of the range
follows from the two, again with no hypothesis on `X`: a member of a collapse
value is, by the image lemma, itself a collapse value of a carrier member.
<!--zh-->
像形成为集：`πX` 以载体的小成员为索引，收集它们的坍缩像。其成员恰是载体各成员的坍缩像 (仅存在性，因为成员关系是截断)，而载体每个成员的坍缩像都是 `πX` 的成员。像的传递性由这两条得出，同样无需对 `X` 的任何假设：坍缩像的成员，按像引理，本身又是载体某成员的坍缩像。
<!--/-->

```agda
  πX : S
  πX = sett ⟪ X ⟫ (λ m → π (⟪ X ⟫↪ m))

  πX-member : (z : S) → ⟨ z ∈ˢ πX ⟩
            → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z)) ∥₁
  πX-member z z∈ = PT.map mk z∈
    where
    mk : Σ[ m ∈ ⟪ X ⟫ ] (π (⟪ X ⟫↪ m) ≡ z)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z))
    mk (m , q) = ⟪ X ⟫↪ m , ( member X m , q )

  πX-intro : (y : S) → ⟨ y ∈ˢ X ⟩ → ⟨ π y ∈ˢ πX ⟩
  πX-intro y y∈X = ∣ fiber X y∈X .fst , cong π (fiber X y∈X .snd) ∣₁

  πX-trans : isTrans πX
  πX-trans {x} {y} y∈x x∈πX = PT.rec (snd (y ∈ˢ πX)) go (πX-member x x∈πX)
    where
    go : Σ[ z ∈ S ] (⟨ z ∈ˢ X ⟩ × (π z ≡ x)) → ⟨ y ∈ˢ πX ⟩
    go (z , z∈X , pzx) = PT.rec (snd (y ∈ˢ πX)) go₂ (π-member z y y∈πz)
      where
      y∈πz : y ∈ᵗ π z
      y∈πz = subst (λ w → y ∈ᵗ w) (sym pzx) y∈x
      go₂ : Σ[ w ∈ S ] (⟨ w ∈ˢ X ⟩ × (π w ≡ y)) → ⟨ y ∈ˢ πX ⟩
      go₂ (w , w∈X , pwy) = subst (λ v → ⟨ v ∈ˢ πX ⟩) pwy (πX-intro w w∈X)
```

<!--en-->
## Membership forward
<!--zh-->
## 隶属向前
<!--/-->

<!--en-->
The forward direction of the iso needs nothing beyond the definition: a member
`y` of a carrier member `x` has a small index in `x`, and the witness that it
lies in the carrier is exactly the filter entry that places `π y` into `π x`.
<!--zh-->
同构的向前方向只需定义：载体成员 `x` 的成员 `y` 在 `x` 里有小索引，而它落在载体内的见证恰是让 `π y` 进入 `π x` 的过滤项。
<!--/-->

```agda
  π∈-fwd : (x y : S) → y ∈ᵗ x → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩
  π∈-fwd x y yx yu = subst (λ w → ⟨ π y ∈ˢ w ⟩) (sym (π-compute x)) wit
    where
    fib : Σ[ m ∈ ⟪ x ⟫ ] (⟪ x ⟫↪ m ≡ y)
    fib = fiber x yx
    m : ⟪ x ⟫
    m = fib .fst
    p : ⟪ x ⟫↪ m ≡ y
    p = fib .snd
    sm : ⟨ ⟪ x ⟫↪ m ∈ₛ X ⟩
    sm = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = X} .fst (subst (λ w → ⟨ w ∈ˢ X ⟩) (sym p) yu)
    wit : ⟨ π y ∈ˢ sett (Fiber x) (λ q → π (⟪ x ⟫↪ (q .fst))) ⟩
    wit = ∣ (m , sm) , cong π p ∣₁
```

<!--en-->
## Extensional injectivity
<!--zh-->
## 外延单射性
<!--/-->

<!--en-->
The one-to-one half is the classical double induction: `π x ≡ π y` implies
`x ≡ y` for carrier members `x, y`. The proof is a single `∈-induction`{.Agda}
on `x`, with the hypothesis quantified over the other argument. Direction 1
moves a member `z` of `x` into `y`: `π z ∈ π x` by the forward lemma, the
equality and the computation law recover a witness `b ∈ y` with `π b ≡ π z`,
and the hypothesis identifies `z` with `b`. Direction 2 is symmetric, but the
hypothesis fires at the witness extracted from the collapsed membership, not at
the input: `z ∈ y` enters through `π z ∈ π x`, which names `b ∈ x` with
`π b ≡ π z`, and the carrier's transitivity certifies `b ∈ X` so the hypothesis
can fire there. That is why the carrier's transitivity is a module parameter
here and only here.
<!--zh-->
单射半边是经典的双重归纳：对载体成员 `x, y`，`π x ≡ π y` 蕴含 `x ≡ y`。证明是对 `x` 的一次 `∈-induction`{.Agda}，假设量化到另一参数。方向一把 `x` 的成员 `z` 搬进 `y`：由向前引理得 `π z ∈ π x`，沿等词与计算律恢复出满足 `π b ≡ π z` 的见证 `b ∈ y`，假设再把 `z` 与 `b` 等同。方向二对称，但假设在从坍缩成员中提取的见证处点燃，而非在输入处：`z ∈ y` 经 `π z ∈ π x` 进入，后者点名 `b ∈ x` 且 `π b ≡ π z`，而载体的传递性正是用来证明 `b ∈ X`，使假设能在那里点燃。这就是为何载体的传递性在此处、也仅在此处成为模块参数。
<!--/-->

```agda
  module Inj (Xtr : isTrans X) where

    P : S → Type (ℓ-suc ℓ)
    P x = (y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y

    -- direction 1: move a member z of x into y; the hypothesis fires at z ∈ x
    in⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ x → z ∈ᵗ X
        → π x ≡ π y
        → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b)
        → ⟨ z ∈ₛ y ⟩
    in⊆ x y z xu yu zx zu e ih = ∈∈ₛ {a = z} {b = y} .fst
      (PT.rec (snd (z ∈ˢ y)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute y)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd x z zx zu))))
      where
      step2 : Σ[ p ∈ Fiber y ] (π (⟪ y ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ y ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym z≡b) by
        where
        b : S
        b = ⟪ y ⟫↪ (p .fst)
        by : ⟨ b ∈ˢ y ⟩
        by = member y (p .fst)
        bu : ⟨ b ∈ˢ X ⟩
        bu = Xtr {x = y} {y = b} by yu
        z≡b : z ≡ b
        z≡b = ih z zx b bu (sym q)

    -- direction 2: move a member z of y into x; the hypothesis fires at the
    -- witness b ∈ x extracted from the collapsed membership
    out⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ y → z ∈ᵗ X
         → π y ≡ π x
         → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b)
         → ⟨ z ∈ₛ x ⟩
    out⊆ x y z xu yu zy zu e ih = ∈∈ₛ {a = z} {b = x} .fst
      (PT.rec (snd (z ∈ˢ x)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute x)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd y z zy zu))))
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) b≡z bx
        where
        b : S
        b = ⟪ x ⟫↪ (p .fst)
        bx : ⟨ b ∈ˢ x ⟩
        bx = member x (p .fst)
        bu : ⟨ b ∈ˢ X ⟩
        bu = Xtr {x = x} {y = b} bx xu
        b≡z : b ≡ z
        b≡z = ih b bx z zu q
```

<!--en-->
The induction step assembles the two directions through extensionality, and
the recursion on membership delivers the theorem.
<!--zh-->
归纳步经外延性把两个方向装配起来，成员递归随之交出定理。
<!--/-->

```agda
    step-inj : (x : S) → ((a : S) → a ∈ᵗ x → P a) → P x
    step-inj x IH y xu yu e = extensionality x y (⊆xy , ⊆yx)
      where
      ih4 : (a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ X → π a ≡ π b → a ≡ b
      ih4 a ax b bu eq = IH a ax b (Xtr {x = x} {y = a} ax xu) bu eq
      ⊆xy : ⟨ x ⊆ y ⟩
      ⊆xy z z∈ₛx = let zx = ∈∈ₛ {a = z} {b = x} .snd z∈ₛx
                   in in⊆ x y z xu yu zx (Xtr {x = x} {y = z} zx xu) e ih4
      ⊆yx : ⟨ y ⊆ x ⟩
      ⊆yx z z∈ₛy = let zy = ∈∈ₛ {a = z} {b = y} .snd z∈ₛy
                   in out⊆ x y z xu yu zy (Xtr {x = y} {y = z} zy yu) (sym e) ih4

    -- extensional injectivity on the carrier, by ∈-induction
    π-inj : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
    π-inj = ∈-induction step-inj
```

<!--en-->
## The backward direction, and the Mostowski statement
<!--zh-->
## 向后方向与 Mostowski 陈述
<!--/-->

<!--en-->
The backward direction runs the same recovery in reverse: `π y ∈ π x` names a
witness `c ∈ x` whose collapse value is `π y`, and injectivity identifies `c`
with `y`. With both directions in hand, the collapse packages into a single
statement, the Mostowski statement for the carrier: the range is a transitive
set, the collapse is one-to-one on the carrier, and membership is preserved
both ways.
<!--zh-->
向后方向把同样的恢复倒着跑：`π y ∈ π x` 点名见证 `c ∈ x`，其坍缩像为 `π y`，单射性再把 `c` 与 `y` 等同。两个方向齐备后，坍缩打包成一条陈述，即该载体的 Mostowski 陈述：像为传递集，坍缩在载体上单射，且成员关系双向保持。
<!--/-->

```agda
    π∈-bwd : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩ → y ∈ᵗ x
    π∈-bwd x y xu yu h =
      PT.rec (snd (y ∈ˢ x)) step2 (subst (λ w → ⟨ π y ∈ˢ w ⟩) (π-compute x) h)
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π y) → ⟨ y ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) (c≡y) cx
        where
        c : S
        c = ⟪ x ⟫↪ (p .fst)
        cx : ⟨ c ∈ˢ x ⟩
        cx = member x (p .fst)
        cu : ⟨ c ∈ˢ X ⟩
        cu = Xtr {x = x} {y = c} cx xu
        c≡y : c ≡ y
        c≡y = π-inj c y cu yu q

    -- the iso reading on the carrier, both directions
    iso : (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩)
    iso x y xu yu = (λ yx → π∈-fwd x y yx yu) , π∈-bwd x y xu yu

    -- the Mostowski statement for the carrier: transitive range, injectivity,
    -- and membership preserved both ways
    Mostowski : Type (ℓ-suc ℓ)
    Mostowski = isTrans πX
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y)
              × ((x y : S) → x ∈ᵗ X → y ∈ᵗ X
               → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩))

    mostowski : Mostowski
    mostowski = πX-trans , π-inj , iso
```

<!--en-->
## Uniqueness
<!--zh-->
## 唯一性
<!--/-->

<!--en-->
The collapse is the unique solution of its recursion equation. If another
function satisfies the same equation, one membership induction identifies it
with `π` pointwise: the two steps are equal because the hypotheses are equal on
members, and `seteq`{.Agda} is the constructor that turns image equality into a
path.
<!--zh-->
坍缩是其递归方程的唯一解。若另有函数满足同一方程，再做一次成员归纳即可把它与 `π` 逐点等同：两个步长相等，因为假设在成员上相等，而 `seteq`{.Agda} 正是把像的相等做成路径的构造子。
<!--/-->

```agda
  unique : (f : S → S)
         → ((x : S) → f x ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst))))
         → (x : S) → π x ≡ f x
  unique f h = ∈-induction stepU
    where
    stepU : (x : S) → ((y : S) → y ∈ᵗ x → π y ≡ f y) → π x ≡ f x
    stepU x IH = π-compute x ∙ step-eq ∙ sym (h x)
      where
      step-eq : sett (Fiber x) (λ p → π (⟪ x ⟫↪ (p .fst)))
              ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst)))
      step-eq = seteq (Fiber x) (Fiber x)
                  (λ p → π (⟪ x ⟫↪ (p .fst)))
                  (λ p → f (⟪ x ⟫↪ (p .fst)))
                  ( (λ p → ∣ p , sym (ih' p) ∣₁)
                  , (λ p → ∣ p , ih' p ∣₁) )
        where
        ih' : (p : Fiber x) → π (⟪ x ⟫↪ (p .fst)) ≡ f (⟪ x ⟫↪ (p .fst))
        ih' p = IH (⟪ x ⟫↪ (p .fst)) (member x (p .fst))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
This chapter delivers the collapse half of condensation. For a transitive
carrier set `X`, the collapse `π` by the hierarchy's own recursion, its range
`πX` as a transitive set, extensional injectivity on the carrier, the
membership iso both ways, and the uniqueness of the recursion equation. The
condensation chapter consumes this at its carrier `M`: its transitivity witness
is definitionally the hypothesis this chapter's injectivity half takes, so no
conversion is needed at the consumer. What remains for condensation is the
elementary-substructure half and the recognition argument, priced elsewhere.
<!--zh-->
本章交付凝聚的坍缩半边。对传递载体集 `X`：由层级自身递归给出的坍缩 `π`，其像 `πX` 作为传递集，载体上的外延单射性，成员同构的两个方向，以及递归方程的唯一性。凝聚章在它的载体 `M` 处消费这一切：它的传递性见证与本章单射半边所取的假设定义性地同一，消费方无需任何转换。凝聚所余的是初等子结构半边与识别论证，两者均已在别处定价。
<!--/-->
