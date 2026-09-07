<!--en-->
# The Mostowski collapse

The Mostowski collapse turns a set-sized extensional membership structure into a transitive set. Membership recursion defines the collapsing map, its range is transitive, and extensionality makes the map injective and hence an isomorphism on the carrier.
<!--zh-->
# Mostowski 塌缩

Mostowski 塌缩把集合大小的外延隶属结构变成传递集。沿隶属关系的递归定义塌缩映射，其像是传递的，而外延性使该映射在载体上单射，因而给出同构。
<!--ja-->
# Mostowski 崩壊

Mostowski 崩壊は、集合の大きさを持つ外延的な所属構造を推移的集合へ変えます。所属関係上の再帰で崩壊写像を定義し、その像が推移的であることを示し、外延性から台上での単射性と同型を得ます。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Collapse {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute )
open import V.Presentation {ℓ} using ( member; fiber )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _⊆_ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## Carrier hypotheses

The collapse starts with a set `X` viewed as a carrier. Transitivity describes closure under membership, while `isExt X`{.Agda} says that two carrier elements are equal once they have the same carrier members; only the latter is needed for injectivity.
<!--zh-->
## 载体假设

塌缩从一个被视为载体的集合 `X` 开始。传递性描述对隶属关系的封闭，而 `isExt X`{.Agda} 断言：两个载体元素若有相同的载体成员便相等；只有后者是证明单射性所需的。
<!--ja-->
## 台に関する仮定

崩壊は、台とみなす集合 `X` から始まります。推移性は所属に関する閉性を表し、`isExt X`{.Agda} は、二つの台の要素が同じ台内の要素を持てば等しいと述べます。単射性に必要なのは後者だけです。
<!--/-->

Transitivity of a set, in the absoluteness-chapter shape; definitionally the
same predicate as the constructible chapter's `isTransV`, so a consumer's
transitivity witness passes through unchanged.

```agda
isTrans : S → Type (ℓ-suc ℓ)
isTrans u = Transitive 𝒮ᵥ (λ x → x ∈ˢ u)
```

Structure extensionality of a set: equal carrier members have equal comparisons
against the carrier's members. The collapse's injectivity half holds under this
hypothesis, without transitivity of the carrier.

```agda
isExt : S → Type (ℓ-suc ℓ)
isExt X = (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
        → x ≡ y
```

The collapse is defined by `∈`-recursion over the whole hierarchy, one step per
set: `π x` is the set of the `π`-images of the members of `x` that lie in the
carrier `X`.

```agda
module Collapse (X : S) where
```

<!--en-->
## The recursive collapse

For each set `x`, the map `π`{.Agda} collects the collapse values of those members of `x` that also lie in `X`. Well-founded recursion on ambient membership defines this map and supplies its computation law.
<!--zh-->
## 递归塌缩

对每个集合 `x`，映射 `π`{.Agda} 收集 `x` 中同时属于 `X` 的成员的塌缩值。环境隶属关系上的良基递归定义此映射，并给出其计算律。
<!--ja-->
## 再帰的な崩壊

各集合 `x` に対し、写像 `π`{.Agda} は `x` の要素のうち `X` にも属するものの崩壊値を集めます。周囲の所属関係上の整礎再帰がこの写像とその計算法則を与えます。
<!--/-->

The filtered small index: the small members of `x` that are small members of the
carrier. The filter uses the small membership, so `Fiber x` is small.

```agda
  Fiber : S → Type ℓ
  Fiber x = Σ[ m ∈ ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ m ∈ₛ X ⟩

  step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
  step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (member x (p .fst)))
```

Perf: the recursion unfolds to an accessibility eliminator; seal at birth,
computation law as the read lemma (R-36).

```agda
  opaque
    π : S → S
    π = ∈-induction step

  opaque
    unfolding π
    π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
    π-compute = ∈-induction-compute step
```

Every member of a collapse value is a collapse value of a member of the carrier;
the filter carries the carrier-membership witness.

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
## The transitive range

The image `πX`{.Agda} is formed from the small presentation of `X`. Every member of a collapse value is itself the collapse of an element of `X`, so this image is a transitive set and contains `π y`{.Agda} for every `y ∈ X`.
<!--zh-->
## 传递的像

像 `πX`{.Agda} 由 `X` 的小呈现构成。塌缩值的每个成员本身都是 `X` 中某元素的塌缩，因此这个像是传递集，并包含每个 `y ∈ X` 的 `π y`{.Agda}。
<!--ja-->
## 推移的な像

像 `πX`{.Agda} は `X` の小さな提示から作られます。崩壊値の各要素はそれ自身が `X` のある要素の崩壊なので、この像は推移的集合であり、各 `y ∈ X` に対する `π y`{.Agda} を含みます。
<!--/-->

The range as a set: the small members of the carrier, their collapse values
collected.

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

Membership forward: a member of a carrier member collapses into the collapsed
carrier member.

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
## Extensionality and the collapse isomorphism

Assuming `isExt X`{.Agda}, membership induction recovers an element of the carrier from its collapse value. Consequently `π`{.Agda} is injective on `X`, and membership in `X` agrees in both directions with membership between collapse values.
<!--zh-->
## 外延性与塌缩同构

假设 `isExt X`{.Agda}，隶属归纳可从塌缩值恢复载体元素。因此 `π`{.Agda} 在 `X` 上单射，并且 `X` 中的隶属关系与塌缩值之间的隶属关系双向相符。
<!--ja-->
## 外延性と崩壊同型

`isExt X`{.Agda} を仮定すると、所属に関する帰納法によって崩壊値から台の要素を復元できます。したがって `π`{.Agda} は `X` 上で単射となり、`X` 内の所属関係は崩壊値の間の所属関係と双方向に一致します。
<!--/-->

Extensional injectivity on the carrier; the carrier's structure extensionality
is a module parameter here and only here. The memberships the transitive proof
took from `Xtr` are carried by the fibers or by the extensionality
quantification, so no transitivity is needed.

```agda
  private
    π∈-recover : (x z : S) → ⟨ π z ∈ˢ π x ⟩
               → ((b : S) → b ∈ᵗ x → b ∈ᵗ X → π b ≡ π z → b ≡ z)
               → z ∈ᵗ x
    π∈-recover x z h same = PT.rec (snd (z ∈ˢ x))
      (λ { (p , q) → subst (λ w → ⟨ w ∈ˢ x ⟩)
        (same (⟪ x ⟫↪ (p .fst)) (member x (p .fst))
          (∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = X} .snd (p .snd)) q)
        (member x (p .fst)) })
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute x) h)

  module InjExt (Xext : isExt X) where

    P : S → Type (ℓ-suc ℓ)
    P x = (y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
```

Direction 1: move a member `z` of `x` into `y`; the hypothesis fires at `z ∈ x`.

```agda
    in⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ x → z ∈ᵗ X
        → π x ≡ π y
        → ((a : S) → a ∈ᵗ x → P a)
        → ⟨ z ∈ˢ y ⟩
    in⊆ x y z xu yu zx zu e IH = π∈-recover y z
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd x z zx zu))
      (λ b by bu q → sym (IH z zx b zu bu (sym q)))
```

Direction 2: move a member `z` of `y` into `x`; the hypothesis fires at the
witness `b ∈ x` extracted from the collapsed membership.

```agda
    out⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ y → z ∈ᵗ X
         → π y ≡ π x
         → ((a : S) → a ∈ᵗ x → P a)
         → ⟨ z ∈ˢ x ⟩
    out⊆ x y z xu yu zy zu e IH = π∈-recover x z
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd y z zy zu))
      (λ b bx bu q → IH b bx z bu zu q)

    step-inj : (x : S) → ((a : S) → a ∈ᵗ x → P a) → P x
    step-inj x IH y xu yu e = Xext x y xu yu to from
      where
      to : (z : S) → z ∈ᵗ X → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩
      to z zu zx = in⊆ x y z xu yu zx zu e IH
      from : (z : S) → z ∈ᵗ X → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
      from z zu zy = out⊆ x y z xu yu zy zu (sym e) IH
```

Extensional injectivity on the carrier, by `∈`-induction.

```agda
    π-inj : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
    π-inj = ∈-induction step-inj
```

The backward direction: a collapsed membership names a witness in the carrier
member, and injectivity identifies it.

```agda
    π∈-bwd : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩ → y ∈ᵗ x
    π∈-bwd x y xu yu h = π∈-recover x y h
      (λ b bx bu q → π-inj b y bu yu q)
```

The iso reading on the carrier, both directions.

```agda
    iso : (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩)
    iso x y xu yu = (λ yx → π∈-fwd x y yx yu) , π∈-bwd x y xu yu
```

The collapse is the unique solution of its recursion equation.

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
      step-eq = cong (sett (Fiber x)) (funExt ih')
        where
        ih' : (p : Fiber x) → π (⟪ x ⟫↪ (p .fst)) ≡ f (⟪ x ⟫↪ (p .fst))
        ih' p = IH (⟪ x ⟫↪ (p .fst)) (member x (p .fst))
```

Devlin 5.2(ii): if `Y ⊆ X` is transitive, the collapse fixes `Y` pointwise. The
filter on a member `y` of `Y` is full, because `Y` is transitive and `Y ⊆ X`, so
every member of `y` lies in `X`.

```agda
  fixes : (Y : S) → ⟨ Y ⊆ X ⟩ → isTrans Y → (y : S) → y ∈ᵗ Y → π y ≡ y
  fixes Y YX Ytr = ∈-induction stepF
    where
    stepF : (y : S) → ((m : S) → m ∈ᵗ y → m ∈ᵗ Y → π m ≡ m)
          → y ∈ᵗ Y → π y ≡ y
    stepF y IH yY = extensionalV (λ x → ⇔toPath (to x) (from x))
      where
      to : (x : S) → ⟨ x ∈ˢ π y ⟩ → x ∈ᵗ y
      to x xπ = PT.rec (snd (x ∈ˢ y)) go
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (π-compute y) xπ)
        where
        go : Σ[ p ∈ Fiber y ] (π (⟪ y ⟫↪ (p .fst)) ≡ x) → x ∈ᵗ y
        go (p , q) = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym ih' ∙ q) (member y (p .fst))
          where
          ih' : π (⟪ y ⟫↪ (p .fst)) ≡ ⟪ y ⟫↪ (p .fst)
          ih' = IH (⟪ y ⟫↪ (p .fst)) (member y (p .fst))
            (Ytr {x = y} {y = ⟪ y ⟫↪ (p .fst)} (member y (p .fst)) yY)

      from : (x : S) → x ∈ᵗ y → ⟨ x ∈ˢ π y ⟩
      from x xy = subst (λ w → ⟨ w ∈ˢ π y ⟩) (IH x xy x∈Y)
        (π∈-fwd y x xy x∈X)
        where
        x∈Y : x ∈ᵗ Y
        x∈Y = Ytr {x = y} {y = x} xy yY
        x∈X : x ∈ᵗ X
        x∈X = ∈∈ₛ {a = x} {b = X} .snd
          (YX x (∈∈ₛ {a = x} {b = Y} .fst x∈Y))
```

Devlin 5.2(ii) at the carrier itself.
