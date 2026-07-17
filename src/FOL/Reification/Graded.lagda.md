# Graded certificates

<!--en-->
The **Levy hierarchy** classifies formulas by quantifier complexity: **Δ₀** allows
only bounded quantifiers, Σ₁ prefixes existentials to a Δ₀ core, Π₁ prefixes
universals. The classification matters because of a textbook theorem the next
chapter proves: Δ₀ formulas keep their meaning between a transitive class and the
full universe, Σ₁ transfer upward, Π₁ downward. This chapter makes the hierarchy
itself a **certificate**: an inductive datum, purely syntactic, portable across any
constant domain, that travels with a formula the way adequacy certificates do.
<!--zh-->
**列维层级**按量词复杂度为公式分类：**Δ₀** 只许有界量词，Σ₁ 在 Δ₀ 核心之前加存在量词，Π₁ 加全称量词。这个分类之所以要紧，在于下一章将证明的教科书定理：Δ₀ 公式在传递类与全宇宙之间含义不变，Σ₁ 向上转移，Π₁ 向下。本章把层级本身做成**证书**：纯语法层面的归纳数据，对任意常量域可携，像适足性证书一样随公式旅行。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Reification.Graded where

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )
open import FOL.Syntax using
  ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈; mapFo )
```

<!--en-->
## The Δ₀ certificate
<!--zh-->
## Δ₀ 证书
<!--/-->

<!--en-->
One constructor per permitted formula shape, and none for `∃̇` or `∀̇`: **absence
is the classification**. A `Δ₀ φ`{.Agda} inhabitant is a machine-checkable witness
that every quantifier in `φ` is bounded.
<!--zh-->
每个获准的公式形状一个构造子，而 `∃̇` 与 `∀̇` 没有：**缺席即分类**。`Δ₀ φ`{.Agda} 的居民就是「`φ` 的每个量词都有界」的机器可查见证。
<!--/-->

```agda
data Δ₀ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  δ-∈  : ∀ {n} {t u : Term K n} → Δ₀ (t ∈̇ u)
  δ-≐  : ∀ {n} {t u : Term K n} → Δ₀ (t ≐ u)
  δ-∧  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∧̇ ψ)
  δ-∨  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∨̇ ψ)
  δ-⇒  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ⇒̇ ψ)
  δ-¬  : ∀ {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (¬̇ φ)
  δ-⊤  : ∀ {n} → Δ₀ {n = n} ⊤̇
  δ-⊥  : ∀ {n} → Δ₀ {n = n} ⊥̇
  δ-∀∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∀̇∈ t φ)
  δ-∃∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∃̇∈ t φ)
```

<!--en-->
Relabelling constants preserves the structure of a formula, so the certificate
follows along, constructor by constructor. This little lemma is what lets an
absoluteness argument carry a Δ₀ witness across a change of constant domain.
<!--zh-->
重标记常量保持公式的结构，证书遂逐构造子随行。这条小引理让绝对性论证得以携着 Δ₀ 见证跨越常量域的更换。
<!--/-->

```agda
mapΔ₀ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (mapFo f φ)
mapΔ₀ f δ-∈ = δ-∈
mapΔ₀ f δ-≐ = δ-≐
mapΔ₀ f (δ-∧ c d) = δ-∧ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-∨ c d) = δ-∨ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-⇒ c d) = δ-⇒ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-¬ c)   = δ-¬ (mapΔ₀ f c)
mapΔ₀ f δ-⊤ = δ-⊤
mapΔ₀ f δ-⊥ = δ-⊥
mapΔ₀ f (δ-∀∈ c) = δ-∀∈ (mapΔ₀ f c)
mapΔ₀ f (δ-∃∈ c) = δ-∃∈ (mapΔ₀ f c)
```

<!--en-->
## Σ₁ and Π₁
<!--zh-->
## Σ₁ 与 Π₁
<!--/-->

<!--en-->
One unbounded quantifier kind each, stacked on a Δ₀ core.
<!--zh-->
各在 Δ₀ 核心之上叠一种无界量词。
<!--/-->

```agda
data Σ₁ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  σ-Δ₀ : ∀ {n} {φ : Formula K n} → Δ₀ φ → Σ₁ φ
  σ-∃  : ∀ {n} {φ : Formula K (suc n)} → Σ₁ φ → Σ₁ (∃̇ φ)

data Π₁ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  π-Δ₀ : ∀ {n} {φ : Formula K n} → Δ₀ φ → Π₁ φ
  π-∀  : ∀ {n} {φ : Formula K (suc n)} → Π₁ φ → Π₁ (∀̇ φ)
```

<!--en-->
## The general hierarchy
<!--zh-->
## 一般层级
<!--/-->

<!--en-->
Σ₁ and Π₁ are the first floor of an alternating tower: Σₙ₊₁ stacks existential
blocks on Πₙ, Πₙ₊₁ stacks universal blocks on Σₙ, and Δ₀ sits inside every level.
Part 4's reflection arguments will climb this tower level by level; the
constructors follow the same one-quantifier-per-step pattern, with `σ-Π` and
`π-Σ` providing the alternation.
<!--zh-->
Σ₁ 与 Π₁ 是一座交替之塔的第一层：Σₙ₊₁ 在 Πₙ 上叠存在块，Πₙ₊₁ 在 Σₙ 上叠全称块，Δ₀ 坐落于每一级之内。第四部的反射论证将沿这座塔逐级攀升；构造子沿用一步一量词的模式，`σ-Π` 与 `π-Σ` 提供交替升级。
<!--/-->

```agda
mutual
  data Σₙ {ℓc} {K : Type ℓc} : ℕ → ∀ {n} → Formula K n → Type ℓc where
    σ-Δ₀ : ∀ {k n} {φ : Formula K n} → Δ₀ φ → Σₙ k φ
    σ-Π  : ∀ {k n} {φ : Formula K n} → Πₙ k φ → Σₙ (suc k) φ
    σ-∃  : ∀ {k n} {φ : Formula K (suc n)} → Σₙ (suc k) φ → Σₙ (suc k) (∃̇ φ)

  data Πₙ {ℓc} {K : Type ℓc} : ℕ → ∀ {n} → Formula K n → Type ℓc where
    π-Δ₀ : ∀ {k n} {φ : Formula K n} → Δ₀ φ → Πₙ k φ
    π-Σ  : ∀ {k n} {φ : Formula K n} → Σₙ k φ → Πₙ (suc k) φ
    π-∀  : ∀ {k n} {φ : Formula K (suc n)} → Πₙ (suc k) φ → Πₙ (suc k) (∀̇ φ)
```

<!--en-->
The relabelling lemma extends to the tower by mutual induction, reusing
`mapΔ₀`{.Agda} at the leaves.
<!--zh-->
重标记引理经互归纳延伸到整座塔，叶位复用 `mapΔ₀`{.Agda}。
<!--/-->

```agda
mutual
  mapΣₙ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
          {k n} {φ : Formula K n} → Σₙ k φ → Σₙ k (mapFo f φ)
  mapΣₙ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
  mapΣₙ f (σ-Π p)  = σ-Π (mapΠₙ f p)
  mapΣₙ f (σ-∃ s)  = σ-∃ (mapΣₙ f s)

  mapΠₙ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
          {k n} {φ : Formula K n} → Πₙ k φ → Πₙ k (mapFo f φ)
  mapΠₙ f (π-Δ₀ d) = π-Δ₀ (mapΔ₀ f d)
  mapΠₙ f (π-Σ s)  = π-Σ (mapΣₙ f s)
  mapΠₙ f (π-∀ p)  = π-∀ (mapΠₙ f p)
```

<!--en-->
## Graded representations
<!--zh-->
## 分级表示
<!--/-->

<!--en-->
Bundling one step further: a **graded representation** is a triple, formula, Δ₀
certificate, adequacy. `forget₀`{.Agda} drops back to a plain representation by
projection, and the graded combinators run the flat factory of the previous
chapter while composing the Δ₀ evidence on the side; the naming pattern appends
the grade as a subscript.
<!--zh-->
再进一步捆绑：**分级表示**是三元组：公式、Δ₀ 证书、适足性。`forget₀`{.Agda} 经投影退回普通表示；分级组合子驱动上一章的平车间，顺手复合 Δ₀ 证据；命名模式以下标缀上级别。
<!--/-->

```agda
module Certified {ℓ ℓ'} (𝕋 : TruthAlg ℓ ℓ') (𝒮 : ZFStructure 𝕋)
                 {ℓc} (K : Type ℓc) (ι : K → ZFStructure.S 𝒮) where

  open TruthAlg 𝕋
  open ZFStructure 𝒮
  open import FOL.Semantics 𝕋 𝒮 using ( module At )
  open At ι using ( _⊨_ )
  open import FOL.Reification.Combinators 𝕋 𝒮 K ι using
    ( RepP; RepS; ∈-rep; ≐-rep; ∧-rep; ∨-rep; ⇒-rep; ¬-rep; ⊤-rep; ⊥-rep
    ; ∀∈-rep; ∃∈-rep )

  RepΔ₀ : (n : ℕ) → (S ^ n → Ω) → Type (ℓ-max ℓc (ℓ-max ℓ ℓ'))
  RepΔ₀ n P = Σ[ φ ∈ Formula K n ] (Δ₀ φ × (∀ γ → (γ ⊨ φ) ≡ P γ))

  forget₀ : ∀ {n} {P : S ^ n → Ω} → RepΔ₀ n P → RepP n P
  forget₀ (φ , _ , a) = φ , a

  ∈-rep₀ : ∀ {n} {a b : S ^ n → S} → RepS n a → RepS n b
         → RepΔ₀ n (λ γ → a γ ∈ˢ b γ)
  ∈-rep₀ ra rb = ∈-rep ra rb .fst , δ-∈ , ∈-rep ra rb .snd

  ≐-rep₀ : ∀ {n} {a b : S ^ n → S} → RepS n a → RepS n b
         → RepΔ₀ n (λ γ → a γ ≈ˢ b γ)
  ≐-rep₀ ra rb = ≐-rep ra rb .fst , δ-≐ , ≐-rep ra rb .snd

  ∧-rep₀ : ∀ {n} {P Q : S ^ n → Ω} → RepΔ₀ n P → RepΔ₀ n Q
         → RepΔ₀ n (λ γ → P γ ⊓ Q γ)
  ∧-rep₀ (φ , c , a) (ψ , d , b) = (φ ∧̇ ψ) , δ-∧ c d , ∧-rep (φ , a) (ψ , b) .snd

  ∨-rep₀ : ∀ {n} {P Q : S ^ n → Ω} → RepΔ₀ n P → RepΔ₀ n Q
         → RepΔ₀ n (λ γ → P γ ⊔ Q γ)
  ∨-rep₀ (φ , c , a) (ψ , d , b) = (φ ∨̇ ψ) , δ-∨ c d , ∨-rep (φ , a) (ψ , b) .snd

  ⇒-rep₀ : ∀ {n} {P Q : S ^ n → Ω} → RepΔ₀ n P → RepΔ₀ n Q
         → RepΔ₀ n (λ γ → P γ ⇒ Q γ)
  ⇒-rep₀ (φ , c , a) (ψ , d , b) = (φ ⇒̇ ψ) , δ-⇒ c d , ⇒-rep (φ , a) (ψ , b) .snd

  ¬-rep₀ : ∀ {n} {P : S ^ n → Ω} → RepΔ₀ n P → RepΔ₀ n (λ γ → ¬ P γ)
  ¬-rep₀ (φ , c , a) = (¬̇ φ) , δ-¬ c , ¬-rep (φ , a) .snd

  ⊤-rep₀ : ∀ {n} → RepΔ₀ n (λ _ → ⊤)
  ⊤-rep₀ = ⊤̇ , δ-⊤ , ⊤-rep .snd

  ⊥-rep₀ : ∀ {n} → RepΔ₀ n (λ _ → ⊥)
  ⊥-rep₀ = ⊥̇ , δ-⊥ , ⊥-rep .snd

  ∀∈-rep₀ : ∀ {n} {a : S ^ n → S} {P : S ^ suc n → Ω}
          → RepS n a → RepΔ₀ (suc n) P
          → RepΔ₀ n (λ γ → ⋀ S (λ x → (x ∈ˢ a γ) ⇒ P (x ∷ γ)))
  ∀∈-rep₀ rt (φ , c , a) = ∀̇∈ (rt .fst) φ , δ-∀∈ c , ∀∈-rep rt (φ , a) .snd

  ∃∈-rep₀ : ∀ {n} {a : S ^ n → S} {P : S ^ suc n → Ω}
          → RepS n a → RepΔ₀ (suc n) P
          → RepΔ₀ n (λ γ → ⋁ S (λ x → (x ∈ˢ a γ) ⊓ P (x ∷ γ)))
  ∃∈-rep₀ rt (φ , c , a) = ∃̇∈ (rt .fst) φ , δ-∃∈ c , ∃∈-rep rt (φ , a) .snd
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The Levy hierarchy lives as inductive certificates, Δ₀ by the absence of unbounded
constructors, Σ₁/Π₁ and the alternating Σₙ/Πₙ tower above it, all stable under
constant relabelling; graded representations carry the Δ₀ witness alongside
adequacy. The certificates are pure syntax; the theorem that gives them their
force is next.
<!--zh-->
列维层级以归纳证书的形态存在：Δ₀ 靠无界构造子的缺席，其上是 Σ₁/Π₁ 与交替的 Σₙ/Πₙ 之塔，全体在常量重标记下稳定；分级表示让 Δ₀ 见证与适足性并肩随行。证书是纯语法；赋予它们力量的定理在下一章。
<!--/-->
