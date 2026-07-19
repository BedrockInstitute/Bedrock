# Graded certificates

<!--en-->
Not every formula travels equally well. Take a set `x` in some sub-world `𝒮 ↾ M`
of a model (the structure chapter's restriction), and ask one question twice:
inside `M`, and in the full world. "Is `x` empty?" gets the same answer in both
places whenever members of members stay inside `M`: the formula `∀̇∈ x ⊥̇`
interrogates only the *members* of `x`, and none of them has escaped. But "is some
set disjoint from `x`?" quantifies over *everything*, and the witness the full
world has in mind may simply be missing from `M`. The difference shows in the
syntax alone: the first formula's quantifier is bounded, the second's is not. The
**Levy hierarchy** grades formulas by exactly this: **Δ₀** allows only bounded
quantifiers, Σ₁ prefixes existentials to a Δ₀ core, Π₁ prefixes universals. This
chapter makes the grades **certificates**: inductive data, purely syntactic,
portable across any constant domain, travelling with the formula they certify;
the next chapter proves the travel theorems they enable.
<!--zh-->
公式的旅行能力并不平等。取模型某个子世界 `𝒮 ↾ M` (结构章的限制) 中的一个集合 `x`，同一个问题问两遍：一遍在 `M` 里问，一遍在全世界问。「`x` 空吗？」只要成员的成员不出 `M`，两处答案就一致：公式 `∀̇∈ x ⊥̇` 只盘问 `x` 的**成员**，而它们谁也没有逃走。可「有集合与 `x` 不相交吗？」对**一切**量化，全世界心里想的那个见证可能恰好不在 `M` 中。这份差别单看语法就能看出：前一条公式的量词有界，后一条无界。**列维层级**恰按此给公式分级：**Δ₀** 只许有界量词，Σ₁ 在 Δ₀ 核心之前加存在量词，Π₁ 加全称量词。本章把级别做成**证书**：纯语法的归纳数据，对任意常量域可携，随其所证的公式旅行；它们所解锁的旅行定理由下一章证明。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Graded where

open import Base.Prelude
open import Base.Truth
open import FOL.Syntax using
  ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
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
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The Levy hierarchy lives as inductive certificates, Δ₀ by the absence of
unbounded constructors, Σ₁/Π₁ and the alternating Σₙ/Πₙ tower above it. The
certificates are pure syntax, and they stay put under a change of constant
domain, a fact catalogued with the relabelling kit at the book's tail. The
theorem that gives them their force is next.
<!--zh-->
列维层级以归纳证书的形态存在：Δ₀ 靠无界构造子的缺席，其上是 Σ₁/Π₁ 与交替的 Σₙ/Πₙ 之塔。证书是纯语法，且在常量改换下纹丝不动，这一事实编在书末的改换工具组里。赋予它们力量的定理在下一章。
<!--/-->
