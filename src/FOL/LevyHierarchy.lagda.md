<!--en-->
# The Lévy hierarchy

The Lévy hierarchy classifies formulas by their unbounded quantifiers. This chapter represents membership in Δ₀, Σ₁, and Π₁ by explicit syntax certificates, provides a Boolean checker for Δ₀ formulas, and extends the classification to every finite level.
<!--zh-->
# 莱维层级

莱维层级按照公式中的无界量词分类。本章用显式语法证书表示公式属于 Δ₀、Σ₁ 与 Π₁，给出 Δ₀ 公式的布尔检查器，并把分类推广到每个有限层级。
<!--ja-->
# レヴィ階層

レヴィ階層は、非有界量化子によって論理式を分類します。本章では Δ₀、Σ₁、Π₁ への所属を明示的な構文の証拠で表し、Δ₀ 論理式のブール判定器を与え、分類をすべての有限レベルへ拡張します。
<!--/-->

<!--en-->
Not every formula travels equally well. Take a set `x` in some sub-world `𝒮 ↾ M`
of a model (the structure chapter's restriction), and ask one question twice:
inside `M`, and in the full world. "Is `x` empty?" gets the same answer in both
places whenever members of members stay inside `M`: the formula `∀̇∈ x ⊥̇`
interrogates only the *members* of `x`, and none of them has escaped. But "is some
set disjoint from `x`?" quantifies over *everything*, and the witness the full
world has in mind may simply be missing from `M`. The difference shows in the
syntax alone: the first formula's quantifier is bounded, the second's is not. The
**Lévy hierarchy** grades formulas by exactly this: **Δ₀** allows only bounded
quantifiers, Σ₁ prefixes existentials to a Δ₀ core, Π₁ prefixes universals. This
chapter makes the grades **witnesses**: inductive data, purely syntactic,
portable across any constant domain, travelling with the formula they certify;
the next chapter proves the travel theorems they enable.
<!--zh-->
公式的旅行能力并不平等。取模型某个子世界 `𝒮 ↾ M` (结构章的限制) 中的一个集合 `x`，同一个问题问两遍：一遍在 `M` 里问，一遍在全世界问。「`x` 空吗？」只要成员的成员不出 `M`，两处答案就一致：公式 `∀̇∈ x ⊥̇` 只盘问 `x` 的**成员**，而它们谁也没有逃走。可「有集合与 `x` 不相交吗？」对**一切**量化，全世界心里想的那个见证可能恰好不在 `M` 中。这份差别单看语法就能看出：前一条公式的量词有界，后一条无界。**Lévy 层级**恰按此给公式分级：**Δ₀** 只许有界量词，Σ₁ 在 Δ₀ 核心之前加存在量词，Π₁ 加全称量词。本章把级别做成**见证**：纯语法的归纳数据，对任意常元域都可携，随其所证的公式旅行；它们所解锁的旅行定理由下一章证明。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.LevyHierarchy where

open import Base.Prelude
open import Base.Truth
open import Cubical.Data.Bool using ( Bool; true; false; _and_; Bool→Type )
open import Cubical.Data.Unit using ( tt )
open import FOL.Syntax using
  ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

<!--en-->
## The Δ₀ witness

One constructor per permitted formula shape, and none for `∃̇` or `∀̇`: **absence
is the classification**. A `Δ₀ φ`{.Agda} inhabitant is a machine-checkable witness
that every quantifier in `φ` is bounded.
<!--zh-->
## Δ₀ 见证

每个获准的公式形状对应一个构造子，而 `∃̇` 与 `∀̇` 没有：**缺席即分类**。`Δ₀ φ`{.Agda} 的居民就是「`φ` 的每个量词都有界」的机器可查见证。
<!--ja-->
## Δ₀ の証拠

`Δ₀ φ`{.Agda} は、`φ` の量化子がすべて集合によって有界であることを構文に沿って証明します。原子式と結合子は閉じ、非有界な `∃̇` と `∀̇` には構成子を与えません。
<!--/-->



```agda
data Δ₀ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
  δ-∈  : ∀ {n} {t u : Term K n} → Δ₀ (t ∈̇ u)
  δ-≐  : ∀ {n} {t u : Term K n} → Δ₀ (t ≐ u)
  δ-∧  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∧̇ ψ)
  δ-∨  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ∨̇ ψ)
  δ-⇒  : ∀ {n} {φ ψ : Formula K n} → Δ₀ φ → Δ₀ ψ → Δ₀ (φ ⇒̇ ψ)
  δ-⊥  : ∀ {n} → Δ₀ {n = n} ⊥̇
  δ-∀∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∀̇∈ t φ)
  δ-∃∈ : ∀ {n} {t : Term K n} {φ : Formula K (suc n)} → Δ₀ φ → Δ₀ (∃̇∈ t φ)

δ-¬ : ∀ {ℓc} {K : Type ℓc} {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (¬̇ φ)
δ-¬ d = δ-⇒ d δ-⊥

δ-⊤ : ∀ {ℓc} {K : Type ℓc} {n} → Δ₀ {K = K} {n = n} ⊤̇
δ-⊤ = δ-⇒ δ-⊥ δ-⊥
```

<!--en-->
## Checking concrete formulas

A Boolean traversal recognizes bounded formulas. Its soundness proof builds the
same `Δ₀` witness as a manual constructor tree. For a concrete bounded formula,
`checkΔ₀ φ tt` lets normalization verify the classification; variable terms do
not affect the result.
<!--zh-->
## 检查具体公式

一次布尔遍历识别有界公式。可靠性证明构造的仍是手写构造子树所给出的 `Δ₀` 见证。对于具体的有界公式，`checkΔ₀ φ tt` 让归一化来核验分级；含变量的项不影响结果。
<!--ja-->
## 具体的な論理式を判定する

`bounded`{.Agda} は論理式を走査して非有界量化子の有無をブール値で調べます。結果が真である証拠から `checkΔ₀`{.Agda} が正式な `Δ₀` 証拠を構成します。
<!--/-->

```agda
bounded : ∀ {ℓc} {K : Type ℓc} {n} → Formula K n → Bool
bounded (t ∈̇ u) = true
bounded (t ≐ u) = true
bounded (φ ∧̇ ψ) = bounded φ and bounded ψ
bounded (φ ∨̇ ψ) = bounded φ and bounded ψ
bounded (φ ⇒̇ ψ) = bounded φ and bounded ψ
bounded ⊥̇ = true
bounded (∃̇ φ) = false
bounded (∀̇ φ) = false
bounded (∀̇∈ t φ) = bounded φ
bounded (∃̇∈ t φ) = bounded φ

private
  and-out : (a b : Bool) → Bool→Type (a and b) → Bool→Type a × Bool→Type b
  and-out false b ()
  and-out true b h = tt , h

checkΔ₀ : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Bool→Type (bounded φ) → Δ₀ φ
checkΔ₀ (t ∈̇ u) h = δ-∈
checkΔ₀ (t ≐ u) h = δ-≐
checkΔ₀ (φ ∧̇ ψ) h = δ-∧ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
checkΔ₀ (φ ∨̇ ψ) h = δ-∨ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
checkΔ₀ (φ ⇒̇ ψ) h = δ-⇒ (checkΔ₀ φ (p .fst)) (checkΔ₀ ψ (p .snd))
  where p = and-out (bounded φ) (bounded ψ) h
checkΔ₀ ⊥̇ h = δ-⊥
checkΔ₀ (∃̇ φ) ()
checkΔ₀ (∀̇ φ) ()
checkΔ₀ (∀̇∈ t φ) h = δ-∀∈ (checkΔ₀ φ h)
checkΔ₀ (∃̇∈ t φ) h = δ-∃∈ (checkΔ₀ φ h)
```

<!--en-->
## Σ₁ and Π₁

One unbounded quantifier kind each, stacked on a Δ₀ core.
<!--zh-->
## Σ₁ 与 Π₁

各在 Δ₀ 核心之上叠一种无界量词。
<!--ja-->
## Σ₁ と Π₁

Σ₁ 論理式は Δ₀ 行列式の前に有限個の存在量化子を置いたもの、Π₁ 論理式は有限個の全称量化子を置いたものとして記録します。この形が絶対性の向きを決めます。
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

Σ₁ and Π₁ are the first floor of an alternating tower: Σₙ₊₁ stacks existential
blocks on Πₙ, Πₙ₊₁ stacks universal blocks on Σₙ, and Δ₀ sits inside every level.
the constructible-universe reflection arguments will climb this tower level by level; the
constructors follow the same one-quantifier-per-step pattern, with `σ-Π` and
`π-Σ` providing the alternation.
<!--zh-->
## 一般层级

Σ₁ 与 Π₁ 是一座交替之塔的第一层：Σₙ₊₁ 在 Πₙ 上叠存在块，Πₙ₊₁ 在 Σₙ 上叠全称块，Δ₀ 坐落于每一级之内。可构造宇宙的反射论证将沿这座塔逐级攀升；构造子沿用一步一量词的模式，`σ-Π` 与 `π-Σ` 提供交替升级。
<!--ja-->
## 一般のレヴィ階層

極性を交互に変えながら量化子ブロックを追加し、Σₙ と Πₙ を再帰的に定義します。低いレベルの証拠を次のレベルへ持ち上げる包含も同時に得られます。
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

The Lévy hierarchy lives as inductive witnesses, Δ₀ by the absence of
unbounded constructors, Σ₁/Π₁ and the alternating Σₙ/Πₙ tower above it. The
witnesses are pure syntax, and they stay put under a change of constant
domain, a fact catalogued with the relabelling kit at the book's tail. The
theorem that gives them their force is next.
<!--zh-->
## 小结

Lévy 层级以归纳见证的形态存在：Δ₀ 靠无界构造子的缺席，其上是 Σ₁/Π₁ 与交替的 Σₙ/Πₙ 之塔。这些见证是纯语法，且在常元改名下纹丝不动，这一事实编在书末的常元改名工具组里。赋予它们力量的定理在下一章给出。
<!--ja-->
## まとめ

Δ₀ は有界量化だけを許し、Σ₁ と Π₁ はその前に一種類の非有界量化を加えます。証拠をデータとして持つため、後の絶対性証明は論理式の形を安全に利用できます。
<!--/-->
