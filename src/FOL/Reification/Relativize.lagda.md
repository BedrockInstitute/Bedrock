# Relativization

<!--en-->
The textbook's other classic move: **relativize** a formula to a bound, tightening
every unbounded quantifier `∃̇`, `∀̇` into its bounded counterpart. Two facts make
the operation valuable here. The result is always Δ₀, certificate included, so the
previous chapter's theorem applies to it; and when the bound denotes a transitive
set, satisfaction of the relativized formula in the big world coincides with
satisfaction of the original in the small one. Between them, "truth inside a set"
becomes a Δ₀ matter of the ambient world.
<!--zh-->
教科书的另一手经典操作：把公式**相对化**到一个界，将每个无界量词 `∃̇`、`∀̇` 收紧为对应的有界量词。两件事实使这一操作在此处值钱。其一，结果永远是 Δ₀，证书随附，于是上一章的定理对它适用；其二，当界指称一个传递集时，相对化公式在大世界的满足与原公式在小世界的满足重合。两相夹击，「集合内部的真」就化成了环境世界里的一桩 Δ₀ 事务。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Reification.Relativize where

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )
open import FOL.Syntax using
  ( con; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Reification.Graded using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
```

<!--en-->
## The operator
<!--zh-->
## 算子
<!--/-->

<!--en-->
The bound enters as a **constant** `c` of the domain: `con c`{.Agda} is a term at
every arity, so pushing the operator under binders needs no variable bookkeeping
whatsoever. Atoms and bounded quantifiers pass through untouched; only the two
unbounded constructors change clothes. A bound that is a proper class has no
constant to stand on, and lies beyond this operator's range; Part 4 meets that
wall head-on.
<!--zh-->
界以常量域中的**常量** `c` 进场：`con c`{.Agda} 在每个元数下都是词项，算子推进约束子之下不需要任何变量记账。原子与有界量词原样通过；只有两个无界构造子换装。真类之界没有常量可立足，超出本算子的射程；第四部将正面迎上那堵墙。
<!--/-->

```agda
relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} → Formula K n → Formula K n
relativize c (t ∈̇ u)  = t ∈̇ u
relativize c (t ≐ u)  = t ≐ u
relativize c (φ ∧̇ ψ)  = relativize c φ ∧̇ relativize c ψ
relativize c (φ ∨̇ ψ)  = relativize c φ ∨̇ relativize c ψ
relativize c (φ ⇒̇ ψ)  = relativize c φ ⇒̇ relativize c ψ
relativize c (¬̇ φ)    = ¬̇ relativize c φ
relativize c ⊤̇        = ⊤̇
relativize c ⊥̇        = ⊥̇
relativize c (∃̇ φ)    = ∃̇∈ (con c) (relativize c φ)
relativize c (∀̇ φ)    = ∀̇∈ (con c) (relativize c φ)
relativize c (∀̇∈ t φ) = ∀̇∈ t (relativize c φ)
relativize c (∃̇∈ t φ) = ∃̇∈ t (relativize c φ)
```

<!--en-->
Every unbounded quantifier became bounded and nothing else changed, so the result
has no `∃̇`/`∀̇` constructors at all: the Δ₀ certificate assembles constructor by
constructor.
<!--zh-->
每个无界量词都变有界，其余分毫未动，结果便不含任何 `∃̇`/`∀̇` 构造子：Δ₀ 证书逐构造子装配即得。
<!--/-->

```agda
Δ₀-relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} (φ : Formula K n) → Δ₀ (relativize c φ)
Δ₀-relativize c (t ∈̇ u)  = δ-∈
Δ₀-relativize c (t ≐ u)  = δ-≐
Δ₀-relativize c (φ ∧̇ ψ)  = δ-∧ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (φ ∨̇ ψ)  = δ-∨ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (φ ⇒̇ ψ)  = δ-⇒ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (¬̇ φ)    = δ-¬ (Δ₀-relativize c φ)
Δ₀-relativize c ⊤̇        = δ-⊤
Δ₀-relativize c ⊥̇        = δ-⊥
Δ₀-relativize c (∃̇ φ)    = δ-∃∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇ φ)    = δ-∀∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇∈ t φ) = δ-∀∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∃̇∈ t φ) = δ-∃∈ (Δ₀-relativize c φ)
```

<!--en-->
## Correctness
<!--zh-->
## 正确性
<!--/-->

<!--en-->
What should relativization mean? Fix a structure, an interpretation, and let `A`
be the bound's value. The intended reading of "φ relativized" is: evaluate φ as
usual, except that both unbounded quantifiers range over members of `A` only. That
reading is itself a semantics, a companion to the standard one differing in
exactly two clauses.
<!--zh-->
相对化该当何意？固定结构与解释，令 `A` 为界的取值。「φ 相对化」的本意是：照常求值 φ，唯独两个无界量词只在 `A` 的成员上取值。这个本意自身就是一套语义，与标准语义恰差两条子句的同伴。
<!--/-->

```agda
module Correct {ℓ ℓ'} (𝕋 : TruthAlg ℓ ℓ') (𝒮 : ZFStructure 𝕋)
               {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) (c : K) where

  open TruthAlg 𝕋
  open ZFStructure 𝒮
  open module Sem = FOL.Semantics 𝕋 𝒮 using ( module At )
  open At ι using ( _⊨_; ⟦_⟧ )

  A : S
  A = ι c

  infix 6 _⊨ᴬ_
  _⊨ᴬ_ : ∀ {n} → S ^ n → Formula K n → Ω
  γ ⊨ᴬ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (φ ∧̇ ψ)  = (γ ⊨ᴬ φ) ⊓ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ∨̇ ψ)  = (γ ⊨ᴬ φ) ⊔ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ⇒̇ ψ)  = (γ ⊨ᴬ φ) ⇒ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (¬̇ φ)    = ¬ (γ ⊨ᴬ φ)
  γ ⊨ᴬ ⊤̇        = ⊤
  γ ⊨ᴬ ⊥̇        = ⊥
  γ ⊨ᴬ (∃̇ φ)    = ⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇ φ)    = ⋀ S (λ x → (x ∈ˢ A) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ᴬ φ))
```

<!--en-->
Correctness is then one structural induction: the standard meaning of
`relativize c φ` equals the `A`-bounded meaning of `φ`. The atoms are
`refl`{.Agda}; the two clauses where the operator actually works are where the
standard semantics of `∃̇∈ (con c) _` unfolds, by computation, to exactly the
companion's clause, since `⟦ con c ⟧ γ` is `A`; everything else is congruence.
<!--zh-->
正确性于是就是一次结构归纳：`relativize c φ` 的标准含义等于 `φ` 的 `A`-有界含义。原子是 `refl`{.Agda}；算子真正动过手脚的两条子句，恰是标准语义对 `∃̇∈ (con c) _` 按计算展开成同伴子句之处，因为 `⟦ con c ⟧ γ` 就是 `A`；其余全是同余。
<!--/-->

```agda
  relativize-correct : ∀ {n} (φ : Formula K n) (γ : S ^ n)
                     → (γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)
  relativize-correct (t ∈̇ u)  γ = refl
  relativize-correct (t ≐ u)  γ = refl
  relativize-correct (φ ∧̇ ψ)  γ = cong₂ _⊓_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (φ ∨̇ ψ)  γ = cong₂ _⊔_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (¬̇ φ)    γ = cong ¬_ (relativize-correct φ γ)
  relativize-correct ⊤̇        γ = refl
  relativize-correct ⊥̇        γ = refl
  relativize-correct (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ A) ⊓ q) (relativize-correct φ (x ∷ γ))))
  relativize-correct (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ A) ⇒ q) (relativize-correct φ (x ∷ γ))))
  relativize-correct (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ ⟦ t ⟧ γ) ⇒ q) (relativize-correct φ (x ∷ γ))))
  relativize-correct (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ ⟦ t ⟧ γ) ⊓ q) (relativize-correct φ (x ∷ γ))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`relativize`{.Agda} tightens the unbounded quantifiers to a constant bound,
`Δ₀-relativize`{.Agda} certifies the result, and `relativize-correct`{.Agda} pins
its meaning to the bounded reading. With this, Part 1 closes: the object language,
its structures and semantics, the variable calculus, representations with their
certificate algebra, the graded hierarchy, absoluteness, and relativization. Every
later part of the book speaks through this toolkit; next, the axioms of set theory.
<!--zh-->
`relativize`{.Agda} 把无界量词收紧到常量界，`Δ₀-relativize`{.Agda} 为结果发证，`relativize-correct`{.Agda} 把它的含义钉在有界读法上。至此第一部收官：对象语言、其结构与语义、变量演算、表示与证书代数、分级层级、绝对性与相对化。本书此后各部都经这套工具箱说话；接下来，集合论的公理。
<!--/-->
