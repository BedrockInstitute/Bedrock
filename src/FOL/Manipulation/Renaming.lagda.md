# Renaming

<!--en-->
A tool stocked ahead of need: nothing in the trunk consumes it yet, and its
first consumers arrive with Part 4's deeper chapters. First, variables.

The syntax chapter pointed out an absence: no substitution, no weakening. The
quantifier clauses take bodies in an extended context directly, so the classical
apparatus for moving variables around never has to exist. What little variable
motion the book does need is covered by one device: **renaming**, a map
`ρ : Fin n → Fin m` pushed through a formula, with a single correctness theorem
that handles weakening, exchange, and contraction in one stroke.
<!--zh-->
一件提前备下的工具：主干至今没有消费它，首批消费者随第四部的深层章节到来。先说变量。

语法章点过一处缺席：没有替换，没有弱化。量词子句直接取扩展语境中的公式体，经典的那套变量搬运装置根本无需存在。本书确实需要的那一点变量挪动，由一个机件包办：**变量变换**，即沿公式推送一个映射 `ρ : Fin n → Fin m`，配一条正确性定理，弱化、交换、收缩一并了断。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Renaming where

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
```

<!--en-->
## The syntactic layer
<!--zh-->
## 语法层
<!--/-->

<!--en-->
Under a binder the renaming must step aside for the freshly bound variable:
`liftρ ρ` keeps variable `0` fixed and shifts everything else through `ρ`. With
that, pushing a renaming through terms and formulas is one clause per constructor;
note it moves only variables, leaving constants alone, exactly complementary to
the `mapFo`{.Agda} of the previous chapter.
<!--zh-->
进入约束子之下，变量变换须为新约束的变量让位：`liftρ ρ` 固定变量 `0`，其余经 `ρ` 平移。此后沿词项与公式推送变换就是一构造子一子句；注意它只动变量、不碰常量，与上一章的 `mapFo`{.Agda} 恰好互补。
<!--/-->

```agda
liftρ : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
liftρ ρ zero    = zero
liftρ ρ (suc i) = suc (ρ i)

renameTm : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Term K n → Term K m
renameTm ρ (con k) = con k
renameTm ρ (var i) = var (ρ i)

renameFo : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Formula K n → Formula K m
renameFo ρ (t ∈̇ u)  = renameTm ρ t ∈̇ renameTm ρ u
renameFo ρ (t ≐ u)  = renameTm ρ t ≐ renameTm ρ u
renameFo ρ (φ ∧̇ ψ)  = renameFo ρ φ ∧̇ renameFo ρ ψ
renameFo ρ (φ ∨̇ ψ)  = renameFo ρ φ ∨̇ renameFo ρ ψ
renameFo ρ (φ ⇒̇ ψ)  = renameFo ρ φ ⇒̇ renameFo ρ ψ
renameFo ρ (¬̇ φ)    = ¬̇ renameFo ρ φ
renameFo ρ ⊤̇        = ⊤̇
renameFo ρ ⊥̇        = ⊥̇
renameFo ρ (∃̇ φ)    = ∃̇ renameFo (liftρ ρ) φ
renameFo ρ (∀̇ φ)    = ∀̇ renameFo (liftρ ρ) φ
renameFo ρ (∀̇∈ t φ) = ∀̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
renameFo ρ (∃̇∈ t φ) = ∃̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
```

<!--en-->
## The semantic layer
<!--zh-->
## 语义层
<!--/-->

<!--en-->
When does renaming preserve meaning? Precisely when the two environments say the
same things to corresponding variables: `Agrees ρ γ δ` asks that looking up
`ρ i` in the big environment equals looking up `i` in the small one, and
`agrees∷`{.Agda} shows the condition survives pushing one new value onto both
sides, which is what happens under a binder. The development is generic over the
truth algebra, the structure, and the constant interpretation.
<!--zh-->
变量变换何时保含义？恰当两个环境对相应的变量说同样的话：`Agrees ρ γ δ` 要求在大环境里查 `ρ i` 等于在小环境里查 `i`；`agrees∷`{.Agda} 表明该条件经得起向两侧同时压入一个新值，即约束子之下发生的事。整个展开对真值代数、结构与常量解释都是泛型的。
<!--/-->

```agda
module Sat {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋)
           {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮

  private module Sem = FOL.Semantics 𝕋 𝒮
  open Sem.At {K = K} ι using ( _⊨_; ⟦_⟧ )

  Agrees : ∀ {n m} → (Fin n → Fin m) → S ^ m → S ^ n → Type ℓ
  Agrees ρ γ δ = ∀ i → lookup (ρ i) γ ≡ lookup i δ
```

<!--en-->
The correctness theorem: a renamed formula in the big environment means the same
as the original in the small one. Terms first, then the usual induction, every
case a congruence, the binder cases stepping through `agrees∷`{.Agda}. Weakening
(inserting an unused variable), exchange, and contraction are all instances,
obtained by choosing `ρ`.
<!--zh-->
正确性定理：变换后的公式在大环境中的含义，与原公式在小环境中的相同。先词项，然后照例归纳，每个情形一条同余，约束子情形踩着 `agrees∷`{.Agda} 过河。弱化 (插入未用的变量)、交换、收缩全是特例，取相应的 `ρ` 即得。
<!--/-->

```agda
  agrees∷ : ∀ {n m} {ρ : Fin n → Fin m} {γ : S ^ m} {δ : S ^ n}
            (x : S) → Agrees ρ γ δ → Agrees (liftρ ρ) (x ∷ γ) (x ∷ δ)
  agrees∷ x ag zero    = refl
  agrees∷ x ag (suc i) = ag i

  ⟦⟧-rename : ∀ {n m} (ρ : Fin n → Fin m) (t : Term K n)
              (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
            → ⟦ renameTm ρ t ⟧ γ ≡ ⟦ t ⟧ δ
  ⟦⟧-rename ρ (con k) γ δ ag = refl
  ⟦⟧-rename ρ (var i) γ δ ag = ag i

  ⊨-rename : ∀ {n m} (ρ : Fin n → Fin m) (φ : Formula K n)
             (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
           → (γ ⊨ renameFo ρ φ) ≡ (δ ⊨ φ)
  ⊨-rename ρ (t ∈̇ u)  γ δ ag = cong₂ _∈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (t ≐ u)  γ δ ag = cong₂ _≈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (φ ∧̇ ψ)  γ δ ag = cong₂ _⊓_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (φ ∨̇ ψ)  γ δ ag = cong₂ _⊔_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (φ ⇒̇ ψ)  γ δ ag = cong₂ _⇒_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (¬̇ φ)    γ δ ag = cong ¬_ (⊨-rename ρ φ γ δ ag)
  ⊨-rename ρ ⊤̇        γ δ ag = refl
  ⊨-rename ρ ⊥̇        γ δ ag = refl
  ⊨-rename ρ (∃̇ φ)    γ δ ag = cong (⋁ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
  ⊨-rename ρ (∀̇ φ)    γ δ ag = cong (⋀ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
  ⊨-rename ρ (∀̇∈ t φ) γ δ ag = cong (⋀ S) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
  ⊨-rename ρ (∃̇∈ t φ) γ δ ag = cong (⋁ S) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Renaming is the book's entire variable calculus: `renameFo`{.Agda} on syntax,
`⊨-rename`{.Agda} on meaning, with `Agrees`{.Agda} naming the exact condition under
which nothing changes. The book's variable machinery now exists, once and in
full, ahead of the heavy consumers waiting in Part 4.
<!--zh-->
变量变换就是本书全部的变量演算：语法上 `renameFo`{.Agda}，含义上 `⊨-rename`{.Agda}，`Agrees`{.Agda} 点明了「什么都不变」的确切条件。本书的变量机件至此一次到位、整装完毕，静候第四部那些重量级消费者。
<!--/-->
