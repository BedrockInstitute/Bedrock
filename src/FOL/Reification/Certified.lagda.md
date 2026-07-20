# Certified representations

<!--en-->
The framework's graded tier, and its closing chapter. The assembly line so far
produces representations; the Levy chapters, read long ago, grade
formulas. This chapter welds the two: a **graded representation** is a triple,
formula, Δ₀ witness, adequacy, and the graded combinators run the flat
assembly line while composing the Δ₀ witnesses on the side. The chapter then
forges `transfer`{.Agda}, the composition of an adequacy certificate with the
absoluteness theorem: the one-line conversion of an inner-world predicate into
outer satisfaction. Like the rest of the framework, none of this has a consumer
in the trunk yet; `transfer` is the shape in which the framework is designed to
be spent, once the deeper chapters of Part 4 start paying the frontier.
<!--zh-->
框架的分级层，也是它的收官章。流水线至此生产表示；早先读过的 Lévy 诸章给公式分级。本章把两者焊接起来：**分级表示**是三元组：公式、Δ₀ 见证、适足性；分级组合子驱动平流水线，顺手复合 Δ₀ 见证。随后锻造 `transfer`{.Agda}：适足性证书与绝对性定理的复合，把内层世界的谓词一行换算为外层满足。与框架其余部分一样，这一切在主干上尚无消费者；`transfer` 是框架设计中被花费的形态，待第四部的深层章节开始偿付前沿时启用。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Reification.Certified where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; Transitive )
open import FOL.Syntax using ( Formula; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Absoluteness using ( module Single )
open import Cubical.Data.Vec using ( map )
```

<!--en-->
## Graded representations
<!--zh-->
## 分级表示
<!--/-->

<!--en-->
`forget₀`{.Agda} drops back to a plain representation by projection; each graded
combinator calls its flat counterpart and pairs adequacy with the Δ₀ witness, with the
naming pattern appending the grade as a subscript.
<!--zh-->
`forget₀`{.Agda} 经投影退回普通表示；每个分级组合子调用其平版同侪并把适足性与 Δ₀ 见证配对，命名模式以下标缀上级别。
<!--/-->

```agda
module Certified {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋)
                 {ℓc} (K : Type ℓc) (ι : K → ZFStructure.S 𝒮) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮
  open import FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )
  open At K ι using ( _⊨_ )
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
## The capstone: transfer
<!--zh-->
## 压轴：transfer
<!--/-->

<!--en-->
Everything composes. Fix the absoluteness chapter's setting, a propositional
structure with a transitive class, and take a graded representation living
inside the restricted world: its adequacy certificate and the absoluteness
theorem meet end to end, and a predicate on the inner world converts to
outer satisfaction in **one path composition**.
<!--zh-->
一切就此复合。固定绝对性章的场景，即带传递类的命题侧结构，取一份住在限制世界内的分级表示：它的适足性证书与绝对性定理首尾相接，内层世界上的谓词经**一次路径复合**换算为外层满足。
<!--/-->

```agda
module Transfer {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
                (M : ZFStructure.S 𝒮 → hProp ℓ)
                (trans : Transitive 𝒮 M) where

  open Single 𝒮 M trans using ( SM; 𝒮M; _⊨ᵛ_; abs₀; _^_ )

  module Inner = Certified (hPropAlgebra ℓ) 𝒮M SM id

  transfer : ∀ {n} {P : SM ^ n → hProp ℓ} (r : Inner.RepΔ₀ n P) (δ : SM ^ n)
           → P δ ≡ ((map fst δ) ⊨ᵛ (r .fst))
  transfer (φ , c , a) δ = sym (a δ) ∙ abs₀ c δ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Graded representations carry the Δ₀ witness alongside adequacy
(`RepΔ₀`{.Agda}), the graded combinators keep both books at once, and
`transfer`{.Agda} composes adequacy with absoluteness into the framework's
working currency. The framework is complete and idle, by design: its first
customers arrive with the chapters that pay the frontier.
<!--zh-->
分级表示让 Δ₀ 见证与适足性并肩随行 (`RepΔ₀`{.Agda})，分级组合子两本账同时记，`transfer`{.Agda} 把适足性与绝对性复合成框架的流通货币。框架完工而闲置，且是有意为之：它的第一批客户，随偿付前沿的那些章节到来。
<!--/-->
