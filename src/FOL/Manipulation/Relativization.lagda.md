<!--en-->
# Relativization

Relativization replaces each unbounded quantifier by one bounded by a chosen constant. The transformed formula is Δ₀, and its ordinary satisfaction agrees with a semantics in which the original formula’s unbounded quantifiers range only over members of the chosen set.
<!--zh-->
# 相对化

相对化把每个无界量词替换为受选定常元约束的量词。变换后的公式是 Δ₀，并且其通常满足关系与一种语义相符；在该语义中，原公式的无界量词只在选定集合的成员上取值。
<!--ja-->
# 相対化

相対化は、各非有界量化子を選んだ定数で有界化します。変換後の論理式は Δ₀ であり、その通常の充足関係は、元の論理式の非有界量化子を選んだ集合の要素だけにわたらせる意味論と一致します。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Relativization where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( con; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
```

<!--en-->
## The operator

`relativize c`{.Agda} leaves atoms and already bounded quantifiers unchanged, while replacing `∃̇` and `∀̇` by quantifiers bounded by `con c`{.Agda}. Because the bound is a constant, it passes beneath binders without any variable shifting.
<!--zh-->
## 算子

`relativize c`{.Agda} 保持原子公式与已有的有界量词不变，同时把 `∃̇` 和 `∀̇` 替换为受 `con c`{.Agda} 约束的量词。由于界是常元，进入约束子时无须随变量移动而调整。
<!--ja-->
## 演算子

`relativize c`{.Agda} は原子論理式と既に有界な量化子を変えず、`∃̇` と `∀̇` を `con c`{.Agda} で有界な量化子へ置き換えます。境界は定数なので、変数をずらさずに束縛子の下へ入れます。
<!--/-->



```agda
relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} → Formula K n → Formula K n
relativize c (t ∈̇ u)  = t ∈̇ u
relativize c (t ≐ u)  = t ≐ u
relativize c (φ ∧̇ ψ)  = relativize c φ ∧̇ relativize c ψ
relativize c (φ ∨̇ ψ)  = relativize c φ ∨̇ relativize c ψ
relativize c (φ ⇒̇ ψ)  = relativize c φ ⇒̇ relativize c ψ
relativize c ⊥̇        = ⊥̇
relativize c (∃̇ φ)    = ∃̇∈ (con c) (relativize c φ)
relativize c (∀̇ φ)    = ∀̇∈ (con c) (relativize c φ)
relativize c (∀̇∈ t φ) = ∀̇∈ t (relativize c φ)
relativize c (∃̇∈ t φ) = ∃̇∈ t (relativize c φ)
```

<!--en-->
Every unbounded quantifier became bounded and nothing else changed, so the result
has no `∃̇`/`∀̇` constructors at all: the Δ₀ witness assembles constructor by
constructor.
<!--zh-->
每个无界量词都变为有界量词，其余部分保持不变，因此结果不含任何 `∃̇`/`∀̇` 构造子；逐构造子装配即可得到所需的 Δ₀ 见证。
<!--/-->

```agda
Δ₀-relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} (φ : Formula K n) → Δ₀ (relativize c φ)
Δ₀-relativize c (t ∈̇ u)  = δ-∈
Δ₀-relativize c (t ≐ u)  = δ-≐
Δ₀-relativize c (φ ∧̇ ψ)  = δ-∧ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (φ ∨̇ ψ)  = δ-∨ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (φ ⇒̇ ψ)  = δ-⇒ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c ⊥̇        = δ-⊥
Δ₀-relativize c (∃̇ φ)    = δ-∃∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇ φ)    = δ-∀∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇∈ t φ) = δ-∀∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∃̇∈ t φ) = δ-∃∈ (Δ₀-relativize c φ)
```

<!--en-->
## Correctness

The comparison semantics interprets the original formula while restricting only its unbounded quantifiers to the value of the chosen bound. Structural induction shows that this is exactly the ordinary semantics of the relativized formula.
<!--zh-->
## 正确性

比较语义解释原公式，但只把其中的无界量词限制到所选界的取值。结构归纳表明，这恰好是相对化公式的通常语义。
<!--ja-->
## 正当性

比較用の意味論は元の論理式を解釈し、非有界量化子だけを選んだ境界の値へ制限します。構造帰納法により、これは相対化した論理式の通常の意味論とちょうど一致します。
<!--/-->



```agda
module Correct {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋)
               {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) (c : K) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮
  open module Sem = FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )
  open At K ι using ( _⊨_; ⟦_⟧ )

  A : S
  A = ι c

  infix 6 _⊨ᴬ_
  _⊨ᴬ_ : ∀ {n} → S ^ n → Formula K n → Ω
  γ ⊨ᴬ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (φ ∧̇ ψ)  = (γ ⊨ᴬ φ) ⊓ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ∨̇ ψ)  = (γ ⊨ᴬ φ) ⊔ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ⇒̇ ψ)  = (γ ⊨ᴬ φ) ⇒ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ ⊥̇        = ⊥
  γ ⊨ᴬ (∃̇ φ)    = ⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇ φ)    = ⋀ S (λ x → (x ∈ˢ A) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ᴬ φ))
```

<!--en-->
Correctness is then one structural induction: the standard meaning of
`relativize c φ` equals the `A`-bounded meaning of `φ`. The atoms are
`refl`{.Agda}; the two clauses the operator actually changes are exactly where the
standard semantics of `∃̇∈ (con c) _` unfolds, by computation, to the
companion's clause, since `⟦ con c ⟧ γ` is `A`; everything else is congruence.
<!--zh-->
正确性由结构归纳证明：`relativize c φ` 的标准含义等于 `φ` 的 `A`-有界含义。原子情形是 `refl`{.Agda}；算子实际改动的两个量词子句，正是标准语义按计算把 `∃̇∈ (con c) _` 展开为相应子句之处，因为 `⟦ con c ⟧ γ` 就是 `A`；其余情形都是同余。
<!--/-->

```agda
  relativize-correct : ∀ {n} (φ : Formula K n) (γ : S ^ n)
                     → (γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)
  relativize-correct (t ∈̇ u)  γ = refl
  relativize-correct (t ≐ u)  γ = refl
  relativize-correct (φ ∧̇ ψ)  γ = cong₂ _⊓_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (φ ∨̇ ψ)  γ = cong₂ _⊔_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (relativize-correct φ γ) (relativize-correct ψ γ)
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

`relativize`{.Agda} produces a Δ₀ formula, `Δ₀-relativize`{.Agda} records that complexity bound, and `relativize-correct`{.Agda} identifies its meaning with quantification inside the chosen set.
<!--zh-->
## 小结

`relativize`{.Agda} 产生 Δ₀ 公式，`Δ₀-relativize`{.Agda} 记录这一复杂度界，而 `relativize-correct`{.Agda} 将其含义识别为在选定集合内部量化。
<!--ja-->
## まとめ

`relativize`{.Agda} は Δ₀ 論理式を作り、`Δ₀-relativize`{.Agda} はその複雑さの上界を記録し、`relativize-correct`{.Agda} はその意味を選んだ集合の内部での量化と同定します。
<!--/-->
