<!--en-->
# Constant relabelling

Changing the constant domain acts structurally on formulas without changing their logical shape. This chapter proves that evaluation commutes with that action and that witnesses in the Lévy hierarchy survive it.
<!--zh-->
# 常元改名

更换常元域会按结构作用于公式，而不改变其逻辑形状。本章证明求值与这一作用可交换，并且 Lévy 层级中的见证在此作用下得以保持。
<!--ja-->
# 定数の改名

定数域の変更は論理式へ構造的に作用し、その論理的な形を変えません。本章では、評価がこの作用と可換であり、Lévy 階層の証人が保存されることを示します。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Relabelling where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo; embed )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈
  ; Σₙ; σ-Δ₀; σ-Π; σ-∃; Πₙ; π-Δ₀; π-Σ; π-∀ )
import FOL.Semantics
import Cubical.Data.Empty as Empty
```

<!--en-->
## Meaning level

Evaluating a relabelled formula under `ι` is the same as evaluating the original under the composite interpretation `ι ∘ f`. Structural induction proves the corresponding statements for term denotation and formula satisfaction, including the parameter-free embedding as a corollary.
<!--zh-->
## 含义层

在 `ι` 下求值经常元改名的公式，等同于在复合解释 `ι ∘ f` 下求值原公式。结构归纳证明词项释义与公式满足关系的对应陈述，并以无参嵌入为推论。
<!--ja-->
## 意味の水準

定数を改名した論理式を `ι` の下で評価することは、元の論理式を合成解釈 `ι ∘ f` の下で評価することと同じです。構造帰納法により、項の表示と論理式の充足関係について対応する主張が得られ、パラメータなしの埋め込みも系として従います。
<!--/-->



```agda
module _ {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮
  open FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )

  module _ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K') (ι : K' → S) where

    open At K' ι using ( _⊨_; ⟦_⟧ )
    open At K (λ k → ι (f k)) using () renaming ( _⊨_ to _⊨∘_ ; ⟦_⟧ to ⟦_⟧∘ )

    ⟦⟧-map : ∀ {n} (t : Term K n) (γ : S ^ n)
           → ⟦ mapTm f t ⟧ γ ≡ ⟦ t ⟧∘ γ
    ⟦⟧-map (con k) γ = refl
    ⟦⟧-map (var i) γ = refl

    ⊨-map : ∀ {n} (φ : Formula K n) (γ : S ^ n)
          → (γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)
    ⊨-map (t ∈̇ u)  γ = cong₂ _∈ˢ_ (⟦⟧-map t γ) (⟦⟧-map u γ)
    ⊨-map (t ≐ u)  γ = cong₂ _≈ˢ_ (⟦⟧-map t γ) (⟦⟧-map u γ)
    ⊨-map (φ ∧̇ ψ)  γ = cong₂ _⊓_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map (φ ∨̇ ψ)  γ = cong₂ _⊔_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (⊨-map φ γ) (⊨-map ψ γ)
    ⊨-map ⊥̇        γ = refl
    ⊨-map (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
    ⊨-map (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
    ⊨-map (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
      cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
    ⊨-map (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
      cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
```

<!--en-->
The corollary for parameter-free formulas: entering any
constant domain through `embed`{.Agda} keeps their meaning. The data axis and
the working syntax share one semantics, so nothing needs proving twice. (The
`∅`-marked satisfaction reads the empty constant domain through
`Empty.rec*`{.Agda}.)
<!--zh-->
由此得到关于无参公式的推论：经 `embed`{.Agda} 进入任何常元域后，公式的含义不变。数据轴与工作语法共享同一套语义，因此无需把任何结论证明两遍。(带 `∅` 标记的满足经 `Empty.rec*`{.Agda} 解读空常元域。)
<!--/-->

```agda
  module _ {ℓe ℓc} {K : Type ℓc} (ι : K → S) where

    open At K ι using ( _⊨_ )
    open At (⊥* {ℓe}) (λ b → ι (Empty.rec* b)) using () renaming ( _⊨_ to _⊨∅_ )

    embed-⊨ : ∀ {n} (φ : Formula (⊥* {ℓe}) n) (γ : S ^ n)
            → (γ ⊨ embed φ) ≡ (γ ⊨∅ φ)
    embed-⊨ = ⊨-map Empty.rec* ι
```

<!--en-->
## Levy witness level

Constant relabelling leaves every connective and quantifier in place, so it transports Δ₀ witnesses constructor by constructor. Mutual induction extends the same fact through the alternating Σ and Π levels of the Lévy hierarchy.
<!--zh-->
## Lévy 见证层

常元改名保持每个联结词与量词的位置，因此可逐构造子搬运 Δ₀ 见证。互归纳把这一事实扩展到 Lévy 层级中交替的 Σ 与 Π 各层。
<!--ja-->
## Lévy 証人の水準

定数の改名は結合子と量化子をすべてそのまま保つため、Δ₀ の証人を構成子ごとに移せます。相互帰納法によって、同じ事実が Lévy 階層で交互に現れる Σ と Π の各水準へ拡張されます。
<!--/-->



```agda
mapΔ₀ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Δ₀ φ → Δ₀ (mapFo f φ)
mapΔ₀ f δ-∈ = δ-∈
mapΔ₀ f δ-≐ = δ-≐
mapΔ₀ f (δ-∧ c d) = δ-∧ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-∨ c d) = δ-∨ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f (δ-⇒ c d) = δ-⇒ (mapΔ₀ f c) (mapΔ₀ f d)
mapΔ₀ f δ-⊥ = δ-⊥
mapΔ₀ f (δ-∀∈ c) = δ-∀∈ (mapΔ₀ f c)
mapΔ₀ f (δ-∃∈ c) = δ-∃∈ (mapΔ₀ f c)
```

<!--en-->
The lemma extends to the whole alternating tower by mutual induction, reusing
`mapΔ₀`{.Agda} at the leaves.
<!--zh-->
引理经互归纳延伸到 Σ 与 Π 交替的各个层级，其中的叶情形复用 `mapΔ₀`{.Agda}。
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
## Recap

The syntactic action `mapFo`{.Agda} commutes with satisfaction and preserves every Lévy grade. A formula can therefore move between constant domains while its meaning and complexity certificate move with it.
<!--zh-->
## 小结

语法作用 `mapFo`{.Agda} 与满足关系可交换，并保持每个 Lévy 级别。因此，公式可以在常元域之间移动，其含义与复杂度见证也一同移动。
<!--ja-->
## まとめ

構文上の作用 `mapFo`{.Agda} は充足関係と可換で、すべての Lévy 等級を保存します。したがって論理式は、意味と複雑さの証明書を伴ったまま定数域の間を移れます。
<!--/-->
