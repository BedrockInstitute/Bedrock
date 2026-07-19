# Relabelling

<!--en-->
The constant domain is a parameter, and the book keeps swapping it: the working
syntax takes a carrier, the parameter-free formulas take the empty type, Part 4
takes a restricted carrier. This chapter is the kit for such swaps, and it works
at three altitudes at once: a map between constant domains pushes through
**syntax** functorially, preserves **meaning** on the nose, and carries the
Levy **witnesses** along unchanged. Like its tail-mates, the kit has no
consumer in the trunk yet; its customers arrive with the deeper chapters of
Part 4, where formulas migrate between the inner world's constants, the codes'
empty domain, and the ambient carrier.
<!--zh-->
常量域是一个参数，而本书不停地换它：工作语法取载体，无参公式取空类型，第四部取受限载体。本章就是这类更换的工具组，且一次在三个海拔上工作：常量域之间的一个映射，沿**语法**函子式推送，在**含义**上分毫不差，还把 Lévy **见证**原样携带。与书末诸同伴一样，这套工具在主干上尚无消费者；它的客户随第四部的深层章节到来，届时公式将在内层世界的常量、码的空域与环境载体之间迁徙。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Relabelling where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
  ; Σₙ; σ-Δ₀; σ-Π; σ-∃; Πₙ; π-Δ₀; π-Σ; π-∀ )
import FOL.Semantics
import Cubical.Data.Empty as Empty
```

<!--en-->
## Syntax level
<!--zh-->
## 语法层
<!--/-->

<!--en-->
The syntax is functorial in its constant domain: a map `K → K'` pushes through a
term or formula, relabelling constants and touching nothing else. One clause per
constructor, each doing the obvious thing.
<!--zh-->
语法对常量域是函子式的：一个映射 `K → K'` 沿词项或公式推送，变换常量，不碰其他任何东西。一构造子一子句，各做显然之事。
<!--/-->

```agda
mapTm : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Term K n → Term K' n
mapTm f (con k) = con (f k)
mapTm f (var i) = var i

mapFo : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Formula K n → Formula K' n
mapFo f (t ∈̇ u)  = mapTm f t ∈̇ mapTm f u
mapFo f (t ≐ u)  = mapTm f t ≐ mapTm f u
mapFo f (φ ∧̇ ψ)  = mapFo f φ ∧̇ mapFo f ψ
mapFo f (φ ∨̇ ψ)  = mapFo f φ ∨̇ mapFo f ψ
mapFo f (φ ⇒̇ ψ)  = mapFo f φ ⇒̇ mapFo f ψ
mapFo f (¬̇ φ)    = ¬̇ mapFo f φ
mapFo f ⊤̇        = ⊤̇
mapFo f ⊥̇        = ⊥̇
mapFo f (∃̇ φ)    = ∃̇ mapFo f φ
mapFo f (∀̇ φ)    = ∀̇ mapFo f φ
mapFo f (∀̇∈ t φ) = ∀̇∈ (mapTm f t) (mapFo f φ)
mapFo f (∃̇∈ t φ) = ∃̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
The most-travelled instance: entering a constant domain from **no** constants.
The syntax chapter introduced the **parameter-free formulas**, the data axis
with the empty type as constant domain; like sentences they bear no separate
name, the type `Formula (⊥* {ℓ}) n` says it whole. From the empty type anything
follows, the library's eliminator `Empty.rec*`{.Agda} says so, and relabelling
along it embeds a parameter-free formula into the syntax over any domain
whatsoever.
<!--zh-->
走动最勤的实例：从**没有**常量的域进入任何常量域。语法章介绍过**无参公式**，即以空类型为常量域的数据轴；与句子一样，本书不为它另设名字，类型 `Formula (⊥* {ℓ}) n` 已经说完全部。从空类型可以推出一切，库的消去子 `Empty.rec*`{.Agda} 说的正是这句话，沿它变换，无参公式便嵌入任意常量域上的语法。
<!--/-->

```agda
embed : ∀ {ℓ ℓ'} {K : Type ℓ'} {n} → Formula (⊥* {ℓ}) n → Formula K n
embed = mapFo Empty.rec*
```

<!--en-->
## Meaning level
<!--zh-->
## 含义层
<!--/-->

<!--en-->
Relabelling constants along `f : K → K'` and then evaluating under `ι` is the
same as evaluating under `ι ∘ f` directly; the `∘`-marked satisfaction and
denotation below are the generic semantics opened at that composite. One
structural induction, every case a congruence; the two term cases are even
`refl`{.Agda}.
<!--zh-->
沿 `f : K → K'` 变换常量后在 `ι` 下求值，与直接在 `ι ∘ f` 下求值相同；下文带 `∘` 标记的满足与释义，就是在该复合解释处打开的泛型语义。一次结构归纳，每个情形都是同余；两个词项情形干脆是 `refl`{.Agda}。
<!--/-->

```agda
module _ {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮
  open FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )

  module _ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K') (ι : K' → S) where

    open At ι using ( _⊨_; ⟦_⟧ )
    open At (λ k → ι (f k)) using () renaming ( _⊨_ to _⊨∘_ ; ⟦_⟧ to ⟦_⟧∘ )

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
    ⊨-map (¬̇ φ)    γ = cong ¬_ (⊨-map φ γ)
    ⊨-map ⊤̇        γ = refl
    ⊨-map ⊥̇        γ = refl
    ⊨-map (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
    ⊨-map (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x → ⊨-map φ (x ∷ γ)))
    ⊨-map (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
      cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
    ⊨-map (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
      cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-map t γ)) (⊨-map φ (x ∷ γ))))
```

<!--en-->
The corollary the parameter-free formulas were waiting for: entering any
constant domain through `embed`{.Agda} keeps their meaning. The data axis and
the working syntax share one semantics; nothing needs proving twice. (The
`∅`-marked satisfaction reads the empty constant domain through
`Empty.rec*`{.Agda}.)
<!--zh-->
无参公式等候的推论：经 `embed`{.Agda} 进入任何常量域，含义不变。数据轴与工作语法共享同一套语义，无一事需证两遍。(带 `∅` 标记的满足经 `Empty.rec*`{.Agda} 解读空常量域。)
<!--/-->

```agda
  module _ {ℓe ℓc} {K : Type ℓc} (ι : K → S) where

    open At ι using ( _⊨_ )
    open At (λ (b : ⊥* {ℓe}) → ι (Empty.rec* b)) using () renaming ( _⊨_ to _⊨∅_ )

    embed-⊨ : ∀ {n} (φ : Formula (⊥* {ℓe}) n) (γ : S ^ n)
            → (γ ⊨ embed φ) ≡ (γ ⊨∅ φ)
    embed-⊨ = ⊨-map Empty.rec* ι
```

<!--en-->
## Levy witness level
<!--zh-->
## Lévy 见证层
<!--/-->

<!--en-->
Relabelling constants preserves the structure of a formula, so a Levy
witness follows along, constructor by constructor. This little lemma is
what will let an absoluteness argument carry a Δ₀ witness across a change of
constant domain.
<!--zh-->
变换常量保持公式的结构，Lévy 见证遂逐构造子随行。正是这条小引理，将让绝对性论证携着 Δ₀ 见证跨越常量域的更换。
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
The lemma extends to the whole alternating tower by mutual induction, reusing
`mapΔ₀`{.Agda} at the leaves.
<!--zh-->
引理经互归纳延伸到整座交替之塔，叶位复用 `mapΔ₀`{.Agda}。
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
<!--zh-->
## 小结
<!--/-->

<!--en-->
One map of constant domains, three altitudes of transport: `mapFo`{.Agda} moves
the syntax (with `embed`{.Agda} as the parameter-free entrance), `⊨-map`{.Agda}
and `embed-⊨`{.Agda} certify that meaning does not move at all, and
`mapΔ₀`{.Agda} with its tower carries the Levy witnesses. A formula, its meaning,
and its grade travel as one; the chapters that migrate formulas between worlds
will lean on exactly that.
<!--zh-->
一个常量域映射，三个海拔的搬运：`mapFo`{.Agda} 搬语法 (`embed`{.Agda} 是无参入口)，`⊨-map`{.Agda} 与 `embed-⊨`{.Agda} 认证含义纹丝不动，`mapΔ₀`{.Agda} 及其塔搬 Lévy 见证。公式、含义与级别作为一体旅行；将来在诸世界之间迁徙公式的章节，靠的正是这一点。
<!--/-->
