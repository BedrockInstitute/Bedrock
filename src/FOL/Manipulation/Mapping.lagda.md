# Mapping constants

<!--en-->
The constant domain is a parameter of first-order syntax. This chapter gives its
functorial action: maps relabel constants in terms and formulas, composition is
preserved, and parameter-free formulas enter every constant domain.
<!--zh-->
常量域是第一阶语法的参数。本章给出它的函子作用：映射在项与公式中重标常量，复合得以保持，而无参公式可进入任意常量域。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Mapping where

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import Cubical.Data.Empty as Empty
```

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
mapFo f ⊥̇        = ⊥̇
mapFo f (∃̇ φ)    = ∃̇ mapFo f φ
mapFo f (∀̇ φ)    = ∀̇ mapFo f φ
mapFo f (∀̇∈ t φ) = ∀̇∈ (mapTm f t) (mapFo f φ)
mapFo f (∃̇∈ t φ) = ∃̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
Two such maps in a row are one map. The composite is the only thing a chapter
that migrates a formula through an intermediate domain ever wants, and proving it
where the syntax is defined costs ten congruences and stops every later
chapter from writing its own. Both term cases are `refl`{.Agda}, because a
variable carries no constant and a constant is relabelled by application.
<!--zh-->
连着两次这样的映射就是一次映射。凡经中间域迁徙一条公式的章节，想要的无非是那个复合；而在语法被定义之处证它，代价是十次同余，却省得此后每一章各写一遍。两个词项情形都是 `refl`{.Agda}，因为变元不携带常量，而常量的变换就是把映射施用上去。
<!--/-->

```agda
mapTm-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (t : Term K n)
           → mapTm g (mapTm f t) ≡ mapTm (λ k → g (f k)) t
mapTm-comp f g (con k) = refl
mapTm-comp f g (var i) = refl

mapFo-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (φ : Formula K n)
           → mapFo g (mapFo f φ) ≡ mapFo (λ k → g (f k)) φ
mapFo-comp f g (t ∈̇ u)  = cong₂ _∈̇_ (mapTm-comp f g t) (mapTm-comp f g u)
mapFo-comp f g (t ≐ u)  = cong₂ _≐_ (mapTm-comp f g t) (mapTm-comp f g u)
mapFo-comp f g (φ ∧̇ ψ)  = cong₂ _∧̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ∨̇ ψ)  = cong₂ _∨̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g ⊥̇        = refl
mapFo-comp f g (∃̇ φ)    = cong ∃̇_ (mapFo-comp f g φ)
mapFo-comp f g (∀̇ φ)    = cong ∀̇_ (mapFo-comp f g φ)
mapFo-comp f g (∀̇∈ t φ) = cong₂ ∀̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
mapFo-comp f g (∃̇∈ t φ) = cong₂ ∃̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
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
## Recap

<!--zh-->
## 小结
<!--/-->

<!--en-->
`mapTm` and `mapFo` express the syntax-level action of a map of constant domains;
`mapFo-comp` gives functoriality, and `embed` is the parameter-free instance.
<!--zh-->
`mapTm` 与 `mapFo` 表达常量域映射在语法层的作用；`mapFo-comp` 给出函子性，`embed` 是无参实例。
<!--/-->
