# The presentation kit

<!--en-->
Four one-line facts about the small presentation, collected once so every
chapter stops re-deriving them. The small member type `⟪ a ⟫` presents the set
`a` through the embedding `⟪ a ⟫↪`; `member` reads the embedding's value back
into membership, `fiber` recovers the index of a member (the untruncated fiber
of the embedding), `↪-inj` is the embedding's injectivity, and `∈ₛ↪` is the
small membership of the embedding's value.
<!--zh-->
小呈现的四条一行事实，一次收齐，让各章不再各自重推。小成员类型 `⟪ a ⟫` 经嵌入 `⟪ a ⟫↪` 呈现集合 `a`；`member` 把嵌入的取值读回隶属关系，`fiber` 还原成员的索引 (嵌入的不加截断的纤维)，`↪-inj` 是嵌入的单射性，`∈ₛ↪` 是嵌入取值的小隶属。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Presentation {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )

open hPropStructure 𝒮ᵥ

member : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ a ⟩
member a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

fiber : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ ⟪ a ⟫ ] (⟪ a ⟫↪ m ≡ x)
fiber a {x} x∈ = ∈-asFiber {a = x} {b = a} x∈

↪-inj : {a : S} {m n : ⟪ a ⟫} → ⟪ a ⟫↪ m ≡ ⟪ a ⟫↪ n → m ≡ n
↪-inj {a} {m} {n} = isEmbedding→Inj isEmb⟪ a ⟫↪ m n

∈ₛ↪ : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ₛ a ⟩
∈ₛ↪ a m = ∈ₛ⟪ a ⟫↪ m
```
