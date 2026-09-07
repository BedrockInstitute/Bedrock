<!--en-->
# Small presentations of sets

Every set in `V`{.Agda} is presented by a small index type and an embedding into the hierarchy. The lemmas here pass between an index and the corresponding membership proof, and record injectivity and small membership for later constructions.
<!--zh-->
# 集合的小呈现

`V`{.Agda} 中每个集合都由一个小索引类型及其到层级的嵌入来呈现。这里的引理在索引与相应隶属证明之间往返，并记录单射性与小隶属，供后续构造使用。
<!--ja-->
# 集合の小さな提示

`V`{.Agda} の各集合は、小さな添字型と階層への埋め込みによって提示されます。ここでは添字と対応する所属証明を相互に移し、後の構成で使う単射性と小さな所属を記録します。
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
