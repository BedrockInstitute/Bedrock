# The frontier

<!--en-->
This book is built root-first: the main theorem is *stated* now and *finished*
over the remaining parts. That calls for a device, and honesty demands it be
neither a hole nor a postulate. The **frontier** is that device: one record
whose fields are precisely the statements not yet proven, so that the root
theorem of the next chapter is an ordinary theorem *from* the frontier. Every
field here is a debt; every remaining chapter of the book pays some of them;
a field, once proven, is deleted. The record is the live registry of what
separates the book from its unconditional theorem, and when it empties, this
chapter disappears with it.

The debts are exactly the model fields still owed for the constructible
structure `𝒮ʟ`: the previous chapter produced the world, and the record below
lists, field for field, what the model record demands of it beyond the two
facts (extensionality, regularity) that the next chapter proves outright. The
choice field is stated relative to an arbitrary ZF model on this carrier, the
same structural form the hierarchy's choice took.
<!--zh-->
本书采取从根开始的构造：主定理**现在**陈述，在余下诸部中**逐步完成**。这需要一件装置，而诚实要求它既不是洞也不是公设。**前沿**就是那件装置：一个 record，其字段恰是尚未证明的陈述，于是下一章的根定理是一条**由**前沿出发的普通定理。这里的每个字段都是一笔债；本书余下的每一章偿还其中若干；字段一经证明即被删除。这个 record 是「离无条件定理还差什么」的实时登记簿，账清之日，本章随之消失。

这些债恰是可构造结构 `𝒮ʟ` 尚欠的模型字段：上一章造出了世界，下面的 record 逐字段列出模型 record 对它的其余要求，扣除下一章直接证明的两条 (外延与正则)。选择字段相对于此载体上任意 ZF 模型陈述，与层级那边的选择取同一结构形式。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Frontier {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; _⊆ˢ_; isZFModel )

module SemanticsL = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
open SemanticsL.At S id using ( _⊨_ )
```

<!--en-->
The choice statement, packaged first so the record can quantify over the model
supplying the intersection it mentions:
<!--zh-->
先打包选择公理的陈述，好让 record 对「供应其中交运算的模型」量化：
<!--/-->

```agda
ChoiceStatement : isZFModel → Type (ℓ-suc ℓ)
ChoiceStatement zf =
  (a : S)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
  → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
       → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
  → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
       → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
  where open ModelL.isZFModel zf using ( _∩_ )
```

<!--en-->
And the registry itself. Each field's statement is the corresponding model
field at `𝒮ʟ`, verbatim; the numeral chain comes with its two pinning
equations, exactly as in the record it will feed.
<!--zh-->
然后是登记簿本身。每个字段的陈述都是模型 record 对应字段在 `𝒮ʟ` 处的原文；数码链连同它的两条钉死方程，与它将要喂进的 record 一字不差。
<!--/-->

```agda
record Frontier : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    hasEmptyL       : isContr (SetOf (λ _ → ⊥))
    hasPairL        : (a b : S) → isContr (SetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)))
    hasUnionL       : (a : S)
                    → isContr (SetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))
    hasSeparationL  : (a : S) (φ : Formula S 1)
                    → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
    hasReplacementL : (a : S) (φ : Formula S 2)
                    → ((x : S) → ⟨ x ∈ˢ a ⟩
                         → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                    → isContr (SetOf (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
    hasPowerL       : (a : S) → isContr (SetOf (λ x → x ⊆ˢ a))
    numeralL        : ℕ → S
    numeralL-zero   : (z : S) → ⟨ z ∈ˢ numeralL zero ⟩ → Empty.⊥
    numeralL-suc    : (n : ℕ) (z : S)
                    → (⟨ z ∈ˢ numeralL (suc n) ⟩
                         → ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩)
                    × (⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
                         → ⟨ z ∈ˢ numeralL (suc n) ⟩)
    hasInfinityL    : isContr (SetOf (λ x →
                        ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralL (lower n))))
    hasChoiceL      : (zf : isZFModel) → ChoiceStatement zf
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Eleven debts, each the verbatim statement of a model field at `𝒮ʟ`, none of
them a postulate: they are hypotheses of the next chapter's theorem, and the
book's remaining work is the shrinking of this record to nothing.
<!--zh-->
十一笔债，每笔都是模型字段在 `𝒮ʟ` 处的原文陈述，无一是公设：它们是下一章定理的假设，而本书余下的工作，就是把这个 record 缩减为空。
<!--/-->
