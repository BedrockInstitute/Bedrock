# Collapsing a transitive well-founded relation

<!--en-->
A transitive well-founded relation has a canonical set-valued collapse. Each
point is sent to the set of the collapses of its predecessors; well-founded
recursion makes that equation a definition, and transitivity makes every value
an ordinal.

The construction is deliberately independent of classical logic and of either
application that needs it. The Hartogs argument uses the collapse to build an
ordinal too large to inject into a given set, while the GCH development uses the
same recursion to turn a well-founded relation represented in `L` into its order
type.
<!--zh-->
一个传递良基关系有一个典范的集合值塌缩。每个点被送到其前驱之塌缩所成的集合；良基递归使这条方程成为定义，而传递性使每个值都成为序数。

这个构造刻意不依赖经典逻辑，也不依赖使用它的任何一个应用。Hartogs 论证借此造出一个过大而不能注入给定集合的序数；GCH 部分则用同一场递归，把 `L` 中表示的良基关系变成它的序型。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Mostowski {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; isPropIsTransV )

open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )
```

<!--en-->
The recursive function and its computation equation are kept opaque together.
Consumers reason through `col-eq`; they never unfold a well-founded induction
during conversion.
<!--zh-->
递归函数及其计算方程一同保持不透明。消费方经 `col-eq` 推理，绝不在转换时展开一场良基归纳。
<!--/-->

```agda
module Mostowski (A : Type ℓ) (_≺_ : A → A → Type ℓ)
                 (wf : WellFounded _≺_)
                 (≺-trans : {x y z : A} → x ≺ y → y ≺ z → x ≺ z) where

  module W = WFI wf using ( induction; induction-compute )

  colStep : (p : A) → (∀ r → r ≺ p → SV.S) → SV.S
  colStep p rec = sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → rec (fst z) (snd z))

  opaque
    col : A → SV.S
    col = W.induction {P = λ _ → SV.S} colStep

    col-eq : (p : A) → col p ≡ sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → col (fst z))
    col-eq = W.induction-compute colStep

  col-in : (p r : A) → r ≺ p → ⟨ col r ∈ˢ col p ⟩
  col-in p r rp =
    subst (λ v → ⟨ col r ∈ˢ v ⟩) (sym (col-eq p)) ∣ (r , rp) , refl ∣₁

  col-out : (p : A) (b : SV.S) → ⟨ b ∈ˢ col p ⟩
          → ∥ Σ[ r ∈ A ] ((r ≺ p) × (col r ≡ b)) ∥₁
  col-out p b b∈ =
    PT.map (λ z → fst (fst z) , snd (fst z) , snd z)
      (subst (λ v → ⟨ b ∈ˢ v ⟩) (col-eq p) b∈)

  col-ord : (p : A) → IsOrd (col p)
  col-ord = W.induction {P = λ p → IsOrd (col p)} ih
    where
    ih : (p : A) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
    ih p rec = tr , mem
      where
      mem : (x : SV.S) → ⟨ x ∈ˢ col p ⟩ → isTransV x
      mem x x∈ = PT.rec (isPropIsTransV x)
        (λ z → subst isTransV (snd (snd z)) (rec (fst z) (fst (snd z)) .fst))
        (col-out p x x∈)
      tr : isTransV (col p)
      tr {x} {y} y∈x x∈col = PT.rec (snd (y ∈ˢ col p)) outer (col-out p x x∈col)
        where
        outer : Σ[ r ∈ A ] ((r ≺ p) × (col r ≡ x)) → ⟨ y ∈ˢ col p ⟩
        outer (r , rp , e) =
          PT.rec (snd (y ∈ˢ col p)) inner
            (col-out r y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))
          where
          inner : Σ[ s ∈ A ] ((s ≺ r) × (col s ≡ y)) → ⟨ y ∈ˢ col p ⟩
          inner (s , sr , e2) =
            subst (λ v → ⟨ v ∈ˢ col p ⟩) e2 (col-in p s (≺-trans sr rp))
```
