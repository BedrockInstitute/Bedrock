# The stage of a constructible set

<!--en-->
Constructibility was defined as "some ordinal stage contains it", and the
witness was deliberately kept in the statement so that later theory could take it
back out. Now it takes it out, and sharpens it: not *some* stage but the
*earliest* one. That function is what every later construction uses to place a
finite collection of constructible sets at a common stage, since bounding the
earliest stages bounds every stage that would do.

Two things have to be shown. That a least stage exists, which is a descent: start
from any stage that works and ask whether a smaller one also works; if so recurse,
and membership is well founded so the recursion stops. And that it is unique,
which is trichotomy: two least stages cannot be strictly ordered either way, so
they are equal.

Both are classical, for reasons already seen. The descent asks, at each step, a
question about an arbitrary set, and uniqueness is comparison. So the stage
function joins the classical cone, and the chapter is the third and last place
the excluded middle enters the L-side machinery.
<!--zh-->
可构造性当初定义为「某个序数阶段包含它」，而那个见证被刻意留在陈述里，好让后续理论把它取回来。现在就取，并且加以锐化：不是**某个**阶段，而是**最早的**那个。正是这个函数，使此后每个构造能把有穷多个可构造集安置在公共阶段上，因为界住最早的阶段就界住了任何合用的阶段。

要证的有两件。最小阶段存在，那是一次下降：从任何合用的阶段出发，问是否有更小的也合用；若有则递归，而成员关系良基，故递归会停。以及它唯一，那是三歧：两个最小阶段无论哪个方向都不能严格相比，故它们相等。

两件都是经典的，理由前面已经见过。下降在每一步问的是关于任意集合的问题，而唯一性是比较。于是阶段函数加入经典锥，本章是排中律进入 L 侧机器的第三处、也是最后一处。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Stage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd; Lset; isL )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Being the earliest stage
<!--zh-->
## 作为最早的阶段
<!--/-->

<!--en-->
An ordinal is earliest for `x` when no smaller ordinal is a stage containing `x`.
Packaging that with the ordinal and the membership gives the data a later chapter
wants; and the package is a proposition, which is what lets it be extracted from
the truncated witness that constructibility carries.
<!--zh-->
一个序数对 `x` 而言是最早的，指没有更小的序数是包含 `x` 的阶段。把这一条与序数性、成员性打成包，就得到后续章节想要的数据；而这个包是命题，正是这一点使它能从可构造性所携带的截断见证中被取出。
<!--/-->

```agda
isEarliest : (x α : S) → Type (ℓ-suc ℓ)
isEarliest x α = (γ : S) → IsOrd γ → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ γ ∈ˢ α ⟩ → Empty.⊥

Earliest : S → Type (ℓ-suc ℓ)
Earliest x = Σ[ α ∈ S ] (IsOrd α × ⟨ x ∈ˢ Lset α ⟩ × isEarliest x α)

isPropEarliest : (x : S) → isProp (Earliest x)
isPropEarliest x (α , ordα , memα , leastα) (α' , ordα' , memα' , leastα') =
  Σ≡Prop propRest α≡α'
  where
  decide : (⟨ α ∈ˢ α' ⟩ ⊎ ((α ≡ α') ⊎ ⟨ α' ∈ˢ α ⟩)) → α ≡ α'
  decide (inl α∈α')       = Empty.rec (leastα' α ordα memα α∈α')
  decide (inr (inl e))    = e
  decide (inr (inr α'∈α)) = Empty.rec (leastα α' ordα' memα' α'∈α)
  α≡α' : α ≡ α'
  α≡α' = decide (ord-tri α ordα α' ordα')
  propRest : (β : S) → isProp (IsOrd β × ⟨ x ∈ˢ Lset β ⟩ × isEarliest x β)
  propRest β = isProp× (isPropIsOrd β)
    (isProp× (snd (x ∈ˢ Lset β))
      (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Empty.isProp⊥))
```

<!--en-->
## The descent
<!--zh-->
## 下降
<!--/-->

<!--en-->
Given any stage containing `x`, walk down. Ask whether a strictly smaller ordinal
is also a stage containing `x`; if one is, recurse into it, and membership being
well founded the walk terminates; if none is, the current stage is earliest, and
the refutation of the question is exactly the earliestness proof.
<!--zh-->
给定任一包含 `x` 的阶段，向下走。问是否有严格更小的序数也是包含 `x` 的阶段；若有则递归进去，而成员关系良基，故这趟行走会终止；若没有，则当前阶段最早，而对那个问题的反驳恰是最早性的证明。
<!--/-->

```agda
earliestBelow : (x α : S) → IsOrd α → ⟨ x ∈ˢ Lset α ⟩ → Earliest x
earliestBelow x = ∈-induction step
  where
  step : (α : S) → (∀ β → ⟨ β ∈ˢ α ⟩ → IsOrd β → ⟨ x ∈ˢ Lset β ⟩ → Earliest x)
       → IsOrd α → ⟨ x ∈ˢ Lset α ⟩ → Earliest x
  step α IH ordα memα = decide (lem Smaller)
    where
    Smaller : hProp (ℓ-suc ℓ)
    Smaller =
      ∃[ β ∶ S ] ((β ∈ˢ α) ⊓ ((IsOrd β , isPropIsOrd β) ⊓ (x ∈ˢ Lset β)))
    decide : (⟨ Smaller ⟩ ⊎ (⟨ Smaller ⟩ → Empty.⊥)) → Earliest x
    decide (inl ∃β) = PT.rec (isPropEarliest x)
      (λ { (β , (β∈α , (ordβ , memβ))) → IH β β∈α ordβ memβ }) ∃β
    decide (inr ¬∃β) = α , ordα , memα , earliestProof
      where
      earliestProof : isEarliest x α
      earliestProof γ ordγ memγ γ∈α = ¬∃β ∣ γ , (γ∈α , (ordγ , memγ)) ∣₁
```

<!--en-->
## The stage function
<!--zh-->
## 阶段函数
<!--/-->

<!--en-->
Constructibility carries its witness truncated, and the descent's result is a
proposition, so the truncation lifts. The stage is then the ordinal component,
with its three properties projected out.

The function is sealed. It unfolds to a well-founded recursion whose steps
mention the tower, and every later type mentioning a stage would otherwise drag
that unfolding into conversion; the three projections open the seal exactly once
each, and no consumer needs it open again.
<!--zh-->
可构造性携带的见证是截断的，而下降的结果是命题，故截断可以抬过去。阶段就是其序数分量，三条性质随之投影而出。

这个函数被封印。它展开是一次良基递归，其步进提到那座塔，而此后每个提到阶段的类型都会把那次展开拖进转换检查；三个投影各开封一次，而没有任何消费方需要再开封。
<!--/-->

```agda
theEarliest : (x : S) → ⟨ isL x ⟩ → Earliest x
theEarliest x = PT.rec (isPropEarliest x)
  (λ { (α , (ordα , memα)) → earliestBelow x α ordα memα })

opaque
  stage : (x : S) → ⟨ isL x ⟩ → S
  stage x p = theEarliest x p .fst

opaque
  unfolding stage
  stage-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (stage x p)
  stage-ord x p = theEarliest x p .snd .fst

  stage-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (stage x p) ⟩
  stage-mem x p = theEarliest x p .snd .snd .fst

  stage-earliest : (x : S) (p : ⟨ isL x ⟩) → isEarliest x (stage x p)
  stage-earliest x p = theEarliest x p .snd .snd .snd
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`stage`{.Agda} names the earliest ordinal stage containing a constructible set,
with `stage-ord`{.Agda}, `stage-mem`{.Agda} and `stage-earliest`{.Agda} its three
properties. Existence is a well-founded descent and uniqueness is trichotomy, so
the chapter is classical; and the function is sealed, so the descent never
reaches a later conversion problem. Reflection is the first consumer: to reflect
a formula it must first place the formula's parameters at a common stage, and it
gets there by bounding their stages.
<!--zh-->
`stage`{.Agda} 为可构造集命名包含它的最早序数阶段，`stage-ord`{.Agda}、`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 是它的三条性质。存在性是一次良基下降，唯一性是三歧，故本章经典；而函数被封印，故那次下降永不抵达日后的转换问题。反射是第一个消费方：要反射一条公式，必先把公式的参数安置在公共阶段上，而它正是经界住诸阶段而抵达那里的。
<!--/-->
