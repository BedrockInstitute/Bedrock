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

Neither argument looks at what the property says. So the chapter proves them for
an arbitrary property of ordinals and reads the stage function off as the
instance, which costs nothing here and pays later: a canonical *choice* of
ordinal is a thing several constructions want, and each one that gets it this way
is one that does not need a well-ordering of L to get it.

Both are classical, for reasons already seen. The descent asks, at each step, a
question about an arbitrary set, and uniqueness is comparison. So the least
ordinal joins the classical cone, and the chapter is the third and last place
the excluded middle enters the L-side machinery.
<!--zh-->
可构造性当初定义为「某个序数阶段包含它」，而那个见证被刻意留在陈述里，好让后续理论把它取回来。现在就取，并且加以锐化：不是**某个**阶段，而是**最早的**那个。正是这个函数，使此后每个构造能把有穷多个可构造集安置在公共阶段上，因为界住最早的阶段就界住了任何合用的阶段。

要证的有两件。最小阶段存在，那是一次下降：从任何合用的阶段出发，问是否有更小的也合用；若有则递归，而成员关系良基，故递归会停。以及它唯一，那是三歧：两个最小阶段无论哪个方向都不能严格相比，故它们相等。

两个论证都不看那条性质说了什么。故本章对任意的序数性质来证，再把阶段函数作为实例读出：此处不费分文，而日后有偿：序数的一个典范**选取**是若干构造都想要的东西，而每个由此获得它的构造，就是一个无须 L 的良序即可获得它的构造。

两件都是经典的，理由前面已经见过。下降在每一步问的是关于任意集合的问题，而唯一性是比较。于是最小序数加入经典锥，本章是排中律进入 L 侧机器的第三处、也是最后一处。
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
open PT using ( ∣_∣₁; ∥_∥₁ )
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
An ordinal is least for a property when no smaller ordinal has that property.
Packaging that with the ordinal and the property gives the data a later chapter
wants; and the package is a proposition, which is what lets it be extracted from
a truncated witness, as constructibility's is.

Uniqueness is where the property's being an `hProp`{.Agda} earns its keep: the
two candidates are compared by trichotomy, each strict direction is refuted by
the other's minimality, and the remaining components are propositions, so the
equality of the ordinals is the equality of the packages.
<!--zh-->
一个序数对某条性质而言是最小的，指没有更小的序数具有该性质。把这一条与序数性、该性质打成包，就得到后续章节想要的数据；而这个包是命题，正是这一点使它能从截断的见证中被取出，可构造性携带的正是这样的见证。

唯一性正是那条性质取值于 `hProp`{.Agda} 的用武之处：两个候选由三歧比较，每个严格方向都被对方的极小性反驳，而其余分量都是命题，故序数相等即是整包相等。
<!--/-->

```agda
module _ (P : S → Ω) where

  isLeastOrd : S → Type (ℓ-suc ℓ)
  isLeastOrd α = (γ : S) → IsOrd γ → ⟨ P γ ⟩ → ⟨ γ ∈ˢ α ⟩ → Empty.⊥

  LeastOrd : Type (ℓ-suc ℓ)
  LeastOrd = Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩ × isLeastOrd α)

  isPropLeastOrd : isProp LeastOrd
  isPropLeastOrd (α , ordα , pα , leastα) (α' , ordα' , pα' , leastα') =
    Σ≡Prop propRest α≡α'
    where
    decide : (⟨ α ∈ˢ α' ⟩ ⊎ ((α ≡ α') ⊎ ⟨ α' ∈ˢ α ⟩)) → α ≡ α'
    decide (inl α∈α')       = Empty.rec (leastα' α ordα pα α∈α')
    decide (inr (inl e))    = e
    decide (inr (inr α'∈α)) = Empty.rec (leastα α' ordα' pα' α'∈α)
    α≡α' : α ≡ α'
    α≡α' = decide (ord-tri α ordα α' ordα')
    propRest : (β : S) → isProp (IsOrd β × ⟨ P β ⟩ × isLeastOrd β)
    propRest β = isProp× (isPropIsOrd β)
      (isProp× (snd (P β))
        (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Empty.isProp⊥))
```

<!--en-->
## The descent
<!--zh-->
## 下降
<!--/-->

<!--en-->
Given any ordinal with the property, walk down. Ask whether a strictly smaller
ordinal also has it; if one does, recurse into it, and membership being well
founded the walk terminates; if none does, the current ordinal is least, and the
refutation of the question is exactly the minimality proof.

The result being a proposition, the starting ordinal may be given truncated, and
that is the form the callers have: they know a suitable ordinal exists without
having chosen one.
<!--zh-->
给定任一具有该性质的序数，向下走。问是否有严格更小的序数也具有它；若有则递归进去，而成员关系良基，故这趟行走会终止；若没有，则当前序数最小，而对那个问题的反驳恰是极小性的证明。

结果既是命题，起始序数便可以截断的形式给出，而这正是诸调用方手上的形式：它们知道合用的序数存在，却未曾选定一个。
<!--/-->

```agda
  leastOrdBelow : (α : S) → IsOrd α → ⟨ P α ⟩ → LeastOrd
  leastOrdBelow = ∈-induction step
    where
    step : (α : S) → (∀ β → ⟨ β ∈ˢ α ⟩ → IsOrd β → ⟨ P β ⟩ → LeastOrd)
         → IsOrd α → ⟨ P α ⟩ → LeastOrd
    step α IH ordα pα = decide (lem Smaller)
      where
      Smaller : hProp (ℓ-suc ℓ)
      Smaller = ∃[ β ∶ S ] ((β ∈ˢ α) ⊓ ((IsOrd β , isPropIsOrd β) ⊓ P β))
      decide : (⟨ Smaller ⟩ ⊎ (⟨ Smaller ⟩ → Empty.⊥)) → LeastOrd
      decide (inl ∃β) = PT.rec isPropLeastOrd
        (λ { (β , (β∈α , (ordβ , pβ))) → IH β β∈α ordβ pβ }) ∃β
      decide (inr ¬∃β) = α , ordα , pα , leastProof
        where
        leastProof : isLeastOrd α
        leastProof γ ordγ pγ γ∈α = ¬∃β ∣ γ , (γ∈α , (ordγ , pγ)) ∣₁

  leastOrd : ∥ (Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩)) ∥₁ → LeastOrd
  leastOrd = PT.rec isPropLeastOrd
    (λ { (α , (ordα , pα)) → leastOrdBelow α ordα pα })
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
theEarliest : (x : S) → ⟨ isL x ⟩ → LeastOrd (λ σ → x ∈ˢ Lset σ)
theEarliest x = leastOrd (λ σ → x ∈ˢ Lset σ)

opaque
  stage : (x : S) → ⟨ isL x ⟩ → S
  stage x p = theEarliest x p .fst

opaque
  unfolding stage
  stage-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (stage x p)
  stage-ord x p = theEarliest x p .snd .fst

  stage-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (stage x p) ⟩
  stage-mem x p = theEarliest x p .snd .snd .fst

  stage-earliest : (x : S) (p : ⟨ isL x ⟩)
                 → isLeastOrd (λ σ → x ∈ˢ Lset σ) (stage x p)
  stage-earliest x p = theEarliest x p .snd .snd .snd
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`leastOrd`{.Agda} picks the least ordinal satisfying any property of ordinals,
from a truncated witness that one exists. `stage`{.Agda} is its first instance,
naming the earliest stage containing a constructible set, with
`stage-ord`{.Agda}, `stage-mem`{.Agda} and `stage-earliest`{.Agda} its three
properties. Existence is a well-founded descent and uniqueness is trichotomy, so
the chapter is classical; and the function is sealed, so the descent never
reaches a later conversion problem. Reflection is an early consumer, and it uses
both: it places a formula's parameters at a common stage by bounding their
stages, and it picks a witness for an existential by taking the least stage that
has one.
<!--zh-->
`leastOrd`{.Agda} 从「合用的序数存在」这一截断见证出发，为任意序数性质选出满足它的最小序数。`stage`{.Agda} 是它的头一个实例，为可构造集命名包含它的最早阶段，`stage-ord`{.Agda}、`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 是它的三条性质。存在性是一次良基下降，唯一性是三歧，故本章经典；而函数被封印，故那次下降永不抵达日后的转换问题。反射是早期的消费方，且两者都用：它经界住诸阶段而把公式的参数安置在公共阶段上，又经取「有见证的最早阶段」而为一个存在量词选出见证。
<!--/-->
