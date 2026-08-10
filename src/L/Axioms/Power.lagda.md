# The power set in L

<!--en-->
The power set of a set of `L`, taken inside `L`, is the set of its *constructible*
subsets, and that is what the model's field asks for: the inclusion it quantifies
over ranges across the model's own carrier, so a subset that is not constructible
is not a candidate. The task is to collect the ones that are.

The argument is bounding and then carving, the same two moves the axioms before
it used. Every subset of a set is a member of the hierarchy's power set, which is
indexed by a small type; the constructible ones among them form a small family
too, so their stages have a common bound, and every constructible subset appears
below it. Carving that stage by the formula "every member of this is a member of
`a`" gives exactly the constructible subsets, because the bound makes the
membership half of the condition automatic.

Two things make the proof short. Separation in `L` now accepts any formula, so
the condition may be written as it reads. And the smallness that the hierarchy's
power set needs, and that resizing an unbounded constructibility statement needs,
are the two halves of the impredicativity package the book already redeems from
the excluded middle: **no new principle enters, and no new level of it either**,
which is worth checking rather than assuming, since the two halves live one
universe apart.

Condensation is not part of this. It is the sharper statement that a subset of a
stage appears at a stage bounded in terms of that stage rather than in terms of
the subsets themselves, and it is what a cardinal arithmetic would want. The
axiom does not.
<!--zh-->
`L` 的集合在 `L` 之内取的幂集，是它**可构造**子集之集，而这正是模型那个字段所索取的：它所量化的包含关系跑遍模型自己的载体，故不可构造的子集根本不是候选。任务是把可构造的那些收集起来。

论证是先界住、再雕出，与它之前诸公理所用的是同样两步。一个集合的每个子集都是层级幂集的成员，而后者由小类型索引；其中可构造的那些也构成小族，故它们的阶段有公共上界，而每个可构造子集都现身于其下。用「此物的每个成员都是 `a` 的成员」这条公式雕出那个阶段，得到的恰是诸可构造子集，因为那个上界使条件中隶属的那一半自动成立。

有两件事使证明变短。`L` 中的分离如今接受任意公式，故那个条件可以照它读起来的样子写。而层级幂集所需的小性、与「把一条无界的可构造性陈述降层」所需的小性，是本书早已从排中律赎回的那个非直谓性打包的两半：**没有新原则进场，也没有新层级的排中律进场**；后者值得核对而非假定，因为那两半相隔一个宇宙。

凝聚不属于这里。它是更锐的陈述：某阶段的子集现身于一个「按该阶段而非按诸子集本身」界住的阶段处，而那是基数算术会想要的东西。公理不想要。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lem→resizing; lem→impredicativity )
open import Base.Impredicativity using ( module Impredicativity )

module L.Axioms.Power {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∀̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( module Power )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )

open import Cubical.Foundations.Equiv using ( _≃_; invEq; equivFun )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; _⊆ˢ_ )
module ModelV = FOL.ZFModel 𝒮ᵥ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Pow = Power (Impredicativity.hPropSmallness (lem→impredicativity lem))
```

<!--en-->
## The condition, as a formula
<!--zh-->
## 作为公式的条件
<!--/-->

<!--en-->
"Everything in this is in `a`", with `a` named as a constant, which it may be
because it is an element of the model. Its meaning is the model's own inclusion,
on the nose: the object language's bounded universal is the truth algebra's
meet over the carrier guarded by membership, and that is how inclusion was
defined.
<!--zh-->
「此物之中的一切都在 `a` 之中」，其中 `a` 以常元点名，而它可以，因为它是模型的元素。它的含义恰是模型自己的包含关系，一分不差：对象语言的有界全称就是真值代数在载体上、由隶属设防的交，而包含关系当初正是这么定义的。
<!--/-->

```agda
subFo : S → Formula S 1
subFo a = ∀̇∈ (var zero) (var zero ∈̇ con a)

```

<!--en-->
## Bounding the constructible subsets
<!--zh-->
## 界住诸可构造子集
<!--/-->

<!--en-->
The hierarchy's power set is indexed by a small type, and the constructible
members of it are cut out by a constructibility statement, which lives one
universe too high to keep the index small. Resizing brings it back down, and
resizing is what the excluded middle was already bought for. With the index small
the stages form a small family and the bounding lemma applies.

Then the surjectivity: every constructible subset really does appear below the
bound. Its underlying set is a subset in the hierarchy's sense, because a member
of a constructible set is constructible and so is covered by the model's own
inclusion; the hierarchy's power set therefore contains it, its index gives a
point of the small family, and its own earliest stage lies below the bound.
<!--zh-->
层级的幂集由小类型索引，而其中可构造的成员由一条可构造性陈述切出，那条陈述高出一个宇宙，无法保持索引为小。降层把它拉回来，而降层正是排中律早已买下的东西。索引一小，诸阶段便构成小族，界层引理随即适用。

然后是满射性：每个可构造子集确实现身于那个上界之下。它的底集在层级的意义上是子集，因为可构造集的成员可构造，故被模型自己的包含关系覆盖；层级的幂集因而含有它，它的索引给出小族的一个点，而它自己的最早阶段落在上界之下。
<!--/-->

```agda
module Bound (a : S) where
  private
    A P : V ℓ
    A = fst a
    P = Pow.𝒫V A

    rsz : (v : V ℓ) → Σ[ Q ∈ hProp ℓ ] (⟨ isL v ⟩ ≃ ⟨ Q ⟩)
    rsz v = lem→resizing lem (isL v)

  Ix : Type ℓ
  Ix = Σ[ m ∈ ⟪ P ⟫ ] ⟨ rsz (⟪ P ⟫↪ m) .fst ⟩

  private
    unres : (i : Ix) → ⟨ isL (⟪ P ⟫↪ (i .fst)) ⟩
    unres i = invEq (rsz (⟪ P ⟫↪ (i .fst)) .snd) (i .snd)

    stg : Ix → V ℓ
    stg i = stage (⟪ P ⟫↪ (i .fst)) (unres i)

    b = boundingOrd Ix stg (λ i → stage-ord (⟪ P ⟫↪ (i .fst)) (unres i))

  β : V ℓ
  β = b .fst

  oβ : IsOrd β
  oβ = b .snd .fst

  below : (x : S) → ⟨ x ⊆ˢ a ⟩ → ⟨ fst x ∈ Lset β ⟩
  below x x⊆a =
    subst (λ w → ⟨ w ∈ Lset β ⟩) pa
      (Lset-mono {α = β} {β = stg i} (b .snd .snd i) (stage-mem _ (unres i)))
    where
    vsub : ⟨ ModelV._⊆ˢ_ (fst x) A ⟩
    vsub v v∈ = x⊆a (v , isL-trans {x = fst x} {y = v} v∈ (x .snd)) v∈
    fib = ∈-asFiber {a = fst x} {b = P}
            (subst ⟨_⟩ (sym (Pow.power-spec A (fst x))) vsub)
    pa : ⟪ P ⟫↪ (fib .fst) ≡ fst x
    pa = fib .snd
    i : Ix
    i = fib .fst
      , equivFun (rsz (⟪ P ⟫↪ (fib .fst)) .snd)
          (subst (λ w → ⟨ isL w ⟩) (sym pa) (x .snd))
```

<!--en-->
## The field
<!--zh-->
## 字段
<!--/-->

<!--en-->
Separate the bounding stage by the condition. What comes out is indexed by the
conjunction "in the stage, and included in `a`", and the second conjunct implies
the first, so the two predicates agree pointwise and the answer transports across.
<!--zh-->
用那个条件雕出界层阶段。出来的东西以「在该阶段中，且包含于 `a`」这一合取为索引，而第二个合取项蕴含第一个，故两个谓词逐点一致，答案随之搬运过去。
<!--/-->

```agda
hasPowerL : (a : S) → isContr (SetOf (λ x → x ⊆ˢ a))
hasPowerL a =
  subst (λ Q → isContr (SetOf Q)) Q≡
    (hasSeparationL (LsetS (Bound.β a) (Bound.oβ a)) (subFo a))
  where
  Q≡ : (λ x → (x ∈ˢ LsetS (Bound.β a) (Bound.oβ a)) ⊓ ((x ∷ []) ⊨ subFo a))
     ≡ (λ x → x ⊆ˢ a)
  Q≡ = funExt (λ x → ⇔toPath
    (λ { (_ , x⊆a) → x⊆a })
    (λ x⊆a → Bound.below a x x⊆a , x⊆a))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`hasPowerL`{.Agda} is the model's power-set field, proved by bounding the
constructible subsets and carving one stage. The frontier is down to choice.

What the proof used, and what it did not, is the point worth carrying away. It
used the classical interface twice, once to resize an unbounded constructibility
statement and once for the hierarchy's own power set, and it used separation for
an arbitrary formula, which the previous part paid for. It did not use
condensation, and did not need to: the axiom asks for the constructible subsets
to form a set, not for them to appear early.
<!--zh-->
`hasPowerL`{.Agda} 是模型的幂集字段，经「界住诸可构造子集、雕出一个阶段」证得。前沿只剩选择。

这个证明用了什么、没用什么，才是该带走的那一点。它两次使用了那个经典接口，一次为把无界的可构造性陈述降层，一次为层级自己的幂集；它还用了任意公式的分离，那是上一部付过的账。它**没有**用凝聚，也不需要：公理索取的是「诸可构造子集构成一个集合」，而非「它们现身得早」。
<!--/-->
