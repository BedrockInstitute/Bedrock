# Ordinals

<!--en-->
The tower of the previous chapter is indexed by ordinals, and so far the book
has needed exactly one fact about them: that being one is a proposition. The
constructions ahead need more. Every closure argument for the constructible
universe has the same shape: a set is built from ingredients that live at
various stages, and the argument must place the result at a *single* stage. So
what the axioms need from ordinals is not a theory of order, but a supply of
upper bounds.

This chapter provides exactly that supply, and nothing else. Zero is an
ordinal; successors of ordinals are ordinals; a union of ordinals is an
ordinal; and, the chapter's deliverable, every small family of ordinals lies
below a single ordinal. That last statement is what turns "each ingredient has
*some* stage" into "all of them share *one* stage", which is the move every
closure proof in the next chapter makes.

Notably absent is comparison. One expects ordinals to be linearly ordered, and
they are, but that fact is not constructive and it is not needed here: a common
bound is cheaper than a comparison, and it is all the axioms ask for. The book
takes the cheaper road, and the basic axioms of the constructible universe cost
no classical logic as a result.
<!--zh-->
上一章的塔以序数为索引，而本书迄今只用到关于序数的一个事实：「是序数」是命题。接下来的构造要得更多。可构造宇宙的每一个闭包论证都是同一个形状：一个集合由散落在各个阶段的材料造出，而论证必须把结果安置在**单一**阶段上。所以诸公理向序数索取的不是一套序理论，而是一批上界。

本章恰好提供这批上界，别无他物。零是序数；序数的后继是序数；序数之并是序数；以及本章的交付物：任一小族序数都落在单一序数之下。最后这条把「每份材料**各有**其阶段」变成「它们共处**同一**阶段」，而这正是下一章每个闭包证明所做的动作。

显眼地缺席的是比较。人们期望序数是线序的，它们确实是，但那个事实不构造，而且此处用不上：公共上界比比较廉价，而公理要的只是公共上界。本书取那条廉价的路，于是可构造宇宙的基本公理不花费任何经典逻辑。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Ordinal {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( union-family-in; union-family-out; ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ}
  using ( isTransV; isPropIsTransV; ∅-trans; setUnion-trans; IsOrd; isPropIsOrd )

open import Cubical.Data.Nat.Order using ( _<_; ≤-suc; isProp≤ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_; ω; #-in-ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Zero and successors
<!--zh-->
## 零与后继
<!--/-->

<!--en-->
Recall the predicate: an ordinal is a transitive set whose members are all
transitive. Both halves are vacuous for the empty set, so zero is an ordinal
with nothing to prove.
<!--zh-->
回忆那个谓词：序数是成员皆传递的传递集。两半对空集都真空成立，于是零是序数，无须证明什么。
<!--/-->

```agda
∅-ord : IsOrd ∅
∅-ord = ∅-trans
      , (λ x x∈∅ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅)))
```

<!--en-->
The successor `sucV A` adds `A` itself as a member, and the hierarchy chapter
left the tool for reasoning about it: a member of `sucV A` is either a member
of `A` or `A` itself, and that case split is a proposition-level eliminator. Both
halves of the ordinal predicate follow it. For transitivity, a member of a
member of `sucV A` lands back in `A` either by `A`'s transitivity or, in the
degenerate branch, immediately; for the second half, the members of `sucV A`
are members of `A` (transitive by assumption) or `A` itself (transitive by
assumption again).
<!--zh-->
后继 `sucV A` 把 `A` 自身添作成员，而层级那一章留下了推理它的工具：`sucV A` 的成员要么是 `A` 的成员，要么就是 `A` 自身，这个分情形是命题级的消去子。序数谓词的两半都照着它走。传递性一半：`sucV A` 的成员之成员，或经 `A` 的传递性、或在退化支上直接地，落回 `A`；第二半：`sucV A` 的成员或是 `A` 的成员 (依假设传递)、或就是 `A` (仍依假设传递)。
<!--/-->

```agda
suc-ord : ∀ {A} → IsOrd A → IsOrd (sucV A)
suc-ord {A} (Atr , Amem) = trans-sucV , mem-sucV
  where
  trans-sucV : isTransV (sucV A)
  trans-sucV {x} {y} y∈x x∈suc = ∈sucV-elim (snd (y ∈ˢ sucV A)) x∈suc
    (λ x∈A → ∈sucV-inl (Atr y∈x x∈A))
    (λ x≡A → ∈sucV-inl (subst (λ w → ⟨ y ∈ˢ w ⟩) x≡A y∈x))
  mem-sucV : (x : S) → ⟨ x ∈ˢ sucV A ⟩ → isTransV x
  mem-sucV x x∈suc = ∈sucV-elim (isPropIsTransV x) x∈suc
    (λ x∈A → Amem x x∈A)
    (λ x≡A → subst isTransV (sym x≡A) Atr)
```

<!--en-->
## Unions and bounds
<!--zh-->
## 并与上界
<!--/-->

<!--en-->
Ordinals are closed under small-indexed unions. Transitivity is the closure
lemma already proved for transitive sets; for the second half, a member of the
union sits inside some `f x`, and that family member is an ordinal by
hypothesis, so its own members are transitive.
<!--zh-->
序数对小索引并封闭。传递性就是传递集那边已证的闭包引理；第二半：并的成员落在某个 `f x` 里面，而依假设该族元是序数，故其成员传递。
<!--/-->

```agda
setUnion-ord : (X : Type ℓ) (f : X → S) → ((x : X) → IsOrd (f x))
             → IsOrd (⋃ (sett X f))
setUnion-ord X f hf = setUnion-trans X f (λ x → hf x .fst) , memTr
  where
  memTr : (z : S) → ⟨ z ∈ˢ (⋃ (sett X f)) ⟩ → isTransV z
  memTr z z∈⋃ = PT.rec (isPropIsTransV z)
    (λ { (x , hz) → hf x .snd z hz }) (union-family-out X f z z∈⋃)
```

<!--en-->
And the chapter's deliverable. Given a small family of ordinals, a single
ordinal contains every member of the family. The naive attempt, take the union
of the family, gives only inclusion: a union absorbs its members' *elements*,
not the members themselves, and no set contains itself. The repair is one step
of successor: union the family of successors instead. Then `f x` belongs to
`sucV (f x)`, which belongs to the family being unioned, so `f x` belongs to
the union, which is what the closure arguments need. The result is a genuine
pair, not a truncated existence: the consumers name the bound and form its
stage.
<!--zh-->
然后是本章的交付物。给定一小族序数，有单一序数包含该族的每一个成员。朴素的尝试，取该族之并，只能给出包含关系：并吸收其成员的**元素**，而非成员本身，且没有集合以自身为成员。补救是一步后继：改取后继族之并。于是 `f x` 属于 `sucV (f x)`，后者属于被取并的那个族，故 `f x` 属于该并，这正是闭包论证所需。结果是货真价实的序对，而非截断的存在：消费方要点名那个上界，并造出它的阶段。
<!--/-->

```agda
boundingOrd : (X : Type ℓ) (f : X → S) → ((x : X) → IsOrd (f x))
            → Σ[ β ∈ S ] (IsOrd β × ((x : X) → ⟨ f x ∈ˢ β ⟩))
boundingOrd X f hf = β , (ordβ , memβ)
  where
  g : X → S
  g x = sucV (f x)
  β : S
  β = ⋃ (sett X g)
  ordβ : IsOrd β
  ordβ = setUnion-ord X g (λ x → suc-ord (hf x))
  memβ : (x : X) → ⟨ f x ∈ˢ β ⟩
  memβ x = union-family-in X g x (f x) (self∈sucV (f x))
```

<!--en-->
The two-element case is worth naming, because it is the one that gets used most:
merging two ordinals into one that contains both. The family is indexed by the
booleans, lifted to the ambient universe so that the general lemma applies, and
the two memberships are read off at the two indices.
<!--zh-->
二元情形值得单独命名，因为用得最多的正是它：把两个序数合并为一个同时包含二者的序数。族由布尔值索引，抬升到周遭宇宙以便通用引理适用，而两条隶属关系在两个索引处读出。
<!--/-->

```agda
bound2 : (σ₁ σ₂ : S) → IsOrd σ₁ → IsOrd σ₂
       → Σ[ β ∈ S ] (IsOrd β × ⟨ σ₁ ∈ˢ β ⟩ × ⟨ σ₂ ∈ˢ β ⟩)
bound2 σ₁ σ₂ o₁ o₂ =
  fst r , (r .snd .fst , r .snd .snd (lift true) , r .snd .snd (lift false))
  where
  f : Lift {ℓ-zero} {ℓ} Bool → S
  f (lift true)  = σ₁
  f (lift false) = σ₂
  fo : (b : Lift {ℓ-zero} {ℓ} Bool) → IsOrd (f b)
  fo (lift true)  = o₁
  fo (lift false) = o₂
  r = boundingOrd (Lift {ℓ-zero} {ℓ} Bool) f fo
```

<!--en-->
## Members
<!--zh-->
## 成员
<!--/-->

<!--en-->
Ordinals are closed downwards: a member of an ordinal is an ordinal. Its own
transitivity is the second half of the hypothesis; that its members are
transitive follows by pulling them back into the ambient ordinal along
transitivity.

The hierarchy chapter's irreflexivity, that no set belongs to itself, is the
other fact these arguments need; it is recalled here because this is where the
ordinal proofs start reaching for it.
<!--zh-->
序数向下封闭：序数的成员是序数。它自身的传递性就是假设的第二半；而其成员传递，则经传递性把它们拉回外层序数即得。

层级那一章的无自环性，即没有集合属于自身，是这些论证需要的另一个事实；此处提起它，是因为序数的证明正是从这里开始取用。
<!--/-->

```agda
mem-ord : ∀ {A} → IsOrd A → (x : S) → ⟨ x ∈ˢ A ⟩ → IsOrd x
mem-ord {A} (Atr , Amem) x x∈A =
  Amem x x∈A , (λ y y∈x → Amem y (Atr y∈x x∈A))
```

<!--en-->
## The numerals, and their limit
<!--zh-->
## 数码，及其极限
<!--/-->

<!--en-->
The hierarchy's numerals are the iterated successors of zero, so they are
ordinals by the two facts above, one induction deep. Their limit `ω` is an
ordinal too, and that is the fact the collection step will need. Its second
half is free from the numerals; its first half, transitivity, says that a
member of a numeral is again a numeral, which is another induction, the
successor case splitting by the eliminator.
<!--zh-->
层级的数码是零的迭代后继，故由上面两个事实即为序数，一层归纳而已。它们的极限 `ω` 也是序数，而那正是收集步骤将要用到的事实。其第二半由数码免费给出；第一半即传递性，说的是数码的成员仍是数码，那是另一次归纳，后继情形按消去子分情形。
<!--/-->

```agda
numeral-ord : (n : ℕ) → IsOrd (# n)
numeral-ord zero    = ∅-ord
numeral-ord (suc n) = suc-ord (numeral-ord n)

#∈ω : (k : ℕ) → ⟨ (# k) ∈ˢ ω ⟩
#∈ω k = ∈∈ₛ {a = # k} {b = ω} .snd (#-in-ω k)

numeral-mem : (k : ℕ) (y : S) → ⟨ y ∈ˢ (# k) ⟩ → ⟨ y ∈ˢ ω ⟩
numeral-mem zero y y∈ =
  Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))
numeral-mem (suc k) y y∈ = ∈sucV-elim (snd (y ∈ˢ ω)) y∈
  (λ y∈#k → numeral-mem k y y∈#k)
  (λ y≡#k → subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym y≡#k) (#∈ω k))

ω-mem-ord : (y : S) → ⟨ y ∈ˢ ω ⟩ → IsOrd y
ω-mem-ord y y∈ω = PT.rec (isPropIsOrd y)
  (λ { (k , #k≡y) → subst IsOrd #k≡y (numeral-ord (lower k)) })
  y∈ω

ω-ord : IsOrd ω
ω-ord = trans-ω , (λ x x∈ω → ω-mem-ord x x∈ω .fst)
  where
  trans-ω : isTransV ω
  trans-ω {x} {y} y∈x x∈ω = PT.rec (snd (y ∈ˢ ω))
    (λ { (k , #k≡x) →
      numeral-mem (lower k) y (subst (λ w → ⟨ y ∈ˢ w ⟩) (sym #k≡x) y∈x) })
    x∈ω
```

<!--en-->
## What lies below a numeral
<!--zh-->
## 数码之下有什么
<!--/-->

<!--en-->
The numerals are not merely ordinals, they are *counted* by ordinals: the members
of the numeral for `n` are exactly the numerals for the smaller naturals. The
first half of that, elimination, is one induction with the successor eliminator;
the second half, that a numeral belonging to a numeral means the indices compare,
follows by injectivity. The coding chapters will use these to read an index out of
a set, which is what a bound on a variable ultimately means.
<!--zh-->
数码不只是序数，它们还被序数**计数**：`n` 的数码的成员，恰是更小自然数的数码。前一半即消去，是一次沿后继消去子的归纳；后一半，即数码属于数码意味着序号可比，则由单射性得出。编码诸章将用它们从一个集合里读出序号，而那正是变元的界最终的含义。
<!--/-->

```agda
∈#-elim : (n : ℕ) (z : S) → ⟨ z ∈ˢ (# n) ⟩
        → ∥ Σ[ m ∈ ℕ ] ((m < n) × (z ≡ # m)) ∥₁
∈#-elim zero    z h = Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst h))
∈#-elim (suc n) z h = ∈sucV-elim {A = # n} {x = z}
  {P = ∥ Σ[ m ∈ ℕ ] ((m < suc n) × (z ≡ # m)) ∥₁} squash₁ h
  (λ z∈#n → PT.map (λ { (m , p , e) → m , ≤-suc p , e }) (∈#-elim n z z∈#n))
  (λ e → ∣ n , (0 , refl) , e ∣₁)

#∈#-elim : (a b : ℕ) → ⟨ (# a) ∈ˢ (# b) ⟩ → a < b
#∈#-elim a b h = PT.rec isProp≤
  (λ { (m , p , e) → subst (_< b) (sym (#-inj′ e)) p })
  (∈#-elim b (# a) h)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Zero, successors and small unions of ordinals are ordinals, and
`boundingOrd`{.Agda} bounds any small family by a single ordinal. That last
result is the chapter's whole purpose: it is how "each of finitely many
ingredients lives at some stage" becomes "all of them live at one stage", and
the next chapter spends it three times over, once for each of the first
closure axioms. Downward closure, the absence of self-membership, and `ω`
itself as an ordinal are the same theory continued; they wait here for the
collection step of infinity, which is what first needs them.
<!--zh-->
零、后继与序数的小并都是序数，而 `boundingOrd`{.Agda} 以单一序数界住任一小族。最后这条就是本章的全部目的：它把「有穷多份材料各有其阶段」变成「它们同处一个阶段」，而下一章会把它花掉三次，头几条闭包公理各一次。向下封闭、无自环，以及 `ω` 自身是序数，都是同一套理论的续篇；它们在此等候无穷公理的收集那一步，那是最先需要它们的地方。
<!--/-->

