# The stage where a set first has a member

<!--en-->
The last debt asks for a set that meets each cell of a disjoint family in
exactly one point. The textbook pays it by well-ordering the universe and taking
the least member of every cell, and that road is expensive here: a well-order of
all of `L` is a relation on a proper class, and nothing built so far speaks of
one.

There is a cheaper road, and it starts by asking where a cell's members *are*.
A cell is a set of `L`, so each of its members appears somewhere in the tower;
so there is an earliest stage at which any of them has appeared at all. That
stage cannot be a limit and cannot be zero: a set enters the tower only by being
carved out of the stage below it, so the earliest stage that meets the cell is
the successor of a stage that does not. The cell therefore carries a canonical
ordinal of its own, the stage one below its first appearance, and at that
ordinal every member of the cell that appears first is a definable subset of one
and the same set.

That is what replaces the well-order. Choosing a member of the cell becomes a
comparison between names written over a single stage, never a comparison between
arbitrary elements of `L`; the ordinal doing the bookkeeping is the stage, so
sets that appear at different times are never compared at all. This chapter
builds that ordinal and proves the two facts the rest of the part turns on: that
it exists and is unique, and that one ordinal suffices to hold a set, its
members and their members, together with the tower's limit level.
<!--zh-->
最后一笔债索取的，是一个与不交族的每一格恰交于一点的集合。教科书的偿付方式是把宇宙良序化，再取每一格中最小的成员，而这条路在此处代价高昂：`L` 整体的良序是一个真类上的关系，而迄今造出的东西没有一样谈得到它。

有一条更廉价的路，它从「一格的诸成员**在哪里**」问起。一格是 `L` 的一个集合，故它的每个成员都现身于塔中某处；于是存在一个最早的阶段，其中已经现身了它的某个成员。那个阶段既不能是极限，也不能是零：集合进入塔的唯一途径是从它下面那个阶段中被雕出，故与该格相交的最早阶段，是某个与它不相交的阶段的后继。于是这一格自带一个典范的序数，即它首次现身之前的那个阶段；而在那个序数处，该格中最先现身的每个成员，都是同一个集合的可定义子集。

这就是取代良序的东西。为一格选取成员，从此成为写在单一阶段之上的诸名字之间的比较，而绝非 `L` 的任意元素之间的比较；记账的序数就是阶段，故现身时刻不同的集合根本不会被拿来比较。本章造出那个序数，并证明本部余下部分所系的两件事：它存在且唯一；以及单一序数足以装下一个集合、它的成员与它们的成员，连同塔的极限层。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Stage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd; isL; isL-trans; Lset; Lset-layer; Lset-out
        ; Lset-mono; layer-trans; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; bound2; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem
  using ( isLeastOrd; LeastOrd; leastOrd; stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The least stage meeting a set
<!--zh-->
## 与一个集合相交的最小阶段
<!--/-->

<!--en-->
"Some member of `u` has appeared by stage `σ`" is a property of ordinals and
nothing more, so the least-ordinal operator applies to it with no work: that
operator was written generic in its property precisely so that instances like
this one cost a line.

The operator wants a truncated witness that *some* ordinal qualifies, and an
inhabited cell supplies it. A member of the cell is constructible, because `L`
is a transitive class and the cell is one of its sets; and constructibility is
by definition the existence of a stage containing it. So the witness is the
member's own stage, read straight off the class.
<!--zh-->
「到阶段 `σ` 为止，`u` 的某个成员已经现身」是一条关于序数的性质，仅此而已，故最小序数算子对它零成本地适用：当初把那个算子写成对性质泛型的，正是为了让这样的实例只花一行。

算子要一份截断的见证，说**某个**序数合用，而一个非空的格恰好供得出。该格的成员可构造，因为 `L` 是传递类而该格是它的一个集合；而可构造按定义就是「存在一个包含它的阶段」。于是见证就是那个成员自己的阶段，从类上直接读出。
<!--/-->

```agda
meets : S → S → Ω
meets u σ = ⋁ S (λ z → (z ∈ˢ u) ⊓ (z ∈ˢ Lset σ))

Inhabited : S → Type (ℓ-suc ℓ)
Inhabited u = ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ u ⟩ ∥₁

meetsSome : (u : S) → ⟨ isL u ⟩ → Inhabited u
          → ∥ Σ[ σ ∈ S ] (IsOrd σ × ⟨ meets u σ ⟩) ∥₁
meetsSome u pu = PT.rec squash₁ atMember
  where
  atMember : Σ[ z ∈ S ] ⟨ z ∈ˢ u ⟩
           → ∥ Σ[ σ ∈ S ] (IsOrd σ × ⟨ meets u σ ⟩) ∥₁
  atMember (z , z∈u) = PT.map
    (λ { (α , (ordα , z∈Lα)) → α , (ordα , ∣ z , (z∈u , z∈Lα) ∣₁) })
    (isL-trans {x = u} {y = z} z∈u pu)
```

<!--en-->
The least such ordinal is `μ u`, and it is sealed exactly as the stage function
was, for exactly the same reason: it unfolds to a well-founded descent whose
steps mention the tower, and every later type mentioning it would drag that
unfolding into conversion. The three projections open the seal once each, and
they are the whole interface.
<!--zh-->
最小的这样的序数是 `μ u`，它按阶段函数当初那样封印，理由完全相同：它展开是一次良基下降，其步进提到那座塔，而此后每个提到它的类型都会把那次展开拖进转换检查。三个投影各开封一次，而它们就是全部接口。
<!--/-->

```agda
theEarliestMeet : (u : S) → ⟨ isL u ⟩ → Inhabited u → LeastOrd (meets u)
theEarliestMeet u pu h = leastOrd (meets u) (meetsSome u pu h)

opaque
  μ : (u : S) → ⟨ isL u ⟩ → Inhabited u → S
  μ u pu h = theEarliestMeet u pu h .fst

opaque
  unfolding μ
  μ-ord : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u) → IsOrd (μ u pu h)
  μ-ord u pu h = theEarliestMeet u pu h .snd .fst

  μ-meets : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u) → ⟨ meets u (μ u pu h) ⟩
  μ-meets u pu h = theEarliestMeet u pu h .snd .snd .fst

  μ-earliest : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
             → isLeastOrd (meets u) (μ u pu h)
  μ-earliest u pu h = theEarliestMeet u pu h .snd .snd .snd
```

<!--en-->
## A first appearance is a successor
<!--zh-->
## 首次现身处是后继
<!--/-->

<!--en-->
Take a member of the cell that has appeared by the least stage. Membership in a
stage is membership in the definable subsets of some earlier stage, and the
successor identity says those definable subsets are the next stage; so that
member has already appeared one stage above the earlier one, and the cell is
already met there. Minimality forbids that stage from being strictly below the
least one, and a member's successor cannot overshoot: it belongs to the least
stage or it *is* it. The first case is the one minimality just refuted, so the
second holds, and the least stage is a successor.

The refuted case is a named helper with its conclusion written down. That is the
discipline the stages chapter set for every split coming out of trichotomy, and
the split here is one: `suc∈or≡`{.Agda} is a comparison in disguise.
<!--zh-->
取该格中一个到最小阶段为止已现身的成员。属于一个阶段，就是属于某个更早阶段的可定义子集，而后继恒等式说那些可定义子集就是下一个阶段；故那个成员在那个更早阶段之上一级就已现身，该格在那里就已被相交。极小性禁止那个阶段严格低于最小阶段，而成员的后继又不会越过头：它或属于最小阶段，或**就是**最小阶段。前一种情形正是极小性刚刚反驳的，故后一种成立，于是最小阶段是后继。

被反驳的那一支写成写明结论的具名辅助件。这是阶段那一章为每个出自三歧的分情形定下的纪律，而此处的分情形正是其一：`suc∈or≡`{.Agda} 是乔装的比较。
<!--/-->

```agda
IsPredOf : S → S → Type (ℓ-suc ℓ)
IsPredOf σ δ = IsOrd δ × (sucV δ ≡ σ)

private
  below-case : (u σ δ : S) → isLeastOrd (meets u) σ → IsOrd δ
             → ⟨ meets u (sucV δ) ⟩ → ⟨ sucV δ ∈ˢ σ ⟩ → sucV δ ≡ σ
  below-case u σ δ least ordδ m s∈σ =
    Empty.rec (least (sucV δ) (suc-ord ordδ) m s∈σ)

  same-case : (u σ δ : S) → sucV δ ≡ σ → sucV δ ≡ σ
  same-case u σ δ e = e

meet-suc : (u σ : S) → IsOrd σ → ⟨ meets u σ ⟩ → isLeastOrd (meets u) σ
         → ∥ Σ[ δ ∈ S ] IsPredOf σ δ ∥₁
meet-suc u σ ordσ m least = PT.rec squash₁ atMember m
  where
  atCarve : (z : S) → ⟨ z ∈ˢ u ⟩
          → Σ[ δ ∈ S ] (⟨ δ ∈ˢ σ ⟩ × ⟨ z ∈ˢ 𝒟ₒ (Lset δ) ⟩)
          → Σ[ δ ∈ S ] IsPredOf σ δ
  atCarve z z∈u (δ , (δ∈σ , z∈𝒟ₒδ)) = δ , (ordδ , suc≡σ)
    where
    ordδ : IsOrd δ
    ordδ = mem-ord {A = σ} ordσ δ δ∈σ
    metAtSuc : ⟨ meets u (sucV δ) ⟩
    metAtSuc = ∣ z , (z∈u
      , subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Lset-suc δ)) z∈𝒟ₒδ) ∣₁
    suc≡σ : sucV δ ≡ σ
    suc≡σ = Sum.rec (below-case u σ δ least ordδ metAtSuc) (same-case u σ δ)
      (suc∈or≡ δ σ ordδ ordσ δ∈σ)

  atMember : Σ[ z ∈ S ] (⟨ z ∈ˢ u ⟩ × ⟨ z ∈ˢ Lset σ ⟩)
           → ∥ Σ[ δ ∈ S ] IsPredOf σ δ ∥₁
  atMember (z , (z∈u , z∈Lσ)) = PT.map (atCarve z z∈u) (Lset-out σ z z∈Lσ)
```

<!--en-->
## The stage a first appearance is defined over
<!--zh-->
## 首次现身所依据的那个阶段
<!--/-->

<!--en-->
A successor determines what it succeeds, at least among ordinals. Compare a
candidate predecessor with another: each belongs to the successor of the other,
so each is a member of the other or equal to it, and two ordinals cannot be
members of each other, since transitivity would then make one a member of
itself. So being the predecessor of a given ordinal is a proposition, and the
predecessor of the least stage may be extracted from the merely-existing one the
previous section produced.

That extraction is what makes `defStage`{.Agda} a function: the *definition
stage* of a cell, the stage over which the cell's first members are written. It
is sealed with its two properties beside it, as `μ`{.Agda} was.
<!--zh-->
后继决定它所后继的东西，至少在序数之内如此。把一个候选前一阶段与另一个相比：各自属于对方的后继，故各自或是对方的成员、或与对方相等；而两个序数不能互为成员，否则传递性会使其一属于自身。于是「是给定序数的前一阶段」是命题，而最小阶段的前一阶段可以从上一节造出的那个仅仅存在者中取出。

正是这次取出使 `defStage`{.Agda} 成为函数：一格的**定义阶段**，即该格最先现身的诸成员所依据写出的那个阶段。它连同两条性质一并封印，与 `μ`{.Agda} 当初一样。
<!--/-->

```agda
private
  cycle₂ : (a b : S) → IsOrd a → ⟨ a ∈ˢ b ⟩ → ⟨ b ∈ˢ a ⟩ → Empty.⊥
  cycle₂ a b orda a∈b b∈a = ∈-irrefl a (orda .fst a∈b b∈a)

  mem-branch : (δ δ' : S) → IsOrd δ → ⟨ δ' ∈ˢ sucV δ ⟩ → ⟨ δ ∈ˢ δ' ⟩ → δ ≡ δ'
  mem-branch δ δ' ordδ δ'∈sδ δ∈δ' =
    ∈sucV-elim {A = δ} {x = δ'} (setIsSet δ δ') δ'∈sδ
      (λ δ'∈δ → Empty.rec (cycle₂ δ δ' ordδ δ∈δ' δ'∈δ))
      (λ δ'≡δ → sym δ'≡δ)

ord-suc-inj : (δ δ' : S) → IsOrd δ → sucV δ ≡ sucV δ' → δ ≡ δ'
ord-suc-inj δ δ' ordδ e =
  ∈sucV-elim {A = δ'} {x = δ} (setIsSet δ δ') δ∈sδ'
    (mem-branch δ δ' ordδ δ'∈sδ)
    (λ δ≡δ' → δ≡δ')
  where
  δ∈sδ' : ⟨ δ ∈ˢ sucV δ' ⟩
  δ∈sδ' = subst (λ w → ⟨ δ ∈ˢ w ⟩) e (self∈sucV δ)
  δ'∈sδ : ⟨ δ' ∈ˢ sucV δ ⟩
  δ'∈sδ = subst (λ w → ⟨ δ' ∈ˢ w ⟩) (sym e) (self∈sucV δ')

isPropPredOf : (σ : S) → isProp (Σ[ δ ∈ S ] IsPredOf σ δ)
isPropPredOf σ (δ , (ordδ , e)) (δ' , (ordδ' , e')) =
  Σ≡Prop (λ d → isProp× (isPropIsOrd d) (setIsSet (sucV d) σ))
    (ord-suc-inj δ δ' ordδ (e ∙ sym e'))

thePred : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
        → Σ[ δ ∈ S ] IsPredOf (μ u pu h) δ
thePred u pu h = PT.rec (isPropPredOf (μ u pu h)) (λ d → d)
  (meet-suc u (μ u pu h) (μ-ord u pu h) (μ-meets u pu h) (μ-earliest u pu h))

opaque
  defStage : (u : S) → ⟨ isL u ⟩ → Inhabited u → S
  defStage u pu h = thePred u pu h .fst

opaque
  unfolding defStage
  defStage-ord : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
               → IsOrd (defStage u pu h)
  defStage-ord u pu h = thePred u pu h .snd .fst

  defStage-suc : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
               → sucV (defStage u pu h) ≡ μ u pu h
  defStage-suc u pu h = thePred u pu h .snd .snd
```

<!--en-->
## One stage for everything below a set
<!--zh-->
## 一个阶段装下一个集合以下的一切
<!--/-->

<!--en-->
The other thing the construction needs is a bound, and no comparison is involved
in getting one. A stage is transitive, so the stage of a set already holds the
set's members, and their members after them; the earliest stage is a stage like
any other, so it serves.

One more ordinal has to be cleared, the tower's limit level. The construction
ahead compares names; a name is built from numerals and pairs and from nothing
else, so it has appeared by `Lset ω`{.Agda}, and the stage doing the bookkeeping
must therefore lie above `ω` as well as above the set's own stage. The bounding
ordinal of two ordinals settles that in one line, and monotonicity carries both
levels up into its stage.
<!--zh-->
构造还需要另一样东西：一个上界，而取得它不牵涉任何比较。阶段传递，故一个集合的阶段已经装着该集合的诸成员，以及其后它们的诸成员；最早的阶段与别的阶段无异，故它就够用。

还有一个序数要清出来，即塔的极限层。后续构造比较的是名字，而一个名字由数码与对造成、别无他物，故它到 `Lset ω`{.Agda} 为止已经现身；于是记账的那个阶段必须既在该集合自身的阶段之上，也在 `ω` 之上。两个序数的上界序数一行解决，而单调性把两层一并抬进它的阶段。
<!--/-->

```agda
stage-below : (a : S) (p : ⟨ isL a ⟩) (x : S) → ⟨ x ∈ˢ a ⟩
            → ⟨ x ∈ˢ Lset (stage a p) ⟩
stage-below a p x x∈a =
  layer-trans (Lset-layer (stage a p)) x∈a (stage-mem a p)

stage-below₂ : (a : S) (p : ⟨ isL a ⟩) (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ a ⟩
             → ⟨ y ∈ˢ Lset (stage a p) ⟩
stage-below₂ a p x y y∈x x∈a =
  layer-trans (Lset-layer (stage a p)) y∈x (stage-below a p x x∈a)

stageBound : (a : S) (p : ⟨ isL a ⟩)
           → Σ[ β ∈ S ] (IsOrd β × ⟨ ω ∈ˢ β ⟩ × ⟨ stage a p ∈ˢ β ⟩)
stageBound a p = bound2 ω (stage a p) ω-ord (stage-ord a p)

bound-below₂ : (a : S) (p : ⟨ isL a ⟩) (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ a ⟩
             → ⟨ y ∈ˢ Lset (stageBound a p .fst) ⟩
bound-below₂ a p x y y∈x x∈a =
  Lset-mono (stageBound a p .snd .snd .snd) (stage-below₂ a p x y y∈x x∈a)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`μ`{.Agda} is the earliest stage at which a set of `L` has a member, and
`meet-suc`{.Agda} says that stage is a successor, because a set enters the tower
only by being carved out of the stage below. `defStage`{.Agda} is the stage it
succeeds, a function because a successor determines what it succeeds among
ordinals (`ord-suc-inj`{.Agda}). So every set that first
appears there carries a name written over one fixed stage, which is what the
choosing device will compare. `stageBound`{.Agda} supplies the ordinal the
bookkeeping runs in: above a set's own stage, hence above its members and
theirs, and above the tower's limit level, where the names themselves live.

Nothing here states a relation on `L`, and nothing here is a recursion. The
comparison and the recursion both arrive in the next chapters, and both are
confined to the material this one has located.
<!--zh-->
`μ`{.Agda} 是 `L` 的一个集合拥有成员的最早阶段，而 `meet-suc`{.Agda} 说那个阶段是后继，因为集合进入塔的唯一途径是从它下面那个阶段中被雕出。`defStage`{.Agda} 是它所后继的那个阶段，之所以是函数，是因为在序数之内后继决定它所后继的东西 (`ord-suc-inj`{.Agda})。于是每个首次现身于该处的集合，都带着一个写在单一固定阶段之上的名字，而那正是选取装置将要比较的东西。`stageBound`{.Agda} 供应记账所在的序数：在一个集合自身的阶段之上，从而在它的成员及其成员之上，也在塔的极限层之上，而诸名字自身正住在那里。

此处没有一条陈述涉及 `L` 上的关系，也没有一处是递归。比较与递归都在后面几章到场，而两者都被限制在本章所定位的材料之内。
<!--/-->
