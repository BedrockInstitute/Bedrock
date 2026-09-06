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
  using ( IsOrd; isPropIsOrd; isL; Lset; Lset-layer; Lset-out
        ; Lset-mono; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; bound2; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem
  using ( isLeastOrd; stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
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
## The predecessor of a least stage
<!--zh-->
## 最小阶段的前一阶段
<!--/-->

<!--en-->
A successor determines what it succeeds, at least among ordinals. Compare a
candidate predecessor with another: each belongs to the successor of the other,
so each is a member of the other or equal to it, and two ordinals cannot be
members of each other, since transitivity would then make one a member of
itself. So being the predecessor of a given ordinal is a proposition, which is
what lets a merely-existing predecessor be read as a definite one.

That a least stage has a predecessor at all is the argument this chapter was
written for, and it uses nothing about cells. Take anything that has appeared by
the least stage at which some property of ordinals holds. Membership in a stage
is membership in the definable subsets of some earlier stage, and the successor
identity says those definable subsets are the next stage; so the thing has
already appeared one stage above the earlier one, and the property already holds
there. Minimality forbids that stage from being strictly below the least one,
and a successor cannot overshoot: it belongs to the least stage or it *is* it.
The first case is the one minimality just refuted, so the second holds, and the
least stage is a successor. The refuted case is a named helper with its
conclusion written down: that is the discipline the stages chapter set for every
split coming out of trichotomy, and `suc∈or≡`{.Agda} is a comparison in
disguise.

Since the property is never read, it is a parameter, and the argument is written
once for every instance of the least-ordinal operator. `Carved`{.Agda} is the
datum it runs on: an ordinal below the least stage whose successor already has
the property. `carveAt`{.Agda} produces that datum, by reading a member out of
the least stage and renaming the carve to a successor; `predOf`{.Agda} consumes
it and closes the truncation on the uniqueness above. They are halves of one
operation rather than two operations, because `carveAt`{.Agda} builds exactly
what `predOf`{.Agda} takes, and no site has ever wanted one of them alone.
<!--zh-->
后继决定它所后继的东西，至少在序数之内如此。把一个候选前一阶段与另一个相比：各自属于对方的后继，故各自或是对方的成员、或与对方相等；而两个序数不能互为成员，否则传递性会使其一属于自身。于是「是给定序数的前一阶段」是命题，正是这一点使一个仅仅存在的前一阶段可以被读作一个确定的前一阶段。

最小阶段究竟凭什么有前一阶段，这正是本章为之而写的那个论证，而它没有用到关于格的任何东西。取任何一样到「某条序数性质成立的最小阶段」为止已现身的东西。属于一个阶段，就是属于某个更早阶段的可定义子集，而后继恒等式说那些可定义子集就是下一个阶段；故那样东西在那个更早阶段之上一级就已现身，而那条性质在那里就已成立。极小性禁止那个阶段严格低于最小阶段，而一个后继又不会越过头：它或属于最小阶段，或**就是**最小阶段。前一种情形正是极小性刚刚反驳的，故后一种成立，于是最小阶段是后继。被反驳的那一支写成写明结论的具名辅助件：这是阶段那一章为每个出自三歧的分情形定下的纪律，而 `suc∈or≡`{.Agda} 是乔装的比较。

既然那条性质从未被读取，它就是一个参数，于是这个论证为最小序数算子的每个实例只写一遍。`Carved`{.Agda} 是它运行其上的那个数据：最小阶段以下的一个序数，其后继已具备那条性质。`carveAt`{.Agda} 产出那个数据，办法是从最小阶段中读出一个成员，再把那次雕出改名为一个后继；`predOf`{.Agda} 消费它，并按上面那条唯一性把截断闭合。它们是一次操作的两半、而不是两次操作，因为 `carveAt`{.Agda} 造出的恰是 `predOf`{.Agda} 所取用的，而从没有哪个用处只要其中一半。
<!--/-->

```agda
IsPredOf : S → S → Type (ℓ-suc ℓ)
IsPredOf σ δ = IsOrd δ × (sucV δ ≡ σ)

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

module _ (P : S → Ω) where

  Carved : S → Type (ℓ-suc ℓ)
  Carved σ = Σ[ δ ∈ S ] (⟨ δ ∈ˢ σ ⟩ × ⟨ P (sucV δ) ⟩)

  private
    below-case : (σ δ : S) → isLeastOrd P σ → IsOrd δ → ⟨ P (sucV δ) ⟩
               → ⟨ sucV δ ∈ˢ σ ⟩ → sucV δ ≡ σ
    below-case σ δ least ordδ m s∈σ =
      Empty.rec (least (sucV δ) (suc-ord ordδ) m s∈σ)

    same-case : (σ δ : S) → sucV δ ≡ σ → sucV δ ≡ σ
    same-case σ δ e = e

    atCarve : (σ : S) → IsOrd σ → isLeastOrd P σ
            → Carved σ → Σ[ δ ∈ S ] IsPredOf σ δ
    atCarve σ ordσ least (δ , (δ∈σ , m)) = δ , (ordδ , suc≡σ)
      where
      ordδ : IsOrd δ
      ordδ = mem-ord {A = σ} ordσ δ δ∈σ
      suc≡σ : sucV δ ≡ σ
      suc≡σ = Sum.rec (below-case σ δ least ordδ m) (same-case σ δ)
        (suc∈or≡ δ σ ordδ ordσ δ∈σ)

  predOf : (σ : S) → IsOrd σ → isLeastOrd P σ → ∥ Carved σ ∥₁
         → Σ[ δ ∈ S ] IsPredOf σ δ
  predOf σ ordσ least = PT.rec (isPropPredOf σ) (atCarve σ ordσ least)

  carveAt : (σ z : S) → ⟨ z ∈ˢ Lset σ ⟩
          → ((δ : S) → ⟨ z ∈ˢ Lset (sucV δ) ⟩ → ⟨ P (sucV δ) ⟩)
          → ∥ Carved σ ∥₁
  carveAt σ z z∈Lσ k = PT.map
    (λ { (δ , (δ∈σ , z∈𝒟)) → δ , (δ∈σ
      , k δ (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Lset-suc δ)) z∈𝒟)) })
    (Lset-out σ z z∈Lσ)
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
The least stage at which a property of ordinals holds is a successor, because a
set enters the tower only by being carved out of the stage below. That argument
reads nothing about cells, so it is written once over any property of ordinals:
`carveAt`{.Agda} carves a witness below the least stage, and `predOf`{.Agda}
turns the carve into the predecessor, closing the truncation on
`isPropPredOf`{.Agda}. The predecessor is definite because a successor
determines what it succeeds among ordinals (`ord-suc-inj`{.Agda}).
`stageBound`{.Agda} supplies the ordinal the
bookkeeping runs in: above a set's own stage, hence above its members and
theirs, and above the tower's limit level, where the names themselves live.

Nothing here states a relation on `L`, and nothing here is a recursion. The
comparison and the recursion both arrive in the next chapters, and both are
confined to the material this one has located.
<!--zh-->
某条序数性质成立的最小阶段是后继，因为集合进入塔的唯一途径是从它下面那个阶段中被雕出。那个论证不读取关于格的任何东西，故它对任意一条序数性质只写一遍：`carveAt`{.Agda} 在最小阶段之下雕出一个见证，而 `predOf`{.Agda} 把那次雕出变成前一阶段，并按 `isPropPredOf`{.Agda} 把截断闭合。那个前一阶段之所以确定，是因为在序数之内后继决定它所后继的东西 (`ord-suc-inj`{.Agda})。`stageBound`{.Agda} 供应记账所在的序数：在一个集合自身的阶段之上，从而在它的成员及其成员之上，也在塔的极限层之上，而诸名字自身正住在那里。

此处没有一条陈述涉及 `L` 上的关系，也没有一处是递归。比较与递归都在后面几章到场，而两者都被限制在本章所定位的材料之内。
<!--/-->
