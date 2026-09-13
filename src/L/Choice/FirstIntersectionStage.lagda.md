<!--en-->
# The first stage meeting a set
<!--zh-->
# 首次与集合相交的层
<!--ja-->
# 集合と交わる最初の段階
<!--/-->

<!--en-->
This chapter finds the least stage meeting a given constructible set and proves
that it has a unique predecessor, then builds one ordinal bounding the set and
two levels of its members.
<!--zh-->
本章找出与给定可构造集合相交的最小层，证明它有唯一的前一层，再造出一个同时界住该集合及其成员以下两层的序数。
<!--ja-->
本章では、与えられた構成可能集合と交わる最小の段階を求め、それが一意な直前の段階をもつことを証明し、さらにその集合と要素の二層をまとめて抑える順序数を構成する。
<!--/-->

<!--en-->
The final requirement asks for a set that meets each cell of a disjoint family in
exactly one point. The textbook approach well-orders the universe and takes
the least member of every cell. This approach is expensive here because a well-order of
all of `L` is a relation on a proper class, and nothing built so far speaks of
one.

Instead, the construction starts by asking where a cell's members *are*.
A cell is a set of `L`, so each of its members appears somewhere in the tower;
so there is an earliest stage at which any of them has appeared at all. That
stage cannot be a limit and cannot be zero: a set enters the tower only by being
carved out of the stage below it, so the earliest stage that meets the cell is
the successor of a stage that does not. The cell therefore carries a canonical
ordinal of its own, the stage one below its first appearance, and at that
ordinal every member of the cell that appears first is a definable subset of one
and the same set.

This construction replaces the well-order. Choosing a member of the cell becomes a
comparison between names written over a single stage, never a comparison between
arbitrary elements of `L`; the ordinal used for the comparison is the stage, so
sets that appear at different times are never compared at all. This chapter
builds that ordinal and proves the two facts required by the rest of the part: that
it exists and is unique, and that one ordinal suffices to hold a set, its
members and their members, together with the tower's limit level.
<!--zh-->
最后一笔债索取的，是一个与不交族的每一格恰交于一点的集合。教科书的偿付方式是把宇宙良序化，再取每一格中最小的成员，而这条路在此处代价高昂：`L` 整体的良序是一个真类上的关系，而迄今造出的东西没有一样谈得上它。

有一条更廉价的路，它从「一格的诸成员**在哪里**」问起。一格是 `L` 的一个集合，故它的每个成员都现身于塔中某处；于是存在一个最早的层，其中已经现身了它的某个成员。那一层既不能是极限，也不能是零：集合进入塔的唯一途径是从它下面那一层中被雕出，故与该格相交的最早层，是某个与它不相交的层的后继。于是这一格自带一个典范的序数，即它首次现身之前的那一层；而在那个序数处，该格中最先现身的每个成员，都是同一个集合的可定义子集。

这提供了良序的替代方案。为一格选择成员时，只比较同一层上的名字，而不比较 `L` 的任意两个元素；用于记录所属层的序数就是比较所在的层，所以在不同层首次出现的集合不会相互比较。本章构造该序数，并证明后文需要的两项性质：它存在且唯一；同一个序数所确定的层包含给定集合、该集合的成员、这些成员的成员以及塔的极限层。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Choice.FirstIntersectionStage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

open hPropStructure 𝒮ᵥ
```

<!--en-->
## The predecessor of a least stage
<!--zh-->
## 最小层的前一层
<!--ja-->
## 最小段階の直前の段階
<!--/-->

<!--en-->
The question is whether a least ordinal stage at which an object appears must be
a successor; the result constructs its unique predecessor from a carve below it.
<!--zh-->
这里问的是：一个对象现身的最小序数层是否必为后继；结论由其下的一次雕出构造出唯一的前一层。
<!--ja-->
ここでは、対象が現れる最小の順序数段階が後者であるかを問い、その下での切り出しから一意な直前の段階を構成する。
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
The first case is the one minimality just ruled out, so the second holds, and the
least stage is a successor. The ruled-out case is a named helper with its
conclusion written down: that is the discipline the stages chapter set for every
split coming out of trichotomy, and `suc∈or≡`{.Agda} is a comparison written
in the form of membership.

Since the property is never read, it is a parameter, and the argument is written
once for every instance of the least-ordinal operator. `Carved`{.Agda} is the
datum it runs on: an ordinal below the least stage whose successor already has
the property. `carveAt`{.Agda} produces that datum, by reading a member out of
the least stage and renaming the carve to a successor; `predOf`{.Agda} consumes
it and closes the truncation on the uniqueness above. They are halves of one
operation rather than two operations, because `carveAt`{.Agda} builds exactly
what `predOf`{.Agda} takes, and no site has ever wanted one of them alone.
<!--zh-->
后继决定它所后继的东西，至少在序数之内如此。把一个候选前一层与另一个相比：各自属于对方的后继，故各自或是对方的成员、或与对方相等；而两个序数不能互为成员，否则传递性会使其一属于自身。于是「是给定序数的前一层」是命题，正是这一点使一个仅仅存在的前一层可以被读作一个确定的前一层。

最小层究竟凭什么有前一层？这正是本章核心的论证，而它没有用到关于格的任何东西。取任何一样到「某条序数性质成立的最小层」为止已出现的东西。属于一层，就是属于某个更早层的可定义子集，而后继恒等式说那些可定义子集就是下一层；故那样东西在那个更早层之上一层就已出现，而那条性质在那里就已成立。极小性禁止那一层严格低于最小层，而一个后继又不会越过头：它或属于最小层，或**就是**最小层。前一种情形正是极小性刚刚排除的，故后一种成立，于是最小层是后继。被排除的那一支写成写明结论的具名辅助件：这是讨论层的那一章为每个出自三歧的分情形定下的规则，而 `suc∈or≡`{.Agda} 不过是以成员关系形式写出的比较。

既然那条性质从未被读取，它就是一个参数，于是这个论证对最小序数算子的每个实例只写一遍。`Carved`{.Agda} 是它作用于其上的那个数据：最小层以下的一个序数，其后继已具备那条性质。`carveAt`{.Agda} 产出那个数据，办法是从最小层中读出一个成员，再把那次雕出改名为一个后继；`predOf`{.Agda} 则使用它，并按上面那条唯一性把截断闭合。它们是一次操作的两半、而不是两次操作，因为 `carveAt`{.Agda} 造出的恰是 `predOf`{.Agda} 所取用的，而没有任何用途只需其中一半。
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

module _ (P : S → hProp (ℓ-suc ℓ)) where

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
## 一层装下一个集合以下的一切
<!--ja-->
## 集合の下方全体を収める一つの段階
<!--/-->

<!--en-->
This section turns stage transitivity and an ordinal bound into one level that
contains a set's members, their members, and the limit level `ω`.
<!--zh-->
本节用层的传递性与序数上界，得到一个同时包含集合的成员、成员的成员以及极限层 `ω` 的层。
<!--ja-->
この節では、段階の推移性と順序数の上界から、集合の要素、その要素の要素、そして極限段階 `ω` を同時に含む一つの層を得る。
<!--/-->

<!--en-->
The other thing the construction needs is a bound, and no comparison is involved
in getting one. A stage is transitive, so the stage of a set already holds the
set's members, and their members after them; the earliest stage is a stage like
any other, so it serves.

One more ordinal remains to be fixed: the tower's limit level. The construction
ahead compares names; a name is built from numerals and pairs and from nothing
else, so it has appeared by `Lset ω`{.Agda}, and the chosen stage must therefore lie above `ω` as well as above the set's own stage. The bounding
ordinal of two ordinals settles that in one line, and monotonicity carries both
levels up into its stage.
<!--zh-->
构造还需要另一样东西：一个上界，而取得它不牵涉任何比较。层传递，故一个集合的层已经装着该集合的诸成员，以及其后它们的诸成员；最早的层与别的层无异，故它就够用。

还需要确定一个包含塔的极限层的序数。后续构造比较名字，而名字只由数码与有序对构成，所以到 `Lset ω`{.Agda} 为止已经出现。因此，所选层必须同时高于该集合自身所在的层和 `ω`。取这两个序数的上界序数，再用单调性，即可得到同时包含这两层的层。
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
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The chapter's reusable outputs are the unique predecessor of a least carved
stage and a bounding ordinal large enough for the later choice construction.
<!--zh-->
本章可复用的结果，是最小雕出层的唯一前一层，以及足以承载后续选择构造的上界序数。
<!--ja-->
本章の再利用可能な成果は、切り出しが生じる最小段階の一意な直前段階と、後の選択構成を収めるのに十分な上界順序数である。
<!--/-->

<!--en-->
The least stage at which a property of ordinals holds is a successor, because a
set enters the tower only by being carved out of the stage below. That argument
reads nothing about cells, so it is written once over any property of ordinals:
`carveAt`{.Agda} carves a witness below the least stage, and `predOf`{.Agda}
turns the carve into the predecessor, closing the truncation on
`isPropPredOf`{.Agda}. The predecessor is definite because a successor
determines what it succeeds among ordinals (`ord-suc-inj`{.Agda}).
`stageBound`{.Agda} supplies the bounding ordinal: above a set's own stage, hence above its members and
theirs, and above the tower's limit level, where the names themselves live.

Nothing here states a relation on `L`, and nothing here is a recursion. The
comparison and the recursion are both handled in the later chapters, and both are
confined to the material this one has located.
<!--zh-->
某条序数性质成立的最小层必为后继，因为集合进入塔的唯一途径是从它下面那一层中被雕出。这一论证不依赖格的任何性质，故对任意一条序数性质只需写一遍：`carveAt`{.Agda} 在最小层之下雕出一个见证，`predOf`{.Agda} 把这次雕出化为前一层，并按 `isPropPredOf`{.Agda} 使截断闭合。这个前一层之所以确定，是因为在序数之内后继决定它所后继的东西 (`ord-suc-inj`{.Agda})。`stageBound`{.Agda} 给出这个界所在的序数：它在一个集合自身的层之上，从而在其成员及其成员之上，也在塔的极限层之上，而诸名字恰在那里。

此处没有一条陈述涉及 `L` 上的关系，也没有一处是递归。比较与递归都留待后面几章处理，且二者都以本章所定位的材料为限。
<!--/-->
