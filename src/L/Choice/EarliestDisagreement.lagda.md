<!--en-->
# An internal family of earliest-disagreement relations
<!--zh-->
# 最早分歧关系的内部族
<!--ja-->
# 最初の相違の関係からなる内部の族
<!--/-->

<!--en-->
This chapter realizes every finite-stage earliest-disagreement relation as a set
of `L`, assembles those relations into a definable family, and proves the
object-language lookup at a numeral agrees with `before`{.Agda}.
<!--zh-->
本章把每个有穷阶段的最先分歧关系实现为 `L` 的集合，把这些关系合起来组成一个可定义族，并证明对象语言在数码处的查找与 `before`{.Agda} 相符。
<!--ja-->
本章では各有限段階の最初の相違の関係を `L` の集合として実現し、それらを定義可能な族にまとめ、対象言語での数項における値の読み取りが `before`{.Agda} と一致することを証明する。
<!--/-->

<!--en-->
The previous chapter left one hypothesis open, and named it exactly: a formula
saying that the earliest-disagreement order **at the numeral held in one slot**
puts a second slot before a third, together with its two readings against the
finite chapter's `before`{.Agda}. Everything else in the limit order is already
unconditional. This chapter discharges that hypothesis, and with it the chapter
before it.

What has to be built is a recursion along the numerals whose values are
**relations**: at zero the empty relation, and at the numeral after `n` the
comparison at the earliest disagreement over the stage at `n`, with the relation
at `n` as its base. A recursion whose values are sets cannot be named by a term,
so what gets described is an approximation, exactly as the tower and the order
table were described: an approximation predicate, a graph quantifying over
approximations, a value lemma pinning every value an approximation records, and
the object itself sealed where it is built.

Two things make this simpler than the tower was. The index is a member of
`ωʟ`{.Agda}, which is a **set**, so the outer induction is on a natural number
and the class-collection half of the hierarchy chapter does not arise; and the
step is already written, since the previous chapter's `PrecedesAt`{.Agda} holds
the base relation and the base stage in slots precisely so it can stand where the
relation is a recursion value. Two things make it harder. The value at a numeral
is a relation rather than a stage, so every step requires a separation over the pairs
of a finite stage; and the previous relation reaches a slot **inside** the
agreement clause, which is precisely the problematic shape, so it arrives as a
variable carrying its defining equation and never as an application.
<!--zh-->
上一章留下一处待证的假设，并准确地指出了它的内容：一条公式，说「在某个槽位所持有的数码处、按最先分歧处的那个序」把第二个槽位排在第三个之前，连同它对着有穷那一章的 `before`{.Agda} 的两条读式。极限之序的其余部分早已是无条件的。本章证明那条假设，并连带补全它前面那一章。

要构造的是沿诸数码递归得到的一族**关系**：零处为空关系；在 `n` 之后的数码处，则以 `n` 处的关系为基底，在 `n` 处的阶段上按最先分歧进行比较。取值为集合的递归无法由一个词项直接给出，因此这里描述的是逼近，其方式与描述塔及序之表相同：给出一个逼近谓词、一个量化所有逼近的图、一条固定逼近所记录之每个取值的值引理，并在对象构造之处将它封装。

有两点使它比塔更简便。索引是 `ωʟ`{.Agda} 的成员，而后者是个**集合**，故外层归纳是对一个自然数作的，层级那一章那半场真类收集根本不会出现；而那一步已经写好，因为上一章的 `PrecedesAt`{.Agda} 把基底关系与基底阶段存放在槽位里，正是为了使它能充当「关系是某场递归之取值」这一断言。也有两点使它更繁难。某个数码处的取值是关系而非阶段，故每一步都要在一个有穷阶段的诸对之上作一次分离；而上一个关系要出现在一致性子句**内部**的一个槽位上，那正是会出问题的形状，故它以变元的身份附带自己的定义等式，而不是以应用的身份出现。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.EarliestDisagreement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ¬̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using
  ( numeral-ord; #∈ω; ∈#-elim; #∈#-elim; mem-ord; boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ}
  using ( extensionalL; LsetS; ∅ʟ; finSet; finSet-in; finSet-out; module FinOf )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL; hasReplacementL )
open import L.Recursion {ℓ} lem using ( smallDom; mereFunct )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( before; precedes; Agrees; Witness; finiteStage )
open import L.Choice.LimitStageOrder {ℓ} lem
  using ( PrecedesAt; module Precedes; module Described )
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt; module RecShape )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; appAt; appAt-adequate; appC; appC-adequate; domAt-intro )
open import L.Coding.Expressions {ℓ} using ( numL; extAt; extAt-out; extAt-in; extAt-in-both )

import FOL.Absoluteness
import FOL.ZFModel
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Nat.Order using
  ( _<_; <-trans; <-asym; pred-≤-pred; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Induction.WellFounded using ( module WFI )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.FinData.Properties using ( toℕ<n; enum; toℕ∘enum )
open import Cubical.Data.FinData.Base using ( toℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = sh2 (sh2 i)

  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = sh2 (sh4 i)
```

Perf: the finite stage and the numerals are sealed where they are built.

```agda
opaque
  stageS : ℕ → S
  stageS n = LsetS (# n) (numeral-ord n)

  stageS-fst : (n : ℕ) → fst (stageS n) ≡ finiteStage n
  stageS-fst n = refl

  numS : ℕ → S
  numS k = # k , numL k

  numS-fst : (k : ℕ) → fst (numS k) ≡ # k
  numS-fst k = refl

  memS : (A : S) (z : V ℓ) → ⟨ z ∈ fst A ⟩ → S
  memS A z h = z , isL-trans {x = fst A} {y = z} h (snd A)

  memS-fst : (A : S) (z : V ℓ) (h : ⟨ z ∈ fst A ⟩) → fst (memS A z h) ≡ z
  memS-fst A z h = refl

  prS : S → S → S
  prS a b = prʟ a b

  prS-fst : (a b : S) → fst (prS a b) ≡ pr (fst a) (fst b)
  prS-fst a b = prʟ-fst a b

stageEl : (n : ℕ) (x : V ℓ) → ⟨ x ∈ finiteStage n ⟩ → S
stageEl n x h = x , Lset→isL (# n) (numeral-ord n) x h
```

<!--en-->
## Each stage's relation, as an element of `L`

<!--zh-->
## 每个阶段的关系，作为 `L` 的一个元素
<!--ja-->
## 各段階の関係を `L` の要素にする
<!--/-->

<!--en-->
For each numeral `n`, separation carves `relAt n`{.Agda} from a bounded set of
pairs, and the two representation lemmas identify its members with
`before n`{.Agda}.
<!--zh-->
对每个数码 `n`，分离从一组有界的对出发给出 `relAt n`{.Agda}；两条表示引理把它的成员与 `before n`{.Agda} 对应起来。
<!--ja-->
各数項 `n` について、分出公理が有界な順序対の集合から `relAt n`{.Agda} を切り出し、二つの表現補題がその要素を `before n`{.Agda} と対応づける。
<!--/-->

<!--en-->

The pairs the relation at a stage can relate cannot escape a single set: the
members of a finite stage are a small family of elements of `L` and so are their
pairs, and the recursion chapter's bounding lemma confines them all at once. The
separation that carves the relation out of that bound is where the extra cost
over the tower sits, and it is paid once per numeral.

The condition it carves with is the previous chapter's step description and
nothing else. That description holds the base relation and the base stage in
**slots**, and a separation is done with a formula of one free variable, so the
two are bound by existentials and **pinned to constants by the object equality**.
That is what lets the step description be used here exactly as it was delivered,
with no second copy written against constants: one formula, two consumers.

`relAt-out`{.Agda} and `relAt-in`{.Agda} are the recursion's two readings, and
they are proved together, by the ordinary induction on the numeral. Each direction
uses the other at the predecessor, because the previous relation is consulted
only inside the agreement clause, and `precedes-map`{.Agda} is the one line that
carries it across: agreement is contravariant in the base relation, so passing
from the recorded relation to `before`{.Agda} needs the reading in the opposite
direction. `relAt-rep`{.Agda} and `relAt-fill`{.Agda} are the corollaries a
consumer wants, at a pair rather than at a member.
<!--zh-->

某个阶段处的关系所能关联的对全部落在同一个集合里：有穷阶段的成员构成 `L` 元素的一个小族，它们的对也是如此，递归那一章的界层引理则一并给出这个界。把该关系限定到这个界上的分离，正是超出塔的那笔开销所在，而且每个数码都要付出一次。

它据以构造的条件就是上一章那条步进描述，别无其他。那条描述把基底关系与基底阶段放在**槽位**里，而分离用带单个自由变量的公式表达，故这两样由存在量词绑定，并**用对象等词固定到诸常元上**。正因如此，那条步进描述能在此处按原样使用，无须再针对常元写第二份：一条公式，两处使用。

`relAt-out`{.Agda} 与 `relAt-in`{.Agda} 是这场递归的两条读式，二者用对数码的普通归纳一并证出。每个方向的证明都要在前趋处用到另一个方向：上一个关系只在一致性子句内部被查阅，而 `precedes-map`{.Agda} 正是完成这一转换的那一行。一致性对基底关系是反变的，故从被记录的关系走到 `before`{.Agda}，需要的是反方向的那条读式。`relAt-rep`{.Agda} 与 `relAt-fill`{.Agda} 是使用者需要的推论，其对象是一个对，而不是一个成员。
<!--/-->

Every pair of members of a finite stage lies in one set of the model.

```agda
pairsAt : (n : ℕ)
        → Σ[ D ∈ S ] ((u v : V ℓ) → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
                     → ⟨ pr u v ∈ fst D ⟩)
pairsAt n = d .fst , onPair
  where
  ixL : ⟪ finiteStage n ⟫ → S
  ixL m = ⟪ finiteStage n ⟫↪ m
        , Lset→isL (# n) (numeral-ord n) (⟪ finiteStage n ⟫↪ m)
            (∈∈ₛ {a = ⟪ finiteStage n ⟫↪ m} {b = finiteStage n} .snd
              (∈ₛ⟪ finiteStage n ⟫↪ m))

  d : Σ[ D ∈ S ] ((p : ⟪ finiteStage n ⟫ × ⟪ finiteStage n ⟫)
                  → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
  d = smallDom (⟪ finiteStage n ⟫ × ⟪ finiteStage n ⟫)
        (λ p → prʟ (ixL (fst p)) (ixL (snd p)))

  onPair : (u v : V ℓ) → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
         → ⟨ pr u v ∈ fst (d .fst) ⟩
  onPair u v hu hv = subst (λ t → ⟨ t ∈ fst (d .fst) ⟩)
    (prʟ-fst (ixL (fu .fst)) (ixL (fv .fst)) ∙ cong₂ pr (fu .snd) (fv .snd))
    (d .snd (fu .fst , fv .fst))
    where
    fu = ∈-asFiber {a = u} {b = finiteStage n} hu
    fv = ∈-asFiber {a = v} {b = finiteStage n} hv
```

The base relation transferred across the agreement clause.

```agda
precedes-map : (R R' : V ℓ → V ℓ → Ω) (A x y : V ℓ)
             → ((w z : V ℓ) → ⟨ w ∈ A ⟩ → ⟨ z ∈ A ⟩ → ⟨ R' w z ⟩ → ⟨ R w z ⟩)
             → ⟨ precedes R A x y ⟩ → ⟨ precedes R' A x y ⟩
precedes-map R R' A x y f = PT.map step
  where
  step : Σ[ z ∈ V ℓ ] Witness R A x y z → Σ[ z ∈ V ℓ ] Witness R' A x y z
  step (z , (z∈A , (z∈y , (z∉x , ag)))) =
    z , (z∈A , (z∈y , (z∉x , ag')))
    where
    ag' : Agrees R' A x y z
    ag' w w∈A hR' = ag w w∈A (f w z w∈A z∈A hR')
```

The condition the separation carves with: the base relation and the base stage
arrive as bound variables pinned to constants, so the step description stands at
slots exactly as it was delivered.

```agda
RelCond : (R A A' : S) → Formula S 1
RelCond R A A' =
  ∃̇ ( (var zero ≐ con R)
    ∧̇ ∃̇ ( (var zero ≐ con A)
         ∧̇ ∃̇∈ (con A') ( ∃̇∈ (con A')
              ( prAtL (sh2 (sh2 zero)) (suc zero) zero
              ∧̇ PrecedesAt (sh2 (suc zero)) (sh2 zero) (suc zero) zero ) ) ) )

opaque
  relAt : ℕ → S
  relAt zero    = ∅ʟ
  relAt (suc n) =
    hasSeparationL (pairsAt (suc n) .fst)
      (RelCond (relAt n) (stageS n) (stageS (suc n))) .fst .fst

  relAt-zero : relAt zero ≡ ∅ʟ
  relAt-zero = refl

  relAt-mem : (n : ℕ) (z : S)
            → (z ∈ˢ relAt (suc n))
            ≡ ( (z ∈ˢ pairsAt (suc n) .fst)
              ⊓ ((z ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n))) )
  relAt-mem n =
    hasSeparationL (pairsAt (suc n) .fst)
      (RelCond (relAt n) (stageS n) (stageS (suc n))) .fst .snd

Rel : ℕ → V ℓ → V ℓ → Ω
Rel n a b = pr a b ∈ fst (relAt n)

private
  s1 : Fin 5
  s1 = suc zero
  s2 : Fin 5
  s2 = sh2 zero
  s3 : Fin 5
  s3 = sh2 (suc zero)
  s4 : Fin 5
  s4 = sh2 (sh2 zero)

RelOf : (k : ℕ) → V ℓ → Type (ℓ-suc ℓ)
RelOf k zv = Σ[ x ∈ S ] Σ[ y ∈ S ]
  ( ⟨ fst x ∈ finiteStage k ⟩
  × ( ⟨ fst y ∈ finiteStage k ⟩
    × ( (zv ≡ pr (fst x) (fst y)) × ⟨ before k (fst x) (fst y) ⟩ ) ) )

relAt-out : (k : ℕ) (zv : V ℓ) → ⟨ zv ∈ fst (relAt k) ⟩ → ∥ RelOf k zv ∥₁
relAt-in  : (k : ℕ) (zv : V ℓ) → RelOf k zv → ⟨ zv ∈ fst (relAt k) ⟩

relAt-out zero zv h = Empty.rec
  (∅-empty zv (∈∈ₛ {a = zv} {b = ∅} .fst
    (subst (λ t → ⟨ zv ∈ fst t ⟩) relAt-zero h)))
relAt-out (suc n) zv h = PT.rec squash₁
  (λ { (r , (qr , ha)) → PT.rec squash₁
    (λ { (a , (qa , hx)) → PT.rec squash₁
      (λ { (x , (x∈ , hy)) → PT.map (atY r a x qr qa x∈) hy }) hx }) ha }) cond
  where
  zS : S
  zS = memS (relAt (suc n)) zv h
  qz : fst zS ≡ zv
  qz = memS-fst (relAt (suc n)) zv h

  cond : ⟨ (zS ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n)) ⟩
  cond = subst ⟨_⟩ (relAt-mem n zS)
    (subst (λ t → ⟨ t ∈ fst (relAt (suc n)) ⟩) (sym qz) h) .snd

  Body : (r a x y : S) → Type (ℓ-suc ℓ)
  Body r a x y =
      ⟨ (y ∷ x ∷ a ∷ r ∷ zS ∷ []) ⊨ prAtL s4 s1 zero ⟩
    × ⟨ (y ∷ x ∷ a ∷ r ∷ zS ∷ []) ⊨ PrecedesAt s3 s2 s1 zero ⟩

  AtY : (r a x : S) → Type (ℓ-suc ℓ)
  AtY r a x = Σ[ y ∈ S ] (⟨ fst y ∈ fst (stageS (suc n)) ⟩ × Body r a x y)

  atY : (r a x : S) → fst r ≡ fst (relAt n) → fst a ≡ fst (stageS n)
      → ⟨ fst x ∈ fst (stageS (suc n)) ⟩ → AtY r a x → RelOf (suc n) zv
  atY r a x qr qa x∈ (y , (y∈ , (hpr , hprec))) =
    x , (y , ( subst (λ t → ⟨ fst x ∈ t ⟩) (stageS-fst (suc n)) x∈
             , ( subst (λ t → ⟨ fst y ∈ t ⟩) (stageS-fst (suc n)) y∈
               , (sym qz ∙ qpair , below) ) ) )
    where
    Rrep : (s t : S) → ⟨ pr (fst s) (fst t) ∈ fst (lookup s3 (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) ⟩
         → ⟨ Rel n (fst s) (fst t) ⟩
    Rrep s t p = subst (λ w → ⟨ pr (fst s) (fst t) ∈ w ⟩) qr p

    Rfill : (s t : S) → ⟨ Rel n (fst s) (fst t) ⟩
          → ⟨ pr (fst s) (fst t) ∈ fst (lookup s3 (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) ⟩
    Rfill s t p = subst (λ w → ⟨ pr (fst s) (fst t) ∈ w ⟩) (sym qr) p

    module P = Precedes s3 s2 s1 zero (y ∷ x ∷ a ∷ r ∷ zS ∷ [])
                        (Rel n) Rrep Rfill

    onStage : ⟨ precedes (Rel n) (finiteStage n) (fst x) (fst y) ⟩
    onStage = subst (λ w → ⟨ precedes (Rel n) w (fst x) (fst y) ⟩)
      (qa ∙ stageS-fst n) (P.PrecedesAt-out hprec)

    below : ⟨ before (suc n) (fst x) (fst y) ⟩
    below = precedes-map (Rel n) (before n) (finiteStage n) (fst x) (fst y)
      (λ w t hw ht hb → relAt-in n (pr w t)
        (stageEl n w hw , (stageEl n t ht , (hw , (ht , (refl , hb))))))
      onStage

    qpair : fst zS ≡ pr (fst x) (fst y)
    qpair = subst ⟨_⟩ (prAtL-adequate s4 s1 zero (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) hpr


relAt-in zero zv (x , (y , (x∈ , (y∈ , (qq , hb))))) = Empty.rec* hb
relAt-in (suc n) zv (x , (y , (x∈ , (y∈ , (qq , hb))))) =
  subst (λ t → ⟨ t ∈ fst (relAt (suc n)) ⟩) (prS-fst x y ∙ sym qq)
    (subst ⟨_⟩ (sym (relAt-mem n (prS x y))) (inBound , cond))
  where
  inBound : ⟨ prS x y ∈ˢ pairsAt (suc n) .fst ⟩
  inBound = subst (λ t → ⟨ t ∈ fst (pairsAt (suc n) .fst) ⟩) (sym (prS-fst x y))
    (pairsAt (suc n) .snd (fst x) (fst y) x∈ y∈)

  module P = Precedes s3 s2 s1 zero
                      (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ [])
                      (Rel n) (λ _ _ p → p) (λ _ _ p → p)

  held : ⟨ precedes (Rel n) (finiteStage n) (fst x) (fst y) ⟩
  held = precedes-map (before n) (Rel n) (finiteStage n) (fst x) (fst y)
    (λ w t hw ht hR → PT.rec (snd (before n w t)) (readBack w t)
      (relAt-out n (pr w t) hR))
    hb
    where
    readBack : (w t : V ℓ) → RelOf n (pr w t) → ⟨ before n w t ⟩
    readBack w t (p , (q , (p∈ , (q∈ , (qq' , hbf))))) =
      subst2 (λ s u → ⟨ before n s u ⟩)
        (sym (pr-inj qq' .fst)) (sym (pr-inj qq' .snd)) hbf

  hprec : ⟨ (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ [])
          ⊨ PrecedesAt s3 s2 s1 zero ⟩
  hprec = P.PrecedesAt-in
    (subst (λ w → ⟨ precedes (Rel n) w (fst x) (fst y) ⟩) (sym (stageS-fst n))
      held)

  hpr : ⟨ (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ []) ⊨ prAtL s4 s1 zero ⟩
  hpr = subst ⟨_⟩
    (sym (prAtL-adequate s4 s1 zero
      (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ []))) (prS-fst x y)

  onStage : (w : V ℓ) → ⟨ w ∈ finiteStage (suc n) ⟩
          → ⟨ w ∈ fst (stageS (suc n)) ⟩
  onStage w hw = subst (λ t → ⟨ w ∈ t ⟩) (sym (stageS-fst (suc n))) hw

  cond : ⟨ (prS x y ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n)) ⟩
  cond = ∣ relAt n , (refl
       , ∣ stageS n , (refl
       , ∣ x , (onStage (fst x) x∈
       , ∣ y , (onStage (fst y) y∈ , (hpr , hprec)) ∣₁) ∣₁) ∣₁) ∣₁

relAt-rep : (n : ℕ) (u v : V ℓ)
          → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
          → ⟨ pr u v ∈ fst (relAt n) ⟩ → ⟨ before n u v ⟩
relAt-rep n u v hu hv h = PT.rec (snd (before n u v)) read (relAt-out n (pr u v) h)
  where
  read : RelOf n (pr u v) → ⟨ before n u v ⟩
  read (p , (q , (p∈ , (q∈ , (qq , hbf))))) =
    subst2 (λ s t → ⟨ before n s t ⟩)
      (sym (pr-inj qq .fst)) (sym (pr-inj qq .snd)) hbf

relAt-fill : (n : ℕ) (u v : V ℓ)
           → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
           → ⟨ before n u v ⟩ → ⟨ pr u v ∈ fst (relAt n) ⟩
relAt-fill n u v hu hv h = relAt-in n (pr u v)
  (stageEl n u hu , (stageEl n v hv , (hu , (hv , (refl , h)))))
```

<!--en-->
## The step, generic in everything it consults

<!--zh-->
## 那一步，对它所查阅的一切保持通用
<!--ja-->
## 参照対象すべてに一般的なステップ
<!--/-->

<!--en-->
The step formula is parameterized by the table, bound, and candidate relation;
`StepOf`{.Agda} states its semantic meaning without fixing any one realization.
<!--zh-->
步进公式以表、界与候选关系为参数；`StepOf`{.Agda} 在不固定任何特定实现的情况下陈述其语义。
<!--ja-->
ステップ論理式は表、上界、候補関係をパラメータとし、`StepOf`{.Agda} は特定の実現を固定せずにその意味を述べる。
<!--/-->

<!--en-->

The body of the recursion's step is written once, with the member, the index and
the approximation all in **slots**, and six binders under it: the predecessor of
the index, the relation the approximation records there, the stage at the
predecessor, the stage at the index, and the two sets being compared.

The predecessor is not a term of the object language and does not have to be. A
numeral is a finite linear order under membership, so its predecessor is its
`∈`-**maximal** member, and that is two atoms: `c` belongs to the index, and no
member of the index has `c` as a member. Written that way no object equality is
needed anywhere, and at the numeral zero there is no such `c`, so the step is
empty there, which is what the recursion wants.

The two stages are reached by the sequence chapter's graph, which is the only way
to reach a stage, and the stage at the index is what confines the value: without
it the extension would be a proper class, since the comparison at the earliest
disagreement never mentions where the two compared sets live. `StepOf`{.Agda}
writes the payload out rather than leaving it to inference, and both readings
stand at variable slots in a variable environment with ordinality at the index as
their only hypothesis.
<!--zh-->

递归那一步的体只写一次，其中成员、索引与逼近三者都在**槽位**里，其下有六层绑定：索引的前趋、逼近在那里所记录的关系、前趋处的阶段、索引处的阶段，以及被比较的那两个集合。

前趋不是对象语言的词项，也不必是。数码在隶属之下是一个有穷线序，故它的前趋就是它的 `∈`-**极大**成员，而那是两个原子：`c` 属于索引，且索引的任何成员都不以 `c` 为成员。这样写，任何地方都不需要对象等词；而在数码零处根本没有这样的 `c`，故那一步在那里是空的，而这正是这场递归想要的。

两个阶段由序列一章的图给出，这是确定相应阶段的唯一方式。索引处的阶段为关系取值提供集合界；若没有这个界，最先分歧比较并不限制被比较的两个集合所属的阶段，其外延会成为真类。`StepOf`{.Agda} 明确写出所携带的数据，不把它留给类型推断；两条读式都在以变元表示环境分量的形式下陈述，唯一假设是索引处的序数性。
<!--/-->

```agda
Held : S → V ℓ → V ℓ → Ω
Held r a b = pr a b ∈ fst r

opaque
 RelBodyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
 RelBodyAt z b f =
   ∃̇ ( (var zero ∈̇ var (suc b))
     ∧̇ ( ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero))
       ∧̇ ∃̇ ( appAt (sh2 f) (suc zero) zero
            ∧̇ ∃̇ ( LsetGraphAt zero (suc (suc zero))
                 ∧̇ ∃̇ ( LsetGraphAt zero (sh4 b)
                      ∧̇ ∃̇∈ (var zero)
                           ( ∃̇∈ (var (suc zero))
                               ( prAtL (sh6 z) (suc zero) zero
                               ∧̇ PrecedesAt (suc (suc (suc (suc zero))))
                                             (suc (suc (suc zero)))
                                             (suc zero) zero ) ) ) ) ) ) )

StepOf : ∀ {n} → Fin n → Fin n → S ^ n → V ℓ → Type (ℓ-suc ℓ)
StepOf b f γ zv =
  Σ[ c ∈ S ] Σ[ r ∈ S ] Σ[ x ∈ S ] Σ[ y ∈ S ]
    ( ⟨ fst c ∈ fst (lookup b γ) ⟩
    × ( ((d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩ → ⟨ fst c ∈ fst d ⟩ → Empty.⊥)
      × ( ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        × ( ⟨ fst x ∈ Lset (fst (lookup b γ)) ⟩
          × ( ⟨ fst y ∈ Lset (fst (lookup b γ)) ⟩
            × ( (zv ≡ pr (fst x) (fst y))
              × ⟨ precedes (Held r) (Lset (fst c)) (fst x) (fst y) ⟩ ) ) ) ) ) )

module _ {n : ℕ} (z b f : Fin n) (γ : S ^ n)
         (ob : IsOrd (fst (lookup b γ))) where
  private
    Body : (c r A A' x y : S) → Type (ℓ-suc ℓ)
    Body c r A A' x y =
        ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ) ⊨ prAtL (sh6 z) (suc zero) zero ⟩
      × ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
          ⊨ PrecedesAt (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                       (suc zero) zero ⟩

    AtY : (c r A A' x : S) → Type (ℓ-suc ℓ)
    AtY c r A A' x = Σ[ y ∈ S ] (⟨ fst y ∈ fst A' ⟩ × Body c r A A' x y)

    MaxOf : (c : S) → Type (ℓ-suc ℓ)
    MaxOf c = (d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩ → ⟨ fst c ∈ fst d ⟩
            → Empty.⊥

    atY : (c r A A' x : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → fst A ≡ Lset (fst c) → fst A' ≡ Lset (fst (lookup b γ))
        → ⟨ fst x ∈ fst A' ⟩
        → AtY c r A A' x → StepOf b f γ (fst (lookup z γ))
    atY c r A A' x c∈ cmax hf qA qA' x∈ (y , (y∈ , (hpr , hprec))) =
      c , (r , (x , (y , (c∈ , (cmax , (hf
        , ( subst (λ t → ⟨ fst x ∈ t ⟩) qA' x∈
          , ( subst (λ t → ⟨ fst y ∈ t ⟩) qA' y∈
            , (qpair , hprec') ) ) ) ) ) ) ) )
      where
      module P = Precedes (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                          (suc zero) zero (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
                          (Held r) (λ _ _ p → p) (λ _ _ p → p)

      hprec' : ⟨ precedes (Held r) (Lset (fst c)) (fst x) (fst y) ⟩
      hprec' = subst (λ t → ⟨ precedes (Held r) t (fst x) (fst y) ⟩) qA
        (P.PrecedesAt-out hprec)

      qpair : fst (lookup z γ) ≡ pr (fst x) (fst y)
      qpair = subst ⟨_⟩
        (prAtL-adequate (sh6 z) (suc zero) zero
          (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)) hpr

    AtX : (c r A A' : S) → Type (ℓ-suc ℓ)
    AtX c r A A' = Σ[ x ∈ S ] (⟨ fst x ∈ fst A' ⟩ × ∥ AtY c r A A' x ∥₁)

    atX : (c r A A' : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → fst A ≡ Lset (fst c) → fst A' ≡ Lset (fst (lookup b γ))
        → AtX c r A A' → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atX c r A A' c∈ cmax hf qA qA' (x , (x∈ , hy)) =
      PT.map (atY c r A A' x c∈ cmax hf qA qA' x∈) hy

    AtA' : (c r A : S) → Type (ℓ-suc ℓ)
    AtA' c r A = Σ[ A' ∈ S ]
      ( ⟨ (A' ∷ A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (sh4 b) ⟩
      × ∥ AtX c r A A' ∥₁ )

    atA' : (c r A : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
         → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
         → fst A ≡ Lset (fst c)
         → AtA' c r A → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atA' c r A c∈ cmax hf qA (A' , (hg , hx)) =
      PT.rec squash₁ (atX c r A A' c∈ cmax hf qA qA') hx
      where
      qA' : fst A' ≡ Lset (fst (lookup b γ))
      qA' = Lset-only zero (sh4 b) (A' ∷ A ∷ r ∷ c ∷ γ) hg ob

    AtA : (c r : S) → Type (ℓ-suc ℓ)
    AtA c r = Σ[ A ∈ S ]
      ( ⟨ (A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
      × ∥ AtA' c r A ∥₁ )

    atA : (c r : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → AtA c r → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atA c r c∈ cmax hf (A , (hg , hA')) =
      PT.rec squash₁ (atA' c r A c∈ cmax hf qA) hA'
      where
      qA : fst A ≡ Lset (fst c)
      qA = Lset-only zero (suc (suc zero)) (A ∷ r ∷ c ∷ γ) hg
        (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈)

    AtR : (c : S) → Type (ℓ-suc ℓ)
    AtR c = Σ[ r ∈ S ]
      ( ⟨ (r ∷ c ∷ γ) ⊨ appAt (sh2 f) (suc zero) zero ⟩ × ∥ AtA c r ∥₁ )

    atR : (c : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → AtR c → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atR c c∈ cmax (r , (happ , hA)) = PT.rec squash₁ (atA c r c∈ cmax hf) hA
      where
      hf : ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
      hf = subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero (r ∷ c ∷ γ)) happ

    AtC : Type (ℓ-suc ℓ)
    AtC = Σ[ c ∈ S ]
      ( ⟨ fst c ∈ fst (lookup b γ) ⟩
      × ( ⟨ (c ∷ γ) ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
        × ∥ AtR c ∥₁ ) )

    atC : AtC → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atC (c , (c∈ , (hmax , hr))) = PT.rec squash₁ (atR c c∈ cmax) hr
      where
      cmax : MaxOf c
      cmax d hd hc = lower (hmax d hd hc)

  opaque
   unfolding RelBodyAt

   RelBody-out : ⟨ γ ⊨ RelBodyAt z b f ⟩
               → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
   RelBody-out = PT.rec squash₁ atC

   RelBody-in : StepOf b f γ (fst (lookup z γ)) → ⟨ γ ⊨ RelBodyAt z b f ⟩
   RelBody-in (c , (r , (x , (y , (c∈ , (cmax , (hf , (x∈ , (y∈
              , (qpair , hprec))))))))))
     = ∣ c , (c∈ , (hmax , ∣ r , (happ , ∣ A , (hgA , ∣ A' , (hgA'
       , ∣ x , (x∈ , ∣ y , (y∈ , (hpr , hprec')) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)) ∣₁
     where
     oc : IsOrd (fst c)
     oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈

     A : S
     A = LsetS (fst c) oc

     A' : S
     A' = LsetS (fst (lookup b γ)) ob

     hmax : ⟨ (c ∷ γ) ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
     hmax d hd hc = lift (cmax d hd hc)

     happ : ⟨ (r ∷ c ∷ γ) ⊨ appAt (sh2 f) (suc zero) zero ⟩
     happ = subst ⟨_⟩
       (sym (appAt-adequate (sh2 f) (suc zero) zero (r ∷ c ∷ γ))) hf

     hgA : ⟨ (A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
     hgA = Lset-defines zero (suc (suc zero)) (A ∷ r ∷ c ∷ γ) oc refl

     hgA' : ⟨ (A' ∷ A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (sh4 b) ⟩
     hgA' = Lset-defines zero (sh4 b) (A' ∷ A ∷ r ∷ c ∷ γ) ob refl

     hpr : ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ) ⊨ prAtL (sh6 z) (suc zero) zero ⟩
     hpr = subst ⟨_⟩
       (sym (prAtL-adequate (sh6 z) (suc zero) zero
         (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ))) qpair

     module P = Precedes (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                         (suc zero) zero (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
                         (Held r) (λ _ _ p → p) (λ _ _ p → p)

     hprec' : ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
              ⊨ PrecedesAt (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                           (suc zero) zero ⟩
     hprec' = P.PrecedesAt-in hprec
 ```

 ```agda
```

<!--en-->
## The approximation and the graph

<!--zh-->
## 逼近与那个图
<!--ja-->
## 近似とグラフ
<!--/-->

<!--en-->
`ApproxAt`{.Agda} says a finite table contains exactly the earlier relation
values it should, while `RelGraphAt`{.Agda} adds the next step value at the
current numeral.
<!--zh-->
`ApproxAt`{.Agda} 断言有穷表恰好包含应有的较早关系取值，而 `RelGraphAt`{.Agda} 在当前数码处加入下一步取值。
<!--ja-->
`ApproxAt`{.Agda} は有限表が必要な以前の関係値をちょうど含むことを述べ、`RelGraphAt`{.Agda} は現在の数項で次のステップ値を加える。
<!--/-->

<!--en-->

Off the template, and shorter than the template, because the domain machinery and
the extension machinery are used exactly as delivered. `RelStepAt`{.Agda} is one
`extAt`{.Agda} over the body. `ApproxAt`{.Agda} is two conjuncts, the domain and
the step condition, and there is deliberately no single-valuedness conjunct: the
step condition already pins every value recorded at an argument, so
single-valuedness is a corollary. `RelGraphAt`{.Agda} is one existential over the
approximation with those two conjuncts under it.

Two descriptions are **sealed where they are built**, and this is the chapter's
own measurement rather than an inherited habit. `RelStepAt`{.Agda} wraps the
body, and the body carries two copies of the sequence chapter's graph. Unsealed,
every satisfaction of the graph at a concrete environment normalizes a formula
carrying two copies of the whole hierarchy description inside it, and the chapter
takes 376 s; sealed, with each reading unfolding its own description and nothing
else, it takes 3.8 s. That is a factor of ninety-nine, and no mathematics changed.
<!--zh-->

照模板来，且比模板更短，因为定义域与外延两套器械都按原样使用。`RelStepAt`{.Agda} 是对体作一次 `extAt`{.Agda}。`ApproxAt`{.Agda} 含两个合取项，即定义域与那条步进条件，且刻意不写单值性合取项：步进条件已经唯一确定每个实参处记录的取值，故单值性是一条推论。`RelGraphAt`{.Agda} 是对逼近的一个存在量词，其下是那两个合取项。

两条描述都在构造之处封装，这是本章实测所得的选择，并非沿用既有习惯。`RelStepAt`{.Agda} 包含那个公式体，而公式体携带序列一章之图的两份副本。若不封装，图在具体环境上的每次满足关系都要正规化一条内部含有两份完整层级描述的公式，本章耗时 376 秒；封装后，每条读式只展开自身的描述，本章耗时 3.8 秒。两者相差九十九倍，而数学内容完全相同。
<!--/-->

```agda
opaque
  RelStepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  RelStepAt v b f = extAt v (RelBodyAt zero (suc b) (suc f))

module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n)
         (ob : IsOrd (fst (lookup b γ))) where
  opaque
   unfolding RelStepAt

   RelStep-out : ⟨ γ ⊨ RelStepAt v b f ⟩ → (w : S)
               → ⟨ fst w ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ (fst w) ∥₁
   RelStep-out h w hw = RelBody-out zero (suc b) (suc f) (w ∷ γ) ob
     (extAt-out v (RelBodyAt zero (suc b) (suc f)) γ h w hw)

   RelStep-back : ⟨ γ ⊨ RelStepAt v b f ⟩ → (w : S) → StepOf b f γ (fst w)
                → ⟨ fst w ∈ fst (lookup v γ) ⟩
   RelStep-back h w s = extAt-in v (RelBodyAt zero (suc b) (suc f)) γ h w
     (RelBody-in zero (suc b) (suc f) (w ∷ γ) ob s)

   RelStep-in : ((w : S) → ⟨ fst w ∈ fst (lookup v γ) ⟩
                 → ∥ StepOf b f γ (fst w) ∥₁)
              → ((w : S) → StepOf b f γ (fst w)
                 → ⟨ fst w ∈ fst (lookup v γ) ⟩)
              → ⟨ γ ⊨ RelStepAt v b f ⟩
   RelStep-in into back = extAt-in-both v (RelBodyAt zero (suc b) (suc f)) γ
     (λ w hw → PT.rec (snd ((w ∷ γ) ⊨ RelBodyAt zero (suc b) (suc f)))
       (RelBody-in zero (suc b) (suc f) (w ∷ γ) ob) (into w hw))
     (λ w h → PT.rec (snd (fst w ∈ fst (lookup v γ))) (back w)
       (RelBody-out zero (suc b) (suc f) (w ∷ γ) ob h))

module A = RecShape RelStepAt
open A using ( ApproxAt; ApproxAt-value; ApproxAt-step
             ; ApproxAt-in; GraphOf; PairOf )
     renaming ( GraphAt to RelGraphAt; Graph-in to RelGraph-in
              ; Graph-out to RelGraph-out; PairGraphAt to PairRelGraphAt
              ; PairGraph-in to PairRelGraph-in
              ; PairGraph-out to PairRelGraph-out )
 ```

 ```agda
```

<!--en-->
## The step, against the recursion

<!--zh-->
## 那一步，对着这场递归
<!--ja-->
## 再帰に対するステップ
<!--/-->

<!--en-->
The two step lemmas show that when a table contains the previously constructed
relations, the internal step formula holds exactly of `relAt k`{.Agda}.
<!--zh-->
两条步进引理表明：当一张表包含此前构造的诸关系时，内部步进公式恰好对 `relAt k`{.Agda} 成立。
<!--ja-->
二つのステップ補題は、表がそれ以前に構成された関係を含むとき、内部のステップ論理式がちょうど `relAt k`{.Agda} について成り立つことを示す。
<!--/-->

<!--en-->

The bridge, and both halves come out of the same two private lines. Given a
correct and complete table below the index, the step at the index is exactly the
relation the meta-language computes there: `step-rel`{.Agda} reads a satisfied
step and gets the relation back, `rel-step`{.Agda} writes the step from the
relation.

Both proofs perform the predecessor analysis, and it is the only place
trichotomy on the naturals is used in this chapter: a member of the index that
is `∈`-maximal in it is its predecessor, because a numeral strictly between
would contradict maximality on one side and the membership on the other. Once
the index is known to be a successor the rest is bookkeeping: the recorded
relation there is the recursion's value by correctness, the stage there is the
tower's value by the sequence chapter's graph, and `precedes-map`{.Agda} carries
the comparison between the two spellings of the base relation.
<!--zh-->

这一联系由同样两行私有代码给出。给定索引以下的一张正确且完备的表，索引处的那一步恰是元语言在那里算出的那个关系：`step-rel`{.Agda} 从一个被满足的步进读出关系，`rel-step`{.Agda} 则由关系写出那一步。

两者的证明都要做前趋分析，而这是本章唯一用到自然数三歧的地方：索引中在 `∈` 下极大的成员就是它的前趋，因为严格介于二者之间的数码会一边违反极大性，一边违反隶属。一旦知道索引是后继，剩下的只是核对两件事：那里被记录的关系因正确性而是这场递归的取值，那里的阶段因序列那一章的图而是塔的取值，而 `precedes-map`{.Agda} 则在基底关系的两种写法之间转换那次比较。
<!--/-->

```agda
Values : S → ℕ → Type (ℓ-suc ℓ)
Values g k = (m : ℕ) → m < k → (w : S)
           → ⟨ pr (# m) (fst w) ∈ fst g ⟩ → fst w ≡ fst (relAt m)

Entries : S → ℕ → Type (ℓ-suc ℓ)
Entries g k = (m : ℕ) → m < k → ⟨ pr (# m) (fst (relAt m)) ∈ fst g ⟩

before-suc : (k : ℕ) (x y : V ℓ) → ⟨ before k x y ⟩ → Σ[ m ∈ ℕ ] (k ≡ suc m)
before-suc zero    x y h = Empty.rec* h
before-suc (suc m) x y h = m , refl

module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) (k : ℕ)
         (qb : fst (lookup b γ) ≡ # k)
         (vals : Values (lookup f γ) k) (ents : Entries (lookup f γ) k) where
  private
    ob : IsOrd (fst (lookup b γ))
    ob = subst IsOrd (sym qb) (numeral-ord k)

    into : (x : V ℓ) → StepOf b f γ x → ⟨ x ∈ fst (relAt k) ⟩
    into x (c , (r , (xx , (yy , (c∈ , (cmax , (hf , (xx∈ , (yy∈
           , (qx , hprec)))))))))) =
      PT.rec (snd (x ∈ fst (relAt k))) atC
        (∈#-elim k (fst c) (subst (λ t → ⟨ fst c ∈ t ⟩) qb c∈))
      where
      atC : Σ[ m ∈ ℕ ] ((m < k) × (fst c ≡ # m)) → ⟨ x ∈ fst (relAt k) ⟩
      atC (m , (hm , qc)) = relAt-in k x
        (xx , (yy , (xxk , (yyk , (qx , below)))))
        where
        ksuc : k ≡ suc m
        ksuc = decide (suc m ≟ k)
          where
          decide : NatOrder.Trichotomy (suc m) k → k ≡ suc m
          decide (NatOrder.lt hlt) = Empty.rec
            (cmax (numS (suc m))
              (subst (λ t → ⟨ fst (numS (suc m)) ∈ t ⟩) (sym qb)
                (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst (suc m)))
                  (#mono (suc m) k hlt)))
              (subst (λ t → ⟨ fst c ∈ t ⟩) (sym (numS-fst (suc m)))
                (subst (λ t → ⟨ t ∈ # (suc m) ⟩) (sym qc)
                  (#mono m (suc m) NatOrder.≤-refl))))
          decide (NatOrder.eq e) = sym e
          decide (NatOrder.gt hgt) = Empty.rec (<-asym hm (pred-≤-pred hgt))

        xxk : ⟨ fst xx ∈ finiteStage k ⟩
        xxk = subst (λ t → ⟨ fst xx ∈ Lset t ⟩) qb xx∈

        yyk : ⟨ fst yy ∈ finiteStage k ⟩
        yyk = subst (λ t → ⟨ fst yy ∈ Lset t ⟩) qb yy∈

        rval : fst r ≡ fst (relAt m)
        rval = vals m hm r
          (subst (λ t → ⟨ pr t (fst r) ∈ fst (lookup f γ) ⟩) qc hf)

        atM : ⟨ precedes (Rel m) (finiteStage m) (fst xx) (fst yy) ⟩
        atM = subst (λ t → ⟨ precedes (λ s u → pr s u ∈ t) (finiteStage m)
                              (fst xx) (fst yy) ⟩) rval
          (subst (λ t → ⟨ precedes (Held r) (Lset t) (fst xx) (fst yy) ⟩) qc
            hprec)

        below : ⟨ before k (fst xx) (fst yy) ⟩
        below = subst (λ j → ⟨ before j (fst xx) (fst yy) ⟩) (sym ksuc)
          (precedes-map (Rel m) (before m) (finiteStage m) (fst xx) (fst yy)
            (λ w t hw ht hbf → relAt-fill m w t hw ht hbf) atM)

    from : (x : V ℓ) → RelOf k x → StepOf b f γ x
    from x (xx , (yy , (xx∈ , (yy∈ , (qx , hbf))))) =
      numS m , (relAt m , (xx , (yy , (c∈ , (cmax , (hf , (xxb , (yyb
        , (qx , hprec)))))))))
      where
      m : ℕ
      m = before-suc k (fst xx) (fst yy) hbf .fst

      qk : k ≡ suc m
      qk = before-suc k (fst xx) (fst yy) hbf .snd

      hm : m < k
      hm = subst (λ j → m < j) (sym qk) NatOrder.≤-refl

      c∈ : ⟨ fst (numS m) ∈ fst (lookup b γ) ⟩
      c∈ = subst (λ t → ⟨ fst (numS m) ∈ t ⟩) (sym qb)
        (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst m)) (#mono m k hm))

      cmax : (d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩
           → ⟨ fst (numS m) ∈ fst d ⟩ → Empty.⊥
      cmax d hd hc = PT.rec Empty.isProp⊥ step
        (∈#-elim k (fst d) (subst (λ t → ⟨ fst d ∈ t ⟩) qb hd))
        where
        step : Σ[ j ∈ ℕ ] ((j < k) × (fst d ≡ # j)) → Empty.⊥
        step (j , (hj , qd)) = <-asym mj (pred-≤-pred (subst (λ i → j < i) qk hj))
          where
          mj : m < j
          mj = #∈#-elim m j
            (subst (λ t → ⟨ t ∈ # j ⟩) (numS-fst m)
              (subst (λ t → ⟨ fst (numS m) ∈ t ⟩) qd hc))

      hf : ⟨ pr (fst (numS m)) (fst (relAt m)) ∈ fst (lookup f γ) ⟩
      hf = subst (λ t → ⟨ pr t (fst (relAt m)) ∈ fst (lookup f γ) ⟩)
        (sym (numS-fst m)) (ents m hm)

      xxb : ⟨ fst xx ∈ Lset (fst (lookup b γ)) ⟩
      xxb = subst (λ t → ⟨ fst xx ∈ Lset t ⟩) (sym qb) xx∈

      yyb : ⟨ fst yy ∈ Lset (fst (lookup b γ)) ⟩
      yyb = subst (λ t → ⟨ fst yy ∈ Lset t ⟩) (sym qb) yy∈

      hprec : ⟨ precedes (Held (relAt m)) (Lset (fst (numS m)))
                 (fst xx) (fst yy) ⟩
      hprec = subst (λ t → ⟨ precedes (Held (relAt m)) (Lset t)
                              (fst xx) (fst yy) ⟩) (sym (numS-fst m))
        (precedes-map (before m) (Rel m) (finiteStage m) (fst xx) (fst yy)
          (λ w t hw ht hR → relAt-rep m w t hw ht hR)
          (subst (λ j → ⟨ before j (fst xx) (fst yy) ⟩) qk hbf))

  step-rel : ⟨ γ ⊨ RelStepAt v b f ⟩ → fst (lookup v γ) ≡ fst (relAt k)
  step-rel h = cong fst (extensionalL {a = lookup v γ} {b = relAt k} pt)
    where
    fwd : (x : S) → ⟨ fst x ∈ fst (lookup v γ) ⟩ → ⟨ fst x ∈ fst (relAt k) ⟩
    fwd x hx = PT.rec (snd (fst x ∈ fst (relAt k))) (into (fst x))
      (RelStep-out v b f γ ob h x hx)

    bwd : (x : S) → ⟨ fst x ∈ fst (relAt k) ⟩ → ⟨ fst x ∈ fst (lookup v γ) ⟩
    bwd x hx = PT.rec (snd (fst x ∈ fst (lookup v γ)))
      (λ ro → RelStep-back v b f γ ob h x (from (fst x) ro))
      (relAt-out k (fst x) hx)

    pt : (x : S) → (fst x ∈ fst (lookup v γ)) ≡ (fst x ∈ fst (relAt k))
    pt x = ⇔toPath (fwd x) (bwd x)

  rel-step : fst (lookup v γ) ≡ fst (relAt k) → ⟨ γ ⊨ RelStepAt v b f ⟩
  rel-step q = RelStep-in v b f γ ob toStep backStep
    where
    toStep : (w : S) → ⟨ fst w ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ (fst w) ∥₁
    toStep w hw = PT.map (from (fst w))
      (relAt-out k (fst w) (subst (λ t → ⟨ fst w ∈ t ⟩) q hw))

    backStep : (w : S) → StepOf b f γ (fst w) → ⟨ fst w ∈ fst (lookup v γ) ⟩
    backStep w st = subst (λ t → ⟨ fst w ∈ t ⟩) (sym q) (into (fst w) st)
```

<!--en-->
## Every value an approximation records

<!--zh-->
## 逼近所记录的每个取值
<!--ja-->
## 近似が記録するすべての値
<!--/-->

<!--en-->
Induction on the numeral proves that every value in an approximation is the
corresponding `relAt`{.Agda}, yielding correctness and uniqueness of recorded
relations.
<!--zh-->
对数码归纳可证逼近中的每个取值都是相应的 `relAt`{.Agda}，从而得到所记录关系的正确性与唯一性。
<!--ja-->
数項についての帰納法により、近似にある各値が対応する `relAt`{.Agda} であることを示し、記録された関係の正しさと一意性を得る。
<!--/-->

<!--en-->

One induction, on the numeral, in the meta-language, with the approximation and
its domain held fixed. The motive says: whatever value the approximation records
at this numeral is the recursion's value there. It quantifies over **all**
recorded values, so single-valuedness is nowhere a hypothesis and the ruling of
the section above is collected here for free.

The induction is well-founded rather than structural, because the step at a
numeral consults the approximation at its predecessor and the argument travels
through the domain rather than through a constructor. Completeness below the
index is where the domain conjunct is spent: a numeral below the index is in the
domain, so the approximation has a value there, and the induction hypothesis
identifies it. `rel-only`{.Agda} is the conclusion the graph was written for:
whatever satisfies it at a numeral is the recursion's value there.
<!--zh-->

一次归纳，在数码上，在元语言中，逼近与它的定义域保持固定。动机说：逼近在这个数码处所记录的任何取值，都是这场递归在那里的取值。它对**一切**被记录的取值作量化，故单值性在任何地方都不是假设，而上一节那条裁定在此处白白收取。

这场归纳是良基的、不是结构的：在某个数码处的那一步查阅的是逼近在其前趋处的取值，因此实参沿定义域下降，而不是沿构造子分解。「索引以下的完备性」这一合取项正是在此被使用的：索引以下的数码落在定义域中，故逼近在那里有取值，而归纳假设把它认同。`rel-only`{.Agda} 就是那张图为之而写的结论：凡在某个数码处满足它者，都是这场递归在那里的取值。
<!--/-->

```agda
entryOf : ∀ {n} (f a : Fin n) (γ : S ^ n) (k : ℕ)
        → fst (lookup a γ) ≡ # k → ⟨ γ ⊨ ApproxAt f a ⟩
        → (j : ℕ) → j < k
        → ((u : S) → ⟨ pr (# j) (fst u) ∈ fst (lookup f γ) ⟩
           → fst u ≡ fst (relAt j))
        → ⟨ pr (# j) (fst (relAt j)) ∈ fst (lookup f γ) ⟩
entryOf f a γ k qa h j hj vs =
  PT.rec (snd (pr (# j) (fst (relAt j)) ∈ fst (lookup f γ))) named
    (ApproxAt-value f a γ h (numS j)
      (subst (λ t → ⟨ fst (numS j) ∈ t ⟩) (sym qa)
        (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst j)) (#mono j k hj))))
  where
  named : Σ[ u ∈ S ] ⟨ pr (fst (numS j)) (fst u) ∈ fst (lookup f γ) ⟩
        → ⟨ pr (# j) (fst (relAt j)) ∈ fst (lookup f γ) ⟩
  named (u , p) =
    subst (λ t → ⟨ pr (# j) t ∈ fst (lookup f γ) ⟩) (vs u p') p'
    where
    p' : ⟨ pr (# j) (fst u) ∈ fst (lookup f γ) ⟩
    p' = subst (λ t → ⟨ pr t (fst u) ∈ fst (lookup f γ) ⟩) (numS-fst j) p

module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) (k : ℕ)
         (qa : fst (lookup a γ) ≡ # k) (h : ⟨ γ ⊨ ApproxAt f a ⟩) where
  private
    Val : ℕ → Type (ℓ-suc ℓ)
    Val m = (m < k) → (w : S) → ⟨ pr (# m) (fst w) ∈ fst (lookup f γ) ⟩
          → fst w ≡ fst (relAt m)

  approx-val : (m : ℕ) → Val m
  approx-val = WFI.induction <-wellfounded go
    where
    go : (m : ℕ) → ((j : ℕ) → j < m → Val j) → Val m
    go m IH hm w hw = step-rel zero (suc zero) (sh2 f) (w ∷ numS m ∷ γ) m
      (numS-fst m) vals ents
      (ApproxAt-step f a γ h (numS m) w
        (subst (λ t → ⟨ pr t (fst w) ∈ fst (lookup f γ) ⟩)
          (sym (numS-fst m)) hw))
      where
      vals : Values (lookup (sh2 f) (w ∷ numS m ∷ γ)) m
      vals j hj u hu = IH j hj (<-trans hj hm) u hu

      ents : Entries (lookup (sh2 f) (w ∷ numS m ∷ γ)) m
      ents j hj = entryOf f a γ k qa h j (<-trans hj hm)
        (λ u p → IH j hj (<-trans hj hm) u p)

  approx-ent : (m : ℕ) → m < k
             → ⟨ pr (# m) (fst (relAt m)) ∈ fst (lookup f γ) ⟩
  approx-ent m hm = entryOf f a γ k qa h m hm (approx-val m hm)

module _ {n : ℕ} (v b : Fin n) (γ : S ^ n) (k : ℕ)
         (qb : fst (lookup b γ) ≡ # k) where
  rel-only : ⟨ γ ⊨ RelGraphAt v b ⟩ → fst (lookup v γ) ≡ fst (relAt k)
  rel-only h = PT.rec (setIsSet (fst (lookup v γ)) (fst (relAt k))) read
    (RelGraph-out v b γ h)
    where
    read : GraphOf v b γ → fst (lookup v γ) ≡ fst (relAt k)
    read (g , (ha , hs)) =
      step-rel (suc v) (suc b) zero (g ∷ γ) k qb
        (λ m hm w hw → approx-val zero (suc b) (g ∷ γ) k qb ha m hm w hw)
        (λ m hm → approx-ent zero (suc b) (g ∷ γ) k qb ha m hm)
        hs
```

<!--en-->
## The approximation, exhibited

<!--zh-->
## 那个逼近的显式构造
<!--ja-->
## 近似を具体的に構成する
<!--/-->

<!--en-->
Finite replacement collects the pairs `(# j , relAt j)`{.Agda} below `k`,
producing `approxSet k`{.Agda} with both the required values and complete domain.
<!--zh-->
用一次有穷替换收集 `k` 以下的各对 `(# j , relAt j)`{.Agda}，得到既有正确取值又有完整定义域的 `approxSet k`{.Agda}。
<!--ja-->
有限な置換が `k` より下の対 `(# j , relAt j)`{.Agda} を集め、必要な値と完全な定義域を備えた `approxSet k`{.Agda} を構成する。
<!--/-->

<!--en-->

The graph says there merely is an approximation; a consumer has to produce one.
At a numeral `k` the approximation wanted is finite, the pairs of a numeral below
`k` with the relation there, so it is spanned by a **finite family** of elements
of `L`, and the basic chapter's `finSetL`{.Agda} makes such a family a set of the
model as soon as its members share one stage. `smallStage`{.Agda} is the bounding
lemma with its ordinal left visible, which is the recursion chapter's own
`smallDom`{.Agda} with one projection more.

No formula is spent here, and that is the saving this chapter's index buys: the
approximation is finite because the index is a numeral, so it needs neither
replacement nor a graph of its own. `approxSet-approx`{.Agda} then checks the two
conjuncts of "is an approximation" against that family, and
`relAt-graph`{.Agda} is the converse of `rel-only`{.Agda}: the recursion's value
at a numeral satisfies the graph there.
<!--zh-->

图只断言逼近存在；下面把它具体构造出来。在数码 `k` 处，所需的逼近是有穷的，即由 `k` 以下的诸数码与相应关系所成的诸对。因此，它由 `L` 元素的一个**有穷族**张成；只要这些成员同处一个阶段，基本公理一章的 `finSetL`{.Agda} 就把这样的族变成模型中的一个集合。`smallStage`{.Agda} 是把序数保留在显式结果中的界层引理，也就是比递归一章的 `smallDom`{.Agda} 多出一个投影。

此处不花任何公式，而这正是本章的索引所买来的那笔节省：逼近之所以有穷，是因为索引是数码，故它既不需要替换，也不需要自己的图。`approxSet-approx`{.Agda} 随后对着那个族核对「是一个逼近」的两个合取项，而 `relAt-graph`{.Agda} 是 `rel-only`{.Agda} 的逆：这场递归在某个数码处的取值满足那里的图。
<!--/-->

```agda
smallStage : (X : Type ℓ) (g : X → S)
           → Σ[ σ ∈ V ℓ ] (IsOrd σ × ((x : X) → ⟨ fst (g x) ∈ Lset σ ⟩))
smallStage X g = bd .fst , (bd .snd .fst , mem)
  where
  bd = boundingOrd X (λ x → stage (fst (g x)) (g x .snd))
         (λ x → stage-ord (fst (g x)) (g x .snd))
  mem : (x : X) → ⟨ fst (g x) ∈ Lset (bd .fst) ⟩
  mem x = Lset-mono {α = bd .fst} {β = stage (fst (g x)) (g x .snd)}
    (bd .snd .snd x) (stage-mem (fst (g x)) (g x .snd))

private
  famOf : (k : ℕ) → Fin k → S
  famOf k i = prS (numS (toℕ i)) (relAt (toℕ i))

  famBnd : (k : ℕ) → Σ[ σ ∈ V ℓ ] (IsOrd σ
         × ((i : Lift {ℓ-zero} {ℓ} (Fin k)) → ⟨ fst (famOf k (lower i)) ∈ Lset σ ⟩))
  famBnd k = smallStage (Lift {ℓ-zero} {ℓ} (Fin k)) (λ i → famOf k (lower i))

  famEq : (k : ℕ) (i : Fin k)
        → fst (famOf k i) ≡ pr (# (toℕ i)) (fst (relAt (toℕ i)))
  famEq k i = prS-fst (numS (toℕ i)) (relAt (toℕ i))
            ∙ cong (λ t → pr t (fst (relAt (toℕ i)))) (numS-fst (toℕ i))

opaque
  approxSet : ℕ → S
  approxSet k = finSet k (λ i → fst (famOf k i))
    , FinOf.finSetL (famBnd k .fst) (famBnd k .snd .fst) k
        (λ i → fst (famOf k i)) (λ i → famBnd k .snd .snd (lift i))

  approxSet-fst : (k : ℕ) → fst (approxSet k) ≡ finSet k (λ i → fst (famOf k i))
  approxSet-fst k = refl

approx-mem-in : (k j : ℕ) → j < k
              → ⟨ pr (# j) (fst (relAt j)) ∈ fst (approxSet k) ⟩
approx-mem-in k j hj =
  subst (λ t → ⟨ t ∈ fst (approxSet k) ⟩)
    (cong (λ i → pr (# i) (fst (relAt i))) (toℕ∘enum j hj))
    (subst (λ t → ⟨ pr (# (toℕ (enum j hj))) (fst (relAt (toℕ (enum j hj)))) ∈ t ⟩)
      (sym (approxSet-fst k))
      (finSet-in k (λ i → fst (famOf k i))
        (pr (# (toℕ (enum j hj))) (fst (relAt (toℕ (enum j hj)))))
        ∣ enum j hj , famEq k (enum j hj) ∣₁))

approx-mem-out : (k : ℕ) (y : V ℓ) → ⟨ y ∈ fst (approxSet k) ⟩
               → ∥ Σ[ j ∈ ℕ ] ((j < k) × (y ≡ pr (# j) (fst (relAt j)))) ∥₁
approx-mem-out k y h = PT.map named
  (finSet-out k (λ i → fst (famOf k i)) y
    (subst (λ t → ⟨ y ∈ t ⟩) (approxSet-fst k) h))
  where
  named : Σ[ i ∈ Fin k ] (fst (famOf k i) ≡ y)
        → Σ[ j ∈ ℕ ] ((j < k) × (y ≡ pr (# j) (fst (relAt j))))
  named (i , q) = toℕ i , (toℕ<n i , (sym q ∙ famEq k i))
approxVals : (k : ℕ) → Values (approxSet k) k
approxVals k m hm u hu = PT.rec (setIsSet (fst u) (fst (relAt m))) named
  (approx-mem-out k (pr (# m) (fst u)) hu)
  where
  named : Σ[ j ∈ ℕ ] ((j < k) × (pr (# m) (fst u) ≡ pr (# j) (fst (relAt j))))
        → fst u ≡ fst (relAt m)
  named (j , (hj , q)) = pr-inj q .snd
    ∙ cong (λ i → fst (relAt i)) (sym (#-inj′ (pr-inj q .fst)))

approxEnts : (k : ℕ) → Entries (approxSet k) k
approxEnts k m hm = approx-mem-in k m hm

module _ (k : ℕ) {n : ℕ} (f a : Fin n) (γ : S ^ n)
         (qf : fst (lookup f γ) ≡ fst (approxSet k))
         (qa : fst (lookup a γ) ≡ # k) where
  private
    onDom : (x : S)
          → (⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
             → ⟨ fst x ∈ fst (lookup a γ) ⟩)
          × (⟨ fst x ∈ fst (lookup a γ) ⟩
             → ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩)
    onDom x = fwd , bwd
      where
      fwd : ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
          → ⟨ fst x ∈ fst (lookup a γ) ⟩
      fwd = PT.rec (snd (fst x ∈ fst (lookup a γ))) atY
        where
        atY : Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst x ∈ fst (lookup a γ) ⟩
        atY (y , p) = PT.rec (snd (fst x ∈ fst (lookup a γ))) named
          (approx-mem-out k (pr (fst x) (fst y))
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) qf p))
          where
          named : Σ[ j ∈ ℕ ]
                    ((j < k) × (pr (fst x) (fst y) ≡ pr (# j) (fst (relAt j))))
                → ⟨ fst x ∈ fst (lookup a γ) ⟩
          named (j , (hj , q)) = subst (λ t → ⟨ fst x ∈ t ⟩) (sym qa)
            (subst (λ t → ⟨ t ∈ # k ⟩) (sym (pr-inj q .fst)) (#mono j k hj))

      bwd : ⟨ fst x ∈ fst (lookup a γ) ⟩
          → ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
      bwd hx = PT.map named
        (∈#-elim k (fst x) (subst (λ t → ⟨ fst x ∈ t ⟩) qa hx))
        where
        named : Σ[ j ∈ ℕ ] ((j < k) × (fst x ≡ # j))
              → Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
        named (j , (hj , q)) = relAt j
          , subst (λ t → ⟨ pr (fst x) (fst (relAt j)) ∈ t ⟩) (sym qf)
              (subst (λ t → ⟨ pr t (fst (relAt j)) ∈ fst (approxSet k) ⟩)
                (sym q) (approx-mem-in k j hj))

    onStep : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
           → ⟨ (y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f) ⟩
    onStep x y p = PT.rec (snd ((y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f)))
      named
      (approx-mem-out k (pr (fst x) (fst y))
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) qf p))
      where
      named : Σ[ j ∈ ℕ ]
                ((j < k) × (pr (fst x) (fst y) ≡ pr (# j) (fst (relAt j))))
            → ⟨ (y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f) ⟩
      named (j , (hj , q)) =
        rel-step zero (suc zero) (sh2 f) (y ∷ x ∷ γ) j (pr-inj q .fst)
          (λ i hi u hu → approxVals k i (<-trans hi hj) u
            (subst (λ t → ⟨ pr (# i) (fst u) ∈ t ⟩) qf hu))
          (λ i hi → subst (λ t → ⟨ pr (# i) (fst (relAt i)) ∈ t ⟩) (sym qf)
            (approxEnts k i (<-trans hi hj)))
          (pr-inj q .snd)

  approxSet-approx : ⟨ γ ⊨ ApproxAt f a ⟩
  approxSet-approx = ApproxAt-in f a γ (domAt-intro f a γ onDom) onStep

relAt-graph : ∀ {n} (v b : Fin n) (γ : S ^ n) (k : ℕ)
            → fst (lookup b γ) ≡ # k → fst (lookup v γ) ≡ fst (relAt k)
            → ⟨ γ ⊨ RelGraphAt v b ⟩
relAt-graph v b γ k qb qv = RelGraph-in v b γ (approxSet k)
  (approxSet-approx k zero (suc b) (approxSet k ∷ γ) refl qb)
  (rel-step (suc v) (suc b) zero (approxSet k ∷ γ) k qb
    (approxVals k) (approxEnts k) qv)
```

<!--en-->
## The family, as an element of `L`

<!--zh-->
## 那一族，作为 `L` 的一个元素
<!--ja-->
## 順序族を `L` の要素にする
<!--/-->

<!--en-->
Replacement over all numerals turns the pair graph into `beforeFam`{.Agda}, a
set whose entry at `# k` is exactly the realized relation `relAt k`{.Agda}.
<!--zh-->
对全部数码施行替换，把成对图化为 `beforeFam`{.Agda}；它在 `# k` 处的条目恰是已实现的关系 `relAt k`{.Agda}。
<!--ja-->
すべての数項に置換公理を適用して対グラフを `beforeFam`{.Agda} にし、その `# k` における値が実現された関係 `relAt k`{.Agda} とちょうど一致することを示す。
<!--/-->

<!--en-->

Replacement along `ωʟ`{.Agda}, with the pair graph as the defining formula, and
that is the whole construction. Functionality at a member of `ωʟ`{.Agda} is
`mereFunct`{.Agda} at the numeral it merely is: the value is exhibited by
`relAt-graph`{.Agda} and nothing else satisfies the graph by `rel-only`{.Agda}.

The frame takes the pair graph as a **variable carrying its own equation**, with
`refl`{.Agda} at the one call site, and it hands back a triple in which **no
formula appears at all**: the family, its two membership directions against the
recursion. That last point is crucial. With the family's
specification stated against the closed sentence, every consumer below has to
decide a satisfaction of that sentence against a satisfaction of its expansion,
and the chapter does not close. Stated against the recursion, there is nothing to
decide.
<!--zh-->

沿 `ωʟ`{.Agda} 作替换、以成对的那个图为定义公式，整个构造仅此而已。在 `ωʟ`{.Agda} 的某个成员处的函数性，就是 `mereFunct`{.Agda} 施于它所是的那个数码：其取值由 `relAt-graph`{.Agda} 给出，而由 `rel-only`{.Agda} 保证，没有别的东西满足那个图。

那个框架把成对的图取作**携带自己等式的变元**，在唯一的调用处填 `refl`{.Agda}；而它交回来的是一个三元组，其中**根本不出现任何公式**：那一族，以及它对着这场递归的两个隶属方向。最后这一点至关重要。若把那一族的规格陈述为对着那个闭句子，那么其下的每个消费方都得去判定「那个句子的满足关系」与「它展开式的满足关系」相等，本章便无法完成。陈述为对着这场递归，就没有什么可判定的了。
<!--/-->

```agda
private
```

Perf: the pair graph enters as a variable carrying its own equation, and
nothing the frame hands back mentions a formula at all; with the closed
sentence spelled out in the family's specification the chapter does not close
(past 400 s).

```agda
  famBuild : (φ : Formula S 2) → φ ≡ PairRelGraphAt zero (suc zero)
           → Σ[ h ∈ S ]
               ( ((k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst h ⟩)
               × ((cS rS : S) (k : ℕ) → fst cS ≡ # k
                  → ⟨ pr (fst cS) (fst rS) ∈ fst h ⟩ → fst rS ≡ fst (relAt k)) )
  famBuild φ qφ = r .fst .fst , (inFam , outFam)
    where
    fc : (c : S) → ⟨ c ∈ˢ ωʟ ⟩
       → isContr (Σ[ y ∈ S ] ⟨ (y ∷ c ∷ []) ⊨ φ ⟩)
    fc c c∈ = mereFunct φ c (PT.map atK c∈)
      where
      atK : Σ[ j ∈ Lift ℕ ] (# (lower j) ≡ fst c)
          → Σ[ y ∈ S ] ( ⟨ (y ∷ c ∷ []) ⊨ φ ⟩
                       × ((y' : S) → ⟨ (y' ∷ c ∷ []) ⊨ φ ⟩ → y' ≡ y) )
      atK (j , qj) = prS c (relAt (lower j)) , (holds , only)
        where
        qc : fst c ≡ # (lower j)
        qc = sym qj

        holds : ⟨ (prS c (relAt (lower j)) ∷ c ∷ []) ⊨ φ ⟩
        holds = PairRelGraph-in zero (suc zero)
          (prS c (relAt (lower j)) ∷ c ∷ []) φ qφ (relAt (lower j))
          (prS-fst c (relAt (lower j)))
          (relAt-graph zero (sh2 zero)
            (relAt (lower j) ∷ prS c (relAt (lower j)) ∷ c ∷ [])
            (lower j) qc refl)

        only : (y' : S) → ⟨ (y' ∷ c ∷ []) ⊨ φ ⟩ → y' ≡ prS c (relAt (lower j))
        only y' h = PT.rec (isSetS y' (prS c (relAt (lower j)))) read
          (PairRelGraph-out zero (suc zero) (y' ∷ c ∷ []) φ qφ h)
          where
          read : PairOf zero (suc zero) (y' ∷ c ∷ []) φ qφ
               → y' ≡ prS c (relAt (lower j))
          read (z , (q , hg)) = Σ≡Prop (λ t → snd (isL t))
            ( q
            ∙ cong (pr (fst c))
                (rel-only zero (sh2 zero) (z ∷ y' ∷ c ∷ []) (lower j) qc hg)
            ∙ sym (prS-fst c (relAt (lower j))) )

    r : isContr (SetOf (λ y → ⋁ S (λ c → (c ∈ˢ ωʟ) ⊓ ((y ∷ c ∷ []) ⊨ φ))))
    r = hasReplacementL ωʟ φ fc

    inFam : (k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst (r .fst .fst) ⟩
    inFam k = subst (λ t → ⟨ t ∈ fst (r .fst .fst) ⟩) qe
      (subst ⟨_⟩ (sym (r .fst .snd (prS (numS k) (relAt k))))
        ∣ numS k , (inω , holds) ∣₁)
      where
      qe : fst (prS (numS k) (relAt k)) ≡ pr (# k) (fst (relAt k))
      qe = prS-fst (numS k) (relAt k)
         ∙ cong (λ t → pr t (fst (relAt k))) (numS-fst k)

      inω : ⟨ numS k ∈ˢ ωʟ ⟩
      inω = subst (λ t → ⟨ t ∈ ω ⟩) (sym (numS-fst k)) (#∈ω k)

      holds : ⟨ (prS (numS k) (relAt k) ∷ numS k ∷ []) ⊨ φ ⟩
      holds = PairRelGraph-in zero (suc zero)
        (prS (numS k) (relAt k) ∷ numS k ∷ []) φ qφ (relAt k)
        (prS-fst (numS k) (relAt k))
        (relAt-graph zero (sh2 zero)
          (relAt k ∷ prS (numS k) (relAt k) ∷ numS k ∷ []) k (numS-fst k) refl)

    outFam : (cS rS : S) (k : ℕ) → fst cS ≡ # k
           → ⟨ pr (fst cS) (fst rS) ∈ fst (r .fst .fst) ⟩
           → fst rS ≡ fst (relAt k)
    outFam cS rS k qc h =
      PT.rec (setIsSet (fst rS) (fst (relAt k))) atD
        (subst ⟨_⟩ (r .fst .snd (prS cS rS))
          (subst (λ t → ⟨ t ∈ fst (r .fst .fst) ⟩) (sym (prS-fst cS rS)) h))
      where
      atD : Σ[ d ∈ S ] ( ⟨ d ∈ˢ ωʟ ⟩ × ⟨ (prS cS rS ∷ d ∷ []) ⊨ φ ⟩ )
          → fst rS ≡ fst (relAt k)
      atD (d , (d∈ , hp)) = PT.rec (setIsSet (fst rS) (fst (relAt k))) read
        (PairRelGraph-out zero (suc zero) (prS cS rS ∷ d ∷ []) φ qφ hp)
        where
        read : PairOf zero (suc zero) (prS cS rS ∷ d ∷ []) φ qφ
             → fst rS ≡ fst (relAt k)
        read (z , (q , hg)) = pr-inj q' .snd
          ∙ rel-only zero (sh2 zero) (z ∷ prS cS rS ∷ d ∷ []) k qd hg
          where
          q' : pr (fst cS) (fst rS) ≡ pr (fst d) (fst z)
          q' = sym (prS-fst cS rS) ∙ q
          qd : fst d ≡ # k
          qd = sym (pr-inj q' .fst) ∙ qc

opaque
  beforeFam : S
  beforeFam = famBuild (PairRelGraphAt zero (suc zero)) refl .fst

  beforeFam-in : (k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst beforeFam ⟩
  beforeFam-in = famBuild (PairRelGraphAt zero (suc zero)) refl .snd .fst

  beforeFam-out : (cS rS : S) (k : ℕ) → fst cS ≡ # k
                → ⟨ pr (fst cS) (fst rS) ∈ fst beforeFam ⟩
                → fst rS ≡ fst (relAt k)
  beforeFam-out = famBuild (PairRelGraphAt zero (suc zero)) refl .snd .snd
```

<!--en-->
## The order at a numeral held in a slot

<!--zh-->
## 某个槽位所持数码处的那个序
<!--ja-->
## スロット内の数項における順序
<!--/-->

<!--en-->
`BeforeAt`{.Agda} applies the internal family to a numeral held in a variable
slot, and its two readings recover precisely the finite-stage `before`{.Agda}
comparison.
<!--zh-->
`BeforeAt`{.Agda} 把内部族施于变元位所持的数码，其两条读式恰好恢复有穷阶段的 `before`{.Agda} 比较。
<!--ja-->
`BeforeAt`{.Agda} は内部の族を変数スロットにある数項へ適用し、その二つの読みから有限段階の `before`{.Agda} 比較を正確に復元する。
<!--/-->

<!--en-->

This is the formula the previous chapter asked for, and it is **one binder**
wide. The family is a set and can be named, so `appC`{.Agda} reads it at the
numeral the slot holds: application at a constant, one bounded existential and
one pair reader, with the adequacy the model chapter proves for the slot version
proved there for the constant version too. What the relation so read holds is
then a single membership of a pair, which is `appAt`{.Agda} at that same slot.

The two compared sets are **confined to the stage at that numeral**, and this
confinement is what shortens the argument. Without it the step has to be re-expanded
here, through the maximal predecessor of the numeral, the stage graph and the
precedence formula; with it, the comparison at a stage against the relation
recorded there is exactly what `relAt-rep`{.Agda} and `relAt-fill`{.Agda} already
prove, so each reading is one composition of those with the family's own
direction. `BeforeAt-out`{.Agda} and `BeforeAt-in`{.Agda} both stand at variable
slots in a variable environment with the numeral appearing as a **variable
carrying its defining equation**, which is the law the level was measured under
one chapter ago.
<!--zh-->

这就是上一章所索取的那条公式，而且它只有**一层绑定**。那一族如今是一个集合，可以被命名，故 `appC`{.Agda} 在该槽位所持的数码处把它读出：这是在常元处的应用，由一个有界存在量词加一次对读式组成；而模型那一章为槽位版所证的充分性，在那里也已为常元版证过。如此读出的关系所持有的东西，随后只是一个对的单次隶属，即同一位上的 `appAt`{.Agda}。

被比较的那两个集合**被禁闭在该数码处的阶段之内**，而正是这一点使后续论证得以缩短。没有它，那一步就得在此处重新展开一遍：经由该数码的极大前趋、阶段之图与那条先序公式；有了它，「在一个阶段上、对着那里所记录的关系」的那次比较，恰是 `relAt-rep`{.Agda} 与 `relAt-fill`{.Agda} 已经证过的东西，故每条读式都只是它们与那一族自己那个方向的一次复合。`BeforeAt-out`{.Agda} 与 `BeforeAt-in`{.Agda} 都作用于变元环境的变元位，而那个数码以**携带自己定义等式的变元**的身份出现；这正是前一章层号所据以实测的那条定律。
<!--/-->

```agda
opaque
  BeforeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  BeforeAt b x y =
    ∃̇ ( appC beforeFam (suc b) zero ∧̇ appAt zero (suc x) (suc y) )

module _ {n : ℕ} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
         (qb : fst (lookup b γ) ≡ # m)
         (hx : ⟨ fst (lookup x γ) ∈ finiteStage m ⟩)
         (hy : ⟨ fst (lookup y γ) ∈ finiteStage m ⟩) where
  private
    Goal : Type (ℓ-suc ℓ)
    Goal = ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩

    AtR : Type (ℓ-suc ℓ)
    AtR = Σ[ r ∈ S ]
      ( ⟨ (r ∷ γ) ⊨ appC beforeFam (suc b) zero ⟩
      × ⟨ (r ∷ γ) ⊨ appAt zero (suc x) (suc y) ⟩ )

    atR : AtR → Goal
    atR (r , (happ , hmem)) =
      relAt-rep m (fst (lookup x γ)) (fst (lookup y γ)) hx hy
        (subst (λ t → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ t ⟩) qr
          (subst ⟨_⟩ (appAt-adequate zero (suc x) (suc y) (r ∷ γ)) hmem))
      where
      hf : ⟨ pr (fst (lookup b γ)) (fst r) ∈ fst beforeFam ⟩
      hf = subst ⟨_⟩ (appC-adequate beforeFam (suc b) zero (r ∷ γ)) happ

      qr : fst r ≡ fst (relAt m)
      qr = beforeFam-out (lookup b γ) r m qb hf

  opaque
    unfolding BeforeAt

    BeforeAt-out : ⟨ γ ⊨ BeforeAt b x y ⟩
                 → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
    BeforeAt-out h =
      PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ)))) atR h

    BeforeAt-in : ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
                → ⟨ γ ⊨ BeforeAt b x y ⟩
    BeforeAt-in h = ∣ relAt m , (happ , hmem) ∣₁
      where
      happ : ⟨ (relAt m ∷ γ) ⊨ appC beforeFam (suc b) zero ⟩
      happ = subst ⟨_⟩
        (sym (appC-adequate beforeFam (suc b) zero (relAt m ∷ γ)))
        (subst (λ t → ⟨ pr t (fst (relAt m)) ∈ fst beforeFam ⟩) (sym qb)
          (beforeFam-in m))

      hmem : ⟨ (relAt m ∷ γ) ⊨ appAt zero (suc x) (suc y) ⟩
      hmem = subst ⟨_⟩
        (sym (appAt-adequate zero (suc x) (suc y) (relAt m ∷ γ)))
        (relAt-fill m (fst (lookup x γ)) (fst (lookup y γ)) hx hy h)
```

<!--en-->
## The frame, discharged

<!--zh-->
## 那个框架，兑现
<!--ja-->
## フレームの仮定を解消する
<!--/-->

<!--en-->
The realized family instantiates both directions required by the limit-order
frame, making the internal earliest-disagreement description unconditional.
<!--zh-->
已实现的族为极限序框架所要求的两个方向给出实例，使内部的最先分歧描述不再带条件。
<!--ja-->
`BeforeAt`{.Agda} とその二つの読みが前章の `Described`{.Agda} フレームを具体化します。そのインスタンスから再公開するのは、次章が実際に使う `codeOrder`{.Agda}、`codeOrder-fill`{.Agda}、`codeOrder-rep`{.Agda} だけです。
<!--/-->

<!--en-->

This is what the whole chapter was for. Supplying `BeforeAt`{.Agda} and its two
readings instantiates the previous chapter's `Described`{.Agda} frame. From that instance, this chapter re-exports only the resulting relation
`codeOrder`{.Agda} and its two membership directions, `codeOrder-fill`{.Agda}
and `codeOrder-rep`{.Agda}, which
are the interface used by the internal well-order construction.

What that closes and what it does not is worth saying precisely. The
internalization chapter's key bundle takes two relation slots, one for the codes
and one for the parameters. The code slot is now filled outright, so the step
adequacy of `L.Choice.NameComparisonAdequacy`{.Agda} needs only the parameter slot, that is the
order on the carrier being named, with its two membership directions. That order
is what `L.Choice.OrderTable`{.Agda} produces at each stage, inside the recursion that
`L.Choice.StageOrderAdequacy`{.Agda}'s `Stp`{.Agda} parameter is itself feeding. So
`Faithful`{.Agda}'s parameter is **not** discharged by this chapter, and the
reason is structural rather than missing mathematics: the step condition at a
stage wants the internalized order at that stage, which the table only has inside
its own induction. Closing it is a re-cut of where the step adequacy is supplied,
not another construction, and it is the one thing left on this chain.
<!--zh-->

这正是整章的目标。`BeforeAt`{.Agda} 及其两条读式为上一章的 `Described`{.Agda} 框架提供了实例。本章只从该实例导出所得关系 `codeOrder`{.Agda}，以及它的两个隶属方向 `codeOrder-fill`{.Agda} 与 `codeOrder-rep`{.Agda}；后续的内部整序构造实际只使用这三个名字。

需要明确本章已经提供和仍未提供的内容。内化章的键之束包含两个关系位，分别对应码与参数；本章已经提供码关系位。因此，`L.Choice.NameComparisonAdequacy`{.Agda} 的步进充分性还需要参数关系位，即命名所依托载体上的序及其两个隶属方向。这个序由 `L.Choice.OrderTable`{.Agda} 在每个阶段产生，但只存在于该表自身的递归内部；`L.Choice.StageOrderAdequacy`{.Agda} 的 `Stp`{.Agda} 参数正为该递归提供输入。因此，本章没有给出 `Faithful`{.Agda} 的这一参数。这是接口安排造成的缺项，不是数学上的缺口；剩余工作是重新安排步进充分性的提供位置。
<!--/-->

```agda
private
  module CodeOrder = Described BeforeAt BeforeAt-in BeforeAt-out

open CodeOrder public using ( codeOrder; codeOrder-fill; codeOrder-rep )
```

<!--en-->
## Recap

<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The finite relations and their numeral-indexed family are sets in `L`;
`BeforeAt`{.Agda} reads the family as the original earliest-disagreement
comparison, and the `Described`{.Agda} instance contributes exactly `codeOrder`{.Agda} with
its fill and representation lemmas to the public interface.
<!--zh-->
有穷阶段关系及其数码索引族都是 `L` 中的集合；`BeforeAt`{.Agda} 把该族读回原来的最先分歧比较，而 `Described`{.Agda} 实例恰好向公开接口提供 `codeOrder`{.Agda} 及其填入与表示引理。
<!--ja-->
有限段階の関係とその数項添字族は `L` 内の集合です。`BeforeAt`{.Agda} はこの族を元の最初の相違による比較として読み戻し、`Described`{.Agda} のインスタンスからは `codeOrder`{.Agda} とその二つの読みだけを再公開します。
<!--/-->

<!--en-->

`relAt`{.Agda} is the earliest-disagreement relation at each numeral, as an
element of `L`: a separation over the pairs of that finite stage, carved with the
previous chapter's step description, whose two slots are bound and **pinned to
constants by the object equality** so that one description serves both this
separation and the graph below. `relAt-out`{.Agda} and `relAt-in`{.Agda} are its
two readings, proved together by induction on the numeral, each spending the other
at the predecessor because the previous relation is consulted only inside the
agreement clause; `precedes-map`{.Agda} is the single line that carries a
comparison between two spellings of the base relation, and it is contravariant.

`RelBodyAt`{.Agda} is the step, generic in the member, the index and the
approximation. The predecessor is said with **no object equality**: it is the
`∈`-maximal member of the index, two atoms, and at zero there is none, which
makes the step empty exactly where the recursion is. `RelStepAt`{.Agda},
`ApproxAt`{.Agda} and `RelGraphAt`{.Agda} follow the template with no
single-valuedness conjunct, and `step-rel`{.Agda} and `rel-step`{.Agda} are the
bridge to the meta-language, applied four times between them.

`approx-val`{.Agda} pins every value an approximation records, by one
well-founded induction on the numeral with no single-valuedness hypothesis
anywhere, and `rel-only`{.Agda} is the graph's determinacy. `approxSet`{.Agda} is
the approximation exhibited, and it costs **no formula at all**: the approximation
below a numeral is finite, so `finSetL`{.Agda} spans it once `smallStage`{.Agda}
puts its members in one stage. `beforeFam`{.Agda} is the family itself, one
replacement along `ωʟ`{.Agda}, sealed where it is built, with its two directions
stated against the recursion and not against any formula.

`BeforeAt`{.Agda} is what the previous chapter asked for: the family read at the
numeral held in a slot, with `appC`{.Agda} for application at a constant and
`appAt`{.Agda} for the pair the relation there holds, and the two compared sets
arriving **confined to the stage at that numeral**, which is what lets each
reading be one composition of `relAt-rep`{.Agda} or `relAt-fill`{.Agda} with the
family's own direction. With its two readings, the `Described`{.Agda} frame is instantiated; only
`codeOrder`{.Agda}, `codeOrder-fill`{.Agda} and `codeOrder-rep`{.Agda} are
re-exported for the next chapter.

One measurement, and it is the largest this part has recorded. The four
descriptions of the recursion must be **sealed where they are built**: unsealed,
each satisfaction at a concrete environment normalizes a formula carrying two
copies of the whole hierarchy description, and the chapter costs 376 s; sealed,
3.8 s, a factor of ninety-nine, with the mathematics untouched. The frame that
builds the family obeys the same law one level up, by handing back a triple in
which no formula appears at all.
<!--zh-->

`relAt`{.Agda} 是每个数码处最先分歧之序的那个关系，作为 `L` 的一个元素：在那个有穷阶段的诸对之上作一次分离，依上一章那条步进描述写出，而那条描述的两个槽位被绑定、并**用对象等词固定在诸常元上**，于是一条描述同时服务于此处的分离与其下的那个图。`relAt-out`{.Agda} 与 `relAt-in`{.Agda} 是它的两条读式，对数码作归纳一并证出，每个方向都要在前趋处用到另一个，因为上一个关系只在一致性子句内部被查阅；`precedes-map`{.Agda} 则在基底关系的两种写法之间传递一次比较，且是反变的。

`RelBodyAt`{.Agda} 是那一步，对成员、索引与逼近保持通用。前趋的说法**不用对象等词**：它是索引的 `∈`-极大成员，两个原子；而在零处没有这样的成员，这使那一步恰好在这场递归为空之处为空。`RelStepAt`{.Agda}、`ApproxAt`{.Agda} 与 `RelGraphAt`{.Agda} 按同一模板给出，不带单值性合取项；`step-rel`{.Agda} 与 `rel-step`{.Agda} 是通向元语言的两个引理，合计用了四次。

`approx-val`{.Agda} 把逼近所记录的每个取值固定下来，靠的是在数码上的一次良基归纳，任何地方都没有单值性假设；`rel-only`{.Agda} 则是那个图的确定性。`approxSet`{.Agda} 是直接给出的那个逼近，而它**根本不使用任何公式**：某个数码以下的逼近是有穷的，故只要 `smallStage`{.Agda} 把它的诸成员放进同一个阶段，`finSetL`{.Agda} 就把它构造为集合。`beforeFam`{.Agda} 是那一族本身，沿 `ωʟ`{.Agda} 作一次替换而得到，并在造出之处封印；它的两个方向都对着这场递归、而非对着任何公式来陈述。

`BeforeAt`{.Agda} 就是上一章所要求的东西：那一族在某个槽位所持数码处被读出，其中在常元处的应用用 `appC`{.Agda}，那里的关系所持有的那个对用 `appAt`{.Agda}；而被比较的那两个集合**被限制在该数码处的阶段之内**，正是这一点使每条读式都只是 `relAt-rep`{.Agda} 或 `relAt-fill`{.Agda} 与那一族自己那个方向的一次复合。有了它的两条读式，`Described`{.Agda} 框架便得到实例；该实例向下一章再导出的公开接口只有 `codeOrder`{.Agda}、`codeOrder-fill`{.Agda} 与 `codeOrder-rep`{.Agda}。

这是一次实测，也是本部记录下差距最大的一次。这场递归的四条描述必须**在造出之处封印**：不封印时，每一次在具体环境上的满足关系都要把一条内部装着两份完整层级描述的公式正规化，本章要花 376 秒；封印之后是 3.8 秒，九十九倍，而数学内容分毫未变。造出那一族的那个框架在高一层遵守同一条定律：它交回来的三元组中根本不出现任何公式。
<!--/-->
