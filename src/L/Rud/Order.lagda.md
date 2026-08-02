# The canonical well-order

<!--en-->
Every level of the S-tower can be well-ordered, and the order is not invented
level by level: it is one comparison, read at every level at once. The recipe is
the classical one (Schindler-Zeman, p. 11). A set that appears earlier precedes
a set that appears later; two sets that appear at the same stage are compared by
the *producer* that first makes them, and producers are compared
lexicographically, by the stage, then by the operation index, then by the two
arguments in the order already built below.

The three-armed membership surface of the concrete step gives the producers
their shape. A member of `step u` is a member of `u`, or `u` itself, or a value
`F_i(a, b)` of one of the sixteen basis rudimentary functions, with both
arguments in `u ∪ {u}`. The first arm is not a producer at all: such a set was
already there, and its own producer lives at an earlier stage. The other two
are, and only the image arm carries a triple. So a producer
is a stage together with either the self mark or an operation index and two
argument producers, and that is a plain tree. The chapter builds the order on
those trees once, and then the order of a level is the pull-back of the tree
order along "take the least producer of this set".

Reading the order off a fixed tree rather than rebuilding it at each stage buys
the coherence lemma outright. The classical texts need it and lean on it in
silence: the order of a later level, restricted to an earlier one, must be the
earlier order, or the union taken at a limit is not a relation at all. Here the
key of a set does not mention the level it is read at, so the lemma is a
one-line consequence rather than an induction.

The excluded middle is spent in exactly two places, and both are searches, not
comparisons: choosing the least producer of a set, and choosing the least
element of a non-empty part of a level. Everything else, the tree, its order,
its trichotomy and transitivity and well-foundedness, and the decoding of a
producer back into the level, is constructive.

The endgame is the point of the chapter. Every level carries a well-order, so
every level is well-orderable; at a limit index that is the same statement about
`J`. From a well-order of a level a choice function on any set of the level
follows by taking least elements, and no satisfaction, no formula, and no
internality is asked for anywhere on the path.
<!--zh-->
S-塔的每一层都可良序化，且这个序不是逐层发明出来的：它是同一个比较，在所有层上一并读取。配方是经典的 (Schindler-Zeman，p. 11)。较早出现的集合先于较晚出现的集合；同阶段出现的两个集合，按最先造出它们的**生成者**比较，而生成者按字典序比较：先比阶段，再比运算索引，最后按下方已建好的序比两个参数。

具体 step 的三臂隶属表面给了生成者以形状。`step u` 的成员或是 `u` 的成员、或是 `u` 自身、或是十六个基底初步函数之一的值 `F_i(a, b)`，其两个参数都在 `u ∪ {u}` 中。第一臂根本不是生成者：那样的集合早已在场，它自己的生成者住在更早的阶段。另两臂才是，且只有像臂携带三元组。于是生成者就是一个阶段，连同自身标记、或一个运算索引加两个参数生成者，这是一棵朴素的树。本章一次性在这些树上建起序，而某一层的序则是树序沿「取此集合的最小生成者」的拉回。

从固定的树上读出序、而非在每个阶段重建它，白白换来了相容引理。经典文献需要它却默不作声地倚仗它：较后层的序限制到较早层上，必须就是那个较早的序，否则极限处所取的并压根不是一个关系。此处一个集合的键不提及它被读取的那一层，故该引理是一行推论，而非一场归纳。

排中律恰好花在两处，且两处都是搜索、不是比较：选取一个集合的最小生成者，以及选取某层的非空部分的极小元。其余一切，即树、树上的序、它的三歧与传递性与良基性，以及把生成者解码回层内，都是构造性的。

终局才是本章的要点。每一层都带一个良序，故每一层可良序化；在极限索引处这就是关于 `J` 的同一句话。由某层的一个良序，取极小元即得该层任一集合上的选择函数，而这条路上处处不问满足、不问公式、不问内部性。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.Order {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri ) renaming ( Tri to OrdTri )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.Step {ℓ} lem A
  using ( Op16; op0; op1; op2; op3; op4; op5; op6; op7
        ; op8; op9; op10; op11; op12; op13; op14; op15
        ; Fof; StepArm; arm-member; arm-self; arm-image
        ; step; step-out; step-in-img; u'; u'-in; u-self-in
        ; Sset; Sset-in; Sset-out; Sset-mono; Sset-mem; Sset-trans; Jset )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; IsLeast; leastOf; natSWO; pullSWO )

open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sum.Properties using ( isProp⊎ )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Two ground orders

The producer tree is indexed by two small pieces of data, and each needs an
order before the tree can have one. The stages are ordinals, ordered by
membership, and an ordinal is carried with its own proof of ordinality, which is
a proposition; so the pair type is a set, and its paths are the paths of the
underlying sets.
<!--zh-->
## 两个地面序

生成者树以两小块数据为索引，二者都要先有序，树才谈得上有序。阶段是序数，按隶属排序，而序数随身携带自己的序数性证明，那是一个命题；故这个对类型是集合，其道路即底层集合的道路。
<!--/-->

```agda
Ord : Type (ℓ-suc ℓ)
Ord = Σ[ δ ∈ S ] IsOrd δ

isSetOrd : isSet Ord
isSetOrd = isSetΣSndProp isSetS isPropIsOrd

ordPath : (δ γ : Ord) → δ .fst ≡ γ .fst → δ ≡ γ
ordPath δ γ = Σ≡Prop isPropIsOrd

ordTrans : (δ γ ε : Ord) → ⟨ δ .fst ∈ˢ γ .fst ⟩ → ⟨ γ .fst ∈ˢ ε .fst ⟩
         → ⟨ δ .fst ∈ˢ ε .fst ⟩
ordTrans δ γ ε h h' = ε .snd .fst {x = γ .fst} {y = δ .fst} h h'
```

<!--en-->
Trichotomy for ordinals is the comparison chapter's classical theorem, repackaged
as the bundle's three-way data, and accessibility is the hierarchy's own
regularity read at the pair type. That gives the first ground order.
<!--zh-->
序数的三歧是比较一章的经典定理，改装成束所要的三路数据，而可及性就是层级自身的正则性在对类型上的读法。这就给出第一个地面序。
<!--/-->

```agda
ordTri : (δ γ : Ord) → Tri ⟨ δ .fst ∈ˢ γ .fst ⟩ (δ ≡ γ) ⟨ γ .fst ∈ˢ δ .fst ⟩
ordTri δ γ = go (ord-tri (δ .fst) (δ .snd) (γ .fst) (γ .snd))
  where
  go : OrdTri (δ .fst) (γ .fst)
     → Tri ⟨ δ .fst ∈ˢ γ .fst ⟩ (δ ≡ γ) ⟨ γ .fst ∈ˢ δ .fst ⟩
  go (inl h) = lt h
  go (inr (inl e)) = eq (ordPath δ γ e)
  go (inr (inr h)) = gt h

ordAcc : (d : S) (o : IsOrd d) → Acc (λ δ γ → ⟨ δ .fst ∈ˢ γ .fst ⟩) (d , o)
ordAcc = ∈-induction go
  where
  go : (d : S) → ((e : S) → e ∈ᵗ d → (o : IsOrd e)
                → Acc (λ δ γ → ⟨ δ .fst ∈ˢ γ .fst ⟩) (e , o))
     → (o : IsOrd d) → Acc (λ δ γ → ⟨ δ .fst ∈ˢ γ .fst ⟩) (d , o)
  go d ih o = acc (λ γ h → ih (γ .fst) h (γ .snd))

ordSWO : SWO Ord
ordSWO = record
  { _<∙_   = λ δ γ → ⟨ δ .fst ∈ˢ γ .fst ⟩
  ; tri∙   = ordTri
  ; irr∙   = λ δ h → ∈-irrefl (δ .fst) h
  ; trans∙ = ordTrans
  ; wf∙    = λ δ → ordAcc (δ .fst) (δ .snd) }

private
  module Stage = SWO ordSWO
```

<!--en-->
The second ground order is the operation index. Sixteen constructors are
numbered, the numbering has a left inverse, and the numbers are already ordered;
so the order is the pull-back of the order on the numbers along the numbering.
<!--zh-->
第二个地面序是运算索引。十六个构造子被编号，编号有左逆，而数已经有序；于是这个序就是数上的序沿编号的拉回。
<!--/-->

```agda
opIx : Op16 → ℕ
opIx op0 = 0
opIx op1 = 1
opIx op2 = 2
opIx op3 = 3
opIx op4 = 4
opIx op5 = 5
opIx op6 = 6
opIx op7 = 7
opIx op8 = 8
opIx op9 = 9
opIx op10 = 10
opIx op11 = 11
opIx op12 = 12
opIx op13 = 13
opIx op14 = 14
opIx op15 = 15

opAt : ℕ → Op16
opAt 0 = op0
opAt 1 = op1
opAt 2 = op2
opAt 3 = op3
opAt 4 = op4
opAt 5 = op5
opAt 6 = op6
opAt 7 = op7
opAt 8 = op8
opAt 9 = op9
opAt 10 = op10
opAt 11 = op11
opAt 12 = op12
opAt 13 = op13
opAt 14 = op14
opAt _ = op15

opAt-opIx : (i : Op16) → opAt (opIx i) ≡ i
opAt-opIx op0 = refl
opAt-opIx op1 = refl
opAt-opIx op2 = refl
opAt-opIx op3 = refl
opAt-opIx op4 = refl
opAt-opIx op5 = refl
opAt-opIx op6 = refl
opAt-opIx op7 = refl
opAt-opIx op8 = refl
opAt-opIx op9 = refl
opAt-opIx op10 = refl
opAt-opIx op11 = refl
opAt-opIx op12 = refl
opAt-opIx op13 = refl
opAt-opIx op14 = refl
opAt-opIx op15 = refl

opIx-inj : (i j : Op16) → opIx i ≡ opIx j → i ≡ j
opIx-inj i j p = sym (opAt-opIx i) ∙ cong opAt p ∙ opAt-opIx j

opSWO : SWO Op16
opSWO = pullSWO natSWO opIx opIx-inj

private
  module Op = SWO opSWO
```

<!--en-->
## Producers

A producer is a stage together with one of the two productive arms: the self
mark, which produces the level itself, or an operation index with two argument
producers, which produces the value of that operation. The membership arm of the
step surface leaves no trace here, because a set that is merely carried up from
an earlier level is produced at that earlier level, by its own producer.
<!--zh-->
## 生成者

一个生成者是一个阶段，连同两个产出臂之一：自身标记，产出该层自身；或者一个运算索引加两个参数生成者，产出该运算的值。step 表面的成员臂在此不留痕迹，因为仅仅从更早的层被带上来的集合，是在那个更早的层由它自己的生成者产出的。
<!--/-->

```agda
data Producer : Type (ℓ-suc ℓ) where
  prod-self  : Ord → Producer
  prod-image : Ord → Op16 → Producer → Producer → Producer

prod-stage : Producer → Ord
prod-stage (prod-self δ) = δ
prod-stage (prod-image δ _ _ _) = δ

prod-value : Producer → S
prod-value (prod-self δ) = Sset (δ .fst)
prod-value (prod-image δ i p q) = Fof i (prod-value p) (prod-value q)
```

<!--en-->
Not every tree describes a production. The arguments of an image at stage `δ`
come from `S_δ ∪ {S_δ}`, so each of them is either produced strictly before `δ`
or is the self producer of `δ` itself. A tree whose every image node satisfies
that bound is *grounded*, and grounding is a proposition, since the two
alternatives exclude each other: a stage cannot be both a member of `δ` and
`δ`.
<!--zh-->
并非每棵树都描述一次产出。阶段 `δ` 处一个像的参数来自 `S_δ ∪ {S_δ}`，故它们各自或是严格早于 `δ` 被产出、或就是 `δ` 自身的自身生成者。每个像节点都满足这条界的树称为**扎根的**，而扎根性是一个命题，因为两个可能互斥：一个阶段不能既是 `δ` 的成员又是 `δ`。
<!--/-->

```agda
SelfAt : Ord → Producer → Type (ℓ-suc ℓ)
SelfAt δ (prod-self γ) = γ ≡ δ
SelfAt δ (prod-image _ _ _ _) = ⊥* {ℓ-suc ℓ}

Earlier : Ord → Producer → Type (ℓ-suc ℓ)
Earlier δ p = ⟨ prod-stage p .fst ∈ˢ δ .fst ⟩ ⊎ SelfAt δ p

Grounded : Producer → Type (ℓ-suc ℓ)
Grounded (prod-self _) = Unit* {ℓ-suc ℓ}
Grounded (prod-image δ _ p q) = (Grounded p × Earlier δ p) × (Grounded q × Earlier δ q)

isPropSelfAt : (δ : Ord) (p : Producer) → isProp (SelfAt δ p)
isPropSelfAt δ (prod-self γ) = isSetOrd γ δ
isPropSelfAt δ (prod-image _ _ _ _) = isProp⊥*

isPropEarlier : (δ : Ord) (p : Producer) → isProp (Earlier δ p)
isPropEarlier δ p =
  isProp⊎ (snd (prod-stage p .fst ∈ˢ δ .fst)) (isPropSelfAt δ p) (disj p)
  where
  disj : (r : Producer) → ⟨ prod-stage r .fst ∈ˢ δ .fst ⟩ → SelfAt δ r → Empty.⊥
  disj (prod-self γ) h e =
    ∈-irrefl (δ .fst) (subst (λ z → ⟨ z .fst ∈ˢ δ .fst ⟩) e h)
  disj (prod-image _ _ _ _) h e = Empty.rec* e

isPropGrounded : (p : Producer) → isProp (Grounded p)
isPropGrounded (prod-self _) = isPropUnit*
isPropGrounded (prod-image δ _ p q) =
  isProp× (isProp× (isPropGrounded p) (isPropEarlier δ p))
          (isProp× (isPropGrounded q) (isPropEarlier δ q))
```

<!--en-->
## The comparison

`≺` reads "precedes". Two producers are compared by stage first. At a common
stage the self producer precedes every image, which is the order's reading of
the step's own shape: the level is the first new thing the step adds. Two images
at a common stage are compared by the operation index, then by the first
argument, then by the second. The recursion is structural in both arguments, so
the comparison is a definition and not a construction.
<!--zh-->
## 比较

`≺` 读作「先于」。两个生成者先比阶段。在公共阶段上，自身生成者先于每个像，这是该序对 step 自身形状的读法：层是 step 添加的第一件新东西。公共阶段上的两个像先比运算索引，再比第一参数，最后比第二参数。递归在两个自变量上都是结构性的，故这个比较是一个定义，而非一次构造。
<!--/-->

```agda
infix 4 _≺_

_≺_ : Producer → Producer → Type (ℓ-suc ℓ)
prod-self δ ≺ prod-self γ = ⟨ δ .fst ∈ˢ γ .fst ⟩
prod-self δ ≺ prod-image γ _ _ _ = ⟨ δ .fst ∈ˢ γ .fst ⟩ ⊎ (δ ≡ γ)
prod-image δ _ _ _ ≺ prod-self γ = ⟨ δ .fst ∈ˢ γ .fst ⟩
prod-image δ i p q ≺ prod-image γ j r s =
  ⟨ δ .fst ∈ˢ γ .fst ⟩
  ⊎ ((δ ≡ γ) × ((i Op.<∙ j) ⊎ ((i ≡ j) × ((p ≺ r) ⊎ ((p ≡ r) × (q ≺ s))))))
```

<!--en-->
Whatever else the comparison does, it never raises the stage: the stage of a
smaller producer is a member of, or equal to, the stage of a larger one, and
conversely a strictly smaller stage already decides the comparison. The first
reading is what makes the well-foundedness argument below able to work one stage
at a time; the second is what makes the order's first clause say what the
classical construction says.
<!--zh-->
无论这个比较还做了什么，它从不抬高阶段：较小生成者的阶段是较大者阶段的成员，或与之相等；反过来，严格更小的阶段已经判定了比较。第一条读式使下方的良基性论证得以一次只处理一个阶段；第二条则使该序的第一条子句说出经典构造所说的话。
<!--/-->

```agda
stage-mono : (p q : Producer) → p ≺ q
           → ⟨ prod-stage p .fst ∈ˢ prod-stage q .fst ⟩ ⊎ (prod-stage p ≡ prod-stage q)
stage-mono (prod-self _) (prod-self _) h = inl h
stage-mono (prod-self _) (prod-image _ _ _ _) (inl h) = inl h
stage-mono (prod-self _) (prod-image _ _ _ _) (inr e) = inr e
stage-mono (prod-image _ _ _ _) (prod-self _) h = inl h
stage-mono (prod-image _ _ _ _) (prod-image _ _ _ _) (inl h) = inl h
stage-mono (prod-image _ _ _ _) (prod-image _ _ _ _) (inr (e , _)) = inr e

stage-below : (p q : Producer)
            → ⟨ prod-stage p .fst ∈ˢ prod-stage q .fst ⟩ → p ≺ q
stage-below (prod-self _) (prod-self _) h = h
stage-below (prod-self _) (prod-image _ _ _ _) h = inl h
stage-below (prod-image _ _ _ _) (prod-self _) h = h
stage-below (prod-image _ _ _ _) (prod-image _ _ _ _) h = inl h
```

<!--en-->
Irreflexivity is four refutations, one per layer of the lexicographic stack, and
each is the corresponding law of the layer's own order.
<!--zh-->
非自反性是四条反驳，字典栈的每层一条，每条都是该层自身之序的相应定律。
<!--/-->

```agda
prod-irr : (p : Producer) → p ≺ p → Empty.⊥
prod-irr (prod-self δ) h = Stage.irr∙ δ h
prod-irr (prod-image δ _ _ _) (inl h) = Stage.irr∙ δ h
prod-irr (prod-image _ i _ _) (inr (_ , inl h)) = Op.irr∙ i h
prod-irr (prod-image _ _ p _) (inr (_ , inr (_ , inl h))) = prod-irr p h
prod-irr (prod-image _ _ _ q) (inr (_ , inr (_ , inr (_ , h)))) = prod-irr q h
```

<!--en-->
Trichotomy descends the same stack, deciding each layer with that layer's own
trichotomy and falling through to the next only when the layer returns an
equality. The last equality assembles the two trees by a path in each of the
four components.
<!--zh-->
三歧沿同一道栈下降，用每层自身的三歧判定该层，仅当该层给出相等时才落到下一层。最后一次相等在四个分量上各取一条道路，把两棵树装配起来。
<!--/-->

```agda
prod-tri : (p q : Producer) → Tri (p ≺ q) (p ≡ q) (q ≺ p)
prod-tri (prod-self δ) (prod-self γ) with Stage.tri∙ δ γ
... | lt h = lt h
... | eq e = eq (cong prod-self e)
... | gt h = gt h
prod-tri (prod-self δ) (prod-image γ _ _ _) with Stage.tri∙ δ γ
... | lt h = lt (inl h)
... | eq e = lt (inr e)
... | gt h = gt h
prod-tri (prod-image δ _ _ _) (prod-self γ) with Stage.tri∙ δ γ
... | lt h = lt h
... | eq e = gt (inr (sym e))
... | gt h = gt (inl h)
prod-tri (prod-image δ i p q) (prod-image γ j r s) with Stage.tri∙ δ γ
... | lt h = lt (inl h)
... | gt h = gt (inl h)
... | eq eδ with Op.tri∙ i j
...   | lt h = lt (inr (eδ , inl h))
...   | gt h = gt (inr (sym eδ , inl h))
...   | eq ei with prod-tri p r
...     | lt h = lt (inr (eδ , inr (ei , inl h)))
...     | gt h = gt (inr (sym eδ , inr (sym ei , inl h)))
...     | eq ep with prod-tri q s
...       | lt h = lt (inr (eδ , inr (ei , inr (ep , h))))
...       | gt h = gt (inr (sym eδ , inr (sym ei , inr (sym ep , h))))
...       | eq eqs = eq (λ k → prod-image (eδ k) (ei k) (ep k) (eqs k))
```

<!--en-->
Transitivity is the one law that has to look at three trees at once. Seven of
the eight shape combinations collapse into stage arithmetic, because a
comparison against a self producer carries nothing but the stage; the eighth is
the lexicographic stack again, where each layer either wins outright or hands
its equality to the layer below.
<!--zh-->
传递性是唯一一条要同时看三棵树的定律。八种形状组合中的七种坍缩为阶段算术，因为与自身生成者的比较除阶段外一无所载；第八种又是那道字典栈，其中每层或径直取胜、或把自己的相等交给下一层。
<!--/-->

```agda
prod-trans : (p q r : Producer) → p ≺ q → q ≺ r → p ≺ r
prod-trans (prod-self δ) (prod-self γ) (prod-self ε) h h' = Stage.trans∙ δ γ ε h h'
prod-trans (prod-self δ) (prod-self γ) (prod-image ε _ _ _) h (inl h') =
  inl (Stage.trans∙ δ γ ε h h')
prod-trans (prod-self δ) (prod-self γ) (prod-image ε _ _ _) h (inr e) =
  inl (subst (λ z → ⟨ δ .fst ∈ˢ z .fst ⟩) e h)
prod-trans (prod-self δ) (prod-image γ _ _ _) (prod-self ε) (inl h) h' =
  Stage.trans∙ δ γ ε h h'
prod-trans (prod-self δ) (prod-image γ _ _ _) (prod-self ε) (inr e) h' =
  subst (λ z → ⟨ z .fst ∈ˢ ε .fst ⟩) (sym e) h'
prod-trans (prod-self δ) (prod-image γ _ _ _) (prod-image ε _ _ _) (inl h) (inl h') =
  inl (Stage.trans∙ δ γ ε h h')
prod-trans (prod-self δ) (prod-image γ _ _ _) (prod-image ε _ _ _) (inl h) (inr (e , _)) =
  inl (subst (λ z → ⟨ δ .fst ∈ˢ z .fst ⟩) e h)
prod-trans (prod-self δ) (prod-image γ _ _ _) (prod-image ε _ _ _) (inr e) (inl h') =
  inl (subst (λ z → ⟨ z .fst ∈ˢ ε .fst ⟩) (sym e) h')
prod-trans (prod-self _) (prod-image _ _ _ _) (prod-image _ _ _ _) (inr e) (inr (e' , _)) =
  inr (e ∙ e')
prod-trans (prod-image δ _ _ _) (prod-self γ) (prod-self ε) h h' = Stage.trans∙ δ γ ε h h'
prod-trans (prod-image δ _ _ _) (prod-self γ) (prod-image ε _ _ _) h (inl h') =
  inl (Stage.trans∙ δ γ ε h h')
prod-trans (prod-image δ _ _ _) (prod-self γ) (prod-image ε _ _ _) h (inr e) =
  inl (subst (λ z → ⟨ δ .fst ∈ˢ z .fst ⟩) e h)
prod-trans (prod-image δ _ _ _) (prod-image γ _ _ _) (prod-self ε) (inl h) h' =
  Stage.trans∙ δ γ ε h h'
prod-trans (prod-image δ _ _ _) (prod-image γ _ _ _) (prod-self ε) (inr (e , _)) h' =
  subst (λ z → ⟨ z .fst ∈ˢ ε .fst ⟩) (sym e) h'
prod-trans (prod-image δ i p q) (prod-image γ j r s) (prod-image ε k t v) h h' =
  outer h h'
  where
  innerP : (p ≺ r) ⊎ ((p ≡ r) × (q ≺ s)) → (r ≺ t) ⊎ ((r ≡ t) × (s ≺ v))
         → (p ≺ t) ⊎ ((p ≡ t) × (q ≺ v))
  innerP (inl a) (inl b) = inl (prod-trans p r t a b)
  innerP (inl a) (inr (b , _)) = inl (subst (λ z → p ≺ z) b a)
  innerP (inr (a , _)) (inl b) = inl (subst (λ z → z ≺ t) (sym a) b)
  innerP (inr (a , a')) (inr (b , b')) = inr (a ∙ b , prod-trans q s v a' b')

  innerI : (i Op.<∙ j) ⊎ ((i ≡ j) × ((p ≺ r) ⊎ ((p ≡ r) × (q ≺ s))))
         → (j Op.<∙ k) ⊎ ((j ≡ k) × ((r ≺ t) ⊎ ((r ≡ t) × (s ≺ v))))
         → (i Op.<∙ k) ⊎ ((i ≡ k) × ((p ≺ t) ⊎ ((p ≡ t) × (q ≺ v))))
  innerI (inl a) (inl b) = inl (Op.trans∙ i j k a b)
  innerI (inl a) (inr (b , _)) = inl (subst (λ z → i Op.<∙ z) b a)
  innerI (inr (a , _)) (inl b) = inl (subst (λ z → z Op.<∙ k) (sym a) b)
  innerI (inr (a , a')) (inr (b , b')) = inr (a ∙ b , innerP a' b')

  outer : prod-image δ i p q ≺ prod-image γ j r s
        → prod-image γ j r s ≺ prod-image ε k t v
        → prod-image δ i p q ≺ prod-image ε k t v
  outer (inl a) (inl b) = inl (Stage.trans∙ δ γ ε a b)
  outer (inl a) (inr (b , _)) = inl (subst (λ z → ⟨ δ .fst ∈ˢ z .fst ⟩) b a)
  outer (inr (a , _)) (inl b) = inl (subst (λ z → ⟨ z .fst ∈ˢ ε .fst ⟩) (sym a) b)
  outer (inr (a , a')) (inr (b , b')) = inr (a ∙ b , innerI a' b')
```

<!--en-->
## Grounded producers, and the descent

The order lives on grounded producers, not on all trees. It has to: an image
node whose arguments may come from anywhere is comparable to images whose
arguments are arbitrarily complicated, and a lexicographic order with an
unbounded innermost slot has no well-foundedness to give. Grounding is exactly
the bound the step supplies, and it is what turns the descent into an induction
on the stage.
<!--zh-->
## 扎根的生成者，与下降

序住在扎根的生成者上，而非住在所有树上。它不得不如此：一个参数可以来自任何地方的像节点，要与参数任意复杂的诸像相比较，而最内层槽位无界的字典序给不出任何良基性。扎根性恰是 step 供给的那条界，也正是它把下降变成一场对阶段的归纳。
<!--/-->

```agda
Trace : Type (ℓ-suc ℓ)
Trace = Σ[ p ∈ Producer ] Grounded p

infix 4 _⊰_

_⊰_ : Trace → Trace → Type (ℓ-suc ℓ)
t ⊰ s = t .fst ≺ s .fst

trace-path : (t s : Trace) → t .fst ≡ s .fst → t ≡ s
trace-path t s = Σ≡Prop isPropGrounded

accMove : (a b : Trace) → a .fst ≡ b .fst → Acc _⊰_ b → Acc _⊰_ a
accMove a b e = subst (Acc _⊰_) (sym (trace-path a b e))

traceTri : (t s : Trace) → Tri (t ⊰ s) (t ≡ s) (s ⊰ t)
traceTri t s = go (prod-tri (t .fst) (s .fst))
  where
  go : Tri (t .fst ≺ s .fst) (t .fst ≡ s .fst) (s .fst ≺ t .fst)
     → Tri (t ⊰ s) (t ≡ s) (s ⊰ t)
  go (lt h) = lt h
  go (eq e) = eq (trace-path t s e)
  go (gt h) = gt h
```

<!--en-->
The induction hypothesis of the descent is that every grounded producer of a
stage strictly below `γ` is accessible. Under it, the self producer of `γ` is
accessible outright, because everything it dominates lies strictly below `γ`;
and an argument at `γ` is accessible either by the hypothesis or by being that
self producer, which is the only thing grounding allows at the current stage.
<!--zh-->
下降的归纳假设是：阶段严格低于 `γ` 的每个扎根生成者都可及。在它之下，`γ` 的自身生成者径直可及，因为它所支配的一切都严格低于 `γ`；而 `γ` 处的参数或经该假设可及、或就是那个自身生成者，那也是扎根性在当前阶段唯一允许的东西。
<!--/-->

```agda
StageAcc : Ord → Type (ℓ-suc ℓ)
StageAcc γ = (s : Trace) → ⟨ prod-stage (s .fst) .fst ∈ˢ γ .fst ⟩ → Acc _⊰_ s

accSelf : (γ : Ord) → StageAcc γ → Acc _⊰_ (prod-self γ , tt*)
accSelf γ H = acc (λ s h → H s (under s h))
  where
  under : (s : Trace) → s ⊰ (prod-self γ , tt*)
        → ⟨ prod-stage (s .fst) .fst ∈ˢ γ .fst ⟩
  under (prod-self _ , _) h = h
  under (prod-image _ _ _ _ , _) h = h
```

<!--en-->
The image case is the nested descent, three deep. Outside is the operation
index, whose order is finite; inside it the first argument, and inside that the
second, each descending in the producer order it already knows to be well
founded. Every predecessor either drops the stage, and is handed to the
hypothesis, or keeps it, and is met by one of the three inner steps after the
stage path is transported away.
<!--zh-->
像的情形是三层嵌套的下降。最外是运算索引，其序有穷；其内是第一参数，再内是第二参数，各自在已知良基的生成者序中下降。每个前驱或降低阶段，交给归纳假设；或保持阶段，在把阶段道路搬走之后由三个内层步骤之一接住。
<!--/-->

```agda
accImg : (γ : Ord) → StageAcc γ → (i : Op16) (p q : Producer)
       → (v : Grounded (prod-image γ i p q))
       → Acc _⊰_ (prod-image γ i p q , v)
accImg γ H i p q ((vp , ep) , (vq , eqq)) =
  outer i (Op.wf∙ i) p vp ep (accArg p vp ep) q vq eqq (accArg q vq eqq)
  where
  accArg : (r : Producer) (w : Grounded r) → Earlier γ r → Acc _⊰_ (r , w)
  accArg r w (inl h) = H (r , w) h
  accArg (prod-self δ) w (inr e) =
    accMove (prod-self δ , w) (prod-self γ , tt*) (cong prod-self e) (accSelf γ H)
  accArg (prod-image _ _ _ _) _ (inr e) = Empty.rec* e

  outer : (j : Op16) → Acc Op._<∙_ j
        → (r : Producer) (vr : Grounded r) (er : Earlier γ r) → Acc _⊰_ (r , vr)
        → (t : Producer) (vt : Grounded t) (et : Earlier γ t) → Acc _⊰_ (t , vt)
        → Acc _⊰_ (prod-image γ j r t , ((vr , er) , (vt , et)))
  outer j (acc rj) = midP
    where
    midP : (r : Producer) (vr : Grounded r) (er : Earlier γ r) → Acc _⊰_ (r , vr)
         → (t : Producer) (vt : Grounded t) (et : Earlier γ t) → Acc _⊰_ (t , vt)
         → Acc _⊰_ (prod-image γ j r t , ((vr , er) , (vt , et)))
    midP r vr er (acc rr) = midQ
      where
      midQ : (t : Producer) (vt : Grounded t) (et : Earlier γ t) → Acc _⊰_ (t , vt)
           → Acc _⊰_ (prod-image γ j r t , ((vr , er) , (vt , et)))
      midQ t vt et (acc rt) = acc descend
        where
        descend : (s : Trace)
                → s ⊰ (prod-image γ j r t , ((vr , er) , (vt , et)))
                → Acc _⊰_ s
        descend (prod-self δ , w) (inl h) = H (prod-self δ , w) h
        descend (prod-self δ , w) (inr e) = accArg (prod-self δ) w (inr e)
        descend (prod-image δ k a b , w) (inl h) = H (prod-image δ k a b , w) h
        descend (prod-image δ k a b , ((va , ea) , (vb , eb))) (inr (e , inl kj)) =
          accMove (prod-image δ k a b , ((va , ea) , (vb , eb)))
                  (prod-image γ k a b , ((va , ea') , (vb , eb')))
                  (λ n → prod-image (e n) k a b)
                  (outer k (rj k kj) a va ea' (accArg a va ea')
                           b vb eb' (accArg b vb eb'))
          where
          ea' : Earlier γ a
          ea' = subst (λ z → Earlier z a) e ea
          eb' : Earlier γ b
          eb' = subst (λ z → Earlier z b) e eb
        descend (prod-image δ k a b , ((va , ea) , (vb , eb)))
                (inr (e , inr (ek , inl ar))) =
          accMove (prod-image δ k a b , ((va , ea) , (vb , eb)))
                  (prod-image γ j a b , ((va , ea') , (vb , eb')))
                  (λ n → prod-image (e n) (ek n) a b)
                  (midP a va ea' (rr (a , va) ar) b vb eb' (accArg b vb eb'))
          where
          ea' : Earlier γ a
          ea' = subst (λ z → Earlier z a) e ea
          eb' : Earlier γ b
          eb' = subst (λ z → Earlier z b) e eb
        descend (prod-image δ k a b , ((va , ea) , (vb , eb)))
                (inr (e , inr (ek , inr (ea2 , bt)))) =
          accMove (prod-image δ k a b , ((va , ea) , (vb , eb)))
                  (prod-image γ j r b , ((vr , er) , (vb , eb')))
                  (λ n → prod-image (e n) (ek n) (ea2 n) b)
                  (midQ b vb eb' (rt (b , vb) bt))
          where
          eb' : Earlier γ b
          eb' = subst (λ z → Earlier z b) e eb
```

<!--en-->
The two cases together are one transfinite induction on the stage, and the
well-order of a producer follows by reading it at the successor of its own
stage. That closes the bundle.
<!--zh-->
两种情形合起来就是对阶段的一场超穷归纳，而一个生成者的良基性只需在它自己阶段的后继处读取即得。束就此收拢。
<!--/-->

```agda
accBelow : (d : S) (t : Trace) → ⟨ prod-stage (t .fst) .fst ∈ˢ d ⟩ → Acc _⊰_ t
accBelow = ∈-induction goD
  where
  goD : (d : S)
      → ((e : S) → e ∈ᵗ d → (t : Trace)
        → ⟨ prod-stage (t .fst) .fst ∈ˢ e ⟩ → Acc _⊰_ t)
      → (t : Trace) → ⟨ prod-stage (t .fst) .fst ∈ˢ d ⟩ → Acc _⊰_ t
  goD d ih (prod-self γ , tt*) h = accSelf γ (ih (γ .fst) h)
  goD d ih (prod-image γ i p q , v) h = accImg γ (ih (γ .fst) h) i p q v

accTrace : (t : Trace) → Acc _⊰_ t
accTrace t = accBelow (sucV (prod-stage (t .fst) .fst)) t
  (self∈sucV (prod-stage (t .fst) .fst))

traceSWO : SWO Trace
traceSWO = record
  { _<∙_   = _⊰_
  ; tri∙   = traceTri
  ; irr∙   = λ t h → prod-irr (t .fst) h
  ; trans∙ = λ t s r h h' → prod-trans (t .fst) (s .fst) (r .fst) h h'
  ; wf∙    = accTrace }
```

<!--en-->
## The producer view, in both directions

A producer describes a set: the self producer of `δ` describes the level `S_δ`,
and an image producer describes the value of its operation on the two sets its
arguments describe. The first direction of the view says that description lands
where it should. A grounded producer whose stage belongs to an ordinal `α`
describes a member of `S_α`: the arguments of an image sit in `S_δ ∪ {S_δ}` by
grounding, so the step admits the value, and the level admits the step. This is
`step-in` realizing every producer, read through the sealed surface and nothing
else.
<!--zh-->
## 生成者视角的两个方向

一个生成者描述一个集合：`δ` 的自身生成者描述层 `S_δ`，而一个像生成者描述其运算施于两个参数所描述之集的值。视角的第一个方向说：描述落在它该落的地方。阶段属于序数 `α` 的扎根生成者描述 `S_α` 的一个成员：由扎根性，像的参数落在 `S_δ ∪ {S_δ}` 中，故 step 接纳该值，而层接纳 step。这就是 `step-in` 实现每个生成者，且只经封印的表面读出。
<!--/-->

```agda
prod-mem : (α : S) → IsOrd α → (p : Producer) → Grounded p
         → ⟨ prod-stage p .fst ∈ˢ α ⟩ → ⟨ prod-value p ∈ˢ Sset α ⟩
prod-mem α _ (prod-self δ) _ h = Sset-mem {α = α} {β = δ .fst} h
prod-mem α _ (prod-image δ i p q) ((vp , ep) , (vq , eqq)) h =
  Sset-in α (δ .fst) (Fof i (prod-value p) (prod-value q)) h
    (step-in-img (Sset (δ .fst)) (Fof i (prod-value p) (prod-value q)) i
      (prod-value p) (prod-value q)
      (toArg p vp ep (prod-mem (δ .fst) (δ .snd) p vp))
      (toArg q vq eqq (prod-mem (δ .fst) (δ .snd) q vq))
      refl)
  where
  toArg : (r : Producer) (w : Grounded r) → Earlier δ r
        → (⟨ prod-stage r .fst ∈ˢ δ .fst ⟩ → ⟨ prod-value r ∈ˢ Sset (δ .fst) ⟩)
        → ⟨ prod-value r ∈ˢ u' (Sset (δ .fst)) ⟩
  toArg r _ (inl h') f = u'-in (Sset (δ .fst)) (prod-value r) (f h')
  toArg (prod-self ε) _ (inr e) _ =
    subst (λ z → ⟨ Sset (z .fst) ∈ˢ u' (Sset (δ .fst)) ⟩) (sym e)
      (u-self-in (Sset (δ .fst)))
  toArg (prod-image _ _ _ _) _ (inr e) _ = Empty.rec* e
```

<!--en-->
The second direction says the view is total: every member of a level has a
producer, and one whose stage is already inside the index. This is `step-out`
giving every member an arm, run along the tower's own recursion. The membership
arm defers to the earlier level, where the induction hypothesis supplies a
producer of a strictly smaller stage; the self arm and the image arm build one on
the spot, and in the image arm the two arguments are handled by the same split,
which is precisely where grounding is discharged.
<!--zh-->
第二个方向说这个视角是完全的：层的每个成员都有生成者，且其阶段已在索引之内。这就是 `step-out` 给每个成员一条臂，沿塔自身的递归跑一遍。成员臂推给更早的层，那里的归纳假设供给一个阶段严格更小的生成者；自身臂与像臂就地造一个，而像臂中两个参数由同一次切分处理，扎根性正是在那里被清偿的。
<!--/-->

```agda
TraceAt : S → S → Type (ℓ-suc ℓ)
TraceAt α x =
  Σ[ t ∈ Trace ] (⟨ prod-stage (t .fst) .fst ∈ˢ α ⟩ × (prod-value (t .fst) ≡ x))

trace-exists : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Sset α ⟩ → ∥ TraceAt α x ∥₁
trace-exists = ∈-induction goA
  where
  goA : (α : S)
      → ((β : S) → β ∈ᵗ α → IsOrd β → (x : S) → ⟨ x ∈ˢ Sset β ⟩ → ∥ TraceAt β x ∥₁)
      → IsOrd α → (x : S) → ⟨ x ∈ˢ Sset α ⟩ → ∥ TraceAt α x ∥₁
  goA α ih ordα x x∈Sα = PT.rec squash₁ atStage (Sset-out α x x∈Sα)
    where
    atStage : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ∥ TraceAt α x ∥₁
    atStage (δ , δ∈α , x∈stepδ) = PT.rec squash₁ byArm (step-out (Sset δ) x x∈stepδ)
      where
      dOrd : Ord
      dOrd = δ , mem-ord {A = α} ordα δ δ∈α

      raise : (t : Trace) → ⟨ prod-stage (t .fst) .fst ∈ˢ δ ⟩
            → ⟨ prod-stage (t .fst) .fst ∈ˢ α ⟩
      raise t h = ordα .fst {x = δ} {y = prod-stage (t .fst) .fst} h δ∈α

      atδ : (y : S) → ⟨ y ∈ˢ Sset δ ⟩ → ∥ TraceAt δ y ∥₁
      atδ = ih δ δ∈α (dOrd .snd)

      ArgTrace : S → Type (ℓ-suc ℓ)
      ArgTrace c = Σ[ t ∈ Trace ] (Earlier dOrd (t .fst) × (prod-value (t .fst) ≡ c))

      argOf : (c : S) → (⟨ c ∈ˢ Sset δ ⟩ ⊎ (c ≡ Sset δ)) → ∥ ArgTrace c ∥₁
      argOf c (inl c∈) = PT.map (λ { (t , h , v) → t , inl h , v }) (atδ c c∈)
      argOf c (inr c≡) = ∣ (prod-self dOrd , tt*) , inr refl , sym c≡ ∣₁

      byArm : StepArm (Sset δ) x → ∥ TraceAt α x ∥₁
      byArm (arm-member x∈) =
        PT.map (λ { (t , h , v) → t , raise t h , v }) (atδ x x∈)
      byArm (arm-self x≡) = ∣ (prod-self dOrd , tt*) , δ∈α , sym x≡ ∣₁
      byArm (arm-image i a b sa sb x≡) =
        PT.rec squash₁ (λ ta → PT.map (build ta) (argOf b sb)) (argOf a sa)
        where
        build : ArgTrace a → ArgTrace b → TraceAt α x
        build (ta , ea , va) (tb , eb , vb) =
            ( prod-image dOrd i (ta .fst) (tb .fst)
            , ((ta .snd , ea) , (tb .snd , eb)) )
          , δ∈α
          , (cong₂ (Fof i) va vb ∙ sym x≡)
```

<!--en-->
## The least producer

A set has many producers and the order picks one: the least. This is the first
of the chapter's two searches, and the first place the excluded middle is spent,
through the least-element theorem of the well-order vocabulary. What comes back
is a producer that describes the set and that nothing describing the same set
precedes.

Two readings matter downstream. The choice does not depend on *which* proof of
having a producer is handed in, since that hypothesis is a proposition; and the
least producer determines the set it describes, so a set is recoverable from its
least producer. The second reading is the injectivity the pull-back needs.
<!--zh-->
## 最小生成者

一个集合有许多生成者，而序挑出一个：最小的那个。这是本章两场搜索的第一场，也是排中律的第一处花销，经良序词汇的极小元定理支出。取回的是一个生成者，它描述该集合，且描述同一集合者无一先于它。

有两条读式在下游要紧。这个选取不取决于交进来的是「有生成者」的**哪一个**证明，因为该前提是命题；而最小生成者决定了它所描述的集合，故集合可从其最小生成者复原。第二条读式正是拉回所需的单射性。
<!--/-->

```agda
HasTrace : S → Type (ℓ-suc ℓ)
HasTrace x = ∥ Σ[ t ∈ Trace ] (prod-value (t .fst) ≡ x) ∥₁

valueIs : S → Trace → hProp (ℓ-suc ℓ)
valueIs x t = (prod-value (t .fst) ≡ x) , isSetS (prod-value (t .fst)) x

leastTraceOf : (x : S) → HasTrace x → Σ[ t ∈ Trace ] IsLeast traceSWO (valueIs x) t
leastTraceOf x = leastOf traceSWO lem (valueIs x)

leastTrace : (x : S) → HasTrace x → Trace
leastTrace x h = leastTraceOf x h .fst

leastTrace-value : (x : S) (h : HasTrace x) → prod-value (leastTrace x h .fst) ≡ x
leastTrace-value x h = leastTraceOf x h .snd .fst

leastTrace-least : (x : S) (h : HasTrace x) (t : Trace)
                 → prod-value (t .fst) ≡ x → t ⊰ leastTrace x h → Empty.⊥
leastTrace-least x h t v = leastTraceOf x h .snd .snd t v

leastTrace-irrel : (x : S) (h k : HasTrace x) → leastTrace x h ≡ leastTrace x k
leastTrace-irrel x h k = cong (leastTrace x) (squash₁ h k)

leastTrace-inj : (x y : S) (hx : HasTrace x) (hy : HasTrace y)
               → leastTrace x hx ≡ leastTrace y hy → x ≡ y
leastTrace-inj x y hx hy p = sym (leastTrace-value x hx)
  ∙ cong (λ t → prod-value (t .fst)) p ∙ leastTrace-value y hy
```

<!--en-->
## The order of a level

The key of a member of a level is its least producer, and the order of the level
is the tree order read through the key. Injectivity of the key is the second
reading above, so the pull-back combinator does the rest: trichotomy,
irreflexivity, transitivity and well-foundedness all arrive from the tree, and
none of them is proved again here.
<!--zh-->
## 一层的序

某层一个成员的键是它的最小生成者，而该层的序就是经键读出的树序。键的单射性即上文第二条读式，其余由拉回组合子完成：三歧、非自反、传递与良基全部自树而来，此处一条也不重证。
<!--/-->

```agda
Member : S → Type (ℓ-suc ℓ)
Member α = Σ[ x ∈ S ] ⟨ x ∈ˢ Sset α ⟩

member-trace : (α : S) → IsOrd α → (m : Member α) → HasTrace (m .fst)
member-trace α ordα m =
  PT.map (λ { (t , _ , v) → t , v }) (trace-exists α ordα (m .fst) (m .snd))

memberKey : (α : S) → IsOrd α → Member α → Trace
memberKey α ordα m = leastTrace (m .fst) (member-trace α ordα m)

memberKey-inj : (α : S) (ordα : IsOrd α) (m n : Member α)
              → memberKey α ordα m ≡ memberKey α ordα n → m ≡ n
memberKey-inj α ordα m n p = Σ≡Prop (λ y → snd (y ∈ˢ Sset α))
  (leastTrace-inj (m .fst) (n .fst)
    (member-trace α ordα m) (member-trace α ordα n) p)

Sset-below : (α : S) → IsOrd α → Member α → Member α → Type (ℓ-suc ℓ)
Sset-below α ordα m n = memberKey α ordα m ⊰ memberKey α ordα n

Sset-order : (α : S) → IsOrd α → SWO (Member α)
Sset-order α ordα = pullSWO traceSWO (memberKey α ordα) (memberKey-inj α ordα)
```

<!--en-->
## Coherence

Here is the lemma the classical construction needs and never states. The key of
a set does not mention the level the set is read at: it is the least producer of
the set, full stop. So two levels that both contain a set assign it the same key,
and the comparison of two such sets is literally the same type at both levels.
The form the texts use, the order of a level restricted to an earlier level, is
the special case: for `β` a member of `α`, cumulativity supplies the missing
membership and the statement below is the restriction. So the union taken at a
limit index is a union of restrictions of one relation rather than a union of
unrelated ones.
<!--zh-->
## 相容

这就是经典构造需要却从不陈述的那条引理。一个集合的键不提及该集合被读取的那一层：它就是这个集合的最小生成者，仅此而已。故同时含有某集合的两层给它同一个键，而这样两个集合的比较在两层上是字面相同的类型。文献所用的形式，即某层的序限制到更早一层，是其特例：当 `β` 是 `α` 的成员时，累积性补上缺的那份隶属，下面这句就是那个限制。故极限索引处所取的并，是同一个关系诸限制之并，不是互不相干者之并。
<!--/-->

```agda
order-coherent : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x : S)
               → (xα : ⟨ x ∈ˢ Sset α ⟩) (xβ : ⟨ x ∈ˢ Sset β ⟩)
               → memberKey α ordα (x , xα) ≡ memberKey β ordβ (x , xβ)
order-coherent α β ordα ordβ x xα xβ =
  leastTrace-irrel x (member-trace α ordα (x , xα)) (member-trace β ordβ (x , xβ))

-- perf: a transported membership proof inside a compared type forces the
-- successor index's union tower to normalize; the memberships stay variables
order-agrees : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x y : S)
             → (xα : ⟨ x ∈ˢ Sset α ⟩) (yα : ⟨ y ∈ˢ Sset α ⟩)
             → (xβ : ⟨ x ∈ˢ Sset β ⟩) (yβ : ⟨ y ∈ˢ Sset β ⟩)
             → Sset-below α ordα (x , xα) (y , yα)
             ≡ Sset-below β ordβ (x , xβ) (y , yβ)
order-agrees α β ordα ordβ x y xα yα xβ yβ = cong₂ _⊰_
  (order-coherent α β ordα ordβ x xα xβ)
  (order-coherent α β ordα ordβ y yα yβ)
```

<!--en-->
## The birth stage

The order compares stages first, so the least producer of a set carries the least
stage at which the set is produced at all. That is the set's birth stage, and it
comes out of the minimality of the key rather than out of a separate search: the
stage of a producer never rises along the order, so a producer that is least is
least in stage as well.

Three readings follow. The stage of a member of a level is a member of the index;
the member is already in the level one step past its stage; and no earlier level
contains it, since any level that does supplies a producer whose stage the least
one cannot exceed.
<!--zh-->
## 诞生阶段

序先比阶段，故一个集合的最小生成者携带该集合被产出的最小阶段。那就是该集合的诞生阶段，而它出自键的极小性、而非另一场搜索：生成者的阶段沿序从不上升，故最小的生成者在阶段上也最小。

由此得三条读式。层的成员的阶段是索引的成员；该成员在其阶段之后一步的层中已经在场；且更早的层都不含它，因为任何含它的层都供出一个生成者，最小者的阶段不可能超过它。
<!--/-->

```agda
stage-least : (x : S) (h : HasTrace x) (γ : S) → IsOrd γ → (t : Trace)
            → prod-value (t .fst) ≡ x → ⟨ prod-stage (t .fst) .fst ∈ˢ γ ⟩
            → ⟨ prod-stage (leastTrace x h .fst) .fst ∈ˢ γ ⟩
stage-least x h γ ordγ t v st = go (traceTri (leastTrace x h) t)
  where
  k : Trace
  k = leastTrace x h
  fromStage : ⟨ prod-stage (k .fst) .fst ∈ˢ prod-stage (t .fst) .fst ⟩
              ⊎ (prod-stage (k .fst) ≡ prod-stage (t .fst))
            → ⟨ prod-stage (k .fst) .fst ∈ˢ γ ⟩
  fromStage (inl m) =
    ordγ .fst {x = prod-stage (t .fst) .fst} {y = prod-stage (k .fst) .fst} m st
  fromStage (inr e) = subst (λ z → ⟨ z .fst ∈ˢ γ ⟩) (sym e) st
  go : Tri (k ⊰ t) (k ≡ t) (t ⊰ k) → ⟨ prod-stage (k .fst) .fst ∈ˢ γ ⟩
  go (lt h') = fromStage (stage-mono (k .fst) (t .fst) h')
  go (eq e) = fromStage (inr (cong (λ s → prod-stage (s .fst)) e))
  go (gt h') = Empty.rec (leastTrace-least x h t v h')

memberStage : (α : S) → IsOrd α → Member α → S
memberStage α ordα m = prod-stage (memberKey α ordα m .fst) .fst

memberStage-ord : (α : S) (ordα : IsOrd α) (m : Member α)
                → IsOrd (memberStage α ordα m)
memberStage-ord α ordα m = prod-stage (memberKey α ordα m .fst) .snd

memberStage-in : (α : S) (ordα : IsOrd α) (m : Member α)
               → ⟨ memberStage α ordα m ∈ˢ α ⟩
memberStage-in α ordα m = PT.rec (snd (memberStage α ordα m ∈ˢ α))
  (λ { (t , st , v) →
     stage-least (m .fst) (member-trace α ordα m) α ordα t v st })
  (trace-exists α ordα (m .fst) (m .snd))

memberStage-first : (α : S) (ordα : IsOrd α) (m : Member α)
                  → ⟨ m .fst ∈ˢ Sset (sucV (memberStage α ordα m)) ⟩
memberStage-first α ordα m =
  subst (λ z → ⟨ z ∈ˢ Sset (sucV (memberStage α ordα m)) ⟩)
    (leastTrace-value (m .fst) (member-trace α ordα m))
    (prod-mem (sucV (memberStage α ordα m)) (suc-ord (memberStage-ord α ordα m))
      (memberKey α ordα m .fst) (memberKey α ordα m .snd)
      (self∈sucV (memberStage α ordα m)))

memberStage-least : (α : S) (ordα : IsOrd α) (m : Member α)
                  → (γ : S) → IsOrd γ → ⟨ m .fst ∈ˢ Sset γ ⟩
                  → ⟨ memberStage α ordα m ∈ˢ γ ⟩
memberStage-least α ordα m γ ordγ h = PT.rec (snd (memberStage α ordα m ∈ˢ γ))
  (λ { (t , st , v) →
     stage-least (m .fst) (member-trace α ordα m) γ ordγ t v st })
  (trace-exists γ ordγ (m .fst) h)
```

<!--en-->
## The successor clauses

What the order does at a successor index is now readable off the pieces, and it
is the classical recipe. A member of `S_{β+1}` that is not already in `S_β` is
born exactly at `β`: it cannot be born earlier, since a set born earlier is
already in `S_β`, one level past its own birth being at or below `β`. So an old
member's birth stage is a member of `β` while a new member's is `β` itself, and
the first clause of the comparison puts every old member below every new one.
Two old members are compared by the order of `S_β`, which is `order-agrees`{.Agda}
read at the successor index. Two new members share the stage `β`, so the comparison falls
through to the arm, then the operation index, then the two arguments, exactly as
the definition of `≺` reads.
<!--zh-->
## 后继处的诸子句

序在后继索引处做什么，如今可以从各部件上读出，而它正是那个经典配方。`S_{β+1}` 中尚不在 `S_β` 里的成员恰在 `β` 处诞生：它不能更早诞生，因为更早诞生的集合已经在 `S_β` 中，其诞生之后一层不高于 `β`。故旧成员的诞生阶段是 `β` 的成员，而新成员的诞生阶段就是 `β`，于是比较的第一条子句把每个旧成员放在每个新成员之下。两个旧成员按 `S_β` 的序比较，这就是 `order-agrees`{.Agda} 在后继索引处的读法。两个新成员共享阶段 `β`，故比较落到臂、再到运算索引、再到两个参数，与 `≺` 的定义所读一模一样。
<!--/-->

```agda
memberStage-new : (β : S) (ordβ : IsOrd β) (m : Member (sucV β))
                → (⟨ m .fst ∈ˢ Sset β ⟩ → Empty.⊥)
                → memberStage (sucV β) (suc-ord ordβ) m ≡ β
memberStage-new β ordβ m fresh =
  ∈sucV-elim {A = β} {x = δ} (isSetS δ β)
    (memberStage-in (sucV β) ordS m)
    (λ δ∈β → Empty.rec (fresh (inLevel δ∈β)))
    (λ e → e)
  where
  ordS : IsOrd (sucV β)
  ordS = suc-ord ordβ
  δ : S
  δ = memberStage (sucV β) ordS m
  ordδ : IsOrd δ
  ordδ = memberStage-ord (sucV β) ordS m
  atSuc : ⟨ m .fst ∈ˢ Sset (sucV δ) ⟩
  atSuc = memberStage-first (sucV β) ordS m
  inLevel : ⟨ δ ∈ˢ β ⟩ → ⟨ m .fst ∈ˢ Sset β ⟩
  inLevel δ∈β = go (ord-tri (sucV δ) (suc-ord ordδ) β ordβ)
    where
    go : OrdTri (sucV δ) β → ⟨ m .fst ∈ˢ Sset β ⟩
    go (inl h) = Sset-mono {α = β} {β = sucV δ} h (m .fst) atSuc
    go (inr (inl e)) = subst (λ z → ⟨ m .fst ∈ˢ Sset z ⟩) e atSuc
    go (inr (inr h)) = Empty.rec* {A = ⟨ m .fst ∈ˢ Sset β ⟩}
      (∈sucV-elim {A = δ} {x = β} (isProp⊥* {ℓ-suc ℓ}) h
        (λ β∈δ → lift (∈-irrefl β (ordβ .fst {x = δ} {y = β} β∈δ δ∈β)))
        (λ β≡δ → lift (∈-irrefl β (subst (λ z → ⟨ z ∈ˢ β ⟩) (sym β≡δ) δ∈β))))

old-before-new : (β : S) (ordβ : IsOrd β) (x y : S)
               → (x∈ : ⟨ x ∈ˢ Sset (sucV β) ⟩) (y∈ : ⟨ y ∈ˢ Sset (sucV β) ⟩)
               → ⟨ x ∈ˢ Sset β ⟩ → (⟨ y ∈ˢ Sset β ⟩ → Empty.⊥)
               → Sset-below (sucV β) (suc-ord ordβ) (x , x∈) (y , y∈)
old-before-new β ordβ x y x∈ y∈ old fresh =
  stage-below (memberKey (sucV β) (suc-ord ordβ) (x , x∈) .fst)
              (memberKey (sucV β) (suc-ord ordβ) (y , y∈) .fst)
              (subst (λ z → ⟨ memberStage (sucV β) (suc-ord ordβ) (x , x∈) ∈ˢ z ⟩)
                (sym (memberStage-new β ordβ (y , y∈) fresh))
                (memberStage-least (sucV β) (suc-ord ordβ) (x , x∈) β ordβ old))

```

<!--en-->
## Choice, without syntax

Every level is well-orderable, and at a limit index that is the statement about
`J`. Nothing internal is claimed: the order is a bundle of the ambient theory,
not an element of the level, and no formula defines it. That is the point of
taking this route to choice. The internal reading, the one that makes the order
sequence a member of the hierarchy, belongs to a later chapter and is not needed
for what follows.
<!--zh-->
## 无需语法的选择

每一层都可良序化，而在极限索引处这就是关于 `J` 的那句话。此处不声称任何内部性：这个序是周遭理论中的一个束，不是层的元素，也没有公式定义它。这正是走这条路通向选择的要点。内部读法，即使序列成为层级成员的那种读法，属于后面的章节，而下文不需要它。
<!--/-->

```agda
Jset-order : (α : S) (lim : ⟨ isLimit α ⟩)
           → SWO (Σ[ x ∈ S ] ⟨ x ∈ˢ Jset α lim ⟩)
Jset-order α lim = Sset-order α (isLimit-ord α lim)
```

<!--en-->
And the corollary the book wants. A set of the level has all its members and all
their members inside the level, by transitivity; so a family of non-empty sets
indexed by the members of a set of the level admits a choice function, obtained
by taking, in each member, the least element of that member. This is the second
and last search, and the second and last place the excluded middle is spent.
<!--zh-->
以及本书想要的推论。由传递性，层的一个集合的所有成员及其成员都在层内；故以层中某集合的诸成员为索引的非空集族容许一个选择函数，办法是在每个成员中取该成员的极小元。这是第二场也是最后一场搜索，也是排中律的第二处也是最后一处花销。
<!--/-->

```agda
Sset-choice : (α : S) → IsOrd α → (a : S) → ⟨ a ∈ˢ Sset α ⟩
            → ((y : S) → ⟨ y ∈ˢ a ⟩ → ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ y ⟩ ∥₁)
            → Σ[ ch ∈ ((y : S) → ⟨ y ∈ˢ a ⟩ → S) ]
                ((y : S) (h : ⟨ y ∈ˢ a ⟩) → ⟨ ch y h ∈ˢ y ⟩)
Sset-choice α ordα a a∈ ne =
  (λ y h → pick y h .fst .fst) , (λ y h → pick y h .snd .fst)
  where
  inLevel : (y : S) → ⟨ y ∈ˢ a ⟩ → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ Sset α ⟩
  inLevel y h z hz =
    Sset-trans α {x = y} {y = z} hz (Sset-trans α {x = a} {y = y} h a∈)
  isIn : (y : S) → Member α → hProp (ℓ-suc ℓ)
  isIn y m = m .fst ∈ˢ y
  pick : (y : S) (h : ⟨ y ∈ˢ a ⟩)
       → Σ[ m ∈ Member α ] IsLeast (Sset-order α ordα) (isIn y) m
  pick y h = leastOf (Sset-order α ordα) lem (isIn y)
    (PT.map (λ { (z , hz) → (z , inLevel y h z hz) , hz }) (ne y h))

Jset-choice : (α : S) (lim : ⟨ isLimit α ⟩) (a : S) → ⟨ a ∈ˢ Jset α lim ⟩
            → ((y : S) → ⟨ y ∈ˢ a ⟩ → ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ y ⟩ ∥₁)
            → Σ[ ch ∈ ((y : S) → ⟨ y ∈ˢ a ⟩ → S) ]
                ((y : S) (h : ⟨ y ∈ˢ a ⟩) → ⟨ ch y h ∈ˢ y ⟩)
Jset-choice α lim = Sset-choice α (isLimit-ord α lim)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The canonical well-order is in place. A producer is a stage with either the self
mark or an operation index and two argument producers, mirroring the three arms
of the sealed step surface, with the membership arm deferring to an earlier
stage. Grounding is the bound the step supplies, and it is what makes the
lexicographic comparison well founded: the descent is an induction on the stage
with a three-deep nested accessibility inside it. The order of a level is the
tree order pulled back along "least producer", which makes coherence
(`order-coherent`{.Agda}, `order-agrees`{.Agda}) a consequence of the key not
mentioning the level, and makes the birth stage
(`memberStage-first`{.Agda}, `memberStage-least`{.Agda}) a consequence of the
key's minimality. The endgame is `Sset-order`{.Agda} and `Jset-order`{.Agda}:
every level, and every `J` at a limit, carries a well-order, and
`Sset-choice`{.Agda} turns that into a choice function on any set of the level.
The excluded middle is spent twice, both times on a search, and the internal
reading of the order sequence is left to a later chapter.
<!--zh-->
典范良序就位。生成者是一个阶段，配以自身标记、或一个运算索引加两个参数生成者，映照封印的 step 表面的三条臂，而成员臂推给更早的阶段。扎根性是 step 供给的那条界，也正是它使字典比较良基：下降是对阶段的一场归纳，其内嵌着三层可及性。层的序是树序沿「最小生成者」的拉回，这使相容 (`order-coherent`{.Agda}、`order-agrees`{.Agda}) 成为「键不提及层」的推论，也使诞生阶段 (`memberStage-first`{.Agda}、`memberStage-least`{.Agda}) 成为键的极小性的推论。终局是 `Sset-order`{.Agda} 与 `Jset-order`{.Agda}：每一层、以及极限处的每个 `J`，都带一个良序，而 `Sset-choice`{.Agda} 把它变成层中任一集合上的选择函数。排中律花掉两次，两次都花在搜索上，而序列的内部读法留给后面的章节。
<!--/-->
