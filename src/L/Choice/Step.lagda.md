# One order for every stage

<!--en-->
The previous chapters have three things ready and one thing missing. The stage
chapter located, for each cell, the one stage at which it first has a member, and
showed that stage to be a successor; the finite chapter well-ordered every stage
below `ω` and the limit stage itself; the naming chapter wrote each member of a
successor stage as a name and well-ordered the names, **given a well-order of the
stage below**. That proviso is the missing thing. Names cannot order a stage
until the stage below is ordered, so what has to be built is not one order but a
family: an order at every stage, each of them an ingredient of the next.

The family is built by membership induction on the ordinal, and the whole chapter
turns on one decision about what it compares first. A member of a stage entered
the tower at a definite moment: there is an earliest stage containing it, that
stage is a successor, and the ordinal it succeeds is the one the set was carved
over. **That ordinal is the primary key.** Two sets carved at different moments
are compared by those moments and by nothing else; only two sets carved at the
same moment are compared by the machinery of that moment, which is the previous
chapter's names, or, below the limit stage, the finite chapter's comparison at
the earliest disagreement.

Taking the stage as the primary key buys the property the rest of the part needs.
The order at a large stage has to restrict, on a smaller one, to the order there,
or a choice made at one stage would be unmade at the next. Here that is not a
theorem about the construction but a reading of the definition: the comparison of
two sets never mentions the stage it is being read at. It mentions the two sets'
own births, and those do not move.
<!--zh-->
前几章备齐了三样东西，还缺一样。阶段那一章为每一格定位了它首次拥有成员的那个阶段，并证明那是一个后继；有穷那一章把 `ω` 以下的每个阶段连同极限阶段本身都良序化了；命名那一章把后继阶段的每个成员写成名字，并把诸名字良序化，**前提是下面那个阶段已有良序**。所缺的正是这个前提。下面那个阶段未被排序之前，名字排不了这个阶段的序，故要造的不是一个序，而是一族：每个阶段一个序，而每一个都是下一个的配料。

这一族沿序数的成员归纳造出，而全章的关键是一个决定：先比较什么。阶段的一个成员是在一个确定的时刻进入塔的：存在包含它的最早阶段，那个阶段是后继，而它所后继的那个序数，就是该集合被雕出时所依据的那一个。**那个序数就是主键。** 雕出时刻不同的两个集合，仅凭那两个时刻比较，别无其他；只有雕出时刻相同的两个集合，才由那个时刻的机器来比较，而那机器就是上一章的名字，或者，在极限阶段以下，是有穷那一章按最先分歧处的比较。

以阶段为主键，换来的正是本部余下部分所需的那条性质。大阶段上的序，限制到较小的阶段上，必须就是那里的序，否则在一个阶段作出的选取会在下一个阶段被推翻。而此处这不是关于该构造的一条定理，而是定义的一种读法：两个集合的比较从不提到它是在哪个阶段处被读的。它提到的是那两个集合各自的诞生阶段，而那是不动的。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Step {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Choice.Stage {ℓ} lem using ( IsPredOf; predOf; carveAt )
open import L.Choice.Finite {ℓ} lem using ( Tri-map )
open import L.Choice.Name {ℓ} lem using ( module Naming )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; isPropLeastOf )

open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The stage a set is carved at
<!--zh-->
## 一个集合被雕出的阶段
<!--/-->

<!--en-->
The stage chapter gave every constructible set its earliest stage, and the
choice-stage chapter showed, for a cell, that the earliest stage meeting it is a
successor. Neither of those arguments was ever about cells or about single sets.
Both take a property of ordinals, its least stage, and a witness carved below
that stage, and both conclude that the least stage is a successor; so the
argument is written once, there, and this chapter is its second instance.

The property here is plain membership in the tower, and it is the *simpler* of
the two. A cell is met by *some* member, so the choice-stage chapter has a
truncation to strip before it can hand the argument a witness; a set is its own
witness, and there is nothing to strip. The application there is eleven lines and
the one here is four. What this chapter used to claim, that the argument applies
verbatim to a single set, was true of the split and of the carve and false of the
interface: the reuse it named was never available until the argument itself was
written over the property.

Two names cross the boundary and no more. `carveAt`{.Agda} reads the set out of
its earliest stage and renames the carve to a successor, and `predOf`{.Agda}
turns that into the predecessor, refuting the low branch by minimality. The split
inside is still a comparison in disguise, written as a named helper with its
conclusion spelled out, and it is now written in one place rather than two.
<!--zh-->
阶段那一章为每个可构造集给出了它的最早阶段，而选取阶段那一章为一格证明了与它相交的最早阶段是后继。那两个论证从来都不是关于格、也不是关于单个集合的。两者收下的都是一条序数的性质、它的最小阶段，以及在那个阶段之下雕出的一个见证，而两者的结论都是「最小阶段是后继」；故那个论证只在那边写一遍，而本章是它的第二个实例。

此处的那条性质，就是塔中光秃秃的隶属，而它是两者中**较简单**的一个。一格是被**某个**成员相交的，故选取阶段那一章要先剥掉一层截断，才交得出论证所要的见证；而一个集合就是它自己的见证，无可剥。那边的施用十一行，此处的施用四行。本章从前所声称的「同一论证逐字适用于单个集合」，这话对分情形与雕出而言为真，对接口而言为假：它所点名的那次复用，在论证本身被写成架在性质之上以前，从来就不存在。

跨过边界的只有两个名字，再无其他。`carveAt`{.Agda} 把该集合从它的最早阶段中读出，并把那次雕出改名为一个后继，而 `predOf`{.Agda} 把它变成前一阶段，途中按极小性反驳低的那一支。里面的分情形依然是乔装的比较，写成写明结论的具名辅助件，只是如今写在一处，而不是两处。
<!--/-->

```agda
theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = predOf (λ σ → x ∈ˢ Lset σ) (stage x p) (stage-ord x p)
  (stage-earliest x p)
  (carveAt (λ σ → x ∈ˢ Lset σ) (stage x p) x (stage-mem x p) (λ δ hz → hz))

opaque
  birth : (x : S) → ⟨ isL x ⟩ → S
  birth x p = theCarve x p .fst

opaque
  unfolding birth
  birth-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (birth x p)
  birth-ord x p = theCarve x p .snd .fst

  birth-suc : (x : S) (p : ⟨ isL x ⟩) → sucV (birth x p) ≡ stage x p
  birth-suc x p = theCarve x p .snd .snd
```

<!--en-->
The ordinal so extracted is the set's **birth**: the stage `x` is carved over,
one below the earliest stage containing it. It is sealed exactly as
`stage`{.Agda} and `defStage`{.Agda} were, and for the same reason: it unfolds to
a well-founded descent through the tower, and every later type mentioning it
would drag that descent into conversion.

Two readings open the seal and nothing else does: the birth is an ordinal, and
its successor is the earliest stage. Everything the chapter uses is derived from
those two without opening anything. The set is a member of the stage just above
its birth, which is where the naming chapter looks for it. The birth does not
depend on which proof of constructibility is supplied, because constructibility
is a proposition. And a member of a stage is born strictly below that stage:
its earliest stage is below the stage or equal to it, and its birth is below its
earliest stage, so ordinal trichotomy settles the three cases, again in a named
helper with its conclusion written down.
<!--zh-->
如此取出的那个序数，就是该集合的**诞生阶段**：`x` 据以被雕出的那个阶段，比包含它的最早阶段低一级。它按 `stage`{.Agda} 与 `defStage`{.Agda} 当初那样封印，理由相同：它展开是一次穿过那座塔的良基下降，而此后每个提到它的类型都会把那次下降拖进转换检查。

有两条读式开封，别无其他：诞生阶段是序数；它的后继是最早阶段。本章所用的一切都由这两条推出，不再开封任何东西。该集合是它诞生阶段之上一级那个阶段的成员，而命名那一章正是在那里找它。诞生阶段不依赖于所供给的是哪一份可构造性证明，因为可构造性是命题。以及，一个阶段的成员诞生于严格更低处：它的最早阶段或低于该阶段、或与之相等，而它的诞生阶段低于它的最早阶段，故序数三歧了结这三种情形，同样写在一个写明结论的具名辅助件里。
<!--/-->

```agda
birth-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (sucV (birth x p)) ⟩
birth-mem x p =
  subst (λ w → ⟨ x ∈ˢ Lset w ⟩) (sym (birth-suc x p)) (stage-mem x p)

birth-stage : (x : S) (p : ⟨ isL x ⟩) → ⟨ birth x p ∈ˢ stage x p ⟩
birth-stage x p =
  subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (birth-suc x p) (self∈sucV (birth x p))

birth-proof : (x : S) (p q : ⟨ isL x ⟩) → birth x p ≡ birth x q
birth-proof x p q = cong (birth x) (snd (isL x) p q)

private
  decideIn : (γ x : S) → IsOrd γ → (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
           → ⟨ γ ∈ˢ stage x p ⟩ ⊎ ((γ ≡ stage x p) ⊎ ⟨ stage x p ∈ˢ γ ⟩)
           → ⟨ birth x p ∈ˢ γ ⟩
  decideIn γ x ordγ p h (inl γ∈) = Empty.rec (stage-earliest x p γ ordγ h γ∈)
  decideIn γ x ordγ p h (inr (inl e)) =
    subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (sym e) (birth-stage x p)
  decideIn γ x ordγ p h (inr (inr s∈)) = ordγ .fst (birth-stage x p) s∈

birth-in : (γ : S) → IsOrd γ → (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
         → ⟨ birth x p ∈ˢ γ ⟩
birth-in γ ordγ x p h =
  decideIn γ x ordγ p h (ord-tri γ ordγ (stage x p) (stage-ord x p))
```

<!--en-->
## Moving a well-order along an injection
<!--zh-->
## 沿一个单射搬运良序
<!--/-->

<!--en-->
Three times in this chapter a well-order is known on one type and wanted on
another that injects into it. The order is the comparison of the images.
Trichotomy is the source's trichotomy, with injectivity turning its middle case
back into an equality; irreflexivity and transitivity are read off; and
well-foundedness descends, because a descent of images is a descent.

The whole transfer is four lines, written once, in the shape its three uses
share. It is not a theory of induced orders, and in particular nothing here is
generic in a family of orders indexed by a first key: such a thing would have to
carry that family and prove its laws in that generality, which is a larger
theorem than any this chapter wants.

Two abbreviations travel with the transfer. `Mem A`{.Agda} is a set's members as
pairs of a set with its membership, the shape everything below is stated at; and
`relOf`{.Agda} reads a bundle's comparison out as a function, which is how an
order is passed around as a value rather than opened.
<!--zh-->
本章有三处，是某个类型上的良序已知，而想要的是另一个单射进它的类型上的良序。序就是对像的比较。三歧取源头的三歧，由单射性把它中间那一情形变回相等；非自反与传递直接读出；良基性则向下传递，因为一串像的下降就是一次下降。

整个搬运四行，写一遍，取的是它三处用法共有的形状。它不是一套「诱导序」的理论，尤其此处没有任何东西是对「以第一个键为索引的一族序」泛型的：那样一件东西得携带那一族并在那种一般性下证出它的诸定律，而这比本章所要的任何定理都大。

有两样缩写随这次搬运同行。`Mem A`{.Agda} 是一个集合的诸成员，取「集合连同它的隶属」之对的形式，而以下一切都陈述在这个形状上；`relOf`{.Agda} 则把一个束的比较当作函数读出来，于是一个序可以作为值传递，而不必被打开。
<!--/-->

```agda
Mem : S → Type (ℓ-suc ℓ)
Mem A = Σ[ x ∈ S ] ⟨ x ∈ˢ A ⟩

module _ {ℓc : Level} {A : Type ℓc} (w : SWO A) where
  open SWO w using () renaming ( _<∙_ to _<ʷ_ )

  relOf : A → A → Type (ℓ-suc ℓ)
  relOf a b = a <ʷ b

module _ {ℓb ℓc : Level} (B : Type ℓb) (C : Type ℓc) (w : SWO C)
         (f : B → C) (finj : (u v : B) → f u ≡ f v → u ≡ v) where
  open SWO w using () renaming
    ( _<∙_ to _<ᶜ_ ; tri∙ to triᶜ ; irr∙ to irrᶜ
    ; trans∙ to transᶜ ; wf∙ to wfᶜ )

  private
    _<ᵇ_ : B → B → Type (ℓ-suc ℓ)
    u <ᵇ v = f u <ᶜ f v

    pullTri : (u v : B) → Tri (u <ᵇ v) (u ≡ v) (v <ᵇ u)
    pullTri u v = Tri-map id (finj u v) id (triᶜ (f u) (f v))

    pullAcc : (u : B) → Acc _<ᶜ_ (f u) → Acc _<ᵇ_ u
    pullAcc u (acc r) = acc (λ v h → pullAcc v (r (f v) h))

  pullOrder : SWO B
  pullOrder = record
    { _<∙_   = _<ᵇ_
    ; tri∙   = pullTri
    ; irr∙   = λ u h → irrᶜ (f u) h
    ; trans∙ = λ u v z → transᶜ (f u) (f v) (f z)
    ; wf∙    = λ u → pullAcc u (wfᶜ (f u)) }
```

<!--en-->
The first use is the canonical presentation of a set. A set's members come in two
shapes: as pairs of a set with a proof that it belongs, which is the shape the
construction below produces, and as the small index type the hierarchy presents
the set by, which is the shape the naming chapter takes. The index map is an
embedding, so moving an order from the first shape to the second is one
application of the transfer, done here and not again.

The second use is an inclusion. When every member of one set is a member of
another, an order on the second restricts to the first, and the injection is the
identity on the underlying sets.
<!--zh-->
第一处用法是一个集合的典范表示。集合的成员有两种形状：一种是「集合连同它属于该集合的证明」之对，这是下面的构造所产出的形状；另一种是层级用来表示该集合的那个小索引类型，这是命名那一章所取用的形状。索引映射是嵌入，故把一个序从第一种形状搬到第二种，就是那次搬运的一次施用，此处做一遍，不再重做。

第二处用法是包含。当一个集合的每个成员都是另一个集合的成员时，第二个集合上的序限制到第一个上，而那个单射在底下的集合上是恒等的。
<!--/-->

```agda
memOf : (A : S) (m : ⟪ A ⟫) → ⟨ ⟪ A ⟫↪ m ∈ˢ A ⟩
memOf A m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)

carry : (A : S) → SWO (Mem A) → SWO ⟪ A ⟫
carry A w = pullOrder ⟪ A ⟫ (Mem A) w (λ m → ⟪ A ⟫↪ m , memOf A m) inj
  where
  inj : (u v : ⟪ A ⟫)
      → _≡_ {A = Mem A} (⟪ A ⟫↪ u , memOf A u) (⟪ A ⟫↪ v , memOf A v) → u ≡ v
  inj u v q = isEmbedding→Inj isEmb⟪ A ⟫↪ u v (cong fst q)

```

<!--en-->
## The step
<!--zh-->
## 步进
<!--/-->

<!--en-->
The step is the chapter's first deliverable: from a well-order of the members of
`Lset δ`{.Agda}, a well-order of the members of `Lset (sucV δ)`{.Agda}, written
`New δ`{.Agda} below, which is to say of the definable subsets of
`Lset δ`{.Agda}.

It has one branch, and it was written with two. Below the limit stage the
members are already ordered, by the finite chapter's well-order of
`Lset ω`{.Agda}, which is also the order a name's first key is compared by; so a
first draft took that order there and the names only above. **Measured, the
second branch is surplus**: taking the names everywhere checks in the same three
seconds. What the guard was actually contributing was not a case distinction but
a **normalization barrier**, since a decision by the excluded middle is stuck
while the excluded middle is a module parameter, and being stuck is what stops
this order from unfolding into the naming chapter's. The `opaque`{.Agda} seal is
that barrier, said in one word, and it is why the definition below is one line.

The reason the first draft gave, that the book should not carry two unrelated
well-orders of one set, was a coherence claim, and this chapter never proved it.
Kept code needs a better warrant than an argument nobody discharged, so the
branch is gone and the claim with it. The base case needs nothing either: the
first stage is empty, so its members are well-ordered for want of any.
<!--zh-->
步进是本章的第一件交付物：由 `Lset δ`{.Agda} 诸成员上的一个良序，得出 `Lset (sucV δ)`{.Agda} 诸成员上的一个良序 (下文记作 `New δ`{.Agda})，也就是 `Lset δ`{.Agda} 的诸可定义子集上的良序。

它只有一支，而当初写成了两支。极限阶段以下诸成员本已有序，即有穷那一章为 `Lset ω`{.Agda} 造的良序，而那也正是一个名字的第一个键据以比较的序；故初稿在那里取那个序，只在极限阶段之上才动用名字。**实测下来，第二支是多余的**：处处取名字，同样三秒检查完毕。那个守卫真正贡献的并不是一次情形区分，而是一道**归一化屏障**：排中律尚是模块参数时，据它作出的判定是卡住的，而正是「卡住」阻止了这个序展开成命名那一章的序。`opaque`{.Agda} 封印就是那道屏障，一个词说完，这也是下面那条定义只有一行的原因。

初稿给出的理由，即本书不该为同一个集合携带两个互不相干的良序，是一条相干性主张，而本章从未证明它。留住代码所需的正当理由，要强过一个无人交付的论证，故那一支已删，那条主张随之。基础情形也无须任何东西：第一个阶段是空的，其诸成员因无可比较而良序。
<!--/-->

```agda
New : S → Type (ℓ-suc ℓ)
New δ = Mem (Lset (sucV δ))

```

<!--en-->
The other branch compares by **least name**. Every member of
`Lset (sucV δ)`{.Agda} is denoted by some name, truncated, which is how the
definable powerset gives up a formula; the names carry a well-order as soon as
the stage below carries one, which is exactly the hypothesis of this step; so the
least name denoting a set is a definite name, and each set is sent to it. That
map is injective because a name determines what it denotes, and the step order is
the name order pulled back along it.

Nothing about names is unpacked here. The naming data stay inside the chapter
whose telescope binds them, and this chapter sees a type carrying an order. That
is not fastidiousness: the previous chapter measured what happens when naming
data are reached from another module, and the answer was that every comparison of
codes forces the limit order open.
<!--zh-->
另一支按**最小名字**比较。`Lset (sucV δ)`{.Agda} 的每个成员都被某个名字指称，且是截断的，因为可定义幂集本来就是这样交出公式的；而只要下面那个阶段带有良序，诸名字就带有良序，那恰是本步进的假设；于是指称一个集合的最小名字是一个确定的名字，每个集合被送到它那里。那个映射是单射，因为名字决定它所指称的东西，而步进的序就是名字的序沿它拉回。

此处没有任何关于名字的东西被拆开。命名数据留在绑定它们的那条模块序列所在的章内，而本章看到的是一个带序的类型。这不是讲究：上一章量过「命名数据从另一个模块够取」会发生什么，答案是每一次码的比较都会把极限序逼开。
<!--/-->

```agda
module _ (δ : S) (w : SWO ⟪ Lset δ ⟫) where
  private
    module NM = Naming (Lset δ) w

  denotesAt : S → NM.Name → hProp (ℓ-suc ℓ)
  denotesAt x n = (NM.denote n ≡ x) , setIsSet (NM.denote n) x

  private
    denotes : New δ → NM.Name → hProp (ℓ-suc ℓ)
    denotes a = denotesAt (a .fst)

    hasName : (a : New δ) → ∥ Σ[ n ∈ NM.Name ] ⟨ denotes a n ⟩ ∥₁
    hasName a = NM.names-complete (a .fst)
      (subst (λ v → ⟨ a .fst ∈ˢ v ⟩) (Lset-suc δ) (a .snd))

    leastOfNew : (a : New δ)
               → Σ[ n ∈ NM.Name ] IsLeast NM.nameOrder (denotes a) n
    leastOfNew a = NM.leastName (denotes a) (hasName a)

    theName : New δ → NM.Name
    theName a = leastOfNew a .fst

    theName-denote : (a : New δ) → NM.denote (theName a) ≡ a .fst
    theName-denote a = leastOfNew a .snd .fst

    nameInj : (u v : New δ) → theName u ≡ theName v → u ≡ v
    nameInj u v q = Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV δ)))
      (sym (theName-denote u) ∙ cong NM.denote q ∙ theName-denote v)

  byName : SWO (New δ)
  byName = pullOrder (New δ) NM.Name NM.nameOrder theName nameInj
```

<!--en-->
Three definitions leave the module, and they are the least a caller can be given
and still say what this order is. `denotesAt`{.Agda} is the family the search is
run at, a set's names; `IsLeastName`{.Agda} is being a least name of a set, and
it is the well-order chapter's `IsLeast`{.Agda} **at that family**, not a
re-spelling of it; `leastNameOf`{.Agda} exhibits one for every member of the new
stage, and it is the search itself, returned.

That `IsLeastName`{.Agda} is a definition and not a re-spelling is a measurement.
Written out as a pair of a denotation equation and a minimality clause, the
search would have to be converted into it at a **computed** name, and a
comparison of names at a computed name unfolds the code order down to the level
search it is defined by: 16 s for that one line, against nothing when the
property is the family's own `IsLeast`{.Agda}. The naming data still stay inside;
what crosses the boundary is a name the caller already holds.
<!--zh-->
有三个定义离开本模块，而它们是「要说清这个序是什么，调用方最少须被给予的东西」。`denotesAt`{.Agda} 是那场搜寻所针对的那一族，即一个集合的诸名字；`IsLeastName`{.Agda} 是「是某个集合的一个最小名字」，而它就是良序那一章的 `IsLeast`{.Agda} **架在那一族上**，不是它的另一种写法；`leastNameOf`{.Agda} 为新阶段的每个成员当场拿出一个，而它就是那场搜寻本身，原样交回。

`IsLeastName`{.Agda} 是一个定义、而不是一次重写，这是量出来的。若写成「一条指称等式加一条极小性子句」之对，那场搜寻就得在一个**算出来的**名字处被转换成它，而在算出来的名字处比较名字，会把码之序展开到它据以定义的那场层号搜寻：仅那一行 16 秒，而当那条性质就是那一族自家的 `IsLeast`{.Agda} 时，分文不花。命名数据仍然留在里面；跨过边界的是一个调用方早已持有的名字。
<!--/-->

```agda
  IsLeastName : NM.Name → S → Type (ℓ-suc ℓ)
  IsLeastName t x = IsLeast NM.nameOrder (denotesAt x) t

  leastNameOf : (a : New δ) → Σ[ t ∈ NM.Name ] IsLeastName t (fst a)
  leastNameOf a = leastOfNew a

  private
    pin : (c : New δ) (t : NM.Name) → IsLeastName t (fst c) → theName c ≡ t
    pin c t h = cong fst
      (isPropLeastOf NM.nameOrder (denotes c) (leastOfNew c) (t , h))

    byName-least : (a b : New δ) (t₁ t₂ : NM.Name)
                 → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                 → relOf byName a b ≡ NM._≺ₙ_ t₁ t₂
    byName-least a b t₁ t₂ h₁ h₂ = cong₂ NM._≺ₙ_ (pin a t₁ h₁) (pin b t₂ h₂)

```

<!--en-->
The two branches are joined by the excluded middle, in a named helper whose
conclusion is written out rather than inferred. This is the only place the
chapter spends the assumption itself; everywhere else it arrives already spent,
inside the trichotomy of ordinals, inside the earliest stage, and inside the
search for a least name.
<!--zh-->
两支由排中律接起来，写在一个写明结论、而非留待推断的具名辅助件里。这是本章唯一一处自己花掉那条假设之处；其余各处它到场时都已被花掉，花在序数的三歧里、最早阶段里，以及寻找最小名字的搜索里。
<!--/-->

```agda
  opaque
    stepAt : SWO (New δ)
    stepAt = byName
```

<!--en-->
The seal is a normalization barrier and not a secret, so two readings are let
through it, one each way: the step relates two members exactly when the name
order relates any two names the caller has shown least. They are the equation
above, transported.

They are proved **here**, inside the telescope that binds the stage and its
order, and that placement is a measurement too. Stated at top level and filled
with the very lemma above, either reading costs 39 s, which is law 20's shape met
at a new place: a statement whose type is written down and whose filling is the
same statement forces a conversion this route cannot afford. Inside, where the
seal is, both are free.
<!--zh-->
那道封印是一道归一化屏障、不是一个秘密，故有两条读式被放行，一个方向一条：那一步关联两个成员，当且仅当名字之序关联「调用方已证为最小的任意两个名字」。它们就是上面那条等式，搬运过来。

它们证在**此处**，即绑定阶段与其序的那条模块序列之内，而这个位置同样是量出来的。若陈述在顶层、再拿上面那条引理去填，任一条读式要花 39 秒，而这正是第 20 条定律在新地方的形状：一条把类型写下来、又用同一条陈述去填的陈述，会逼出一次这条路线付不起的转换。在里面，在封印所在之处，两条都分文不花。
<!--/-->

```agda
  opaque
    unfolding stepAt

    stepAt-fill : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → NM._≺ₙ_ t₁ t₂ → relOf stepAt a b
    stepAt-fill a b t₁ t₂ h₁ h₂ =
      transport (sym (byName-least a b t₁ t₂ h₁ h₂))

    stepAt-read : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → relOf stepAt a b → NM._≺ₙ_ t₁ t₂
    stepAt-read a b t₁ t₂ h₁ h₂ =
      transport (byName-least a b t₁ t₂ h₁ h₂)
```

<!--en-->
## The family
<!--zh-->
## 族
<!--/-->

<!--en-->
One piece of vocabulary comes first. The step order at a birth has to be applied
to two sets that are members of the stage just above that birth, and the
membership proofs are in the way: they are what makes the two sets members, they
are propositions, and they arrive differently at each occurrence. So the
comparison is stated between two **sets**, with the two memberships quantified
inside it, and the ordinal is an explicit argument of the statement.

That shape is what lets an equality of births move a whole comparison from one
birth to another in a single transport, which is the recurring move of the proofs
below; and `under-at`{.Agda} reads the comparison back out at any chosen pair of
proofs, which is the only bookkeeping the quantification costs.
<!--zh-->
先立一样词汇。诞生阶段处的步进序，要施用于两个集合，它们都是该诞生阶段之上一级那个阶段的成员，而隶属证明碍事：正是它们使那两个集合成为成员，它们是命题，且每次出现时到场的方式都不同。于是这次比较陈述在两个**集合**之间，两条隶属被量化在它里面，而那个序数是该陈述的显式实参。

正是这个形状，使一条诞生阶段的等式能以单次搬运把整条比较从一个诞生阶段挪到另一个，而这也是下文诸证明反复用到的动作；`under-at`{.Agda} 则在任选的一对证明处把那条比较读回来，而这就是那次量化所花的全部记账。
<!--/-->

```agda
Under : (δ : S) → SWO (New δ) → S → S → Type (ℓ-suc ℓ)
Under δ v x y = Σ[ hx ∈ ⟨ x ∈ˢ Lset (sucV δ) ⟩ ]
                Σ[ hy ∈ ⟨ y ∈ˢ Lset (sucV δ) ⟩ ]
                relOf v (x , hx) (y , hy)

under-at : (δ : S) (v : SWO (New δ)) (x y : S)
           (hx : ⟨ x ∈ˢ Lset (sucV δ) ⟩) (hy : ⟨ y ∈ˢ Lset (sucV δ) ⟩)
         → Under δ v x y → relOf v (x , hx) (y , hy)
under-at δ v x y hx hy (kx , ky , h) =
  subst2 (λ p q → relOf v (x , p) (y , q))
    (snd (x ∈ˢ Lset (sucV δ)) kx hx) (snd (y ∈ˢ Lset (sucV δ)) ky hy) h
```

<!--en-->
The induction's step takes the orders at every ordinal below `γ` and produces one
at `γ`. Each member of `Lset γ`{.Agda} is constructible, because `γ` is an
ordinal, so it has a birth; and that birth is a member of `γ`. Packaging the
birth with that membership gives exactly the datum the induction hypothesis can
be applied at, and `stepIn`{.Agda} is the step order there.

The comparison is then the two-key one: births first, and, when the births agree,
the step order at the common birth. The equality of births is carried in the
direction that lets the second set be read at the first's birth, which keeps the
definition free of a transport; and it is carried as an equality of **ordinals**
rather than of the packaged pairs. The packaged form is recovered where the transports
want it, since the membership is a proposition.
<!--zh-->
归纳的这一步，收下 `γ` 以下每个序数处的序，产出 `γ` 处的一个。`Lset γ`{.Agda} 的每个成员都可构造，因为 `γ` 是序数，故它有诞生阶段；而那个诞生阶段是 `γ` 的成员。把诞生阶段与那条隶属打成包，得到的恰是归纳假设可以施用其上的那个数据，而 `stepIn`{.Agda} 就是那里的步进序。

于是比较是两个键的：先诞生阶段，若诞生阶段相符，则用共同诞生阶段处的步进序。诞生阶段的等式所携带的方向，使第二个集合可以在第一个的诞生阶段处读出，这让定义中不出现搬运；而它携带的是**序数**之间的等式、不是打包之对之间的等式。打包的形式在诸搬运需要它的地方现取，因为那条隶属是命题。
<!--/-->

```agda
module Family (γ : S)
              (IH : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
              (ordγ : IsOrd γ) where
  private
    Member : Type (ℓ-suc ℓ)
    Member = Mem (Lset γ)

    memberL : (a : Member) → ⟨ isL (a .fst) ⟩
    memberL a = Lset→isL γ ordγ (a .fst) (a .snd)

    newIn : (a : Member) → ⟨ a .fst ∈ˢ Lset (sucV (birth (a .fst) (memberL a))) ⟩
    newIn a = birth-mem (a .fst) (memberL a)

  bornAt : Member → Mem γ
  bornAt a = birth (a .fst) (memberL a)
           , birth-in γ ordγ (a .fst) (memberL a) (a .snd)

  stepIn : (d : Mem γ) → SWO (New (d .fst))
  stepIn d = stepAt (d .fst) (carry (Lset (d .fst))
    (IH (d .fst) (d .snd) (mem-ord {A = γ} ordγ (d .fst) (d .snd))))

  UnderAt : (d : Mem γ) → Member → Member → Type (ℓ-suc ℓ)
  UnderAt d a b = Under (d .fst) (stepIn d) (a .fst) (b .fst)

  _≺_ : Member → Member → Type (ℓ-suc ℓ)
  a ≺ b = ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
        ⊎ ((bornAt b .fst ≡ bornAt a .fst) × UnderAt (bornAt a) a b)

  private
    packBirth : (d z : Mem γ) → d .fst ≡ z .fst → d ≡ z
    packBirth d z = Σ≡Prop (λ v → snd (v ∈ˢ γ))
```

<!--en-->
Irreflexivity is the two keys' own: no ordinal belongs to itself, and no step
order puts a set below itself. Transitivity is four cases, of which the two mixed
ones carry an equality of births across a membership, and the last composes two
comparisons at one birth after moving the second one there.

Trichotomy descends the keys, each reached only when the previous one has
pronounced equality: the ordinals first, the step order second. Both splits are
named helpers with their conclusion written down. That is the discipline the
previous two chapters paid for and this one inherits: a split whose branches
conclude in a membership proposition, left to a `with`{.Agda} or to inference, is
solved against the whole disjunction rather than against its own branch.
<!--zh-->
非自反是两个键各自的：没有序数属于自身，也没有哪个步进序把一个集合排在它自己之下。传递是四种情形，其中两种混合情形把一条诞生阶段的等式带过一条隶属，最后一种在把第二条比较挪到同一个诞生阶段之后，把两条比较复合起来。

三歧沿诸键下行，每一个唯有在前一个宣布相等时才被抵达：先序数，后步进序。两次分情形都是写明结论的具名辅助件。这是前两章付过学费、本章继承下来的纪律：分支结论落在隶属命题上的分情形，若交给 `with`{.Agda} 或交给推断，就会对着整个析取、而不是对着它自己那一支求解。
<!--/-->

```agda
  private
    ≺-irr : (a : Member) → a ≺ a → Empty.⊥
    ≺-irr a (inl h) = ∈-irrefl (bornAt a .fst) h
    ≺-irr a (inr (_ , u)) =
      SWO.irr∙ (stepIn (bornAt a)) (a .fst , newIn a)
        (under-at (bornAt a .fst) (stepIn (bornAt a)) (a .fst) (a .fst)
          (newIn a) (newIn a) u)

    ≺-trans : (a b c : Member) → a ≺ b → b ≺ c → a ≺ c
    ≺-trans a b c (inl h) (inl k) =
      inl (birth-ord (c .fst) (memberL c) .fst h k)
    ≺-trans a b c (inl h) (inr (e , _)) =
      inl (subst (λ v → ⟨ bornAt a .fst ∈ˢ v ⟩) (sym e) h)
    ≺-trans a b c (inr (e , _)) (inl k) =
      inl (subst (λ v → ⟨ v ∈ˢ bornAt c .fst ⟩) e k)
    ≺-trans a b c (inr (e , u)) (inr (eb , v)) = inr (eb ∙ e , joined)
      where
      d : Mem γ
      d = bornAt a
      moved : UnderAt d b c
      moved = subst (λ z → UnderAt z b c) (packBirth (bornAt b) d e) v
      joined : UnderAt d a c
      joined = u .fst , (moved .snd .fst
        , SWO.trans∙ (stepIn d) (a .fst , u .fst) (b .fst , moved .fst)
            (c .fst , moved .snd .fst)
            (under-at (d .fst) (stepIn d) (a .fst) (b .fst)
              (u .fst) (moved .fst) u)
            (under-at (d .fst) (stepIn d) (b .fst) (c .fst)
              (moved .fst) (moved .snd .fst) moved))

    ≺-tri : (a b : Member) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    ≺-tri a b = byBirth (ord-tri (bornAt a .fst) (birth-ord (a .fst) (memberL a))
                                 (bornAt b .fst) (birth-ord (b .fst) (memberL b)))
      where
      byBirth : ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
              ⊎ ((bornAt a .fst ≡ bornAt b .fst) ⊎ ⟨ bornAt b .fst ∈ˢ bornAt a .fst ⟩)
              → Tri (a ≺ b) (a ≡ b) (b ≺ a)
      byBirth (inl h)       = lt (inl h)
      byBirth (inr (inr h)) = gt (inl h)
      byBirth (inr (inl e)) =
        bySteps (SWO.tri∙ (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
        where
        same : bornAt b .fst ≡ bornAt a .fst
        same = sym e
        ha : ⟨ a .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
        ha = newIn a
        hb : ⟨ b .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
        hb = subst (λ v → ⟨ b .fst ∈ˢ Lset (sucV v) ⟩) (sym e) (newIn b)
        bySteps : Tri (relOf (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
                      ((a .fst , ha) ≡ (b .fst , hb))
                      (relOf (stepIn (bornAt a)) (b .fst , hb) (a .fst , ha))
                → Tri (a ≺ b) (a ≡ b) (b ≺ a)
        bySteps (lt h) = lt (inr (same , (ha , hb , h)))
        bySteps (eq q) = eq (Σ≡Prop (λ v → snd (v ∈ˢ Lset γ)) (cong fst q))
        bySteps (gt h) = gt (inr (sym same
          , subst (λ z → UnderAt z b a)
              (packBirth (bornAt a) (bornAt b) (sym same)) (hb , ha , h)))
```

<!--en-->
Well-foundedness is two nested inductions, kept apart exactly as the finite
chapter kept its own two apart. The outer one is membership induction on the
birth, and it hands down a hypothesis covering every earlier birth; the inner one
is an ordinary descent along the accessibility the step order already has at that
birth. A step down in birth appeals to the outer hypothesis, a step within a
birth to the inner one, and since the inner function recurses on nothing but its
own accessibility argument the two never have to be compared.

The member always arrives as a member, with an equation saying where its birth
sits. That is the same law as the trichotomy's, met again from the other side: an
accessibility stated at a member's components would have to be matched against
one stated at the member.
<!--zh-->
良基性是两层嵌套的归纳，其分开的方式与有穷那一章把它自己那两层分开的方式完全相同。外层是对诞生阶段的成员归纳，它交下一个覆盖所有更早诞生阶段的假设；内层则是沿步进序在那个诞生阶段处本已具备的可及性作普通下降。降一个诞生阶段的一步诉诸外层假设，诞生阶段之内的一步诉诸内层假设，而由于内层函数除自己的可及性实参外不沿任何东西递归，二者从不需要放在一起比较。

成员总是以成员的身份到场，外加一条说明它的诞生阶段坐在哪里的等式。这与三歧那一条是同一条规矩，此番从另一侧再度出现：陈述在一个成员的诸分量上的可及性，将不得不与陈述在那个成员上的可及性对上。
<!--/-->

```agda
  private
    accInside : (d : Mem γ)
              → ((z : Mem γ) → ⟨ z .fst ∈ˢ d .fst ⟩
                 → (b : Member) → bornAt b ≡ z → Acc _≺_ b)
              → (u : New (d .fst)) → Acc (relOf (stepIn d)) u
              → (b : Member) → bornAt b ≡ d → b .fst ≡ u .fst → Acc _≺_ b
    accInside d ih u (acc r) b q qu = acc step
      where
      step : (c : Member) → c ≺ b → Acc _≺_ c
      step c (inl h) = ih (bornAt c)
        (subst (λ v → ⟨ bornAt c .fst ∈ˢ v ⟩) (cong fst q) h) c refl
      step c (inr (eb , v)) =
        accInside d ih (c .fst , hc) (r (c .fst , hc) below) c qc refl
        where
        qc : bornAt c ≡ d
        qc = packBirth (bornAt c) d (sym eb ∙ cong fst q)
        moved : UnderAt d c b
        moved = subst (λ z → UnderAt z c b) qc v
        hc : ⟨ c .fst ∈ˢ Lset (sucV (d .fst)) ⟩
        hc = moved .fst
        below : relOf (stepIn d) (c .fst , hc) u
        below = subst (λ z → relOf (stepIn d) (c .fst , hc) z)
          (Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV (d .fst)))) qu)
          (under-at (d .fst) (stepIn d) (c .fst) (b .fst)
            hc (moved .snd .fst) moved)

    accByBirth : (δ : S) (i : ⟨ δ ∈ˢ γ ⟩)
               → (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
    accByBirth = ∈-induction {P = Motive} outer
      where
      Motive : S → Type (ℓ-suc ℓ)
      Motive δ = (i : ⟨ δ ∈ˢ γ ⟩) (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
      outer : (δ : S) → ((z : S) → ⟨ z ∈ˢ δ ⟩ → Motive z) → Motive δ
      outer δ ih i b q = accInside (δ , i) inner (b .fst , hb)
        (SWO.wf∙ (stepIn (δ , i)) (b .fst , hb)) b q refl
        where
        hb : ⟨ b .fst ∈ˢ Lset (sucV δ) ⟩
        hb = subst (λ z → ⟨ b .fst ∈ˢ Lset (sucV (z .fst)) ⟩) q (newIn b)
        inner : (z : Mem γ) → ⟨ z .fst ∈ˢ δ ⟩
              → (c : Member) → bornAt c ≡ z → Acc _≺_ c
        inner z h c qz = ih (z .fst) h (z .snd) c qz

    ≺-wf : WellFounded _≺_
    ≺-wf a = accByBirth (bornAt a .fst) (bornAt a .snd) a refl

  famOrder : SWO (Mem (Lset γ))
  famOrder = record
    { _<∙_   = _≺_
    ; tri∙   = ≺-tri
    ; irr∙   = ≺-irr
    ; trans∙ = ≺-trans
    ; wf∙    = ≺-wf }
```

<!--en-->
The family is that step run by membership induction, and it is sealed. Unsealed,
an order at a stage unfolds into a recursion over the whole hierarchy, and every
type mentioning one would carry that unfolding into conversion;
`orderAt-step`{.Agda} opens the seal once, on the recursion equation alone, for
the two chapters that unfold it, `L.Choice.Faithful`{.Agda} and
`L.GCH.StageCount`{.Agda}. `stageOrder`{.Agda} is the same
order at the presentation the naming chapter takes, and it is what the argument
ahead will hand to `leastName`{.Agda}.
<!--zh-->
这一族就是那一步沿成员归纳跑出来的东西，而它被封印。不封印的话，一个阶段处的序会展开成一场遍历整座层级的递归，而每个提到某个这样的序的类型都会把那次展开带进转换检查；`orderAt-step`{.Agda} 开封一次，且只为那条递归方程，供展开它的两章使用：`L.Choice.Faithful`{.Agda} 与 `L.GCH.StageCount`{.Agda}。`stageOrder`{.Agda} 是同一个序，取在命名那一章所用的那种表示上，而它正是后续论证将要递给 `leastName`{.Agda} 的东西。
<!--/-->

```agda
famStep : (γ : S) → ((δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
        → IsOrd γ → SWO (Mem (Lset γ))
famStep = Family.famOrder

opaque
  orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))
  orderAt = ∈-induction famStep

opaque
  unfolding orderAt
  orderAt-step : (γ : S) → orderAt γ ≡ famStep γ (λ δ _ → orderAt δ)
  orderAt-step = ∈-induction-compute famStep

stageOrder : (γ : S) → IsOrd γ → SWO ⟪ Lset γ ⟫
stageOrder γ oγ = carry (Lset γ) (orderAt γ oγ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`birth`{.Agda} is the ordinal a constructible set is carved over, one below the
earliest stage containing it, and it exists because a set enters the tower only
by being carved out. `theCarve`{.Agda} is that extraction, and it is the
choice-stage chapter's `carveAt`{.Agda} and `predOf`{.Agda} applied at plain
membership in the tower: the simpler of the operator's two instances, four lines
here against eleven there, because nothing has to be brought out of a truncation
first. `birth-in`{.Agda} places it strictly below any stage the set belongs to,
and `birth-proof`{.Agda} says it does not depend on the constructibility proof
supplied.

`stepAt`{.Agda} is the step: a well-order of `Lset (sucV δ)`{.Agda} out of one of
`Lset δ`{.Agda}, at every stage by the previous chapter's name order pulled back
along **least name**, which is a function because the names are well-ordered as
soon as the stage below is. It was written with a second branch below the limit
stage and that branch was measured surplus and deleted; the body says why.
`pullOrder`{.Agda} moves a well-order along an injection and is the only transfer
written; the step uses it, and so does `carry`{.Agda}, which presents a stage's
members as the index type the naming chapter takes.

Three definitions say what that pulled-back order is, for a caller outside:
`denotesAt`{.Agda} is a set's names, `IsLeastName`{.Agda} is the well-order
chapter's `IsLeast`{.Agda} at that family, and `leastNameOf`{.Agda} is the search.
`stepAt-fill`{.Agda} and `stepAt-read`{.Agda} then read the step both ways
against the name order, at any two names the caller has shown least. Two
measurements sit behind those five lines: the property must be the family's own
`IsLeast`{.Agda} and never a re-spelling of it (16 s against nothing, because a
comparison at a computed name opens the code order), and both readings must be
proved inside the telescope the seal lives in and never restated at top level
(39 s each against nothing, which is law 20 at a new place).

`orderAt`{.Agda} is the family: at every ordinal, a strict well-order of that
stage's members, all four laws included, built by membership induction from the
orders below. Its comparison has the **birth as the primary key** and the step
order at a common birth as the secondary, and it never mentions the stage it is
read at.

What is now available is exactly the missing hypothesis of the previous chapter,
at every stage at once. The argument ahead takes the one stage the choice-stage
chapter singled out, hands `stageOrder`{.Agda} to the names written over it, and
picks the least name.
<!--zh-->
`birth`{.Agda} 是一个可构造集据以被雕出的那个序数，比包含它的最早阶段低一级；它之所以存在，是因为集合进入塔的唯一途径就是被雕出。`theCarve`{.Agda} 就是那次取出，而它是选取阶段那一章的 `carveAt`{.Agda} 与 `predOf`{.Agda} 施用在塔中光秃秃的隶属上：那个算子两个实例中较简单的一个，此处四行，那边十一行，因为此处无须先把什么从截断中取出来。`birth-in`{.Agda} 把它安置在该集合所属的任何阶段之下且严格更低，而 `birth-proof`{.Agda} 说它不依赖于所供给的那份可构造性证明。

`stepAt`{.Agda} 就是步进：由 `Lset δ`{.Agda} 上的一个良序造出 `Lset (sucV δ)`{.Agda} 上的一个，在**每一个**阶段处都是上一章的名字序沿**最小名字**拉回，而最小名字之所以是函数，是因为只要下面那个阶段已被良序化，诸名字就已被良序化。它当初写着「极限阶段以下另有一支」，而那一支被实测为多余并删去；正文说了为什么。`pullOrder`{.Agda} 沿一个单射搬运良序，是本章写下的唯一一次搬运；步进用它，`carry`{.Agda} 也用它，后者把一个阶段的诸成员呈现为命名那一章所取的索引类型。

有三个定义为外面的调用方说清那个拉回的序是什么：`denotesAt`{.Agda} 是一个集合的诸名字，`IsLeastName`{.Agda} 是良序那一章的 `IsLeast`{.Agda} 架在那一族上，而 `leastNameOf`{.Agda} 就是那场搜寻。随后 `stepAt-fill`{.Agda} 与 `stepAt-read`{.Agda} 两个方向地把那一步对着名字之序读出来，读在「调用方已证为最小的任意两个名字」处。这五行背后有两次实测：那条性质必须是那一族自家的 `IsLeast`{.Agda}、绝不可另写一遍 (16 秒对分文不花，因为在算出来的名字处的一次比较会把码之序打开)，而两条读式都必须证在封印所在的那条模块序列之内、绝不可在顶层重述 (各 39 秒对分文不花，这是第 20 条定律在新地方)。

`orderAt`{.Agda} 就是那一族：在每个序数处，该阶段诸成员上的一个严格良序，四条定律齐备，由下面诸序沿成员归纳造出。它的比较以**诞生阶段为主键**，以共同诞生阶段处的步进序为次键，而且从不提到它是在哪个阶段处被读的。

现在到手的，恰是上一章所缺的那个前提，且一举在每个阶段处到手。后续论证取选取阶段那一章单挑出来的那一个阶段，把 `stageOrder`{.Agda} 递给写在其上的诸名字，再挑出最小的名字。
<!--/-->
