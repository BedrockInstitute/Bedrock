# Satisfaction over the whole code set

<!--en-->
The first instance of this recursion, since retired, was indexed by
`slot B φ`{.Agda}, the keys of one formula and its subformulas. Nothing
downstream can use it. A consumer
arrives holding a **code**, not the formula the code came from: the internal
definable powerset ranges over the codes of arity one at a stage, and the
well-order compares two codes that are subcodes of no common formula. Indexed by
one formula's slot there is a table per formula, and "what does the table say at
this code" has no answer until someone produces a formula the code is a subcode
of.

The domain that answers is the code set at a stage, and the previous goal built
it. `AllCodes`{.Agda} holds the keys of the formulas over the carrier at *every*
arity, which is exactly what a consumer arrives holding.

Closedness of the whole code set is **not** what discharges the graph's demand on
an index set, and it is worth saying so, because that theorem is what the previous
goal was registered for. The graph binds its table and its index set
**existentially**, so `funct`{.Agda} owes only *some* qualifying set containing the
member, and the smallest one is the member's own formula's slot, closed by the
chapter that built it. Nothing anywhere consumed it, and it has since been
retired.

What the change costs is the whole content of this chapter, and it is almost
nothing, for a reason worth stating before any of it. The graph binds its table
**existentially**. So `funct`{.Agda} at a member does not have to exhibit a table
over the whole domain; it has to exhibit some closed, total, clause-satisfying
table holding that member, and the smallest such table is the subformula slot of
the member's own formula, which four earlier chapters already built and
certified. The recursion changes its domain and nothing else changes:
`Table`{.Agda}, `Slot`{.Agda}, `Sound`{.Agda} and `Unique`{.Agda} are untouched
statement for statement.

One thing here is genuinely new, and it is not about recursion at all. The code
set's members are keys taken in the **hierarchy's** coding over the stage's own
alphabet; everything the recursion speaks is keys taken in the **model's** coding
over the model's language. Those are the same construction at two alphabets, and
no theorem connected them.
<!--zh-->
这场递归的第一个实例以 `slot B φ`{.Agda} 为索引，即一条公式及其诸子公式的诸键，此后已予撤除。下游没有任何东西用得上它。消费方到场时手里握着的是一个**码**，而不是该码所出自的那条公式：内部可定义幂集在某阶段处元数一的诸码上取值，而良序要比较的两个码并非任何共同公式的子码。以一条公式的槽为索引，就是一条公式一张表，而「这张表在这个码处说什么」在有人拿出「该码是其子码」的某条公式之前，根本没有答案。

作答的那个定义域是某阶段处的码集，而上一个目标已经把它造好。`AllCodes`{.Agda} 持有载体之上诸公式在**每个**元数处的诸键，而那恰是消费方到场时手里握着的东西。

整个码集的封闭性**不是**打发图对索引集之要求的那个东西，而这件事值得说出来，因为那条定理正是上一个目标为之登记的。图把自己的表与索引集都作**存在**绑定，故 `funct`{.Agda} 只欠「**某个**装着该成员的合格集合」，而最小的那个就是该成员自己那条公式的槽，其封闭性由造出它的那一章给出。它在任何地方都不被消费，故此后已予撤除。

这次更换的代价就是本章的全部内容，而它几乎为零；理由值得在一切之前说明。那个图把自己的表**存在**绑定。故 `funct`{.Agda} 在一个成员处不必拿出一张覆盖整个定义域的表；它只需拿出「某张封闭、全的、满足诸子句的、装着该成员的表」，而最小的这样一张，就是该成员自己那条公式的子公式槽，而它已由前面四章造好并认证。这场递归换掉它的定义域，其余一概不变：`Table`{.Agda}、`Slot`{.Agda}、`Sound`{.Agda} 与 `Unique`{.Agda} 逐条陈述原封不动。

此处确有一件全新的东西，而它压根与递归无关。码集的诸成员是在**层级**的编码里、在该阶段自己的字母表之上取的键；而这场递归所说的一切，是在**模型**的编码里、在模型的语言之上取的键。两者是同一套构造落在两个字母表上，而没有任何定理把它们接上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Uniform {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; ⊨-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( module LCode; prʟ-fst; codeBridge; domAt; domAt-intro; domAt-out )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Bridge {ℓ} lem
  using ( intoL; asConst; Sat-spec ) renaming ( graph to envGraph )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; slot; satTable; total; inSlot; entry-in )
open import L.Coding.Slot {ℓ} lem using ( slotClosed )
open import L.Coding.Clauses {ℓ} lem using
  ( Tags; nn; towerAt; tableAt; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; f10; f11
  ; module Tower; module TowerHolds )
open import L.Coding.Pinned {ℓ} lem using ( module SatSoundC; module SlotHolds ) renaming ( keyBridge to keyBridge' )
open import L.Coding.Graph {ℓ} lem using
  ( satGraph; graph-in; graph-out; GraphWit
  ; Bi; Ti; Ci; Ei; NN; ev; numν; numTags )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; AllCodes-out; key∈AllCodes )
open import L.Recursion {ℓ} lem using ( Recursion; mereFunct; module Of )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## A member, named
<!--zh-->
## 点名一个成员
<!--/-->

<!--en-->
Three lines, and they are the chapter's one performance decision. A consumer that
wants the value at a particular formula has to name the member the value is taken
at, and the obvious name is the key itself; naming it that way does not
elaborate, because the key unfolds into a pair of a numeral with a code and that
construction then sits inside the recursion's domain and inside a satisfaction.

So the name is sealed where it is made. Sealed, it is an element of `L` that a
type can mention without unfolding, and the two facts a consumer needs come out
with it: it lies in the domain, and it is the key of the formula it was made
from. Everything below is stated at a variable member and reaches its key by an
equation, so the seal is the only thing that has to be opened, and nothing opens
it.
<!--zh-->
三行，而它们是本章唯一的一次性能决定。想要某条特定公式处的取值的消费方，必须为「取值所在的那个成员」点名，而显而易见的名字就是那个键本身；可是那样点名展开不了，因为键会展成「数码与码之对」，而那个构造随后就坐进了递归的定义域里、也坐进了一个满足关系里面。

于是那个名字在它被造出之处封印。封印之后，它是 `L` 的一个元素，类型可以提它而不必展开，而消费方所需的两条事实随之出来：它落在定义域中，且它是「造它时所用的那条公式」的键。下面的一切都陈述在变元成员上、并经一条等式抵达它的键，故需要被打开的只有这个封印，而没有任何东西打开它。
<!--/-->

```agda
module _ (A : S) where
  opaque
    keyIn : ∀ {n} → Formula ⟪ fst A ⟫ n → S
    keyIn ψ = keyS A ψ

    keyIn≡ : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) → fst (keyIn ψ) ≡ fst (keyS A ψ)
    keyIn≡ ψ = refl

    keyIn∈ : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) → ⟨ keyIn ψ ∈ˢ AllCodes A ⟩
    keyIn∈ ψ = key∈AllCodes A ψ
```

<!--en-->
## The two codings meet
<!--zh-->
## 两套编码的会合
<!--/-->

<!--en-->
A key in the hierarchy's coding is the arity numeral paired with the code of the
formula relabelled along the alphabet's embedding; a key in the model's coding is
the numeral of `L` paired with the code taken in `L`. `codeBridge`{.Agda} equates
the two codes, one clause per constructor. It was written in the model chapter
and has had no consumer since, because this is the statement it was written for.

What it does not supply is the relabelling. The set's formulas are over the
alphabet `⟪ A ⟫`{.Agda} and the recursion's formulas are over `L`, so the two
sides pass through two different maps and their composite has to be recognized as
one map. That is functoriality of relabelling, which belongs where relabelling is
defined and is now there, so the whole bridge is four rewrites and no induction.

The map into the model is not built here either. It is the bridge chapter's own
`asConst`{.Agda}, the alphabet's embedding followed by the class inclusion, and
taking that one rather than an equal one is what lets the last section quote the
adequacy without a translation step.

The bridge takes the alphabet and nothing else. The set the environments range
over never appears in it, so it is stated one parameter short of the recursion
below, and a later chapter that needs the two codings to agree at a carrier held
in a slot can use it without supplying a second carrier it does not have.
<!--zh-->
层级编码里的一个键，是元数数码与「沿字母表的嵌入重标之后那条公式的码」之对；模型编码里的一个键，是 `L` 的数码与「在 `L` 里取的码」之对。`codeBridge`{.Agda} 把这两个码等同起来，一构造子一子句。它写在模型那一章，此后一直没有消费方，因为它当初就是为这条陈述而写的。

它供不出的是那次重标。集合那边的公式在字母表 `⟪ A ⟫`{.Agda} 之上，递归这边的公式在 `L` 之上，故两侧经过的是两个不同的映射，而它们的复合必须被认出为一个映射。那是重标的函子性，它归属于重标被定义之处，而如今就在那里；于是整座桥是四次改写，没有归纳。

通往模型的那个映射也不在此处造。它就是桥那一章自己的 `asConst`{.Agda}，即字母表的嵌入接上类包含；而取它、而非取一个与它相等的映射，正是使最后一节能够径直引用那条充分性、无须任何翻译步骤的原因。

这座桥只取字母表，别无其他。诸环境所落之上的那个集合在它里面从未出现，故它比下面那场递归少一个参数；而后面某一章若需要两套编码在「握在一位上的载体」处相符，便可以直接用它，无须供上一个它并不拥有的第二载体。
<!--/-->

```agda
module _ (A : S) where
  keyBridge : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            → fst (keyS A ψ) ≡ fst (keyʟ (mapFo (asConst A) ψ))
  keyBridge = keyBridge' A

module _ (B : S) where
  fr : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → S ^ (16 + n)
  fr φ γ = ev numν (Tower.tower B) (slot B φ) (satTable B φ) B γ

  frTags : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → Tags (fr φ γ) NN
  frTags φ γ = numTags (Tower.tower B) (slot B φ) (satTable B φ) B γ

  frTow : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → ⟨ fr φ γ ⊨ towerAt Ei Bi (NN f0) ⟩
  frTow φ γ = TowerHolds.holds Ei Bi (NN f0) (fr φ γ) B refl refl refl

  frDom : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → ⟨ fr φ γ ⊨ domAt Ti Ci ⟩
  frDom φ γ = domAt-intro Ti Ci (fr φ γ)
    (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot B φ)))
              (λ { (w , hw) → inSlot B φ (fst z) (fst w) hw }) h)
         , (λ h → total B φ (fst z) h))

module _ (A B : S) where
  private
    toS : ∀ {n} → Formula ⟪ fst A ⟫ n → Formula S n
    toS = mapFo (asConst A)
```

<!--en-->
## Both halves, at the formula the code names
<!--zh-->
## 两半，落在那个码所命名的公式上
<!--/-->

<!--en-->
Both are the previous chapters', applied at the formula the member is the key
of rather than at an ambient formula, and the change makes existence *shorter*.
The per-formula instance had to transport a subformula's entry along the
inclusion of its own subtree into the ambient table; here the recovered formula
**is** the formula whose table is being handed over, so `entry-in`{.Agda} applies
directly and the transport is gone.

Uniqueness does not notice the change at all, and the reason is structural.
`Pinned`{.Agda} speaks about the index set and the table the graph produced,
which are bound variables of the caller's environment, never about the
recursion's domain. The domain occurs nowhere in it, nor in the twelve clauses,
so changing what the recursion is indexed by cannot reach uniqueness.

Only the totality hypothesis is written out here, and its environment is written
out with it. Left to inference, the graph's three existentially bound slots
determine nothing and six metavariables survive; naming the environment costs one
line and is the difference between elaborating and not.
<!--zh-->
两半都是前几章的，只是施于「该成员是其键的那条公式」而非某条周遭公式，而这次更换使存在性**更短**。按公式索引的那个实例得把一条子公式的条目沿「它自己的子树到周遭表的包含」搬过去；此处被还原出来的那条公式**就是**其表正被递出的那条公式，故 `entry-in`{.Agda} 直接适用，那次搬运消失了。

唯一性压根察觉不到这次更换，而理由是结构性的。`Pinned`{.Agda} 谈的是「图所产出的索引集与表」，那是调用方环境里的被绑定变元，从不谈递归的定义域。定义域既不出现在它里面，也不出现在十二条子句里，故更换递归的索引，够不着唯一性。

此处只把全性那条假设写出来，而它的环境也一并写出。若交给推断，图那三个存在绑定的槽位什么也决定不了，会剩下六个元变元；把环境点名只花一行，而那正是「能否被展开求解」的分水岭。
<!--/-->

```agda
    toB : ∀ {n} → Formula ⟪ fst B ⟫ n → Formula S n
    toB = mapFo (asConst B)

    exists : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) → fst x ≡ fst (keyʟ (toB ψ))
           → ⟨ (Sat B (toB ψ) ∷ x ∷ []) ⊨ satGraph B ⟩
    exists {n} ψ x k = graph-in B x (Sat B (toB ψ))
      ∣ numν
      , (Tower.tower B
      , (slot B (toB ψ)
      , (satTable B (toB ψ)
      , (B
      , (refl
      , (frTags B (toB ψ) δ2
      , (frTow B (toB ψ) δ2
      , (slotClosed B (toB ψ) (Tower.tower B ∷ numν f0 ∷ numν f1 ∷ numν f2 ∷ numν f3
            ∷ numν f4 ∷ numν f5 ∷ numν f6 ∷ numν f7 ∷ numν f8 ∷ numν f9 ∷ numν f10
            ∷ numν f11 ∷ Sat B (toB ψ) ∷ x ∷ [])
      , (frDom B (toB ψ) δ2
      , (subst (λ w → ⟨ pr w (fst (Sat B (toB ψ))) ∈ fst (satTable B (toB ψ)) ⟩) (sym k)
            (entry-in B (toB ψ))
      , SlotHolds.holds B Ti Bi Ci Ei NN (fr B (toB ψ) δ2) refl
          (frTags B (toB ψ) δ2) (frTow B (toB ψ) δ2) ψ refl refl)))))))))) ∣₁
      where δ2 = Sat B (toB ψ) ∷ x ∷ []

    unique : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) → fst x ≡ fst (keyʟ (toB ψ))
           → (y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → y ≡ Sat B (toB ψ)
    unique {n} ψ x k y hy = Σ≡Prop (λ v → snd (isL v))
      (PT.rec (setIsSet (fst y) (fst (Sat B (toB ψ))))
        (λ { (ν , (E , (C , (T , (b , (eb , (tg , (hE , (hc , (hd , (ha , h12))))))))))) →
          SatSoundC.pinned Ti Bi Ci Ei NN (ev ν E C T b (y ∷ x ∷ [])) B eb tg hE hc h12
            ψ (subst (λ u → ⟨ u ∈ fst C ⟩) (k ∙ sym (keyBridge' B ψ))
                 (domAt-out Ti Ci (ev ν E C T b (y ∷ x ∷ [])) hd x y ha)) y
            (subst (λ u → ⟨ pr u (fst y) ∈ fst T ⟩) (k ∙ sym (keyBridge' B ψ)) ha) })
        (graph-out B x y hy))
```

<!--en-->
## The instance
<!--zh-->
## 那个实例
<!--/-->

<!--en-->
The domain is the code set at the stage, the graph is the one two chapters back,
and `funct`{.Agda} is filled through `mereFunct`{.Agda}, because a merely existing
unique solution is a contractible one. A member arrives as a mere key of a
formula over the alphabet, the bridge turns its equation into one about the
model's key, and the two halves above are applied at that key.

The two carriers are independent parameters and stay so. `A` is the alphabet the
codes' constants are drawn from; `B` is the set the environments range over;
nothing in the recursion relates them, and charging the recursion for a relation
it does not use would be stating a weaker theorem. They are pinned together in
the next section, and only there, because that is where satisfaction acquires a
meaning.
<!--zh-->
定义域是该阶段处的码集，图是两章之前的那一个，而 `funct`{.Agda} 经 `mereFunct`{.Agda} 交付，因为「仅仅存在的唯一解」就是可缩解。一个成员以「字母表之上某条公式的键」这种仅仅存在的形式到场，那座桥把它的等式变成一条关于模型之键的等式，而上面两半就施于那个键。

两个载体是彼此独立的参数，且保持如此。`A` 是诸码的常元所取自的字母表；`B` 是诸环境所落之上的集合；递归里没有任何东西把它们联系起来，而为一个用不上的关系向递归收费，等于陈述一条更弱的定理。它们在下一节、且只在那里被钉在一起，因为那才是满足关系获得含义的地方。
<!--/-->

```agda
  satRec : Recursion
  Recursion.dom satRec = AllCodes B
  Recursion.graph satRec = satGraph B
  Recursion.funct satRec x x∈ = mereFunct (satGraph B) x
    (PT.map
      (λ { (n , ψ , q) → Sat B (toB ψ)
         , ( exists ψ x (q ∙ keyBridge' B ψ)
           , unique ψ x (q ∙ keyBridge' B ψ) ) })
      (AllCodes-out B x x∈))

  module Table = Of satRec
```

<!--en-->
## What the value is
<!--zh-->
## 那个取值是什么
<!--/-->

<!--en-->
A recursion connected to nothing defines nothing, so the value is stated twice.

Against the recursion's own construction first, and that is uniqueness spent in
the other direction: the value at a member that is the key of a formula is the
set the meta-level recursion built at that formula, because the existence half
exhibits that set as a solution and the recursion's value is the only solution.
This is the reading a consumer needs to get anything out of the table at all,
since the value function comes from a contractibility and computes to nothing on
its own.

The member is a **variable** and its key is reached by an equation, and that is a
measurement, not a taste. Stated at the key itself, the value function's argument
is a concrete code construction, which puts that construction inside the graph
satisfaction the value is defined from; the statement that costs four seconds at
a variable ran past six minutes at the key and was abandoned, and so did the same
statement written as a corollary of the variable one, which shows the cost is in
the *statement* and not in the proof. The uniqueness chapter recorded this law at
its first case and it holds here unchanged.

Nothing is lost, in either direction. A consumer holding a member holds it as a
member, with its key equation beside it; and a consumer that wants to *name* the
member gets the convenient form back through the sealed name, at no cost, because
what the type mentions there does not unfold.
<!--zh-->
一场与任何东西都不相连的递归什么也没定义，故那个取值陈述两遍。

先对着递归自己的构造，而那是唯一性反过来花掉：在「是某条公式之键」的那个成员处，取值就是元语言递归在那条公式处造出的那个集合，因为存在性那一半把那个集合作为一个解拿了出来，而递归的取值是唯一的解。这就是消费方要从这张表里取出任何东西所需的读式，因为那个值函数来自一次可缩性，自身不化简出任何东西。

那个成员是**变元**，而它的键经一条等式抵达；这是一次测量，不是口味。若径直陈述在那个键上，值函数的实参就是一个具体的码构造，也就把那个构造塞进了「值据以定义的那个图的满足关系」里；在变元上花四秒的那条陈述，写在键上跑过了六分钟并被放弃，而把它写成变元版本的推论时同样如此，这说明代价在**陈述**里、不在证明里。唯一性那一章在它的第一个情形上记下了这条规矩，而它在此处原样成立。

两个方向都什么也没有失去。手里握着一个成员的消费方，握着的就是一个成员，外加它的键等式；而想把那个成员**点名**的消费方，可经那个封印过的名字把方便的形式拿回来，且分文不花，因为类型在那里所提的东西不会展开。
<!--/-->

```agda
  val-at : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) (x∈ : ⟨ x ∈ˢ AllCodes B ⟩)
         → fst x ≡ fst (keyS B ψ)
         → Table.val x x∈ ≡ Sat B (toB ψ)
  val-at ψ x x∈ q =
    Table.val-uniq x x∈ (Sat B (toB ψ)) (exists ψ x (q ∙ keyBridge' B ψ))

```

<!--en-->
And against satisfaction, which is the reason to have the goal. The bridge
chapter proved that a member of the meta-level value is an environment satisfying
the formula in the world `(B, ∈)`; composing it with the reading above says the
same of the table this recursion produces. At arity one it specializes to the
definable subset the definable powerset means, so **the table read at a member
that is the key of a formula is that formula's definable subset**, which is the
statement the internal hierarchy will read `Def`{.Agda} off.

The two carriers meet here because this is where they have to. A formula whose
constants are members of the carrier is one the inner world can read; a formula
naming an arbitrary element of `L` is not, and the bridge chapter says so about
itself. So the two theorems below are stated at the one carrier, which is the
instantiation the consumer wants anyway: the codes at a stage, satisfied over
that same stage.
<!--zh-->
再对着满足关系，而那是这个目标存在的理由。桥那一章证过：元语言那个取值的成员，就是在世界 `(B, ∈)` 中满足该公式的一个环境；把它与上面那条读式复合，同一句话便落到这场递归所产出的表上。在元数一处它特化为可定义幂集所指的那个可定义子集，故**在「是某条公式之键」的那个成员处读出的那张表，就是该公式的可定义子集**，而那正是内部层级将据以读出 `Def`{.Agda} 的陈述。

两个载体在此会合，因为此处是它们非会合不可的地方。常元皆为载体成员的公式，内层世界读得了；点名了 `L` 的任意元素的公式则不然，而桥那一章对自己就是这么说的。故下面两条定理陈述在同一个载体上，而那本来也是消费方想要的实例化：某阶段处的诸码，在同一个阶段之上被满足。
<!--/-->

```agda
module _ (A : S) where
  module DA = DefOf (fst A)
  open DA using ( _⊨ᵐ_ )

  val-sat : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            (x : S) (x∈ : ⟨ x ∈ˢ AllCodes A ⟩) → fst x ≡ fst (keyS A ψ)
          → (δ : DA.SM ^ n) (z : S) → fst z ≡ envGraph A δ
          → (z ∈ˢ Table.val A A x x∈) ≡ (δ ⊨ᵐ ψ)
  val-sat ψ x x∈ q δ z qz =
      cong (z ∈ˢ_)
        (val-at A A ψ x x∈ q ∙ cong (Sat A) (sym (mapFo-comp DA.ι (intoL A) ψ)))
    ∙ Sat-spec A (mapFo DA.ι ψ) δ z qz
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι id ψ δ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`satRec`{.Agda} is satisfaction as an internalized recursion over **the codes at
a stage**, not over one formula's subformulas, and `Table`{.Agda} is the table it
yields. `val-at`{.Agda} reads a value out at a member given as a key, and
`val-sat`{.Agda} says that value **is** satisfaction over the carrier.

Nothing below was re-indexed and nothing was weakened. The registered risk for
this goal was that the domain or its well-formedness predicate would need the
carrier as a *constant* somewhere it cannot be a slot, which would have re-indexed
the slot, the table, totality and membership at a pair of a carrier and a key, and
charged the two halves a transport for each of their twelve cases. It did not
fire, and the direct evidence is that `slot`{.Agda}, `satTable`{.Agda},
`total`{.Agda}, `inSlot`{.Agda}, `slotClosed`{.Agda}, `soundness`{.Agda} and
`Good.pinned`{.Agda} are all applied above at their existing types. The code
carrier never reaches the graph: it is bound and pinned inside the code set's own
predicate, and what comes out is an element of `L`, which is all a domain is.

What made this cheap is the existential in the graph, and it is worth keeping as
a design fact rather than an accident. A graph that quantifies its table
existentially lets a value be justified by *any* admissible table, so an instance
may answer at each index with the smallest table that reaches it. Had the graph
named its table, the domain and the table would have had to grow together and
every earlier chapter would have moved.

The one cost that was not predicted is in the statements, not in the proofs, and
it is the chapter's measurement. A value read at a key *written out* does not
elaborate, at any length of proof, because the key's construction lands inside a
satisfaction; the reading that costs four seconds at a variable member ran past
six minutes at the key, and so did the same statement written as a corollary of
the variable one. Two things fix it and they are the two recorded laws, one each:
every reading takes the member as a variable and reaches its key by an equation,
and the name a consumer would write instead is sealed where it is built. The
first is the uniqueness chapter's law, met again where nothing is being proved by
induction; the second is the law about a construction appearing in a goal, met at
a goal that is a plain equation.
<!--zh-->
`satRec`{.Agda} 是作为已内化递归的满足关系，跑在**某阶段处的诸码**之上，而非跑在一条公式的诸子公式之上，而 `Table`{.Agda} 是它产出的那张表。`val-at`{.Agda} 在一个以键的形式给出的成员处读出取值；`val-sat`{.Agda} 说那个取值**就是**载体之上的满足关系。

底下没有任何东西被重新索引，也没有任何东西被削弱。本目标登记在案的风险是：定义域或它的良构谓词会在某个不能取作槽位之处、把载体当作**常元**来要；那将把槽、表、全性与隶属重新索引在「载体与键」之对上，并为两半的十二个情形各记一笔搬运。它没有引爆，而直接的证据是：`slot`{.Agda}、`satTable`{.Agda}、`total`{.Agda}、`inSlot`{.Agda}、`slotClosed`{.Agda}、`soundness`{.Agda} 与 `Good.pinned`{.Agda} 在上面全都是按它们既有的类型施用的。码载体压根到不了那个图：它在码集自己的谓词里被绑定、被钉住，而出来的是 `L` 的一个元素，而定义域无非就是这个。

使这一切便宜的是图里的那个存在量词，而这值得当作一项设计事实、而非一次偶然留存下来。一个把自己的表存在量化的图，允许一个取值由**任意**一张合格的表来担保，故实例可以在每个索引处用「够得着它的最小的表」作答。倘若那个图把自己的表点了名，定义域与表就得一起长大，而前面每一章都要动。

唯一没被预料到的代价落在诸陈述里、不落在诸证明里，而它就是本章的那次测量。在一个**写开了的**键处读出的取值，无论证明写多长都展开不了，因为那个键的构造落进了一个满足关系里面；在变元成员上花四秒的那条读式，写在键上跑过了六分钟，而把它写成变元版本的推论时同样如此。修好它的有两件事，恰是登记在案的两条规矩、一条一件：每条读式都把成员取作变元、并经一条等式抵达它的键；而消费方本会写下的那个名字，在它被造出之处封印。前者是唯一性那一章的规矩，此番出现在一个压根没有在作归纳证明的地方；后者是「关于出现在目标里的构造」的那条规矩，此番出现在一个只是一条等式的目标上。
<!--/-->
