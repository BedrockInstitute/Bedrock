<!--en-->
# An internal table of stage orders
<!--zh-->
# 阶段序的内部表
<!--ja-->
# 段階順序の内部の表
<!--/-->

<!--en-->
This chapter turns the described stage comparison into a set-valued relation at
every ordinal, by recursively building a table whose entries realize exactly the
order at their stages.
<!--zh-->
本章把已描述的阶段比较化为每个序数处的集合值关系，办法是递归构造一张表，使其每个条目恰好实现相应阶段的序。
<!--ja-->
本章では記述された段階比較を各順序数で集合値の関係にするため、各項目がその段階の順序を正確に実現する表を再帰的に構成する。
<!--/-->

<!--en-->
The previous chapter wrote the order down in the object language; this chapter
turns the description into an **object**. A formula is not something the model can
quantify over, and the choosing ahead needs a relation it can quantify over: a set
of ordered pairs, living inside `L`, whose members are exactly the pairs the order
relates. That set is what this chapter builds, one at every ordinal.

The shape is the hierarchy chapter's, followed closely, because the problem is the
same problem. A recursion whose values are sets cannot be named by a graph, so what
is described instead is an **approximation**: a table recording, at each ordinal
below its domain, the relation there. A graph quantifies over approximations; a
value lemma pins every value an approximation records; and replacement inside `L`
collects the table, with the functionality obligation filled through
`mereFunct`{.Agda}, because the value at an ordinal is a construction and not a
decision.

One thing here is not the hierarchy chapter's, and it is why this chapter needs two
constructions rather than one. The tower has a meta-language term, `Lset`{.Agda},
so the hierarchy's induction could always exhibit the value it was about to record.
The order at a stage has no such term: the set of related pairs is exactly what is
being built. So the induction carries **two** things at once, the table below an
ordinal and the relation at it, and the second is cut out by the model's own
separation from a bound the pairs cannot escape.
<!--zh-->
上一章用对象语言把那个序写了出来；本章把那条描述变成一个**对象**。公式不是模型量化得了的东西，而后续的选取需要一个它量化得了的关系：一个有序对之集，位于 `L` 之内，其成员恰是那个序所关联的诸对。本章构造的正是那个集合，每个序数处一个。

形状取自层级那一章，二者完全一致，因为处理的是同一个问题。取值为集合的递归无法由一个图直接给出，故被描述的是**逼近**：一张表，在它定义域以下的每个序数处记录那里的关系。图对诸逼近作量化；值引理逐点确定逼近所记录的每个取值；而 `L` 内部的替换把表聚合起来，函数性由 `mereFunct`{.Agda} 证得，因为某个序数处的取值是一个构造、而不是一次判定。

此处有一样东西不是层级那一章所有的，而它正是本章需要两个构造而非一个的原因。塔有一个元语言的词项 `Lset`{.Agda}，故层级那场归纳总能当场给出它要记录的取值。阶段处的序没有这样的词项：被关联的诸对所成的集合正是要造的东西。于是那场归纳一次携带**两**样东西，即某个序数以下的表与它那里的关系，而后者由模型自身的分离从「诸对逃不出的那个界」中得出。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.OrderTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL; hasSeparationL )
open import L.Recursion {ℓ} lem using ( mereFunct; smallDom )
open import L.Coding.Model {ℓ} using ( domAt-intro; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( extAt; extAt-in; extAt-out; extAt-in-both )
open import L.Coding.HierarchySequence {ℓ} lem using ( module RecShape )
open import L.Choice.StageOrders {ℓ} lem using ( Mem; relOf; orderAt; memOf; carry )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )

open import Cubical.Data.Sigma using ( Σ≡Prop; _×_ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```

<!--en-->
## The comparison, read back whole
<!--zh-->
## 把比较整个读回来
<!--ja-->
## 比較を切り詰めから取り戻す
<!--/-->

<!--en-->
`strict`{.Agda} removes the propositional truncation from a comparison belonging
to a strict well-order, using trichotomy to show that only one branch can hold.
<!--zh-->
`strict`{.Agda} 从严格良序中的比较上消去命题截断，并借助三歧性证明只有一个分支能够成立。
<!--ja-->
`strict`{.Agda} は狭義整列順序の比較から命題的切り詰めを除き、三分性により、成立しうる分岐は一つだけであることを示す。
<!--/-->

<!--en-->
A class of the model is a proposition-valued predicate, and the comparison at a
stage is not known to be proposition-valued: it is a sum of two keys, and nothing
so far says a set comes before another in only one way. So the class below carries
the comparison **truncated**, and the truncation has to come off again, since the
naming chapter's consumers need the comparison itself, untruncated.

It comes off for free, and for a reason that belongs to every strict well-order
rather than to this one. Split on trichotomy first: in the strict case the
comparison is already in hand and no truncation is eliminated at all; in the other
two cases the goal is absurdity, which is a proposition, so the truncation may be
opened there. Irreflexivity closes the equal case and transitivity the reversed
one. Two lines of mathematics, and the truncation never has to be avoided
anywhere else in the chapter.
<!--zh-->
模型中的类是命题值谓词，而阶段处的比较尚未证明为命题值：它是两个键的和，目前没有结论保证一个集合只能以一种方式排在另一个之前。因此，下面的类携带**截断**后的比较；命名一章的使用者需要未截断的实际比较，所以随后还必须消去这层截断。

它是白脱的，理由属于每一个严格良序，而非只属于这一个。先按三歧分情形：严格那一情形中比较早已在手，压根不消去任何截断；另外两种情形中目标是荒谬，而荒谬是命题，故截断可以在那里打开。非自反封住相等那一支，传递封住反向那一支。数学只有两行，而本章其余各处再不必绕开截断。
<!--/-->

```agda
Ordering : (α : V ℓ) → IsOrd α → Mem (Lset α) → Mem (Lset α) → Ω
Ordering α oα a b = ∥ relOf (orderAt α oα) a b ∥₁ , squash₁

strict : (α : V ℓ) (oα : IsOrd α) (a b : Mem (Lset α))
       → ⟨ Ordering α oα a b ⟩ → relOf (orderAt α oα) a b
strict α oα a b h = decide (SWO.tri∙ W a b)
  where
  W = orderAt α oα
  decide : Tri (relOf W a b) (a ≡ b) (relOf W b a) → relOf W a b
  decide (lt k) = k
  decide (eq q) = Empty.rec (PT.rec Empty.isProp⊥
    (λ k → SWO.irr∙ W a (subst (relOf W a) (sym q) k)) h)
  decide (gt k) = Empty.rec (PT.rec Empty.isProp⊥
    (λ j → SWO.irr∙ W a (SWO.trans∙ W a b a j k)) h)
```

<!--en-->
## What the relation at a stage is
<!--zh-->
## 阶段处的关系是什么
<!--ja-->
## 段階における関係
<!--/-->

<!--en-->
`Related`{.Agda} is the class of ordered pairs of stage members related by the
meta comparison, and `Realizes`{.Agda} specifies a set with exactly that
membership.
<!--zh-->
`Related`{.Agda} 是由元比较所关联的阶段成员有序对之类，而 `Realizes`{.Agda} 刻画其成员恰为该类的那些集合。
<!--ja-->
`Related`{.Agda} はメタな比較で関係づけられる段階要素の順序対からなるクラスであり、`Realizes`{.Agda} はその要素をちょうどもつ集合を指定する。
<!--/-->

<!--en-->
`Related`{.Agda} is the class the object realizes: the ordered pairs of two members
of the stage that the order there relates. Ordinality is bound **inside** the
class rather than carried beside it, so nothing below ever transports a
comparison along a proof that an ordinal is one; the one place a chosen proof is
wanted, the reading, moves it in a single `subst`{.Agda}, because being an ordinal
is a proposition.

`Realizes`{.Agda} says a set of the model realizes that class, member for member,
and it is written as an indexed conjunction of two implications rather than as a
pointwise equality of propositions. That is a level constraint and not a
preference: an equality of propositions lives one universe above the propositions
themselves, and this statement has to be a proposition of the model, because the
table records it. The two forms are interchangeable, and where an equality is
wanted `⇔toPath`{.Agda} supplies it.
<!--zh-->
`Related`{.Agda} 是那个对象所实现的类：阶段的两个成员所成的、被那里的序所关联的有序对。序数性信息绑定在类**之内**，而不是另行随行携带，于是下文任何地方都不必随「某个序数确是序数」的一份证明去搬运一次比较；唯一需要一份指定证明之处，即那条读式，用单次 `subst`{.Agda} 把它传递过去，因为「是序数」是命题。

`Realizes`{.Agda} 说模型的某个集合逐成员地实现那个类，而它写成两条蕴含的合取，而不是命题之间的逐点相等。这是层级上的约束，不是偏好：命题之间的相等属于诸命题自身之上的一个宇宙，而这条陈述必须是模型内部的一个命题，因为那张表要把它记录下来。两种形式可以互相转换，需要相等之处由 `⇔toPath`{.Agda} 提供。
<!--/-->

```agda
Related : V ℓ → V ℓ → Ω
Related α z = ⋁ (IsOrd α) (λ oα → ⋁ (Mem (Lset α)) (λ a → ⋁ (Mem (Lset α)) (λ b →
  ((z ≡ pr (fst a) (fst b)) , setIsSet z (pr (fst a) (fst b))) ⊓ Ordering α oα a b)))

Realizes : V ℓ → S → Ω
Realizes α r = ⋀ S (λ z → ((fst z ∈ fst r) ⇒ Related α (fst z))
                        ⊓ (Related α (fst z) ⇒ (fst z ∈ fst r)))

IsRel : V ℓ → S → Type (ℓ-suc ℓ)
IsRel α r = ⟨ Realizes α r ⟩

rel-path : (α : V ℓ) (r : S) → IsRel α r
         → (z : S) → (fst z ∈ fst r) ≡ Related α (fst z)
rel-path α r p z =
  ⇔toPath {P = fst z ∈ fst r} {Q = Related α (fst z)} (p z .fst) (p z .snd)

rel-unique : (α : V ℓ) (r r' : S) → IsRel α r → IsRel α r' → r ≡ r'
rel-unique α r r' p q = extensionalL
  (λ z → rel-path α r p z ∙ sym (rel-path α r' q z))

module _ (α : V ℓ) (oα : IsOrd α) (a b : Mem (Lset α)) where
  related-in : relOf (orderAt α oα) a b → ⟨ Related α (pr (fst a) (fst b)) ⟩
  related-in h = ∣ oα , ∣ a , ∣ b , (refl , ∣ h ∣₁) ∣₁ ∣₁ ∣₁

  related-out : ⟨ Related α (pr (fst a) (fst b)) ⟩ → relOf (orderAt α oα) a b
  related-out h = strict α oα a b (PT.rec squash₁ atOrd h)
    where
    atPair : (o : IsOrd α) (a' b' : Mem (Lset α))
           → (pr (fst a) (fst b) ≡ pr (fst a') (fst b'))
           → ⟨ Ordering α o a' b' ⟩ → ⟨ Ordering α oα a b ⟩
    atPair o a' b' q = PT.map
      (λ k → subst2 (relOf (orderAt α oα)) (sym ea) (sym eb)
        (subst (λ o' → relOf (orderAt α o') a' b') (isPropIsOrd α o oα) k))
      where
      ea : a ≡ a'
      ea = Σ≡Prop (λ x → snd (x ∈ Lset α)) (pr-inj q .fst)
      eb : b ≡ b'
      eb = Σ≡Prop (λ x → snd (x ∈ Lset α)) (pr-inj q .snd)

    atOrd : Σ[ o ∈ IsOrd α ] ⟨ ⋁ (Mem (Lset α)) (λ a' → ⋁ (Mem (Lset α)) (λ b' →
              ((pr (fst a) (fst b) ≡ pr (fst a') (fst b'))
                 , setIsSet _ (pr (fst a') (fst b'))) ⊓ Ordering α o a' b')) ⟩
          → ⟨ Ordering α oα a b ⟩
    atOrd (o , h₁) = PT.rec squash₁
      (λ { (a' , h₂) → PT.rec squash₁
        (λ { (b' , (q , hr)) → atPair o a' b' q hr }) h₂ }) h₁
```

<!--en-->
## Whatever realizes the class, read at both shapes
<!--zh-->
## 凡实现那个类者，读在两种形状上
<!--ja-->
## クラスを実現する任意の集合を二つの形で読む
<!--/-->

<!--en-->
Four representation lemmas read any realizing set at raw pairs and at indexed
stage members, in both the membership-to-comparison and comparison-to-membership
directions.
<!--zh-->
四条表示引理针对任意实现该类的集合，分别在裸有序对与带索引的阶段成员这两种形状上读取其成员关系，并覆盖从隶属到比较、从比较到隶属两个方向。
<!--ja-->
四つの表現補題は、任意の実現集合を生の順序対と添字つき段階要素の二つの形で読み、所属から比較へ、比較から所属への両方向を与える。
<!--/-->

<!--en-->
The two readings a consumer wants are membership in **a** set that realizes the
class, and they are stated of any such set rather than of the one this chapter
builds. That is not generality for its own sake. The set the naming machinery
must be handed is the relation at the stage below the one being built, and inside
the construction that set arrives from the table, as a value with the hypothesis
that it realizes the class there; whereas the set this chapter finally returns
exists only after the construction is finished. Stated of any realizing set, the
two readings are available a stage earlier than the construction, and that is
exactly where they are wanted.

Both are two lines. A member of a stage reaches the model as a pair with its
constructibility proof, `Related`{.Agda} is read at the pair the model builds
rather than at the meta pair, and one congruence along `prʟ-fst`{.Agda} moves
between them.
<!--zh-->
所需的两条读式陈述「某个实现该类的集合的成员关系」，并适用于任何这样的集合，而不限于本章最终构造的那个集合。这种一般性有具体用途：命名构造需要正在建造阶段的前一阶段处的关系；在构造内部，该集合来自表的一个取值，并附带它在该处实现相应类的假设，而本章最终返回的集合要到构造结束后才存在。因此，对任意实现集合陈述读式，使它们能提前一个阶段使用。

两条各两行。阶段的一个成员抵达模型时是一个对，携带它的可构造性证明；`Related`{.Agda} 读在模型所造的那个对上、而不是元层面那个对上，而沿 `prʟ-fst`{.Agda} 的一次同余在两者之间搬运。
<!--/-->

```agda
module _ (α : V ℓ) (oα : IsOrd α) (r : S) (hr : IsRel α r) where
  private
    memL : Mem (Lset α) → S
    memL c = fst c , Lset→isL α oα (fst c) (snd c)

    atRel : (a b : Mem (Lset α))
          → (fst (prʟ (memL a) (memL b)) ∈ fst r)
          ≡ (pr (fst a) (fst b) ∈ fst r)
    atRel a b = cong (λ x → x ∈ fst r) (prʟ-fst (memL a) (memL b))

    atRelated : (a b : Mem (Lset α))
              → ⟨ Related α (fst (prʟ (memL a) (memL b))) ⟩
              ≡ ⟨ Related α (pr (fst a) (fst b)) ⟩
    atRelated a b = cong (λ x → ⟨ Related α x ⟩) (prʟ-fst (memL a) (memL b))

  rel-fill : (a b : Mem (Lset α)) → relOf (orderAt α oα) a b
           → ⟨ pr (fst a) (fst b) ∈ fst r ⟩
  rel-fill a b h = subst ⟨_⟩ (atRel a b)
    (hr (prʟ (memL a) (memL b)) .snd
      (transport (sym (atRelated a b)) (related-in α oα a b h)))

  rel-rep : (a b : Mem (Lset α))
          → ⟨ pr (fst a) (fst b) ∈ fst r ⟩ → relOf (orderAt α oα) a b
  rel-rep a b h = related-out α oα a b
    (transport (atRelated a b)
      (hr (prʟ (memL a) (memL b)) .fst (subst ⟨_⟩ (sym (atRel a b)) h)))

  private
    atIx : ⟪ Lset α ⟫ → Mem (Lset α)
    atIx m = ⟪ Lset α ⟫↪ m , memOf (Lset α) m

  open SWO (carry (Lset α) (orderAt α oα)) using () renaming ( _<∙_ to _≺ᶜ_ )

  ixRel-fill : (u v : ⟪ Lset α ⟫) → u ≺ᶜ v
             → ⟨ pr (⟪ Lset α ⟫↪ u) (⟪ Lset α ⟫↪ v) ∈ fst r ⟩
  ixRel-fill u v = rel-fill (atIx u) (atIx v)

  ixRel-rep : (u v : ⟪ Lset α ⟫)
            → ⟨ pr (⟪ Lset α ⟫↪ u) (⟪ Lset α ⟫↪ v) ∈ fst r ⟩ → u ≺ᶜ v
  ixRel-rep u v = rel-rep (atIx u) (atIx v)
```

<!--en-->
## What a table records
<!--zh-->
## 一张表记录了什么
<!--ja-->
## 表が記録するもの
<!--/-->

<!--en-->
`Values`{.Agda}, `Entries`{.Agda}, and `Domain`{.Agda} separately state
correctness of recorded relations, existence of every bounded entry, and absence
of entries outside the bound.
<!--zh-->
`Values`{.Agda}、`Entries`{.Agda} 与 `Domain`{.Agda} 分别陈述所记录关系的正确性、每个界内条目的存在性，以及界外无条目。
<!--ja-->
`Values`{.Agda}、`Entries`{.Agda}、`Domain`{.Agda} はそれぞれ、記録された関係の正しさ、上界内の各項目の存在、上界外に項目がないことを述べる。
<!--/-->

<!--en-->
Three conditions, one line each, and they are kept apart for the reason the
hierarchy chapter kept its own apart: the two consumers need different subsets of
them. `Values`{.Agda} says a value recorded below `B` realizes the relation there.
`Entries`{.Agda} says every argument below `B` has some value recorded at it, and
merely so, which is all the step ever asks. `Domain`{.Agda} says nothing outside
`B` is recorded, which the induction on an approximation cannot have and the
finished table does.
<!--zh-->
三个条件，各一行；把它们分开的理由与层级那一章分开自己那三个的理由相同：两个消费方所需的子集不同。`Values`{.Agda} 说 `B` 以下所记录的取值实现那里的关系。`Entries`{.Agda} 说 `B` 以下的每个实参处都记录着某个取值，且内容仅此而已，而这正是那一步所需的全部。`Domain`{.Agda} 说 `B` 以外的东西没有被记录；这是关于逼近的那场归纳所不可能给出、而造完的表却具有的性质。
<!--/-->

```agda
Values : S → V ℓ → Type (ℓ-suc ℓ)
Values h B = (c r : S) → ⟨ fst c ∈ B ⟩
           → ⟨ pr (fst c) (fst r) ∈ fst h ⟩ → IsRel (fst c) r

Entries : S → V ℓ → Type (ℓ-suc ℓ)
Entries h B = (c : S) → ⟨ fst c ∈ B ⟩
            → ∥ (Σ[ r ∈ S ] ⟨ pr (fst c) (fst r) ∈ fst h ⟩) ∥₁

Domain : S → V ℓ → Type (ℓ-suc ℓ)
Domain h B = (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩
```

<!--en-->
## The step, as a parameter
<!--zh-->
## 那一步，取作参数
<!--ja-->
## ステップをパラメータとする
<!--/-->

<!--en-->
The table construction assumes a formula for one stage step together with two
adequacy directions, one at variable slots and one at constants used by
separation.
<!--zh-->
序表构造假设一条描述单阶段步进的公式及其两个充分性方向，一种用于变元位，另一种用于分离所用的常元。
<!--ja-->
表の構成は一段階のステップを表す論理式と、その二つの妥当性方向を仮定する。一方は変数スロットで、他方は分出公理が使う定数で用いられる。
<!--/-->

<!--en-->
The step at an ordinal says which pairs the relation there holds, given the table
below. Everything after this section is generic in that condition, which enters as
a **parameter** in two forms with one meaning: at slots, because the graph must
bind the table it consults, and at constants, because separation carves with a
formula of one free variable and the table it consults is, at the moment of
carving, a definite element of the model. The meaning is the hypothesis, stated
once for each form: at a correct and complete table below an ordinal, the
condition holds of a set exactly when that set is a pair the order there relates.

This interface has three ingredients: the adequacy of `StepAt`{.Agda}, the
object-language description of birth stages, and the code set over a carrier
that varies with the birth stage. The later chapters `L.Choice.NameComparisonAdequacy`{.Agda},
`L.Choice.StageOrderAdequacy`{.Agda}, and `L.Choice.InternalWellOrder`{.Agda} supply and assemble them.
Here the construction is generic in that interface: given it, the relation at
every stage is an element of `L` whose members are exactly the right pairs.

The step itself is one `extAt`{.Agda}, for the reason every set-valued clause on
this route is one: a value is the set of exactly the things meeting a condition,
and writing that as a pair of inclusions would say the condition twice.
<!--zh-->
某个序数处的那一步说清：给定以下的表，那里的关系持有哪些对。本节之后的一切都对那个条件保持通用，而它以**参数**身份进场，取两种形式、只有一个含义：落在诸位上，因为图必须绑定它所查阅的那张表；以及落在常元上，因为分离是用单自由变量的公式去雕的，而它所查阅的那张表，在下刀的那一刻是模型的一个确定元素。含义就是那条假设，两种形式各说一遍：在某个序数以下一张正确且完备的表上，那个条件对某个集合成立，当且仅当该集合是那里的序所关联的一个对。

这个接口包含三项：`StepAt`{.Agda} 的充分性、诞生阶段的对象语言描述，以及随诞生阶段变化的载体上的码集。后面的 `L.Choice.NameComparisonAdequacy`{.Agda}、`L.Choice.StageOrderAdequacy`{.Agda} 与 `L.Choice.InternalWellOrder`{.Agda} 供应并组装它们。本章的构造对这个接口保持通用：给定它，每个阶段处的关系都是 `L` 的一个元素，其成员恰是那些正确的对。

那一步自身是一次 `extAt`{.Agda}，理由与这条路线上每一条取值为集合的子句相同：一个取值恰是满足某条件的那些东西之集，而若写成一对包含，那个条件就要说两遍。
<!--/-->

```agda
module Described
  (Cond : ∀ {n} → Fin n → Fin n → Formula S (suc n))
  (Cond₀ : S → S → Formula S 1)
  (cond-spec : ∀ {n} (b f : Fin n) (γ : S ^ n) → IsOrd (fst (lookup b γ))
             → Values (lookup f γ) (fst (lookup b γ))
             → Entries (lookup f γ) (fst (lookup b γ))
             → (z : S)
             → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z))
  (cond₀-spec : (b f : S) → IsOrd (fst b)
              → Values f (fst b) → Entries f (fst b)
              → (z : S) → ((z ∷ []) ⊨ Cond₀ b f) ≡ Related (fst b) (fst z))
  where

  StepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  StepAt v b f = extAt v (Cond b f)

  module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n)
           (ob : IsOrd (fst (lookup b γ)))
           (vals : Values (lookup f γ) (fst (lookup b γ)))
           (ents : Entries (lookup f γ) (fst (lookup b γ))) where
    private
      same : (z : S) → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z)
      same = cond-spec b f γ ob vals ents

    step-rel : ⟨ γ ⊨ StepAt v b f ⟩ → IsRel (fst (lookup b γ)) (lookup v γ)
    step-rel h z =
        (λ hz → subst ⟨_⟩ (same z) (extAt-out v (Cond b f) γ h z hz))
      , (λ hz → extAt-in v (Cond b f) γ h z (subst ⟨_⟩ (sym (same z)) hz))

    step-table : IsRel (fst (lookup b γ)) (lookup v γ) → ⟨ γ ⊨ StepAt v b f ⟩
    step-table sp = extAt-in-both v (Cond b f) γ
      (λ z hz → subst ⟨_⟩ (sym (same z)) (sp z .fst hz))
      (λ z h → sp z .snd (subst ⟨_⟩ (same z) h))
```

<!--en-->
## Approximations and the graph
<!--zh-->
## 诸逼近，与那个图
<!--ja-->
## 近似とグラフ
<!--/-->

<!--en-->
`ApproxAt`{.Agda} combines bounded domain and correct recorded values, while
`GraphAt`{.Agda} says the next value satisfies the step computed from that same
approximation.
<!--zh-->
`ApproxAt`{.Agda} 组合有界定义域与所记录取值的正确性，而 `GraphAt`{.Agda} 断言下一个取值满足由同一逼近计算出的步进。
<!--ja-->
`ApproxAt`{.Agda} は有界な定義域と記録値の正しさを組み合わせ、`GraphAt`{.Agda} は次の値が同じ近似から計算されるステップを満たすことを述べる。
<!--/-->

<!--en-->
Two conjuncts and no third: the table is defined on the argument, and every value
it records is the step at that argument from the table itself. The pair is a
membership **equivalence**, which is what makes the existence claim below a
proposition; single-valuedness is not a conjunct, because it is a corollary, and
the corollary is established two sections down.

The graph binds the table, and it has to: a graph may not name the object it
defines, and the tower of relations is defined here. The value stands at the first
slot and the argument at the second, which is the order the model's replacement
field reads a graph in.
<!--zh-->
这里恰有两个合取项：该表定义在给定实参上；并且它记录的每个取值，都是在该实参处由表自身算出的那一步。二者组成一条隶属**等价**，从而使下文的存在性断言成为命题。单值性不另列为合取项，因为它是由这些条件推出的结论，该推论在下面两节取得。

图把表绑住，而这是不得不然：一个图不可以点名它所定义的对象，而诸关系之塔正是在此处被定义的。取值站在第一位、实参站在第二位，这正是模型的替换字段读一个图所用的顺序。
<!--/-->

```agda
  module A = RecShape StepAt
  open A using ( ApproxAt; GraphAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step
               ; ApproxAt-in; GraphOf; Graph-in; Graph-out
               ; PairGraphAt; PairOf; PairGraph-in; PairGraph-out )
```

<!--en-->
## Every value an approximation records
<!--zh-->
## 逼近所记录的每个取值
<!--ja-->
## 近似が記録するすべての値
<!--/-->

<!--en-->
Ordinal induction proves every recorded value realizes the corresponding stage
relation; extensionality then gives uniqueness without assuming the table is
single-valued.
<!--zh-->
序数归纳证明每个所记录取值都实现相应阶段关系；外延性随后给出唯一性，而无须假设表为单值。
<!--ja-->
順序数帰納法により各記録値が対応する段階関係を実現すると示し、表の単値性を仮定せずに外延性から一意性を得る。
<!--/-->

<!--en-->
One induction, on the argument, in the meta-language, with the approximation and
its domain held fixed. The motive says: whatever value the approximation records
at this argument realizes the relation there. It quantifies over **all** recorded
values, and that is why single-valuedness is nowhere a hypothesis: two values
recorded at one argument realize one class, so extensionality in `L` makes them
equal, and `approx-uniq`{.Agda} is those three lines.

The step of the induction is the step condition read at the recorded value.
Correctness below the argument *is* the induction hypothesis, verbatim.
Completeness below the argument is where the domain hypothesis is spent: an
argument below this one is below the approximation's domain, because the domain is
an ordinal and ordinals are transitive, so the approximation has a value there.
<!--zh-->
一次在元语言中、在实参上进行的归纳，使逼近与它的定义域保持固定。动机说：逼近在这个实参处所记录的任何取值，都实现那里的关系。它对**一切**被记录的取值作量化，而这正是单值性在任何地方都不作为假设的原因：在同一个实参处记录的两个取值实现同一个类，故 `L` 中的外延性使它们相等，而 `approx-uniq`{.Agda} 就是那三行。

归纳的步进就是那条步进条件读在被记录的取值上。实参以下的正确性**就是**归纳假设，一字不差。实参以下的完备性则是那条定义域假设被花掉之处：比这个实参更低的实参落在逼近的定义域以下，因为定义域是序数，而序数传递，故逼近在那里有取值。
<!--/-->

```agda
  module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
    private
      Value : V ℓ → Type (ℓ-suc ℓ)
      Value u = ⟨ isL u ⟩ → IsOrd u → (r : S)
              → ⟨ pr u (fst r) ∈ fst (lookup f γ) ⟩ → IsRel u r

    approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
               → (c : S) → IsOrd (fst c) → (r : S)
               → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩ → IsRel (fst c) r
    approx-val h oa c = ∈-induction {P = Value} go (fst c) (snd c)
      where
      go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
      go u IH hu ou r p = step-rel zero (suc zero) (sh2 f) (r ∷ d ∷ γ) ou vals ents
        (ApproxAt-step f a γ h d r p)
        where
        d : S
        d = u , hu
        u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
        u∈a = ApproxAt-dom f a γ h d r p
        vals : Values (lookup f γ) u
        vals e t e∈ q =
          IH (fst e) e∈ (snd e) (mem-ord {A = u} ou (fst e) e∈) t q
        ents : Entries (lookup f γ) u
        ents e e∈ = ApproxAt-value f a γ h e (oa .fst {x = u} {y = fst e} e∈ u∈a)

```

<!--en-->
## The graph holds of nothing else
<!--zh-->
## 图对别的什么都不成立
<!--ja-->
## グラフが決定する値
<!--/-->

<!--en-->
`graph-only`{.Agda} shows the graph determines its value from the approximation,
and `graph-table`{.Agda} proves any correct complete bounded table satisfies the
same graph.
<!--zh-->
`graph-only`{.Agda} 证明图由逼近决定其取值，而 `graph-table`{.Agda} 证明任意正确、完整且有界的表都满足同一张图。
<!--ja-->
`graph-only`{.Agda} はグラフの値が近似から決まることを示し、`graph-table`{.Agda} は正しく完全で有界な任意の表が同じグラフを満たすことを証明する。
<!--/-->

<!--en-->
Read the graph and everything is already in hand: unpack the approximation, take
correctness from `approx-val`{.Agda}, take completeness from the approximation's
own domain projection, and read the step once more. The conclusion is that the
graph **determines** its value, and the converse is a table: a correct, complete,
bounded table satisfies the graph, because it satisfies both conjuncts of "is an
approximation" and the outer step as well.

Both readings stand at variable slots, and that is not decoration. Their consumers
instantiate them at two different concrete environments, and a statement made at
either would have to be converted to the other through a satisfaction carrying the
whole description inside it.
<!--zh-->
把图读出来，所需的一切都直接可得：拆开逼近，正确性取自 `approx-val`{.Agda}，完备性取自该逼近在本章所给的定义域投影，然后再读一次外层那一步。于是图**确定**它的取值；反方向则是一张表：一张正确、完备且有界的表满足那个图，因为它同时满足「是一个逼近」的两个合取项以及外层那一步。

两条读式都出现在变元的位置上，这并非单纯的记号安排：它们各自在两个不同的具体环境中被实例化，而要把陈述从其中一处转换到另一处，都必须经过一个内部带有整条描述的满足关系。
<!--/-->

```agda
  module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    graph-only : ⟨ γ ⊨ GraphAt w b ⟩ → IsOrd (fst (lookup b γ))
               → IsRel (fst (lookup b γ)) (lookup w γ)
    graph-only h ob = PT.rec (snd (Realizes (fst (lookup b γ)) (lookup w γ)))
      read (Graph-out w b γ h)
      where
      read : GraphOf w b γ → IsRel (fst (lookup b γ)) (lookup w γ)
      read (f , (ha , hs)) = step-rel (suc w) (suc b) zero (f ∷ γ) ob vals ents hs
        where
        vals : Values f (fst (lookup b γ))
        vals c r c∈ p = approx-val zero (suc b) (f ∷ γ) ha ob c
          (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈) r p
        ents : Entries f (fst (lookup b γ))
        ents = ApproxAt-value zero (suc b) (f ∷ γ) ha

    graph-table : (h : S) → IsOrd (fst (lookup b γ))
                → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
                → Domain h (fst (lookup b γ))
                → IsRel (fst (lookup b γ)) (lookup w γ) → ⟨ γ ⊨ GraphAt w b ⟩
    graph-table h ob vals ents dom sp = Graph-in w b γ h approx
      (step-table (suc w) (suc b) zero (h ∷ γ) ob vals ents sp)
      where
      onDom : (c : S)
            → (⟨ ⋁ S (λ r → pr (fst c) (fst r) ∈ fst h) ⟩
               → ⟨ fst c ∈ fst (lookup b γ) ⟩)
            × (⟨ fst c ∈ fst (lookup b γ) ⟩
               → ⟨ ⋁ S (λ r → pr (fst c) (fst r) ∈ fst h) ⟩)
      onDom c = (λ hr → PT.rec (snd (fst c ∈ fst (lookup b γ)))
                          (λ { (r , p) → dom c r p }) hr)
              , ents c

      onStep : (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
             → ⟨ (r ∷ c ∷ h ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
      onStep c r p = step-table zero (suc zero) (suc (suc zero)) (r ∷ c ∷ h ∷ γ)
        oc vals' ents' (vals c r c∈ p)
        where
        c∈ : ⟨ fst c ∈ fst (lookup b γ) ⟩
        c∈ = dom c r p
        oc : IsOrd (fst c)
        oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈
        vals' : Values h (fst c)
        vals' e t _ q = vals e t (dom e t q) q
        ents' : Entries h (fst c)
        ents' e e∈ = ents e (ob .fst {x = fst c} {y = fst e} e∈ c∈)

      approx : ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
      approx = ApproxAt-in zero (suc b) (h ∷ γ)
        (domAt-intro zero (suc b) (h ∷ γ) onDom) onStep
```

<!--en-->
## The pair graph
<!--zh-->
## 成对的那个图
<!--ja-->
## 順序対を値とするグラフ
<!--/-->

<!--en-->
`PairGraphAt`{.Agda} packages the value at an ordinal as the ordered pair of that
ordinal and its realized relation, in the graph form required by replacement.
<!--zh-->
`PairGraphAt`{.Agda} 把某个序数处的关系取值封装成该序数与其已实现关系组成的有序对，由此得到替换所需的图。
<!--ja-->
`PairGraphAt`{.Agda} は順序数での値を、その順序数と実現された関係との順序対としてまとめ、置換公理が要求するグラフの形にする。
<!--/-->

<!--en-->
The table has to be built, and the only construction available is replacement,
which requires a graph. This is that graph in paired form: the value at an
argument is the ordered pair of the argument with the relation there. Its two
readings take the sentence as a
**parameter**, with the sentence's own equation as a hypothesis, `refl`{.Agda} at
the single call site. That is the shape rule the hierarchy chapter measured at
eighty-five seconds, met here again: written directly against the closed sentence,
Agda decides the equality of two spellings of one formula by normalizing a
satisfaction that carries the entire description inside it.
<!--zh-->
表必须构造出来，而这里构造表所用的是替换；替换又需要一张图。这张图的成对形式规定：某个实参处的取值，是该实参与相应关系组成的有序对。两条读式把描述该图的句子作为**参数**，并假设该句子等于给定公式；唯一调用处以 `refl`{.Agda} 提供等式。这正是层级一章实测为八十五秒的形状规则：若直接对闭句子陈述，Agda 为判断同一公式的两种写法相等，会正规化内部含有整条描述的满足关系。
<!--/-->

<!--en-->
## The table, and the relation at the bound
<!--zh-->
## 那张表，与界上的那个关系
<!--ja-->
## 表と上界における関係
<!--/-->

<!--en-->
Replacement builds `tableAt`{.Agda} from the pair graph, proves its exact bounded
domain, and extracts `relL`{.Agda} as the realized relation at the chosen bound.
<!--zh-->
替换从成对图构造 `tableAt`{.Agda}，证明其精确的有界定义域，并抽取 `relL`{.Agda} 作为选定界处的已实现关系。
<!--ja-->
置換公理は順序対グラフから `tableAt`{.Agda} を構成し、その正確な有界定義域を証明して、選んだ上界での実現関係として `relL`{.Agda} を取り出す。
<!--/-->

<!--en-->
`Recorded`{.Agda} names the class the table realizes: the pairs of an ordinal below
`B` with the relation there, and nothing besides. `IsTable`{.Agda} says a set of
the model realizes it, member for member, and that is a membership equivalence for
the reason the hierarchy chapter recorded: said one way it would not say the table
holds *only* such pairs, the existence claim would not be a proposition, and the
induction's motive would not be either.

`Bundle`{.Agda} is what the induction carries, and its second component is what
this chapter has that the hierarchy chapter did not need: the relation **at** the
ordinal, not merely below it. Both components are unique, the table by
extensionality against the class it realizes and the relation by
`rel-unique`{.Agda}, so the bundle is a proposition and the induction may be run
against it.

The construction proceeds by membership induction. At `α` the pair graph is
functional at every argument below it: the induction hypothesis supplies the table
up to that argument and the relation at it, `graph-table`{.Agda} turns the pair
into a satisfaction of the graph, and `graph-only`{.Agda} says nothing else satisfies it.
Replacement collects the pairs. The relation at `α` itself is then separated out
of a bound, and this bound is the one construction this chapter adds beyond the
hierarchy chapter: the pairs of two members of a stage form a **small** family of
elements of `L`, indexed by the stage's own index type twice over, so a single
appeal to `smallDom`{.Agda} gives a common bound for all of them. The ordinality of
each argument is taken from `mem-ord`{.Agda} untruncated, and the whole construction
is sealed where it is built.
<!--zh-->
`Recorded`{.Agda} 为那张表所实现的类命名：「`B` 以下的序数与那里的关系」所成的诸对，此外别无他物。`IsTable`{.Agda} 说模型的某个集合逐成员地实现它，而这是一条隶属等价；理由已在层级那一章记下：若反过来说，它便没有说这张表**只**含有那样的对，那条存在性断言因此不是命题，归纳的动机也不是。

`Bundle`{.Agda} 是那场归纳所携带的数据，其第二个分量正是本章有而层级那一章不需要的：序数**处**的关系，而不只是它以下的关系。两个分量都唯一：表由外延性相对于它所实现的类而唯一，关系由 `rel-unique`{.Agda} 而唯一；故这个束是命题，那场归纳可以依它进行。

构造沿成员归纳。在 `α` 处，成对图对其下每个实参都是函数性的：归纳假设给出截至该实参的表及该处关系，`graph-table`{.Agda} 将二者变成图的一个取值，而 `graph-only`{.Agda} 排除其他取值。替换收集这些有序对。随后，`α` 从一个集合界中分离出该处关系；这个界是本章相较层级一章唯一新增的构造：阶段中两个成员组成的有序对构成由阶段索引类型两次索引的 `L` 元素**小**族，因此一次应用 `smallDom`{.Agda} 即可给出共同界。每个实参的序数性由 `mem-ord`{.Agda} 无截断地给出，整个构造在产生之处封装。
<!--/-->

```agda
  Recorded : V ℓ → V ℓ → Ω
  Recorded B z = ⋁ S (λ c → (fst c ∈ B) ⊓ ⋁ S (λ r →
    ((z ≡ pr (fst c) (fst r)) , setIsSet z (pr (fst c) (fst r)))
    ⊓ Realizes (fst c) r))

  IsTable : V ℓ → S → Type (ℓ-suc (ℓ-suc ℓ))
  IsTable B h = (z : S) → (fst z ∈ fst h) ≡ Recorded B (fst z)

  Bundle : V ℓ → Type (ℓ-suc (ℓ-suc ℓ))
  Bundle α = Σ[ h ∈ S ] Σ[ r ∈ S ] (IsTable α h × IsRel α r)

  module _ (B : V ℓ) (oB : IsOrd B) (h : S) (sp : IsTable B h) where
    private
      atPair : (c r : S)
             → (pr (fst c) (fst r) ∈ fst h) ≡ Recorded B (pr (fst c) (fst r))
      atPair c r = subst (λ x → (x ∈ fst h) ≡ Recorded B x) (prʟ-fst c r)
        (sp (prʟ c r))

    table-out : Domain h B × Values h B
    table-out = (λ c r p → read c r p .fst) , (λ c r _ p → read c r p .snd)
      where
      read : (c r : S) → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
           → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
      read c r p = PT.rec isPropBoth outer (subst ⟨_⟩ (atPair c r) p)
        where
        isPropBoth : isProp (⟨ fst c ∈ B ⟩ × IsRel (fst c) r)
        isPropBoth = isProp× (snd (fst c ∈ B)) (snd (Realizes (fst c) r))

        inner : (d t : S) → ⟨ fst d ∈ B ⟩
              → (pr (fst c) (fst r) ≡ pr (fst d) (fst t)) → IsRel (fst d) t
              → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
        inner d t d∈ q hr =
            subst (λ x → ⟨ x ∈ B ⟩) (sym (pr-inj q .fst)) d∈
          , subst2 IsRel (sym (pr-inj q .fst)) (sym rt) hr
          where
          rt : r ≡ t
          rt = Σ≡Prop (λ x → snd (isL x)) (pr-inj q .snd)

        outer : Σ[ d ∈ S ] ( ⟨ fst d ∈ B ⟩
                  × ⟨ ⋁ S (λ t → ((pr (fst c) (fst r) ≡ pr (fst d) (fst t))
                        , setIsSet _ (pr (fst d) (fst t))) ⊓ Realizes (fst d) t) ⟩ )
              → ⟨ fst c ∈ B ⟩ × IsRel (fst c) r
        outer (d , (d∈ , hs)) = PT.rec isPropBoth
          (λ { (t , (q , hr)) → inner d t d∈ q hr }) hs

    table-in : (c r : S) → ⟨ fst c ∈ B ⟩ → IsRel (fst c) r
             → ⟨ pr (fst c) (fst r) ∈ fst h ⟩
    table-in c r c∈ hr = subst ⟨_⟩ (sym (atPair c r))
      ∣ c , (c∈ , ∣ r , (refl , hr) ∣₁) ∣₁

  bound : (α : V ℓ) (oα : IsOrd α)
        → Σ[ D ∈ S ] ((z : S) → ⟨ Related α (fst z) ⟩ → ⟨ fst z ∈ fst D ⟩)
  bound α oα = d .fst , confine
    where
    ixL : ⟪ Lset α ⟫ → S
    ixL m = ⟪ Lset α ⟫↪ m , Lset→isL α oα (⟪ Lset α ⟫↪ m) (memOf (Lset α) m)

    d : Σ[ D ∈ S ] ((p : ⟪ Lset α ⟫ × ⟪ Lset α ⟫)
                    → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
    d = smallDom (⟪ Lset α ⟫ × ⟪ Lset α ⟫) (λ p → prʟ (ixL (fst p)) (ixL (snd p)))

    onPair : (a b : Mem (Lset α)) → ⟨ pr (fst a) (fst b) ∈ fst (d .fst) ⟩
    onPair a b = subst (λ x → ⟨ x ∈ fst (d .fst) ⟩)
      (prʟ-fst (ixL (fa .fst)) (ixL (fb .fst))
        ∙ cong₂ pr (fa .snd) (fb .snd))
      (d .snd (fa .fst , fb .fst))
      where
      fa = ∈-asFiber {a = fst a} {b = Lset α} (snd a)
      fb = ∈-asFiber {a = fst b} {b = Lset α} (snd b)

    confine : (z : S) → ⟨ Related α (fst z) ⟩ → ⟨ fst z ∈ fst (d .fst) ⟩
    confine z = PT.rec (snd (fst z ∈ fst (d .fst)))
      (λ { (_ , h₁) → PT.rec (snd (fst z ∈ fst (d .fst)))
        (λ { (a , h₂) → PT.rec (snd (fst z ∈ fst (d .fst)))
          (λ { (b , (q , _)) →
            subst (λ x → ⟨ x ∈ fst (d .fst) ⟩) (sym q) (onPair a b) }) h₂ }) h₁ })

  opaque
    tableAt : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → Bundle α
    tableAt = ∈-induction {P = λ α → ⟨ isL α ⟩ → IsOrd α → Bundle α}
      (build (PairGraphAt zero (suc zero)) refl)
      where
```

Perf: the pair graph enters as a variable with its own equation.

```agda
      build : (φ : Formula S 2) → φ ≡ PairGraphAt zero (suc zero)
            → (α : V ℓ)
            → ((δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ isL δ ⟩ → IsOrd δ → Bundle δ)
            → ⟨ isL α ⟩ → IsOrd α → Bundle α
      build φ qφ α IH hα oα = rep .fst .fst , (sep .fst .fst , (spec , rspec))
        where
        A : S
        A = α , hα

        ordOf : (c : S) → ⟨ fst c ∈ α ⟩ → IsOrd (fst c)
        ordOf c c∈ = mem-ord {A = α} oα (fst c) c∈

        bun : (c : S) → ⟨ fst c ∈ α ⟩ → Bundle (fst c)
        bun c c∈ = IH (fst c) c∈ (snd c) (ordOf c c∈)

        value : (c : S) → ⟨ fst c ∈ α ⟩ → S
        value c c∈ = bun c c∈ .snd .fst

        relOK : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) → IsRel (fst c) (value c c∈)
        relOK c c∈ = bun c c∈ .snd .snd .snd

        entry : (c : S) → ⟨ fst c ∈ α ⟩ → S
        entry c c∈ = prʟ c (value c c∈)

        below : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
              → ⟨ (value c c∈ ∷ k ∷ c ∷ []) ⊨ GraphAt zero (suc (suc zero)) ⟩
        below c c∈ k = graph-table zero (suc (suc zero))
          (value c c∈ ∷ k ∷ c ∷ []) (bun c c∈ .fst) (ordOf c c∈)
          (reads .snd) ents (reads .fst) (relOK c c∈)
          where
          reads : Domain (bun c c∈ .fst) (fst c) × Values (bun c c∈ .fst) (fst c)
          reads = table-out (fst c) (ordOf c c∈) (bun c c∈ .fst)
                    (bun c c∈ .snd .snd .fst)
          ents : Entries (bun c c∈ .fst) (fst c)
          ents e e∈ = ∣ value e e∈' , table-in (fst c) (ordOf c c∈) (bun c c∈ .fst)
                         (bun c c∈ .snd .snd .fst) e (value e e∈') e∈ (relOK e e∈') ∣₁
            where
            e∈' : ⟨ fst e ∈ α ⟩
            e∈' = oα .fst {x = fst c} {y = fst e} e∈ c∈

        holds : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) → ⟨ (entry c c∈ ∷ c ∷ []) ⊨ φ ⟩
        holds c c∈ = PairGraph-in zero (suc zero) (entry c c∈ ∷ c ∷ []) φ qφ
          (value c c∈) (prʟ-fst c (value c c∈)) (below c c∈ (entry c c∈))

        only : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
             → ⟨ (k ∷ c ∷ []) ⊨ φ ⟩ → k ≡ entry c c∈
        only c c∈ k h = PT.rec (isSetS k (entry c c∈)) read
          (PairGraph-out zero (suc zero) (k ∷ c ∷ []) φ qφ h)
          where
          read : PairOf zero (suc zero) (k ∷ c ∷ []) φ qφ → k ≡ entry c c∈
          read (r , (q , hg)) = Σ≡Prop (λ x → snd (isL x))
            ( q
            ∙ cong (pr (fst c)) (cong fst (rel-unique (fst c) r (value c c∈)
                (graph-only zero (suc (suc zero)) (r ∷ k ∷ c ∷ []) hg (ordOf c c∈))
                (relOK c c∈)))
            ∙ sym (prʟ-fst c (value c c∈)) )

        fc : (c : S) → ⟨ c ∈ˢ A ⟩
           → isContr (Σ[ k ∈ S ] ⟨ (k ∷ c ∷ []) ⊨ φ ⟩)
        fc c c∈ = mereFunct φ c ∣ entry c c∈ , (holds c c∈ , only c c∈) ∣₁

        rep : isContr (SetOf (λ z → ⋁ S (λ c → (c ∈ˢ A) ⊓ ((z ∷ c ∷ []) ⊨ φ))))
        rep = hasReplacementL A φ fc

        H : S
        H = rep .fst .fst

        spec : IsTable α H
        spec z = ⇔toPath toRec fromRec
          where
          toRec : ⟨ fst z ∈ fst H ⟩ → ⟨ Recorded α (fst z) ⟩
          toRec hz = PT.rec squash₁
            (λ { (c , (c∈ , hp)) → ∣ c , (c∈ , ∣ value c c∈
               , ( cong fst (only c c∈ z hp) ∙ prʟ-fst c (value c c∈)
                 , relOK c c∈ ) ∣₁) ∣₁ })
            (subst ⟨_⟩ (rep .fst .snd z) hz)

          fromRec : ⟨ Recorded α (fst z) ⟩ → ⟨ fst z ∈ fst H ⟩
          fromRec hz = subst ⟨_⟩ (sym (rep .fst .snd z)) (PT.map
            (λ { (c , (c∈ , hr)) → c , (c∈ , PT.rec (snd ((z ∷ c ∷ []) ⊨ φ))
              (λ { (r , (q , hs)) → subst (λ t → ⟨ (t ∷ c ∷ []) ⊨ φ ⟩)
                (sym (Σ≡Prop (λ x → snd (isL x))
                  (q ∙ cong (pr (fst c)) (cong fst
                     (rel-unique (fst c) r (value c c∈) hs (relOK c c∈)))
                     ∙ sym (prʟ-fst c (value c c∈)))))
                (holds c c∈) }) hr) }) hz)

        tvals : Values H α
        tvals = table-out α oα H spec .snd

        tents : Entries H α
        tents c c∈ = ∣ value c c∈
                    , table-in α oα H spec c (value c c∈) c∈ (relOK c c∈) ∣₁

        sep : isContr (SetOf (λ x → (x ∈ˢ bound α oα .fst)
                                  ⊓ ((x ∷ []) ⊨ Cond₀ A H)))
        sep = hasSeparationL (bound α oα .fst) (Cond₀ A H)

        rspec : IsRel α (sep .fst .fst)
        rspec z =
            (λ hz → subst ⟨_⟩ (cond₀-spec A H oα tvals tents z)
                      (subst ⟨_⟩ (sep .fst .snd z) hz .snd))
          , (λ hz → subst ⟨_⟩ (sym (sep .fst .snd z))
                      ( bound α oα .snd z hz
                      , subst ⟨_⟩ (sym (cond₀-spec A H oα tvals tents z)) hz ))

  relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
  relL α hα oα = tableAt α hα oα .snd .fst

  relL-spec : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α) → IsRel α (relL α hα oα)
  relL-spec α hα oα = tableAt α hα oα .snd .snd .snd
```

<!--en-->
## The members are the pairs the order relates
<!--zh-->
## 成员就是那个序所关联的诸对
<!--ja-->
## 要素は順序が関係づける順序対である
<!--/-->

<!--en-->
The final fill and representation lemmas specialize the generic readings to
`relL`{.Agda}, equating membership in this set with the stage comparison.
<!--zh-->
最后的填充与表示引理把通用读式专用于 `relL`{.Agda}，将对该集合的隶属与阶段比较等同起来。
<!--ja-->
最後の fill 補題と表現補題は一般的な読みを `relL`{.Agda} に特殊化し、この集合への所属を段階比較と同一視する。
<!--/-->

<!--en-->
The last two statements instantiate the readings above at the set this chapter
builds: the relation at the stage realizes the class, so it is a set the
readings apply to. Nothing new is proved here; what is fixed is which realizing
set is meant.

Nothing here is an approximation to the statement. The membership is an
equivalence, so a separation that carves with this set carves with the order
itself, and that is what the transversal chapter will do.
<!--zh-->
最后两条结论把上文的读式实例化到本章构造的集合上。阶段处的关系实现相应的类，因此该集合满足这些读式的适用条件。这里不证明新的数学事实，只确定所采用的是实现该类的哪一个集合。

此处没有任何东西是对那条陈述的近似。隶属是一条等价，故拿这个集合去作的分离，就是拿那个序本身去作的分离，而这正是横截集那一章要做的事。
<!--/-->

```agda
  module _ (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α) where
    relL-fill : (a b : Mem (Lset α)) → relOf (orderAt α oα) a b
              → ⟨ pr (fst a) (fst b) ∈ fst (relL α hα oα) ⟩
    relL-fill = rel-fill α oα (relL α hα oα) (relL-spec α hα oα)

    relL-rep : (a b : Mem (Lset α))
             → ⟨ pr (fst a) (fst b) ∈ fst (relL α hα oα) ⟩
             → relOf (orderAt α oα) a b
    relL-rep = rel-rep α oα (relL α hα oα) (relL-spec α hα oα)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The table recursion realizes every stage order as a set in `L` and exports the
four membership/comparison readings needed by later internal descriptions.
<!--zh-->
序表递归把每个阶段序实现为 `L` 中的集合，并导出后续内部描述所需的四条隶属与比较读式。
<!--ja-->
表の再帰は各段階順序を `L` 内の集合として実現し、後の内部記述が必要とする所属と比較の四つの読みを公開する。
<!--/-->

<!--en-->
`Related`{.Agda} is the class the chapter realizes, the pairs of two members of a
stage that the order there relates, with the comparison carried truncated because
it is not known to be proposition-valued, and `strict`{.Agda} takes the truncation
off again for every strict well-order at once, by splitting on trichotomy before
eliminating anything. `Realizes`{.Agda} says a set of the model realizes that
class, written as an indexed conjunction of two implications so that it is a
proposition of the model rather than an equality one universe up.
`rel-fill`{.Agda}, `rel-rep`{.Agda}, `ixRel-fill`{.Agda} and `ixRel-rep`{.Agda}
read the membership of **any** realizing set at the two shapes a member of a
stage comes in, and they are stated of any such set on purpose: the naming
mechanism has to be given the relation at the stage below the one being built,
and inside the construction that set arrives from the table with the hypothesis
that it realizes the class there, a stage before the set this chapter returns
exists.

`ApproxAt`{.Agda} and `GraphAt`{.Agda} are the approximation and its graph,
generic in the step condition, which enters as a parameter in two forms, at slots
for the graph and at constants for the separation, each with the hypothesis that
says what it means. `approx-val`{.Agda} pins every value an approximation records
by one membership induction on the argument, with no single-valuedness hypothesis
anywhere, and `approx-uniq`{.Agda} is the corollary. `graph-only`{.Agda} and
`graph-table`{.Agda} are the graph's two directions against a table.

`tableAt`{.Agda} is the construction, sealed where it is built, and it carries
**two** things at every ordinal: the table of relations below it, collected by
replacement through `mereFunct`{.Agda}, and the relation at it, separated out of a
bound. The bound is the one piece with no counterpart in the hierarchy chapter,
and one appeal suffices: the pairs of two members of a stage form a small family
of elements of `L`, so `smallDom`{.Agda} confines them all at once. `relL`{.Agda} is
the second component, and `relL-fill`{.Agda} and `relL-rep`{.Agda} are
`rel-fill`{.Agda} and `rel-rep`{.Agda} instantiated at it.

What the chapter does not do is prove the step condition's own adequacy, named
here as the two hypotheses of `Described`{.Agda}. That is not one thing but
three: the previous chapter's `StepAt`{.Agda} against the meta step, the birth
stage described in the object language, which nothing describes yet, and the code
set at a carrier that moves with the birth. Together they are what stands between
this construction and an unconditional theorem.
<!--zh-->
`Related`{.Agda} 是本章所实现的类，即一个阶段的两个成员所成的、被那里的序所关联的诸对；那次比较是带着截断陈述的，因为它并不已知是命题值的，而 `strict`{.Agda} 对每一个严格良序去掉这个截断，办法是在消去任何东西之前先按三歧分情形。`Realizes`{.Agda} 说模型的某个集合实现那个类，写成两条蕴含的指标合取，于是它是模型的一个命题，而不是高出一个宇宙的一条等式。`rel-fill`{.Agda}、`rel-rep`{.Agda}、`ixRel-fill`{.Agda} 与 `ixRel-rep`{.Agda} 把**任何**实现该类的集合的隶属，读在「阶段的成员出现时的两种形状」上；把它们陈述为「任何这样的集合」是有意为之：必须交给命名机制的，是「正在建造的那个阶段之下一级」处的关系，而在构造内部，那个集合来自表，并带着「它在那里实现那个类」这条假设，比本章交回的那个集合的存在早一个阶段。

`ApproxAt`{.Agda} 与 `GraphAt`{.Agda} 是逼近与它的图，二者对那条步进条件保持通用；该条件作为参数以两种形式出现：图的形式取诸位，分离的形式取诸常元，各自带有说明其含义的假设。`approx-val`{.Agda} 通过在实参上沿成员关系作归纳，逐一确立逼近所记录的每个取值，全程并未假设单值性；`approx-uniq`{.Agda} 是这一点的推论。`graph-only`{.Agda} 与 `graph-table`{.Agda} 是图与表之间相互转化的两个方向。

`tableAt`{.Agda} 是所需构造，并在构造处封印。它在每个序数处包含**两**项：由替换和 `mereFunct`{.Agda} 收集的较低索引关系表，以及从一个统一阶段界中分离出的当前关系。层级章没有提供这个界；这里只需证明一次：某阶段中任意两个成员组成的有序对形成 `L` 元素的小族，`smallDom`{.Agda} 因而给出包含所有这些对的单一阶段。`relL`{.Agda} 是第二个分量，`relL-fill`{.Agda} 与 `relL-rep`{.Agda} 分别是 `rel-fill`{.Agda} 与 `rel-rep`{.Agda} 在该分量上的实例。

本章没有证明那条步进条件自身的充分性，而是以 `Described`{.Agda} 的两条假设的形式指出这一点。这不是一件事，而是三件事：`StepAt`{.Agda} 对应于元层面那一步的充分性、诞生阶段在对象语言里的描述、以及在一个随诞生阶段移动的载体上的码集。这三件事合起来，正是这个构造与一条无条件定理之间尚待补足的部分。
<!--/-->
