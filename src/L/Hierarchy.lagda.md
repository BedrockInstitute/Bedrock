# The hierarchy, inside

<!--en-->
The previous chapter wrote the sentence; this chapter proves it says what it was
meant to say. `LsetGraphAt`{.Agda} describes the tower by quantifying over
approximations, and nothing so far connects it to `Lset`{.Agda}, the tower the
book actually built. Three statements make that connection, and they are the
chapter: a value the graph assigns is the meta tower's value there, the meta
tower's value is one the graph assigns, and the collection of all of them below
an ordinal is a single element of `L`.

The last of the three is the deliverable, and it is worth saying plainly what it
is for. `hierL`{.Agda} is the **internal hierarchy**: the set of pairs of an
ordinal with the tower's value at it, living inside the model rather than beside
it. That set is what an internal definition of `L` is made of, and the internal
well-order of `L` is read off it. To say "this set comes before that one" is to
say at which stage each first appears, and a stage is speakable inside the model
only once the tower is an object of the model. Nothing here defines the
well-order; everything here is what the well-order will be defined from.

One shape repeats throughout. A **table** is a set of ordered pairs; it is
*correct* on a set when every value it records below that set is the meta tower
there, and *complete* when it records a value at every argument below. Correct
and complete tables are exactly what the graph's step condition reads and what it
can be written from, so one pair of lemmas serves the elimination and the
introduction, and the rest of the chapter is those two lemmas applied at four
places.
<!--zh-->
上一章写下了那个句子；本章证明它说出了它本该说的话。`LsetGraphAt`{.Agda} 靠对诸逼近作量化来描述塔，而至此还没有任何东西把它与 `Lset`{.Agda} (本书真正造出的那座塔) 联系起来。三条陈述作出这个联系，而它们就是本章：图所指派的取值就是元层面的塔在那里的取值，元层面的塔的取值也是图所指派的一个，而它们在某个序数以下的全体是 `L` 的单独一个元素。

三者中的最后一条是交付物，而它为什么而设，值得直说。`hierL`{.Agda} 是**内部层级**：由「序数与塔在它那里的取值」所成之对的集合，住在模型**之内**、而非模型之旁。那个集合正是 `L` 的内部定义的材料，而 `L` 的内部良序就是从它上面读出来的。说「这个集合排在那个之前」，就是说各自最早出现在哪个阶段；而唯有塔成为模型的一个对象之后，阶段才在模型内部说得出口。此处不定义良序；此处的一切都是良序日后据以定义的东西。

全章重复着同一个形状。**表**是有序对之集；它在某个集合上**正确**，指它在该集合以下所记录的每个取值都是元层面的塔在那里的取值；它**完备**，指它在以下的每个实参处都记录了一个取值。正确且完备的表，恰是图的步进条件所读出的东西、也恰是它可以据以写下的东西，故一对引理同时服务于消去与引入，而本章其余部分就是这两条引理在四处的应用。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Hierarchy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; Lset; Lset-in; Lset-out; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-𝒟ₒ; extensionalL )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import L.Recursion {ℓ} lem using ( mereFunct )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; domAt-intro )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepOf; PowOK; StepAt-in; StepAt-out; StepAt-back
        ; ApproxAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step; ApproxAt-in
        ; LsetGraphAt; LsetGraph-in; LsetGraph-out; GraphOf )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

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
## What a table records
<!--zh-->
## 一张表记录了什么
<!--/-->

<!--en-->
Three conditions, one line each, because each is one direction of one statement.
`Values`{.Agda} says a value recorded at an argument below `B` is the meta tower
there. `Entries`{.Agda} says every argument below `B` has the meta tower recorded
at it. `Domain`{.Agda} says nothing outside `B` is recorded at all.

They are kept apart rather than bundled, because the two consumers need different
subsets of them. The induction over an approximation has the first two and cannot
have the third: an approximation's entries lie below its own domain, not below
whichever argument the induction currently stands at. The internal hierarchy has
all three, because it is built as exactly the set of the right pairs. Bundled,
the weaker consumer would be asked for a condition it cannot prove.

`B` is a plain set of the hierarchy here, not an element of the model. None of
the three asks for constructibility; that enters with the ordinals, one section
down.
<!--zh-->
三个条件，各一行，因为每个都是同一句陈述的一个方向。`Values`{.Agda} 说：在 `B` 以下某个实参处所记录的取值，就是元层面的塔在那里的取值。`Entries`{.Agda} 说：`B` 以下的每个实参处都记录着元层面的塔。`Domain`{.Agda} 说：`B` 以外的东西根本没有被记录。

它们分开而不打包，因为两个消费方所需的子集不同。对逼近作的那场归纳有前两个，而不可能有第三个：逼近的诸条目落在它自己的定义域以下，而不落在归纳当前所处的那个实参以下。内部层级三个都有，因为它就是按「恰好是那些对的集合」造出来的。若打包，较弱的那个消费方就会被索取一个它证不出的条件。

此处的 `B` 是层级的一个普通集合，不是模型的元素。三者都不索取可构造性；那要到下一节、随序数一同进场。
<!--/-->

```agda
Values : S → V ℓ → Type (ℓ-suc ℓ)
Values h B = (c z : S) → ⟨ fst c ∈ B ⟩
           → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → fst z ≡ Lset (fst c)

Entries : S → V ℓ → Type (ℓ-suc ℓ)
Entries h B = (c : S) → ⟨ fst c ∈ B ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ fst h ⟩

Domain : S → V ℓ → Type (ℓ-suc ℓ)
Domain h B = (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩
```

<!--en-->
## The step, against the tower
<!--zh-->
## 那一步，对着塔
<!--/-->

<!--en-->
This is the chapter's engine, and both halves of it come out of the same three
private lines. The step at an argument `b` collects, over the arguments `c` below
`b` and the values `w` recorded there, the members of the definable powerset of
`w`. The meta tower at `b` collects the same thing with `Lset c` in place of `w`.
So if the table is correct the two have the same members, and that is the whole
mathematics: `step-Lset`{.Agda} reads a satisfied step and gets the tower back,
`step-table`{.Agda} writes the step from the tower.

The previous chapter's side condition is discharged here, once, for both
directions. `PowOK`{.Agda} asks that the definable powerset of every recorded
value be an element of `L`; a recorded value is the tower at an argument below
`B`, that argument is an ordinal because `B` is one, and the definable powerset
of a stage is constructible. So correctness plus a single ordinality hypothesis
is all the step ever needs, and neither reading carries the condition in its
statement.

The two directions are named apart because they are used apart. Going up is the
definable powerset of a recorded value sitting inside the tower at `B`, which is
`Lset-in`{.Agda}. Coming down is the tower's own decomposition,
`Lset-out`{.Agda}, followed by naming the ordinal it produces as an element of
the model, which transitivity of the class supplies for free.
<!--zh-->
这是本章的引擎，而它的两半都出自同样三行私有代码。实参 `b` 处的那一步，沿 `b` 以下的诸实参 `c` 与在其处所记录的诸取值 `w`，收集 `w` 的可定义幂集的诸成员。元层面的塔在 `b` 处收集的是同一样东西，只是把 `w` 换成 `Lset c`。故若表是正确的，两者就有同样的成员，而全部数学仅此而已：`step-Lset`{.Agda} 读一个被满足的步进、把塔取回来，`step-table`{.Agda} 则由塔写出那一步。

上一章那个旁条件在此处一次性地、为两个方向一并解除。`PowOK`{.Agda} 索取的是：每个被记录的取值，其可定义幂集是 `L` 的元素；而被记录的取值是塔在 `B` 以下某个实参处的值，该实参因 `B` 是序数而是序数，而阶段的可定义幂集可构造。故那一步所需的全部，就是正确性加上单独一条序数性假设，而两种读法的陈述里都不带那个条件。

两个方向分开命名，因为它们分开使用。向上是「被记录取值的可定义幂集落在 `B` 处的塔里面」，那就是 `Lset-in`{.Agda}。向下是塔自家的分解 `Lset-out`{.Agda}，随后把它产出的那个序数点名为模型的元素，而这由类的传递性免费供上。
<!--/-->

```agda
module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) where
  private
    ok : IsOrd (fst (lookup b γ)) → Values (lookup f γ) (fst (lookup b γ))
       → PowOK b f γ
    ok ob vals c z rec = subst (λ u → ⟨ isL (𝒟ₒ u) ⟩)
      (sym (vals c z (rec .fst) (rec .snd)))
      (isL-𝒟ₒ (fst c) (mem-ord {A = fst (lookup b γ)} ob (fst c) (rec .fst)))

    below : IsOrd (fst (lookup b γ)) → Entries (lookup f γ) (fst (lookup b γ))
          → (z : S)
          → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ fst z ∈ 𝒟ₒ (Lset δ) ⟩)
          → StepOf b f γ z
    below ob ents z (δ , (δ∈ , hz)) =
      d , (LsetS δ oδ , ((δ∈ , ents d δ∈) , hz))
      where
      oδ : IsOrd δ
      oδ = mem-ord {A = fst (lookup b γ)} ob δ δ∈
      d : S
      d = δ , isL-trans {x = fst (lookup b γ)} {y = δ} δ∈ (lookup b γ .snd)

    above : Values (lookup f γ) (fst (lookup b γ)) → (z : S) → StepOf b f γ z
          → ⟨ fst z ∈ Lset (fst (lookup b γ)) ⟩
    above vals z (c , (w , (rec , hz))) =
      Lset-in (fst (lookup b γ)) (fst c) (fst z) (rec .fst)
        (subst (λ u → ⟨ fst z ∈ 𝒟ₒ u ⟩) (vals c w (rec .fst) (rec .snd)) hz)

  step-Lset : ⟨ γ ⊨ StepAt v b f ⟩ → IsOrd (fst (lookup b γ))
            → Values (lookup f γ) (fst (lookup b γ))
            → Entries (lookup f γ) (fst (lookup b γ))
            → fst (lookup v γ) ≡ Lset (fst (lookup b γ))
  step-Lset h ob vals ents =
    extensionalV {a = fst (lookup v γ)} {b = Lset (fst (lookup b γ))} pt
    where
    fwd : (x : V ℓ) → ⟨ x ∈ fst (lookup v γ) ⟩
        → ⟨ x ∈ Lset (fst (lookup b γ)) ⟩
    fwd x hx = PT.rec (snd (x ∈ Lset (fst (lookup b γ)))) (above vals z)
      (StepAt-out v b f γ h (ok ob vals) z hx)
      where
      z : S
      z = x , isL-trans {x = fst (lookup v γ)} {y = x} hx (lookup v γ .snd)

    bwd : (x : V ℓ) → ⟨ x ∈ Lset (fst (lookup b γ)) ⟩
        → ⟨ x ∈ fst (lookup v γ) ⟩
    bwd x hx = PT.rec (snd (x ∈ fst (lookup v γ))) put
      (Lset-out (fst (lookup b γ)) x hx)
      where
      z : S
      z = x , isL-trans {x = Lset (fst (lookup b γ))} {y = x} hx
                (LsetS (fst (lookup b γ)) ob .snd)
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
          → ⟨ x ∈ fst (lookup v γ) ⟩
      put s = StepAt-back v b f γ h (ok ob vals) z (below ob ents z s)

    pt : (x : V ℓ) → (x ∈ fst (lookup v γ)) ≡ (x ∈ Lset (fst (lookup b γ)))
    pt x = ⇔toPath (fwd x) (bwd x)

  step-table : IsOrd (fst (lookup b γ))
             → Values (lookup f γ) (fst (lookup b γ))
             → Entries (lookup f γ) (fst (lookup b γ))
             → fst (lookup v γ) ≡ Lset (fst (lookup b γ))
             → ⟨ γ ⊨ StepAt v b f ⟩
  step-table ob vals ents q = StepAt-in v b f γ (ok ob vals) into back
    where
    into : (z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁
    into z hz = PT.map (below ob ents z)
      (Lset-out (fst (lookup b γ)) (fst z)
        (subst (λ u → ⟨ fst z ∈ u ⟩) q hz))

    back : (z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩
    back z s = subst (λ u → ⟨ fst z ∈ u ⟩) (sym q) (above vals z s)
```

<!--en-->
## Every value an approximation records
<!--zh-->
## 逼近所记录的每个取值
<!--/-->

<!--en-->
One induction, on the argument, in the meta-language, with the approximation and
its domain held fixed. The motive says: whatever value the approximation records
at this argument is the meta tower there. It quantifies over **all** recorded
values, and that is why single-valuedness is nowhere a hypothesis. Two values
recorded at one argument are both pinned to the same tower value, so they are
equal; the previous chapter's ruling that the approximation carries no
single-valuedness conjunct is collected here, as `approx-uniq`{.Agda}, in three
lines.

The step of the induction is `step-Lset`{.Agda} at the recorded value.
Correctness below the argument *is* the induction hypothesis, verbatim.
Completeness below the argument is where the domain hypothesis is spent: an
argument below this one is below the approximation's domain, because the domain
is an ordinal and ordinals are transitive; the approximation therefore has a
value there; and the induction hypothesis identifies it with the tower's. That
value is produced only merely, which is enough, because what is being proved of
it is a membership.
<!--zh-->
一次归纳，在实参上，在元语言中，逼近与它的定义域保持固定。动机说：逼近在这个实参处所记录的任何取值，都是元层面的塔在那里的取值。它对**一切**被记录的取值作量化，而这正是单值性在任何地方都不作为假设的原因。在同一个实参处记录的两个取值都被钉在同一个塔值上，故两者相等；上一章那条「逼近不带单值性合取项」的裁定，在此处以 `approx-uniq`{.Agda} 之名、用三行收取。

归纳的步进就是 `step-Lset`{.Agda} 施于被记录的那个取值。实参以下的正确性**就是**归纳假设，一字不差。实参以下的完备性则是那条定义域假设被花掉之处：比这个实参更低的实参落在逼近的定义域以下，因为定义域是序数、而序数传递；逼近于是在那里有取值；而归纳假设把它与塔的取值认同。那个取值只是「仅仅」被拿出来的，而这已经够了，因为要对它证的是一条隶属关系。
<!--/-->

```agda
module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
  private
    Value : V ℓ → Type (ℓ-suc ℓ)
    Value u = ⟨ isL u ⟩ → (z : S)
            → ⟨ pr u (fst z) ∈ fst (lookup f γ) ⟩ → fst z ≡ Lset u

  approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
             → (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩
             → fst z ≡ Lset (fst x)
  approx-val h oa x = ∈-induction {P = Value} go (fst x) (snd x)
    where
    go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
    go u IH hu z p = step-Lset zero (suc zero) (sh2 f) (z ∷ d ∷ γ)
      (ApproxAt-step f a γ h d z p) ou vals ents
      where
      d : S
      d = u , hu
      u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
      u∈a = ApproxAt-dom f a γ h d z p
      ou : IsOrd u
      ou = mem-ord {A = fst (lookup a γ)} oa u u∈a
      vals : Values (lookup f γ) u
      vals c y c∈ q = IH (fst c) c∈ (snd c) y q
      ents : Entries (lookup f γ) u
      ents c c∈ = PT.rec
        (snd (pr (fst c) (Lset (fst c)) ∈ fst (lookup f γ))) named
        (ApproxAt-value f a γ h c (oa .fst {x = u} {y = fst c} c∈ u∈a))
        where
        named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst (lookup f γ) ⟩
              → ⟨ pr (fst c) (Lset (fst c)) ∈ fst (lookup f γ) ⟩
        named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst (lookup f γ) ⟩)
          (IH (fst c) c∈ (snd c) y q) q

  approx-uniq : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
              → (x y z : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
              → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩ → y ≡ z
  approx-uniq h oa x y z p q = Σ≡Prop (λ u → snd (isL u))
    (approx-val h oa x y p ∙ sym (approx-val h oa x z q))
```

<!--en-->
## The graph holds of nothing else
<!--zh-->
## 图对别的什么都不成立
<!--/-->

<!--en-->
The graph says there merely is an approximation on the argument whose step at the
argument is the value. Read it and everything is already in hand: unpack the
approximation, take correctness from `approx-val`{.Agda}, take completeness from
`ApproxAt-value`{.Agda} composed with `approx-val`{.Agda} again, and apply
`step-Lset`{.Agda} one last time. The conclusion is that the graph **determines**
its value: whatever satisfies it at an ordinal is the meta tower there.

The reading stands at variable slots, and that is not decoration. Its two
consumers instantiate it at two different concrete environments, and a statement
made at either would have to be converted to the other through a satisfaction
carrying the whole tower description inside it.
<!--zh-->
图说：仅仅存在实参上的一个逼近，使得它在该实参处的那一步就是那个取值。把它读出来，一切都已在手：拆开逼近，正确性取自 `approx-val`{.Agda}，完备性取自 `ApproxAt-value`{.Agda} 再复合一次 `approx-val`{.Agda}，然后最后一次应用 `step-Lset`{.Agda}。结论是：图**确定**它的取值，凡在某个序数处满足它者，都是元层面的塔在那里的取值。

这条读式站在变元位上，而这不是装饰。它的两个消费方在两个不同的具体环境上把它实例化，而陈述在其中任一处，都得经由一个内部装着整条塔描述的满足关系，转换到另一处去。
<!--/-->

```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
            → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
  Lset-only h ob = PT.rec
    (setIsSet (fst (lookup w γ)) (Lset (fst (lookup b γ)))) read
    (LsetGraph-out w b γ h)
    where
    read : GraphOf w b γ → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
    read (f , (ha , hs)) =
      step-Lset (suc w) (suc b) zero (f ∷ γ) hs ob vals ents
      where
      vals : Values f (fst (lookup b γ))
      vals c z _ p = approx-val zero (suc b) (f ∷ γ) ha ob c z p
      ents : Entries f (fst (lookup b γ))
      ents c c∈ = PT.rec (snd (pr (fst c) (Lset (fst c)) ∈ fst f)) named
        (ApproxAt-value zero (suc b) (f ∷ γ) ha c c∈)
        where
        named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst f ⟩
              → ⟨ pr (fst c) (Lset (fst c)) ∈ fst f ⟩
        named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst f ⟩)
          (approx-val zero (suc b) (f ∷ γ) ha ob c y q) q
```

<!--en-->
## A table is an approximation
<!--zh-->
## 表就是逼近
<!--/-->

<!--en-->
The converse direction needs a witness, and a correct, complete table is one.
`graph-table`{.Agda} turns such a table into a satisfaction of the graph by
filling in the previous chapter's projections and doing nothing else.

The domain conjunct is `Domain`{.Agda} one way and `Entries`{.Agda} the other.
The step conjunct at a recorded pair is `step-table`{.Agda} at that argument,
whose correctness and completeness are the table's own restricted below it; the
restriction is where transitivity of the ordinal is spent for the second and last
time. The value the graph is asked about is the step at the whole argument, which
is `step-table`{.Agda} once more. So one table serves both conjuncts of "is an
approximation" and the outer step as well.
<!--zh-->
反方向需要一个见证，而一张正确且完备的表就是。`graph-table`{.Agda} 把这样一张表变成对图的满足，办法是填上上一章的诸投影，此外什么也不做。

定义域那个合取项，一个方向是 `Domain`{.Agda}、另一个方向是 `Entries`{.Agda}。在某个被记录的对上，步进那个合取项是 `step-table`{.Agda} 施于那个实参，其正确性与完备性就是这张表自身在它以下的限制；那次限制正是序数的传递性第二次、也是最后一次被花掉之处。图所问的那个取值，是整个实参处的那一步，那又是一次 `step-table`{.Agda}。故一张表同时服务于「是一个逼近」的两个合取项，以及外层的那一步。
<!--/-->

```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  graph-table : (h : S) → IsOrd (fst (lookup b γ))
              → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
              → Domain h (fst (lookup b γ))
              → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
              → ⟨ γ ⊨ LsetGraphAt w b ⟩
  graph-table h ob vals ents dom q = LsetGraph-in w b γ h approx
    (step-table (suc w) (suc b) zero (h ∷ γ) ob vals ents q)
    where
    onDom : (c : S)
          → (⟨ ⋁ S (λ y → pr (fst c) (fst y) ∈ fst h) ⟩
             → ⟨ fst c ∈ fst (lookup b γ) ⟩)
          × (⟨ fst c ∈ fst (lookup b γ) ⟩
             → ⟨ ⋁ S (λ y → pr (fst c) (fst y) ∈ fst h) ⟩)
    onDom c = (λ hy → PT.rec (snd (fst c ∈ fst (lookup b γ))) named hy)
            , (λ c∈ → ∣ LsetS (fst c) (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈)
                     , ents c c∈ ∣₁)
      where
      named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst h ⟩
            → ⟨ fst c ∈ fst (lookup b γ) ⟩
      named (y , p) = dom c y p

    onStep : (c y : S) → ⟨ pr (fst c) (fst y) ∈ fst h ⟩
           → ⟨ (y ∷ c ∷ h ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
    onStep c y p = step-table zero (suc zero) (suc (suc zero)) (y ∷ c ∷ h ∷ γ)
      oc vals' ents' (vals c y c∈ p)
      where
      c∈ : ⟨ fst c ∈ fst (lookup b γ) ⟩
      c∈ = dom c y p
      oc : IsOrd (fst c)
      oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈
      vals' : Values h (fst c)
      vals' e t _ r = vals e t (dom e t r) r
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
<!--/-->

<!--en-->
The table has to be **built**, and the only builder is replacement, which asks
for a graph. This is that graph, and it is the previous chapter's packaged: the
value at an argument is the ordered pair of the argument with the tower's value
there. One existential binds the tower's value, the pair reader equates the entry
with the pair, and the tower graph says the bound value is the right one.

Its two readings take the sentence as a **parameter**, with the sentence's own
equation as a hypothesis, `refl`{.Agda} at the single call site. That is the
shape rule for a frame generic in a construction, and this chapter is where it
was measured on a sentence rather than on a constructor: written directly against
the closed sentence, the readings cost 85 seconds, because Agda decides the
equality of two spellings of one formula by normalizing a satisfaction that
carries the entire definable-powerset description inside it. With the sentence a
variable there is nothing to normalize.
<!--zh-->
表必须被**造出来**，而唯一的建造者是替换，而替换索要一个图。这就是那个图，它是上一章那个图的打包版：某个实参处的取值，是「该实参与塔在那里的取值」所成的有序对。一个存在量词把塔的取值绑住，对读式把那个条目与那个对等同起来，而塔的图说被绑住的那个取值是对的。

它的两种读法把那个句子取作**参数**，并把该句子自己的等式取作假设，在唯一的调用处是 `refl`{.Agda}。这就是「对某个构造保持通用的框架」的形状规矩，而本章正是它在一个句子而非一个构造子上被测出来的地方：直接对着那个闭句子写，两条读法花掉 85 秒，因为 Agda 判定「同一条公式的两种写法」是否相等的办法，是把一个内部装着整条可定义幂集描述的满足关系正规化。句子一旦是变元，就没有什么可正规化的了。
<!--/-->

```agda
PairGraphAt : ∀ {n} → Fin n → Fin n → Formula S n
PairGraphAt e c = ∃̇ (prAtL (suc e) (suc c) zero ∧̇ LsetGraphAt zero (suc c))

module _ {n : ℕ} (e c : Fin n) (γ : S ^ n)
         (φ : Formula S n) (qφ : φ ≡ PairGraphAt e c) where
  PairOf : Type (ℓ-suc ℓ)
  PairOf = Σ[ z ∈ S ] ( (fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z))
                      × ⟨ (z ∷ γ) ⊨ LsetGraphAt zero (suc c) ⟩ )

  private
    readPair : Σ[ z ∈ S ] ⟨ (z ∷ γ) ⊨
                 (prAtL (suc e) (suc c) zero ∧̇ LsetGraphAt zero (suc c)) ⟩
             → PairOf
    readPair (z , (hq , hg)) =
      z , (subst ⟨_⟩ (prAtL-adequate (suc e) (suc c) zero (z ∷ γ)) hq , hg)

  PairGraph-in : (z : S) → fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z)
               → ⟨ (z ∷ γ) ⊨ LsetGraphAt zero (suc c) ⟩
               → ⟨ γ ⊨ φ ⟩
  PairGraph-in z q hg = subst (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym qφ)
    ∣ z , (subst ⟨_⟩
      (sym (prAtL-adequate (suc e) (suc c) zero (z ∷ γ))) q , hg) ∣₁

  PairGraph-out : ⟨ γ ⊨ φ ⟩ → ∥ PairOf ∥₁
  PairGraph-out h = PT.map readPair (subst (λ ψ → ⟨ γ ⊨ ψ ⟩) qφ h)
```

<!--en-->
## The internal hierarchy
<!--zh-->
## 内部层级
<!--/-->

<!--en-->
`Recorded`{.Agda} names the class the internal hierarchy realizes: the pairs of
an ordinal below `α` with the tower's value there, and nothing besides.
`IsHier`{.Agda} says a set of the model realizes it, member for member. That is a
**membership equivalence** and not a one-directional collection, for the reason
the previous chapter recorded: said one way it would not say the collection holds
*only* such pairs, the existence claim would then not be a proposition, and every
step below would need an internal function-extensionality lemma to pass from two
collections to one. Said as an equivalence, two realizers are equal by
extensionality in `L`, `HierOf`{.Agda} is a proposition, and so is the motive of
the induction that builds it.

The two readings stand at a **variable** collection reached by its specification,
never at the sealed construction. Reading out is injectivity of the pair applied
to a member; reading in exhibits the pair as an element of the model, which the
model's own pairing supplies, and needs ordinality of the argument in order to
name the value at all.

Then the construction, one membership induction on the ordinal. At `α` the pair
graph is functional at every argument below: the induction hypothesis hands over
the hierarchy up to that argument, `graph-table`{.Agda} turns it into a
satisfaction of the tower graph, and `Lset-only`{.Agda} says nothing else
satisfies it. Replacement collects the pairs, and the collected set realizes the
class in both directions through those same two facts. Ordinality of each
argument is taken from `mem-ord`{.Agda} **untruncated**, which is why no
decidable-ordinality branch appears anywhere on this route, and the functionality
obligation is filled through `mereFunct`{.Agda}, because the value at an argument
is a construction rather than a decision.

The construction is sealed where it is built. Everything below reaches it through
its specification, and no induction is ever unfolded into a conversion.
<!--zh-->
`Recorded`{.Agda} 为内部层级所实现的那个类命名：「`α` 以下的序数与塔在它那里的取值」所成的诸对，此外别无他物。`IsHier`{.Agda} 说模型的某个集合逐成员地实现它。这是一条**隶属等价**、而不是一个单向的收集，理由上一章已经记下：若那样说，它就没有说这个收集**只**持有那样的对，那条存在性断言于是不是命题，而其下的每一步都会需要一条内部的函数外延性引理，才能从两个收集走到一个。作为等价说出来，两个实现者由 `L` 中的外延性而相等，`HierOf`{.Agda} 是命题，而造出它的那场归纳的动机也是命题。

两条读式都站在一个**变元**收集上、经它的规格抵达，绝不站在被封印的构造上。读出来是对某个成员施用对的单射性；读进去则是把那个对作为模型的元素拿出来，而这由模型自家的配对供上，并且需要实参的序数性，否则那个取值根本点不出名字。

然后是构造，在序数上作一次沿成员的归纳。在 `α` 处，成对的那个图在以下的每个实参上都是函数性的：归纳假设交出直到那个实参为止的层级，`graph-table`{.Agda} 把它变成对塔之图的满足，而 `Lset-only`{.Agda} 说别的东西都不满足它。替换把那些对收拢起来，而收拢所得的集合经同样这两条事实、在两个方向上实现那个类。每个实参的序数性取自 `mem-ord`{.Agda} 且**不加截断**，这正是这条路线上任何地方都不出现「序数性可判定」分支的原因；而函数性那笔债经 `mereFunct`{.Agda} 偿付，因为某个实参处的取值是一个构造、而不是一次判定。

构造在它被造出之处封印。其下的一切都经它的规格抵达，而没有任何一场归纳会被展开成一次转换。
<!--/-->

```agda
Recorded : V ℓ → V ℓ → Ω
Recorded B z = ⋁ S (λ c → (fst c ∈ B)
  ⊓ ((z ≡ pr (fst c) (Lset (fst c))) , setIsSet z (pr (fst c) (Lset (fst c)))))

IsHier : V ℓ → S → Type (ℓ-suc (ℓ-suc ℓ))
IsHier B h = (z : S) → (fst z ∈ fst h) ≡ Recorded B (fst z)

HierOf : V ℓ → Type (ℓ-suc (ℓ-suc ℓ))
HierOf B = Σ[ h ∈ S ] IsHier B h

hier-unique : (B : V ℓ) (h k : S) → IsHier B h → IsHier B k → h ≡ k
hier-unique B h k sp sq = extensionalL (λ z → sp z ∙ sym (sq z))

isPropHierOf : (B : V ℓ) → isProp (HierOf B)
isPropHierOf B (h , sp) (k , sq) = Σ≡Prop
  (λ m → isPropΠ (λ z → isSetHProp (fst z ∈ fst m) (Recorded B (fst z))))
  (hier-unique B h k sp sq)

module _ (B : V ℓ) (oB : IsOrd B) (h : S) (sp : IsHier B h) where
  hier-out : (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩
           → ⟨ fst c ∈ B ⟩ × (fst z ≡ Lset (fst c))
  hier-out c z p = PT.rec
    (isProp× (snd (fst c ∈ B)) (setIsSet (fst z) (Lset (fst c)))) read
    (subst ⟨_⟩ (sp k) p)
    where
    k : S
    k = pr (fst c) (fst z)
      , isL-trans {x = fst h} {y = pr (fst c) (fst z)} p (h .snd)
    read : Σ[ d ∈ S ] (⟨ fst d ∈ B ⟩
             × (pr (fst c) (fst z) ≡ pr (fst d) (Lset (fst d))))
         → ⟨ fst c ∈ B ⟩ × (fst z ≡ Lset (fst c))
    read (d , (d∈ , eq)) =
        subst (λ t → ⟨ t ∈ B ⟩) (sym (pr-inj eq .fst)) d∈
      , (pr-inj eq .snd ∙ cong Lset (sym (pr-inj eq .fst)))

  hier-in : (c : S) → ⟨ fst c ∈ B ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ fst h ⟩
  hier-in c c∈ = subst (λ t → ⟨ t ∈ fst h ⟩) (prʟ-fst c (LsetS (fst c) oc))
    (subst ⟨_⟩ (sym (sp k)) ∣ c , (c∈ , prʟ-fst c (LsetS (fst c) oc)) ∣₁)
    where
    oc : IsOrd (fst c)
    oc = mem-ord {A = B} oB (fst c) c∈
    k : S
    k = prʟ c (LsetS (fst c) oc)

opaque
  hierAt : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → HierOf α
  hierAt = ∈-induction {P = λ α → ⟨ isL α ⟩ → IsOrd α → HierOf α}
    (build (PairGraphAt zero (suc zero)) refl)
    where
    -- perf: the pair graph enters as a variable with its own equation; spelled
    -- out as the closed sentence, three conversions cost 85 s between them
    build : (φ : Formula S 2) → φ ≡ PairGraphAt zero (suc zero)
          → (α : V ℓ)
          → ((δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ isL δ ⟩ → IsOrd δ → HierOf δ)
          → ⟨ isL α ⟩ → IsOrd α → HierOf α
    build φ qφ α IH hα oα = r .fst .fst , spec
      where
      A : S
      A = α , hα

      value : (c : S) → ⟨ fst c ∈ α ⟩ → S
      value c c∈ = LsetS (fst c) (mem-ord {A = α} oα (fst c) c∈)

      entry : (c : S) → ⟨ fst c ∈ α ⟩ → S
      entry c c∈ = prʟ c (value c c∈)

      below : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
            → ⟨ (value c c∈ ∷ k ∷ c ∷ []) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
      below c c∈ k = graph-table zero (suc (suc zero)) (value c c∈ ∷ k ∷ c ∷ [])
        (hc .fst) oc
        (λ d z _ p → hier-out (fst c) oc (hc .fst) (hc .snd) d z p .snd)
        (hier-in (fst c) oc (hc .fst) (hc .snd))
        (λ d z p → hier-out (fst c) oc (hc .fst) (hc .snd) d z p .fst)
        refl
        where
        oc : IsOrd (fst c)
        oc = mem-ord {A = α} oα (fst c) c∈
        hc : HierOf (fst c)
        hc = IH (fst c) c∈ (snd c) oc

      holds : (c : S) (c∈ : ⟨ fst c ∈ α ⟩)
            → ⟨ (entry c c∈ ∷ c ∷ []) ⊨ φ ⟩
      holds c c∈ = PairGraph-in zero (suc zero) (entry c c∈ ∷ c ∷ []) φ qφ
        (value c c∈) (prʟ-fst c (value c c∈)) (below c c∈ (entry c c∈))

      only : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
           → ⟨ (k ∷ c ∷ []) ⊨ φ ⟩ → k ≡ entry c c∈
      only c c∈ k h = PT.rec (isSetS k (entry c c∈)) read
        (PairGraph-out zero (suc zero) (k ∷ c ∷ []) φ qφ h)
        where
        read : PairOf zero (suc zero) (k ∷ c ∷ []) φ qφ → k ≡ entry c c∈
        read (z , (q , hg)) = Σ≡Prop (λ t → snd (isL t))
          ( q
          ∙ cong (pr (fst c))
              (Lset-only zero (suc (suc zero)) (z ∷ k ∷ c ∷ []) hg
                (mem-ord {A = α} oα (fst c) c∈))
          ∙ sym (prʟ-fst c (value c c∈)) )

      fc : (c : S) → ⟨ c ∈ˢ A ⟩
         → isContr (Σ[ k ∈ S ] ⟨ (k ∷ c ∷ []) ⊨ φ ⟩)
      fc c c∈ = mereFunct φ c ∣ entry c c∈ , (holds c c∈ , only c c∈) ∣₁

      r : isContr (SetOf (λ z → ⋁ S (λ c → (c ∈ˢ A) ⊓ ((z ∷ c ∷ []) ⊨ φ))))
      r = hasReplacementL A φ fc

      spec : IsHier α (r .fst .fst)
      spec z = ⇔toPath toRec fromRec
        where
        toRec : ⟨ fst z ∈ fst (r .fst .fst) ⟩ → ⟨ Recorded α (fst z) ⟩
        toRec hz = PT.rec squash₁ conv (subst ⟨_⟩ (r .fst .snd z) hz)
          where
          conv : Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩ × ⟨ (z ∷ c ∷ []) ⊨ φ ⟩)
               → ⟨ Recorded α (fst z) ⟩
          conv (c , (c∈ , hp)) = ∣ c , (c∈ , cong fst (only c c∈ z hp)
                                            ∙ prʟ-fst c (value c c∈)) ∣₁

        fromRec : ⟨ Recorded α (fst z) ⟩ → ⟨ fst z ∈ fst (r .fst .fst) ⟩
        fromRec hz = subst ⟨_⟩ (sym (r .fst .snd z)) (PT.map conv hz)
          where
          conv : Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩
                   × (fst z ≡ pr (fst c) (Lset (fst c))))
               → Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩ × ⟨ (z ∷ c ∷ []) ⊨ φ ⟩)
          conv (c , (c∈ , eq)) = c , (c∈
            , subst (λ t → ⟨ (t ∷ c ∷ []) ⊨ φ ⟩) (sym zeq) (holds c c∈))
            where
            zeq : z ≡ entry c c∈
            zeq = Σ≡Prop (λ t → snd (isL t))
              (eq ∙ sym (prʟ-fst c (value c c∈)))

hierL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
hierL α hα oα = hierAt α hα oα .fst

hierL-spec : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α)
           → IsHier α (hierL α hα oα)
hierL-spec α hα oα = hierAt α hα oα .snd
```

<!--en-->
## The tower satisfies the graph
<!--zh-->
## 塔满足那个图
<!--/-->

<!--en-->
The last statement is one line, because the internal hierarchy at an ordinal is a
correct, complete table on it and `graph-table`{.Agda} was written for exactly
that. With `Lset-only`{.Agda} beside it, the graph and the meta tower now agree
in both directions at every ordinal, which is what the chapter was for.
<!--zh-->
最后一条陈述只有一行，因为某个序数处的内部层级，就是那个序数上一张正确且完备的表，而 `graph-table`{.Agda} 正是为此而写。与 `Lset-only`{.Agda} 并置，图与元层面的塔如今在每个序数处、在两个方向上都一致，而这正是本章的目的。
<!--/-->

```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  Lset-defines : IsOrd (fst (lookup b γ))
               → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
               → ⟨ γ ⊨ LsetGraphAt w b ⟩
  Lset-defines ob q = graph-table w b γ H ob
    (λ c z _ p → hier-out (fst (lookup b γ)) ob H sp c z p .snd)
    (hier-in (fst (lookup b γ)) ob H sp)
    (λ c z p → hier-out (fst (lookup b γ)) ob H sp c z p .fst)
    q
    where
    H : S
    H = hierL (fst (lookup b γ)) (lookup b γ .snd) ob
    sp : IsHier (fst (lookup b γ)) H
    sp = hierL-spec (fst (lookup b γ)) (lookup b γ .snd) ob
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`approx-val`{.Agda} pins every value an approximation records to the meta tower,
by one membership induction on the argument, with no single-valuedness hypothesis
anywhere; `approx-uniq`{.Agda} is the corollary the previous chapter left to be
collected here. `Lset-only`{.Agda} and `Lset-defines`{.Agda} are the graph's two
directions against the tower, and `hierL`{.Agda} is what the second is built
from: the internal hierarchy, an element of `L` whose members are exactly the
pairs of an ordinal with the tower's value at it, unique because its
specification is a membership equivalence, and sealed where it is built.

Nothing here recomputes the last chapter. The step's three readings, the
approximation's four projections and the graph's two are used as delivered; what
is added is the bridge to the meta tower, and the bridge is two lemmas,
`step-Lset`{.Agda} and `step-table`{.Agda}, applied four times between them.

Two measurements are worth keeping, and both are about a name rather than about
mathematics. Letting the pair graph enter as a **variable** carrying its own
equation, rather than as the closed sentence it will be instantiated to, is worth
85 seconds; the mechanism is the one the last two chapters met, that two
spellings of one formula are compared by normalizing a satisfaction with the
whole definable-powerset description inside it. And the set argument of
`mem-ord`{.Agda} has to be given **explicitly** at every use:
`IsOrd`{.Agda} unfolds to a quantified membership, so nothing in the hypothesis
determines the set it is about, and left implicit the chapter does not close at
all.

What the chapter delivers is the object the next part consumes. `L` now has a
name for its own tower, and a well-order of `L` is read off a tower: one set
before another when it appears at an earlier stage, or at the same stage under an
earlier formula. The first half of that is now sayable inside the model.
<!--zh-->
`approx-val`{.Agda} 把逼近所记录的每个取值都钉在元层面的塔上，靠的是在实参上的一次沿成员的归纳，任何地方都没有单值性假设；`approx-uniq`{.Agda} 则是上一章留待此处收取的那条推论。`Lset-only`{.Agda} 与 `Lset-defines`{.Agda} 是图对着塔的两个方向，而 `hierL`{.Agda} 是后者据以造出的东西：内部层级，`L` 的一个元素，其成员恰是「序数与塔在它那里的取值」所成的诸对；它唯一，因为它的规格是一条隶属等价；它在被造出之处封印。

此处没有重算上一章。那一步的三种读法、逼近的四个投影、图的两条读式，都按交付时的原样使用；新添的是通往元层面的塔的那座桥，而这座桥就是两条引理 `step-Lset`{.Agda} 与 `step-table`{.Agda}，两者合计用了四次。

有两次测量值得留存，而两次都关乎一个名字、无关数学。让成对的那个图以**变元**身份进场、随身带着它自己的等式，而不是以「它将被实例化成的那个闭句子」的身份进场，价值 85 秒；机制就是前两章遇上的那一个：同一条公式的两种写法，是靠把一个内部装着整条可定义幂集描述的满足关系正规化来比较的。以及，`mem-ord`{.Agda} 的那个集合实参必须在每次使用时**显式**给出：`IsOrd`{.Agda} 展开成一条带量词的隶属关系，故那条假设里没有任何东西能确定它所谈的集合，若留作隐式，本章根本检查不完。

本章交付的是下一部所消费的那个对象。`L` 如今有了指称它自家那座塔的名字，而 `L` 的良序正是从一座塔上读出来的：一个集合排在另一个之前，当它出现在更早的阶段，或在同一阶段而由更早的公式给出。这句话的前半，如今在模型内部说得出口了。
<!--/-->
