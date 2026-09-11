<!--en-->
# The constructible hierarchy inside L

A first-order graph inside `L` records the external constructible hierarchy up to a chosen ordinal. Tables are compared with the external tower, shown functional and exact, then collected into a constructible set whose members are precisely the earlier stages.
<!--zh-->
# L 内部的可构造层级

`L` 内的一阶图记录外部的可构造层级，直至给定序数。表中的值与外部层级逐一比较，并被证明具有函数性且精确；随后这些表被收集成一个可构造集合，其成员恰是此前各层。
<!--ja-->
# L の内部における構成可能階層

`L` 内の一階のグラフは、指定した順序数までの外部の構成可能階層を記録する。表を外部の階層と比較して関数的かつ正確であることを示し、それらを、以前の段階をちょうど要素に持つ構成可能集合へまとめる。
<!--/-->

<!--en-->
The last of the three states the purpose of the construction. `hierL`{.Agda} is the **internal hierarchy**: the set of ordered pairs of an ordinal with the tower's value at it, an object inside the model rather than beside it. This set supplies the material for an internal definition of `L`, and the internal well-order of `L` is read off it. The stage at which each set first appears supplies the first comparison key, and such a stage can be expressed inside the model only once the tower is an object of the model. This section does not define the well-order; it provides the data from which the well-order will be defined.

One pattern repeats throughout the chapter. A **table** is a set of ordered pairs; it is *correct* on a set when every value it records below that set is the meta tower there, and *complete* when it records a value at every argument below. Correct and complete tables are exactly what the graph's step condition reads and what it can be written from, so one pair of lemmas serves elimination and introduction, and the rest of the chapter applies those two lemmas at four places.
<!--zh-->
三项结果中的最后一项说明了这一构造的目的。`hierL`{.Agda} 是**内部层级**，即由序数及塔在该序数处的取值组成的有序对集合；它是模型**内部**的对象。这个集合为 `L` 的内部定义提供材料，`L` 的内部良序也由它定义。两个集合的先后次序由它们最早出现的层决定，而只有把塔表示成模型中的对象，才能在模型内部表达这些层。本节尚不定义良序，只提供后续定义良序所需的数据。

全章重复同一个模式。**表**是有序对之集；说它在某个集合上**正确**，指它在该集合以下所记录的每个取值都是元层面的塔在那里的取值；说它**完备**，指它在以下的每个实参处都记录了一个取值。正确且完备的表，恰是图的步进条件所读出的内容，也恰是步进条件据以写下的内容；因此一对引理同时服务于消去与引入，而本章其余部分就是这两条引理在四处情形的应用。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Hierarchy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; Lset; Lset-in; Lset-out; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-𝒟ₒ )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import L.Recursion {ℓ} lem using ( mereFunct )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; domAt-intro )
open import L.Coding.HierarchySequence {ℓ} lem
  using ( StepAt; StepOf; PowOK; StepAt-in; StepAt-out; StepAt-back
        ; ApproxAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step; ApproxAt-in
        ; LsetGraphAt; LsetGraph-in; LsetGraph-out; GraphOf
        ; PairGraphAt; PairOf; PairGraph-in; PairGraph-out )

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

Three conditions, one line each, because each is one direction of one statement.
`Values`{.Agda} says a value recorded at an argument below `B` is the meta tower
there. `Entries`{.Agda} says every argument below `B` has the meta tower recorded
at it. `Domain`{.Agda} says nothing outside `B` is recorded at all.
<!--zh-->
## 表记录什么

三个条件各占一行，因为每个都是同一句陈述的一个方向。`Values`{.Agda} 说：在 `B` 以下某个实参处所记录的取值，就是元层面的塔在那里的取值。`Entries`{.Agda} 说：`B` 以下的每个实参处都记录着元层面的塔在那里的取值。`Domain`{.Agda} 说：`B` 以外的东西根本没有被记录。
<!--ja-->
## 表が記録するもの

表は順序対を用いて、順序数の入力と構成可能段階の出力を記録します。`Values`、`Entries`、`Domain` はそれぞれ値の正しさ、各記録の形、定義域がどこまで覆われるかを表します。
<!--/-->

<!--en-->
They are listed as three separate conditions rather than bundled into one, because
the two applications need only different subsets of them. The induction over an
approximation uses the first two, and the third cannot hold: an approximation's
entries lie below its own domain, not below whichever argument the induction
currently stands at. The internal hierarchy has all three, because it is built as
exactly the set of the right pairs. If the conditions were bundled, the weaker
application would have to meet a condition it cannot prove.

`B` is a plain set of the hierarchy here, not an element of the model. None of
the three asks for constructibility; that enters with the ordinals, one section
down.
<!--zh-->
三个条件分开列出而不合并，因为两个应用各自只需其中的一部分。对逼近所作的归纳只用到前两个，而第三个不可能成立：逼近的诸条目落在它自己的定义域以下，而不落在归纳当前所处的那个实参以下。内部层级三个都有，因为它就是按「恰好是那些对的集合」定义的。若合并成一个条件，较弱的应用就要承担一个它证不出的条件。

此处的 `B` 是层级的一个普通集合，不是模型的元素。三者都不要求可构造性；可构造性要到下一节、随序数一同引入。
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

This is the chapter's central step, and both directions of it come out of the same
three private lines. The step at an argument `b` collects, over the arguments `c` below
`b` and the values `w` recorded there, the members of the definable powerset of
`w`. The meta tower at `b` collects the same thing with `Lset c` in place of `w`.
So if the table is correct the two have the same members, and that is the whole
mathematics: `step-Lset`{.Agda} uses a satisfied step to read the tower's values back,
`step-table`{.Agda} writes the step from the tower.
<!--zh-->
## 与外部层级对照的步骤

这是本章的核心步骤，其两个方向出自同样的三行私有代码。实参 `b` 处的那一步，沿 `b` 以下的诸实参 `c` 与在其处所记录的诸取值 `w`，收集 `w` 的可定义幂集的诸成员。元层面的塔在 `b` 处收集的是同一样东西，只是把 `w` 换成 `Lset c`。故若表是正确的，两者就有同样的成员，而所需的数学仅此而已：`step-Lset`{.Agda} 使用一个已成立的步进把塔的取值读回来，`step-table`{.Agda} 则由塔写出那一步。
<!--ja-->
## 外部の階層と照合する一段階

表が以前の段階を正しく記録しているとき、内部の定義可能冪集合と和集合の操作は外部の `Lset`{.Agda} の再帰方程式と一致します。この比較が新しい表の値を決定します。
<!--/-->

<!--en-->
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
上一章的那个旁条件在此处一次性地、为两个方向一并解除。`PowOK`{.Agda} 要求的是：每个被记录的取值，其可定义幂集是 `L` 的元素；而被记录的取值是塔在 `B` 以下某个实参处的值，该实参因 `B` 是序数而是序数，而层的可定义幂集可构造。故那一步所需的全部，就是正确性加上单独一条序数性假设，而两种读法的陈述里都不带那个条件。

两个方向分开命名，因为它们分开使用。向上是「被记录取值的可定义幂集落在 `B` 处的塔里面」，那就是 `Lset-in`{.Agda}。向下是塔本身的分解 `Lset-out`{.Agda}，随后把它产出的那个序数记为模型的元素，而这一步由类的传递性直接给出。
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

One induction, on the argument, in the meta-language, with the approximation and
its domain held fixed. The motive says: whatever value the approximation records
at this argument is the meta tower there. It quantifies over **all** recorded
values, and that is why single-valuedness is nowhere a hypothesis. Two values
recorded at one argument are both pinned to the same tower value, so they are
equal; the previous chapter's ruling that the approximation carries no
single-valuedness conjunct is collected here, as `approx-uniq`{.Agda}, in three
lines.
<!--zh-->
## 逼近所记录的每个值

一次归纳，在实参上，在元语言中，逼近与它的定义域保持固定。动机说：逼近在这个实参处所记录的任何取值，都是元层面的塔在那里的取值。它对**一切**被记录的取值作量化，而这正是单值性在任何地方都不作为假设的原因。在同一个实参处记录的两个取值都被钉在同一个塔值上，故两者相等；上一章那条「逼近不带单值性合取项」的裁定，在此处以 `approx-uniq`{.Agda} 之名、用三行收取。
<!--ja-->
## 近似が記録するすべての値

近似表に入力と出力の組があれば、その出力はその入力における外部の構成可能段階と等しいことを、表の構成に関する帰納法で示します。
<!--/-->

<!--en-->
The step of the induction is `step-Lset`{.Agda} at the recorded value.
Correctness below the argument *is* the induction hypothesis, verbatim.
Completeness below the argument is where the domain hypothesis is spent: an
argument below this one is below the approximation's domain, because the domain
is an ordinal and ordinals are transitive; the approximation therefore has a
value there; and the induction hypothesis identifies it with the tower's. That
value is produced only merely, which is enough, because what is being proved of
it is a membership.
<!--zh-->
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

```

<!--en-->
## The graph holds of nothing else

The graph says there merely is an approximation on the argument whose step at the
argument is the value. Read it and everything is already in hand: unpack the
approximation, take correctness from `approx-val`{.Agda}, take completeness from
`ApproxAt-value`{.Agda} composed with `approx-val`{.Agda} again, and apply
`step-Lset`{.Agda} one last time. The conclusion is that the graph **determines**
its value: whatever satisfies it at an ordinal is the meta tower there.
<!--zh-->
## 图只对正确值成立

图说：仅存在实参上的一个逼近，使得它在实参处的那一步正是那个取值。把这条读式展开，所需的材料全部就位：拆开逼近，正确性取自 `approx-val`{.Agda}，完备性取自 `ApproxAt-value`{.Agda} 再复合一次 `approx-val`{.Agda}，最后应用一次 `step-Lset`{.Agda}。结论是：图**确定**它的取值；凡在某个序数处满足它的对象，都是元层面的塔在该处的取值。
<!--ja-->
## グラフは正しい値だけを持つ

内部グラフを満たす組は、構文的な表の条件から外部の `Lset`{.Agda} の値へ復元できます。したがってグラフは余分な入力・出力の組を認めません。
<!--/-->

<!--en-->
The reading stands at variable slots, and that is not decoration. Its two
consumers instantiate it at two different concrete environments, and a statement
made at either would have to be converted to the other through a satisfaction
carrying the whole tower description inside it.
<!--zh-->
这条读式以变元形式陈述，这一点是必要的。它的两个使用处会在两个不同的具体环境中将其实例化；若改在任一具体环境中陈述，就必须通过一个满足关系把它转换到另一处，而该满足关系内部包含完整的塔描述。
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

The converse direction needs a witness, and a correct, complete table is one.
`graph-table`{.Agda} turns such a table into a satisfaction of the graph by
filling in the previous chapter's projections and doing nothing else.
<!--zh-->
## 表就是逼近

反方向需要一个见证，而一张正确且完备的表就是。`graph-table`{.Agda} 把这样一张表变成对图的满足，办法是填上上一章的诸投影，此外什么也不做。
<!--ja-->
## 表は近似である

表を構成する各段階は、定義域、項目の形、値の正しさという近似条件を満たします。この事実により、表の構文的構成と外部階層についての意味論的主張を結びます。
<!--/-->

<!--en-->
The domain conjunct is `Domain`{.Agda} one way and `Entries`{.Agda} the other.
The step conjunct at a recorded pair is `step-table`{.Agda} at that argument,
whose correctness and completeness are those of the table itself restricted below
the argument; this restriction is where transitivity of the ordinal is spent for
the second and last time. The value the graph is asked about is the step at the
whole argument, which is `step-table`{.Agda} once more. So one table serves both conjuncts
of "is an approximation" and the outer step as well.
<!--zh-->
定义域合取项的一个方向由 `Domain`{.Agda} 给出，另一个方向由 `Entries`{.Agda} 给出。对某个已记录的有序对，步进合取项由 `step-table`{.Agda} 应用于相应实参得到；所需的正确性与完备性，就是该表限制到此实参以下后具有的性质。序数的传递性在这里第二次、也是最后一次使用。图要求的取值是整个实参处的步进结果，这也由 `step-table`{.Agda} 得到。因此，同一张表证明「是一个逼近」的两个合取项，并证明外层的步进条件。
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

The table has to be **built**, and the only builder is replacement, which asks
for a graph. This is that graph, and it is the packaged form of the previous
chapter's graph: the value at an argument is the ordered pair of the argument
with the tower's value there. One existential binds the tower's value, the pair
reader equates the entry with the pair, and the tower graph says the bound value
is the right one.
<!--zh-->
## 有序对图

表必须被**构造出来**，而造表所用的是替换；替换需要一个图。这里给出的就是该图，也是上一章相应图的打包形式：某个实参处的取值，是该实参与塔在该处的取值组成的有序对。一个存在量词绑定塔的取值，对读式把相应条目与这个有序对等同起来，而塔的图说明所绑定的取值是正确的。
<!--ja-->
## 順序対によるグラフ

表の各入力・出力を順序対として集合に符号化します。対の単射性により、この集合から入力に対応する出力を一意に読み戻せます。
<!--/-->

<!--en-->
Its two readings take the sentence as a **parameter**, with the sentence's own
equation as a hypothesis, `refl`{.Agda} at the single call site. That is the shape
required of a frame generic in a construction, and this chapter is where that shape
is checked on a sentence rather than on a constructor: written directly against
the closed sentence, the readings take 85 seconds, because Agda decides the
equality of two spellings of one formula by normalizing a satisfaction that
carries the entire definable-powerset description inside it. With the sentence a
variable there is nothing to normalize.
<!--zh-->
它的两种读法把那个句子取作**参数**，并把该句子自己的等式取作假设，唯一的调用处是 `refl`{.Agda}。这就是「对某个构造保持通用的框架」所要求的形状，而本章正是在一个句子而非一个构造子上检验它的地方：直接对着那个闭句子写，两条读法耗时 85 秒，因为 Agda 判定「同一条公式的两种写法」是否相等，靠的是把一个内部装着整条可定义幂集描述的满足关系正规化。句子一旦是变元，就没有什么可正规化的了。
<!--/-->

<!--en-->
## The internal hierarchy

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
<!--zh-->
## 内部层级

`Recorded`{.Agda} 为内部层级所实现的那个类命名：「`α` 以下的序数与塔在它那里的取值」所成的诸对，此外别无他物。`IsHier`{.Agda} 说模型的某个集合逐成员地实现它。这是一条**隶属等价**、而不是一个单向的收集，理由上一章已经记下：若只作单向陈述，便没有说明这个收集**只**持有那样的对，那条存在性断言于是不是命题，而其下的每一步都需要一条内部的函数外延性引理，才能把两个收集合成一个。作为等价说出来，两个实现者由 `L` 中的外延性而相等，`HierOf`{.Agda} 是命题，而造出它的那场归纳的动机也是命题。
<!--ja-->
## 内部の階層

指定した順序数までの正しい表を `L` 内で定義し、その順序対のグラフを一つの構成可能集合として取り出します。`IsHier`{.Agda} は、この集合が外部の階層を正確に記録することを表します。
<!--/-->

<!--en-->
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
requirement is discharged through `mereFunct`{.Agda}, because the value at an argument
is a construction rather than a decision.

The construction is sealed where it is built. Everything below reaches it through
its specification, and no induction is ever unfolded into a conversion.
<!--zh-->
两条读式都针对一个**变元**收集陈述，只通过该收集的规格使用构造，而不直接作用于保持不透明的构造。向外读取时，对某个成员应用有序对的单射性；向内写入时，把相应有序对取作模型的元素，这由模型自身的配对给出。后一步还需要实参具有序数性，否则无法指称相应取值。

然后是构造，在序数上作一次沿成员的归纳。在 `α` 处，成对的那个图在以下的每个实参上都是函数性的：归纳假设给出直到那个实参为止的层级，`graph-table`{.Agda} 把它变成对塔之图的满足，而 `Lset-only`{.Agda} 说别的东西都不满足它。替换把那些对收拢起来，收拢所得的集合经同样这两条事实在两个方向上实现那个类。每个实参的序数性取自 `mem-ord`{.Agda} 且**不加截断**，这正是这条路线上任何地方都不出现「序数性可判定」分支的原因；而函数性则由 `mereFunct`{.Agda} 补足，因为某个实参处的取值是一个构造、而不是一次判定。

构造在定义处保持不透明。此后的论证只通过它的规格使用它，因此不会在转换过程中展开任何一次归纳。
<!--/-->

```agda
Recorded : V ℓ → V ℓ → Ω
Recorded B z = ⋁ S (λ c → (fst c ∈ B)
  ⊓ ((z ≡ pr (fst c) (Lset (fst c))) , setIsSet z (pr (fst c) (Lset (fst c)))))

IsHier : V ℓ → S → Type (ℓ-suc (ℓ-suc ℓ))
IsHier B h = (z : S) → (fst z ∈ fst h) ≡ Recorded B (fst z)

HierOf : V ℓ → Type (ℓ-suc (ℓ-suc ℓ))
HierOf B = Σ[ h ∈ S ] IsHier B h

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
```

Perf: the pair graph enters as a variable with its own equation; spelled out as
the closed sentence, three conversions cost 85 s between them.

```agda
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

The last statement is one line, because the internal hierarchy at an ordinal is a
correct, complete table on it and `graph-table`{.Agda} was written for exactly
that. With `Lset-only`{.Agda} beside it, the graph and the meta tower now agree
in both directions at every ordinal, which is what the chapter was for.
<!--zh-->
## 外部层级满足该图

最后一条陈述只有一行，因为某个序数处的内部层级，就是那个序数上一张正确且完备的表，而 `graph-table`{.Agda} 正是为此而写。与 `Lset-only`{.Agda} 并置，图与元层面的塔如今在每个序数处，在两个方向上都一致，而这正是本章的目的。
<!--ja-->
## 外部の階層はグラフを満たす

外部で定義した `Lset`{.Agda} の各段階は、内部グラフが要求する再帰方程式を満たします。したがって内部階層から読み出した値は外部の塔の値と一致します。
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

`approx-val`{.Agda} proves, by one membership induction on the argument, that every
value an approximation records equals the meta tower's value at that argument,
with no single-valuedness hypothesis anywhere; `approx-uniq`{.Agda} is the
corollary left by the previous chapter and completed here. `Lset-only`{.Agda} and
`Lset-defines`{.Agda} are the graph's two directions against the tower, and the second
is what `hierL`{.Agda} is built from: the internal hierarchy, an element of
`L` whose members are exactly the pairs of an ordinal with the tower's value
at it, unique because its specification is a membership equivalence, and sealed
where it is built.
<!--zh-->
## 小结

`approx-val`{.Agda} 通过对实参作一次沿成员归纳，证明逼近记录的每个取值都等于元层面的塔在相应实参处的取值；这里不需要任何单值性假设。`approx-uniq`{.Agda} 则是上一章留下、由本节完成的推论。`Lset-only`{.Agda} 与 `Lset-defines`{.Agda} 给出图与塔之间的两个方向，而后者用于构造 `hierL`{.Agda}。`hierL`{.Agda} 是内部层级，是 `L` 的一个元素；其成员恰是「序数与塔在该处取值」组成的有序对。它的规格是隶属等价，因此它唯一；该构造在定义处保持不透明。
<!--ja-->
## まとめ

表と近似を使って、構成可能階層の有限区間を `L` 内の順序対グラフとして符号化します。正しさと一意性により、その内部グラフの値は外部の `Lset`{.Agda} と正確に一致します。
<!--/-->

<!--en-->
Nothing here recomputes the last chapter. The step's three readings, the
approximation's four projections and the graph's two are used in the form the
previous chapter gave them; what is added is the connection to the meta tower,
in the form of two lemmas, `step-Lset`{.Agda} and `step-table`{.Agda}, applied four
times between them.

Two timings are worth recording, and both are about a name rather than about
mathematics. Introducing the pair graph as a **variable** carrying its own
equation, rather than as the closed sentence it will be instantiated to, saves
85 seconds; the mechanism is the one the last two chapters met, that two
spellings of one formula are compared by normalizing a satisfaction with the
whole definable-powerset description inside it. And the set argument of
`mem-ord`{.Agda} has to be given **explicitly** at every use:
`IsOrd`{.Agda} unfolds to a quantified membership, so nothing in the hypothesis
determines the set it is about, and left implicit the chapter does not check at
all.

What the chapter provides is the object the next part uses. `L` now has a
name for its own tower, and a well-order of `L` is read off a tower: one set
before another when it appears at an earlier stage, or at the same stage under an
earlier formula. The first half of that is now sayable inside the model.
<!--zh-->
本章没有重做上一章的计算。那一步的三种读法、逼近的四个投影、图的两条读式，都按上一章给出的形式原样使用；新添的是连接塔与元层面的那两条引理 `step-Lset`{.Agda} 与 `step-table`{.Agda}，两者合计使用了四次。

有两次耗时值得记录，都与一个命名有关、与数学无关。把成对的那个图以**变元**身份引入，让它随身携带自己的等式，而不写成「它将被实例化成的那个闭句子」，可节省 85 秒；其机制正是前两章遇到的那一个：同一条公式的两种写法，靠把一个内部装有整条可定义幂集描述的满足关系正规化来比较。另外，`mem-ord`{.Agda} 的那个集合实参必须在每次使用时**显式**给出：`IsOrd`{.Agda} 展开成一条带量词的隶属关系，因此那条假设里没有任何东西能确定它所谈的集合；若留作隐式，本章根本检查不完。

本章给出下一部分将使用的那个对象。`L` 如今有了一个指称它自己那座塔的名字，而 `L` 的良序正是从这座塔上读出来的：当它出现在更早的层，或在同一层而由更早的公式给出时，一个集合排在另一个之前。这句话的前半，如今在模型内部说得出口了。
<!--/-->
