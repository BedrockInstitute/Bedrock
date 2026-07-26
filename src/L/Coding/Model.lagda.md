# Readers, quoted in the model

<!--en-->
The readers were written about the hierarchy and the bridge carries them into the
model. This chapter takes the bridge across, once, and states what a quoted
reader means on the far side.

There is one wrinkle and it is small. A reader's meaning was stated in terms of
the value of a variable in a hierarchy environment; on the far side the
environment holds elements of the model, and the hierarchy environment is the one
obtained by taking underlying sets. Looking up in the projected environment is
projecting the lookup, which is a two-line induction, and after it the quoted
reader says exactly what the original said about the underlying sets.

The first reader to cross is the one everything else is built from: the ordered
pair. Nothing above it needs a new argument, because the bridge is generic and
the readers' own characterizations were proved once already.
<!--zh-->
诸读式写的是关于层级的事，而那座桥把它们运进模型。本章把桥走一遍，并陈述一条被引用的读式在彼岸说的是什么。

有一处小小的皱褶。读式的含义当初是按「变元在层级环境中的取值」陈述的；而在彼岸，环境装的是模型的元素，那个层级环境是取底集得来的。在投影后的环境中查表就是把查表的结果投影，这是一次两行的归纳，之后被引用的读式所说的，恰是原读式关于诸底集所说的。

第一条过河的读式是此后一切所由构造的那条：有序对。它之上不再需要新的论证，因为那座桥是通用的，而诸读式自身的刻画早已证过一次。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Model {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( liftFo; transferFo )
open import L.Coding.Base {ℓ} using ( prAt; Δ₀-prAt; prAt-adequate )

open import Cubical.Data.Vec using ( map )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Looking up in a projected environment
<!--zh-->
## 在投影后的环境中查表
<!--/-->

<!--en-->
Two lines, and the only bookkeeping the crossing costs.
<!--zh-->
两行，也是这次过河所付的全部记账。
<!--/-->

```agda
lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
           → lookup i (map fst γ) ≡ fst (lookup i γ)
lookup-fst zero    (x ∷ γ) = refl
lookup-fst (suc i) (x ∷ γ) = lookup-fst i γ
```

<!--en-->
## The ordered pair
<!--zh-->
## 有序对
<!--/-->

<!--en-->
The quoted reader is the original lifted along the bridge, and the lift asks for
nothing: the reader names no constants, so there is nothing to be constructible
and the admissibility witness is empty.

Its meaning is three steps. The bridge equates satisfaction in the model with
satisfaction in the hierarchy at the projected environment; the reader's own
characterization says what that is; and the lookups are projected. What comes out
is the statement a consumer wants: the value of one variable is the Kuratowski
pair of the values of the other two, as sets.
<!--zh-->
被引用的读式就是原读式沿桥抬升，而抬升什么也不索取：该读式不点名任何常元，故没有东西需要可构造，合格性证书是空的。

它的含义分三步。桥把「在模型中满足」等同于「在层级中、于投影后的环境处满足」；读式自家的刻画说出那是什么；诸查表被投影。出来的正是消费方想要的陈述：一个变元的取值，是另两个变元取值的 Kuratowski 对，作为集合而言。
<!--/-->

```agda
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

prAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAtL q u v = liftFo (prAt q u v) _

prAtL-adequate : ∀ {n} (q u v : Fin n) (γ : S ^ n)
  → (γ ⊨ prAtL q u v)
  ≡ PairIs (fst (lookup q γ)) (pr (fst (lookup u γ)) (fst (lookup v γ)))
prAtL-adequate q u v γ =
    transferFo (prAt q u v) _ (Δ₀-prAt q u v) γ
  ∙ prAt-adequate q u v (map fst γ)
  ∙ cong₂ PairIs (lookup-fst q γ)
      (cong₂ pr (lookup-fst u γ) (lookup-fst v γ))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`prAtL`{.Agda} says, in the object language of the model, that one set is the
ordered pair of two others, and `prAtL-adequate`{.Agda} is its meaning. It was
obtained by quoting, not by re-proving: the reader and its characterization stay
where they were written, and the crossing cost one induction on environments.

That is the pattern for every reader that follows, and it is the reason the
coding chapters did not have to be re-based. What it does not cover is any
predicate that is not Δ₀, and those are to be written directly over the model
instead, since nothing in the model's comprehension asks them to be bounded.
<!--zh-->
`prAtL`{.Agda} 在模型的对象语言里说「这个集合是那两个的有序对」，而 `prAtL-adequate`{.Agda} 是它的含义。它由引用得来，而非重新证得：读式与它的刻画留在写下它们的地方，而这次过河只花了一次关于环境的归纳。

这就是此后每条读式的套路，也是编码诸章无须换底的原因。它不覆盖的是任何非 Δ₀ 的谓词，那些应当直接在模型上写，因为模型的概括不要求它们有界。
<!--/-->
