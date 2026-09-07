# The hierarchy, said as a sequence

<!--en-->
The tower is the one construction on this route that cannot be internalized the
way the satisfaction recursion was. A graph may not name the object it defines,
and the tower at a stage is built out of the tower below that stage, so a graph
written directly for the tower would have to name its own values at
sub-arguments. It has none to name.

What can be said instead is what an **approximation** is. A function `f` is an
approximation to the hierarchy on `a` when it is defined exactly on the members
of `a` and every value it records is the step at that argument computed from `f`
itself. The step consults `f` only below the argument, so the condition never
looks at a value the function does not already record, and the tower's own value
at `a` is then whatever the step from such an `f` yields. That is a sequence
characterization, and it is a first-order sentence about `f` alone.

Every slot in this chapter is a slot. The approximation is bound by the graph's
one existential, the argument and the value are the graph's two free variables,
and nothing anywhere is a named constant, which is what lets the whole
description be spoken where the hierarchy needs it: under the binder that holds
the stage. Every reading below is stated at a **variable** environment, for the
reason the last two chapters were: an adequacy discharged at a concrete
environment puts the construction of that environment inside a satisfaction, and
the same statement then costs minutes instead of seconds.
<!--zh-->
在这条路线上，塔是唯一一个没法照满足关系那场递归的办法内化的构造。一个图不可以点名它所定义的对象，而塔在某个阶段处是由该阶段以下的塔造出来的，故直接为塔写下的图将不得不点名它自己在诸子实参处的取值。它没有可点名的取值。

能说出口的是**逼近**是什么。函数 `f` 是层级在 `a` 上的一个逼近，当它恰好定义在 `a` 的诸成员上，且它所记录的每个取值都是「在那个实参处、由 `f` 自身算出的那一步」。那一步只在实参以下查阅 `f`，故这个条件永不查看该函数尚未记录的取值，而塔自己在 `a` 处的取值就是「由这样一个 `f` 所得的那一步」。这是一条序列刻画，而它是一个只谈 `f` 的一阶句子。

本章的每一位都是一位。逼近由图仅有的那个存在量词绑定，实参与取值是图的两个自由变元，而任何地方都没有点名的常元，正是这一点让整条描述能在层级所需之处说出口：在持有阶段的那层绑定之下。下面每一条读式都陈述在**变元**环境上，理由与前两章相同：在具体环境上解除的充分性，把那个环境的构造塞进了一个满足关系里面，同一条陈述于是从几秒变成几分钟。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Sequence {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; domAt; domAt-in; domAt-out; prAtL; prAtL-adequate )
open import L.Coding.Expressions {ℓ} using ( extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Powerset {ℓ} lem using ( DefAt; DefAt-in; DefAt-out )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## What the step at an argument says
<!--zh-->
## 某个实参处的那一步说了什么
<!--/-->

<!--en-->
`v` is the stage at `b`, given the approximation `f` below `b`, when the members
of `v` are exactly the sets lying in the definable powerset of some value `f`
records at some argument in `b`. Three adjacent existentials carry it: the
argument `c`, the value `w` the approximation records there, and the definable
powerset `d` of that value. The powerset has to be **bound**, because the
previous chapter delivers a description of it and not a term for it; `DefAt`
says that `d` is the definable powerset of `w`, so the only way to use it is to
quantify over the thing it describes.

The whole step is **one** `extAt`, and that is a decision rather than a
convenience. A stage is a set, and every clause of a set-valued recursion says
the same thing: this value is the set of exactly those things meeting a
condition. Written as a hand-made pair of inclusions the condition would appear
twice, once under each inclusion, so the three existentials would be duplicated,
every later change to them would have to be made in two places, and each reading
would have to be reassembled from two halves that are not each other's inverse.
`extAt` writes the condition once and hands the two readings back as
projections, which is exactly what it exists for.

One side condition travels with the step, and one hypothesis discharges it in
both directions. To satisfy the description one must produce the definable
powerset **as an element of the model**, since an object-language existential
ranges over `L`; to read the description back one needs the elimination of
`DefAt`, whose side condition is that the definable subsets of the carrier are
constructible. The first implies the second: if `𝒟ₒ w` is an element of `L` then
its members are constructible by transitivity of the class. So both directions
ask for the same thing, `PowOK`{.Agda}, and a consumer at a stage discharges it
with the successor identity.
<!--zh-->
`v` 是 `b` 处的阶段 (给定 `b` 以下的逼近 `f`)，当 `v` 的诸成员恰是「落在 `f` 于 `b` 中某个实参处所记录的某个取值的可定义幂集之中」的那些集合。三个相邻的存在量词承载它：那个实参 `c`、逼近在其处所记录的取值 `w`，以及该取值的可定义幂集 `d`。幂集必须**被绑定**，因为上一章交付的是关于它的一条描述、而不是指称它的一个词项；`DefAt` 说的是 `d` 是 `w` 的可定义幂集，故使用它的唯一办法就是对它所描述的那个东西作量化。

整一步是**一次** `extAt`，而这是一项决定、不是图省事。阶段是一个集合，而凡取值为集合的递归，其每一条子句说的都是同一句话：这个取值恰是满足某个条件的那些东西之集。若手写成一对包含，那个条件就要出现两次、每条包含之下各一次，于是那三个存在量词被复制一份，此后对它们的每一次改动都得在两处各做一遍，而每一种读法都得由「互非逆」的两半重新拼起来。`extAt` 把条件只写一次，并把两种读法作为投影交回来，而它存在的意义恰在于此。

有一个旁条件随这一步一同旅行，而一条假设在两个方向上都把它解除。要满足这条描述，必须把可定义幂集**作为模型的元素**拿出来，因为对象语言的存在量词在 `L` 上取值；要把描述读回来，则需要 `DefAt` 的消去，而它的旁条件是「载体的诸可定义子集皆可构造」。前者蕴含后者：若 `𝒟ₒ w` 是 `L` 的元素，则由该类的传递性，它的诸成员皆可构造。故两个方向索取的是同一样东西，即 `PowOK`{.Agda}，而位于某个阶段处的消费方用后继恒等式把它解除。
<!--/-->

```agda
private
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

StepBody : ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc (suc n))))
StepBody b f = (var (suc (suc zero)) ∈̇ var (sh4 b))
             ∧̇ ( appAt (sh4 f) (suc (suc zero)) (suc zero)
               ∧̇ ( DefAt zero (suc zero)
                 ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

StepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
StepAt v b f = extAt v (∃̇ (∃̇ (∃̇ (StepBody b f))))

Records : ∀ {n} → Fin n → Fin n → S ^ n → S → S → Type (ℓ-suc ℓ)
Records b f γ c w = ⟨ fst c ∈ fst (lookup b γ) ⟩
                  × ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩

StepOf : ∀ {n} → Fin n → Fin n → S ^ n → S → Type (ℓ-suc ℓ)
StepOf b f γ z = Σ[ c ∈ S ] Σ[ w ∈ S ]
                   (Records b f γ c w × ⟨ fst z ∈ 𝒟ₒ (fst w) ⟩)

PowOK : ∀ {n} → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
PowOK b f γ = (c w : S) → Records b f γ c w → ⟨ isL (𝒟ₒ (fst w)) ⟩
```

<!--en-->
## The step, both ways
<!--zh-->
## 那一步，两个方向
<!--/-->

<!--en-->
Reading the body is where the three existentials are spent, and each `PT.rec`
below names the type of its payload. That is the law the Powerset chapter was
written under and it is not a stylistic one: left to inference the payload is a
metavariable standing for the satisfaction of a formula the elaborator has not
committed to, and the same two lines then run past two minutes instead of two
seconds.

Assembling the body is the same three existentials filled in. The definable
powerset is supplied as the element of the model that `PowOK`{.Agda} provides,
its own coding equation is `refl`{.Agda} at that element, and the introduction
of `DefAt`{.Agda} needs nothing else. The readings of the step are then
`extAt`{.Agda}'s directions with those halves plugged in, and there are three of
them rather than two: `StepAt-out`{.Agda} reads a member of the step as a
payload, `StepAt-back`{.Agda} puts a payload back, and `StepAt-in`{.Agda} builds
the step from both directions at once, since a set built by extension has to be
re-entered member by member from both sides. The reading and the assembly of the
body are shared between all three, so each projection is one line.
<!--zh-->
读体是那三个存在量词被花掉之处，而下面每一次 `PT.rec` 都为自己载荷的类型点名。这是上一章据以写下的规矩，且它不是文风问题：若交给推断，载荷就是一个元变元，代表着「某条公式的满足关系」，而消解器尚未对那条公式作出承诺，同样两行于是从两秒变成跑过两分钟。

装配体则是把同样三个存在量词填上。可定义幂集以 `PowOK`{.Agda} 所提供的那个模型元素供上，它自己的编码等式在那个元素处是 `refl`{.Agda}，而 `DefAt`{.Agda} 的引入别无所需。这一步的诸读法于是就是 `extAt`{.Agda} 的诸方向、把那两半插进去；而它们有三条而非两条：`StepAt-out`{.Agda} 把这一步的一个成员读作一份载荷，`StepAt-back`{.Agda} 把一份载荷放回去，而 `StepAt-in`{.Agda} 由两个方向一并造出这一步，因为一个以外延造出的集合，必须从两侧逐成员地重新进入。读体与装配体为三者所共用，故每个投影都只有一行。
<!--/-->

```agda
module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) where
  private
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (∃̇ (StepBody b f)))

    readBody : PowOK b f γ → (z c w d : S)
             → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩ → StepOf b f γ z
    readBody ok z c w d (hb , (ha , (hd , hz))) =
      c , w , rec , subst (λ X → ⟨ fst z ∈ X ⟩) qd hz
      where
```

Perf: `env` spelled out at both ends; via an abbreviation, 15 s per conversion.

```agda
      rec : Records b f γ c w
      rec = hb , subst ⟨_⟩ (appAt-adequate
        (sh4 f) (suc (suc zero)) (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)) ha

      qd : fst d ≡ 𝒟ₒ (fst w)
      qd = DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
        (λ x x∈ → isL-trans {x = 𝒟ₒ (fst w)} {y = x} x∈ (ok c w rec)) refl hd

    unfold : PowOK b f γ → (z : S)
           → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ∥ StepOf b f γ z ∥₁
    unfold ok z = PT.rec squash₁ viaArg
      where
      viaPow : (c w : S)
             → Σ[ d ∈ S ] ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
             → ∥ StepOf b f γ z ∥₁
      viaPow c w (d , hd) = ∣ readBody ok z c w d hd ∣₁

      viaVal : (c : S)
             → Σ[ w ∈ S ] ⟨ (w ∷ c ∷ z ∷ γ) ⊨ ∃̇ (StepBody b f) ⟩
             → ∥ StepOf b f γ z ∥₁
      viaVal c (w , hw) = PT.rec squash₁ (viaPow c w) hw

      viaArg : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (∃̇ (StepBody b f)) ⟩
             → ∥ StepOf b f γ z ∥₁
      viaArg (c , hc) = PT.rec squash₁ (viaVal c) hc

    fill : PowOK b f γ → (z : S) → StepOf b f γ z → ⟨ (z ∷ γ) ⊨ Φ ⟩
    fill ok z (c , (w , (rec , hz))) =
      ∣ c , ∣ w , ∣ D , (rec .fst , (ha , (hdef , hz))) ∣₁ ∣₁ ∣₁
      where
```

Perf: `env` spelled out at both ends; via an abbreviation, 15 s per conversion.

```agda
      D : S
      D = 𝒟ₒ (fst w) , ok c w rec

      ha : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨ appAt (sh4 f) (suc (suc zero)) (suc zero) ⟩
      ha = subst ⟨_⟩ (sym (appAt-adequate
        (sh4 f) (suc (suc zero)) (suc zero) (D ∷ w ∷ c ∷ z ∷ γ))) (rec .snd)

      hdef : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      hdef = DefAt-in w zero (suc zero) (D ∷ w ∷ c ∷ z ∷ γ) refl refl

  StepAt-out : ⟨ γ ⊨ StepAt v b f ⟩ → PowOK b f γ
             → (z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁
  StepAt-out h ok z z∈ = unfold ok z (extAt-out v Φ γ h z z∈)

  StepAt-back : ⟨ γ ⊨ StepAt v b f ⟩ → PowOK b f γ
              → (z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩
  StepAt-back h ok z s = extAt-in v Φ γ h z (fill ok z s)

  StepAt-in : PowOK b f γ
            → ((z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁)
            → ((z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩)
            → ⟨ γ ⊨ StepAt v b f ⟩
  StepAt-in ok into back = extAt-in-both v Φ γ
    (λ z z∈ → PT.rec (snd ((z ∷ γ) ⊨ Φ)) (fill ok z) (into z z∈))
    (λ z h → PT.rec (snd (fst z ∈ fst (lookup v γ))) (back z) (unfold ok z h))
```

<!--en-->
## What it is to be an approximation
<!--zh-->
## 成为一个逼近是什么意思
<!--/-->

<!--en-->
Two conjuncts, and there is no third. `f` is defined on `a`, and every value `f`
records is the step at that argument from `f` itself. The second conjunct needs
no guard saying the argument lies in `a`: the first conjunct already pins the
domain to `a` in both directions, so an argument at which anything is recorded
is a member of `a` and saying so again would only lengthen the sentence.

The pair is a membership **equivalence**, and that matters more than it looks.
Stated the other way, as "for each argument in `a` there merely is a value which
is the step there", the sentence permits `f` to hold junk pairs beside the right
ones, so it does not determine `f`, the existence claim is not a proposition,
and an induction against it needs an internal function-extensionality lemma to
get from two approximations to one. As an equivalence the motive is a
proposition and that lemma never has to be written.

There is deliberately **no single-valuedness conjunct**. It would assert nothing
the second conjunct does not already give: if two values are recorded at one
argument then both are the step at that argument, the step is a set identity,
and two sets with the same members are equal. Carrying it would put three
universal quantifiers under a satisfaction in exchange for a corollary.

The three projections are the three questions a consumer asks: an argument with
an entry is in the domain, an argument in the domain has an entry, and a
recorded value is a step. The introduction is here rather than at the call site
for the reason every reading is: it discharges an adequacy, and it must do so
at a variable environment.
<!--zh-->
两个合取项，没有第三个。`f` 定义在 `a` 上，且 `f` 所记录的每个取值都是「在那个实参处、由 `f` 自身算出的那一步」。第二个合取项无须加上「实参落在 `a` 中」这道防护：第一个合取项已经在两个方向上把定义域钉在 `a` 上，故凡记录了东西的实参都是 `a` 的成员，再说一遍只会把句子拉长。

这一对是一条隶属**等价**，而这比看上去更要紧。若反过来陈述为「对 `a` 中的每个实参，仅仅存在一个取值是那里的那一步」，这句话就容许 `f` 在正确的对之外还持有一些垃圾对，故它并不确定 `f`，那条存在性断言不是命题，而针对它的归纳需要一条内部的函数外延性引理，才能从两个逼近走到一个。作为等价，动机是命题，而那条引理根本无须写下。

此处**刻意没有单值性合取项**。它断言不出第二个合取项尚未给出的任何东西：若在同一个实参处记录了两个取值，则两者都是那个实参处的那一步，而那一步是一条集合等式，同成员的两个集合相等。带上它，等于拿三个置于满足关系之下的全称量词去换一条推论。

三个投影就是消费方要问的三个问题：有条目的实参在定义域中、定义域中的实参有条目、被记录的取值是一步。引入之所以放在此处而不放在调用处，理由与每一条读式相同：它解除一次充分性，而那必须在变元环境上做。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

module RecShape (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n) where

  Domain₀ : S → V ℓ → Type (ℓ-suc ℓ)
  Domain₀ h B = (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩

  ApproxAt : ∀ {n} → Fin n → Fin n → Formula S n
  ApproxAt f a = domAt f a
               ∧̇ ∀̇ (∀̇ ( appAt (sh2 f) (suc zero) zero
                       ⇒̇ Step zero (suc zero) (sh2 f) ))

  GraphAt : ∀ {n} → Fin n → Fin n → Formula S n
  GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)

  module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
    ApproxAt-dom : ⟨ γ ⊨ ApproxAt f a ⟩ → Domain₀ (lookup f γ) (fst (lookup a γ))
    ApproxAt-dom h = domAt-out f a γ (h .fst)

    ApproxAt-value : ⟨ γ ⊨ ApproxAt f a ⟩ → (c : S)
                   → ⟨ fst c ∈ fst (lookup a γ) ⟩
                   → ∥ (Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩) ∥₁
    ApproxAt-value h = domAt-in f a γ (h .fst)

    ApproxAt-step : ⟨ γ ⊨ ApproxAt f a ⟩ → (c z : S)
                  → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                  → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩
    ApproxAt-step h c z p = h .snd c z
      (subst ⟨_⟩ (sym (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ))) p)

    ApproxAt-in : ⟨ γ ⊨ domAt f a ⟩
                → ((c z : S) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                   → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩)
                → ⟨ γ ⊨ ApproxAt f a ⟩
    ApproxAt-in hd hs = hd , λ c z p → hs c z
      (subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ)) p)

  module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    GraphOf : Type (ℓ-suc ℓ)
    GraphOf = Σ[ f ∈ S ] ( ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
                         × ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ )

    Graph-in : (f : S) → ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
             → ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ → ⟨ γ ⊨ GraphAt w b ⟩
    Graph-in f ha hs = ∣ f , (ha , hs) ∣₁

    Graph-out : ⟨ γ ⊨ GraphAt w b ⟩ → ∥ GraphOf ∥₁
    Graph-out h = h

  PairGraphAt : ∀ {n} → Fin n → Fin n → Formula S n
  PairGraphAt e c = ∃̇ (prAtL (suc e) (suc c) zero ∧̇ GraphAt zero (suc c))

  module _ {n : ℕ} (e c : Fin n) (γ : S ^ n)
           (φ : Formula S n) (qφ : φ ≡ PairGraphAt e c) where
    PairOf : Type (ℓ-suc ℓ)
    PairOf = Σ[ z ∈ S ] ( (fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z))
                        × ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ )

    PairGraph-in : (z : S) → fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z)
                 → ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ → ⟨ γ ⊨ φ ⟩
    PairGraph-in z q hg = subst (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym qφ)
      ∣ z , (subst ⟨_⟩
        (sym (prAtL-adequate (suc e) (suc c) zero (z ∷ γ))) q , hg) ∣₁

    PairGraph-out : ⟨ γ ⊨ φ ⟩ → ∥ PairOf ∥₁
    PairGraph-out h = PT.map
      (λ { (z , (hq , hg)) →
        z , (subst ⟨_⟩ (prAtL-adequate (suc e) (suc c) zero (z ∷ γ)) hq , hg) })
      (subst (λ ψ → ⟨ γ ⊨ ψ ⟩) qφ h)

open RecShape StepAt public renaming ( GraphAt to LsetGraphAt
                                     ; Graph-in to LsetGraph-in
                                     ; Graph-out to LsetGraph-out )

```

<!--en-->
## The graph
<!--zh-->
## 那个图
<!--/-->

<!--en-->
One existential over the approximation, and under it the two conjuncts the
chapter was written for: `f` is an approximation on the argument, and the value
is the step at that argument from `f`. The value stands at the first slot and
the argument at the second, which is the order the model's replacement field
reads a graph in, and `LsetGraph`{.Agda} is the sentence with those two slots
filled in.

The approximation is bound, and it has to be. A graph may not name the object it
defines, and it may assert the existence of something only when that something
is already known to be an element of `L`, since satisfaction is read at the
model. An approximation is such a thing: it is a set of pairs collected by
replacement from arguments below, not the tower it is used to describe. The
consumer supplies one; the graph merely says there merely is one.

Both readings are one line each, because a satisfied existential **is** a
truncated sigma and a satisfied conjunction **is** a pair. What they buy is not
proof, it is the name and the slot. `GraphOf`{.Agda} writes the payload type out
rather than leaving it to inference, and both readings stand at **variable**
slots in a variable environment, so a consumer instantiates them rather than
converting against them.

The naming is the whole cost of this section, and the figure is worth keeping
because the first diagnosis of it was wrong. Stated with the graph named by its
closed-sentence alias, the same two lines took 98 seconds of the chapter's 130.
The slots were blamed and they are innocent: an isolating measurement in the next
chapter puts a reading at fully concrete slots at fifteen milliseconds and the
same reading against an alias at fifty-one seconds. What costs is deciding a
satisfaction of the alias against a satisfaction of its expansion, which Agda
settles by normalizing a satisfaction that carries the entire
definable-powerset description inside it. Generic in the slots the readings never
meet that question, and the closed sentence is one unfolding away,
and the concrete sentence is one unfolding away.
<!--zh-->
在逼近上的一个存在量词，其下是本章为之而写的那两个合取项：`f` 是那个实参上的一个逼近，而那个取值是「在那个实参处、由 `f` 算出的那一步」。取值站在第一位、实参站在第二位，这正是模型的替换字段读一个图所用的顺序，而 `LsetGraph`{.Agda} 就是把那两位填好之后的那个句子。

逼近被绑定，而这是不得不然。一个图不可以点名它所定义的对象，且仅当某物已知是 `L` 的元素时，它才可以断言该物存在，因为满足关系是在模型处读的。逼近正是这样一样东西：它是由较低的诸实参经替换收集起来的对之集，而不是它被用来描述的那座塔。消费方供上一个；图只说仅仅存在一个。

两种读法各只一行，因为被满足的存在量词**就是**一个截断的 sigma，被满足的合取**就是**一个对。它们买到的不是证明，而是那个名字与那一位：`GraphOf`{.Agda} 把载荷的类型写了出来、不交给推断，而两种读法都站在一个变元环境的**变元**位上，故消费方是去实例化它们，而不是去与它们作转换。

命名就是本节的全部代价，而这个数字值得留存，因为对它的第一次诊断是错的。若把图以它那个闭句别名来称呼，同样两行花掉了本章 130 秒中的 98 秒。当初怪罪的是那两位，而它们是清白的：下一章一次隔离测量把「读式落在完全具体的位上」量到十五毫秒，而把「同一条读式对着一个别名」量到五十一秒。真正花钱的是「判定别名的满足关系与它展开式的满足关系相等」，而 Agda 解决它的办法，是把一个内部装着整条可定义幂集描述的满足关系正规化。落在变元位上，诸读式根本碰不到这个问题，而那个闭句只差一次展开。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`LsetGraph`{.Agda} is the object-language sentence "the value is the stage at
the argument", written without naming a stage, a tower, or an ordinal.
`StepAt`{.Agda} is one `extAt`{.Agda} over three adjacent existentials, the
argument, the value recorded there and its definable powerset;
`ApproxAt`{.Agda} is two conjuncts, the domain and the step condition, and no
more.

Nothing here is proved twice. The definable powerset arrives from the previous
chapter as a description at a slot and is used exactly as it was delivered, the
function machinery is read off `appAt`{.Agda} and `domAt`{.Agda}, and the step's
two readings are `extAt`{.Agda}'s own two. What the chapter contributes is the
shape: a graph that consults an approximation rather than the tower, which is
the only shape a graph is allowed to have.

Two rulings are recorded where a reader meets them. The step is a membership
equivalence rather than a one-directional collection, which keeps the motive of
the induction to come a proposition and removes an internal
function-extensionality lemma from the route entirely. And there is no
single-valuedness conjunct, because the step condition already pins every value
recorded at an argument, so single-valuedness is a corollary and not a
hypothesis.

One measurement, and the chapter after this one corrected its diagnosis. Every
second this chapter ever cost was a conversion between two spellings of the same
thing, and every time Agda answered it by normalizing a satisfaction with the
whole definable-powerset description inside: 98 seconds for two readings taken
against the graph's closed-sentence alias, and 15 seconds at each place where a
hypothesis carried an environment written out while the application named it
behind an abbreviation. Concrete slots are not the mechanism and cost nothing.
Written so that the two sides are the same expression, the chapter checks in
under two seconds rather than 130, with no change to the mathematics. The law
the preceding coding chapters were written under, that an adequacy is discharged at a
variable argument, holds for a **statement** exactly as it does for a
substitution.
<!--zh-->
`LsetGraph`{.Agda} 是对象语言中「取值是实参处的阶段」这个句子，写下来时不点名任何阶段、任何塔、任何序数。`StepAt`{.Agda} 是一次 `extAt`{.Agda} 罩住三个相邻的存在量词，即那个实参、在其处所记录的取值，以及它的可定义幂集；`ApproxAt`{.Agda} 是两个合取项，即定义域与那条步进条件，再无其他。

此处没有任何东西被证两遍。可定义幂集以「落在一位上的描述」的形式从上一章到来，并按交付时的原样使用；函数机器从 `appAt`{.Agda} 与 `domAt`{.Agda} 上读出；而那一步的两种读法就是 `extAt`{.Agda} 自己的那两个。本章所贡献的是形状：一个查阅逼近、而非查阅塔的图，而那是一个图被允许拥有的唯一形状。

有两条裁定被记录在读者与之相遇之处。那一步是一条隶属等价，而非一个单向的收集，这使即将到来的那场归纳的动机保持为命题，并把一条内部的函数外延性引理整个从路线上移除。以及，没有单值性合取项，因为步进条件已经把「在一个实参处记录的每个取值」钉住了，故单值性是一条推论、不是一条假设。

一次测量，而紧随本章的下一章更正了它的诊断。本章曾经花掉的每一秒，都是「同一样东西的两种写法」之间的一次转换，而 Agda 每一次都用「把一个内部装着整条可定义幂集描述的满足关系正规化」来作答：两条读法对着图的那个闭句别名而取，98 秒；每一处「假设把环境写开、而应用把它藏在一个缩写背后」，各 15 秒。具体位不是那个机制，它们分文不取。写成两侧是同一个表达式之后，本章在两秒之内、而不是 130 秒检查完毕，数学分毫未改。前几章据以写下的那条规矩，即充分性在变元实参处解除，对一条**陈述**成立，与它对一次代换成立完全一样。
<!--/-->
