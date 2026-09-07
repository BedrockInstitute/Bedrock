# The codes, as one set

<!--en-->
Every chapter so far has been careful to say that the set of *all* codes is not
an element of `L`, and that nothing needed it. One thing needs it now. The
satisfaction recursion wants an index set closed under subcodes, and a
quantifier's subformula lives one arity up, so it wants the keys at every arity.

The set is not built by collecting the codes. It is cut out of a superset:
`smallDom`{.Agda} contains any small family of elements of `L` in a single stage,
the keys are such a family, and separation inside `L` holds for formulas of any
complexity. So the chapter is one object-language predicate, and the two
directions of adequacy for it.

The predicate has two conjuncts and they are not of equal weight. The second one,
"there merely is a carrier equal to `A` and a set `C` with `x` a member of it, `C`
closed and `C` shaped at that carrier", is unbounded existentials and costs
nothing here: satisfaction is read at the class model, where an existential ranges
over `L` and no stage has to reflect anything.

The first conjunct is the load-bearing one, and it is the finding. `recover`{.Agda}
does not take a member of a closed and shaped set; it takes a member handed over
**as a key at a stated arity**, and nothing in `closedAt`{.Agda} or
`shapedAt`{.Agda} constrains the arity slot. Shapedness binds the arity
existentially and puts no condition on it, so a set holding a pair whose first
component is not a numeral at all satisfies both halves, and the decode has
nothing to say about that pair. That debt was recorded where it was incurred, and
this is where it is paid: the predicate says, from outside, that `x` is a pair
whose first component is a numeral, and it binds that numeral, requiring only
that it lie in `ωʟ`{.Agda}.

The carrier is a slot, and one binder above the slot is what turns it into a
constant. Shapedness takes its carrier as a slot, so something has to occupy that
slot; `hasWitnessAt`{.Agda} leaves the slot to its caller, and `hasWitness`{.Agda}
occupies it with a bound variable pinned by `var zero ≐ con A`{.Agda}.

Splitting it that way is forced, and the reason is the consumer rather than this
chapter. The internal hierarchy binds its stage, so the definable powerset has to
be described at a carrier that is a **bound variable**, and a set enters a formula
only by being named as a constant. A predicate that names its carrier therefore
cannot be spoken under that binder at all, which is why the carrier had to stop
being a constant here. Pinning is what an instance that does hold the carrier as a
set of its own does afterwards, and the pinned form is one existential longer than
the general one: that binder existed only to name the constant.

Which half is hard, then, is settled. Introduction is three lemmas already
proved, applied to the subformula closure. Elimination is where the arity
conjunct is spent, and without it there is no elimination at all.
<!--zh-->
至此每一章都小心地说过：**全体**码之集不是 `L` 的元素，而且没有东西需要它。现在有一样东西需要它了。满足关系那场递归想要一个对诸子码封闭的索引集，而量词的子公式住在高一级的元数上，故它想要的是每个元数处的诸键。

这个集合不是靠把诸码收集起来造出的。它是从一个超集中切出来的：`smallDom`{.Agda} 把 `L` 元素的任意小族装进单一阶段，而诸键正是这样一个族，且 `L` 内部的分离对任意复杂度的公式成立。故本章是一条对象语言谓词，以及它充分性的两个方向。

那条谓词有两个合取项，而二者分量不等。第二项「仅仅存在一个等于 `A` 的载体、以及一个集合 `C`，`x` 是它的成员，`C` 封闭且 `C` 在该载体上成形」是若干无界存在，在此处不费分文：满足关系是在类模型处读的，存在量词在 `L` 上取值，无须任何阶段去反射任何东西。

第一个合取项才是承重的那个，而它就是本章的发现。`recover`{.Agda} 收下的不是「封闭且成形之集的一个成员」；它收下的是**以某个已言明元数处的键的形式**递交过来的成员，而 `closedAt`{.Agda} 与 `shapedAt`{.Agda} 都没有约束元数那一位。形状把元数存在量化，且对它不加任何条件，故一个持有「第一分量压根不是数码的对」的集合同样满足两半，而解码对那个对无话可说。这笔债在欠下之处已被记下，而此处正是偿付之处：那条谓词从外面说出，`x` 是一个第一分量为数码的对，并把那个数码绑定，只要求它属于 `ωʟ`{.Agda}。

载体是一位，而把那一位变成常元的，是它上面那一层绑定。成形性把它的载体取作一位，故必须有什么东西占住那一位；`hasWitnessAt`{.Agda} 把那一位留给自己的调用方，而 `hasWitness`{.Agda} 用一个由 `var zero ≐ con A`{.Agda} 钉住的被绑定变元占住它。

这样一拆是被逼的，而理由出在消费方、不出在本章。内部层级把自己的阶段绑定起来，故可定义幂集必须在一个**被绑定变元**形式的载体上被描述，而集合进入公式的唯一方式是被点名为常元。于是一条点名了自己载体的谓词，在那层绑定之下压根说不出口，而这正是载体在此处不得不不再是常元的原因。钉住，是那些确实把载体握作自己一个集合的实例事后要做的事；而被钉住的形式比一般的形式长一个存在量词：那个绑定当初仅仅是为了点名那个常元而存在的。

于是哪一半难，已然定案。引入是三条早已证好的引理，施于子公式闭包。消去才是花掉元数合取项的地方，而没有它，就根本没有消去。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.CodeSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Mapping using ( mapFo )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate )
open import L.Coding.Expressions {ℓ} using ( tagAtL; tagAtL-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt )
open import L.Coding.InL {ℓ} using ( key; keyL; codeL; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ} using ( shapedAt; closureShaped )
open import L.Coding.Recover {ℓ} using ( keyOf-fst; module Decode )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Is a key at a stated arity
<!--zh-->
## 是某个已言明元数处的键
<!--/-->

<!--en-->
One reader, and it is the only new piece of object language the chapter needs. A
key at arity `k` is a pair whose first component is the numeral `k`, and the tag
reader already says exactly that of a *named* second component. What is wanted
here is the second component left unnamed, so the reader is the tag reader under
one existential, and its two directions are the existential's two directions with
the tag reader's adequacy equation discharged inside.

The equation is discharged with the index, the numeral and the environment all
still variables, because that is the only way it is cheap.
<!--zh-->
一条读式，也是本章所需的唯一一件新的对象语言。元数 `k` 处的键，是第一分量为数码 `k` 的对，而标签读式对一个**点了名的**第二分量所说的恰是这句话。此处想要的是第二分量不点名，故这条读式就是标签读式套在一个存在量词之下，而它的两个方向就是那个存在量词的两个方向，标签读式的适足等式在里面交付。

那条等式在索引、数码与环境都还是变元时交付，因为只有这样它才便宜。
<!--/-->

```agda
keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

keyArityAtL-out : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n)
                → ⟨ γ ⊨ keyArityAtL c k ⟩
                → ∥ (Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))) ∥₁
keyArityAtL-out c k γ = PT.map
  (λ { (z , hz) →
    z , subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (z ∷ γ)) hz })

keyArityAtL-in : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) (z : S)
               → fst (lookup c γ) ≡ pr (# k) (fst z)
               → ⟨ γ ⊨ keyArityAtL c k ⟩
keyArityAtL-in c k γ z e =
  ∣ z , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (z ∷ γ))) e ∣₁
```

<!--en-->
## Is a key at some arity
<!--zh-->
## 是某个元数处的键
<!--/-->

<!--en-->
The reader above names its arity as a metalevel numeral, which is what pins the
arity to one; a set that has to hold subcodes cannot do that, because a
quantifier's subformula lives one arity up. So the arity has to become a bound
set, and something has to say of that set what `# k`{.Agda} said for free: that
it is a numeral.

Saying it costs one constant. `ωʟ`{.Agda} is an element of `L` whose members are
exactly the numerals, so "the arity component lies in `ωʟ`{.Agda}" *is* the
condition, written with the same unbounded membership the second conjunct already
uses. Two existentials, one for the arity and one for the payload, the pair reader
between them, and the membership on the arity.

Reading it back is where the choice pays. `ω-specL`{.Agda} is an equation between
propositions, not an implication, so a member of `ωʟ`{.Agda} *is* a truncated
natural number, and one composition with the chain's projection equation turns it
into the metalevel `# m`{.Agda} that `recover`{.Agda} takes as its arity argument.
There is no induction in either direction; the numeral chapter did it.
<!--zh-->
上面那条读式把元数点名为一个元语言的数码，而正是这一点把元数钉在一上；一个必须持有诸子码的集合做不到这件事，因为量词的子公式住在高一级的元数上。故元数必须变成一个被绑定的集合，而须有什么东西对那个集合说出 `# k`{.Agda} 白送的那句话：它是一个数码。

说出它只花一个常元。`ωʟ`{.Agda} 是 `L` 的元素，其成员恰是诸数码，故「元数分量属于 `ωʟ`{.Agda}」**就是**那个条件，且写法与第二个合取项早已在用的那种无界隶属相同。两个存在量词，一个管元数、一个管载荷，中间是对读式，再加上落在元数上的那条隶属。

读回来的时候，这个选择才见分晓。`ω-specL`{.Agda} 是命题之间的等式，不是蕴含，故 `ωʟ`{.Agda} 的成员**就是**一个被截断的自然数，而与链的投影等式复合一次，就把它变成 `recover`{.Agda} 作为元数实参所收下的那个 `# m`{.Agda}。两个方向里都没有归纳；数码那一章已经做过了。
<!--/-->

```agda
arityNumAtL : ∀ {n} → Fin n → Formula S n
arityNumAtL c = ∃̇ (∃̇ (prAtL (suc (suc c)) (suc zero) zero
                     ∧̇ (var (suc zero) ∈̇ con ωʟ)))

arityNumAtL-out : ∀ {n} (c : Fin n) (γ : S ^ n)
                → ⟨ γ ⊨ arityNumAtL c ⟩
                → ∥ (Σ[ m ∈ ℕ ] Σ[ z ∈ S ]
                      (fst (lookup c γ) ≡ pr (# m) (fst z))) ∥₁
arityNumAtL-out c γ = PT.rec squash₁ (λ { (ar , h) →
  PT.rec squash₁ (λ { (z , (hp , hω)) → PT.map
    (λ { (m , qm) → lower m , z
       , ( subst ⟨_⟩
             (prAtL-adequate (suc (suc c)) (suc zero) zero (z ∷ ar ∷ γ)) hp
         ∙ cong (λ w → pr w (fst z)) (qm ∙ numeralL-fst (lower m)) ) })
    (subst ⟨_⟩ (ω-specL ar) hω) }) h })

arityNumAtL-in : ∀ {n} (c : Fin n) (γ : S ^ n) (m : ℕ) (z : S)
               → fst (lookup c γ) ≡ pr (# m) (fst z)
               → ⟨ γ ⊨ arityNumAtL c ⟩
arityNumAtL-in c γ m z e = ∣ numeralL m , ∣ z
  , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc c)) (suc zero) zero
        (z ∷ numeralL m ∷ γ)))
        (e ∙ cong (λ w → pr w (fst z)) (sym (numeralL-fst m)))
    , subst ⟨_⟩ (sym (ω-specL (numeralL m))) ∣ lift m , refl ∣₁ ) ∣₁ ∣₁
```

<!--en-->
## The predicate
<!--zh-->
## 那条谓词
<!--/-->

<!--en-->
Two conjuncts, at one free variable. The first pins the arity from outside, which
is the conjunct the previous chapter asked for by name. The second is a witness
for the decode's two hypotheses: a set holding the argument, closed and shaped.

Nothing in the second conjunct is bounded, and nothing has to be. The witness is
produced from a formula's own subformula closure in the introduction, and
consumed as a set of `L` in the elimination, and the class model is where both
readings happen.

The second conjunct is written twice: once at two slots, the carrier and the
argument, and once with the carrier pinned to a constant. The general one is a
single existential, for the set; the pinned one wraps it in the binder that names
`A`, and that binder is the entire difference between them.
<!--zh-->
两个合取项，落在一个自由变元上。第一项从外面钉住元数，而这正是上一章点名索取的那个合取项。第二项是解码那两条假设的见证：一个装着实参、既封闭又成形的集合。

第二项里没有任何东西是有界的，也不需要有。那个见证在引入这边由一条公式自己的子公式闭包产出，在消去那边作为 `L` 的一个集合被消费，而两种读法都发生在类模型处。

第二个合取项写了两遍：一遍落在两个槽位上，即载体与实参；另一遍把载体钉在一个常元上。一般的那一遍只有一个存在量词，管那个集合；被钉住的那一遍把它裹进点名 `A` 的那层绑定，而那层绑定就是二者之间的全部差别。
<!--/-->

```agda
hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                      ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))

hasWitness : S → Formula S 1
hasWitness A = ∃̇ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero))

isCodeAny : S → Formula S 1
isCodeAny A = arityNumAtL zero ∧̇ hasWitness A
```

<!--en-->
## The superset, and the set
<!--zh-->
## 那个超集，与那个集合
<!--/-->

<!--en-->
The carrier is fixed, and the consumer will fix it at a stage. Its members are
the alphabet, exactly as the coding chapters' two parameters expect: the
embedding into the hierarchy, and the certificate that what it lands on is
constructible. The second is transitivity of `L` applied once, and the membership
it is applied to is named separately, because the shape predicate now asks for it
in its own right.

Then the superset. `smallDom`{.Agda} asks for a small family of elements of `L`
and returns a stage containing all of it; the family is indexed by the pairs of
an arity and a formula at it. The type is of the right size because syntax is an
inductive type at the alphabet's own level, and the arity is a natural number,
which costs no level at all. What comes back contains every key and much else,
and separation removes the else.

The set is sealed where it is built. Unsealed, every later type mentioning it
would carry the separation instrument's unfolding into conversion, and the facts
exported here are all any consumer needs. Only the ones that read a separation
are inside a seal; the directions back and the equations they compose into are
outside, since none of them needs to know what the set was cut out of.
<!--zh-->
载体是固定的，而消费方会把它固定在某个阶段上。它的诸成员就是字母表，恰如诸编码章的两个参数所期待：到层级的嵌入，以及「它落到的东西可构造」这份证书。后者是 `L` 的传递性用一次，而它所施于的那条隶属关系被单独命名，因为形状谓词如今按其自身的名义索取它。

然后是那个超集。`smallDom`{.Agda} 索取 `L` 元素的一个小族，返回一个装下它全部的阶段；那个族以「一个元数连同该元数处的一条公式」之对为索引。它是尺寸正确的类型，因为语法是在字母表自身层级上的归纳类型，而元数是自然数，压根不花层级。回来的东西含有每个键，也含有别的许多；而分离把「别的」去掉。

这个集合在它被造出之处封印。不封印的话，此后每个提到它的类型都会把分离器械的展开带进转换检查，而此处导出的诸事实已是任何消费方所需的全部。封印之内只有读分离的那几条；回来的那些方向、以及它们复合成的那些等式在封印之外，因为它们都不需要知道这个集合是从什么里切出来的。
<!--/-->

```agda
module _ (A : S) where
  private
    ι : ⟪ fst A ⟫ → V ℓ
    ι = ⟪ fst A ⟫↪

    ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ fst A ⟩
    ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

    ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
    ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) (A .snd)

  codeS : ∀ {n} → Formula ⟪ fst A ⟫ n → S
  codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ

  keyS : ∀ {n} → Formula ⟪ fst A ⟫ n → S
  keyS φ = key ι ιL φ , keyL ι ιL φ

  private
    smallAny : Σ[ d ∈ S ] ((p : Σ[ n ∈ ℕ ] Formula ⟪ fst A ⟫ n)
                          → ⟨ keyS (snd p) ∈ˢ d ⟩)
    smallAny = smallDom (Σ[ n ∈ ℕ ] Formula ⟪ fst A ⟫ n) (λ p → keyS (snd p))

    sepAny : isContr
      (SetOf (λ x → (x ∈ˢ smallAny .fst) ⊓ ((x ∷ []) ⊨ isCodeAny A)))
    sepAny = hasSeparationL (smallAny .fst) (isCodeAny A)
```

<!--en-->
## The witness, in and out
<!--zh-->
## 那个见证，进与出
<!--/-->

<!--en-->
Both halves of the second conjunct are proved here, once, at a variable arity, a
variable carrier slot and a variable environment, and everything below applies
them. The arity may be variable because the conjunct never mentions it: the
introduction produces a closed, shaped set for a formula of any arity, and the
elimination consumes one and calls the decode, which took the arity as an
argument from the start. The carrier and the environment may be variable because
every lemma the two halves are built from already takes them so.

Introduction is the half with nothing in it. The witness is the subformula
closure, whose three obligations are `key∈closure`{.Agda}, `closureClosed`{.Agda}
and `closureShaped`{.Agda}, one chapter each and all already discharged. The last
of them asks for one thing more, that every constant is a member of the carrier,
and at this alphabet that is the fact the alphabet was defined by, carried across
the slot's equation.

Elimination is the other half, and it starts from the member already in key form
at a stated arity, which is what `recover`{.Agda} demands and what nothing in the
second conjunct would supply. The carrier slot's equation turns a membership in
whatever that slot holds into a membership in `A`, which is what makes the
decode's hypothesis dischargeable: `A`'s members are exactly the image of
`⟪ A ⟫`, by the presentation of a set by its own members. Read the existential
and a closed, shaped set arrives with it. Then the decode runs, and its answer is
a formula over the carrier, at the arity it was handed.

The pinned pair is these two at the environment the naming binder makes, and
that is the whole of what pinning costs: introduction supplies `A` for the binder
and `refl`{.Agda} for its equation, elimination reads the binder off and hands
what it holds to the general form. **Reading it off is where the payload has to
be named.** Left to inference, the truncation's payload at a pinned carrier is a
metavariable standing for the satisfaction of a formula the elaborator has not
committed to, and the same two lines that check in two seconds with the type
written out ran past 140 seconds without it and were killed there. This is the
law the recursion's totality hypothesis recorded, met again in a different place:
it is not about the graph, it is about `PT.rec`{.Agda} at a concrete environment.
<!--zh-->
第二个合取项的两半都在此处、在变元元数、变元载体位与变元环境上一次证完，而下面的一切只是把它们施用一遍。元数可以是变元，是因为那个合取项从不提它：引入为任意元数的一条公式产出一个既封闭又成形的集合，消去消费一个这样的集合并调用解码，而解码从一开始就把元数取作实参。载体与环境可以是变元，则是因为两半所倚的每条引理本来就是这样收它们的。

引入是里面什么也没有的那一半。那个见证是子公式闭包，其三笔债 `key∈closure`{.Agda}、`closureClosed`{.Agda} 与 `closureShaped`{.Agda} 各出一章，且都已偿清。其中最后一条多要一件东西，即每个常元都是载体的成员，而在这个字母表上，那正是字母表当初据以定义的那件事，沿那一位的等式搬过去即可。

消去是另一半，而它从「已以某个已言明元数处的键的形式到场的那个成员」出发，那正是 `recover`{.Agda} 所索取的、也是第二个合取项供不出的。载体那一位的等式把「属于那一位所持有的东西」变成「属于 `A`」，而这正是解码那条假设得以交付的原因：`A` 的诸成员恰是 `⟪ A ⟫` 的像，凭的是「一个集合由其自身诸成员的呈现」。读出那个存在量词，一个既封闭又成形的集合便随之到场。随后解码开跑，而它的答案是载体之上、落在它被递交的那个元数处的一条公式。

被钉住的那一对，就是这两条落在「点名那层绑定所造出的环境」上，而钉住的全部代价也就在此：引入为那层绑定供上 `A`、为它的等式供上 `refl`{.Agda}，消去把那层绑定读出来、再把它所持有的东西交给一般的形式。**读出来的地方，正是载荷必须被点名之处。** 若交给推断，被钉住的载体处那个截断的载荷就是一个元变元，代表着「一条求解器尚未认定的公式的满足关系」；同样两行，把类型写出来时两秒检查完毕，不写则跑过 140 秒并在那里被杀掉。这就是递归那条全性假设所记下的规矩，在另一处再次遇上：它不关乎那个图，它关乎在具体环境处的 `PT.rec`{.Agda}。
<!--/-->

```agda
  witnessAt-in : ∀ {n k} (b c : Fin n) (γ : S ^ n) (φ : Formula ⟪ fst A ⟫ k)
               → fst (lookup b γ) ≡ fst A
               → fst (lookup c γ) ≡ fst (keyS φ)
               → ⟨ γ ⊨ hasWitnessAt b c ⟩
  witnessAt-in b c γ φ qb qc = ∣ clo ι ιL φ
    , ( subst (λ w → ⟨ w ∈ fst (clo ι ιL φ) ⟩) (sym qc) (key∈closure ι ιL φ)
      , ( closureClosed ι ιL φ γ
        , closureShaped ι ιL φ b γ
            (λ m → subst (λ w → ⟨ ι m ∈ w ⟩) (sym qb) (ι∈ m)) ) ) ∣₁

  witnessAt-out : ∀ {n} (b c : Fin n) (γ : S ^ n)
                → fst (lookup b γ) ≡ fst A
                → ⟨ γ ⊨ hasWitnessAt b c ⟩
                → (k : ℕ) (z : S) → fst (lookup c γ) ≡ pr (# k) (fst z)
                → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ]
                      (fst (lookup c γ) ≡ fst (keyS ψ))) ∥₁
  witnessAt-out b c γ qb hw k z qz = PT.rec squash₁ viaSlot hw
    where
    Target : Type (ℓ-suc ℓ)
    Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ]
                 (fst (lookup c γ) ≡ fst (keyS ψ))) ∥₁

    onto : (y : V ℓ) → ⟨ y ∈ fst (lookup b γ) ⟩
         → ∥ Σ[ m ∈ ⟪ fst A ⟫ ] (ι m ≡ y) ∥₁
    onto y y∈ = ∣ ∈-asFiber {a = y} {b = fst A}
      (subst (λ w → ⟨ y ∈ w ⟩) qb y∈) ∣₁

    viaSlot : Σ[ C ∈ S ] ⟨ (C ∷ γ) ⊨ ((var (suc c) ∈̇ var zero)
                ∧̇ (closedAt zero ∧̇ shapedAt zero (suc b))) ⟩
            → Target
    viaSlot (C , (x∈C , (hcl , hsh))) = PT.map
      (λ { (ψ , qψ) → ψ , (qz ∙ cong (pr (# k)) (sym qψ)) })
      (Decode.recover ι zero (suc b) (C ∷ γ) onto hcl hsh k z
        (subst (λ w → ⟨ w ∈ fst C ⟩) (qz ∙ sym (keyOf-fst k z)) x∈C))

  private
    witness-in : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
               → ⟨ (keyS φ ∷ []) ⊨ hasWitness A ⟩
    witness-in φ = ∣ A , ( refl
      , witnessAt-in zero (suc zero) (A ∷ keyS φ ∷ []) φ refl refl ) ∣₁

    witness-out : (x : S) → ⟨ (x ∷ []) ⊨ hasWitness A ⟩
                → (k : ℕ) (z : S) → fst x ≡ pr (# k) (fst z)
                → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁
    witness-out x hw k z qz = PT.rec squash₁ viaCarrier hw
      where
      viaCarrier : Σ[ B ∈ S ] ⟨ (B ∷ x ∷ [])
                     ⊨ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero)) ⟩
                 → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁
      viaCarrier (B , (qB , hB)) =
        witnessAt-out zero (suc zero) (B ∷ x ∷ []) qB hB k z qz
```

<!--en-->
## The set at every arity
<!--zh-->
## 那个集合，落在每个元数上
<!--/-->

<!--en-->
What comes out is the class of keys of formulas over the carrier **at any
arity**, which is the class a recursion over subcodes has to be indexed by,
because a quantifier's subformula lives one arity up and the arity-one class does
not contain it.
<!--zh-->
出来的是载体之上诸公式**在任意元数处**的诸键之类，而那正是「对诸子码作递归」必须以之为索引的那一类，因为量词的子公式住在高一级的元数上，而一元那一类装不下它。
<!--/-->

```agda
  IsKeyOverAny : S → Ω
  IsKeyOverAny x =
    ∥ (Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A ⟫ n ] (fst x ≡ fst (keyS ψ))) ∥₁
    , squash₁

  opaque
    AllCodes : S
    AllCodes = sepAny .fst .fst

    key∈AllCodes : ∀ {n} (φ : Formula ⟪ fst A ⟫ n) → ⟨ keyS φ ∈ˢ AllCodes ⟩
    key∈AllCodes {n} φ = subst ⟨_⟩ (sym (sepAny .fst .snd (keyS φ)))
      ( smallAny .snd (n , φ)
      , ( arityNumAtL-in zero (keyS φ ∷ []) n (codeS φ) refl
        , witness-in φ ) )

    AllCodes-out : (x : S) → ⟨ x ∈ˢ AllCodes ⟩ → ⟨ IsKeyOverAny x ⟩
    AllCodes-out x x∈ = PT.rec squash₁
      (λ { (k , z , qz) → PT.map (λ { (ψ , q) → k , ψ , q })
        (witness-out x (sat .snd) k z qz) })
      (arityNumAtL-out zero (x ∷ []) (sat .fst))
      where
      sat : ⟨ (x ∷ []) ⊨ isCodeAny A ⟩
      sat = subst ⟨_⟩ (sepAny .fst .snd x) x∈ .snd

  AllCodes-in : (x : S) → ⟨ IsKeyOverAny x ⟩ → ⟨ x ∈ˢ AllCodes ⟩
  AllCodes-in x = PT.rec (snd (x ∈ˢ AllCodes))
    (λ { (n , ψ , q) →
      subst (λ w → ⟨ w ∈ fst AllCodes ⟩) (sym q) (key∈AllCodes ψ) })
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
One set, one predicate. `AllCodes`{.Agda} is an element of `L` whose members are
exactly the keys of the formulas over the carrier, at every arity, by
`AllCodes-out`{.Agda} and `AllCodes-in`{.Agda}.

The whole content is in two conjuncts, and both are of the same kind. Closedness
and shapedness together recognize the *shape* of a code and say nothing about the
arity a key carries or the alphabet its constants come from, so a decode written
against them has to be handed both, and a set built from them has to state both.
`smallDom`{.Agda} and general-formula separation do the rest, and neither needed
anything the earlier chapters had not already paid for.

The set exists for the *class* it characterizes, not for a theorem about it. A
recursion over codes has to answer at a code's subcodes, a quantifier's
subformula lives one arity up, and the arity-one class does not contain it, so
the domain has to be the keys at every arity.
<!--zh-->
一个集合，一条谓词。`AllCodes`{.Agda} 是 `L` 的元素，凭 `AllCodes-out`{.Agda} 与 `AllCodes-in`{.Agda}，它的诸成员恰是载体之上诸公式在**每个**元数处的诸键。

全部内容在两个合取项里，而两者同类。封闭性与成形性合起来认出的是码的**形状**，对一个键所携带的元数、以及它的诸常元出自哪个字母表，都只字未提，故一条对着它们写下的解码必须被递交这两样，而一个由它们造出的集合必须把这两样说出来。`smallDom`{.Agda} 与任意公式的分离做掉其余，而两者都没有索取前几章尚未付清的任何东西。

这个集合的存在，是为了它所刻画的那**一类**，而不是为了某条关于它的定理。对码的递归必须在一个码的诸子码处作答，而量词的子公式住在高一级的元数上，一元那一类装不下它，故定义域只能是每个元数处的诸键。
<!--/-->
