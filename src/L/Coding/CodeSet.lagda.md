# The codes, as one set

<!--en-->
Every chapter so far has been careful to say that the set of *all* codes is not
an element of `L`, and that nothing needed it. Two things need it now, and they
want different sets. The definable powerset takes syntax as its index type,
`Def A = sett (Formula ⟪A⟫ 1) defSet`, so internalizing definability at a stage
means naming the arity-one formulas over that stage from inside the model, and a
formula can only name a set. The satisfaction recursion wants an index set closed
under subcodes, and a quantifier's subformula lives one arity up, so it wants the
keys at every arity instead.

Neither set is built by collecting the codes. Each is cut out of a superset:
`smallDom`{.Agda} contains any small family of elements of `L` in a single stage,
the keys are such a family, and separation inside `L` holds for formulas of any
complexity. So the chapter is two object-language predicates that differ in one
conjunct, and the two directions of adequacy for each.

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
whose first component is a numeral. Which numeral is the only difference between
the two predicates. The arity-one set names it, the all-arity set binds it and
requires only that it lie in `ωʟ`{.Agda}, and everything else in the chapter is
shared verbatim.

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
至此每一章都小心地说过：**全体**码之集不是 `L` 的元素，而且没有东西需要它。现在有两样东西需要它了，而它们想要的不是同一个集合。可定义幂集以语法为索引类型，`Def A = sett (Formula ⟪A⟫ 1) defSet`，故在一个阶段处内化可定义性，就意味着从模型内部点名该阶段之上的一元公式，而公式只能点名集合。满足关系那场递归想要一个对诸子码封闭的索引集，而量词的子公式住在高一级的元数上，故它想要的是每个元数处的诸键。

两个集合都不是靠把诸码收集起来造出的。各自都是从一个超集中切出来的：`smallDom`{.Agda} 把 `L` 元素的任意小族装进单一阶段，而诸键正是这样一个族，且 `L` 内部的分离对任意复杂度的公式成立。故本章是两条只差一个合取项的对象语言谓词，以及各自适足性的两个方向。

那条谓词有两个合取项，而二者分量不等。第二项「仅仅存在一个等于 `A` 的载体、以及一个集合 `C`，`x` 是它的成员，`C` 封闭且 `C` 在该载体上成形」是若干无界存在，在此处不费分文：满足关系是在类模型处读的，存在量词在 `L` 上取值，无须任何阶段去反射任何东西。

第一个合取项才是承重的那个，而它就是本章的发现。`recover`{.Agda} 收下的不是「封闭且成形之集的一个成员」；它收下的是**以某个已言明元数处的键的形式**递交过来的成员，而 `closedAt`{.Agda} 与 `shapedAt`{.Agda} 都没有约束元数那一位。形状把元数存在量化，且对它不加任何条件，故一个持有「第一分量压根不是数码的对」的集合同样满足两半，而解码对那个对无话可说。这笔债在欠下之处已被记下，而此处正是偿付之处：那条谓词从外面说出，`x` 是一个第一分量为数码的对。是哪个数码，正是两条谓词之间唯一的差别。一元那个集合把它点名，全元数那个集合把它绑定、只要求它属于 `ωʟ`{.Agda}，而本章其余一切逐字共享。

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
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; tagAtL; tagAtL-adequate; closedAt )
open import L.Coding.InL {ℓ} using ( key; keyL; codeL; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ} using ( shapedAt; closureShaped )
open import L.Coding.Recover {ℓ} using ( keyOf-fst; module Decode )

open import Cubical.Functions.Logic using ( ⇔toPath )
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
still variables, because that is the only way it is cheap. Both call sites below
are at a fixed index and a fixed numeral, and neither pays for the unfolding.
<!--zh-->
一条读式，也是本章所需的唯一一件新的对象语言。元数 `k` 处的键，是第一分量为数码 `k` 的对，而标签读式对一个**点了名的**第二分量所说的恰是这句话。此处想要的是第二分量不点名，故这条读式就是标签读式套在一个存在量词之下，而它的两个方向就是那个存在量词的两个方向，标签读式的适足等式在里面交付。

那条等式在索引、数码与环境都还是变元时交付，因为只有这样它才便宜。下面两个调用点都在固定的索引与固定的数码上，而两者都不为那次展开付账。
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
`A`, and that binder is the entire difference between them. Both predicates below
take the pinned form verbatim, and so do both halves of both adequacy proofs;
what separates the two predicates is the arity conjunct and nothing else.
<!--zh-->
两个合取项，落在一个自由变元上。第一项从外面钉住元数，而这正是上一章点名索取的那个合取项。第二项是解码那两条假设的见证：一个装着实参、既封闭又成形的集合。

第二项里没有任何东西是有界的，也不需要有。那个见证在引入这边由一条公式自己的子公式闭包产出，在消去那边作为 `L` 的一个集合被消费，而两种读法都发生在类模型处。

第二个合取项写了两遍：一遍落在两个槽位上，即载体与实参；另一遍把载体钉在一个常元上。一般的那一遍只有一个存在量词，管那个集合；被钉住的那一遍把它裹进点名 `A` 的那层绑定，而那层绑定就是二者之间的全部差别。下面两条谓词都逐字取用被钉住的那个形式，两条适足性的两半也都如此；分开这两条谓词的只有元数合取项，别无其他。
<!--/-->

```agda
hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                      ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))

hasWitness : S → Formula S 1
hasWitness A = ∃̇ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero))

isCode : S → Formula S 1
isCode A = keyArityAtL zero 1 ∧̇ hasWitness A

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

Then the supersets, one for each set. `smallDom`{.Agda} asks for a small family of
elements of `L` and returns a stage containing all of it; the arity-one family is
indexed by the arity-one formulas over the alphabet, and the all-arity family by
the pairs of an arity and a formula at it. Both are types of the right size
because syntax is an inductive type at the alphabet's own level, and the arity is
a natural number, which costs no level at all. What comes back contains every key
and much else, and separation removes the else.

Both sets are sealed where they are built. Unsealed, every later type mentioning
one would carry the separation instrument's unfolding into conversion, and the
facts exported here are all any consumer needs. Only the ones that read a
separation are inside a seal; the directions back and the equations they compose
into are outside, since none of them needs to know what the set was cut out of.
<!--zh-->
载体是固定的，而消费方会把它固定在某个阶段上。它的诸成员就是字母表，恰如诸编码章的两个参数所期待：到层级的嵌入，以及「它落到的东西可构造」这份证书。后者是 `L` 的传递性用一次，而它所施于的那条隶属关系被单独命名，因为形状谓词如今按其自身的名义索取它。

然后是那两个超集，一集一个。`smallDom`{.Agda} 索取 `L` 元素的一个小族，返回一个装下它全部的阶段；一元那个族以字母表之上的一元公式为索引，全元数那个族则以「一个元数连同该元数处的一条公式」之对为索引。两者都是尺寸正确的类型，因为语法是在字母表自身层级上的归纳类型，而元数是自然数，压根不花层级。回来的东西含有每个键，也含有别的许多；而分离把「别的」去掉。

两个集合都在它们被造出之处封印。不封印的话，此后每个提到其一的类型都会把分离器械的展开带进转换检查，而此处导出的诸事实已是任何消费方所需的全部。封印之内只有读分离的那几条；回来的那些方向、以及它们复合成的那些等式在封印之外，因为它们都不需要知道这个集合是从什么里切出来的。
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
    small : Σ[ d ∈ S ] ((φ : Formula ⟪ fst A ⟫ 1) → ⟨ keyS φ ∈ˢ d ⟩)
    small = smallDom (Formula ⟪ fst A ⟫ 1) keyS

    sep : isContr (SetOf (λ x → (x ∈ˢ small .fst) ⊓ ((x ∷ []) ⊨ isCode A)))
    sep = hasSeparationL (small .fst) (isCode A)

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
Both halves of the second conjunct are proved here, once, at a variable arity,
and both sets below simply apply them. That is possible because the conjunct
never mentions the arity: the introduction produces a closed, shaped set for a
formula of any arity, and the elimination consumes one and calls the decode,
which took the arity as an argument from the start.

Introduction is the half with nothing in it. The carrier existential takes `A`
itself and its equation is `refl`{.Agda}; the inner existential's witness is the
subformula closure, whose three obligations are `key∈closure`{.Agda},
`closureClosed`{.Agda} and `closureShaped`{.Agda}, one chapter each and all
already discharged. The last of them asks for one thing more, that every constant
is a member of the carrier, and at this alphabet that is the fact the alphabet was
defined by.

Elimination is the other half, and it starts from the member already in key form
at a stated arity, which is what `recover`{.Agda} demands and what nothing in the
second conjunct would supply. Read the carrier existential and its equation turns
a membership in the bound carrier into a membership in `A`, which is what makes
the decode's hypothesis dischargeable: `A`'s members are exactly the image of
`⟪ A ⟫`, by the presentation of a set by its own members. Read the inner
existential and a closed, shaped set arrives with it. Then the decode runs, and
its answer is a formula over the carrier, at the arity it was handed.
<!--zh-->
第二个合取项的两半都在此处、在变元元数上、一次证完，而下面两个集合只是把它们施用一遍。这之所以可行，是因为那个合取项从不提元数：引入为任意元数的一条公式产出一个既封闭又成形的集合，消去消费一个这样的集合并调用解码，而解码从一开始就把元数取作实参。

引入是里面什么也没有的那一半。载体那个存在量词取 `A` 自身，它的等式是 `refl`{.Agda}；内层存在量词的见证是子公式闭包，其三笔债 `key∈closure`{.Agda}、`closureClosed`{.Agda} 与 `closureShaped`{.Agda} 各出一章，且都已偿清。其中最后一条多要一件东西，即每个常元都是载体的成员，而在这个字母表上，那正是字母表当初据以定义的那件事。

消去是另一半，而它从「已以某个已言明元数处的键的形式到场的那个成员」出发，那正是 `recover`{.Agda} 所索取的、也是第二个合取项供不出的。读出载体那个存在量词，它的等式把「属于被绑定的那个载体」变成「属于 `A`」，而这正是解码那条假设得以交付的原因：`A` 的诸成员恰是 `⟪ A ⟫` 的像，凭的是「一个集合由其自身诸成员的呈现」。读出内层存在量词，一个既封闭又成形的集合便随之到场。随后解码开跑，而它的答案是载体之上、落在它被递交的那个元数处的一条公式。
<!--/-->

```agda
  private
    witness-in : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
               → ⟨ (keyS φ ∷ []) ⊨ hasWitness A ⟩
    witness-in φ = ∣ A , ( refl
      , ∣ clo ι ιL φ
        , ( key∈closure ι ιL φ
          , ( closureClosed ι ιL φ (A ∷ keyS φ ∷ [])
            , closureShaped ι ιL φ zero (A ∷ keyS φ ∷ []) ι∈ ) ) ∣₁ ) ∣₁

    witness-out : (x : S) → ⟨ (x ∷ []) ⊨ hasWitness A ⟩
                → (k : ℕ) (z : S) → fst x ≡ pr (# k) (fst z)
                → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁
    witness-out x hw k z qz = PT.rec squash₁ viaCarrier hw
      where
      Target : Type (ℓ-suc ℓ)
      Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁

      viaCarrier : Σ[ B ∈ S ] ⟨ (B ∷ x ∷ [])
                     ⊨ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero)) ⟩
                 → Target
      viaCarrier (B , (qB , hB)) = PT.rec squash₁ viaSlot hB
        where
        onto : (y : V ℓ) → ⟨ y ∈ fst B ⟩
             → ∥ Σ[ c ∈ ⟪ fst A ⟫ ] (ι c ≡ y) ∥₁
        onto y y∈ = ∣ ∈-asFiber {a = y} {b = fst A}
          (subst (λ w → ⟨ y ∈ w ⟩) qB y∈) ∣₁

        viaSlot : Σ[ C ∈ S ] ⟨ (C ∷ B ∷ x ∷ [])
                    ⊨ ((var (suc (suc zero)) ∈̇ var zero)
                       ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
                → Target
        viaSlot (C , (x∈C , (hcl , hsh))) = PT.map
          (λ { (ψ , qψ) → ψ , (qz ∙ cong (pr (# k)) (sym qψ)) })
          (Decode.recover ι zero (suc zero) (C ∷ B ∷ x ∷ []) onto hcl hsh k z
            (subst (λ w → ⟨ w ∈ fst C ⟩) (qz ∙ sym (keyOf-fst k z)) x∈C))
```

<!--en-->
## Both directions, and they meet
<!--zh-->
## 两个方向，而它们会合
<!--/-->

<!--en-->
The statement both directions are about is written first, and it is one class:
the keys, at arity one, of the formulas over the carrier. Introduction says every
such key is a member and elimination says every member is such a key, so the two
are no longer two bounds on the set but one characterization of it.

What is left of each direction, once the witness is factored out, is the arity
conjunct. Introduction adds two things to `witness-in`{.Agda}: membership in the
superset, by the family the key indexes, and the arity conjunct, whose witness is
the code and whose equation is `refl`{.Agda}. Elimination reads the arity conjunct
first, because without it the member does not arrive in key form at all, and hands
what it reads to `witness-out`{.Agda}.
<!--zh-->
两个方向所谈的那条陈述先写出来，而它是一个类：载体之上诸公式在元数一处的诸键。引入说每个这样的键都是成员，消去说每个成员都是这样一个键，故二者不再是这个集合的两道界，而是它的一条刻画。

把那个见证提出去之后，每个方向剩下的就是元数合取项。引入在 `witness-in`{.Agda} 之上添两样：属于那个超集，凭那个键所索引的族；以及元数合取项，其见证是那条码、其等式是 `refl`{.Agda}。消去先读元数合取项，因为没有它那个成员根本不以键的形式到场，再把读到的东西交给 `witness-out`{.Agda}。
<!--/-->

```agda
  IsKeyOver : S → Ω
  IsKeyOver x =
    ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst x ≡ fst (keyS ψ))) ∥₁ , squash₁

  opaque
    Codes : S
    Codes = sep .fst .fst

    key∈Codes : (φ : Formula ⟪ fst A ⟫ 1) → ⟨ keyS φ ∈ˢ Codes ⟩
    key∈Codes φ = subst ⟨_⟩ (sym (sep .fst .snd (keyS φ)))
      ( small .snd φ
      , ( keyArityAtL-in zero 1 (keyS φ ∷ []) (codeS φ) refl
        , witness-in φ ) )

    Codes-out : (x : S) → ⟨ x ∈ˢ Codes ⟩ → ⟨ IsKeyOver x ⟩
    Codes-out x x∈ = PT.rec squash₁
      (λ { (z , qz) → witness-out x (sat .snd) 1 z qz })
      (keyArityAtL-out zero 1 (x ∷ []) (sat .fst))
      where
      sat : ⟨ (x ∷ []) ⊨ isCode A ⟩
      sat = subst ⟨_⟩ (sep .fst .snd x) x∈ .snd

  Codes-in : (x : S) → ⟨ IsKeyOver x ⟩ → ⟨ x ∈ˢ Codes ⟩
  Codes-in x = PT.rec (snd (x ∈ˢ Codes))
    (λ { (ψ , q) → subst (λ w → ⟨ w ∈ fst Codes ⟩) (sym q) (key∈Codes ψ) })

  Codes-spec : (x : S) → (x ∈ˢ Codes) ≡ IsKeyOver x
  Codes-spec x = ⇔toPath (Codes-out x) (Codes-in x)
```

<!--en-->
## The round trip
<!--zh-->
## 往返
<!--/-->

<!--en-->
The two directions are now stated over the same alphabet, and they compose into
an equation between propositions: a member of `Codes`{.Agda} is exactly a key of
a formula over the carrier. The direction back is one substitution, because
membership depends on the underlying set alone and a key is one; nothing has to
be reproved, since `key∈Codes`{.Agda} already put every such key in.

The conjunct that closed it was `isTmAt`{.Agda}'s, and it is worth saying plainly
what was wrong before. A variable's index was bounded, by the arity numeral; a
constant's payload was bounded by nothing, so the clause said only "there is
something, and the payload is its tag", and the something was an arbitrary
element of `L`. A formula recovered from a member could therefore name constants
outside the carrier, and no reading of the old predicate ruled it out. The set was
caught between two statements: every formula over the carrier had its key in it,
and every member came back as a formula over the model. Those are not the same
class. They are now, and the bound on the constants is the whole of the
difference.
<!--zh-->
两个方向如今在同一个字母表上陈述，而它们复合成一条命题之间的等式：`Codes`{.Agda} 的成员恰是载体之上某条公式的键。回来那个方向只是一次代换，因为隶属只依赖底集，而键就是一个底集；无须重证任何东西，因为 `key∈Codes`{.Agda} 早已把每个这样的键放了进去。

补上它的那个合取项是 `isTmAt`{.Agda} 的，而先前错在哪里值得明说。变元的序号有界，界自元数数码；常元的载荷则不受任何东西所界，于是那一支只说「存在某物，而载荷是它的标签」，而那个某物是 `L` 的任意元素。故从某个成员还原出来的公式可能点名载体之外的常元，而旧谓词的任何读法都排除不了这一点。那时这个集合被两条陈述夹住：载体之上的每条公式，其键都在里面；而每个成员回来时是模型之上的一条公式。二者不是同一类。如今是了，而全部差别就是那道对诸常元的界。
<!--/-->

<!--en-->
## The same set at every arity
<!--zh-->
## 同一个集合，落在每个元数上
<!--/-->

<!--en-->
The second set differs from the first in one conjunct and one index type, and its
adequacy is the same two lines with the arity carried along. What comes out is the
class of keys of formulas over the carrier **at any arity**, which is the class a
recursion over subcodes has to be indexed by, because a quantifier's subformula
lives one arity up and the arity-one class does not contain it.

The arity-one set is left exactly as it was, and that is a decision worth stating.
It could be cut out of the all-arity set by the old arity conjunct, but the
elimination would then have to turn "a key at some arity `n`, and the arity is
one" back into a formula at arity one, which means inverting the numeral and
transporting a formula along the resulting equation. That is more work than the
separation it would replace, and the two sets share everything that was expensive
already: one witness introduction, one witness elimination, one decode.
<!--zh-->
第二个集合与第一个只差一个合取项和一个索引类型，而它的适足性就是同样两行，只是把元数一路带着。出来的是载体之上诸公式**在任意元数处**的诸键之类，而那正是「对诸子码作递归」必须以之为索引的那一类，因为量词的子公式住在高一级的元数上，而一元那一类装不下它。

一元那个集合原样保留，而这个决定值得说明。它本可由旧的元数合取项从全元数集合里切出，但那样一来消去就得把「某个元数 `n` 处的键，且元数为一」变回元数一处的一条公式，也就是要把数码反过来求解，再沿所得的等式搬运一条公式。那比它所要替换的那次分离更费事，而两个集合早已共享了所有贵的东西：一次见证引入、一次见证消去、一次解码。
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

  AllCodes-spec : (x : S) → (x ∈ˢ AllCodes) ≡ IsKeyOverAny x
  AllCodes-spec x = ⇔toPath (AllCodes-out x) (AllCodes-in x)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Two sets, and one predicate apart. `Codes`{.Agda} is an element of `L` whose
members are exactly the arity-one keys of the formulas over the carrier, by
`Codes-spec`{.Agda}, which is the statement the definable powerset needs, since
`Def A`{.Agda} indexes by that class and no other. `AllCodes`{.Agda} is the same
construction with the arity bound instead of named, and `AllCodes-spec`{.Agda}
pins it to the keys at *every* arity.

The whole content is in two conjuncts, and both are of the same kind. Closedness
and shapedness together recognize the *shape* of a code and say nothing about the
arity a key carries or the alphabet its constants come from, so a decode written
against them has to be handed both, and a set built from them has to state both.
`smallDom`{.Agda} and general-formula separation do the rest, and neither needed
anything the earlier chapters had not already paid for.

The all-arity set exists for the *class* it characterizes, not for a theorem
about it. A recursion over codes has to answer at a code's subcodes, a
quantifier's subformula lives one arity up, and the arity-one class does not
contain it, so the domain has to be the keys at every arity. What the arity
conjunct changed, from a metalevel numeral to membership in `ωʟ`{.Agda}, is the
whole of the difference between a set a recursion can be indexed by and a set it
cannot.
<!--zh-->
两个集合，只差一条谓词。`Codes`{.Agda} 是 `L` 的元素，凭 `Codes-spec`{.Agda}，它的诸成员恰是载体之上诸公式在元数一处的诸键；那正是可定义幂集所需要的那条陈述，因为 `Def A`{.Agda} 以那一类、而非别的任何一类为索引。`AllCodes`{.Agda} 是同一套构造，只是元数由点名改为绑定，而 `AllCodes-spec`{.Agda} 把它钉在**每个**元数处的诸键上。

全部内容在两个合取项里，而两者同类。封闭性与成形性合起来认出的是码的**形状**，对一个键所携带的元数、以及它的诸常元出自哪个字母表，都只字未提，故一条对着它们写下的解码必须被递交这两样，而一个由它们造出的集合必须把这两样说出来。`smallDom`{.Agda} 与任意公式的分离做掉其余，而两者都没有索取前几章尚未付清的任何东西。

全元数那个集合的存在，是为了它所刻画的那**一类**，而不是为了某条关于它的定理。对码的递归必须在一个码的诸子码处作答，而量词的子公式住在高一级的元数上，一元那一类装不下它，故定义域只能是每个元数处的诸键。元数合取项所改的那件事，即从元语言的数码改为属于 `ωʟ`{.Agda}，就是「递归可以据以索引的集合」与「递归不可据以索引的集合」之间的全部差别。
<!--/-->
