# The codes, as one set

<!--en-->
Every chapter so far has been careful to say that the set of *all* codes is not
an element of `L`, and that nothing needed it. Something needs it now. The
definable powerset takes syntax as its index type, `Def A = sett (Formula ⟪A⟫ 1)
defSet`, so internalizing definability at a stage means naming the arity-one
formulas over that stage from inside the model, and a formula can only name a
set.

The set is not built by collecting the codes. It is cut out of a superset:
`smallDom`{.Agda} contains any small family of elements of `L` in a single stage,
the arity-one keys are such a family, and separation inside `L` holds for
formulas of any complexity. So the whole chapter is one object-language
predicate, and the two directions of its adequacy.

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
whose first component is the numeral one.

The carrier is bound and then pinned, rather than named as a constant where it is
used. Shapedness takes its carrier as a slot, so something has to occupy that
slot, and an existential guarded by `var zero ≐ con A`{.Agda} occupies it with a
variable that is provably `A`. One equation buys what a constant would have cost
a re-indexing of every predicate below.

Which half is hard, then, is settled. Introduction is three lemmas already
proved, applied to the subformula closure. Elimination is where the arity
conjunct is spent, and without it there is no elimination at all.
<!--zh-->
至此每一章都小心地说过：**全体**码之集不是 `L` 的元素，而且没有东西需要它。现在有东西需要了。可定义幂集以语法为索引类型，`Def A = sett (Formula ⟪A⟫ 1) defSet`，故在一个阶段处内化可定义性，就意味着从模型内部点名该阶段之上的一元公式，而公式只能点名集合。

这个集合不是靠把诸码收集起来造出的。它是从一个超集中切出来的：`smallDom`{.Agda} 把 `L` 元素的任意小族装进单一阶段，而诸一元键正是这样一个族，且 `L` 内部的分离对任意复杂度的公式成立。故整章就是一条对象语言的谓词，加上它适足性的两个方向。

那条谓词有两个合取项，而二者分量不等。第二项「仅仅存在一个等于 `A` 的载体、以及一个集合 `C`，`x` 是它的成员，`C` 封闭且 `C` 在该载体上成形」是若干无界存在，在此处不费分文：满足关系是在类模型处读的，存在量词在 `L` 上取值，无须任何阶段去反射任何东西。

第一个合取项才是承重的那个，而它就是本章的发现。`recover`{.Agda} 收下的不是「封闭且成形之集的一个成员」；它收下的是**以某个已言明元数处的键的形式**递交过来的成员，而 `closedAt`{.Agda} 与 `shapedAt`{.Agda} 都没有约束元数那一位。形状把元数存在量化，且对它不加任何条件，故一个持有「第一分量压根不是数码的对」的集合同样满足两半，而解码对那个对无话可说。这笔债在欠下之处已被记下，而此处正是偿付之处：那条谓词从外面说出，`x` 是一个第一分量为数码一的对。

载体是先被绑定、再被钉住的，而不是在用到它的地方点名为常元。成形性把它的载体取作一位，故必须有什么东西占住那一位，而一个由 `var zero ≐ con A`{.Agda} 把守的存在量词，用一个可证等于 `A` 的变元占住它。一条等式买下的，是常元本会以「把下面每条谓词重新索引一遍」为代价的东西。

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
open import L.Coding.Model {ℓ} using ( tagAtL; tagAtL-adequate; closedAt )
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
<!--zh-->
两个合取项，落在一个自由变元上。第一项从外面钉住元数，而这正是上一章点名索取的那个合取项。第二项是解码那两条假设的见证：一个装着实参、既封闭又成形的集合。

第二项里没有任何东西是有界的，也不需要有。那个见证在引入这边由一条公式自己的子公式闭包产出，在消去那边作为 `L` 的一个集合被消费，而两种读法都发生在类模型处。
<!--/-->

```agda
isCode : S → Formula S 1
isCode A = keyArityAtL zero 1
        ∧̇ ∃̇ ((var zero ≐ con A)
             ∧̇ ∃̇ ((var (suc (suc zero)) ∈̇ var zero)
                  ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))))
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
and returns a stage containing all of it; the family is the arity-one keys,
indexed by the arity-one formulas over the alphabet, which is a type of the right
size because syntax is an inductive type at the alphabet's own level. What comes
back contains every key and much else, and separation removes the else.

The set is sealed where it is built. Unsealed, every later type mentioning it
would carry the separation instrument's unfolding into conversion, and the facts
exported here are all any consumer needs. Only the two that read the separation
are inside the seal; the direction back and the equation it composes into are
outside it, since neither needs to know what the set was cut out of.
<!--zh-->
载体是固定的，而消费方会把它固定在某个阶段上。它的诸成员就是字母表，恰如诸编码章的两个参数所期待：到层级的嵌入，以及「它落到的东西可构造」这份证书。后者是 `L` 的传递性用一次，而它所施于的那条隶属关系被单独命名，因为形状谓词如今按其自身的名义索取它。

然后是那个超集。`smallDom`{.Agda} 索取 `L` 元素的一个小族，返回一个装下它全部的阶段；这个族就是诸一元键，以字母表之上的一元公式为索引，而那是一个尺寸正确的类型，因为语法是在字母表自身层级上的归纳类型。回来的东西含有每个键，也含有别的许多；而分离把「别的」去掉。

这个集合在它被造出之处封印。不封印的话，此后每个提到它的类型都会把分离器械的展开带进转换检查，而此处导出的诸事实已是任何消费方所需的全部。封印之内只有读分离的那两条；回来那个方向、以及它们复合成的那条等式在封印之外，因为两者都不需要知道这个集合是从什么里切出来的。
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

    codeS : Formula ⟪ fst A ⟫ 1 → S
    codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ

  keyS : Formula ⟪ fst A ⟫ 1 → S
  keyS φ = key ι ιL φ , keyL ι ιL φ

  private
    small : Σ[ d ∈ S ] ((φ : Formula ⟪ fst A ⟫ 1) → ⟨ keyS φ ∈ˢ d ⟩)
    small = smallDom (Formula ⟪ fst A ⟫ 1) keyS

    sep : isContr (SetOf (λ x → (x ∈ˢ small .fst) ⊓ ((x ∷ []) ⊨ isCode A)))
    sep = hasSeparationL (small .fst) (isCode A)
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

Introduction is the half with nothing in it. A formula's key is in the superset
by the family it indexes; the arity conjunct is the key's own shape, so its
witness is the code and its equation is `refl`{.Agda}; the carrier existential
takes `A` itself and its equation is `refl`{.Agda} again; and the inner
existential's witness is the subformula closure, whose three obligations are
`key∈closure`{.Agda}, `closureClosed`{.Agda} and `closureShaped`{.Agda}, one
chapter each and all already discharged. The last of them now asks for one thing
more, that every constant is a member of the carrier, and at this alphabet that
is the fact the alphabet was defined by.

Elimination is the other half. Read the arity conjunct and the member arrives in
key form at arity one, which is what `recover`{.Agda} demands and what nothing
else in the predicate would supply. Read the carrier existential and its equation
turns a membership in the bound carrier into a membership in `A`, which is what
makes the decode's hypothesis dischargeable: `A`'s members are exactly the image
of `⟪ A ⟫`, by the presentation of a set by its own members. Read the inner
existential and a closed, shaped set arrives with it. Then the decode runs, and
its answer is a formula over the carrier.
<!--zh-->
两个方向所谈的那条陈述先写出来，而它是一个类：载体之上诸公式在元数一处的诸键。引入说每个这样的键都是成员，消去说每个成员都是这样一个键，故二者不再是这个集合的两道界，而是它的一条刻画。

引入是里面什么也没有的那一半。一条公式的键属于那个超集，凭它所索引的那个族；元数合取项就是那个键自身的形状，故它的见证是那条码、它的等式是 `refl`{.Agda}；载体那个存在量词取 `A` 自身，它的等式又是 `refl`{.Agda}；而内层存在量词的见证是子公式闭包，其三笔债 `key∈closure`{.Agda}、`closureClosed`{.Agda} 与 `closureShaped`{.Agda} 各出一章，且都已偿清。其中最后一条如今多要一件东西，即每个常元都是载体的成员，而在这个字母表上，那正是字母表当初据以定义的那件事。

消去是另一半。读出元数合取项，那个成员就以「元数一处的键」的形式到场，而这正是 `recover`{.Agda} 所索取的、也是谓词里别的东西都供不出的。读出载体那个存在量词，它的等式把「属于被绑定的那个载体」变成「属于 `A`」，而这正是解码那条假设得以交付的原因：`A` 的诸成员恰是 `⟪ A ⟫` 的像，凭的是「一个集合由其自身诸成员的呈现」。读出内层存在量词，一个既封闭又成形的集合便随之到场。随后解码开跑，而它的答案是载体之上的一条公式。
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
        , ∣ A , ( refl
          , ∣ clo ι ιL φ
            , ( key∈closure ι ιL φ
              , ( closureClosed ι ιL φ (A ∷ keyS φ ∷ [])
                , closureShaped ι ιL φ zero (A ∷ keyS φ ∷ []) ι∈ ) ) ∣₁ ) ∣₁ ) )

    Codes-out : (x : S) → ⟨ x ∈ˢ Codes ⟩ → ⟨ IsKeyOver x ⟩
    Codes-out x x∈ = PT.rec squash₁ viaArity
      (keyArityAtL-out zero 1 (x ∷ []) (sat .fst))
      where
      sat : ⟨ (x ∷ []) ⊨ isCode A ⟩
      sat = subst ⟨_⟩ (sep .fst .snd x) x∈ .snd

      viaArity : Σ[ z ∈ S ] (fst x ≡ pr (# 1) (fst z)) → ⟨ IsKeyOver x ⟩
      viaArity (z , qz) = PT.rec squash₁ viaCarrier (sat .snd)
        where
        viaCarrier : Σ[ B ∈ S ] ⟨ (B ∷ x ∷ [])
                       ⊨ ((var zero ≐ con A)
                          ∧̇ ∃̇ ((var (suc (suc zero)) ∈̇ var zero)
                               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero)))) ⟩
                   → ⟨ IsKeyOver x ⟩
        viaCarrier (B , (qB , hB)) = PT.rec squash₁ viaSlot hB
          where
          onto : (y : V ℓ) → ⟨ y ∈ fst B ⟩
               → ∥ Σ[ c ∈ ⟪ fst A ⟫ ] (ι c ≡ y) ∥₁
          onto y y∈ = ∣ ∈-asFiber {a = y} {b = fst A}
            (subst (λ w → ⟨ y ∈ w ⟩) qB y∈) ∣₁

          viaSlot : Σ[ C ∈ S ] ⟨ (C ∷ B ∷ x ∷ [])
                      ⊨ ((var (suc (suc zero)) ∈̇ var zero)
                         ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
                  → ⟨ IsKeyOver x ⟩
          viaSlot (C , (x∈C , (hcl , hsh))) = PT.map
            (λ { (ψ , qψ) → ψ , (qz ∙ cong (pr (# 1)) (sym qψ)) })
            (Decode.recover ι zero (suc zero) (C ∷ B ∷ x ∷ []) onto hcl hsh 1 z
              (subst (λ w → ⟨ w ∈ fst C ⟩) (qz ∙ sym (keyOf-fst 1 z)) x∈C))

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
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`Codes`{.Agda} is an element of `L`, cut out of a stage by one object-language
predicate, and `Codes-spec`{.Agda} pins it: its members are exactly the arity-one
keys of the formulas over the carrier. That is the statement the definable
powerset needs, since `Def A`{.Agda} indexes by that class and no other.

The whole content is in two conjuncts, and both are of the same kind. Closedness
and shapedness together recognize the *shape* of a code and say nothing about the
arity a key carries or the alphabet its constants come from, so a decode written
against them has to be handed both, and a set built from them has to state both.
`smallDom`{.Agda} and general-formula separation do the rest, and neither needed
anything the earlier chapters had not already paid for.

What the chapter still does not say is anything about arities other than one. The
predicate names the numeral one twice over, in the arity conjunct and in the
family the superset is taken of, and a recursion whose domain must be closed under
subcodes descends through the binders into every arity. That set is a different
object and is owed elsewhere.
<!--zh-->
`Codes`{.Agda} 是 `L` 的元素，由一条对象语言的谓词从一个阶段中切出，而 `Codes-spec`{.Agda} 把它钉死：它的诸成员恰是载体之上诸公式在元数一处的诸键。那正是可定义幂集所需要的那条陈述，因为 `Def A`{.Agda} 以那一类、而非别的任何一类为索引。

全部内容在两个合取项里，而两者同类。封闭性与成形性合起来认出的是码的**形状**，对一个键所携带的元数、以及它的诸常元出自哪个字母表，都只字未提，故一条对着它们写下的解码必须被递交这两样，而一个由它们造出的集合必须把这两样说出来。`smallDom`{.Agda} 与任意公式的分离做掉其余，而两者都没有索取前几章尚未付清的任何东西。

本章仍未说的，是关于元数一以外的任何事。那条谓词两处点了数码一的名，一处在元数合取项、一处在超集所取的那个族；而一个定义域必须对子码封闭的递归，会经诸绑定子下降到每个元数上。那个集合是另一个对象，欠在别处。
<!--/-->
