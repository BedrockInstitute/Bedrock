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
"there merely is a set `C` with `x` a member of it, `C` closed and `C` shaped", is
one unbounded existential and costs nothing here: satisfaction is read at the
class model, where an existential ranges over `L` and no stage has to reflect
anything.

The first conjunct is the load-bearing one, and it is the finding. `recover`{.Agda}
does not take a member of a closed and shaped set; it takes a member handed over
**as a key at a stated arity**, and nothing in `closedAt`{.Agda} or
`shapedAt`{.Agda} constrains the arity slot. Shapedness binds the arity
existentially and puts no condition on it, so a set holding a pair whose first
component is not a numeral at all satisfies both halves, and the decode has
nothing to say about that pair. That debt was recorded where it was incurred, and
this is where it is paid: the predicate says, from outside, that `x` is a pair
whose first component is the numeral one.

Which half is hard, then, is settled. Introduction is three lemmas already
proved, applied to the subformula closure. Elimination is where the arity
conjunct is spent, and without it there is no elimination at all.
<!--zh-->
至此每一章都小心地说过：**全体**码之集不是 `L` 的元素，而且没有东西需要它。现在有东西需要了。可定义幂集以语法为索引类型，`Def A = sett (Formula ⟪A⟫ 1) defSet`，故在一个阶段处内化可定义性，就意味着从模型内部点名该阶段之上的一元公式，而公式只能点名集合。

这个集合不是靠把诸码收集起来造出的。它是从一个超集中切出来的：`smallDom`{.Agda} 把 `L` 元素的任意小族装进单一阶段，而诸一元键正是这样一个族，且 `L` 内部的分离对任意复杂度的公式成立。故整章就是一条对象语言的谓词，加上它适足性的两个方向。

那条谓词有两个合取项，而二者分量不等。第二项「仅仅存在一个集合 `C`，`x` 是它的成员，`C` 封闭且 `C` 成形」是一个无界存在，在此处不费分文：满足关系是在类模型处读的，存在量词在 `L` 上取值，无须任何阶段去反射任何东西。

第一个合取项才是承重的那个，而它就是本章的发现。`recover`{.Agda} 收下的不是「封闭且成形之集的一个成员」；它收下的是**以某个已言明元数处的键的形式**递交过来的成员，而 `closedAt`{.Agda} 与 `shapedAt`{.Agda} 都没有约束元数那一位。形状把元数存在量化，且对它不加任何条件，故一个持有「第一分量压根不是数码的对」的集合同样满足两半，而解码对那个对无话可说。这笔债在欠下之处已被记下，而此处正是偿付之处：那条谓词从外面说出，`x` 是一个第一分量为数码一的对。

于是哪一半难，已然定案。引入是三条早已证好的引理，施于子公式闭包。消去才是花掉元数合取项的地方，而没有它，就根本没有消去。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.CodeSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( tagAtL; tagAtL-adequate; closedAt; module LCode )
open import L.Coding.InL {ℓ} using ( key; keyL; codeL; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ} using ( shapedAt; closureShaped )
open import L.Coding.Recover {ℓ} using ( keyOf; keyOf-fst; module Decode )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
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
isCode : Formula S 1
isCode = keyArityAtL zero 1
      ∧̇ ∃̇ ((var (suc zero) ∈̇ var zero) ∧̇ (closedAt zero ∧̇ shapedAt zero))
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
constructible. The second is transitivity of `L` applied once.

Then the superset. `smallDom`{.Agda} asks for a small family of elements of `L`
and returns a stage containing all of it; the family is the arity-one keys,
indexed by the arity-one formulas over the alphabet, which is a type of the right
size because syntax is an inductive type at the alphabet's own level. What comes
back contains every key and much else, and separation removes the else.

The set is sealed where it is built. Unsealed, every later type mentioning it
would carry the separation instrument's unfolding into conversion, and the three
facts exported here are all any consumer needs.
<!--zh-->
载体是固定的，而消费方会把它固定在某个阶段上。它的诸成员就是字母表，恰如诸编码章的两个参数所期待：到层级的嵌入，以及「它落到的东西可构造」这份证书。后者是 `L` 的传递性用一次。

然后是那个超集。`smallDom`{.Agda} 索取 `L` 元素的一个小族，返回一个装下它全部的阶段；这个族就是诸一元键，以字母表之上的一元公式为索引，而那是一个尺寸正确的类型，因为语法是在字母表自身层级上的归纳类型。回来的东西含有每个键，也含有别的许多；而分离把「别的」去掉。

这个集合在它被造出之处封印。不封印的话，此后每个提到它的类型都会把分离器械的展开带进转换检查，而此处导出的三个事实已是任何消费方所需的全部。
<!--/-->

```agda
module _ (A : S) where
  private
    ι : ⟪ fst A ⟫ → V ℓ
    ι = ⟪ fst A ⟫↪

    ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
    ιL m = isL-trans {x = fst A} {y = ι m}
      (∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)) (A .snd)

    codeS : Formula ⟪ fst A ⟫ 1 → S
    codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ

  keyS : Formula ⟪ fst A ⟫ 1 → S
  keyS φ = key ι ιL φ , keyL ι ιL φ

  private
    small : Σ[ d ∈ S ] ((φ : Formula ⟪ fst A ⟫ 1) → ⟨ keyS φ ∈ˢ d ⟩)
    small = smallDom (Formula ⟪ fst A ⟫ 1) keyS

    sep : isContr (SetOf (λ x → (x ∈ˢ small .fst) ⊓ ((x ∷ []) ⊨ isCode)))
    sep = hasSeparationL (small .fst) isCode
```

<!--en-->
## Both directions
<!--zh-->
## 两个方向
<!--/-->

<!--en-->
Introduction first, because it is the half with nothing in it. A formula's key is
in the superset by the family it indexes; the arity conjunct is the key's own
shape, so its witness is the code and its equation is `refl`{.Agda}; and the
existential's witness is the subformula closure, whose three obligations are
`key∈closure`{.Agda}, `closureClosed`{.Agda} and `closureShaped`{.Agda}, one
chapter each and all already discharged.

Elimination is the other half. Read the arity conjunct and the member arrives in
key form at arity one, which is what `recover`{.Agda} demands and what nothing
else in the predicate would supply. Read the existential and a closed, shaped set
arrives with it. Then the decode runs, and its answer is transported back along
the arity equation the first conjunct produced.
<!--zh-->
先引入，因为它是里面什么也没有的那一半。一条公式的键属于那个超集，凭它所索引的那个族；元数合取项就是那个键自身的形状，故它的见证是那条码、它的等式是 `refl`{.Agda}；而那个存在量词的见证是子公式闭包，其三笔债 `key∈closure`{.Agda}、`closureClosed`{.Agda} 与 `closureShaped`{.Agda} 各出一章，且都已偿清。

消去是另一半。读出元数合取项，那个成员就以「元数一处的键」的形式到场，而这正是 `recover`{.Agda} 所索取的、也是谓词里别的东西都供不出的。读出那个存在量词，一个既封闭又成形的集合便随之到场。随后解码开跑，而它的答案沿第一个合取项产出的那条元数等式搬回来。
<!--/-->

```agda
  opaque
    Codes : S
    Codes = sep .fst .fst

    key∈Codes : (φ : Formula ⟪ fst A ⟫ 1) → ⟨ keyS φ ∈ˢ Codes ⟩
    key∈Codes φ = subst ⟨_⟩ (sym (sep .fst .snd (keyS φ)))
      ( small .snd φ
      , ( keyArityAtL-in zero 1 (keyS φ ∷ []) (codeS φ) refl
        , ∣ clo ι ιL φ
          , ( key∈closure ι ιL φ
            , ( closureClosed ι ιL φ (keyS φ ∷ [])
              , closureShaped ι ιL φ (keyS φ ∷ []) ) ) ∣₁ ) )

    Codes-out : (x : S) → ⟨ x ∈ˢ Codes ⟩
              → ∥ (Σ[ ψ ∈ Formula S 1 ]
                    (fst x ≡ fst (keyOf 1 LCode.⌜ ψ ⌝))) ∥₁
    Codes-out x x∈ = PT.rec squash₁ viaArity
      (keyArityAtL-out zero 1 (x ∷ []) (sat .fst))
      where
      sat : ⟨ (x ∷ []) ⊨ isCode ⟩
      sat = subst ⟨_⟩ (sep .fst .snd x) x∈ .snd

      viaArity : Σ[ z ∈ S ] (fst x ≡ pr (# 1) (fst z))
               → ∥ (Σ[ ψ ∈ Formula S 1 ]
                     (fst x ≡ fst (keyOf 1 LCode.⌜ ψ ⌝))) ∥₁
      viaArity (z , qz) = PT.rec squash₁ viaSlot (sat .snd)
        where
        viaSlot : Σ[ C ∈ S ] ⟨ (C ∷ x ∷ [])
                    ⊨ ((var (suc zero) ∈̇ var zero)
                       ∧̇ (closedAt zero ∧̇ shapedAt zero)) ⟩
                → ∥ (Σ[ ψ ∈ Formula S 1 ]
                      (fst x ≡ fst (keyOf 1 LCode.⌜ ψ ⌝))) ∥₁
        viaSlot (C , (x∈C , (hcl , hsh))) = PT.map
          (λ { (ψ , qψ) → ψ
             , ( qz ∙ cong (pr (# 1)) (sym qψ)
               ∙ sym (keyOf-fst 1 LCode.⌜ ψ ⌝) ) })
          (Decode.recover zero (C ∷ x ∷ []) hcl hsh 1 z
            (subst (λ w → ⟨ w ∈ fst C ⟩) (qz ∙ sym (keyOf-fst 1 z)) x∈C))
```

<!--en-->
## What lands where, and the gap
<!--zh-->
## 什么落在哪里，以及那个缺口
<!--/-->

<!--en-->
The two directions are not stated over the same alphabet, and the asymmetry is
real rather than cosmetic. Introduction starts from a `Formula ⟪A⟫ 1`, a formula
whose constants are members of the carrier. **Elimination lands only at
`Formula S 1`**, a formula over the whole model.

The reason is `isTmAt`{.Agda}, and specifically its constant clause. A variable's
index is bounded, by the arity numeral, which is the entire point of that
clause's second disjunct; a constant's payload is bounded by nothing. The clause
says only "there is something, and the payload is its tag", and the something it
produces is an arbitrary element of `L`. So a formula recovered from a member of
this set may name constants that are not members of the carrier, and no reading
of the present predicate rules that out.

This is a real gap and the next goal must close it, not a detail to be waved
past. Closing it means one more conjunct, of the same kind as the arity one and
for the same reason: a bound on the constants, written into the predicate from
outside, since nothing the decode consumes will supply it. Until then, `Codes`{.Agda}
is the set of arity-one keys of formulas over the model that happen to sit in a
closed, shaped set, and the introduction says every formula over the carrier has
its key there.
<!--zh-->
两个方向不是在同一个字母表上陈述的，而这种不对称是实打实的，不是门面上的。引入从一条 `Formula ⟪A⟫ 1` 出发，即常元取自载体成员的公式。**消去只落在 `Formula S 1`**，即整个模型之上的公式。

理由是 `isTmAt`{.Agda}，确切说是它的常元那一支。变元的序号有界，界自元数数码，而那正是那一支第二个析取项的全部意义所在；常元的载荷则不受任何东西所界。那一支只说「存在某物，而载荷是它的标签」，而它所产出的那个某物是 `L` 的任意元素。故从本集某个成员还原出来的公式，可能点名并非载体成员的常元，而当前这条谓词的任何读法都排除不了这一点。

这是一个实打实的缺口，下一个目标必须把它补上，而不是一处可以挥手带过的细节。补上它意味着再加一个合取项，与元数那个同类、理由也相同：一条对诸常元的界，从外面写进谓词里，因为解码所消费的东西没有一样会供给它。在那之前，`Codes`{.Agda} 是「恰好坐落在某个封闭且成形的集合里的、模型之上诸公式的一元键」之集，而引入说的是：载体之上的每条公式，其键都在那里。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`Codes`{.Agda} is an element of `L`, cut out of a stage by one object-language
predicate, and it is caught between two statements rather than pinned by one.
`key∈Codes`{.Agda} puts the key of every formula over the carrier into it;
`Codes-out`{.Agda} takes every member back to a formula over the *model*. Those
are not the same class, and until the gap below is closed they are what the set
is, in place of a characterization.

The whole content is the first conjunct. Closedness and shapedness together
recognize the *shape* of a code and say nothing about the arity a key carries, so
a decode written against them has to be handed the arity, and a set built from
them has to state it. `smallDom`{.Agda} and general-formula separation do the
rest, and neither needed anything the earlier chapters had not already paid for.

The elimination lands at `Formula S 1` and not at `Formula ⟪A⟫ 1`. That is the
one thing this chapter leaves open, and it is left open in the same place the
arity was: in the predicate, which is where a bound on the constants would have
to be written.
<!--zh-->
`Codes`{.Agda} 是 `L` 的元素，由一条对象语言的谓词从一个阶段中切出，而它是被两条陈述**夹住**的、不是被一条钉死的。`key∈Codes`{.Agda} 把载体之上每条公式的键放进去；`Codes-out`{.Agda} 把每个成员带回一条**模型之上**的公式。二者不是同一类，而在下面那处敞口被关掉之前，它们就是这个集合之所是，代替了一条刻画。

全部内容就是第一个合取项。封闭性与成形性合起来认出的是码的**形状**，对一个键所携带的元数只字未提，故一条对着它们写下的解码必须被递交元数，而一个由它们造出的集合必须把元数说出来。`smallDom`{.Agda} 与任意公式的分离做掉其余，而两者都没有索取前几章尚未付清的任何东西。

消去落在 `Formula S 1`，而非 `Formula ⟪A⟫ 1`。那是本章留下的唯一一处敞口，而它敞在与元数当初相同的位置：在那条谓词里，那也正是「对诸常元的界」将不得不写下之处。
<!--/-->
