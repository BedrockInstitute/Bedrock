# Domains closed under subcodes

<!--en-->
Recursion clauses determine values only after every compound code brings its
subcodes into the same domain. This chapter states that closure condition, gives
its semantic readers, and constructs the witnesses needed to satisfy it.
<!--zh-->
只有当每个复合码都把其子码带入同一定义域时，递归子句才会确定取值。本章陈述这项封闭条件，给出它的语义读式，并构造满足它所需的见证。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Closure {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )

open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ}
  using ( arityTagAtL; arityTagAtL-adequate; arityTagPairAtL; arityTagPairAtL-adequate
        ; sucAtL; sucAtL-adequate )
```

<!--en-->
## A domain that is closed under subcodes
<!--zh-->
## 对子码封闭的定义域
<!--/-->

<!--en-->
The clauses developed in `L.Coding.Expressions` constrain a table wherever both
a code and its subcodes carry
entries, and say nothing where the subcodes do not. That is the right reading,
and it is also the reason a table satisfying all ten can be almost empty: take
the index set to be one **compound** code and the table one entry there, with any
value at all. The seven clauses that consult a subcode go vacuous because the
subcodes carry no entry, and the three that do not consult one, the two atoms and
bottom, go vacuous because the index holds nothing of their shape. So
the clauses alone do not pin a value, and what pins it is a further demand on the
index set, that it contain the subcodes of everything in it. Compound matters:
put the one entry at a constant's code instead and the clause for `⊥̇` pins the
value outright, which is the shape of the whole argument in miniature.

Stating that demand needs the same two frames as the clauses, minus the table.
What is left is the shape reader and the implication: for every key in the set of
that shape, such and such keys are in the set too. A key is an arity paired with
a code, so a subkey is built from the same arity, or from its successor for the
four constructors that bind a variable, and `appAt`{.Agda} is already the reader
for "this pair is in that set".

Seven of the ten say something. The two atoms have term codes below them and
bottom has a numeral, and none of the three has a subformula, so their
clauses would be empty and are not written.
<!--zh-->
`L.Coding.Expressions` 中展开的那些子句在「码与其诸子码都带有条目」之处约束一张表，在诸子码没有条目之处则什么也不说。那样读是对的，而这也正是「满足全部十条的表可以几乎为空」的原因：取索引集为单独一个**复合**码，取表为该处的一个条目，取值随便什么。查询子码的那七条空洞，因为诸子码没有条目；不查询子码的那三条 (两个原子与底) 也空洞，因为索引里没有它们那种形状的东西。故诸子句本身钉不住任何取值，而钉住它的是对索引集的一项进一步要求：它须含有其每个成员的诸子码。「复合」这一点要紧：把那个条目改放在底的码处，`⊥̇` 的子句立刻把取值钉死，而那正是整个论证的缩影。

陈述这项要求所需的框架与诸子句相同，只是去掉了表。剩下的是形状读式与那个蕴含：对集合中每个那种形状的键，某某几个键也在该集合中。一个键是元数与码之对，故一个子键由同一个元数造出，或者对那四个绑定变元的构造子而言，由该元数的后继造出；而 `appAt`{.Agda} 早已是「这个对在那个集合中」的读式。

十条里有七条说了话。两个原子之下是词项码，底之下是数码，而这三个都没有子公式，故它们的子句会是空的，不写。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh4 : Fin n → Fin (4 + n)
    sh4 i = suc (suc (suc (suc i)))

    c4 n4 a4 b4 : Fin (4 + n)
    c4 = suc (suc (suc zero))
    n4 = suc (suc zero)
    a4 = suc zero
    b4 = zero

    sh3 : Fin n → Fin (3 + n)
    sh3 i = suc (suc (suc i))

    c3 n3 a3 : Fin (3 + n)
    c3 = suc (suc zero)
    n3 = suc zero
    a3 = zero

  binShapeAt : Fin n → ℕ → Formula S (4 + n) → Formula S n
  binShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ ( arityTagPairAtL c4 n4 k a4 b4 ⇒̇ rel))))

  unShapeAt : Fin n → ℕ → Formula S (3 + n) → Formula S n
  unShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ ( arityTagAtL c3 n3 k a3 ⇒̇ rel)))

  binShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  binShape-out C k rel γ h c ar a b c∈ shape =
    h c c∈ ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
        shape)

  unShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  unShape-out C k rel γ h c ar a c∈ shape =
    h c c∈ ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ))) shape)
```

<!--en-->
Four generic relations cover the payload shapes. The seven active closure clauses
use three of them: the three binary connectives want both components at the arity
they were read at; the two unbounded quantifiers want their one
component one arity up, which is an existential over the successor, and the two
bounded ones want their *second* component there, the first being a term.
<!--zh-->
四条通用关系覆盖载荷形状。七条实际封闭性子句使用其中三条：三个二元联结词要它们的两个分量都在被读出的那个元数处；两个无界量词要它们的那一个分量高一个元数，那是一个关于后继的存在；而两个有界量词要它们的**第二个**分量在那里，第一个是词项。
<!--/-->

```agda
  bothSameAt : Fin n → Formula S (4 + n)
  bothSameAt C = appAt (sh4 C) n4 a4 ∧̇ appAt (sh4 C) n4 b4

  oneSameAt : Fin n → Formula S (3 + n)
  oneSameAt C = appAt (sh3 C) n3 a3

  oneSuccAt : Fin n → Formula S (3 + n)
  oneSuccAt C = ∃̇ (sucAtL (suc n3) zero ∧̇ appAt (suc (sh3 C)) zero (suc a3))

  succSndAt : Fin n → Formula S (4 + n)
  succSndAt C = ∃̇ (sucAtL (suc n4) zero ∧̇ appAt (suc (sh4 C)) zero (suc b4))
```

<!--en-->
Reading them back is what a consumer does, so each is stated at the clause,
already composed with its frame: given a key of that shape in the set, the keys
the constructor demands are in the set. The two that change arity discharge a
truncation on the way, which the target admits because membership is a
proposition.
<!--zh-->
把它们读回来是消费方要做的事，故每一条都在子句处陈述，且已与其框架复合：给定集合中一个那种形状的键，该构造子所要的诸键也在集合中。改变元数的那两条在途中消掉一个截断，而目标允许这件事，因为隶属是命题。
<!--/-->

```agda
  binSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
    × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩
  binSameClosed-out C k γ h c ar a b c∈ shape =
      subst ⟨_⟩ (appAt-adequate (sh4 C) n4 a4 δ) (r .fst)
    , subst ⟨_⟩ (appAt-adequate (sh4 C) n4 b4 δ) (r .snd)
    where
    δ : S ^ (4 + n)
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    r = binShape-out C k (bothSameAt C) γ h c ar a b c∈ shape

  unSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
  unSameClosed-out C k γ h c ar a c∈ shape =
    subst ⟨_⟩ (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ))
      (unShape-out C k (oneSameAt C) γ h c ar a c∈ shape)

  unSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩
  unSuccClosed-out C k γ h c ar a c∈ shape =
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
          (subst ⟨_⟩ (sucAtL-adequate (suc n3) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh3 C)) zero (suc a3) (z ∷ δ)) ap) })
      (unShape-out C k (oneSuccAt C) γ h c ar a c∈ shape)
    where
    δ : S ^ (3 + n)
    δ = a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ)

  binSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩
  binSuccClosed-out C k γ h c ar a b c∈ shape =
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
          (subst ⟨_⟩ (sucAtL-adequate (suc n4) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh4 C)) zero (suc b4) (z ∷ δ)) ap) })
      (binShape-out C k (succSndAt C) γ h c ar a b c∈ shape)
    where
    δ : S ^ (4 + n)
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ)
```

<!--en-->
The seven clauses, and their conjunction. A consumer takes the conjunct it wants
and hands it to the reader that goes with it; nothing else is needed, which is
why the seven are written without a module around them.
<!--zh-->
七条子句，及其合取。消费方取它要的那个合取项，交给与之配套的读式；此外不需要别的，这也是为何那七条没有套一层模块。
<!--/-->

```agda
  andClosedAt orClosedAt impClosedAt : Fin n → Formula S n
  existClosedAt forallClosedAt allInClosedAt exInClosedAt : Fin n → Formula S n

  andClosedAt    C = binShapeAt C 2 (bothSameAt C)
  orClosedAt     C = binShapeAt C 3 (bothSameAt C)
  impClosedAt    C = binShapeAt C 4 (bothSameAt C)
  existClosedAt  C = unShapeAt  C 6 (oneSuccAt C)
  forallClosedAt C = unShapeAt  C 7 (oneSuccAt C)
  allInClosedAt  C = binShapeAt C 8 (succSndAt C)
  exInClosedAt   C = binShapeAt C 9 (succSndAt C)

  closedAt : Fin n → Formula S n
  closedAt C =
    andClosedAt C ∧̇ (orClosedAt C ∧̇ (impClosedAt C ∧̇ (existClosedAt C
      ∧̇ (forallClosedAt C ∧̇ (allInClosedAt C ∧̇ exInClosedAt C)))))
```

<!--en-->
The other direction, which the first instance needs and no clause needed. A
consumer of a recursion reads its hypotheses; the meta-level set that will be
handed to one has to *satisfy* them, so every frame and every relation is owed an
introduction as well as an elimination. Both frames introduce by a lambda, since
a bounded universal over the model is a function on members and the implication
is a function on the reader's proof. The two arity-raising relations build the
successor as an element of the model, which the numeral chapter supplies.
<!--zh-->
另一个方向，是第一个实例需要而任何子句都不需要的。递归的消费方读它的假设；而将要交给它的那个元语言层面的集合必须**满足**那些假设，故每个框架、每条关系都欠一条引入，正如它们欠一条消去。两个框架都以一个 λ 引入，因为模型上的有界全称就是成员上的函数，而那个蕴含是读式证明上的函数。两条抬升元数的关系要把后继造成模型的元素，而数码那一章供给它。
<!--/-->

```agda
  binShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
  binShape-in C k rel γ g c c∈ ar a b sh =
    g c ar a b c∈
      (subst ⟨_⟩ (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)) sh)

  unShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
  unShape-in C k rel γ g c c∈ ar a sh =
    g c ar a c∈
      (subst ⟨_⟩ (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ)) sh)

  binSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
       × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
  binSameClosed-in C k γ g = binShape-in C k (bothSameAt C) γ
    (λ c ar a b c∈ sh →
        subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 a4 (b ∷ a ∷ ar ∷ c ∷ γ)))
          (g c ar a b c∈ sh .fst)
      , subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
          (g c ar a b c∈ sh .snd))

  unSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
  unSameClosed-in C k γ g = unShape-in C k (oneSameAt C) γ
    (λ c ar a c∈ sh →
      subst ⟨_⟩ (sym (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ)))
        (g c ar a c∈ sh))

  unSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
  unSuccClosed-in C k γ g = unShape-in C k (oneSuccAt C) γ
    (λ c ar a c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n3) zero
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh3 C)) zero (suc a3)
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a c∈ sh)) ) ∣₁)

  binSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
  binSuccClosed-in C k γ g = binShape-in C k (succSndAt C) γ
    (λ c ar a b c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n4) zero
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh4 C)) zero (suc b4)
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a b c∈ sh)) ) ∣₁)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`closedAt` requires every compound code in the domain to bring along the
subformula codes its clause reads. Its elimination lemmas expose those subcodes,
and its introduction lemmas build the same seven obligations from meta-level
membership facts.
<!--zh-->
`closedAt` 要求定义域中的每个复合码都带上其子句将读取的子公式码。消去引理取出这些子码，引入引理则从元语言的隶属事实构造同样的七项义务。
<!--/-->
