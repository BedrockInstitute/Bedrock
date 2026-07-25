# The numeral chain

<!--en-->
Infinity is stated in this book in its strong form: the numerals form a set. That
statement has two halves, and they are of very different difficulty. First the
chain itself has to exist inside `L`, with zero at the bottom and each numeral
the successor of the last; then that chain has to be *collected*, which is the
axiom proper. This chapter does the first half, and it does it for free, because
the previous chapter already built everything a successor is made of.

The point worth watching is a mismatch. Inside the model, the successor of `a`
is `a ∪ {a}`, spelled with the model's own pairing and union, and those are
`℩`-projections out of unique-existence proofs rather than the library's set
operations. Outside, the ambient hierarchy has its own successor, and its own
chain of numerals built from it. The two chains ought to agree, but nothing so
far says they do: one is assembled from contractibility centres, the other from
constructors. So this chapter's real content is a family of **projection
equations**, saying that the model's operations, read through the underlying
set, are the hierarchy's operations. With those in hand the two chains coincide
step by step, and the two pinning equations that the model record demands of a
numeral chain follow by transporting the hierarchy's own facts along them.
<!--zh-->
本书的无穷公理取强形式：数码构成一个集合。这个陈述有两半，难度截然不同。首先，链本身必须存在于 `L` 之内，零在底，每个数码是前一个的后继；然后这条链必须被**收集**起来，那才是公理本身。本章做第一半，而且是白拿，因为上一章已经把后继所需的一切都造好了。

值得盯住的是一处错位。在模型内部，`a` 的后继是 `a ∪ {a}`，用模型自己的配对与并写出，而那两者是从唯一存在性证明中取出的 `℩` 投影，不是库的集合运算。在外部，环境层级有它自己的后继，以及由此造出的自己的数码链。两条链理应一致，可迄今没有任何东西说它们一致：一条由可缩中心装配，另一条由构造子装配。所以本章真正的内容是一族**投影等式**，说的是模型的运算沿底层集合读出来就是层级的运算。有了它们，两条链逐步重合，而模型 record 向数码链索取的两条钉死方程，也就沿着它们搬运层级自己的事实而得。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Infinity {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Model {ℓ}
  using ( pair-singleton; ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ}
  using ( hasPairL; hasUnionL; module PairOf; module UnionOf; isL-directed
        ; ∅ʟ; uniqueL )

open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; ℩ )
```

<!--en-->
## The model's own operations
<!--zh-->
## 模型自己的运算
<!--/-->

<!--en-->
Unique existence hands over an operation: the description operator takes the
contractibility proof to its centre. Pairing and union become functions on the
constructible sets, and the successor is written the way the model record writes
it, as the union of a pair of pairs.
<!--zh-->
唯一存在交出一个运算：摹状词算子把可缩性证明送到它的中心。配对与并成为可构造集上的函数，而后继就按模型 record 的写法写出，即一对之对的并。
<!--/-->

```agda
pairʟ : S → S → S
pairʟ a b = ℩ (hasPairL a b)

unionʟ : S → S
unionʟ a = ℩ (hasUnionL a)

sucʟ : S → S
sucʟ a = unionʟ (pairʟ a (pairʟ a a))
```

<!--en-->
## Projection equations
<!--zh-->
## 投影等式
<!--/-->

<!--en-->
Now the mismatch. The centre of a contractibility proof is not, on the face of
it, the set the hierarchy would have built: the proof went through a merely
existing witness, so nothing computes. But contractibility says more than
existence, it says every witness *is* the centre; and the previous chapter's
construction, applied to any stage that works, is a witness. So the two agree.
The truncation is harmless because the goal is an equation between sets, and the
hierarchy's carrier is a set.
<!--zh-->
现在处理那处错位。可缩性证明的中心，表面上并不是层级会造出的那个集合：证明经过了一个仅仅存在的见证，故什么也算不出来。但可缩性说的比存在更多，它说**每个**见证都等于中心；而上一章的构造，施于任何合用的阶段，正是一个见证。于是二者一致。截断在此无害，因为目标是集合之间的等式，而层级的载体是集合。
<!--/-->

```agda
pairʟ-fst : (a b : S) → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆
pairʟ-fst a b = PT.rec (setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆)
  (λ { (σ , (oσ , (fa∈ , fb∈))) →
       cong (λ (e : SetOf (PairOf.Q a b)) → fst (fst e))
         (hasPairL a b .snd (PairOf.mkPair a b σ oσ fa∈ fb∈)) })
  (isL-directed (fst a) (fst b) (a .snd) (b .snd))

unionʟ-fst : (a : S) → fst (unionʟ a) ≡ ⋃ (fst a)
unionʟ-fst a = PT.rec (setIsSet (fst (unionʟ a)) (⋃ (fst a)))
  (λ { (σ , (oσ , fa∈)) →
       cong (λ (e : SetOf (UnionOf.Q a)) → fst (fst e))
         (hasUnionL a .snd (UnionOf.mkUnion a σ oσ fa∈)) })
  (a .snd)
```

<!--en-->
The successor equation is the three of them composed, plus the hierarchy's own
identification of `{a, a}` with `{a}`: unfold the outer union, then the outer
pair, then the inner pair, then collapse the doubled singleton, and what is left
is the hierarchy's successor.
<!--zh-->
后继的等式就是这三条复合，再加上层级自己对 `{a, a}` 与 `{a}` 的认同：先展开外层的并，再外层的对，再内层的对，最后把重复的单点集塌掉，剩下的就是层级的后继。
<!--/-->

```agda
sucʟ-fst : (a : S) → fst (sucʟ a) ≡ sucV (fst a)
sucʟ-fst a =
    unionʟ-fst (pairʟ a (pairʟ a a))
  ∙ cong ⋃_ (pairʟ-fst a (pairʟ a a))
  ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pairʟ-fst a a)
  ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pair-singleton (fst a))
```

<!--en-->
## The chain
<!--zh-->
## 链
<!--/-->

<!--en-->
The chain is now written by ordinary recursion on a natural number, and one
induction says it projects onto the hierarchy's numerals. Zero is the empty set
built in the previous chapter, whose projection is the empty set on the nose.
<!--zh-->
链现在可以沿自然数普通递归写出，而一次归纳即说明它投影到层级的数码上。零就是上一章造出的空集，其投影严格就是空集。
<!--/-->

```agda
numeralL : ℕ → S
numeralL zero    = ∅ʟ
numeralL (suc n) = sucʟ (numeralL n)

numeralL-fst : (n : ℕ) → fst (numeralL n) ≡ # n
numeralL-fst zero    = refl
numeralL-fst (suc n) = sucʟ-fst (numeralL n) ∙ cong sucV (numeralL-fst n)
```

<!--en-->
## The two pinning equations
<!--zh-->
## 两条钉死方程
<!--/-->

<!--en-->
The model record does not take the chain on trust: it demands that zero be
empty and that each successor have exactly the members of its predecessor
together with the predecessor itself, both stated through membership rather than
through the derived operations. That phrasing is deliberate, and it is what makes
these two proofs cheap: each is a fact about the hierarchy's numerals,
transported along the projection equation. Nothing here ever unfolds a
description operator.
<!--zh-->
模型 record 不肯轻信这条链：它要求零为空，且每个后继的成员恰是前者的成员连同前者自身，两条都经隶属陈述，而非经派生运算。这个措辞是有意的，也正是这两个证明廉价的原因：每一条都是关于层级数码的事实，沿投影等式搬运过来。全程从不展开摹状词算子。
<!--/-->

```agda
numeralL-zero : (z : S) → ⟨ z ∈ˢ numeralL zero ⟩ → Empty.⊥
numeralL-zero z z∈ = ∅-empty (fst z)
  (∈∈ₛ {a = fst z} {b = ∅} .fst
    (subst (λ w → ⟨ fst z ∈ w ⟩) (numeralL-fst zero) z∈))

numeralL-suc : (n : ℕ) (z : S)
             → (⟨ z ∈ˢ numeralL (suc n) ⟩
                  → ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩)
             × (⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
                  → ⟨ z ∈ˢ numeralL (suc n) ⟩)
numeralL-suc n z = fwd , bwd
  where
  up : ⟨ z ∈ˢ numeralL (suc n) ⟩ → ⟨ fst z ∈ sucV (# n) ⟩
  up z∈ = subst (λ w → ⟨ fst z ∈ w ⟩) (numeralL-fst (suc n)) z∈

  fwd : ⟨ z ∈ˢ numeralL (suc n) ⟩
      → ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
  fwd z∈ = ∈sucV-elim {A = # n} {x = fst z}
    (snd ((z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n)))
    (up z∈)
    (λ fz∈#n → ∣ inl (subst (λ w → ⟨ fst z ∈ w ⟩) (sym (numeralL-fst n)) fz∈#n) ∣₁)
    (λ fz≡#n → ∣ inr (fz≡#n ∙ sym (numeralL-fst n)) ∣₁)

  bwd : ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
      → ⟨ z ∈ˢ numeralL (suc n) ⟩
  bwd = PT.rec (snd (z ∈ˢ numeralL (suc n)))
    (λ { (inl z∈n) →
           subst (λ w → ⟨ fst z ∈ w ⟩) (sym (numeralL-fst (suc n)))
             (∈sucV-inl {A = # n}
               (subst (λ w → ⟨ fst z ∈ w ⟩) (numeralL-fst n) z∈n))
       ; (inr z≡n) →
           subst (λ w → ⟨ fst z ∈ w ⟩) (sym (numeralL-fst (suc n)))
             (subst (λ w → ⟨ w ∈ sucV (# n) ⟩)
               (sym (z≡n ∙ numeralL-fst n)) (self∈sucV (# n))) })
```

<!--en-->
## Collecting the chain
<!--zh-->
## 收集这条链
<!--/-->

<!--en-->
Now the axiom proper. A set whose members are exactly the numerals must be
exhibited inside `L`, and the ambient hierarchy has the obvious candidate,
namely `ω`. What has to be shown is that `ω` is constructible, and the previous
chapter gives it in one line: `ω` is an ordinal, and an ordinal appears at the
stage after itself.

This is the step that costs the excluded middle, and it is worth seeing where
the cost went. Not into the chain, which was free; not into collecting a family,
which no principle here does; but into knowing *which ordinals live at which
stage*, and that is a comparison.
<!--zh-->
现在是公理本身。必须在 `L` 内拿出一个成员恰为诸数码的集合，而环境层级有现成的候选，即 `ω`。要证的是 `ω` 可构造，上一章一行给出：`ω` 是序数，而序数现身于自身之后的那个阶段。

这就是花费排中律的那一步，值得看清代价花在了哪里。不在链上，链是免费的；不在收集一个族上，此处没有任何原则做那件事；而在于知道**哪些序数住在哪个阶段**，那是一次比较。
<!--/-->

```agda
ω∈L : ⟨ isL ω ⟩
ω∈L = ∣ sucV ω , (suc-ord ω-ord , ord∈Lset-suc ω ω-ord) ∣₁

ωʟ : S
ωʟ = ω , ω∈L
```

<!--en-->
It remains to check that the members of `ωʟ` are exactly the numerals of the
chain. Membership in `ωʟ` is membership in `ω`, which the library gives as
"merely hit by some library numeral"; the chain's projection equation turns each
of those into a member of the chain, and back. So `ωʟ` realises the numeral
predicate, and extensionality makes it the unique such set.
<!--zh-->
余下要核对的是 `ωʟ` 的成员恰是链上的诸数码。属于 `ωʟ` 就是属于 `ω`，而库把后者给成「仅仅被某个库数码命中」；链的投影等式把其中每一个换成链的成员，反之亦然。于是 `ωʟ` 实现了那个数码谓词，而外延性使它成为唯一这样的集合。
<!--/-->

```agda
isNumeralL : S → Ω
isNumeralL x = ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralL (lower n))

ω-specL : (x : S) → (x ∈ˢ ωʟ) ≡ isNumeralL x
ω-specL x = ⇔toPath
  (PT.map (λ { (k , p) → lift (lower k)
             , (sym p ∙ sym (numeralL-fst (lower k))) }))
  (PT.map (λ { (n , q) → lift (lower n)
             , (sym (q ∙ numeralL-fst (lower n))) }))

hasInfinityL : isContr (SetOf isNumeralL)
hasInfinityL = uniqueL isNumeralL (ωʟ , ω-specL)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The axiom of infinity is paid in full: the chain `numeralL`{.Agda} with its two
pinning equations, and `hasInfinityL`{.Agda} collecting it into a set. Four
fields leave the frontier, and the split between them is the chapter's lesson.
Building the chain was free; collecting it cost one comparison of ordinals, and
therefore the excluded middle. That is the whole classical content of infinity
in `L`, and it is visible in this chapter's telescope.
<!--zh-->
无穷公理已全额付清：链 `numeralL`{.Agda} 连同它的两条钉死方程，以及把它收集成集合的 `hasInfinityL`{.Agda}。四个字段离开前沿，而二者之间的分野正是本章的教益。造链是免费的；收集它花掉一次序数比较，从而花掉排中律。这就是 `L` 中无穷公理的全部经典内容，而它在本章的参数表里一望可见。
<!--/-->
