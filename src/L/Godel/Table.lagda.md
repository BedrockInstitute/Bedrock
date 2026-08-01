# The denotation table

<!--en-->
The internal recursion's raw material. A table entry pairs a term code with
the term's denotation, and the clauses of this chapter say, one per
constructor, what an entry must look like against the family it sits in: the
code has this tag and this payload, the children's entries are present, and
the value is the operation of the children's values. Every ingredient is
already owned: the codes chapter fixed the payload shapes, the description
chapter fixed every operation's reading, and the coding part's readers walk
the pairs. This chapter binds them, one node clause at a time, each with a
meta shape and both readings; the tag-and-payload reader is factored first,
since every clause opens with it.
<!--zh-->
内部递归的原料。表的条目把项码与项的指称配成对，而本章的子句逐构造子说出条目对着其所在的族必须长什么样：码带这个标签与这个载荷、孩子的条目在场、取值是孩子取值上的那个运算。每样配料都已在手：码章钉了载荷形状，描述章钉了每个运算的读法，编码部分的读式行走诸对。本章把它们绑起来，一次一条节点子句，各带元层形状与双向读式；标签加载荷的读式先行提出，因为每条子句都以它开头。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Godel.Table {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate; numL )
open import L.Godel.Operations {ℓ} using ( _∪_; _∩_; shiftDown )
open import L.Godel.Definable {ℓ}
  using ( interAt; interAt-out; interAt-in
        ; unionAt; unionAt-out; unionAt-in
        ; shiftDownAt; shiftDownAt-out; shiftDownAt-in )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The tag-and-payload reader
<!--zh-->
## 标签加载荷读式
<!--/-->

<!--en-->
Every code is a pair of a numeral tag and a payload, so every clause opens by
reading one: the slot is the pair of this tag with that payload slot. The tag
is pinned by one object equality against the sealed numeral, and both
readings are the pair reader's, composed with the numeral's projection.
<!--zh-->
每个码都是数码标签与载荷的对，故每条子句都以读出一个这样的对开头：槽位是此标签与彼载荷槽位的对。标签由一条对着封印数码的对象等式钉住，两个读向都是对读式的，与数码的投影复合。
<!--/-->

```agda
tagPrAt : ∀ {n} → ℕ → Fin n → Fin n → Formula S n
tagPrAt tg s p =
  ∃̇ ((var zero ≐ con (numeralL tg)) ∧̇ prAtL (suc s) zero (suc p))

module _ {n : ℕ} (tg : ℕ) (s p : Fin n) (γ : S ^ n) where
  tagPr-out : ⟨ γ ⊨ tagPrAt tg s p ⟩
            → fst (lookup s γ) ≡ pr (# tg) (fst (lookup p γ))
  tagPr-out = PT.rec (setIsSet (fst (lookup s γ)) (pr (# tg) (fst (lookup p γ))))
    λ { (t , (ek , hp)) →
        subst ⟨_⟩ (prAtL-adequate (suc s) zero (suc p) (t ∷ γ)) hp
      ∙ cong (λ u → pr u (fst (lookup p γ))) (ek ∙ numeralL-fst tg) }

  tagPr-in : fst (lookup s γ) ≡ pr (# tg) (fst (lookup p γ))
           → ⟨ γ ⊨ tagPrAt tg s p ⟩
  tagPr-in e = ∣ (# tg , numL tg)
    , ( sym (numeralL-fst tg)
      , subst ⟨_⟩ (sym (prAtL-adequate (suc s) zero (suc p)
          ((# tg , numL tg) ∷ γ))) e ) ∣₁
```

<!--en-->
## The node clauses, unconditional three
<!--zh-->
## 节点子句，无条件的三条
<!--/-->

<!--en-->
One frame serves both binary nodes: five binders pick the payload pair, the
two children's codes and their recorded values, five conjuncts read the tag,
split the payload, find both entries and pin the value by the operation's
description. The shift node is the same with one child and no payload split.
Each clause carries its meta shape, and both readings are assembled from the
readers already in stock, with the packaged pair supplying the payload
witness on the way in.
<!--zh-->
一个框架供两个二元节点共用：五个束缚元挑出载荷对、两个孩子的码与其被记录的取值，五条合取读出标签、拆开载荷、找到两个条目、以运算的描述钉住取值。移位节点相同，只是单孩子、不拆载荷。每条子句携带元层形状，两个读向都由存货中的读式组装，进入方向由封印对供给载荷见证。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 x = suc (suc x)

  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 x = suc (suc (suc (suc (suc x))))

module BinNode (tg : ℕ) (op : V ℓ → V ℓ → V ℓ)
  (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (opAt-out : ∀ {n} (k i j : Fin n) (γ : S ^ n) → ⟨ γ ⊨ opAt k i j ⟩
            → fst (lookup k γ) ≡ op (fst (lookup i γ)) (fst (lookup j γ)))
  (opAt-in : ∀ {n} (k i j : Fin n) (γ : S ^ n)
           → fst (lookup k γ) ≡ op (fst (lookup i γ)) (fst (lookup j γ))
           → ⟨ γ ⊨ opAt k i j ⟩)
  where

  NodeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  NodeAt s w f = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt tg (sh5 s) (suc (suc (suc (suc zero))))
    ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) (suc (suc zero))
    ∧̇ ( appAt (sh5 f) (suc (suc (suc zero))) (suc zero)
    ∧̇ ( appAt (sh5 f) (suc (suc zero)) zero
    ∧̇ opAt (sh5 w) (suc zero) zero ))))))))

  NodeOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  NodeOf F x v = Σ[ cs ∈ S ] Σ[ ct ∈ S ] Σ[ ws ∈ S ] Σ[ wt ∈ S ]
    ( ⟨ pr (fst cs) (fst ws) ∈ F ⟩
    × ( ⟨ pr (fst ct) (fst wt) ∈ F ⟩
    × ( (x ≡ pr (# tg) (pr (fst cs) (fst ct)))
      × (v ≡ op (fst ws) (fst wt)) )))

  module _ {n : ℕ} (s w f : Fin n) (γ : S ^ n) where
    Node-out : ⟨ γ ⊨ NodeAt s w f ⟩
             → ∥ NodeOf (fst (lookup f γ)) (fst (lookup s γ))
                   (fst (lookup w γ)) ∥₁
    Node-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (cs , w₂) →
      PT.rec PT.squash₁ (λ { (ct , w₃) →
      PT.rec PT.squash₁ (λ { (ws , w₄) →
      PT.rec PT.squash₁ (λ { (wt , body) →
        finish p₁ cs ct ws wt body })
      w₄ }) w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ cs ct ws wt : S)
             → ⟨ (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt tg (sh5 s) (suc (suc (suc (suc zero))))
                     ∧̇ ( prAtL (suc (suc (suc (suc zero))))
                           (suc (suc (suc zero))) (suc (suc zero))
                     ∧̇ ( appAt (sh5 f) (suc (suc (suc zero))) (suc zero)
                     ∧̇ ( appAt (sh5 f) (suc (suc zero)) zero
                     ∧̇ opAt (sh5 w) (suc zero) zero )))) ⟩
             → ∥ NodeOf (fst (lookup f γ)) (fst (lookup s γ))
                   (fst (lookup w γ)) ∥₁
      finish p₁ cs ct ws wt (h1 , (h2 , (h3 , (h4 , h5)))) =
        ∣ cs , ct , ws , wt ,
          ( subst ⟨_⟩ (appAt-adequate (sh5 f) (suc (suc (suc zero)))
              (suc zero) (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ)) h3
          , ( subst ⟨_⟩ (appAt-adequate (sh5 f) (suc (suc zero)) zero
                (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ)) h4
          , ( ( tagPr-out tg (sh5 s) (suc (suc (suc (suc zero))))
                  (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ) h1
              ∙ cong (pr (# tg))
                  (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                    (suc (suc (suc zero))) (suc (suc zero))
                    (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ)) h2) )
            , opAt-out (sh5 w) (suc zero) zero
                (wt ∷ ws ∷ ct ∷ cs ∷ p₁ ∷ γ) h5 ) ) ) ∣₁

    Node-in : NodeOf (fst (lookup f γ)) (fst (lookup s γ)) (fst (lookup w γ))
            → ⟨ γ ⊨ NodeAt s w f ⟩
    Node-in (cs , ct , ws , wt , (e1 , (e2 , (qs , qw)))) =
      ∣ prʟ cs ct , ∣ cs , ∣ ct , ∣ ws , ∣ wt ,
        ( tagPr-in tg (sh5 s) (suc (suc (suc (suc zero))))
            (wt ∷ ws ∷ ct ∷ cs ∷ prʟ cs ct ∷ γ)
            (qs ∙ cong (pr (# tg)) (sym (prʟ-fst cs ct)))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
              (suc (suc (suc zero))) (suc (suc zero))
              (wt ∷ ws ∷ ct ∷ cs ∷ prʟ cs ct ∷ γ))) (prʟ-fst cs ct)
        , ( subst ⟨_⟩ (sym (appAt-adequate (sh5 f) (suc (suc (suc zero)))
              (suc zero) (wt ∷ ws ∷ ct ∷ cs ∷ prʟ cs ct ∷ γ))) e1
        , ( subst ⟨_⟩ (sym (appAt-adequate (sh5 f) (suc (suc zero)) zero
              (wt ∷ ws ∷ ct ∷ cs ∷ prʟ cs ct ∷ γ))) e2
        , opAt-in (sh5 w) (suc zero) zero
            (wt ∷ ws ∷ ct ∷ cs ∷ prʟ cs ct ∷ γ) qw ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

module InterNode = BinNode 4 _∩_ interAt interAt-out interAt-in
module UnionNode = BinNode 5 _∪_ unionAt unionAt-out unionAt-in

shiftNodeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
shiftNodeAt s w f = ∃̇ (∃̇
  ( tagPrAt 7 (sh2 s) (suc zero)
  ∧̇ ( appAt (sh2 f) (suc zero) zero
    ∧̇ shiftDownAt (sh2 w) zero )))

NodeShiftOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
NodeShiftOf F x v = Σ[ ct ∈ S ] Σ[ wt ∈ S ]
  ( ⟨ pr (fst ct) (fst wt) ∈ F ⟩
  × ( (x ≡ pr (# 7) (fst ct))
    × (v ≡ shiftDown (fst wt)) ))

module _ {n : ℕ} (s w f : Fin n) (γ : S ^ n) where
  shiftNode-out : ⟨ γ ⊨ shiftNodeAt s w f ⟩
                → ∥ NodeShiftOf (fst (lookup f γ)) (fst (lookup s γ))
                      (fst (lookup w γ)) ∥₁
  shiftNode-out =
    PT.rec PT.squash₁ (λ { (ct , w₁) →
    PT.rec PT.squash₁ (λ { (wt , body) → finish ct wt body })
    w₁ })
    where
    finish : (ct wt : S)
           → ⟨ (wt ∷ ct ∷ γ)
                 ⊨ ( tagPrAt 7 (sh2 s) (suc zero)
                   ∧̇ ( appAt (sh2 f) (suc zero) zero
                     ∧̇ shiftDownAt (sh2 w) zero ) ) ⟩
           → ∥ NodeShiftOf (fst (lookup f γ)) (fst (lookup s γ))
                 (fst (lookup w γ)) ∥₁
    finish ct wt (h1 , (h2 , h3)) =
      ∣ ct , wt ,
        ( subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero
            (wt ∷ ct ∷ γ)) h2
        , ( tagPr-out 7 (sh2 s) (suc zero) (wt ∷ ct ∷ γ) h1
          , shiftDownAt-out (sh2 w) zero (wt ∷ ct ∷ γ) h3 ) ) ∣₁

  shiftNode-in : NodeShiftOf (fst (lookup f γ)) (fst (lookup s γ))
                   (fst (lookup w γ))
               → ⟨ γ ⊨ shiftNodeAt s w f ⟩
  shiftNode-in (ct , wt , (e1 , (qs , qw))) =
    ∣ ct , ∣ wt ,
      ( tagPr-in 7 (sh2 s) (suc zero) (wt ∷ ct ∷ γ) qs
      , ( subst ⟨_⟩ (sym (appAt-adequate (sh2 f) (suc zero) zero
            (wt ∷ ct ∷ γ))) e1
        , shiftDownAt-in (sh2 w) zero (wt ∷ ct ∷ γ) qw ) )
    ∣₁ ∣₁
```
