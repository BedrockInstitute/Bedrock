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
  using ( Formula; var; con; _≐_; _∧̇_; _∨̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; module FinOf )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; sucAtL; sucAtL-adequate; numL )
open import L.Godel.Operations {ℓ}
  using ( _∪_; _∩_; _∖_; shiftDown; selectMember; selectEqual; extendFamily )
open import L.Godel.Tuples {ℓ} using ( allTuples )
open import L.Godel.Definable {ℓ}
  using ( interAt; interAt-out; interAt-in
        ; unionAt; unionAt-out; unionAt-in
        ; diffAt; diffAt-out; diffAt-in
        ; shiftDownAt; shiftDownAt-out; shiftDownAt-in
        ; allTuplesAt; allTuplesAt-out; allTuplesAt-in
        ; selectMemberAt; selectMemberAt-out; selectMemberAt-in
        ; selectEqualAt; selectEqualAt-out; selectEqualAt-in
        ; extendFamilyAt; extendFamilyAt-out; extendFamilyAt-in )
open import L.Godel.InL {ℓ}
  using ( allTuplesL; selectEqualL; extendFamilyL; denoteL; stageFam )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK
        ; ⟦_⟧ᴷ )
open import L.Godel.Codes {ℓ}
  using ( module Codes; tagNe; SubK; sizeK; subK; subSplitK; selfIxK; sub-selfK
        ; interIdxL; interIdxR; unionIdxL; unionIdxR )
open import L.Coding.InL {ℓ} using ( sglL )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( znots; snotz; injSuc )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( module FinSumChar )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )

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

<!--en-->
## The conditional clauses: the complement and the tuple leaf
<!--zh-->
## 有条件的子句：补节点与元组叶
<!--/-->

<!--en-->
Where a clause reads an arity off a payload, the outward reading cannot know
the payload is a numeral, so the meta shape carries the fact conditionally:
whenever the payload equals a numeral, the bound family is the tuple family
at that arity. The inward reading always has the arity, since it starts from
a real code, so it takes the number explicitly and every witness package is
assembled from the constructibility lemmas of the bridge chapter. The
complement node is the pattern's first instance; the tuple leaf is its
smallest, one binder and two conjuncts.
<!--zh-->
凡子句从载荷读出元数之处，向外的读向无从知道载荷是数码，故元层形状把这件事作为条件式携带：只要载荷等于某数码，被绑的族就是该元数处的元组族。向内的读向总是持有元数，因为它从真实的码出发，故显式接收数字，每个见证包由桥梁章的可构造性引理组装。补节点是该模式的第一个实例；元组叶是最小的一个，一个束缚元两条合取。
<!--/-->

```agda
private
  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 x = suc (suc (suc (suc (suc (suc x)))))

  sh10 : ∀ {n} → Fin n
       → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))
  sh10 x = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc x)))))))))

  nS : ℕ → S
  nS j = # j , numL j

complNodeAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
complNodeAt s w f a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
  ( tagPrAt 6 (sh5 s) (suc (suc (suc (suc zero))))
  ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) (suc (suc zero))
  ∧̇ ( appAt (sh5 f) (suc (suc zero)) (suc zero)
  ∧̇ ( allTuplesAt zero (sh5 a) (suc (suc (suc zero)))
  ∧̇ diffAt (sh5 w) zero (suc zero) ))))))))

NodeComplOf : V ℓ → V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
NodeComplOf A F x v = Σ[ mv ∈ S ] Σ[ ct ∈ S ] Σ[ wt ∈ S ] Σ[ w' ∈ S ]
  ( ⟨ pr (fst ct) (fst wt) ∈ F ⟩
  × ( (x ≡ pr (# 6) (pr (fst mv) (fst ct)))
  × ( ((m : ℕ) → fst mv ≡ # m → fst w' ≡ allTuples A m)
    × (v ≡ fst w' ∖ fst wt) )))

module _ {n : ℕ} (s w f a : Fin n) (γ : S ^ n) where
  complNode-out : ⟨ γ ⊨ complNodeAt s w f a ⟩
                → ∥ NodeComplOf (fst (lookup a γ)) (fst (lookup f γ))
                      (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
  complNode-out =
    PT.rec PT.squash₁ (λ { (p₁ , w₁) →
    PT.rec PT.squash₁ (λ { (mv , w₂) →
    PT.rec PT.squash₁ (λ { (ct , w₃) →
    PT.rec PT.squash₁ (λ { (wt , w₄) →
    PT.rec PT.squash₁ (λ { (w' , body) →
      finish p₁ mv ct wt w' body })
    w₄ }) w₃ }) w₂ }) w₁ })
    where
    finish : (p₁ mv ct wt w' : S)
           → ⟨ (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ)
                 ⊨ ( tagPrAt 6 (sh5 s) (suc (suc (suc (suc zero))))
                   ∧̇ ( prAtL (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero))) (suc (suc zero))
                   ∧̇ ( appAt (sh5 f) (suc (suc zero)) (suc zero)
                   ∧̇ ( allTuplesAt zero (sh5 a) (suc (suc (suc zero)))
                   ∧̇ diffAt (sh5 w) zero (suc zero) )))) ⟩
           → ∥ NodeComplOf (fst (lookup a γ)) (fst (lookup f γ))
                 (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    finish p₁ mv ct wt w' (h1 , (h2 , (h3 , (h4 , h5)))) =
      ∣ mv , ct , wt , w' ,
        ( subst ⟨_⟩ (appAt-adequate (sh5 f) (suc (suc zero)) (suc zero)
            (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ)) h3
        , ( ( tagPr-out 6 (sh5 s) (suc (suc (suc (suc zero))))
                (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ) h1
            ∙ cong (pr (# 6))
                (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero))) (suc (suc zero))
                  (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ)) h2) )
        , ( (λ m qm → allTuplesAt-out zero (sh5 a) (suc (suc (suc zero)))
              (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ) m qm h4)
          , diffAt-out (sh5 w) zero (suc zero)
              (w' ∷ wt ∷ ct ∷ mv ∷ p₁ ∷ γ) h5 ) ) ) ∣₁

  complNode-in : (m : ℕ) (ct wt : S)
               → ⟨ pr (fst ct) (fst wt) ∈ fst (lookup f γ) ⟩
               → fst (lookup s γ) ≡ pr (# 6) (pr (# m) (fst ct))
               → fst (lookup w γ) ≡ allTuples (fst (lookup a γ)) m ∖ fst wt
               → ⟨ γ ⊨ complNodeAt s w f a ⟩
  complNode-in m ct wt e1 qs qw =
    ∣ prʟ (nS m) ct , ∣ nS m , ∣ ct , ∣ wt , ∣ w'S ,
      ( tagPr-in 6 (sh5 s) (suc (suc (suc (suc zero)))) env₅
          (qs ∙ cong (pr (# 6)) (sym (prʟ-fst (nS m) ct)))
      , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
            (suc (suc (suc zero))) (suc (suc zero)) env₅)) (prʟ-fst (nS m) ct)
      , ( subst ⟨_⟩ (sym (appAt-adequate (sh5 f) (suc (suc zero)) (suc zero)
            env₅)) e1
      , ( allTuplesAt-in zero (sh5 a) (suc (suc (suc zero))) env₅ m refl refl
        , diffAt-in (sh5 w) zero (suc zero) env₅ qw ) ) ) )
    ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    w'S : S
    w'S = allTuples (fst (lookup a γ)) m
        , allTuplesL (fst (lookup a γ)) (lookup a γ .snd) m
    env₅ : S ^ (suc (suc (suc (suc (suc n)))))
    env₅ = w'S ∷ wt ∷ ct ∷ nS m ∷ prʟ (nS m) ct ∷ γ

allLeafAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
allLeafAt s w a = ∃̇
  ( tagPrAt 0 (suc s) zero
  ∧̇ allTuplesAt (suc w) (suc a) zero )

LeafAllOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
LeafAllOf A x v = Σ[ mv ∈ S ]
  ( (x ≡ pr (# 0) (fst mv))
  × ((m : ℕ) → fst mv ≡ # m → v ≡ allTuples A m) )

module _ {n : ℕ} (s w a : Fin n) (γ : S ^ n) where
  allLeaf-out : ⟨ γ ⊨ allLeafAt s w a ⟩
              → ∥ LeafAllOf (fst (lookup a γ)) (fst (lookup s γ))
                    (fst (lookup w γ)) ∥₁
  allLeaf-out = PT.rec PT.squash₁
    λ { (mv , (h1 , h2)) →
      ∣ mv
      , ( tagPr-out 0 (suc s) zero (mv ∷ γ) h1
        , (λ m qm → allTuplesAt-out (suc w) (suc a) zero (mv ∷ γ) m qm h2) )
      ∣₁ }

  allLeaf-in : (m : ℕ)
             → fst (lookup s γ) ≡ pr (# 0) (# m)
             → fst (lookup w γ) ≡ allTuples (fst (lookup a γ)) m
             → ⟨ γ ⊨ allLeafAt s w a ⟩
  allLeaf-in m qs qw =
    ∣ nS m
    , ( tagPr-in 0 (suc s) zero (nS m ∷ γ) qs
      , allTuplesAt-in (suc w) (suc a) zero (nS m ∷ γ) m refl qw )
    ∣₁
```

<!--en-->
## The selection leaves
<!--zh-->
## 选择叶
<!--/-->

<!--en-->
One frame serves the two plain selection leaves: the payload splits twice
into an arity and two key numerals, the tuple family is bound at the arity
conditionally as before, and the selection description pins the value at the
two keys. The constant selection leaf is the long composite: its payload
carries a carrier member, the successor key is the sealed numeral one up, so
its clause holds by `refl`{.Agda} on the way in, and the value chains the
extension, the selection and the shift through two bound intermediates whose
witness packages come from the bridge chapter.
<!--zh-->
一个框架供两个朴素选择叶共用：载荷两次拆开为元数与两个键数码，元组族照旧有条件地绑在元数处，选择描述在两个键处钉住取值。常量选择叶是那条长复合：其载荷携带载体成员，后继键是高一位的封印数码，故其子句在进入方向由 `refl`{.Agda} 成立，而取值经两个被绑中间件把扩张、选择与移位串起来，见证包来自桥梁章。
<!--/-->

```agda
module SelLeaf (tg : ℕ) (sel : V ℓ → V ℓ → V ℓ → V ℓ)
  (selAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (selAt-out : ∀ {n} (k f' a' b' : Fin n) (γ : S ^ n) → ⟨ γ ⊨ selAt k f' a' b' ⟩
             → fst (lookup k γ)
             ≡ sel (fst (lookup f' γ)) ⁅ fst (lookup a' γ) ⁆s ⁅ fst (lookup b' γ) ⁆s)
  (selAt-in : ∀ {n} (k f' a' b' : Fin n) (γ : S ^ n)
            → fst (lookup k γ)
            ≡ sel (fst (lookup f' γ)) ⁅ fst (lookup a' γ) ⁆s ⁅ fst (lookup b' γ) ⁆s
            → ⟨ γ ⊨ selAt k f' a' b' ⟩)
  where

  LeafAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  LeafAt s w a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt tg (sh6 s) (suc (suc (suc (suc (suc zero)))))
    ∧̇ ( prAtL (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero)))
          (suc (suc (suc (suc zero))))
    ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero)) (suc zero)
    ∧̇ ( allTuplesAt zero (sh6 a) (suc (suc (suc zero)))
    ∧̇ selAt (sh6 w) zero (suc (suc zero)) (suc zero) )))))))))

  LeafOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  LeafOf A x v = Σ[ mv ∈ S ] Σ[ iv ∈ S ] Σ[ jv ∈ S ] Σ[ w' ∈ S ]
    ( (x ≡ pr (# tg) (pr (fst mv) (pr (fst iv) (fst jv))))
    × ( ((m : ℕ) → fst mv ≡ # m → fst w' ≡ allTuples A m)
      × (v ≡ sel (fst w') ⁅ fst iv ⁆s ⁅ fst jv ⁆s) ))

  module _ {n : ℕ} (s w a : Fin n) (γ : S ^ n) where
    Leaf-out : ⟨ γ ⊨ LeafAt s w a ⟩
             → ∥ LeafOf (fst (lookup a γ)) (fst (lookup s γ))
                   (fst (lookup w γ)) ∥₁
    Leaf-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (p₂ , w₂) →
      PT.rec PT.squash₁ (λ { (mv , w₃) →
      PT.rec PT.squash₁ (λ { (iv , w₄) →
      PT.rec PT.squash₁ (λ { (jv , w₅) →
      PT.rec PT.squash₁ (λ { (w' , body) →
        finish p₁ p₂ mv iv jv w' body })
      w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ p₂ mv iv jv w' : S)
             → ⟨ (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt tg (sh6 s) (suc (suc (suc (suc (suc zero)))))
                     ∧̇ ( prAtL (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
                     ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero))
                           (suc zero)
                     ∧̇ ( allTuplesAt zero (sh6 a) (suc (suc (suc zero)))
                     ∧̇ selAt (sh6 w) zero (suc (suc zero)) (suc zero) )))) ⟩
             → ∥ LeafOf (fst (lookup a γ)) (fst (lookup s γ))
                   (fst (lookup w γ)) ∥₁
      finish p₁ p₂ mv iv jv w' (h1 , (h2 , (h3 , (h4 , h5)))) =
        ∣ mv , iv , jv , w' ,
          ( ( tagPr-out tg (sh6 s) (suc (suc (suc (suc (suc zero)))))
                (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ) h1
            ∙ cong (pr (# tg))
                ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                    (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
                    (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ)) h2
                ∙ cong (pr (fst mv))
                    (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                      (suc (suc zero)) (suc zero)
                      (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ)) h3) ) )
          , ( (λ m qm → allTuplesAt-out zero (sh6 a) (suc (suc (suc zero)))
                (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ) m qm h4)
            , selAt-out (sh6 w) zero (suc (suc zero)) (suc zero)
                (w' ∷ jv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ) h5 ) ) ∣₁

    Leaf-in : (m i j : ℕ)
            → fst (lookup s γ) ≡ pr (# tg) (pr (# m) (pr (# i) (# j)))
            → fst (lookup w γ)
              ≡ sel (allTuples (fst (lookup a γ)) m) ⁅ # i ⁆s ⁅ # j ⁆s
            → ⟨ γ ⊨ LeafAt s w a ⟩
    Leaf-in m i j qs qw =
      ∣ prʟ (nS m) (prʟ (nS i) (nS j)) , ∣ prʟ (nS i) (nS j)
      , ∣ nS m , ∣ nS i , ∣ nS j , ∣ w'S ,
        ( tagPr-in tg (sh6 s) (suc (suc (suc (suc (suc zero))))) env₆
            (qs ∙ cong (pr (# tg))
              (sym ( prʟ-fst (nS m) (prʟ (nS i) (nS j))
                   ∙ cong (pr (# m)) (prʟ-fst (nS i) (nS j)) )))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
              (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) env₆))
              (prʟ-fst (nS m) (prʟ (nS i) (nS j)))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
              (suc (suc zero)) (suc zero) env₆))
              (prʟ-fst (nS i) (nS j))
        , ( allTuplesAt-in zero (sh6 a) (suc (suc (suc zero))) env₆ m refl refl
          , selAt-in (sh6 w) zero (suc (suc zero)) (suc zero) env₆ qw ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      w'S : S
      w'S = allTuples (fst (lookup a γ)) m
          , allTuplesL (fst (lookup a γ)) (lookup a γ .snd) m
      env₆ : S ^ (suc (suc (suc (suc (suc (suc n))))))
      env₆ = w'S ∷ nS j ∷ nS i ∷ nS m
           ∷ prʟ (nS i) (nS j) ∷ prʟ (nS m) (prʟ (nS i) (nS j)) ∷ γ

module SelMemLeaf = SelLeaf 1 selectMember
  selectMemberAt selectMemberAt-out selectMemberAt-in
module SelEqLeaf = SelLeaf 2 selectEqual
  selectEqualAt selectEqualAt-out selectEqualAt-in
```

```agda
selEqConLeafAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
selEqConLeafAt s w a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇
  ( tagPrAt 3 (sh10 s)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  ∧̇ ( prAtL (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
        (suc (suc (suc (suc (suc (suc (suc zero)))))))
        (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  ∧̇ ( prAtL (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
        (suc (suc (suc (suc (suc (suc zero))))))
        (suc (suc (suc (suc (suc zero)))))
  ∧̇ ( allTuplesAt (suc (suc (suc (suc zero)))) (sh10 a)
        (suc (suc (suc (suc (suc (suc (suc zero)))))))
  ∧̇ ( sucAtL (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero)))
  ∧̇ ( (var (suc (suc zero)) ≐ con (numeralL 0))
  ∧̇ ( extendFamilyAt (suc zero) (suc (suc (suc (suc zero))))
        (suc (suc (suc (suc (suc zero)))))
  ∧̇ ( selectEqualAt zero (suc zero) (suc (suc (suc zero))) (suc (suc zero))
  ∧̇ shiftDownAt (sh10 w) zero )))))))))))))))))

LeafSelEqConOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
LeafSelEqConOf A x v = Σ[ mv ∈ S ] Σ[ iv ∈ S ] Σ[ cv ∈ S ] Σ[ w₁ ∈ S ] Σ[ w₂ ∈ S ]
  ( (x ≡ pr (# 3) (pr (fst mv) (pr (fst iv) (fst cv))))
  × ( ((m : ℕ) → fst mv ≡ # m → fst w₁ ≡ allTuples A m)
  × ( (fst w₂ ≡ extendFamily (fst w₁) ⁅ fst cv ⁆s)
    × (v ≡ shiftDown (selectEqual (fst w₂) ⁅ sucV (fst iv) ⁆s ⁅ # 0 ⁆s)) )))

module _ {n : ℕ} (s w a : Fin n) (γ : S ^ n) where
  selEqConLeaf-out : ⟨ γ ⊨ selEqConLeafAt s w a ⟩
                   → ∥ LeafSelEqConOf (fst (lookup a γ)) (fst (lookup s γ))
                         (fst (lookup w γ)) ∥₁
  selEqConLeaf-out =
    PT.rec PT.squash₁ (λ { (p₁ , u₁) →
    PT.rec PT.squash₁ (λ { (p₂ , u₂) →
    PT.rec PT.squash₁ (λ { (mv , u₃) →
    PT.rec PT.squash₁ (λ { (iv , u₄) →
    PT.rec PT.squash₁ (λ { (cv , u₅) →
    PT.rec PT.squash₁ (λ { (w₁ , u₆) →
    PT.rec PT.squash₁ (λ { (sv , u₇) →
    PT.rec PT.squash₁ (λ { (zv , u₈) →
    PT.rec PT.squash₁ (λ { (w₂ , u₉) →
    PT.rec PT.squash₁ (λ { (w₃ , body) →
      finish p₁ p₂ mv iv cv w₁ sv zv w₂ w₃ body })
    u₉ }) u₈ }) u₇ }) u₆ }) u₅ }) u₄ }) u₃ }) u₂ }) u₁ })
    where
    finish : (p₁ p₂ mv iv cv w₁ sv zv w₂ w₃ : S)
           → ⟨ (w₃ ∷ w₂ ∷ zv ∷ sv ∷ w₁ ∷ cv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ)
                 ⊨ ( tagPrAt 3 (sh10 s)
                       (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                   ∧̇ ( prAtL (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                         (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                   ∧̇ ( prAtL (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                         (suc (suc (suc (suc (suc (suc zero))))))
                         (suc (suc (suc (suc (suc zero)))))
                   ∧̇ ( allTuplesAt (suc (suc (suc (suc zero)))) (sh10 a)
                         (suc (suc (suc (suc (suc (suc (suc zero)))))))
                   ∧̇ ( sucAtL (suc (suc (suc (suc (suc (suc zero))))))
                         (suc (suc (suc zero)))
                   ∧̇ ( (var (suc (suc zero)) ≐ con (numeralL 0))
                   ∧̇ ( extendFamilyAt (suc zero) (suc (suc (suc (suc zero))))
                         (suc (suc (suc (suc (suc zero)))))
                   ∧̇ ( selectEqualAt zero (suc zero) (suc (suc (suc zero)))
                         (suc (suc zero))
                   ∧̇ shiftDownAt (sh10 w) zero )))))))) ⟩
           → ∥ LeafSelEqConOf (fst (lookup a γ)) (fst (lookup s γ))
                 (fst (lookup w γ)) ∥₁
    finish p₁ p₂ mv iv cv w₁ sv zv w₂ w₃
      (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , (h7 , (h8 , h9)))))))) =
      ∣ mv , iv , cv , w₁ , w₂ ,
        ( ( tagPr-out 3 (sh10 s)
              (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
              env h1
          ∙ cong (pr (# 3))
              ( subst ⟨_⟩ (prAtL-adequate
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                  (suc (suc (suc (suc (suc (suc (suc zero)))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                  env) h2
              ∙ cong (pr (fst mv))
                  (subst ⟨_⟩ (prAtL-adequate
                    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                    (suc (suc (suc (suc (suc (suc zero))))))
                    (suc (suc (suc (suc (suc zero))))) env) h3) ) )
        , ( (λ m qm → allTuplesAt-out (suc (suc (suc (suc zero)))) (sh10 a)
              (suc (suc (suc (suc (suc (suc (suc zero))))))) env m qm h4)
        , ( extendFamilyAt-out (suc zero) (suc (suc (suc (suc zero))))
              (suc (suc (suc (suc (suc zero))))) env h7
          , ( shiftDownAt-out (sh10 w) zero env h9
            ∙ cong shiftDown
                ( selectEqualAt-out zero (suc zero) (suc (suc (suc zero)))
                    (suc (suc zero)) env h8
                ∙ cong₂ (λ u u' → selectEqual (fst w₂) ⁅ u ⁆s ⁅ u' ⁆s)
                    (subst ⟨_⟩ (sucAtL-adequate
                      (suc (suc (suc (suc (suc (suc zero))))))
                      (suc (suc (suc zero))) env) h5)
                    (h6 ∙ numeralL-fst 0) ) ) ) ) ) ∣₁
      where
      env : S ^ (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))
      env = w₃ ∷ w₂ ∷ zv ∷ sv ∷ w₁ ∷ cv ∷ iv ∷ mv ∷ p₂ ∷ p₁ ∷ γ

  selEqConLeaf-in : (m i : ℕ) (cv : S)
    → fst (lookup s γ) ≡ pr (# 3) (pr (# m) (pr (# i) (fst cv)))
    → fst (lookup w γ)
      ≡ shiftDown (selectEqual
          (extendFamily (allTuples (fst (lookup a γ)) m) ⁅ fst cv ⁆s)
          ⁅ # (suc i) ⁆s ⁅ # 0 ⁆s)
    → ⟨ γ ⊨ selEqConLeafAt s w a ⟩
  selEqConLeaf-in m i cv qs qw =
    ∣ prʟ (nS m) (prʟ (nS i) cv) , ∣ prʟ (nS i) cv
    , ∣ nS m , ∣ nS i , ∣ cv , ∣ w₁S , ∣ nS (suc i) , ∣ nS 0 , ∣ w₂S , ∣ w₃S ,
      ( tagPr-in 3 (sh10 s)
          (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) env
          (qs ∙ cong (pr (# 3))
            (sym ( prʟ-fst (nS m) (prʟ (nS i) cv)
                 ∙ cong (pr (# m)) (prʟ-fst (nS i) cv) )))
      , ( subst ⟨_⟩ (sym (prAtL-adequate
            (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
            (suc (suc (suc (suc (suc (suc (suc zero)))))))
            (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) env))
            (prʟ-fst (nS m) (prʟ (nS i) cv))
      , ( subst ⟨_⟩ (sym (prAtL-adequate
            (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
            (suc (suc (suc (suc (suc (suc zero))))))
            (suc (suc (suc (suc (suc zero))))) env))
            (prʟ-fst (nS i) cv)
      , ( allTuplesAt-in (suc (suc (suc (suc zero)))) (sh10 a)
            (suc (suc (suc (suc (suc (suc (suc zero))))))) env m refl refl
      , ( subst ⟨_⟩ (sym (sucAtL-adequate
            (suc (suc (suc (suc (suc (suc zero))))))
            (suc (suc (suc zero))) env)) refl
      , ( sym (numeralL-fst 0)
      , ( extendFamilyAt-in (suc zero) (suc (suc (suc (suc zero))))
            (suc (suc (suc (suc (suc zero))))) env refl
      , ( selectEqualAt-in zero (suc zero) (suc (suc (suc zero)))
            (suc (suc zero)) env refl
        , shiftDownAt-in (sh10 w) zero env qw ) ) ) ) ) ) ) )
    ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    w₁S : S
    w₁S = allTuples (fst (lookup a γ)) m
        , allTuplesL (fst (lookup a γ)) (lookup a γ .snd) m
    w₂S : S
    w₂S = extendFamily (fst w₁S) ⁅ fst cv ⁆s
        , extendFamilyL (w₁S .snd) (sglL (cv .snd))
    w₃S : S
    w₃S = selectEqual (fst w₂S) ⁅ # (suc i) ⁆s ⁅ # 0 ⁆s
        , selectEqualL (w₂S .snd) (sglL (numL (suc i))) (sglL (numL 0))
    env : S ^ (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))
    env = w₃S ∷ w₂S ∷ nS 0 ∷ nS (suc i) ∷ w₁S ∷ cv ∷ nS i ∷ nS m
        ∷ prʟ (nS i) cv ∷ prʟ (nS m) (prʟ (nS i) cv) ∷ γ
```

<!--en-->
## The clause
<!--zh-->
## 子句
<!--/-->

<!--en-->
Eight constructors, one disjunction, in tag order. The outward reading peels
the disjunction and hands each branch to its own reader; the eight
injections are what the approximation family will use, one per constructor,
since the inward readings take their numerals explicitly and no single
inverse exists at the disjunction.
<!--zh-->
八个构造子，一个析取，按标签排序。向外的读向剥开析取，把每个分支递给自己的读式；八个注入是逼近族将要使用的东西，每构造子一个，因为向内的读式显式接收数码，析取处不存在单一的逆。
<!--/-->

```agda
ClauseAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
ClauseAt s w f a =
  allLeafAt s w a
  ∨̇ ( SelMemLeaf.LeafAt s w a
  ∨̇ ( SelEqLeaf.LeafAt s w a
  ∨̇ ( selEqConLeafAt s w a
  ∨̇ ( InterNode.NodeAt s w f
  ∨̇ ( UnionNode.NodeAt s w f
  ∨̇ ( complNodeAt s w f a
    ∨̇ shiftNodeAt s w f ))))))

ClauseOf : V ℓ → V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
ClauseOf A F x v =
  LeafAllOf A x v
  ⊎ ( SelMemLeaf.LeafOf A x v
  ⊎ ( SelEqLeaf.LeafOf A x v
  ⊎ ( LeafSelEqConOf A x v
  ⊎ ( InterNode.NodeOf F x v
  ⊎ ( UnionNode.NodeOf F x v
  ⊎ ( NodeComplOf A F x v
    ⊎ NodeShiftOf F x v ))))))

module _ {n : ℕ} (s w f a : Fin n) (γ : S ^ n) where
  Clause-out : ⟨ γ ⊨ ClauseAt s w f a ⟩
             → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
                   (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
  Clause-out = PT.rec PT.squash₁ br₁
    where
    br₈ : ⟨ γ ⊨ complNodeAt s w f a ⟩ ⊎ ⟨ γ ⊨ shiftNodeAt s w f ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₈ (inl x) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inl c)))))))
      (complNode-out s w f a γ x)
    br₈ (inr x) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inr c)))))))
      (shiftNode-out s w f γ x)
    br₇ : ⟨ γ ⊨ UnionNode.NodeAt s w f ⟩
        ⊎ ⟨ γ ⊨ (complNodeAt s w f a ∨̇ shiftNodeAt s w f) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₇ (inl x) = PT.map (λ c → inr (inr (inr (inr (inr (inl c))))))
      (UnionNode.Node-out s w f γ x)
    br₇ (inr r) = PT.rec PT.squash₁ br₈ r
    br₆ : ⟨ γ ⊨ InterNode.NodeAt s w f ⟩
        ⊎ ⟨ γ ⊨ (UnionNode.NodeAt s w f
              ∨̇ (complNodeAt s w f a ∨̇ shiftNodeAt s w f)) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₆ (inl x) = PT.map (λ c → inr (inr (inr (inr (inl c)))))
      (InterNode.Node-out s w f γ x)
    br₆ (inr r) = PT.rec PT.squash₁ br₇ r
    br₅ : ⟨ γ ⊨ selEqConLeafAt s w a ⟩
        ⊎ ⟨ γ ⊨ (InterNode.NodeAt s w f
              ∨̇ (UnionNode.NodeAt s w f
              ∨̇ (complNodeAt s w f a ∨̇ shiftNodeAt s w f))) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₅ (inl x) = PT.map (λ c → inr (inr (inr (inl c))))
      (selEqConLeaf-out s w a γ x)
    br₅ (inr r) = PT.rec PT.squash₁ br₆ r
    br₄ : ⟨ γ ⊨ SelEqLeaf.LeafAt s w a ⟩
        ⊎ ⟨ γ ⊨ (selEqConLeafAt s w a
              ∨̇ (InterNode.NodeAt s w f
              ∨̇ (UnionNode.NodeAt s w f
              ∨̇ (complNodeAt s w f a ∨̇ shiftNodeAt s w f)))) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₄ (inl x) = PT.map (λ c → inr (inr (inl c)))
      (SelEqLeaf.Leaf-out s w a γ x)
    br₄ (inr r) = PT.rec PT.squash₁ br₅ r
    br₃ : ⟨ γ ⊨ SelMemLeaf.LeafAt s w a ⟩
        ⊎ ⟨ γ ⊨ (SelEqLeaf.LeafAt s w a
              ∨̇ (selEqConLeafAt s w a
              ∨̇ (InterNode.NodeAt s w f
              ∨̇ (UnionNode.NodeAt s w f
              ∨̇ (complNodeAt s w f a ∨̇ shiftNodeAt s w f))))) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₃ (inl x) = PT.map (λ c → inr (inl c))
      (SelMemLeaf.Leaf-out s w a γ x)
    br₃ (inr r) = PT.rec PT.squash₁ br₄ r
    br₁ : ⟨ γ ⊨ allLeafAt s w a ⟩
        ⊎ ⟨ γ ⊨ (SelMemLeaf.LeafAt s w a
              ∨̇ (SelEqLeaf.LeafAt s w a
              ∨̇ (selEqConLeafAt s w a
              ∨̇ (InterNode.NodeAt s w f
              ∨̇ (UnionNode.NodeAt s w f
              ∨̇ (complNodeAt s w f a ∨̇ shiftNodeAt s w f)))))) ⟩
        → ∥ ClauseOf (fst (lookup a γ)) (fst (lookup f γ))
              (fst (lookup s γ)) (fst (lookup w γ)) ∥₁
    br₁ (inl x) = PT.map inl (allLeaf-out s w a γ x)
    br₁ (inr r) = PT.rec PT.squash₁ br₃ r

  clause₀ : ⟨ γ ⊨ allLeafAt s w a ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₀ x = ∣ inl x ∣₁
  clause₁ : ⟨ γ ⊨ SelMemLeaf.LeafAt s w a ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₁ x = ∣ inr ∣ inl x ∣₁ ∣₁
  clause₂ : ⟨ γ ⊨ SelEqLeaf.LeafAt s w a ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₂ x = ∣ inr ∣ inr ∣ inl x ∣₁ ∣₁ ∣₁
  clause₃ : ⟨ γ ⊨ selEqConLeafAt s w a ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₃ x = ∣ inr ∣ inr ∣ inr ∣ inl x ∣₁ ∣₁ ∣₁ ∣₁
  clause₄ : ⟨ γ ⊨ InterNode.NodeAt s w f ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₄ x = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl x ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  clause₅ : ⟨ γ ⊨ UnionNode.NodeAt s w f ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₅ x = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl x ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  clause₆ : ⟨ γ ⊨ complNodeAt s w f a ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₆ x = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl x ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  clause₇ : ⟨ γ ⊨ shiftNodeAt s w f ⟩ → ⟨ γ ⊨ ClauseAt s w f a ⟩
  clause₇ x = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr x ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
```

<!--en-->
## The values are the denotations
<!--zh-->
## 诸取值即诸指称
<!--/-->

<!--en-->
The recursion's uniqueness half, against an abstract step: any family whose
entries all satisfy the clause records, at any code, exactly the coded term's
denotation. One structural induction, no well-founded descent; the diagonal
cases read the clause's equations back through the code equations, with every
payload path split by pair injectivity and the arity paths feeding the
conditional facts; the fifty-six off-diagonal cases die by tag
discrimination, each a one-line arithmetic clash through the recorded law's
helpers.
<!--zh-->
递归的唯一性那一半，对着抽象的步：任何条目全部满足子句的族，在任何码处记录的恰是被编码项的指称。一次结构归纳，无须良基下降；对角情形把子句的等式沿码等式读回，每条载荷道路由对单射性拆开，元数道路喂给条件式事实；五十六个非对角情形死于标签判别，每个都是经在案定律辅助件的一行算术冲突。
<!--/-->

```agda
module Denote (A : V ℓ) (lA : ⟨ isL A ⟩) where
  private
    module C = Codes A lA

    neS : {a b : ℕ} → (a ≡ b → Empty.⊥) → suc a ≡ suc b → Empty.⊥
    neS ne q = ne (injSuc q)

    n1z n2z n3z n4z n5z n6z : {k : ℕ} → _
    n1z {k} = neS (znots {n = k})
    n2z {k} = neS (n1z {k})
    n3z {k} = neS (n2z {k})
    n4z {k} = neS (n3z {k})
    n5z {k} = neS (n4z {k})
    n6z {k} = neS (n5z {k})

    n1s n2s n3s n4s n5s n6s : {k : ℕ} → _
    n1s {k} = neS (snotz {n = k})
    n2s {k} = neS (n1s {k})
    n3s {k} = neS (n2s {k})
    n4s {k} = neS (n3s {k})
    n5s {k} = neS (n4s {k})
    n6s {k} = neS (n5s {k})

  approx-val : (F : V ℓ)
    → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ F ⟩
       → ∥ ClauseOf A F (fst x) (fst y) ∥₁)
    → {n : ℕ} (t : KT ⟪ A ⟫ n) (x y : S)
    → fst x ≡ C.code t
    → ⟨ pr (fst x) (fst y) ∈ F ⟩
    → fst y ≡ ⟦_⟧ᴷ A t
  approx-val F step = go
    where
    go : {n : ℕ} (t : KT ⟪ A ⟫ n) (x y : S) → fst x ≡ C.code t
       → ⟨ pr (fst x) (fst y) ∈ F ⟩ → fst y ≡ ⟦_⟧ᴷ A t
    use : {n : ℕ} (t : KT ⟪ A ⟫ n) (x y : S) → fst x ≡ C.code t
        → ClauseOf A F (fst x) (fst y) → fst y ≡ ⟦_⟧ᴷ A t

    go t x y qx e = PT.rec (setIsSet (fst y) (⟦_⟧ᴷ A t)) (use t x y qx)
      (step x y e)

    use {n} allK x y qx (inl (mv , (qs , cond))) =
      cond n (pr-inj (sym qs ∙ qx ∙ C.code-allK n) .snd)
    use {n} allK x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 0 snotz (sym qs ∙ qx ∙ C.code-allK n))
    use {n} allK x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 0 snotz (sym qs ∙ qx ∙ C.code-allK n))

    use {n} (selMemK i j) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 1 znots (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inl (mv , iv , jv , w' , (qs , (cond , qv))))) =
      qv ∙ (λ ι → selectMember (cond n (pr-inj pq .fst) ι)
                    ⁅ pr-inj (pr-inj pq .snd) .fst ι ⁆s
                    ⁅ pr-inj (pr-inj pq .snd) .snd ι ⁆s)
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-selMemK n i j) .snd
    use {n} (selMemK i j) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))
    use {n} (selMemK i j) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 1 n1s (sym qs ∙ qx ∙ C.code-selMemK n i j))

    use {n} (selEqK i j) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 2 znots (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 2 n1z (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , (cond , qv)))))) =
      qv ∙ (λ ι → selectEqual (cond n (pr-inj pq .fst) ι)
                    ⁅ pr-inj (pr-inj pq .snd) .fst ι ⁆s
                    ⁅ pr-inj (pr-inj pq .snd) .snd ι ⁆s)
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-selEqK n i j) .snd
    use {n} (selEqK i j) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 2 n2s (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 2 n2s (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 2 n2s (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 2 n2s (sym qs ∙ qx ∙ C.code-selEqK n i j))
    use {n} (selEqK i j) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 2 n2s (sym qs ∙ qx ∙ C.code-selEqK n i j))

    use {n} (selEqConK i a) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 3 znots (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 3 n1z (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 3 n2z (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , (cond , (qw₂ , qv)))))))) =
      qv ∙ (λ ι → shiftDown (selectEqual (pw₂ ι) ⁅ sucV (ivq ι) ⁆s ⁅ # 0 ⁆s))
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-selEqConK n i a) .snd
      ivq = pr-inj (pr-inj pq .snd) .fst
      cvq = pr-inj (pr-inj pq .snd) .snd
      pw₂ = qw₂ ∙ (λ ι → extendFamily (cond n (pr-inj pq .fst) ι) ⁅ cvq ι ⁆s)
    use {n} (selEqConK i a) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 3 n3s (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 3 n3s (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 3 n3s (sym qs ∙ qx ∙ C.code-selEqConK n i a))
    use {n} (selEqConK i a) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 3 n3s (sym qs ∙ qx ∙ C.code-selEqConK n i a))

    use (interK s t) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 4 znots (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 4 n1z (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 4 n2z (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 4 n3z (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (e1 , (e2 , (qs , qv))))))))) =
      qv ∙ (λ ι → _∩_ (go s cs ws (pr-inj pq .fst) e1 ι)
                      (go t ct wt (pr-inj pq .snd) e2 ι))
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-interK s t) .snd
    use (interK s t) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 4 n4s (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 4 n4s (sym qs ∙ qx ∙ C.code-interK s t))
    use (interK s t) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 4 n4s (sym qs ∙ qx ∙ C.code-interK s t))

    use (unionK s t) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 5 znots (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 5 n1z (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 5 n2z (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 5 n3z (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 5 n4z (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (e1 , (e2 , (qs , qv)))))))))) =
      qv ∙ (λ ι → _∪_ (go s cs ws (pr-inj pq .fst) e1 ι)
                      (go t ct wt (pr-inj pq .snd) e2 ι))
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-unionK s t) .snd
    use (unionK s t) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 5 n5s (sym qs ∙ qx ∙ C.code-unionK s t))
    use (unionK s t) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 5 n5s (sym qs ∙ qx ∙ C.code-unionK s t))

    use {n} (complK t) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 6 znots (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 6 n1z (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 6 n2z (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 6 n3z (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 6 n4z (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 6 n5z (sym qs ∙ qx ∙ C.code-complK t))
    use {n} (complK t) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (e2 , (qs , (cond , qv))))))))))) =
      qv ∙ (λ ι → _∖_ (cond n (pr-inj pq .fst) ι)
                      (go t ct wt (pr-inj pq .snd) e2 ι))
      where
      pq = pr-inj (sym qs ∙ qx ∙ C.code-complK t) .snd
    use {n} (complK t) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 7 6 n6s (sym qs ∙ qx ∙ C.code-complK t))

    use (shiftK t) x y qx (inl (mv , (qs , _))) =
      Empty.rec (tagNe 0 7 znots (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inl (mv , iv , jv , w' , (qs , _)))) =
      Empty.rec (tagNe 1 7 n1z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inl (mv , iv , jv , w' , (qs , _))))) =
      Empty.rec (tagNe 2 7 n2z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inr (inl (mv , iv , cv , w₁ , w₂ , (qs , _)))))) =
      Empty.rec (tagNe 3 7 n3z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _))))))))) =
      Empty.rec (tagNe 4 7 n4z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inr (inr (inr (inl (cs , ct , ws , wt , (_ , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 5 7 n5z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' , (_ , (qs , _)))))))))) =
      Empty.rec (tagNe 6 7 n6z (sym qs ∙ qx ∙ C.code-shiftK t))
    use (shiftK t) x y qx (inr (inr (inr (inr (inr (inr (inr (ct , wt , (e1 , (qs , qv)))))))))) =
      qv ∙ cong shiftDown
        (go t ct wt (pr-inj (sym qs ∙ qx ∙ C.code-shiftK t) .snd) e1)
```

<!--en-->
## The approximation, exhibited
<!--zh-->
## 逼近，被展示出来
<!--/-->

<!--en-->
The existence half. A term's approximation is the finite family of its
subterm entries, each entry the sealed pair of a code with its denotation and
an element of the model outright, the denotation's constructibility being the
bridge chapter's capstone. The family is a finite set over one stage found by
the family lemma, sealed at birth per the recorded law. Every entry then
satisfies its clause against the family itself: the constructor cases are the
clause's inward witnesses assembled from self-membership of the children, and
the child cases are the children's own clauses carried up by monotonicity,
which only ever touches the entry conjuncts.
<!--zh-->
存在性那一半。项的逼近是其子项条目的有穷族，每个条目是码与其指称的封印对、当下就是模型的元素，指称的可构造性正是桥梁章的封顶。族是家族引理找到的一个阶段上的有穷集合，按在案定律出生即封印。族的每个条目随后对着族自身满足其子句：构造子情形是子句的向内见证、由孩子的自身隶属组装，孩子情形是孩子自己的子句经单调性上抬，而单调性只碰条目合取。
<!--/-->

```agda
  entryS : SubK ⟪ A ⟫ → S
  entryS (m , t) = prʟ (C.codeS t) (⟦_⟧ᴷ A t , denoteL A lA t)

  entry : SubK ⟪ A ⟫ → V ℓ
  entry p = fst (entryS p)

  entry-eq : (p : SubK ⟪ A ⟫)
           → entry p ≡ pr (C.code (p .snd)) (⟦_⟧ᴷ A (p .snd))
  entry-eq (m , t) = prʟ-fst (C.codeS t) (⟦_⟧ᴷ A t , denoteL A lA t)

  private
    apxBnd : {n : ℕ} (T : KT ⟪ A ⟫ n)
           → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ
             × ((i : Fin (sizeK T)) → ⟨ entry (subK T i) ∈ Lset σ ⟩)) ∥₁
    apxBnd T = stageFam (sizeK T) (λ i → entry (subK T i))
      (λ i → entryS (subK T i) .snd)

  opaque
    apxS : {n : ℕ} → KT ⟪ A ⟫ n → S
    apxS T = finSet (sizeK T) (λ i → entry (subK T i)) , isl
      where
      isl : ⟨ isL (finSet (sizeK T) (λ i → entry (subK T i))) ⟩
      isl = PT.rec (snd (isL (finSet (sizeK T) (λ i → entry (subK T i)))))
        (λ { (σ , oσ , mem) →
          FinOf.finSetL σ oσ (sizeK T) (λ i → entry (subK T i)) mem })
        (apxBnd T)

    apx-in : {n : ℕ} (T : KT ⟪ A ⟫ n) (i : Fin (sizeK T))
           → ⟨ entry (subK T i) ∈ fst (apxS T) ⟩
    apx-in T i = finSet-in (sizeK T) (λ j → entry (subK T j))
      (entry (subK T i)) ∣ i , refl ∣₁

    apx-out : {n : ℕ} (T : KT ⟪ A ⟫ n) (z : V ℓ) → ⟨ z ∈ fst (apxS T) ⟩
            → ∥ Σ[ i ∈ Fin (sizeK T) ] (entry (subK T i) ≡ z) ∥₁
    apx-out T z = finSet-out (sizeK T) (λ j → entry (subK T j)) z


  entrySelf∈ : {n : ℕ} (t : KT ⟪ A ⟫ n)
             → ⟨ pr (C.code t) (⟦_⟧ᴷ A t) ∈ fst (apxS t) ⟩
  entrySelf∈ {n} t = subst (λ u → ⟨ u ∈ fst (apxS t) ⟩)
    ( entry-eq (subK t (selfIxK t))
    ∙ (λ ι → pr (C.code (sub-selfK t ι .snd)) (⟦_⟧ᴷ A (sub-selfK t ι .snd))) )
    (apx-in t (selfIxK t))
```

```agda
  private
    monoInterL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
               → ⟨ z ∈ fst (apxS s) ⟩ → ⟨ z ∈ fst (apxS (interK s t)) ⟩
    monoInterL s t z hz = PT.rec (snd (z ∈ fst (apxS (interK s t)))) named
      (apx-out s z hz)
      where
      named : Σ[ i ∈ Fin (sizeK s) ] (entry (subK s i) ≡ z)
            → ⟨ z ∈ fst (apxS (interK s t)) ⟩
      named (i , q) = subst (λ e → ⟨ e ∈ fst (apxS (interK s t)) ⟩)
        (cong entry (interIdxL s t i) ∙ q)
        (apx-in (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

    monoInterR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
               → ⟨ z ∈ fst (apxS t) ⟩ → ⟨ z ∈ fst (apxS (interK s t)) ⟩
    monoInterR s t z hz = PT.rec (snd (z ∈ fst (apxS (interK s t)))) named
      (apx-out t z hz)
      where
      named : Σ[ j ∈ Fin (sizeK t) ] (entry (subK t j) ≡ z)
            → ⟨ z ∈ fst (apxS (interK s t)) ⟩
      named (j , q) = subst (λ e → ⟨ e ∈ fst (apxS (interK s t)) ⟩)
        (cong entry (interIdxR s t j) ∙ q)
        (apx-in (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

    monoUnionL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
               → ⟨ z ∈ fst (apxS s) ⟩ → ⟨ z ∈ fst (apxS (unionK s t)) ⟩
    monoUnionL s t z hz = PT.rec (snd (z ∈ fst (apxS (unionK s t)))) named
      (apx-out s z hz)
      where
      named : Σ[ i ∈ Fin (sizeK s) ] (entry (subK s i) ≡ z)
            → ⟨ z ∈ fst (apxS (unionK s t)) ⟩
      named (i , q) = subst (λ e → ⟨ e ∈ fst (apxS (unionK s t)) ⟩)
        (cong entry (unionIdxL s t i) ∙ q)
        (apx-in (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

    monoUnionR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
               → ⟨ z ∈ fst (apxS t) ⟩ → ⟨ z ∈ fst (apxS (unionK s t)) ⟩
    monoUnionR s t z hz = PT.rec (snd (z ∈ fst (apxS (unionK s t)))) named
      (apx-out t z hz)
      where
      named : Σ[ j ∈ Fin (sizeK t) ] (entry (subK t j) ≡ z)
            → ⟨ z ∈ fst (apxS (unionK s t)) ⟩
      named (j , q) = subst (λ e → ⟨ e ∈ fst (apxS (unionK s t)) ⟩)
        (cong entry (unionIdxR s t j) ∙ q)
        (apx-in (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

    monoCompl : {n : ℕ} (t : KT ⟪ A ⟫ n) (z : V ℓ)
              → ⟨ z ∈ fst (apxS t) ⟩ → ⟨ z ∈ fst (apxS (complK t)) ⟩
    monoCompl t z hz = PT.rec (snd (z ∈ fst (apxS (complK t)))) named
      (apx-out t z hz)
      where
      named : Σ[ i ∈ Fin (sizeK t) ] (entry (subK t i) ≡ z)
            → ⟨ z ∈ fst (apxS (complK t)) ⟩
      named (i , q) = subst (λ e → ⟨ e ∈ fst (apxS (complK t)) ⟩) q
        (apx-in (complK t) (suc i))

    monoShift : {n : ℕ} (t : KT ⟪ A ⟫ (suc n)) (z : V ℓ)
              → ⟨ z ∈ fst (apxS t) ⟩ → ⟨ z ∈ fst (apxS (shiftK t)) ⟩
    monoShift t z hz = PT.rec (snd (z ∈ fst (apxS (shiftK t)))) named
      (apx-out t z hz)
      where
      named : Σ[ i ∈ Fin (sizeK t) ] (entry (subK t i) ≡ z)
            → ⟨ z ∈ fst (apxS (shiftK t)) ⟩
      named (i , q) = subst (λ e → ⟨ e ∈ fst (apxS (shiftK t)) ⟩) q
        (apx-in (shiftK t) (suc i))

  clause-mono : (F F' : V ℓ) → ((z : V ℓ) → ⟨ z ∈ F ⟩ → ⟨ z ∈ F' ⟩)
              → {x v : V ℓ} → ClauseOf A F x v → ClauseOf A F' x v
  clause-mono F F' up (inl c) = inl c
  clause-mono F F' up (inr (inl c)) = inr (inl c)
  clause-mono F F' up (inr (inr (inl c))) = inr (inr (inl c))
  clause-mono F F' up (inr (inr (inr (inl c)))) = inr (inr (inr (inl c)))
  clause-mono F F' up (inr (inr (inr (inr (inl
    (cs , ct , ws , wt , (e1 , (e2 , rest)))))))) =
    inr (inr (inr (inr (inl (cs , ct , ws , wt ,
      ( up (pr (fst cs) (fst ws)) e1
      , (up (pr (fst ct) (fst wt)) e2 , rest) ))))))
  clause-mono F F' up (inr (inr (inr (inr (inr (inl
    (cs , ct , ws , wt , (e1 , (e2 , rest))))))))) =
    inr (inr (inr (inr (inr (inl (cs , ct , ws , wt ,
      ( up (pr (fst cs) (fst ws)) e1
      , (up (pr (fst ct) (fst wt)) e2 , rest) )))))))
  clause-mono F F' up (inr (inr (inr (inr (inr (inr (inl
    (mv , ct , wt , w' , (e2 , rest))))))))) =
    inr (inr (inr (inr (inr (inr (inl (mv , ct , wt , w' ,
      ( up (pr (fst ct) (fst wt)) e2 , rest ))))))))
  clause-mono F F' up (inr (inr (inr (inr (inr (inr (inr
    (ct , wt , (e1 , rest))))))))) =
    inr (inr (inr (inr (inr (inr (inr (ct , wt ,
      ( up (pr (fst ct) (fst wt)) e1 , rest ))))))))

  apx-clauseOf : {n : ℕ} (T : KT ⟪ A ⟫ n) (i : Fin (sizeK T))
               → ClauseOf A (fst (apxS T))
                   (C.code (subK T i .snd)) (⟦_⟧ᴷ A (subK T i .snd))
  apx-clauseOf {n} allK i =
    inl ((# n , numL n)
      , (C.code-allK n , λ m qm → cong (allTuples A) (#-inj′ qm)))
  apx-clauseOf {n} (selMemK i' j') i =
    inr (inl ((# n , numL n) , (# (toℕ i') , numL (toℕ i'))
      , (# (toℕ j') , numL (toℕ j'))
      , (allTuples A n , allTuplesL A lA n)
      , (C.code-selMemK n i' j'
        , ((λ m qm → cong (allTuples A) (#-inj′ qm)) , refl))))
  apx-clauseOf {n} (selEqK i' j') i =
    inr (inr (inl ((# n , numL n) , (# (toℕ i') , numL (toℕ i'))
      , (# (toℕ j') , numL (toℕ j'))
      , (allTuples A n , allTuplesL A lA n)
      , (C.code-selEqK n i' j'
        , ((λ m qm → cong (allTuples A) (#-inj′ qm)) , refl)))))
  apx-clauseOf {n} (selEqConK i' a') i =
    inr (inr (inr (inl ((# n , numL n) , (# (toℕ i') , numL (toℕ i'))
      , C.paramS a'
      , (allTuples A n , allTuplesL A lA n)
      , ( extendFamily (allTuples A n) ⁅ ⟪ A ⟫↪ a' ⁆s
        , extendFamilyL {X = allTuples A n} {Y = ⁅ ⟪ A ⟫↪ a' ⁆s}
            (allTuplesL A lA n) (sglL (C.paramS a' .snd)) )
      , (C.code-selEqConK n i' a'
        , ((λ m qm → cong (allTuples A) (#-inj′ qm)) , (refl , refl)))))))
  apx-clauseOf (interK s t) zero =
    inr (inr (inr (inr (inl (C.codeS s , C.codeS t
      , (⟦_⟧ᴷ A s , denoteL A lA s) , (⟦_⟧ᴷ A t , denoteL A lA t)
      , ( monoInterL s t (pr (C.code s) (⟦_⟧ᴷ A s)) (entrySelf∈ s)
        , ( monoInterR s t (pr (C.code t) (⟦_⟧ᴷ A t)) (entrySelf∈ t)
          , (C.code-interK s t , refl) ) ))))))
  apx-clauseOf (interK s t) (suc k) =
    goSplit (FinSumChar.inv (sizeK s) (sizeK t) k)
    where
    goSplit : (v : Fin (sizeK s) ⊎ Fin (sizeK t))
            → ClauseOf A (fst (apxS (interK s t)))
                (C.code (subSplitK s t v .snd)) (⟦_⟧ᴷ A (subSplitK s t v .snd))
    goSplit (inl i) = clause-mono (fst (apxS s)) (fst (apxS (interK s t)))
      (monoInterL s t) (apx-clauseOf s i)
    goSplit (inr j) = clause-mono (fst (apxS t)) (fst (apxS (interK s t)))
      (monoInterR s t) (apx-clauseOf t j)
  apx-clauseOf (unionK s t) zero =
    inr (inr (inr (inr (inr (inl (C.codeS s , C.codeS t
      , (⟦_⟧ᴷ A s , denoteL A lA s) , (⟦_⟧ᴷ A t , denoteL A lA t)
      , ( monoUnionL s t (pr (C.code s) (⟦_⟧ᴷ A s)) (entrySelf∈ s)
        , ( monoUnionR s t (pr (C.code t) (⟦_⟧ᴷ A t)) (entrySelf∈ t)
          , (C.code-unionK s t , refl) ) )))))))
  apx-clauseOf (unionK s t) (suc k) =
    goSplit (FinSumChar.inv (sizeK s) (sizeK t) k)
    where
    goSplit : (v : Fin (sizeK s) ⊎ Fin (sizeK t))
            → ClauseOf A (fst (apxS (unionK s t)))
                (C.code (subSplitK s t v .snd)) (⟦_⟧ᴷ A (subSplitK s t v .snd))
    goSplit (inl i) = clause-mono (fst (apxS s)) (fst (apxS (unionK s t)))
      (monoUnionL s t) (apx-clauseOf s i)
    goSplit (inr j) = clause-mono (fst (apxS t)) (fst (apxS (unionK s t)))
      (monoUnionR s t) (apx-clauseOf t j)
  apx-clauseOf {n} (complK t) zero =
    inr (inr (inr (inr (inr (inr (inl ((# n , numL n) , C.codeS t
      , (⟦_⟧ᴷ A t , denoteL A lA t)
      , (allTuples A n , allTuplesL A lA n)
      , ( monoCompl t (pr (C.code t) (⟦_⟧ᴷ A t)) (entrySelf∈ t)
        , (C.code-complK t
          , ((λ m qm → cong (allTuples A) (#-inj′ qm)) , refl)) ))))))))
  apx-clauseOf (complK t) (suc k) =
    clause-mono (fst (apxS t)) (fst (apxS (complK t)))
      (monoCompl t) (apx-clauseOf t k)
  apx-clauseOf (shiftK t) zero =
    inr (inr (inr (inr (inr (inr (inr (C.codeS t
      , (⟦_⟧ᴷ A t , denoteL A lA t)
      , ( monoShift t (pr (C.code t) (⟦_⟧ᴷ A t)) (entrySelf∈ t)
        , (C.code-shiftK t , refl) ))))))))
  apx-clauseOf (shiftK t) (suc k) =
    clause-mono (fst (apxS t)) (fst (apxS (shiftK t)))
      (monoShift t) (apx-clauseOf t k)
```
