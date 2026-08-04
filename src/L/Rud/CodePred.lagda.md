# The code predicate, read inside a level

<!--en-->
The code set chapter ended with a named gap: a formula of the object
language whose definable set is the set of codes. This chapter writes that
formula and proves it adequate in both directions, which turns the gap into a
theorem and hands the satisfaction engine everything it needs.

The formula says what a first-order formula can say about a code: not "this set
is a code", which is a statement about an unbounded recursion, but "some set
witnesses that this set is a code". The witness is a set of keys, a key being an
arity paired with a code, closed downwards under the parts a constructor names
and containing nothing that is not such a key. Twelve clauses, one per
constructor, say both things at once, and the existential over the witness is
the only place where the recursion is hidden.

Everything is read in the **inner** world of the level. The definable power
accepts any formula at all, so no clause has to be bounded, no absoluteness
argument is spent, and the quantifier over the witness set ranges over the level
itself. That is the whole reason this chapter is short where the same predicate
over the constructible tower was long.

The two directions are not symmetric. From a witness to a formula is a recursion
on the rank of the code, since a Kuratowski pair puts a part four membership
steps below the whole; from a formula to a witness is a construction, the finite
set of keys of the subformulas, and its well-formedness is one induction. Both
end at the same place: the codes of the arity-k formulas over a carrier are
exactly the definable subset the formula carves, so the code set is a member of
the level above.
<!--zh-->
码集那一章以一处具名的缺口收尾：对象语言的一条公式，其可定义集就是诸码之集。本章写出那条公式，并证其双向适足，于是缺口变成定理，而满足集引擎所需的一切都已备齐。

那条公式说的是一阶公式能对码说的话：不是「这个集合是一个码」，那是关于一场无界递归的陈述，而是「有某个集合见证这个集合是一个码」。见证是一个键之集，而键是元数与码配成的对；该集向下对构造子所点名的诸部件封闭，且不含任何不是这种键的东西。十二条子句，每个构造子一条，一次把两件事都说出来，而对见证集的存在量化是递归唯一的藏身之处。

一切都在该层的**内层**世界中读出。可定义幂接纳任意公式，故没有哪条子句必须有界，绝对性的论证一分不花，而对见证集的量词遍历该层自身。这正是本章短、而可构造塔之上同一条谓词长的全部理由。

两个方向并不对称。从见证到公式是一场跑在码的秩上的递归，因为 Kuratowski 对把一个部件放在整体之下四个成员步之处；从公式到见证则是一次构造，即诸子公式之键所成的有限集，其良构性是一次归纳。两者终点相同：某载体之上诸 k 元公式的码，恰是该公式刻出的那个可定义子集，故码集是其上那一层的成员。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.CodePred {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; module VCode )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-ord )
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import L.Rud.Ops {ℓ} using ( F0-spec; F5-spec )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f5; Fof; Fof-f0; Fof-f5; singl≡pair
        ; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.CodeSet {ℓ} lem A
  using ( module Codes; module InLevel; module Carrier )
open import L.Rud.StepInL {ℓ} lem A using ( module Reads; module Desc )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId'; toℕ<n )
open import Cubical.Data.Nat.Order using ( _<_; <-split; ¬-<-zero )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; _∪_; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## A sealed vocabulary of shapes
<!--zh-->
## 一套封好的形状词汇
<!--/-->

<!--en-->
Before anything is said about codes, five constructions are given names of their
own and sealed: the Kuratowski pair, the numerals, the successor, the singleton
and the binary union. They are the same constructions as before and the seal
proves it, one equation each.

The seal is not caution about size, and it is not optional. Every statement
below is an equation or a membership whose two sides mention a pair inside a
pair inside a pair. Unsealed, each such comparison unfolds both sides into
nested braces and the typechecker does not finish; sealed, the comparison stops
at the name and descends argument by argument. Measured here: the same
three-quantifier frame that does not check in three minutes with the library's
pair checks in two seconds with this one. It is the same seal, and the same
reason, that the rank chapter records.
<!--zh-->
在对码说任何话之前，先给五样构造各起一个自己的名字并封印：Kuratowski 对、诸数码、后继、单点集与二元并。它们与原先是同样的构造，而封印各用一条等式把这一点证出来。

封印不是对尺寸的谨慎，也不是可选项。以下每条陈述都是一条等式或一条隶属，其两侧都提到「对里的对里的对」。不封印，每一次这样的比较都会把两侧展开成嵌套的花括号，类型检查器跑不完；封印之后，比较停在那个名字处，再逐个实参下降。此处实测：同一个三层量词的框架，用库里的对三分钟查不完，用这一个两秒查完。这与秩那一章所记的是同一道封印、同一个理由。
<!--/-->

```agda
opaque
  prS : S → S → S
  prS a b = pr a b

  numS : ℕ → S
  numS k = # k

  sucS : S → S
  sucS x = sucV x

  sglS : S → S
  sglS a = ⁅ a ⁆s

  cupS : S → S → S
  cupS a b = a ∪ b

  prS-pr : (a b : S) → prS a b ≡ pr a b
  prS-pr a b = refl

  numS-# : (k : ℕ) → numS k ≡ (# k)
  numS-# k = refl

  sucS-sucV : (x : S) → sucS x ≡ sucV x
  sucS-sucV x = refl

  sglS-sgl : (a : S) → sglS a ≡ ⁅ a ⁆s
  sglS-sgl a = refl

  cupS-cup : (a b : S) → cupS a b ≡ (a ∪ b)
  cupS-cup a b = refl

  numS-suc : (k : ℕ) → numS (suc k) ≡ sucS (numS k)
  numS-suc k = refl

  prS-inj : {a b c d : S} → prS a b ≡ prS c d → (a ≡ c) × (b ≡ d)
  prS-inj = pr-inj
```

<!--en-->
## Rank descends into a code
<!--zh-->
## 秩下降进一条码
<!--/-->

<!--en-->
A recursion over codes cannot run on membership: a Kuratowski pair holds its
parts four steps down, and the sets in between are not codes. Rank does run,
because it grows strictly along membership and ordinals compose four steps into
one. Three descents are all that is needed, since a tagged code is a pair whose
payload is either a code or a pair of two, and the tag is never entered.

The lemmas are stated at variable sets through the sealed pair and applied once,
so that no proof below unfolds a nested brace expression.
<!--zh-->
一场跑在码上的递归不能跑在成员关系上：Kuratowski 对把它的诸部件放在四步之下，而中间那些集合不是码。秩则跑得动，因为它沿成员关系严格增长，而序数把四步合成一步。所需的下降只有三条，因为一条带标签的码是一个对，其载荷要么是一条码、要么是两条码所成的对，而标签从不被进入。

诸引理经封好的对、在变元集合上陈述并施用一次，故下方没有任何证明会展开嵌套的花括号表达式。
<!--/-->

```agda
private
  pair∈ : (u v w : S) → ∥ (w ≡ u) ⊎ (w ≡ v) ∥₁ → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
  pair∈ u v w h = F0-spec u v w .snd h

  self∈sgl : (a : S) → ⟨ a ∈ˢ ⁅ a ⁆s ⟩
  self∈sgl a = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym (singl≡pair a))
    (pair∈ a a a ∣ inl refl ∣₁)

  trans≺ : (x y z : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank y ∈ˢ rank z ⟩
         → ⟨ rank x ∈ˢ rank z ⟩
  trans≺ x y z x∈y ry∈rz = rank-ord z .fst (rank-mono x y x∈y) ry∈rz

  chain4 : (x y z w v : S) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ z ⟩ → ⟨ z ∈ˢ w ⟩ → ⟨ w ∈ˢ v ⟩
         → ⟨ rank x ∈ˢ rank v ⟩
  chain4 x y z w v x∈y y∈z z∈w w∈v =
    trans≺ x y v x∈y (trans≺ y z v y∈z (trans≺ z w v z∈w (rank-mono w v w∈v)))

opaque
  unfolding prS

  payload≺ : (c z : S) → ⟨ rank z ∈ˢ rank (prS c z) ⟩
  payload≺ c z = trans≺ z ⁅ c , z ⁆ (pr c z)
    (pair∈ c z z ∣ inr refl ∣₁)
    (rank-mono ⁅ c , z ⁆ (pr c z)
      (pair∈ ⁅ c ⁆s ⁅ c , z ⁆ ⁅ c , z ⁆ ∣ inr refl ∣₁))

  leftPart : (c a b : S) → ⟨ rank a ∈ˢ rank (prS c (prS a b)) ⟩
  leftPart c a b = chain4 a ⁅ a ⁆s (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
    (self∈sgl a)
    (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s ∣ inl refl ∣₁)
    (pair∈ c (pr a b) (pr a b) ∣ inr refl ∣₁)
    (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ ∣ inr refl ∣₁)

  rightPart : (c a b : S) → ⟨ rank b ∈ˢ rank (prS c (prS a b)) ⟩
  rightPart c a b = chain4 b ⁅ a , b ⁆ (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
    (pair∈ a b b ∣ inr refl ∣₁)
    (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ ∣ inr refl ∣₁)
    (pair∈ c (pr a b) (pr a b) ∣ inr refl ∣₁)
    (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ ∣ inr refl ∣₁)
```

<!--en-->
## The level, as a telescope
<!--zh-->
## 层，作为一条望远镜
<!--/-->

<!--en-->
Nothing below mentions the tower. What the predicate needs of the level it is
written over is exactly seven facts: transitivity, that the carrier is a member,
and that the level is closed under the sealed pair, the numerals, the singleton
and the binary union, and holds the empty set. Every one of them is one
application of the sealed operation family at a limit index, and they are
discharged once, at the end, inside a single block.

Writing the chapter at the telescope rather than at a stage is what keeps a
concrete level out of every type below, which is the standing rule for a
construction this size.
<!--zh-->
以下没有任何东西提到那座塔。谓词对它所写在其上的那一层的要求，恰是七条事实：传递性、载体是成员，以及该层对封好的对、诸数码、单点集与二元并封闭，并持有空集。它们每一条都是封好的运算族在极限索引处的一次施用，而它们只在末尾、于单一一个块内交付一次。

把本章写在望远镜上、而不写在某个阶段上，正是使具体的层不出现在下方每个类型里的那件事，而这是这种规模的构造的常设规矩。
<!--/-->

```agda
module Pred (W : S) (Wtr : Transitive 𝒮ᵥ (λ x → x ∈ˢ W))
            (C : S) (C∈ : ⟨ C ∈ˢ W ⟩)
            (prIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ prS a b ∈ˢ W ⟩)
            (numIn : (k : ℕ) → ⟨ numS k ∈ˢ W ⟩)
            (sglIn : (a : S) → ⟨ a ∈ˢ W ⟩ → ⟨ sglS a ∈ˢ W ⟩)
            (cupIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ cupS a b ∈ˢ W ⟩)
            (∅∈W : ⟨ ∅ ∈ˢ W ⟩)
            (codeIn : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ Codes.code C φ ∈ˢ W ⟩)
            where

  open Reads W Wtr using ( mem; prL∈; prR∈ )
  open Desc W Wtr
  open DefC using ( SM; _⊨ᵐ_; defSet )
  open Codes C using ( ι; codeTm; code; codeSet; codeSet-out; code∈codeSet )

  private
    v0 : {n : ℕ} → Fin (suc n)
    v0 = zero
    v1 : {n : ℕ} → Fin (suc (suc n))
    v1 = suc v0
    v2 : {n : ℕ} → Fin (suc (suc (suc n)))
    v2 = suc v1
    v3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    v3 = suc v2
    v4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
    v4 = suc v3
    v5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
    v5 = suc v4
    v6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
    v6 = suc v5

  keyOf : ℕ → S → S
  keyOf n x = prS (numS n) x

  binKey : ℕ → S → S → S → S
  binKey t N a b = prS N (prS (numS t) (prS a b))

  unKey : ℕ → S → S → S
  unKey t N a = prS N (prS (numS t) a)

  mC : ⟪ W ⟫
  mC = ∈-asFiber {a = C} {b = W} C∈ .fst

  qC : ⟪ W ⟫↪ mC ≡ C
  qC = ∈-asFiber {a = C} {b = W} C∈ .snd

  nm : ℕ → ⟪ W ⟫
  nm k = ∈-asFiber {a = numS k} {b = W} (numIn k) .fst

  qnm : (k : ℕ) → ⟪ W ⟫↪ (nm k) ≡ numS k
  qnm k = ∈-asFiber {a = numS k} {b = W} (numIn k) .snd

  opaque
    unfolding prS

    prSIn : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ pr a b ∈ˢ W ⟩
    prSIn = prIn

    prParts : (p q : S) → ⟨ prS p q ∈ˢ W ⟩ → ⟨ p ∈ˢ W ⟩ × ⟨ q ∈ˢ W ⟩
    prParts p q h = prL∈ p q h , prR∈ p q h

    prAtS-out : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ prAt q u v ⟩
              → fst (lookup q δ) ≡ prS (fst (lookup u δ)) (fst (lookup v δ))
    prAtS-out = prAt-out

    prAtS-in : {n : ℕ} (q u v : Fin n) (δ : Vec SM n)
             → fst (lookup q δ) ≡ prS (fst (lookup u δ)) (fst (lookup v δ))
             → ⟨ δ ⊨ᵐ prAt q u v ⟩
    prAtS-in = prAt-in
```

<!--en-->
## Tagged pairs, at variables and at a constant tag
<!--zh-->
## 带标签的对，在变元上、标签取常量
<!--/-->

<!--en-->
Every shape a code takes is a Kuratowski pair whose first component is a
numeral, and the level's pair reader is already delivered at variables. What is
missing is the constant tag, and it is cheaper to bind a fresh variable and pin
it to the numeral than to write a second reader: the pinning is one atomic
equation and the reader is reused unchanged.

Two assembled readers follow, for the two payload shapes. Reading them once,
generically in the tag and the positions, is what keeps the twelve clauses from
each unfolding a formula three quantifiers deep.
<!--zh-->
码所取的每一种形状都是第一分量为数码的 Kuratowski 对，而该层的对读式在变元上已然交付。缺的是那个常量标签，而绑一个新变元、把它钉到那个数码上，比再写一条读式更便宜：钉的动作是一条原子等式，而读式原样复用。

随后是两条组装好的读式，对应两种载荷形状。把它们各读一次、且对标签与诸位置泛型，正是使那十二条子句不必各自展开一条嵌套三层量词的公式的那件事。
<!--/-->

```agda
  tagPr : {n : ℕ} → Fin n → ℕ → Fin n → Formula ⟪ W ⟫ n
  tagPr q t x = ∃̇ ((var v0 ≐ con (nm t)) ∧̇ prAt (suc q) v0 (suc x))

  tagPr-out : {n : ℕ} (q : Fin n) (t : ℕ) (x : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ tagPr q t x ⟩
            → fst (lookup q δ) ≡ prS (numS t) (fst (lookup x δ))
  tagPr-out q t x δ = PT.rec (setIsSet _ _)
    (λ { (ym , (e , h)) →
      prAtS-out (suc q) v0 (suc x) (ym ∷ δ) h
      ∙ cong (λ u → prS u (fst (lookup x δ))) (e ∙ qnm t) })

  tagPr-in : {n : ℕ} (q : Fin n) (t : ℕ) (x : Fin n) (δ : Vec SM n)
           → fst (lookup q δ) ≡ prS (numS t) (fst (lookup x δ))
           → ⟨ δ ⊨ᵐ tagPr q t x ⟩
  tagPr-in q t x δ e =
    ∣ pt (numS t) (numIn t)
    , (sym (qnm t)
      , prAtS-in (suc q) v0 (suc x) (pt (numS t) (numIn t) ∷ δ) e) ∣₁

  keyPairAt : {n : ℕ} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula ⟪ W ⟫ n
  keyPairAt w N t a b =
    ∃̇ (∃̇ ( prAt v1 (suc (suc a)) (suc (suc b))
          ∧̇ (tagPr v0 t v1
          ∧̇ prAt (suc (suc w)) (suc (suc N)) v0) ))

  keyPairAt-out : {n : ℕ} (w N : Fin n) (t : ℕ) (a b : Fin n) (δ : Vec SM n)
                → ⟨ δ ⊨ᵐ keyPairAt w N t a b ⟩
                → fst (lookup w δ)
                  ≡ binKey t (fst (lookup N δ)) (fst (lookup a δ))
                             (fst (lookup b δ))
  keyPairAt-out w N t a b δ = PT.rec (setIsSet _ _)
    (λ { (pm , hp) → PT.rec (setIsSet _ _)
      (λ { (qm , (e₁ , (e₂ , e₃))) →
        prAtS-out (suc (suc w)) (suc (suc N)) v0 (qm ∷ pm ∷ δ) e₃
        ∙ cong (prS (fst (lookup N δ)))
            (tagPr-out v0 t v1 (qm ∷ pm ∷ δ) e₂
             ∙ cong (prS (numS t)) (prAtS-out v1 (suc (suc a)) (suc (suc b))
                                      (qm ∷ pm ∷ δ) e₁)) })
      hp })

  keyPairAt-in : {n : ℕ} (w N : Fin n) (t : ℕ) (a b : Fin n) (δ : Vec SM n)
               → fst (lookup w δ)
                 ≡ binKey t (fst (lookup N δ)) (fst (lookup a δ))
                            (fst (lookup b δ))
               → ⟨ δ ⊨ᵐ keyPairAt w N t a b ⟩
  keyPairAt-in w N t a b δ e =
    ∣ pm
    , ∣ qm
      , ( prAtS-in v1 (suc (suc a)) (suc (suc b)) (qm ∷ pm ∷ δ) refl
        , ( tagPr-in v0 t v1 (qm ∷ pm ∷ δ) refl
          , prAtS-in (suc (suc w)) (suc (suc N)) v0 (qm ∷ pm ∷ δ) e ) ) ∣₁ ∣₁
    where
    pm : SM
    pm = pt (prS (fst (lookup a δ)) (fst (lookup b δ)))
            (prIn _ _ (snd (lookup a δ)) (snd (lookup b δ)))
    qm : SM
    qm = pt (prS (numS t) (fst pm)) (prIn _ _ (numIn t) (snd pm))

  keyUnAt : {n : ℕ} → Fin n → Fin n → ℕ → Fin n → Formula ⟪ W ⟫ n
  keyUnAt w N t a = ∃̇ ( tagPr v0 t (suc a) ∧̇ prAt (suc w) (suc N) v0 )

  keyUnAt-out : {n : ℕ} (w N : Fin n) (t : ℕ) (a : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ keyUnAt w N t a ⟩
              → fst (lookup w δ) ≡ unKey t (fst (lookup N δ)) (fst (lookup a δ))
  keyUnAt-out w N t a δ = PT.rec (setIsSet _ _)
    (λ { (qm , (e₁ , e₂)) →
      prAtS-out (suc w) (suc N) v0 (qm ∷ δ) e₂
      ∙ cong (prS (fst (lookup N δ))) (tagPr-out v0 t (suc a) (qm ∷ δ) e₁) })

  keyUnAt-in : {n : ℕ} (w N : Fin n) (t : ℕ) (a : Fin n) (δ : Vec SM n)
             → fst (lookup w δ) ≡ unKey t (fst (lookup N δ)) (fst (lookup a δ))
             → ⟨ δ ⊨ᵐ keyUnAt w N t a ⟩
  keyUnAt-in w N t a δ e =
    ∣ qm
    , ( tagPr-in v0 t (suc a) (qm ∷ δ) refl
      , prAtS-in (suc w) (suc N) v0 (qm ∷ δ) e ) ∣₁
    where
    qm : SM
    qm = pt (prS (numS t) (fst (lookup a δ)))
            (prIn _ _ (numIn t) (snd (lookup a δ)))
```

<!--en-->
## The two frames
<!--zh-->
## 两个框架
<!--/-->

<!--en-->
Twelve tags, two payload shapes: a pair of parts, or a single part. Each frame
binds the arity and the parts, reads the key's nested shape once through the
readers above, and hands the rest to a relation it is generic in. Discharging
the shape here, with the tag, the relation and the environment all still
variables, is the difference between a second and an afternoon.

Every branch of every elimination below is given a written type of its own.
That is not a matter of taste either: a branch whose type is inferred is solved
against the whole target, and the target here is an equation between iterated
pairs. Measured in this chapter: the same frame does not finish in three minutes
with the branch inferred and checks in two seconds with the branch written. It
is the rule the constructibility chapters recorded, and it decides this chapter
line by line.
<!--zh-->
十二个标签，两种载荷形状：两个部件所成的对，或单个部件。每个框架绑住元数与诸部件，经上面的读式把键的嵌套形状读一次，再把其余交给它对之泛型的一条关系。在此处、且在标签、关系与环境都还是变元时交付那个形状，正是一秒与一下午的差别。

以下每次消去的每一支都各给一个写出来的类型。这也不是趣味问题：类型靠推断的分支是对着整个目标求解的，而此处的目标是迭代对之间的等式。本章实测：同一个框架，分支类型靠推断三分钟跑不完，分支类型写出来两秒查完。这正是可构造性诸章所记的那条规矩，而它逐行决定本章。
<!--/-->

```agda
  unForm : ℕ → Formula ⟪ W ⟫ 6 → Formula ⟪ W ⟫ 4
  unForm t rel = ∃̇ (∃̇ ( keyUnAt v2 v1 t v0 ∧̇ rel ))

  UnWit : ℕ → Formula ⟪ W ⟫ 6 → Vec SM 3 → SM → Type (ℓ-suc ℓ)
  UnWit t rel δ w = Σ[ N ∈ SM ] Σ[ a ∈ SM ]
    ((fst w ≡ unKey t (fst N) (fst a)) × ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ rel ⟩)

  unForm-out : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
             → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩ → ∥ UnWit t rel δ w ∥₁
  unForm-out t rel δ w h = PT.rec squash₁ (λ { (N , hN) → PT.map (mk N) hN }) h
    where
    mk : (N : SM)
       → Σ[ a ∈ SM ] ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ (keyUnAt v2 v1 t v0 ∧̇ rel) ⟩
       → UnWit t rel δ w
    mk N (a , (hk , hr)) =
      N , a , ( keyUnAt-out v2 v1 t v0 (a ∷ N ∷ w ∷ δ) hk , hr )
```

```agda
  binForm : ℕ → Formula ⟪ W ⟫ 7 → Formula ⟪ W ⟫ 4
  binForm t rel = ∃̇ (∃̇ (∃̇ ( keyPairAt v3 v2 t v1 v0 ∧̇ rel )))

  BinWit : ℕ → Formula ⟪ W ⟫ 7 → Vec SM 3 → SM → Type (ℓ-suc ℓ)
  BinWit t rel δ w = Σ[ N ∈ SM ] Σ[ a ∈ SM ] Σ[ b ∈ SM ]
    ((fst w ≡ binKey t (fst N) (fst a) (fst b))
     × ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ rel ⟩)

  binForm-out : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
              → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩ → ∥ BinWit t rel δ w ∥₁
  binForm-out t rel δ w h =
    PT.rec squash₁ (λ { (N , hN) → PT.rec squash₁ (mk₂ N) hN }) h
    where
    mk₃ : (N a : SM)
        → Σ[ b ∈ SM ] ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ (keyPairAt v3 v2 t v1 v0 ∧̇ rel) ⟩
        → BinWit t rel δ w
    mk₃ N a (b , (hk , hr)) =
      N , a , b , ( keyPairAt-out v3 v2 t v1 v0 (b ∷ a ∷ N ∷ w ∷ δ) hk , hr )
    mk₂ : (N : SM)
        → Σ[ a ∈ SM ] ⟨ (a ∷ N ∷ w ∷ δ)
                        ⊨ᵐ (∃̇ (keyPairAt v3 v2 t v1 v0 ∧̇ rel)) ⟩
        → ∥ BinWit t rel δ w ∥₁
    mk₂ N (a , ha) = PT.map (mk₃ N a) ha

  binForm-in : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
             → BinWit t rel δ w → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩
  binForm-in t rel δ w (N , a , b , (e , hr)) =
    ∣ N , ∣ a , ∣ b
      , ( keyPairAt-in v3 v2 t v1 v0 (b ∷ a ∷ N ∷ w ∷ δ) e , hr ) ∣₁ ∣₁ ∣₁

  unForm-in : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
            → UnWit t rel δ w → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩
  unForm-in t rel δ w (N , a , (e , hr)) =
    ∣ N , ∣ a , ( keyUnAt-in v2 v1 t v0 (a ∷ N ∷ w ∷ δ) e , hr ) ∣₁ ∣₁
```

<!--en-->
## Terms, subkeys, and the next arity
<!--zh-->
## 词项、子键与下一个元数
<!--/-->

<!--en-->
Three clauses recur inside the twelve, and each is written once. A term code is
a constant or a variable: the constant's payload is a member of the carrier, and
the variable's payload is a member of the arity, which is what makes the code a
code **at that arity** rather than at a larger one. A subkey is the arity paired
with a part, asked to be a member of the witness set. And the next arity is the
successor of a set, described by the level's own equality frame, since a
quantifier's subformula lives one arity up.

None of the three is bounded and none of them needs to be. The reading is inside
the level throughout, so an unbounded quantifier is a quantifier over the level,
and that is exactly the range the witnesses live in.
<!--zh-->
十二条之内反复出现的有三条子句，每条只写一次。词项码要么是常元、要么是变元：常元的载荷是载体的成员，变元的载荷是元数的成员，正是后者使那条码成为**在该元数上的**码、而非在某个更大的元数上。子键是元数与某个部件配成的对，被要求是见证集的成员。而下一个元数是某个集合的后继，用该层自己的等词框架描述，因为量词的子公式住在高一级的元数上。

三条都不是有界的，也都不必是。整个读法都在该层之内，故无界量词就是对该层的量词，而那恰是诸见证所居之处。
<!--/-->

```agda
  IsTm : S → S → Type (ℓ-suc ℓ)
  IsTm N t = ∥ (Σ[ y ∈ S ] ((t ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
             ⊎ (Σ[ y ∈ S ] ((t ≡ prS (numS 1) y) × ⟨ y ∈ˢ N ⟩)) ∥₁

  isTm : {n : ℕ} → Fin n → Fin n → Formula ⟪ W ⟫ n
  isTm t N = ∃̇ ( tagPr (suc t) 0 v0 ∧̇ (var v0 ∈̇ con mC) )
          ∨̇ ∃̇ ( tagPr (suc t) 1 v0 ∧̇ (var v0 ∈̇ var (suc N)) )

  isTm-out : {n : ℕ} (t N : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ isTm t N ⟩
           → IsTm (fst (lookup N δ)) (fst (lookup t δ))
  isTm-out t N δ = PT.rec squash₁
    (λ { (inl h) → PT.map conCase h ; (inr h) → PT.map varCase h })
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
         ⊎ (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 1) y)
                        × ⟨ y ∈ˢ fst (lookup N δ) ⟩))
    conCase : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ tagPr (suc t) 0 v0 ⟩
                            × ⟨ fst ym ∈ˢ ⟪ W ⟫↪ mC ⟩) → Goal
    conCase (ym , (e , h∈)) = inl (fst ym
      , ( tagPr-out (suc t) 0 v0 (ym ∷ δ) e
        , subst (λ u → ⟨ fst ym ∈ˢ u ⟩) qC h∈ ))
    varCase : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ tagPr (suc t) 1 v0 ⟩
                            × ⟨ fst ym ∈ˢ fst (lookup N δ) ⟩) → Goal
    varCase (ym , (e , h∈)) = inr (fst ym
      , ( tagPr-out (suc t) 1 v0 (ym ∷ δ) e , h∈ ))

  isTm-in : {n : ℕ} (t N : Fin n) (δ : Vec SM n)
          → IsTm (fst (lookup N δ)) (fst (lookup t δ)) → ⟨ δ ⊨ᵐ isTm t N ⟩
  isTm-in t N δ = PT.rec (snd (δ ⊨ᵐ isTm t N)) go
    where
    go : (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
       ⊎ (Σ[ y ∈ S ] ((fst (lookup t δ) ≡ prS (numS 1) y)
                      × ⟨ y ∈ˢ fst (lookup N δ) ⟩))
       → ⟨ δ ⊨ᵐ isTm t N ⟩
    go (inl (y , (e , y∈))) =
      ∣ inl ∣ pt y (mem C y y∈ C∈)
            , ( tagPr-in (suc t) 0 v0 (pt y (mem C y y∈ C∈) ∷ δ) e
              , subst (λ u → ⟨ y ∈ˢ u ⟩) (sym qC) y∈ ) ∣₁ ∣₁
    go (inr (y , (e , y∈))) =
      ∣ inr ∣ pt y (mem (fst (lookup N δ)) y y∈ (snd (lookup N δ)))
            , ( tagPr-in (suc t) 1 v0
                  (pt y (mem (fst (lookup N δ)) y y∈ (snd (lookup N δ))) ∷ δ) e
              , y∈ ) ∣₁ ∣₁

  subK : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ W ⟫ n
  subK N a D = ∃̇ ( prAt v0 (suc N) (suc a) ∧̇ (var v0 ∈̇ var (suc D)) )

  subK-out : {n : ℕ} (N a D : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ subK N a D ⟩
           → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
  subK-out N a D δ = PT.rec (snd (_ ∈ˢ fst (lookup D δ))) go
    where
    go : Σ[ ym ∈ SM ] (⟨ (ym ∷ δ) ⊨ᵐ prAt v0 (suc N) (suc a) ⟩
                       × ⟨ fst ym ∈ˢ fst (lookup D δ) ⟩)
       → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
    go (ym , (e , h)) = subst (λ u → ⟨ u ∈ˢ fst (lookup D δ) ⟩)
      (prAtS-out v0 (suc N) (suc a) (ym ∷ δ) e) h

  subK-in : {n : ℕ} (N a D : Fin n) (δ : Vec SM n)
          → ⟨ prS (fst (lookup N δ)) (fst (lookup a δ)) ∈ˢ fst (lookup D δ) ⟩
          → ⟨ δ ⊨ᵐ subK N a D ⟩
  subK-in N a D δ h = ∣ ym , (prAtS-in v0 (suc N) (suc a) (ym ∷ δ) refl , h) ∣₁
    where
    ym : SM
    ym = pt (prS (fst (lookup N δ)) (fst (lookup a δ)))
            (prIn _ _ (snd (lookup N δ)) (snd (lookup a δ)))

  sucBody : {n : ℕ} → Fin n → Formula ⟪ W ⟫ (suc n)
  sucBody N = (var v0 ∈̇ var (suc N)) ∨̇ (var v0 ≐ var (suc N))

  succEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ W ⟫ n
  succEq m N = eqFrame m (sucBody N)

  opaque
    unfolding sucS

    sucSub : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S)
           → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩ → ⟨ v ∈ˢ W ⟩
    sucSub N δ v h = ∈sucV-elim {A = fst (lookup N δ)} {x = v}
      (snd (v ∈ˢ W)) h
      (λ h' → mem (fst (lookup N δ)) v h' (snd (lookup N δ)))
      (λ e → subst (λ u → ⟨ u ∈ˢ W ⟩) (sym e) (snd (lookup N δ)))

    sucMout : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S) (v∈ : ⟨ v ∈ˢ W ⟩)
            → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ sucBody N ⟩
            → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩
    sucMout N δ v v∈ = PT.rec (snd (v ∈ˢ sucV (fst (lookup N δ)))) go
      where
      go : ⟨ v ∈ˢ fst (lookup N δ) ⟩ ⊎ (v ≡ fst (lookup N δ))
         → ⟨ v ∈ˢ sucV (fst (lookup N δ)) ⟩
      go (inl h) = ∈sucV-inl {A = fst (lookup N δ)} {x = v} h
      go (inr e) = subst (λ u → ⟨ u ∈ˢ sucV (fst (lookup N δ)) ⟩) (sym e)
        (self∈sucV (fst (lookup N δ)))

    sucMin : {n : ℕ} (N : Fin n) (δ : Vec SM n) (v : S) (v∈ : ⟨ v ∈ˢ W ⟩)
           → ⟨ v ∈ˢ sucS (fst (lookup N δ)) ⟩
           → ⟨ (pt v v∈ ∷ δ) ⊨ᵐ sucBody N ⟩
    sucMin N δ v v∈ h = ∈sucV-elim {A = fst (lookup N δ)} {x = v}
      (snd ((pt v v∈ ∷ δ) ⊨ᵐ sucBody N)) h
      (λ h' → ∣ inl h' ∣₁) (λ e → ∣ inr e ∣₁)

  succEq-out : {n : ℕ} (m N : Fin n) (δ : Vec SM n) → ⟨ δ ⊨ᵐ succEq m N ⟩
             → fst (lookup m δ) ≡ sucS (fst (lookup N δ))
  succEq-out m N δ = eqFrame-out m (sucBody N) δ (sucS (fst (lookup N δ)))
    (sucSub N δ) (sucMout N δ) (sucMin N δ)

  succEq-in : {n : ℕ} (m N : Fin n) (δ : Vec SM n)
            → fst (lookup m δ) ≡ sucS (fst (lookup N δ))
            → ⟨ δ ⊨ᵐ succEq m N ⟩
  succEq-in m N δ = eqFrame-in m (sucBody N) δ (sucS (fst (lookup N δ)))
    (sucSub N δ) (sucMout N δ) (sucMin N δ)
```

<!--en-->
## The six relations
<!--zh-->
## 六条关系
<!--/-->

<!--en-->
What a tag demands of its payload beyond its shape. An atom demands two term
codes; a connective demands that both parts are keys of the witness set at the
same arity; a negation demands one; a constant demands that its payload is zero;
a quantifier demands one key at the next arity; a bounded quantifier demands a
term code and one key at the next arity. Six relations, twelve tags, and the
only thing that varies between two tags of the same kind is a number.
<!--zh-->
一个标签对其载荷除形状之外的要求。原子索取两条词项码；联结词索取两个部件都是见证集在同一元数上的键；否定索取一个；常量索取其载荷为零；量词索取下一元数上的一个键；有界量词索取一条词项码与下一元数上的一个键。六条关系，十二个标签，而同一类的两个标签之间唯一变动的是一个数。
<!--/-->

```agda
  relTm relSame relBnd : Formula ⟪ W ⟫ 7
  relTm   = isTm v1 v2 ∧̇ isTm v0 v2
  relSame = subK v2 v1 v5 ∧̇ subK v2 v0 v5
  relBnd  = isTm v1 v2 ∧̇ ∃̇ ( succEq v0 v3 ∧̇ subK v0 v1 v6 )

  relOne relZero relSucc : Formula ⟪ W ⟫ 6
  relOne  = subK v1 v0 v4
  relZero = var v0 ≐ con (nm 0)
  relSucc = ∃̇ ( succEq v0 v2 ∧̇ subK v0 v1 v5 )

  relTm-out : (δ : Vec SM 3) (w N a b : SM)
            → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relTm ⟩
            → IsTm (fst N) (fst a) × IsTm (fst N) (fst b)
  relTm-out δ w N a b (h₁ , h₂) =
      isTm-out v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , isTm-out v0 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relTm-in : (δ : Vec SM 3) (w N a b : SM)
           → IsTm (fst N) (fst a) → IsTm (fst N) (fst b)
           → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relTm ⟩
  relTm-in δ w N a b h₁ h₂ =
      isTm-in v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , isTm-in v0 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relSame-out : (δ : Vec SM 3) (w N a b : SM)
              → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relSame ⟩
              → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
              × ⟨ prS (fst N) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
  relSame-out δ w N a b (h₁ , h₂) =
      subK-out v2 v1 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , subK-out v2 v0 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relSame-in : (δ : Vec SM 3) (w N a b : SM)
             → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ prS (fst N) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relSame ⟩
  relSame-in δ w N a b h₁ h₂ =
      subK-in v2 v1 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , subK-in v2 v0 v5 (b ∷ a ∷ N ∷ w ∷ δ) h₂

  relBnd-out : (δ : Vec SM 3) (w N a b : SM)
             → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relBnd ⟩
             → IsTm (fst N) (fst a)
             × ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
  relBnd-out δ w N a b (h₁ , h₂) =
    isTm-out v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , PT.rec (snd (prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ))) go h₂
    where
    go : Σ[ Mm ∈ SM ] (⟨ (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ succEq v0 v3 ⟩
                       × ⟨ (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ subK v0 v1 v6 ⟩)
       → ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
    go (Mm , (e , s)) =
      subst (λ u → ⟨ prS u (fst b) ∈ˢ fst (lookup v1 δ) ⟩)
        (succEq-out v0 v3 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) e)
        (subK-out v0 v1 v6 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) s)

  relBnd-in : (δ : Vec SM 3) (w N a b : SM) → ⟨ sucS (fst N) ∈ˢ W ⟩
            → IsTm (fst N) (fst a)
            → ⟨ prS (sucS (fst N)) (fst b) ∈ˢ fst (lookup v1 δ) ⟩
            → ⟨ (b ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ relBnd ⟩
  relBnd-in δ w N a b hs h₁ h₂ =
      isTm-in v1 v2 (b ∷ a ∷ N ∷ w ∷ δ) h₁
    , ∣ Mm , ( succEq-in v0 v3 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) refl
             , subK-in v0 v1 v6 (Mm ∷ b ∷ a ∷ N ∷ w ∷ δ) h₂ ) ∣₁
    where
    Mm : SM
    Mm = pt (sucS (fst N)) hs

  relOne-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relOne ⟩
             → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
  relOne-out δ w N a = subK-out v1 v0 v4 (a ∷ N ∷ w ∷ δ)

  relOne-in : (δ : Vec SM 3) (w N a : SM)
            → ⟨ prS (fst N) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
            → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relOne ⟩
  relOne-in δ w N a = subK-in v1 v0 v4 (a ∷ N ∷ w ∷ δ)

  relZero-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relZero ⟩
              → fst a ≡ numS 0
  relZero-out δ w N a e = e ∙ qnm 0

  relZero-in : (δ : Vec SM 3) (w N a : SM) → fst a ≡ numS 0
             → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relZero ⟩
  relZero-in δ w N a e = e ∙ sym (qnm 0)

  relSucc-out : (δ : Vec SM 3) (w N a : SM) → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relSucc ⟩
              → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
  relSucc-out δ w N a =
    PT.rec (snd (prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ))) go
    where
    go : Σ[ Mm ∈ SM ] (⟨ (Mm ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ succEq v0 v2 ⟩
                       × ⟨ (Mm ∷ a ∷ N ∷ w ∷ δ) ⊨ᵐ subK v0 v1 v5 ⟩)
       → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
    go (Mm , (e , s)) =
      subst (λ u → ⟨ prS u (fst a) ∈ˢ fst (lookup v1 δ) ⟩)
        (succEq-out v0 v2 (Mm ∷ a ∷ N ∷ w ∷ δ) e)
        (subK-out v0 v1 v5 (Mm ∷ a ∷ N ∷ w ∷ δ) s)

  relSucc-in : (δ : Vec SM 3) (w N a : SM) → ⟨ sucS (fst N) ∈ˢ W ⟩
             → ⟨ prS (sucS (fst N)) (fst a) ∈ˢ fst (lookup v1 δ) ⟩
             → ⟨ (a ∷ N ∷ w ∷ δ) ⊨ᵐ relSucc ⟩
  relSucc-in δ w N a hs h =
    ∣ Mm , ( succEq-in v0 v2 (Mm ∷ a ∷ N ∷ w ∷ δ) refl
           , subK-in v0 v1 v5 (Mm ∷ a ∷ N ∷ w ∷ δ) h ) ∣₁
    where
    Mm : SM
    Mm = pt (sucS (fst N)) hs
```

<!--en-->
## The twelve clauses
<!--zh-->
## 十二条子句
<!--/-->

<!--en-->
One clause per constructor, each a frame at its tag with the relation that tag
calls for, and beside each the meta-level fact its satisfaction amounts to. The
tag is a number, so the twelve are a function of a number and the disjunction
over them is a fold rather than a chain of injections: the elimination comes
back with a number and the introduction takes one, and neither ever nests a
truncation eleven deep.
<!--zh-->
每个构造子一条子句，每条都是该标签处的一个框架配上那个标签所要求的关系，而每条旁边是它的满足关系所归结到的元层事实。标签是一个数，故这十二条是一个关于数的函数，而它们的析取是一次折叠、而不是一串注入：消去带着一个数回来，引入取走一个数，两边都不会把截断嵌套十一层深。
<!--/-->

```agda
  clause : ℕ → Formula ⟪ W ⟫ 4
  clause 0  = binForm 0  relTm
  clause 1  = binForm 1  relTm
  clause 2  = binForm 2  relSame
  clause 3  = binForm 3  relSame
  clause 4  = binForm 4  relSame
  clause 5  = unForm  5  relOne
  clause 6  = unForm  6  relZero
  clause 7  = unForm  7  relZero
  clause 8  = unForm  8  relSucc
  clause 9  = unForm  9  relSucc
  clause 10 = binForm 10 relBnd
  clause 11 = binForm 11 relBnd
  clause _  = ⊥̇

  TmShape SameShape BndShape : ℕ → S → S → Type (ℓ-suc ℓ)
  TmShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (IsTm N a × IsTm N b))
  SameShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (⟨ prS N a ∈ˢ D ⟩ × ⟨ prS N b ∈ˢ D ⟩))
  BndShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ] Σ[ b ∈ S ]
    ((w ≡ binKey t N a b) × (IsTm N a × ⟨ prS (sucS N) b ∈ˢ D ⟩))

  OneShape ZeroShape SuccShape : ℕ → S → S → Type (ℓ-suc ℓ)
  OneShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × ⟨ prS N a ∈ˢ D ⟩)
  ZeroShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × (a ≡ numS 0))
  SuccShape t D w = Σ[ N ∈ S ] Σ[ a ∈ S ]
    ((w ≡ unKey t N a) × ⟨ prS (sucS N) a ∈ˢ D ⟩)

  Shape : ℕ → S → S → Type (ℓ-suc ℓ)
  Shape 0  = TmShape 0
  Shape 1  = TmShape 1
  Shape 2  = SameShape 2
  Shape 3  = SameShape 3
  Shape 4  = SameShape 4
  Shape 5  = OneShape 5
  Shape 6  = ZeroShape 6
  Shape 7  = ZeroShape 7
  Shape 8  = SuccShape 8
  Shape 9  = SuccShape 9
  Shape 10 = BndShape 10
  Shape 11 = BndShape 11
  Shape _  = λ _ _ → ⊥*
```

<!--en-->
Reading a clause is its frame's elimination followed by its relation's, and
writing one is the two introductions in the other order. The parts a shape names
are members of the level because the whole is, which the sealed pair's two
projections supply; that is the only thing the introduction needs that the shape
itself does not carry.
<!--zh-->
读一条子句就是先用它那个框架的消去、再用它那条关系的消去，而写一条则是两个引入反过来。一个形状所点名的诸部件是该层的成员，因为整体是，而这由封好的对的两个投影供给；那也是引入所需、而形状自身不携带的唯一一样东西。
<!--/-->

```agda
  private
    packBin : (t : ℕ) (rel : Formula ⟪ W ⟫ 7) (δ : Vec SM 3) (w : SM)
              (N a b : S) → fst w ≡ binKey t N a b
            → ((hN : ⟨ N ∈ˢ W ⟩) (ha : ⟨ a ∈ˢ W ⟩) (hb : ⟨ b ∈ˢ W ⟩)
               → ⟨ (pt b hb ∷ pt a ha ∷ pt N hN ∷ w ∷ δ) ⊨ᵐ rel ⟩)
            → ⟨ (w ∷ δ) ⊨ᵐ binForm t rel ⟩
    packBin t rel δ w N a b e k =
      binForm-in t rel δ w
        (pt N hN , pt a ha , pt b hb , (e , k hN ha hb))
      where
      p1 = prParts N (prS (numS t) (prS a b))
             (subst (λ u → ⟨ u ∈ˢ W ⟩) e (snd w))
      p2 = prParts (numS t) (prS a b) (p1 .snd)
      p3 = prParts a b (p2 .snd)
      hN = p1 .fst
      ha = p3 .fst
      hb = p3 .snd

    packUn : (t : ℕ) (rel : Formula ⟪ W ⟫ 6) (δ : Vec SM 3) (w : SM)
             (N a : S) → fst w ≡ unKey t N a
           → ((hN : ⟨ N ∈ˢ W ⟩) (ha : ⟨ a ∈ˢ W ⟩)
              → ⟨ (pt a ha ∷ pt N hN ∷ w ∷ δ) ⊨ᵐ rel ⟩)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t rel ⟩
    packUn t rel δ w N a e k =
      unForm-in t rel δ w (pt N hN , pt a ha , (e , k hN ha))
      where
      p1 = prParts N (prS (numS t) a) (subst (λ u → ⟨ u ∈ˢ W ⟩) e (snd w))
      p2 = prParts (numS t) a (p1 .snd)
      hN = p1 .fst
      ha = p2 .snd

    sucOfKey : (N a D : S) → ⟨ D ∈ˢ W ⟩ → ⟨ prS (sucS N) a ∈ˢ D ⟩
             → ⟨ sucS N ∈ˢ W ⟩
    sucOfKey N a D hD h =
      prParts (sucS N) a (mem D (prS (sucS N) a) h hD) .fst

    outTm : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relTm δ w
          → TmShape t (fst (lookup v1 δ)) (fst w)
    outTm t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relTm-out δ w N a b hr)

    outSame : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relSame δ w
            → SameShape t (fst (lookup v1 δ)) (fst w)
    outSame t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relSame-out δ w N a b hr)

    outBnd : (t : ℕ) (δ : Vec SM 3) (w : SM) → BinWit t relBnd δ w
           → BndShape t (fst (lookup v1 δ)) (fst w)
    outBnd t δ w (N , a , b , (e , hr)) =
      fst N , fst a , fst b , (e , relBnd-out δ w N a b hr)

    outOne : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relOne δ w
           → OneShape t (fst (lookup v1 δ)) (fst w)
    outOne t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relOne-out δ w N a hr)

    outZero : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relZero δ w
            → ZeroShape t (fst (lookup v1 δ)) (fst w)
    outZero t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relZero-out δ w N a hr)

    outSucc : (t : ℕ) (δ : Vec SM 3) (w : SM) → UnWit t relSucc δ w
            → SuccShape t (fst (lookup v1 δ)) (fst w)
    outSucc t δ w (N , a , (e , hr)) =
      fst N , fst a , (e , relSucc-out δ w N a hr)

    inTm : (t : ℕ) (δ : Vec SM 3) (w : SM)
         → TmShape t (fst (lookup v1 δ)) (fst w)
         → ⟨ (w ∷ δ) ⊨ᵐ binForm t relTm ⟩
    inTm t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relTm δ w N a b e
        (λ hN ha hb → relTm-in δ w (pt N hN) (pt a ha) (pt b hb) h₁ h₂)

    inSame : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → SameShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ binForm t relSame ⟩
    inSame t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relSame δ w N a b e
        (λ hN ha hb → relSame-in δ w (pt N hN) (pt a ha) (pt b hb) h₁ h₂)

    inBnd : (t : ℕ) (δ : Vec SM 3) (w : SM)
          → BndShape t (fst (lookup v1 δ)) (fst w)
          → ⟨ (w ∷ δ) ⊨ᵐ binForm t relBnd ⟩
    inBnd t δ w (N , a , b , (e , (h₁ , h₂))) =
      packBin t relBnd δ w N a b e
        (λ hN ha hb → relBnd-in δ w (pt N hN) (pt a ha) (pt b hb)
          (sucOfKey N b (fst (lookup v1 δ)) (snd (lookup v1 δ)) h₂) h₁ h₂)

    inOne : (t : ℕ) (δ : Vec SM 3) (w : SM)
          → OneShape t (fst (lookup v1 δ)) (fst w)
          → ⟨ (w ∷ δ) ⊨ᵐ unForm t relOne ⟩
    inOne t δ w (N , a , (e , h)) =
      packUn t relOne δ w N a e
        (λ hN ha → relOne-in δ w (pt N hN) (pt a ha) h)

    inZero : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → ZeroShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t relZero ⟩
    inZero t δ w (N , a , (e , h)) =
      packUn t relZero δ w N a e
        (λ hN ha → relZero-in δ w (pt N hN) (pt a ha) h)

    inSucc : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → SuccShape t (fst (lookup v1 δ)) (fst w)
           → ⟨ (w ∷ δ) ⊨ᵐ unForm t relSucc ⟩
    inSucc t δ w (N , a , (e , h)) =
      packUn t relSucc δ w N a e
        (λ hN ha → relSucc-in δ w (pt N hN) (pt a ha)
          (sucOfKey N a (fst (lookup v1 δ)) (snd (lookup v1 δ)) h) h)

  clauseOut : (t : ℕ) (δ : Vec SM 3) (w : SM) → ⟨ (w ∷ δ) ⊨ᵐ clause t ⟩
            → ∥ Shape t (fst (lookup v1 δ)) (fst w) ∥₁
  clauseOut 0  δ w h = PT.map (outTm 0 δ w) (binForm-out 0 relTm δ w h)
  clauseOut 1  δ w h = PT.map (outTm 1 δ w) (binForm-out 1 relTm δ w h)
  clauseOut 2  δ w h = PT.map (outSame 2 δ w) (binForm-out 2 relSame δ w h)
  clauseOut 3  δ w h = PT.map (outSame 3 δ w) (binForm-out 3 relSame δ w h)
  clauseOut 4  δ w h = PT.map (outSame 4 δ w) (binForm-out 4 relSame δ w h)
  clauseOut 5  δ w h = PT.map (outOne 5 δ w) (unForm-out 5 relOne δ w h)
  clauseOut 6  δ w h = PT.map (outZero 6 δ w) (unForm-out 6 relZero δ w h)
  clauseOut 7  δ w h = PT.map (outZero 7 δ w) (unForm-out 7 relZero δ w h)
  clauseOut 8  δ w h = PT.map (outSucc 8 δ w) (unForm-out 8 relSucc δ w h)
  clauseOut 9  δ w h = PT.map (outSucc 9 δ w) (unForm-out 9 relSucc δ w h)
  clauseOut 10 δ w h = PT.map (outBnd 10 δ w) (binForm-out 10 relBnd δ w h)
  clauseOut 11 δ w h = PT.map (outBnd 11 δ w) (binForm-out 11 relBnd δ w h)
  clauseOut (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc t))))))))))))  δ w h = Empty.rec* h

  clauseIn : (t : ℕ) (δ : Vec SM 3) (w : SM)
           → Shape t (fst (lookup v1 δ)) (fst w) → ⟨ (w ∷ δ) ⊨ᵐ clause t ⟩
  clauseIn 0  = inTm 0
  clauseIn 1  = inTm 1
  clauseIn 2  = inSame 2
  clauseIn 3  = inSame 3
  clauseIn 4  = inSame 4
  clauseIn 5  = inOne 5
  clauseIn 6  = inZero 6
  clauseIn 7  = inZero 7
  clauseIn 8  = inSucc 8
  clauseIn 9  = inSucc 9
  clauseIn 10 = inBnd 10
  clauseIn 11 = inBnd 11
  clauseIn (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc t)))))))))))) δ w s = Empty.rec* s
```

<!--en-->
## The predicate
<!--zh-->
## 谓词
<!--/-->

<!--en-->
The disjunction of the twelve, the statement that every member of a set is one
of them, and the predicate itself: a set is a code at an arity when some set
holds its key and holds nothing that is not a well-formed key. The witness is
bound by an unbounded existential, which is a quantifier over the level, and the
level is where every witness the other direction builds will live.
<!--zh-->
十二条的析取、「某集合的每个成员都是其中之一」这条陈述，以及谓词本身：一个集合在某元数上是一条码，当有某个集合持有它的键、且不持有任何不是良构键的东西。见证由一个无界存在量词绑住，那是对该层的量词，而另一方向所造的每个见证都将住在该层中。
<!--/-->

```agda
  orUpto : ℕ → Formula ⟪ W ⟫ 4
  orUpto zero    = ⊥̇
  orUpto (suc m) = clause m ∨̇ orUpto m

  node : Formula ⟪ W ⟫ 4
  node = orUpto 12

  orUpto-in : (m t : ℕ) → t < m → (δ : Vec SM 4) → ⟨ δ ⊨ᵐ clause t ⟩
            → ⟨ δ ⊨ᵐ orUpto m ⟩
  orUpto-in zero t lt δ h = Empty.rec (¬-<-zero lt)
  orUpto-in (suc m) t lt δ h = Sum.rec
    (λ lt' → ∣ inr (orUpto-in m t lt' δ h) ∣₁)
    (λ e → ∣ inl (subst (λ j → ⟨ δ ⊨ᵐ clause j ⟩) e h) ∣₁)
    (<-split lt)

  orUpto-out : (m : ℕ) (δ : Vec SM 4) → ⟨ δ ⊨ᵐ orUpto m ⟩
             → ∥ Σ[ t ∈ ℕ ] ⟨ δ ⊨ᵐ clause t ⟩ ∥₁
  orUpto-out zero δ h = Empty.rec* h
  orUpto-out (suc m) δ = PT.rec squash₁ go
    where
    go : ⟨ δ ⊨ᵐ clause m ⟩ ⊎ ⟨ δ ⊨ᵐ orUpto m ⟩
       → ∥ Σ[ t ∈ ℕ ] ⟨ δ ⊨ᵐ clause t ⟩ ∥₁
    go (inl h) = ∣ m , h ∣₁
    go (inr h) = orUpto-out m δ h

  private
    shapeLt : (t : ℕ) (D w : S) → Shape t D w → t < 12
    shapeLt 0  D w _ = 11 , refl
    shapeLt 1  D w _ = 10 , refl
    shapeLt 2  D w _ = 9  , refl
    shapeLt 3  D w _ = 8  , refl
    shapeLt 4  D w _ = 7  , refl
    shapeLt 5  D w _ = 6  , refl
    shapeLt 6  D w _ = 5  , refl
    shapeLt 7  D w _ = 4  , refl
    shapeLt 8  D w _ = 3  , refl
    shapeLt 9  D w _ = 2  , refl
    shapeLt 10 D w _ = 1  , refl
    shapeLt 11 D w _ = 0  , refl
    shapeLt (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc t)))))))))))) D w s = Empty.rec* s

  Well : S → Type (ℓ-suc ℓ)
  Well D = (w : S) → ⟨ w ∈ˢ D ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁

  wellAt : Formula ⟪ W ⟫ 3
  wellAt = ∀̇∈ (var v1) node

  well-out : (δ : Vec SM 3) → ⟨ δ ⊨ᵐ wellAt ⟩ → Well (fst (lookup v1 δ))
  well-out δ h w w∈ = PT.rec squash₁ go (orUpto-out 12 (wm ∷ δ) (h wm w∈))
    where
    wm : SM
    wm = pt w (mem (fst (lookup v1 δ)) w w∈ (snd (lookup v1 δ)))
    go : Σ[ t ∈ ℕ ] ⟨ (wm ∷ δ) ⊨ᵐ clause t ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t (fst (lookup v1 δ)) w ∥₁
    go (t , ht) = PT.map (λ s → t , s) (clauseOut t δ wm ht)

  well-in : (δ : Vec SM 3) → Well (fst (lookup v1 δ)) → ⟨ δ ⊨ᵐ wellAt ⟩
  well-in δ hw xm x∈ = PT.rec (snd ((xm ∷ δ) ⊨ᵐ node)) go (hw (fst xm) x∈)
    where
    go : Σ[ t ∈ ℕ ] Shape t (fst (lookup v1 δ)) (fst xm)
       → ⟨ (xm ∷ δ) ⊨ᵐ node ⟩
    go (t , s) = orUpto-in 12 t (shapeLt t (fst (lookup v1 δ)) (fst xm) s)
      (xm ∷ δ) (clauseIn t δ xm s)

  Φ : ℕ → Formula ⟪ W ⟫ 1
  Φ k = ∃̇ (∃̇ ( tagPr v0 k v2 ∧̇ ((var v0 ∈̇ var v1) ∧̇ wellAt) ))

  Witness : ℕ → S → Type (ℓ-suc ℓ)
  Witness k x = Σ[ D ∈ S ] (Well D × ⟨ keyOf k x ∈ˢ D ⟩)

  Φ-out : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
        → ∥ Witness k x ∥₁
  Φ-out k x x∈ = PT.rec squash₁ (λ { (Dm , hD) → PT.map (go Dm) hD })
    where
    go : (Dm : SM)
       → Σ[ km ∈ SM ]
           (⟨ (km ∷ Dm ∷ pt x x∈ ∷ []) ⊨ᵐ tagPr v0 k v2 ⟩
            × (⟨ fst km ∈ˢ fst Dm ⟩
               × ⟨ (km ∷ Dm ∷ pt x x∈ ∷ []) ⊨ᵐ wellAt ⟩))
       → Witness k x
    go Dm (km , (e , (h∈ , hw))) = fst Dm
      , ( well-out (km ∷ Dm ∷ pt x x∈ ∷ []) hw
        , subst (λ u → ⟨ u ∈ˢ fst Dm ⟩)
            (tagPr-out v0 k v2 (km ∷ Dm ∷ pt x x∈ ∷ []) e) h∈ )

  Φ-in : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) (D : S) (hD : ⟨ D ∈ˢ W ⟩)
       → Well D → ⟨ keyOf k x ∈ˢ D ⟩ → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
  Φ-in k x x∈ D hD hw h∈ =
    ∣ pt D hD
    , ∣ km , ( tagPr-in v0 k v2 env refl , (h∈ , well-in env hw) ) ∣₁ ∣₁
    where
    km : SM
    km = pt (keyOf k x) (prIn (numS k) x (numIn k) x∈)
    env : Vec SM 3
    env = km ∷ pt D hD ∷ pt x x∈ ∷ []
```

<!--en-->
## From a witness to a formula
<!--zh-->
## 从见证到公式
<!--/-->

<!--en-->
The first half of adequacy. A witness set holding the key of a set at an arity
produces a formula of that arity whose code is that set. The recursion runs on
the rank of the code, carrying the arity beside it as a number, so that a
quantifier may come back one arity higher without anything being descended into
twice.

Twelve tags collapse to six frames, since a frame is decided by the payload's
shape and what changes inside a frame is a tag and a constructor. Each frame
takes its constructor's coding equation as an argument rather than leaving the
elaborator to find it; with the constructor a variable nothing reduces, and the
unification would be the whole cost.
<!--zh-->
充分性的头一半。持有某个集合在某元数上的键的见证集，产出该元数上的一条公式，其码就是那个集合。递归跑在码的秩上，把元数作为一个数在旁边带着，好让量词能在高一级的元数上回来，而不必有任何东西被下降两次。

十二个标签收拢为六个框架，因为框架由载荷的形状决定，而一个框架之内变动的只是一个标签与一个构造子。每个框架把它那个构造子的编码等式取作实参，而不留给归约器去找；构造子既是变元，就没有东西会化简，而那次合一将是全部代价。
<!--/-->

```agda
  Coded : ℕ → S → Type (ℓ-suc ℓ)
  Coded n x = ∥ Σ[ φ ∈ Formula ⟪ C ⟫ n ] (code φ ≡ x) ∥₁

  splitBin : (j t : ℕ) (z N a b : S) → keyOf j z ≡ binKey t N a b
           → (numS j ≡ N) × (z ≡ prS (numS t) (prS a b))
  splitBin j t z N a b = prS-inj

  splitUn : (j t : ℕ) (z N a : S) → keyOf j z ≡ unKey t N a
          → (numS j ≡ N) × (z ≡ prS (numS t) a)
  splitUn j t z N a = prS-inj

  opaque
    unfolding prS numS

    codeBin : (t : ℕ) (p q : S) → prS (numS t) (prS p q) ≡ VCode.mkTag t (pr p q)
    codeBin t p q = refl

    codeUn : (t : ℕ) (p : S) → prS (numS t) p ≡ VCode.mkTag t p
    codeUn t p = refl

  private
    tmOf : (j : ℕ) (a : S) → IsTm (numS j) a
         → ∥ Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a) ∥₁
    tmOf j a = PT.rec squash₁ go
      where
      go : (Σ[ y ∈ S ] ((a ≡ prS (numS 0) y) × ⟨ y ∈ˢ C ⟩))
         ⊎ (Σ[ y ∈ S ] ((a ≡ prS (numS 1) y) × ⟨ y ∈ˢ numS j ⟩))
         → ∥ Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a) ∥₁
      go (inl (y , (e , y∈))) =
        ∣ con (fib .fst)
        , ( cong (VCode.mkTag 0) (fib .snd)
            ∙ sym (codeUn 0 y) ∙ sym e ) ∣₁
        where
        fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ y)
        fib = ∈-asFiber {a = y} {b = C} y∈
      go (inr (y , (e , y∈))) = PT.map pick
        (∈#-elim j y (subst (λ u → ⟨ y ∈ˢ u ⟩) (numS-# j) y∈))
        where
        pick : Σ[ m ∈ ℕ ] ((m < j) × (y ≡ (# m)))
             → Σ[ τ ∈ Term ⟪ C ⟫ j ] (codeTm τ ≡ a)
        pick (m , (m<j , qy)) = var (fromℕ' j m m<j)
          , ( cong (λ u → VCode.mkTag 1 (# u)) (toFromId' j m m<j)
              ∙ cong (VCode.mkTag 1) (sym qy)
              ∙ sym (codeUn 1 y) ∙ sym e )

  recover : (D : S) → Well D → (n : ℕ) (x : S) → ⟨ keyOf n x ∈ˢ D ⟩ → Coded n x
  recover D hw n x = ∈-induction step (rank x) n x refl
    where
    P : S → Type (ℓ-suc ℓ)
    P r = (j : ℕ) (z : S) → rank z ≡ r → ⟨ keyOf j z ∈ˢ D ⟩ → Coded j z

    step : (r : S) → ((y : S) → ⟨ y ∈ˢ r ⟩ → P y) → P r
    step r IH j z qr wz = PT.rec squash₁ fill (hw (keyOf j z) wz)
      where
      rec : (i : ℕ) (u : S) → ⟨ rank u ∈ˢ rank z ⟩ → ⟨ keyOf i u ∈ˢ D ⟩
          → Coded i u
      rec i u lt wu =
        IH (rank u) (subst (λ v → ⟨ rank u ∈ˢ v ⟩) qr lt) i u refl wu

      atomK : (t : ℕ)
              (op : ∀ {i} → Term ⟪ C ⟫ i → Term ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
            → (∀ {i} (s u : Term ⟪ C ⟫ i)
               → code (op s u) ≡ VCode.mkTag t (pr (codeTm s) (codeTm u)))
            → TmShape t D (keyOf j z) → Coded j z
      atomK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ f1 (tmOf j a ha')
        where
        sp = splitBin j t z N a b e
        ha' : IsTm (numS j) a
        ha' = subst (λ u → IsTm u a) (sym (sp .fst)) ha
        hb' : IsTm (numS j) b
        hb' = subst (λ u → IsTm u b) (sym (sp .fst)) hb
        f2 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a)
           → Σ[ u ∈ Term ⟪ C ⟫ j ] (codeTm u ≡ b)
           → Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ z)
        f2 (s , qs) (u , qu) = op s u
          , ( qop s u ∙ cong (VCode.mkTag t) (cong₂ pr qs qu)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        f1 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a) → Coded j z
        f1 p = PT.map (f2 p) (tmOf j b hb')

      sameK : (t : ℕ)
              (op : ∀ {i} → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
            → (∀ {i} (φ ψ : Formula ⟪ C ⟫ i)
               → code (op φ ψ) ≡ VCode.mkTag t (pr (code φ) (code ψ)))
            → SameShape t D (keyOf j z) → Coded j z
      sameK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ f1
        (rec j a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                   (leftPart (numS t) a b))
                 (subst (λ u → ⟨ prS u a ∈ˢ D ⟩) (sym (sp .fst)) ha))
        where
        sp = splitBin j t z N a b e
        f2 : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a)
           → Σ[ ψ ∈ Formula ⟪ C ⟫ j ] (code ψ ≡ b)
           → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f2 (φ , qφ) (ψ , qψ) = op φ ψ
          , ( qop φ ψ ∙ cong (VCode.mkTag t) (cong₂ pr qφ qψ)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        f1 : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a) → Coded j z
        f1 p = PT.map (f2 p)
          (rec j b (subst (λ u → ⟨ rank b ∈ˢ rank u ⟩) (sym (sp .snd))
                     (rightPart (numS t) a b))
                   (subst (λ u → ⟨ prS u b ∈ˢ D ⟩) (sym (sp .fst)) hb))

      oneK : (t : ℕ) (op : ∀ {i} → Formula ⟪ C ⟫ i → Formula ⟪ C ⟫ i)
           → (∀ {i} (φ : Formula ⟪ C ⟫ i)
              → code (op φ) ≡ VCode.mkTag t (code φ))
           → OneShape t D (keyOf j z) → Coded j z
      oneK t op qop (N , a , (e , ha)) = PT.map f
        (rec j a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                   (payload≺ (numS t) a))
                 (subst (λ u → ⟨ prS u a ∈ˢ D ⟩) (sym (sp .fst)) ha))
        where
        sp = splitUn j t z N a e
        f : Σ[ φ ∈ Formula ⟪ C ⟫ j ] (code φ ≡ a)
          → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f (φ , qφ) = op φ
          , ( qop φ ∙ cong (VCode.mkTag t) qφ
              ∙ sym (codeUn t a) ∙ sym (sp .snd) )

      zeroK : (t : ℕ) (op : ∀ {i} → Formula ⟪ C ⟫ i)
            → (∀ (i : ℕ) → code (op {i}) ≡ VCode.mkTag t (# 0))
            → ZeroShape t D (keyOf j z) → Coded j z
      zeroK t op qop (N , a , (e , ha)) = ∣ op
        , ( qop j ∙ cong (VCode.mkTag t) (sym (numS-# 0))
            ∙ sym (codeUn t (numS 0)) ∙ cong (prS (numS t)) (sym ha)
            ∙ sym (splitUn j t z N a e .snd) ) ∣₁

      succK : (t : ℕ)
              (op : ∀ {i} → Formula ⟪ C ⟫ (suc i) → Formula ⟪ C ⟫ i)
            → (∀ {i} (φ : Formula ⟪ C ⟫ (suc i))
               → code (op φ) ≡ VCode.mkTag t (code φ))
            → SuccShape t D (keyOf j z) → Coded j z
      succK t op qop (N , a , (e , ha)) = PT.map f
        (rec (suc j) a (subst (λ u → ⟨ rank a ∈ˢ rank u ⟩) (sym (sp .snd))
                         (payload≺ (numS t) a))
                       (subst (λ u → ⟨ prS u a ∈ˢ D ⟩)
                         (sym (numS-suc j ∙ cong sucS (sp .fst))) ha))
        where
        sp = splitUn j t z N a e
        f : Σ[ φ ∈ Formula ⟪ C ⟫ (suc j) ] (code φ ≡ a)
          → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f (φ , qφ) = op φ
          , ( qop φ ∙ cong (VCode.mkTag t) qφ
              ∙ sym (codeUn t a) ∙ sym (sp .snd) )

      bndK : (t : ℕ)
             (op : ∀ {i} → Term ⟪ C ⟫ i → Formula ⟪ C ⟫ (suc i) → Formula ⟪ C ⟫ i)
           → (∀ {i} (s : Term ⟪ C ⟫ i) (φ : Formula ⟪ C ⟫ (suc i))
              → code (op s φ) ≡ VCode.mkTag t (pr (codeTm s) (code φ)))
           → BndShape t D (keyOf j z) → Coded j z
      bndK t op qop (N , a , b , (e , (ha , hb))) = PT.rec squash₁ f1
        (tmOf j a (subst (λ u → IsTm u a) (sym (sp .fst)) ha))
        where
        sp = splitBin j t z N a b e
        f2 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a)
           → Σ[ φ ∈ Formula ⟪ C ⟫ (suc j) ] (code φ ≡ b)
           → Σ[ χ ∈ Formula ⟪ C ⟫ j ] (code χ ≡ z)
        f2 (s , qs) (φ , qφ) = op s φ
          , ( qop s φ ∙ cong (VCode.mkTag t) (cong₂ pr qs qφ)
              ∙ sym (codeBin t a b) ∙ sym (sp .snd) )
        f1 : Σ[ s ∈ Term ⟪ C ⟫ j ] (codeTm s ≡ a) → Coded j z
        f1 p = PT.map (f2 p)
          (rec (suc j) b (subst (λ u → ⟨ rank b ∈ˢ rank u ⟩) (sym (sp .snd))
                           (rightPart (numS t) a b))
                         (subst (λ u → ⟨ prS u b ∈ˢ D ⟩)
                           (sym (numS-suc j ∙ cong sucS (sp .fst))) hb))

      fill : Σ[ t ∈ ℕ ] Shape t D (keyOf j z) → Coded j z
      fill (0  , s) = atomK 0  _∈̇_ (λ _ _ → refl) s
      fill (1  , s) = atomK 1  _≐_ (λ _ _ → refl) s
      fill (2  , s) = sameK 2  _∧̇_ (λ _ _ → refl) s
      fill (3  , s) = sameK 3  _∨̇_ (λ _ _ → refl) s
      fill (4  , s) = sameK 4  _⇒̇_ (λ _ _ → refl) s
      fill (5  , s) = oneK  5  ¬̇_  (λ _ → refl) s
      fill (6  , s) = zeroK 6  ⊤̇   (λ _ → refl) s
      fill (7  , s) = zeroK 7  ⊥̇   (λ _ → refl) s
      fill (8  , s) = succK 8  ∃̇_  (λ _ → refl) s
      fill (9  , s) = succK 9  ∀̇_  (λ _ → refl) s
      fill (10 , s) = bndK  10 ∀̇∈  (λ _ _ → refl) s
      fill (11 , s) = bndK  11 ∃̇∈  (λ _ _ → refl) s
      fill ((suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc t)))))))))))) , s) = Empty.rec* s
```

<!--en-->
## From a formula to a witness
<!--zh-->
## 从公式到见证
<!--/-->

<!--en-->
The other half. What a formula owes is a set, and the set is the keys of its
subformulas: its own key, together with the same collection for each part. Every
member of the level, since a singleton and a binary union are two applications
of the operations, and the keys themselves are pairs of numerals with codes.

Its well-formedness is one induction, and it is stated for any superset rather
than for the closure itself. That is not generality for its own sake: the
induction hands a part's collection to the same statement, and the part's shape
has to name keys of the **whole** collection, which only a statement quantified
over the superset can say.
<!--zh-->
另一半。一条公式所欠的是一个集合，而那个集合是它诸子公式的键：它自己的键，连同每个部件的同样那份收集。全都是该层的成员，因为单点集与二元并是运算的两次施用，而诸键本身是数码与码所成的对。

它的良构性是一次归纳，且是对任意超集陈述、而非只对那个闭包。这不是为一般性而一般性：归纳把一个部件的收集交给同一条陈述，而该部件的形状必须点名**整份**收集里的键，而这只有对超集作量化的陈述才说得出来。
<!--/-->

```agda
  key : ∀ {n} → Formula ⟪ C ⟫ n → S
  key {n} φ = keyOf n (code φ)

  opaque
    unfolding cupS sglS

    cup-inl : (a b x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ cupS a b ⟩
    cup-inl a b x h = F5-spec ⁅ a , b ⁆ a x .snd
      ∣ a , (pair∈ a b a ∣ inl refl ∣₁ , h) ∣₁

    cup-inr : (a b x : S) → ⟨ x ∈ˢ b ⟩ → ⟨ x ∈ˢ cupS a b ⟩
    cup-inr a b x h = F5-spec ⁅ a , b ⁆ a x .snd
      ∣ b , (pair∈ a b b ∣ inr refl ∣₁ , h) ∣₁

    cup-out : (a b x : S) → ⟨ x ∈ˢ cupS a b ⟩
            → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
    cup-out a b x h = PT.rec squash₁ pick (F5-spec ⁅ a , b ⁆ a x .fst h)
      where
      pick : Σ[ v ∈ S ] (⟨ v ∈ˢ ⁅ a , b ⁆ ⟩ × ⟨ x ∈ˢ v ⟩)
           → ∥ ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩ ∥₁
      pick (v , (v∈ , x∈v)) = PT.map choose (F0-spec a b v .fst v∈)
        where
        choose : (v ≡ a) ⊎ (v ≡ b) → ⟨ x ∈ˢ a ⟩ ⊎ ⟨ x ∈ˢ b ⟩
        choose (inl e) = inl (subst (λ u → ⟨ x ∈ˢ u ⟩) e x∈v)
        choose (inr e) = inr (subst (λ u → ⟨ x ∈ˢ u ⟩) e x∈v)

    sgl-in : (a : S) → ⟨ a ∈ˢ sglS a ⟩
    sgl-in = self∈sgl

    sgl-out : (a x : S) → ⟨ x ∈ˢ sglS a ⟩ → x ≡ a
    sgl-out a x h = singl-eq x a h

  clo : ∀ {n} → Formula ⟪ C ⟫ n → S
  subclo : ∀ {n} → Formula ⟪ C ⟫ n → S

  clo φ = cupS (sglS (key φ)) (subclo φ)

  subclo (s ∈̇ u)  = ∅
  subclo (s ≐ u)  = ∅
  subclo (a ∧̇ b)  = cupS (clo a) (clo b)
  subclo (a ∨̇ b)  = cupS (clo a) (clo b)
  subclo (a ⇒̇ b)  = cupS (clo a) (clo b)
  subclo (¬̇ a)    = clo a
  subclo ⊤̇        = ∅
  subclo ⊥̇        = ∅
  subclo (∃̇ a)    = clo a
  subclo (∀̇ a)    = clo a
  subclo (∀̇∈ s a) = clo a
  subclo (∃̇∈ s a) = clo a

  key∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ key φ ∈ˢ W ⟩
  key∈W {n} φ = prIn (numS n) (code φ) (numIn n) (codeIn φ)

  clo∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ clo φ ∈ˢ W ⟩
  subclo∈W : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ subclo φ ∈ˢ W ⟩

  clo∈W φ = cupIn _ _ (sglIn (key φ) (key∈W φ)) (subclo∈W φ)

  subclo∈W (s ∈̇ u)  = ∅∈W
  subclo∈W (s ≐ u)  = ∅∈W
  subclo∈W (a ∧̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (a ∨̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (a ⇒̇ b)  = cupIn _ _ (clo∈W a) (clo∈W b)
  subclo∈W (¬̇ a)    = clo∈W a
  subclo∈W ⊤̇        = ∅∈W
  subclo∈W ⊥̇        = ∅∈W
  subclo∈W (∃̇ a)    = clo∈W a
  subclo∈W (∀̇ a)    = clo∈W a
  subclo∈W (∀̇∈ s a) = clo∈W a
  subclo∈W (∃̇∈ s a) = clo∈W a

  key∈clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) → ⟨ key φ ∈ˢ clo φ ⟩
  key∈clo φ = cup-inl (sglS (key φ)) (subclo φ) (key φ) (sgl-in (key φ))

  sub∈clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) (x : S)
          → ⟨ x ∈ˢ subclo φ ⟩ → ⟨ x ∈ˢ clo φ ⟩
  sub∈clo φ = cup-inr (sglS (key φ)) (subclo φ)
```

<!--en-->
Terms first, since nothing about them descends: a constant's code is the
constant, which is a member of the carrier by the presentation, and a variable's
code carries an index below the arity, which is a numeral inside a numeral. Then
the head of a closure, one tuple per constructor, with the subkeys read out of
the collection the caller supplies.
<!--zh-->
先看词项，因为它们身上没有任何东西下降：常元的码就是那个常元，而它由呈现给出是载体的成员；变元的码携带一个低于元数的序号，那是数码之内的数码。然后是一个闭包的头部，每个构造子一个元组，其诸子键从调用方所供的那份收集里读出。
<!--/-->

```agda
  private
    tmIn : ∀ {m} (τ : Term ⟪ C ⟫ m) → IsTm (numS m) (codeTm τ)
    tmIn (con c) = ∣ inl (ι c , ( sym (codeUn 0 (ι c))
                                , ∈∈ₛ {a = ι c} {b = C} .snd (∈ₛ⟪ C ⟫↪ c) )) ∣₁
    tmIn {m} (var i) = ∣ inr ((# (toℕ i))
      , ( sym (codeUn 1 (# (toℕ i)))
        , subst (λ u → ⟨ (# (toℕ i)) ∈ˢ u ⟩) (sym (numS-# m))
            (#mono (toℕ i) m (toℕ<n i)) )) ∣₁

    binEq : ∀ {n} (t : ℕ) (φ : Formula ⟪ C ⟫ n) (p q : S)
          → code φ ≡ VCode.mkTag t (pr p q)
          → key φ ≡ binKey t (numS n) p q
    binEq {n} t φ p q e =
      cong (prS (numS n)) (e ∙ sym (codeBin t p q))

    unEq : ∀ {n} (t : ℕ) (φ : Formula ⟪ C ⟫ n) (p : S)
         → code φ ≡ VCode.mkTag t p → key φ ≡ unKey t (numS n) p
    unEq {n} t φ p e = cong (prS (numS n)) (e ∙ sym (codeUn t p))

    subIn : ∀ {n m} (φ : Formula ⟪ C ⟫ n) (a : Formula ⟪ C ⟫ m) (D : S)
          → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
          → ⟨ key a ∈ˢ clo φ ⟩ → ⟨ prS (numS m) (code a) ∈ˢ D ⟩
    subIn φ a D sub h = sub (key a) h

    sucKey : ∀ {n} (a : Formula ⟪ C ⟫ (suc n)) (D : S)
           → ⟨ prS (numS (suc n)) (code a) ∈ˢ D ⟩
           → ⟨ prS (sucS (numS n)) (code a) ∈ˢ D ⟩
    sucKey {n} a D h =
      subst (λ u → ⟨ prS u (code a) ∈ˢ D ⟩) (numS-suc n) h

  headShape : ∀ {n} (φ : Formula ⟪ C ⟫ n) (D : S)
            → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
            → Σ[ t ∈ ℕ ] Shape t D (key φ)
  headShape {n} (s ∈̇ u) D sub = 0
    , ( numS n , codeTm s , codeTm u
      , ( binEq 0 (s ∈̇ u) (codeTm s) (codeTm u) refl , (tmIn s , tmIn u) ) )
  headShape {n} (s ≐ u) D sub = 1
    , ( numS n , codeTm s , codeTm u
      , ( binEq 1 (s ≐ u) (codeTm s) (codeTm u) refl , (tmIn s , tmIn u) ) )
  headShape {n} φ@(a ∧̇ b) D sub = 2
    , ( numS n , code a , code b
      , ( binEq 2 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(a ∨̇ b) D sub = 3
    , ( numS n , code a , code b
      , ( binEq 3 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(a ⇒̇ b) D sub = 4
    , ( numS n , code a , code b
      , ( binEq 4 φ (code a) (code b) refl
        , ( subIn φ a D sub
              (sub∈clo φ (key a) (cup-inl (clo a) (clo b) (key a) (key∈clo a)))
          , subIn φ b D sub
              (sub∈clo φ (key b) (cup-inr (clo a) (clo b) (key b) (key∈clo b)))
          ) ) )
  headShape {n} φ@(¬̇ a) D sub = 5
    , ( numS n , code a
      , ( unEq 5 φ (code a) refl
        , subIn φ a D sub (sub∈clo φ (key a) (key∈clo a)) ) )
  headShape {n} ⊤̇ D sub = 6
    , ( numS n , numS 0
      , ( unEq 6 ⊤̇ (numS 0) (cong (VCode.mkTag 6) (sym (numS-# 0))) , refl ) )
  headShape {n} ⊥̇ D sub = 7
    , ( numS n , numS 0
      , ( unEq 7 ⊥̇ (numS 0) (cong (VCode.mkTag 7) (sym (numS-# 0))) , refl ) )
  headShape {n} φ@(∃̇ a) D sub = 8
    , ( numS n , code a
      , ( unEq 8 φ (code a) refl
        , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) )
  headShape {n} φ@(∀̇ a) D sub = 9
    , ( numS n , code a
      , ( unEq 9 φ (code a) refl
        , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) )
  headShape {n} φ@(∀̇∈ s a) D sub = 10
    , ( numS n , codeTm s , code a
      , ( binEq 10 φ (codeTm s) (code a) refl
        , ( tmIn s
          , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) ) )
  headShape {n} φ@(∃̇∈ s a) D sub = 11
    , ( numS n , codeTm s , code a
      , ( binEq 11 φ (codeTm s) (code a) refl
        , ( tmIn s
          , sucKey a D (subIn φ a D sub (sub∈clo φ (key a) (key∈clo a))) ) ) )
```

<!--en-->
Every member of a closure is well shaped, by one induction on the formula. Each
case splits the member between the head key and the parts' collections, answers
the head from the table above, and hands a part to itself with the inclusion
composed. The four leaves have no parts, so their split has an impossible
branch.
<!--zh-->
一个闭包的每个成员都是良形的，凭沿公式的一次归纳。每种情形把成员在头部的键与诸部件的收集之间切开，头部由上面那张表作答，而部件连同复合好的包含一起交回给它自己。四个叶子没有部件，故它们的切分有一支不可能。
<!--/-->

```agda
  private
    headOf : ∀ {m} (ψ : Formula ⟪ C ⟫ m) (D w : S)
           → ((x : S) → ⟨ x ∈ˢ clo ψ ⟩ → ⟨ x ∈ˢ D ⟩)
           → ⟨ w ∈ˢ sglS (key ψ) ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    headOf ψ D w sub e = ∣ subst (λ v → Σ[ t ∈ ℕ ] Shape t D v)
      (sym (sgl-out (key ψ) w e)) (headShape ψ D sub) ∣₁

    noSub : (D w : S) → ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    noSub D w h = Empty.rec (∅-empty w (∈∈ₛ {a = w} {b = ∅} .fst h))

  cloWell : ∀ {n} (φ : Formula ⟪ C ⟫ n) (D : S)
          → ((x : S) → ⟨ x ∈ˢ clo φ ⟩ → ⟨ x ∈ˢ D ⟩)
          → (w : S) → ⟨ w ∈ˢ clo φ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
  cloWell φ@(s ∈̇ u) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@(s ≐ u) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@⊤̇ D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@⊥̇ D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ ∅ ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = noSub D w h
  cloWell φ@(¬̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∃̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∀̇ a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∀̇∈ s a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(∃̇∈ s a) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ clo a ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = cloWell a D (λ x hx → sub x (sub∈clo φ x hx)) w h
  cloWell φ@(a ∧̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)
  cloWell φ@(a ∨̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)
  cloWell φ@(a ⇒̇ b) D sub w hw =
    PT.rec squash₁ go (cup-out (sglS (key φ)) (subclo φ) w hw)
    where
    go2 : ⟨ w ∈ˢ clo a ⟩ ⊎ ⟨ w ∈ˢ clo b ⟩ → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go2 (inl h) = cloWell a D
      (λ x hx → sub x (sub∈clo φ x (cup-inl (clo a) (clo b) x hx))) w h
    go2 (inr h) = cloWell b D
      (λ x hx → sub x (sub∈clo φ x (cup-inr (clo a) (clo b) x hx))) w h
    go : ⟨ w ∈ˢ sglS (key φ) ⟩ ⊎ ⟨ w ∈ˢ cupS (clo a) (clo b) ⟩
       → ∥ Σ[ t ∈ ℕ ] Shape t D w ∥₁
    go (inl e) = headOf φ D w sub e
    go (inr h) = PT.rec squash₁ go2 (cup-out (clo a) (clo b) w h)

  Well-clo : ∀ {n} (φ : Formula ⟪ C ⟫ n) → Well (clo φ)
  Well-clo φ = cloWell φ (clo φ) (λ x h → h)
```

<!--en-->
## Adequacy, and the code set described
<!--zh-->
## 充分性，与被描述的码集
<!--/-->

<!--en-->
The two halves meet. A member of the level satisfies the predicate at an arity
exactly when it is the code of a formula of that arity over the carrier: the
closure supplies the witness one way, the recursion reads it the other. So the
definable subset the predicate carves out of the level **is** the code set, which
is the equation the code set chapter left standing.
<!--zh-->
两半会合。该层的一个成员在某元数上满足该谓词，恰当它是载体之上该元数的某条公式的码：闭包朝一个方向供给见证，递归朝另一个方向把它读出。故该谓词从该层中刻出的那个可定义子集**就是**那个码集，而这正是码集那一章留在那里的等式。
<!--/-->

```agda
  satCode : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
          → Coded k x
  satCode k x x∈ h = PT.rec squash₁ go (Φ-out k x x∈ h)
    where
    go : Witness k x → Coded k x
    go (D , (hw , h∈)) = recover D hw k x h∈

  codeSat : (k : ℕ) (x : S) (x∈ : ⟨ x ∈ˢ W ⟩) → Coded k x
          → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
  codeSat k x x∈ = PT.rec (snd ((pt x x∈ ∷ []) ⊨ᵐ Φ k)) go
    where
    go : Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) → ⟨ (pt x x∈ ∷ []) ⊨ᵐ Φ k ⟩
    go (φ , q) = Φ-in k x x∈ (clo φ) (clo∈W φ) (Well-clo φ)
      (subst (λ u → ⟨ keyOf k u ∈ˢ clo φ ⟩) q (key∈clo φ))

  codeSet-desc : (k : ℕ) → ((x : S) → ⟨ x ∈ˢ codeSet k ⟩ → ⟨ x ∈ˢ W ⟩)
               → defSet (Φ k) ≡ codeSet k
  codeSet-desc k inW = described (Φ k) (codeSet k) inW din dout
    where
    din : (v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ v ∈ˢ codeSet k ⟩
        → ⟨ (pt v v∈ ∷ []) ⊨ᵐ Φ k ⟩
    din v v∈ h = codeSat k v v∈ (codeSet-out k v h)
    dout : (v : S) (v∈ : ⟨ v ∈ˢ W ⟩) → ⟨ (pt v v∈ ∷ []) ⊨ᵐ Φ k ⟩
         → ⟨ v ∈ˢ codeSet k ⟩
    dout v v∈ h = PT.rec (snd (v ∈ˢ codeSet k)) go (satCode k v v∈ h)
      where
      go : Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ v) → ⟨ v ∈ˢ codeSet k ⟩
      go (φ , q) = subst (λ u → ⟨ u ∈ˢ codeSet k ⟩) q (code∈codeSet k φ)
```

<!--en-->
## The discharge, at the honest index
<!--zh-->
## 兑付，在诚实的索引处
<!--/-->

<!--en-->
The telescope is instantiated once, and where it is instantiated is the whole
arithmetic of the previous chapter. The codes of the formulas over a carrier are
cofinal above the carrier's own stage, so no finite offset holds them; but a
**limit** level holding the carrier holds every one of them, which is that
chapter's containment half. So the level the predicate is written over is the
next limit above the carrier, and the level the code set is a member of is any
limit above that one.

Two limits, not one and not a finite offset: the inner one to hold the codes and
carry the quantifiers, the outer one to hold the set. Everything the telescope
asks of the inner level is one application of the sealed operation family, and
the seven applications live in a single block so that no concrete stage is ever
handed to conversion anywhere else.
<!--zh-->
望远镜只被实例化一次，而它在何处被实例化，正是上一章的全部算术。某载体之上诸公式的码在该载体自身的阶段之上共尾，故没有有限偏移持有它们；但持有该载体的某个**极限**层持有它们中的每一个，那正是那一章包含的那一半。故谓词所写在其上的那一层是载体之上的下一个极限，而码集所属的那一层是其上的任何极限。

两个极限，不是一个、也不是有限偏移：内层用来持有诸码并承载诸量词，外层用来持有那个集合。望远镜向内层索取的一切都是封好的运算族的一次施用，而这七次施用住在单一一个块里，好让任何具体的阶段都不在别处被交给转换检查。
<!--/-->

```agda
module At (γ : S) (limγ : ⟨ isLimit γ ⟩)
          (δ : S) (limδ : ⟨ isLimit δ ⟩) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
          (C : S) (C∈δ : ⟨ C ∈ˢ Sset δ ⟩) where

  private
    W : S
    W = Sset δ

    module IL = InLevel δ limδ
    module CR = Carrier δ limδ C C∈δ

  C∈γ : ⟨ C ∈ˢ Sset γ ⟩
  C∈γ = Sset-trans γ {x = Sset δ} {y = C} C∈δ (Sset-mem {α = γ} {β = δ} δ∈γ)

  opaque
    unfolding prS numS sglS cupS

    prJ : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ prS a b ∈ˢ W ⟩
    prJ = IL.pr∈J

    numJ : (k : ℕ) → ⟨ numS k ∈ˢ W ⟩
    numJ = IL.numeral∈J C C∈δ

    sglJ : (a : S) → ⟨ a ∈ˢ W ⟩ → ⟨ sglS a ∈ˢ W ⟩
    sglJ a ha = subst (λ u → ⟨ u ∈ˢ W ⟩)
      (Fof-f0 a a ∙ sym (singl≡pair a)) (Jset-rud δ limδ f0 a a ha ha)

    cupJ : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩ → ⟨ cupS a b ∈ˢ W ⟩
    cupJ a b ha hb = subst (λ u → ⟨ u ∈ˢ W ⟩)
      (Fof-f5 (Fof f0 a b) a ∙ cong ⋃_ (Fof-f0 a b))
      (Jset-rud δ limδ f5 (Fof f0 a b) a (Jset-rud δ limδ f0 a b ha hb) ha)

  module P = Pred W (Sset-trans δ) C C∈δ prJ numJ sglJ cupJ
                  (IL.∅∈J C C∈δ) CR.code∈J

  module CG = Carrier γ limγ C C∈γ

  codeSet-Description : (k : ℕ) → CG.Description (Codes.codeSet C k)
  codeSet-Description k =
    ∣ δ , (δ∈γ , (P.Φ k , P.codeSet-desc k (CR.codeSet⊆J k))) ∣₁

  codeSet∈J : (k : ℕ) → ⟨ Codes.codeSet C k ∈ˢ Sset γ ⟩
  codeSet∈J k = CG.codeSet∈J k (codeSet-Description k)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The object-language predicate `Φ`{.Agda} says, at any arity, that a set is the
code of a formula of that arity over a carrier: a witness set holds its key, and
every member of that witness set is a well-formed key, by twelve clauses keyed
by the tag (`clause`{.Agda}, `Shape`{.Agda}). It is read entirely inside the
level, so no clause is bounded and no absoluteness is spent. Both directions of
adequacy are proved: from a witness the formula is recovered by a recursion on
the rank of the code (`recover`{.Agda}), and from a formula a witness is built as
the finite collection of its subformulas' keys (`clo`{.Agda},
`Well-clo`{.Agda}). Hence the definable subset the predicate carves out of a
limit level holding the carrier is exactly the code set at that arity
(`codeSet-desc`{.Agda}).

That equation is the object the code set chapter left standing, and it is
discharged here (`codeSet-Description`{.Agda}), so the code set at every arity is
a member of any limit level above the one the predicate is read in
(`codeSet∈J`{.Agda}). The index is honest in the chapter's own sense: not a
finite offset, which the previous chapter refuted, but the next limit for the
codes and one more limit for the set.
<!--zh-->
对象语言谓词 `Φ`{.Agda} 在任意元数上说出：某个集合是载体之上该元数的某条公式的码，即有一个见证集持有它的键，且该见证集的每个成员都是良构的键，凭十二条以标签为键的子句 (`clause`{.Agda}、`Shape`{.Agda})。它整个在层内读出，故没有哪条子句有界，绝对性也分文未花。充分性的两个方向都证出：从见证经一场跑在码的秩上的递归还原出公式 (`recover`{.Agda})，而从公式则把它诸子公式之键所成的有限收集造成见证 (`clo`{.Agda}、`Well-clo`{.Agda})。于是该谓词从持有载体的某个极限层中刻出的可定义子集，恰是该元数上的码集 (`codeSet-desc`{.Agda})。

那条等式正是码集那一章留在那里的对象，而它在此兑付 (`codeSet-Description`{.Agda})，故每个元数上的码集都是该谓词所读之层之上任何极限层的成员 (`codeSet∈J`{.Agda})。这个索引在那一章自己的意义上是诚实的：不是有限偏移，那已被上一章反驳，而是诸码所需的下一个极限，再加为那个集合多取的一个极限。
<!--/-->
