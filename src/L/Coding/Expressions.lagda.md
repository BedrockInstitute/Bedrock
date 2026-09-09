<!--en-->
# Formula expressions for coded recursion
<!--zh-->
# 码化递归所用的公式表达式
<!--ja-->
# 符号化再帰のための論理式表現
<!--/-->

<!--en-->
This chapter builds reusable object-language formulas for the set expressions,
tags, environment operations, quantifiers, term evaluation, and atoms needed by
the coded satisfaction recursion, together with their semantic readings.
<!--zh-->
本章为码化满足关系递归所需的集合表达式、标签、环境运算、量词、词项求值与原子构造可复用的对象语言公式，并给出其语义读式。
<!--ja-->
本章では、符号化された充足関係の再帰に必要な集合表現、タグ、環境演算、量化子、項の評価、原子のための再利用可能な対象言語の論理式を構成し、それぞれの意味論的な読みを与える。
<!--/-->

<!--en-->
This chapter builds finite expressions from slots, literals, numerals, and pairs.
Their single structural reader is adequate for the value they denote, and the
remaining definitions compose that reader into the formula shapes used by coded
recursion clauses.
<!--zh-->
本章用位置、字面常元、数码与配对构成有穷表达式。一次结构递归得到的读式，恰好刻画表达式所指的值；其余定义再把该读式组合成码化递归子句所用的公式形状。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Expressions {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import FOL.Manipulation.ConstantBounding using ( BoundedFo )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo )
open import L.Coding.Environment {ℓ}
  using ( sucAt; Δ₀-sucAt; sucAt-adequate; consAt; Δ₀-consAt; consAt-adequate
        ; env; cons; shiftPairAt; sgl0At; pair0At; tag0At )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )

open import L.Coding.Model {ℓ}
  using ( lookup-fst; prʟ; prʟ-fst; prAtL; prAtL-adequate; envOverAt
        ; Container; container )
```

```agda
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

module PairExpression where
  data Expr (n : ℕ) : Type (ℓ-suc ℓ) where
    slot : Fin n → Expr n
    literal : S → Expr n
    numeral : ℕ → Expr n
    pair : Expr n → Expr n → Expr n

  value : ∀ {n} → Expr n → (Fin n → V ℓ) → V ℓ
  value (slot i) γ = γ i
  value (literal a) γ = fst a
  value (numeral k) γ = # k
  value (pair a b) γ = pr (value a γ) (value b γ)

  element : ∀ {n} → Expr n → (Fin n → S) → S
  element (slot i) γ = γ i
  element (literal a) γ = a
  element (numeral k) γ = numeralL k
  element (pair a b) γ = prʟ (element a γ) (element b γ)

  element-fst : ∀ {n} (e : Expr n) (γ : Fin n → S)
              → fst (element e γ) ≡ value e (λ i → fst (γ i))
  element-fst (slot i) γ = refl
  element-fst (literal a) γ = refl
  element-fst (numeral k) γ = numeralL-fst k
  element-fst (pair a b) γ = prʟ-fst (element a γ) (element b γ)
    ∙ cong₂ pr (element-fst a γ) (element-fst b γ)

  lift3 : ∀ {n m} → (Fin n → Fin m) → Fin n → Fin (3 + m)
  lift3 ρ i = suc (suc (suc (ρ i)))

  read : ∀ {n m} → Expr n → (Fin n → Fin m) → Fin m → Formula S m
  read (slot i) ρ q = var q ≐ var (ρ i)
  read (literal a) ρ q = var q ≐ con a
  read (numeral k) ρ q = var q ≐ con (numeralL k)
  read (pair a b) ρ q = ∃̇∈ (var q) (∃̇∈ (var zero) (∃̇∈ (var (suc zero))
    (prAtL (suc (suc (suc q))) (suc zero) zero
      ∧̇ (read a (lift3 ρ) (suc zero) ∧̇ read b (lift3 ρ) zero))))

  out : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
       → ⟨ γ ⊨ read e ρ q ⟩ → fst (lookup q γ) ≡ value e (λ i → fst (lookup (ρ i) γ))
  out (slot i) ρ q γ h = h
  out (literal a) ρ q γ h = h
  out (numeral k) ρ q γ h = h ∙ numeralL-fst k
  out (pair a b) ρ q γ = PT.rec (setIsSet _ _) (λ { (s , s∈ , hs) →
    PT.rec (setIsSet _ _) (λ { (u , u∈ , hu) →
      PT.rec (setIsSet _ _) (λ { (v , v∈ , p , ha , hb) →
        subst ⟨_⟩ (prAtL-adequate (suc (suc (suc q))) (suc zero) zero (v ∷ u ∷ s ∷ γ)) p
        ∙ cong₂ pr (out a (lift3 ρ) (suc zero) (v ∷ u ∷ s ∷ γ) ha)
                   (out b (lift3 ρ) zero (v ∷ u ∷ s ∷ γ) hb) }) hu }) hs })

  into : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
        → fst (lookup q γ) ≡ value e (λ i → fst (lookup (ρ i) γ)) → ⟨ γ ⊨ read e ρ q ⟩
  into (slot i) ρ q γ h = h
  into (literal a) ρ q γ h = h
  into (numeral k) ρ q γ h = h ∙ sym (numeralL-fst k)
  into {n} {m} (pair a b) ρ q γ h = ∣ s , c .snd .fst , ∣ u , c .snd .snd .fst ,
    ∣ v , c .snd .snd .snd ,
      subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc q))) (suc zero) zero δ)) e
      , into a (lift3 ρ) (suc zero) δ (element-fst a η)
      , into b (lift3 ρ) zero δ (element-fst b η) ∣₁ ∣₁ ∣₁
    where
    η : Fin n → S
    η i = lookup (ρ i) γ
    u v : S
    u = element a η
    v = element b η
    e : fst (lookup q γ) ≡ pr (fst u) (fst v)
    e = h ∙ sym (cong₂ pr (element-fst a η) (element-fst b η))
    c : Container (lookup q γ) u v
    c = container (lookup q γ) u v e
    s : S
    s = c .fst
    δ : S ^ (suc (suc (suc m)))
    δ = v ∷ u ∷ s ∷ γ

  adequate : ∀ {n m} (e : Expr n) (ρ : Fin n → Fin m) (q : Fin m) (γ : S ^ m)
            → (γ ⊨ read e ρ q) ≡ PairIs (fst (lookup q γ)) (value e (λ i → fst (lookup (ρ i) γ)))
  adequate e ρ q γ = ⇔toPath (out e ρ q γ) (into e ρ q γ)

  member : ∀ {n} → Expr n → Term S n → Formula S n
  member e C = ∃̇∈ C (read e suc zero)

  member-out : ∀ {n} (e : Expr n) (C : Term S n) (γ : S ^ n)
              → ⟨ γ ⊨ member e C ⟩ → ⟨ value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ) ⟩
  member-out e C γ = PT.rec (snd (value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ)))
    (λ { (x , h , p) → subst (λ v → ⟨ v ∈ fst (⟦ C ⟧ γ) ⟩) (out e suc zero (x ∷ γ) p) h })

  member-in : ∀ {n} (e : Expr n) (C : Term S n) (γ : S ^ n)
             → ⟨ value e (λ i → fst (lookup i γ)) ∈ fst (⟦ C ⟧ γ) ⟩ → ⟨ γ ⊨ member e C ⟩
  member-in e C γ h = ∣ x , h , into e suc zero (x ∷ γ) refl ∣₁
    where
    x : S
    x = value e (λ i → fst (lookup i γ)) , isL-trans h (snd (⟦ C ⟧ γ))

tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = PairExpression.read
  (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot x)) id s

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot x)) id s γ

tagPairAtL : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagPairAtL s k a b = PairExpression.read
  (PairExpression.pair (PairExpression.numeral k)
    (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b))) id s

tagPairAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ tagPairAtL s k a b)
  ≡ PairIs (fst (lookup s γ))
      (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ))))
tagPairAtL-adequate s k a b γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.numeral k)
    (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b))) id s γ
```

<!--en-->
## Sets by extension
<!--zh-->
## 以外延给出集合
<!--ja-->
## 外延によって集合を定める
<!--/-->

<!--en-->
`extAt`{.Agda} states that a set in one slot has exactly the members satisfying a
unary formula, and its readers expose both directions of that membership
equivalence.
<!--zh-->
`extAt`{.Agda} 断言某槽位中的集合，其成员恰为满足一元公式的对象；其读式暴露成员等价的两个方向。
<!--ja-->
`extAt`{.Agda} はあるスロットの集合が一変数論理式を満たす対象をちょうど要素にもつことを述べ、その読み補題が所属の同値の両方向を与える。
<!--/-->

<!--en-->
Every clause of a recursion whose values are sets says the same thing: this value
is the set of exactly those things satisfying such-and-such. Written once, with
the condition left as a parameter, it is two implications under one quantifier,
and its two readings are the two projections. Nothing is proved, which is the
point: after this the clauses of a recursion cost only their conditions.

The set operations follow immediately, each one condition long, and each with its
meaning already in hand. The rest of a clause's content is whatever the condition
says, and that is where the mathematics of a particular recursion lives.
<!--zh-->
凡取值为集合的递归，其每一条子句说的都是同一句话：这个取值恰是满足某某条件的那些东西之集。把它一次写出来，条件留作参数，那就是一个量词之下的两条蕴含，而它的两种读法就是两个投影。什么也没有证，而这正是要点：此后一条递归子句的代价，只剩它的条件。

诸集合运算随即而来，每个一条条件那么长，且含义都已在手。一条子句其余的内容全在它的条件里说，而那正是某个特定递归的数学之所在。
<!--/-->

```agda
extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd

  extAt-in-both : ((z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
                → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
                → ⟨ γ ⊨ extAt y φ ⟩
  extAt-in-both f g = f , g


```

<!--en-->
## Reading a key in two layers
<!--zh-->
## 分两层读一个键
<!--ja-->
## 二層の鍵を読む
<!--/-->

<!--en-->
The arity-tag formulas recognize keys nested as an arity paired with a tagged
payload, and their adequacy lemmas recover the three components exactly.
<!--zh-->
元数标签公式识别「元数与带标签载荷之对」这一嵌套键，而其充分性引理准确恢复三个分量。
<!--ja-->
アリティ付きタグの論理式は、アリティとタグ付きペイロードとの対として入れ子になった鍵を認識し、その妥当性補題が三つの成分を正確に復元する。
<!--/-->

<!--en-->
The codes a recursion ranges over carry their arity: an entry is the arity's
numeral paired with the code proper, and the code proper is in turn a tag paired
with its payload. So a clause's hypothesis has to read *two* layers, not one, and
reading only the outer one is worse than incomplete. Pairing is injective, so a
one-layer reader silently matches the arity against the constructor tag and binds
the payload's own tag as though it were a subcode: the clause is then vacuous at
every arity but one, and wrong at that one. Nothing in Agda reports this, because
the reader is still true; it simply cannot be supplied.

The pair expression records both layers: the arity paired with a tagged
payload. The structural reader supplies the bounded component witnesses and
its adequacy proves the whole shape. The arity is left as a variable, so a
clause can speak of it, which the four constructors that change arity need.
<!--zh-->
递归所遍历的诸码携带自己的元数：一个条目是「元数的数码」与「码本身」之对，而码本身又是「标签」与「载荷」之对。故一条子句的假设必须读**两**层，不是一层；而只读外层比读得不完整更糟。配对是单射的，于是一层的读式会悄悄把元数与构造子标签匹配起来，并把载荷自己的标签当作子码绑定：那条子句于是在除一个元数外的所有元数上空洞，而在那一个上是错的。Agda 不会报告这件事，因为那条读式仍然为真；它只是无法被供给。

配对表达式记录这两层：元数与带标签的载荷配成对。结构读式供给有界的分量见证，其充分性证明整个形状。元数留作变元，好让子句能谈论它，而四个改变元数的构造子正需要这一点。
<!--/-->

```agda
arityTagPairAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula S n
arityTagPairAtL c ar k a b = PairExpression.read
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k)
      (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b)))) id c

arityTagPairAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagPairAtL c ar k a b)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ))
        (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ)))))
arityTagPairAtL-adequate c ar k a b γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k)
      (PairExpression.pair (PairExpression.slot a) (PairExpression.slot b)))) id c γ

arityTagAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Formula S n
arityTagAtL c ar k a = PairExpression.read
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot a))) id c

arityTagAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagAtL c ar k a)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ)) (pr (# k) (fst (lookup a γ))))
arityTagAtL-adequate c ar k a γ = PairExpression.adequate
  (PairExpression.pair (PairExpression.slot ar)
    (PairExpression.pair (PairExpression.numeral k) (PairExpression.slot a))) id c γ
```

<!--en-->
## Looking a subcode up in the table
<!--zh-->
## 在表中查一个子码
<!--ja-->
## 表から部分符号を引く
<!--/-->

<!--en-->
The lookup formulas connect a subformula's code and its environment to the value
recorded for that key in a satisfaction table.
<!--zh-->
查找公式把子公式的码及其环境，与满足关系表在该键处记录的取值联系起来。
<!--ja-->
参照の論理式は、部分論理式の符号とその環境を、充足関係表がその鍵に記録した値へ結びつける。
<!--/-->

<!--en-->
The frames bind a code's payload but never look the table up at it, because a
payload component may be a term code, at which the table has nothing. A relation
that does want the value must therefore build the key itself: pair the arity with
the component, and read the table there.

That is one existential over the key, and it is the piece four of the ten
relations are built from. The two that speak of a subformula at the next arity
need the same thing with the arity bumped, which is this with one more layer.
<!--zh-->
诸框架绑定一个码的载荷，却从不在其上查表，因为载荷分量可能是词项码，而表在那里什么也没有。想要取值的关系于是必须自己造那个键：把元数与该分量配成对，再在那里读表。

那是对该键的一个存在量词，也是十条关系中四条所由构造的部件。谈论下一元数处子公式的那两条，需要的是同一件事而元数加一，即此物再加一层。
<!--/-->


<!--en-->
The following discussion explains the table clauses conceptually. Their active
bounded formulas and semantic readers are defined in `L.Coding.SatisfactionClauses`;
the unused earlier clause formulas and frame indices have been removed here.
<!--zh-->
以下讨论从数学上解释表的子句。实际使用的有界公式与语义读式定义于 `L.Coding.SatisfactionClauses`；本章不再保留未被使用的旧子句公式及其框架索引。
<!--/-->

<!--en-->
## The shape of a clause
<!--zh-->
## 一条子句的形状
<!--ja-->
## 節の共通形
<!--/-->

<!--en-->
The clause combinators bind a code and its assigned value, assert the required
tagged syntax shape, and leave only the constructor-specific semantic condition
to their caller.
<!--zh-->
子句组合器绑定一个码及其被指派的值，断言所需的带标签语法形状，并把构造器特有的语义条件留给调用方。
<!--ja-->
節の結合子は符号とその割り当て値を束縛し、必要なタグ付き構文形を述べ、構成子ごとの意味条件だけを呼び出し側に残す。
<!--/-->

<!--en-->
A recursion on codes is stated by clauses, and the clauses come in a few shapes
rather than ten. A binary constructor's clause says: for every code in the
index with this tag over these two subcodes, and for the values the table records
at the three of them, such-and-such holds. All of that is fixed except the
such-and-such, so it is written once with the relation as a parameter, and the
three binary constructors differ only in which relation they hand it.

Five things are bound, in the order a reader meets them: the code, its arity, its
two payload components, and the value the table records at the code. The values
at the payload components are **not** bound, and that is what makes the frame
general. A connective's payload is a pair of formula codes and its
clause does want them, but an atom's payload is a pair of *term* codes, at which
the table has no entries at all, and a bounded quantifier's payload mixes the
two. So the frame binds what every constructor has and leaves the lookups to the
relation, which may perform them freely.

Reading the clause back is one chain of substitutions along the readers'
adequacy, and it is stated in the direction a soundness proof consumes: given a
code of that shape in the index and the three recorded values, the relation
holds.
<!--zh-->
对码的递归由子句陈述，而子句只有几种形状，不是十种。一个二元构造子的子句说：对索引中每个以此标签架在这两个子码之上的码，以及表在这三者处所记录的取值，某某成立。除了那个「某某」，其余全是固定的，故只写一次，把那条关系留作参数，而三个二元构造子只差交给它的是哪条关系。

被绑定的有五样，按读者遇到的次序：那个码、它的元数、它的两个载荷分量以及表在该码处记录的取值。诸载荷分量处的取值**不**被绑定，而这正是使该框架通用之处。一个联结词的载荷是一对公式码，它的子句确实要它们；但一个原子的载荷是一对**词项**码，表在那里根本没有条目，而有界量词的载荷则两者混杂。故框架只绑定每个构造子都有的东西，把查表留给那条关系，由它自行执行。

把子句读回来是沿诸读式的充分性作一串代换，而它按可靠性证明所消费的方向陈述：给定索引中一个那种形状的码与三个被记录的取值，那条关系成立。
<!--/-->


<!--en-->
Each frame reads the other way too, and the other way is what an instance uses.
The elimination takes a clause apart for a consumer who has a code in hand; the
introduction assembles one for a table that has to *satisfy* it. Both frames
introduce by a lambda, because a bounded universal over the model is a function
on members and an implication is a function on the reader's proof, so the two are
the same substitutions run backwards.
<!--zh-->
每个框架也向另一个方向读，而另一个方向才是实例要用的。消去是为「手上握着一个码」的消费方把子句拆开；引入是为「必须**满足**它」的一张表把子句装起来。两个框架都以一个 λ 引入，因为模型上的有界全称就是成员上的函数，而蕴含就是读式证明上的函数，故两者是同样的几次代换倒着跑。
<!--/-->

<!--en-->
Counting the shapes is worth a moment, because it says how much of the ten is
really there, and because counting it wrong is easy: this paragraph has been
wrong twice.

The frames distinguish exactly one thing, whether the payload is a pair or a
single component. The pair frame covers the two atoms, the three binary
connectives and the two bounded quantifiers, which is seven. The single-component
frame covers bottom and the two unbounded quantifiers, which is three. **Two**
frames, then, and ten relations above them.

What the frames must not distinguish is what the payload components *are*.
Grouping by that gives five kinds of relation, not five frames: term against
term, formula against formula, term against formula, one formula, and one
formula at the next arity. That is where the ten actually divide, and it
divides them in the relations, where the lookups live.

The single-component frame is the pair frame with one binder fewer, and reads
back the same way.
<!--zh-->
数一数有几种形状是值得的，因为它说出那十条里真正存在多少，也因为数错很容易：这一段已经错过两次。

诸框架只区分一件事：载荷是一个对，还是单个分量。对框架覆盖两个原子、三个二元联结词与两个有界量词，共七个；单分量框架覆盖底与两个无界量词，共三个。故是**两**个框架，其上有十条关系。

诸框架不可区分的，是那些载荷分量究竟**是什么**。按那个分组得到的是五种关系而非五个框架：词项对词项、公式对公式、词项对公式、单个公式、以及处于下一元数的单个公式。那才是十条真正分开的地方，而它们分在诸关系里，也就是查表所在之处。

单分量框架就是少一个绑定的对框架，读回来的方式相同。
<!--/-->



<!--en-->
## The positive connectives
<!--zh-->
## 正的联结词
<!--ja-->
## 正の結合子
<!--/-->

<!--en-->
The conjunction and disjunction clauses look up both immediate subcodes and
combine their recorded truth values with the corresponding positive connective.
<!--zh-->
合取与析取子句查找两个直接子码，并以相应正联结词组合其所记录的真值。
<!--ja-->
論理積と論理和の節は二つの直下の部分符号を参照し、記録された真理値を対応する正の結合子で組み合わせる。
<!--/-->

<!--en-->
Two of the ten can be written now, and they are the two that need nothing the
chapter has not got. Conjunction and disjunction relate the value at a code to
the values at its two subcodes by intersection and union, at the same arity, and
that is the whole of their content.

The shared part is a relation that binds the two subvalues and guards them with
the table lookups; the operation is what is left over, and it speaks of the value
at the code and the two subvalues, at positions two, one and zero. So a
propositional clause is one line above the shared part.

Implication needs the set of all environments at the code's arity, which the
chapter does not yet name, so it waits for that set. This is exactly the split
between the two lattice operations and the function-space semantics of
implication.
<!--zh-->
十条里有两条现在就能写，而它们正是不需要本章尚未拥有之物的那两条。合取与析取把某码处的取值与它两个子码处的取值以交、并相关联，元数相同，而这就是它们的全部内容。

共用的部分是一条关系，它绑定两个子取值，并以查表为它们设防；剩下的就是那个运算，它谈论该码处的取值与两个子取值，位于位置二、一、零。故一条命题子句在共用部分之上只有一行。

蕴含需要该码元数处的全体环境之集，而本章尚未为它命名，故它在此等候。这条界线正是两个格运算与蕴含的函数空间语义之间的分界。
<!--/-->


<!--en-->
## The ambient environment set
<!--zh-->
## 周遭环境集
<!--ja-->
## 周囲の環境集合
<!--/-->

<!--en-->
`envSetAt`{.Agda} retrieves from the environment tower the set of environments
at the arity held in a slot, so later clauses can bound their environment
quantifiers.
<!--zh-->
`envSetAt`{.Agda} 从环境塔中取出槽位所持元数处的环境集，使后续子句能界住其环境量词。
<!--ja-->
`envSetAt`{.Agda} は環境塔からスロットにあるアリティの環境集合を取り出し、後の節が環境についての量化子を有界にできるようにする。
<!--/-->

<!--en-->
Implication is interpreted over the set of all environments at the code's
arity, and that arity is a variable bound by the frame. The ambient set is
therefore a variable too, constrained by the extension frame applied to the
environment predicate. Inside a clause, the obligation is to describe that set;
the table construction later supplies one.
<!--zh-->
蕴含在该码元数处的全体环境之集上解释，而那个元数是框架绑定的变元。故周遭集合也是一个变元，由施于环境谓词的外延框架约束。在子句里，义务只是描述这个集合；此后造表的章节会交出一个这样的集合。
<!--/-->

```agda
envSetAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envSetAt E ar B = extAt E (envOverAt zero (suc ar) (suc B))


```

<!--en-->
## Implication and bottom
<!--zh-->
## 蕴含与底
<!--ja-->
## 含意と偽
<!--/-->

<!--en-->
The implication clause combines the two looked-up truth values with implication,
while the bottom clause assigns the false truth value without subcodes.
<!--zh-->
蕴含子句以蕴含组合两个查得的真值，而底子句不含子码，直接指派假真值。
<!--ja-->
含意の節は参照した二つの真理値を含意で組み合わせ、偽の節は部分符号を使わず偽の真理値を割り当てる。
<!--/-->

<!--en-->
Implication is stated the way the reference semantics states it, as an
implication, and not as the complement of the antecedent joined with the
consequent. The two agree classically and do not agree here. The truth algebra's
arrow is a function space, so the joined form is the weaker of the two, and
recovering the intended one from it is excluded middle for "this environment
satisfies the antecedent". A chapter that takes no classical parameter may not
quietly need one.

Said as an implication it is shorter than the joined form as well: the object
language's own arrow does the work inside the extension frame. Bottom is the
shortest clause. Its value is empty, so its relation binds no ambient set and
ignores the numeral payload.
<!--zh-->
蕴含按参照语义陈述它的方式写出，即作为一条蕴含，而非「前件的补集与后件的并」。二者在经典下一致，在此处不一致。真值代数的箭头是函数空间，故那个并式是两者中较弱的一个，而从它恢复出本意，恰是「这个环境满足前件」的排中律。一章若不取经典参数，就不可以悄悄需要一个。

写成蕴含也比写成并式更短：对象语言自己的箭头在外延框架之内完成了工作。底的子句最短；其取值为空，故关系不绑定周遭集合，并忽略数码载荷。
<!--/-->


<!--en-->
Two more pairs of readers, and the pattern does not change: an elimination
peels the frame and the relation's own binders off, an introduction puts them
back. Bottom is shorter than the connective because their relations bind
less, not because they are special.
<!--zh-->
又是两对读式，而套路不变：消去把框架与那条关系自己的诸绑定剥掉，引入再装回去。底比那个联结词短，是因为它们的关系绑得少，不是因为它们特殊。
<!--/-->

<!--en-->
## The next arity
<!--zh-->
## 下一个元数
<!--ja-->
## 次のアリティ
<!--/-->

<!--en-->
`sucAtL`{.Agda} is the internal formula saying that one numeral is the successor
of another, with an adequacy lemma identifying the represented ordinals.
<!--zh-->
`sucAtL`{.Agda} 是断言一个数码为另一数码后继的内部公式，其充分性引理对应所表示的序数。
<!--ja-->
`sucAtL`{.Agda} は一つの数項が別の数項の後者であることを述べる内部論理式であり、その妥当性補題が表される順序数を同一視する。
<!--/-->

<!--en-->
Four of the ten bind a variable, so their subformula sits one arity higher and
the table has to be consulted there. The successor reader is already written on
the hierarchy side and names no constants, so it crosses by quoting, and the
lookup at the next arity is the lookup at a fresh arity constrained to be the
successor of the one the frame bound.

The backward direction needs the successor as an element of the model, and the
numeral chapter supplies it: the model's own successor, read through the
underlying set, is the hierarchy's.
<!--zh-->
十条里有四条绑定一个变元，故它们的子公式高出一个元数，而表必须在那里被查询。后继读式在层级一侧已经写好，且不点名常元，故它经引用过河；而「下一元数处的查表」，就是「在一个新元数处的查表」加上「该元数是框架所绑元数的后继」这条约束。

反向需要那个后继作为模型的元素，而数码那一章供给它：模型自己的后继，沿底层集合读出来，就是层级的后继。
<!--/-->

```agda
sucAtL : ∀ {n} → Fin n → Fin n → Formula S n
sucAtL i j = liftFo (sucAt i j) _

sucAtL-adequate : ∀ {n} (i j : Fin n) (γ : S ^ n)
  → (γ ⊨ sucAtL i j) ≡ PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))
sucAtL-adequate i j γ =
    transferFo (sucAt i j) _ (Δ₀-sucAt i j) γ
  ∙ sucAt-adequate i j (map fst γ)
  ∙ cong₂ PairIs (lookup-fst j γ) (cong sucV (lookup-fst i γ))

```

<!--en-->
## Extending an environment
<!--zh-->
## 扩展一个环境
<!--ja-->
## 環境を拡張する
<!--/-->

<!--en-->
`consAtL`{.Agda} describes extending an environment by a new leading value, and
its adequacy lemma identifies the resulting coded environment exactly.
<!--zh-->
`consAtL`{.Agda} 描述以一个新的首值扩展环境，其充分性引理准确对应所得的码化环境。
<!--ja-->
`consAtL`{.Agda} は新しい先頭値による環境の拡張を記述し、その妥当性補題が得られる符号化環境を正確に同一視する。
<!--/-->

<!--en-->
The other half of a quantifier clause: the environment the subformula is
evaluated in is the one at hand with a value pushed on the front. That reader is
already written on the hierarchy side, and its meaning there is stated against a
meta-level family, which is exactly the form a soundness proof will want. So it
is worth quoting rather than rewriting, and quoting is free here: the reader
names no numeral, because its tag is the empty set and emptiness needs no
constant. The numeral's own constructibility comes from the numeral chapter,
which is why it sits here rather than with the codes.
<!--zh-->
量词子句的另一半：子公式所在的环境，就是手上这个环境前面推入一个取值。那条读式在层级一侧已经写好，而它在那边的含义是按元层的族陈述的，恰是可靠性证明将要采用的形式。故它值得引用而非重写，而此处引用是免费的：读式不点名任何数码，因为它的标签是空集，而空不需要常元。数码自身的可构造性来自数码那一章，这也是它住在此处而非与诸码同处的原因。
<!--/-->

```agda
numL : (k : ℕ) → InL (# k)
numL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

private
  bddSgl0 : ∀ {n} (k : Fin n) → BoundedFo InL (sgl0At k)
  bddSgl0 k = (_ , (_ , _)) , (_ , (_ , _))

  bddPair0 : ∀ {n} (k j : Fin n) → BoundedFo InL (pair0At k j)
  bddPair0 k j = (_ , (_ , _)) , ((_ , _) , (_ , ((_ , _) , (_ , _))))

  bddTag0 : ∀ {n} (s x : Fin n) → BoundedFo InL (tag0At s x)
  bddTag0 {n} s x =
      (_ , bddSgl0 {suc n} zero)
    , ( (_ , bddPair0 {suc n} zero (suc x))
      , (_ , (bddSgl0 {suc n} zero , bddPair0 {suc n} zero (suc x))) )

  bddShift : ∀ {n} (p' p : Fin n) → BoundedFo InL (shiftPairAt p' p)
  bddShift p' p = _

  bddCons : ∀ {n} (e' m e : Fin n) → BoundedFo InL (consAt e' m e)
  bddCons {n} e' m e =
      (_ , bddTag0 {suc n} zero (suc m))
    , ( (_ , (_ , bddShift {suc (suc n)} zero (suc zero)))
      , (_ , ( bddTag0 {suc n} zero (suc m)
             , (_ , bddShift {suc (suc n)} (suc zero) zero) )) )

consAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
consAtL e' m e = liftFo (consAt e' m e) (bddCons e' m e)

consAtL-adequate : ∀ {n} (e' m e : Fin n) (γ : S ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → fst (lookup e γ) ≡ env g
  → (γ ⊨ consAtL e' m e)
  ≡ PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))
consAtL-adequate e' m e γ g hE =
    transferFo (consAt e' m e) (bddCons e' m e) (Δ₀-consAt e' m e) γ
  ∙ consAt-adequate e' m e (map fst γ) g
      (lookup-fst e γ ∙ hE)
  ∙ cong₂ PairIs (lookup-fst e' γ)
      (cong (λ w → env (cons w g)) (lookup-fst m γ))

```

<!--en-->
## The unbounded quantifiers
<!--zh-->
## 无界量词
<!--ja-->
## 非有界量化子
<!--/-->

<!--en-->
The existential and universal clauses extend each environment by every carrier
element, look up the subformula there, and aggregate the resulting truth values.
<!--zh-->
存在与全称子句以载体的每个元素扩展各环境，在扩展环境处查找子公式，并汇总所得真值。
<!--ja-->
存在量化子と全称量化子の節は、各環境を台のすべての要素で拡張し、その環境で部分論理式を参照して、得られた真理値を集約する。
<!--/-->

<!--en-->
An environment satisfies an existential exactly when some value from the
structure, pushed onto the front, gives an environment satisfying the body, and
the body's value is recorded one arity higher. So the clause binds the value at
the next arity, binds the ambient set at its own arity, and then describes its
own value by extension: the environments in the ambient set that can be extended
into the body's.

Nine things are in scope by the innermost point, which is the deepest the chapter
goes, and every one of them was needed: the code and its parts from the frame,
the two values, the environment being classified, the value pushed on, and the
extended environment. The universal clause turns the two innermost quantifiers
around, each taking the connective its form asks for: a conjunction under the
existential, an implication under the universal.

Nothing else moves, and the outermost conjunct in particular does not. The one
that puts the environment in the ambient set is a conjunction in **both**, as it
is in every clause written in this frame, and the reason is worth stating because
getting it wrong is not a wrong clause but an unsatisfiable one. `extAt`{.Agda}
makes a value the set of exactly what its condition holds of; a condition that
could hold outside the ambient set would be asking for a value that is not a set.
<!--zh-->
一个环境满足存在量词，恰在结构中的某个取值被推到它前面、所得的环境满足主体时，而主体的取值记录在高一个元数处。故该子句绑定下一元数处的取值，绑定它自己元数处的周遭集合，然后以外延描述自己的取值：周遭集合中那些能被扩展进主体取值里的环境。

到最内处共有九样在作用域中，那是本章所及的最深处，而每一样都是必需的：来自框架的那个码与它的诸部分、两个取值、被分类的那个环境、被推入的取值、以及扩展后的环境。全称子句把最内两个量词调转，每个都带上其形式所要的联结词：存在之下是合取，全称之下是蕴含。

除此之外别无变动，尤其是最外那个合取项不动。把环境放进周遭集合的那一项，在**两条**里都是合取，一如这个框架下写出的每一条子句；而这个理由值得说出来，因为弄错它得到的不是一条错的子句，而是一条无法满足的子句。`extAt`{.Agda} 使一个取值恰为「使那个条件成立的东西」之集；一个可能在周遭集合之外成立的条件，等于在索要一个并非集合的取值。
<!--/-->


At the innermost point: `e'` = 0, `m` = 1, `e` = 2, `E` = 3, `ya` = 4.

<!--en-->
The quantifier clauses read the same way, and the tag and the body are what a
caller supplies, so one pair of readers serves both. The subvalue sits an arity
up, which is the only difference from a same-arity lookup.
<!--zh-->
两条量词子句读法相同，而标签与主体由调用方提供，故一对读式服务两者。子取值高一个元数，这也是它与同元数查表唯一的差别。
<!--/-->

<!--en-->
## Evaluating a term, and the atoms
<!--zh-->
## 求一个词项的值，与两个原子
<!--ja-->
## 項の評価と二つの原子論理式
<!--/-->

<!--en-->
The term-evaluation expression reads a coded term in an environment, and the
membership and equality clauses compare the two evaluated values in the model.
<!--zh-->
词项求值表达式在环境中读取码化词项，而隶属与相等子句在模型内比较两个求得的值。
<!--ja-->
項評価の表現は環境内で符号化された項を読み、所属と等号の節はモデル内で二つの評価値を比較する。
<!--/-->

<!--en-->
The last thing the chapter lacked, and the place a wrong sentence sat for a day.
A term is a variable **or a constant**, so a reader for its value has two cases,
not one: a variable's code is the variable tag over a key and its value is what
the environment records at that key; a constant's code is the constant tag over
the constant itself, and its value is that, in any environment at all.

The one-case version was written when the alphabet was empty, and the sentence
that justified it, "a term of a parameter-free formula is a variable", stayed
true of the alphabet and stopped being true of the chapter. What made it a defect
rather than a gap is that this reader sits under `extAt`{.Agda}, which asserts
**both** directions: a constant was not left unconstrained, its value was pinned
to the empty set. And the case is the normal form rather than a corner, since
relativization gives every bounded quantifier a constant bound.

So the reader is stated with a characterization this time, in both directions,
which is what makes the shape of the defect impossible to reintroduce silently.

The atoms then read both sides and compare them. Their payload is a pair of
*term* codes, at which the table has nothing, which is why the frame was made not
to look there; here is where that pays. The two atoms differ in one atom of the
object language, membership against equality, so they share everything else.
<!--zh-->
本章尚缺的最后一件，也是一句错话待了一天的地方。一个词项是变元**或常元**，故读它取值的读式有两种情形，而不是一种：变元的码是「变元标签架在一个键之上」，取值是环境在该键处记录的东西；常元的码是「常元标签架在那个常元自己之上」，而它的取值就是那个常元，在任何环境中都一样。

一情形的版本写于字母表为空之时，而为它开脱的那句话「无参公式的一个词项是变元」，对字母表仍为真，对本章已不再为真。使它成为**缺陷**而非空缺的，是这条读式坐在 `extAt`{.Agda} 之下，而后者断言**双向**：一个常元并未被放任不管，它的取值被钉成了空集。而这一情形是常态，而不是边角，因为相对化给每条有界量词都配一个常元界。

故这次这条读式带着一份两个方向的刻画写出，而正是那份刻画使这种形状的缺陷不可能再悄悄回来。

两个原子随后读出两侧并加以比较。它们的载荷是一对**词项**码，而表在那里什么也没有，这正是当初把框架做成不往那里看的原因；此处便是它的回报。两个原子只差对象语言的一个原子，隶属对相等，其余全部共享。
<!--/-->


At the innermost point: `w` = 0, `v` = 1, `e` = 2, `E` = 3, `yc` = 4, `b` = 5,
`a` = 6.


<!--en-->
## The bounded quantifiers
<!--zh-->
## 有界量词
<!--ja-->
## 有界量化子
<!--/-->

<!--en-->
The bounded existential and universal clauses evaluate the bound term first,
then aggregate subformula values only over members of that resulting set.
<!--zh-->
有界存在与全称子句先求界词项之值，再仅对所得集合的成员汇总子公式取值。
<!--ja-->
有界な存在量化子と全称量化子の節は、まず境界となる項を評価し、その結果の集合の要素だけについて部分論理式の値を集約する。
<!--/-->

<!--en-->
The last two, and they need nothing new. A bounded quantifier's payload is a term
code paired with a formula code, so the bound is evaluated in the environment and
the body's value is read one arity higher; then the values pushed on are the ones
lying in **both** the carrier and the bound, and the extended environments are
looked for in the body's value.

Ranging over the carrier as well as the bound is not redundant. The reference
semantics quantifies over the carrier and guards by membership in the bound, and
a bound may perfectly well have members outside the carrier; quantifying over the
bound alone would then demand entries the table does not have.

Every piece has appeared: the next-arity lookup for the body, the ambient set for
the extension frame, term evaluation for the bound, and environment extension for
the step. The two differ, as the unbounded pair did, only in which quantifier
each of the three innermost binders carries.
<!--zh-->
最后两条，而它们不需要任何新东西。有界量词的载荷是「词项码与公式码的对」，故那个界在环境中求值，而主体的取值在高一个元数处读出；随后被推入的取值取自**载体与那个界之交**，再到主体的取值里去找扩展后的环境。

同时遍历载体与那个界并非冗余。参照语义是在载体上作量化，再以「属于那个界」设防，而一个界完全可以有落在载体之外的成员；只在那个界上作量化，就会索要表所没有的条目。

每一件都已登场：主体所需的下一元数查表、外延框架所需的周遭集合、界所需的词项求值、以及推入所需的环境扩展。两条之间的差别，与无界的那一对一样，只在最内三个绑定各自带的是哪个量词。
<!--/-->


At depth 7: `E` = 0, `yb` = 1, `yc` = 2, `b` = 3, `a` = 4, `ar` = 5, `c` = 6.


At depth 9: `w` = 0, `e` = 1, `a` = 6.


At depth 11: `e'` = 0, `m` = 1, `e` = 3, `yb` = 5.


Inside the bound's quantifier, at depth 10: `m` = 0, `w` = 1.

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
These expressions give the coded recursion a common vocabulary for syntax
shape, environments, lookup, term evaluation, and every logical constructor.
<!--zh-->
这些表达式为码化递归提供一套共用词汇，覆盖语法形状、环境、查找、词项求值与每个逻辑构造器。
<!--ja-->
これらの表現は、構文形、環境、参照、項評価、すべての論理構成子について、符号化再帰に共通の語彙を与える。
<!--/-->

<!--en-->
One expression reader now handles slots, literals, numerals, and nested pairs.
The chapter then assembles it with the model dictionary to describe extensions,
environments, arities, tags, and the relation patterns used by recursion clauses.
Closure of the code domain is the next, separate requirement.
<!--zh-->
一条表达式读式现在统一处理位置、字面常元、数码与嵌套配对。本章再把它与模型词典组合，用来描述外延、环境、元数、标签以及递归子句所需的关系形状。码域对子码的封闭性是下一章的独立要求。
<!--/-->
