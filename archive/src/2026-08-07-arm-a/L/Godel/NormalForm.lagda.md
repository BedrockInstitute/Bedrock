# The normal form

<!--en-->
The theorem the part exists for: **every satisfaction set is reachable by a
finite composition of the operations**, applied to the carrier and finitely
many of its members. The composition terms are a small syntax with no
binders; a term denotes a set by structural recursion; and reachability of a
set is a term with a denotation path. The proof is one induction over the
formula, and every case is a case equation of the satisfaction chapter read
off: the connectives compose the induction hypotheses, the quantifiers add a
shift or a difference, and the atoms are leaves, assembled from the
selections and, where a constant occurs, from the reductions through the
exceptional atom. Nothing here is classical except the two cases that were
already classical, and they enter through the same one assumption.
<!--zh-->
本部为之存在的定理：**每个满足集都可由运算的有穷复合达到**，施于载体与它的有穷多个成员。复合项是一个无绑定子的小语法；项经结构递归指称一个集合；集合的可达性就是一个项加一条指称路径。证明是对公式的一次归纳，而每个情形都是满足关系那一章某条情形等式的读出：联结词复合归纳假设，量词添一次移位或一次差，原子是叶子，由诸选择装配，遇常元则经例外原子的化归装配。除本来就经典的那两个情形外，此处无一经典，而它们经由同一份假设进场。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.NormalForm {ℓ : Level} where

open import Base.Classical using ( LEM )

open import FOL.Syntax
  using ( Formula; Term; var; con
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈; ⊤̇; ⊥̇ )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Godel.Operations {ℓ}
  using ( _∪_; _∩_; _∖_; ∖-self
        ; selectMember; selectEqual; extendFamily; shiftDown )
open import L.Godel.Tuples {ℓ} using ( allTuples; allTuples-zero; allTuples-suc )
open import L.Godel.Satisfaction {ℓ}
  using ( satSet; sat-⊥; sat-⊤; sat-∧; sat-∨; sat-¬; sat-∈vv; sat-≐vv
        ; sat-≐vc; sat-∃
        ; red-∈cv; red-∈vc; red-∈cc; red-≐cv; red-≐cc; red-∃∈; red-∀∈
        ; module Classical )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( #_ )
```

<!--en-->
## Terms, denotation, reachability

The composition terms have two leaves, the carrier and a member of it, and
one node per operation the induction consumes; an operation nothing below
composes is not a constructor, which is what will let the closure chapter
read its basis off this syntax. Denotation is structural. A set is
**reachable** when some term denotes it on the nose, and reachability
transports along any identity, which is the one-line lemma every case ends
with.
<!--zh-->
## 项、指称、可达性

复合项有两种叶，载体与它的一个成员，每个被归纳消费的运算一个节点；下面无人复合的运算不设构造子，而这正是将来闭包那一章从这套语法上读出其运算基的凭据。指称是结构性的。当某个项不多不少指称一个集合时，该集合**可达**，而可达性沿任何等同输运，即每个情形收尾的那条单行引理。
<!--/-->

```agda
-- perf: the term syntax is parameterized by an abstract parameter type
-- and applied at the carrier's member type below; declared inside the
-- carrier module, the positivity check normalizes the member type's
-- presentation and runs 346 s, abstract it is instant
data GT (P : Type ℓ) : Type ℓ where
  carrier : GT P
  param   : P → GT P
  pairT unionT intersectT diffT extendFamilyT : GT P → GT P → GT P
  selectMemberT selectEqualT : GT P → GT P → GT P → GT P
  bigUnionT shiftDownT : GT P → GT P

module _ (A : V ℓ) where
  private
    κ : ⟪ A ⟫ → V ℓ
    κ = ⟪ A ⟫↪

  ⟦_⟧ᵍ : GT ⟪ A ⟫ → V ℓ
  ⟦ carrier ⟧ᵍ = A
  ⟦ param m ⟧ᵍ = κ m
  ⟦ pairT s t ⟧ᵍ = ⁅ ⟦ s ⟧ᵍ , ⟦ t ⟧ᵍ ⁆
  ⟦ unionT s t ⟧ᵍ = ⟦ s ⟧ᵍ ∪ ⟦ t ⟧ᵍ
  ⟦ intersectT s t ⟧ᵍ = ⟦ s ⟧ᵍ ∩ ⟦ t ⟧ᵍ
  ⟦ diffT s t ⟧ᵍ = ⟦ s ⟧ᵍ ∖ ⟦ t ⟧ᵍ
  ⟦ extendFamilyT s t ⟧ᵍ = extendFamily ⟦ s ⟧ᵍ ⟦ t ⟧ᵍ
  ⟦ selectMemberT s t u ⟧ᵍ = selectMember ⟦ s ⟧ᵍ ⟦ t ⟧ᵍ ⟦ u ⟧ᵍ
  ⟦ selectEqualT s t u ⟧ᵍ = selectEqual ⟦ s ⟧ᵍ ⟦ t ⟧ᵍ ⟦ u ⟧ᵍ
  ⟦ bigUnionT s ⟧ᵍ = ⋃ ⟦ s ⟧ᵍ
  ⟦ shiftDownT s ⟧ᵍ = shiftDown ⟦ s ⟧ᵍ

  Reach : V ℓ → Type (ℓ-suc ℓ)
  Reach X = Σ[ t ∈ GT ⟪ A ⟫ ] (⟦ t ⟧ᵍ ≡ X)

  reachBy : {X Y : V ℓ} → Reach X → Y ≡ X → Reach Y
  reachBy (t , e) eq = t , e ∙ sym eq
```

<!--en-->
## The stock of reachable sets

The empty set is the carrier's difference with itself; a numeral steps by
von Neumann, which is one big union of a pair; a singleton is the pair of a
set with itself; and the set of all assignments steps by the family
extension, with the pair of empty sets at length zero. Each is the tuple or
operations chapter's equation, packaged as a term.
<!--zh-->
## 可达集合的存货

空集是载体与自身的差；数码按冯·诺伊曼走步，即一个对的一次大并；单点集是集合与自身的对；全体赋值之集按族扩张走步，长度零处是空集之对。每一件都是元组或运算那一章的等式，打包成一个项。
<!--/-->

```agda
  reach-∅ : Reach ∅
  reach-∅ = diffT carrier carrier , ∖-self A

  reach-# : (k : ℕ) → Reach (# k)
  reach-# zero = reach-∅
  reach-# (suc k) =
    let (t , e) = reach-# k
    in bigUnionT (pairT t (pairT t t))
     , cong ⋃_ (cong₂ ⁅_,_⁆ e (cong₂ ⁅_,_⁆ e e ∙ pair-singleton (# k)))

  reach-sing : {z : V ℓ} → Reach z → Reach ⁅ z ⁆s
  reach-sing {z} (t , e) = pairT t t , cong₂ ⁅_,_⁆ e e ∙ pair-singleton z

  reach-all : (n : ℕ) → Reach (allTuples A n)
  reach-all zero =
    pairT (diffT carrier carrier) (diffT carrier carrier)
    , cong₂ ⁅_,_⁆ (∖-self A) (∖-self A) ∙ sym (allTuples-zero A)
  reach-all (suc n) =
    let (t , e) = reach-all n
    in extendFamilyT t carrier
     , cong (λ z → extendFamily z A) e ∙ sym (allTuples-suc A n)
```

<!--en-->
## The atoms, as leaves

One lemma per atom, by cases on the two terms. Two variables is the
selection with singleton numeral keys. A constant meets a variable, or a
constant, through the reductions: the reduced formula is an existential of a
conjunction whose parts are atoms already covered, so its satisfaction set is
the shift of an intersection of reachable sets, and the constant itself
enters as a parameter leaf under the exceptional atom's equation. The
deepest case, a membership of two constants, unfolds through two reductions.
<!--zh-->
## 原子，作为叶子

每个原子一条引理，对两个词项分情形。两变元就是带单点数码键的选择。常元与变元相遇，或与常元相遇，经化归：化归后的公式是某个合取的存在式，其零件是已覆盖的原子，故其满足集是可达集合之交的移位，而常元自身经例外原子的等式以参数叶进场。最深的情形，两个常元的隶属，穿过两次化归展开。
<!--/-->

```agda
  private
    reach-≐vc : {n : ℕ} (i : Fin n) (a : ⟪ A ⟫)
              → Reach (satSet A (var i ≐ con a))
    reach-≐vc {n} i a =
      let (tE , eE) = reach-all n
          (ta , ea) = reach-sing {z = κ a} (param a , refl)
          (ti , ei) = reach-sing (reach-# (suc (toℕ i)))
          (tz , ez) = reach-sing (reach-# 0)
      in shiftDownT (selectEqualT (extendFamilyT tE ta) ti tz)
       , (λ x → shiftDown (selectEqual (extendFamily (eE x) (ea x))
                            (ei x) (ez x)))
       ∙ sym (sat-≐vc A i a)

    reach-∈vv : {n : ℕ} (i j : Fin n)
              → Reach (satSet A (var i ∈̇ var j))
    reach-∈vv {n} i j =
      let (tE , eE) = reach-all n
          (ti , ei) = reach-sing (reach-# (toℕ i))
          (tj , ej) = reach-sing (reach-# (toℕ j))
      in selectMemberT tE ti tj
       , (λ x → selectMember (eE x) (ei x) (ej x))
       ∙ sym (sat-∈vv A i j)

    reach-≐vv : {n : ℕ} (i j : Fin n)
              → Reach (satSet A (var i ≐ var j))
    reach-≐vv {n} i j =
      let (tE , eE) = reach-all n
          (ti , ei) = reach-sing (reach-# (toℕ i))
          (tj , ej) = reach-sing (reach-# (toℕ j))
      in selectEqualT tE ti tj
       , (λ x → selectEqual (eE x) (ei x) (ej x))
       ∙ sym (sat-≐vv A i j)

    exists∧ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ (suc n))
            → Reach (satSet A φ) → Reach (satSet A ψ)
            → Reach (satSet A (∃̇ (φ ∧̇ ψ)))
    exists∧ φ ψ (t₁ , e₁) (t₂ , e₂) =
      shiftDownT (intersectT t₁ t₂)
      , cong shiftDown (cong₂ _∩_ e₁ e₂ ∙ sym (sat-∧ A φ ψ))
      ∙ sym (sat-∃ A (φ ∧̇ ψ))

    reachAtom≐ : {n : ℕ} (t u : Term ⟪ A ⟫ n)
               → Reach (satSet A (t ≐ u))
    reachAtom≐ (var i) (var j) = reach-≐vv i j
    reachAtom≐ (var i) (con a) = reach-≐vc i a
    reachAtom≐ (con a) (var i) = reachBy (reach-≐vc i a) (red-≐cv A i a)
    reachAtom≐ (con a) (con b) = reachBy
      (exists∧ (var zero ≐ con a) (var zero ≐ con b)
        (reach-≐vc zero a) (reach-≐vc zero b))
      (red-≐cc A a b)

    reachAtom∈ : {n : ℕ} (t u : Term ⟪ A ⟫ n)
               → Reach (satSet A (t ∈̇ u))
    reachAtom∈ (var i) (var j) = reach-∈vv i j
    reachAtom∈ (var i) (con a) = reachBy
      (exists∧ (var zero ≐ con a) (var (suc i) ∈̇ var zero)
        (reach-≐vc zero a) (reach-∈vv (suc i) zero))
      (red-∈vc A i a)
    reachAtom∈ (con a) (var j) = reachBy
      (exists∧ (var zero ≐ con a) (var zero ∈̇ var (suc j))
        (reach-≐vc zero a) (reach-∈vv zero (suc j)))
      (red-∈cv A j a)
    reachAtom∈ (con a) (con b) = reachBy
      (exists∧ (var zero ≐ con b) (con a ∈̇ var zero)
        (reach-≐vc zero b)
        (reachBy
          (exists∧ (var zero ≐ con a) (var zero ∈̇ var (suc zero))
            (reach-≐vc zero a) (reach-∈vv zero (suc zero)))
          (red-∈cv A zero a)))
      (red-∈cc A a b)
```

<!--en-->
## The theorem

One induction, one assumption, and every case a read-off. The two classical
cases open the satisfaction chapter's classical module, and the bounded
quantifiers pass through their reductions to a guard the atom lemmas already
reach at any pair of terms.
<!--zh-->
## 定理

一次归纳，一份假设，每个情形一次读出。两个经典情形打开满足关系那一章的经典模块，有界量词经各自的化归落到一个守卫上，而原子引理在任意一对词项处都够得着它。
<!--/-->

```agda
  module WithLEM (lem : LEM (ℓ-suc ℓ)) where
    private module C = Classical A lem

    normalForm : {n : ℕ} (φ : Formula ⟪ A ⟫ n) → Reach (satSet A φ)
    normalForm ⊥̇ = reachBy reach-∅ (sat-⊥ A)
    normalForm {n} ⊤̇ = reachBy (reach-all n) (sat-⊤ A)
    normalForm (t ∈̇ u) = reachAtom∈ t u
    normalForm (t ≐ u) = reachAtom≐ t u
    normalForm (φ ∧̇ ψ) =
      let (t₁ , e₁) = normalForm φ
          (t₂ , e₂) = normalForm ψ
      in intersectT t₁ t₂
       , cong₂ _∩_ e₁ e₂ ∙ sym (sat-∧ A φ ψ)
    normalForm (φ ∨̇ ψ) =
      let (t₁ , e₁) = normalForm φ
          (t₂ , e₂) = normalForm ψ
      in unionT t₁ t₂
       , cong₂ _∪_ e₁ e₂ ∙ sym (sat-∨ A φ ψ)
    normalForm {n} (¬̇ φ) =
      let (tA , eA) = reach-all n
          (t , e) = normalForm φ
      in diffT tA t
       , cong₂ _∖_ eA e ∙ sym (sat-¬ A φ)
    normalForm {n} (φ ⇒̇ ψ) =
      let (tA , eA) = reach-all n
          (t₁ , e₁) = normalForm φ
          (t₂ , e₂) = normalForm ψ
      in diffT tA (intersectT t₁ (diffT tA t₂))
       , cong₂ _∖_ eA
           (cong₂ _∩_ e₁ (cong₂ _∖_ eA e₂))
       ∙ sym (C.sat-⇒ φ ψ)
    normalForm (∃̇ φ) =
      let (t , e) = normalForm φ
      in shiftDownT t , cong shiftDown e ∙ sym (sat-∃ A φ)
    normalForm {n} (∀̇ φ) =
      let (tA , eA) = reach-all n
          (tS , eS) = reach-all (suc n)
          (t , e) = normalForm φ
      in diffT tA (shiftDownT (diffT tS t))
       , cong₂ _∖_ eA (cong shiftDown (cong₂ _∖_ eS e))
       ∙ sym (C.sat-∀ φ)
    normalForm (∃̇∈ t φ) = reachBy
      (let (t₁ , e₁) = reachAtom∈ (var zero) (renameTm suc t)
           (t₂ , e₂) = normalForm φ
       in shiftDownT (intersectT t₁ t₂)
        , cong shiftDown
            (cong₂ _∩_ e₁ e₂
             ∙ sym (sat-∧ A (var zero ∈̇ renameTm suc t) φ))
        ∙ sym (sat-∃ A ((var zero ∈̇ renameTm suc t) ∧̇ φ)))
      (red-∃∈ A t φ)
    normalForm {n} (∀̇∈ t φ) = reachBy
      (let (tA , eA) = reach-all n
           (tS , eS) = reach-all (suc n)
           (t₁ , e₁) = reachAtom∈ (var zero) (renameTm suc t)
           (t₂ , e₂) = normalForm φ
       in diffT tA (shiftDownT
            (diffT tS (diffT tS (intersectT t₁ (diffT tS t₂)))))
        , cong₂ _∖_ eA
            (cong shiftDown (cong₂ _∖_ eS
              ( cong₂ _∖_ eS (cong₂ _∩_ e₁ (cong₂ _∖_ eS e₂))
              ∙ sym (C.sat-⇒ (var zero ∈̇ renameTm suc t) φ) )))
        ∙ sym (C.sat-∀ ((var zero ∈̇ renameTm suc t) ⇒̇ φ)))
      (red-∀∈ A t φ)
```

<!--en-->
## Recap

The composition terms `GT`{.Agda} with their denotation, reachability
`Reach`{.Agda}, the stock `reach-∅`{.Agda}, `reach-#`{.Agda},
`reach-sing`{.Agda} and `reach-all`{.Agda}, and the theorem
`normalForm`{.Agda}: every satisfaction set over the carrier is denoted by a
composition term over the carrier and its members, under the one classical
assumption the book already carries. This is what the closure chapter will
close under, and what makes a definable subset something a set can reach in
finitely many watched steps.
<!--zh-->
## 小结

复合项 `GT`{.Agda} 及其指称、可达性 `Reach`{.Agda}、存货 `reach-∅`{.Agda}、`reach-#`{.Agda}、`reach-sing`{.Agda} 与 `reach-all`{.Agda}，以及定理 `normalForm`{.Agda}：载体之上的每个满足集，都由载体与其成员之上的一个复合项所指称，凭的是本书已携带的那一份经典假设。这就是闭包那一章将要对之封闭的东西，也是使可定义子集成为「集合能以有穷多可旁观步骤达到之物」的东西。
<!--/-->
