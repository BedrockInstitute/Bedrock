# The table satisfies the clauses

<!--en-->
The existence half. The table built by recursion on a formula of the
meta-language really does stand in the relation the internal clauses describe,
one clause at a time.

Each verification is the same four moves, and three of them are already built.
The index is inverted to the formula whose key it is; the formula's constructor
is computed from the clause's tag; the recorded values are identified with the
values the meta-level recursion built. What is left over, and the only part that
is new, is a set identity: that the value at a conjunction really is the
intersection of the values below it, and so on for the other eleven.

Those identities are cheap for a reason worth saying plainly. The meta-level
recursion defined the value at a constructor by separating the ambient set by a
condition naming the values below, so the identity is that condition read back,
which is what the separation's own specification says.
<!--zh-->
存在性的那一半。沿元语言公式递归造出的那张表，确实处在内部诸子句所描述的关系之中，一条子句一条子句地。

每次验证都是同样四步，而其中三步已经造好。索引被求逆回「它是谁的键」的那条公式；该公式的构造子由子句的标签算出；被记录的诸取值与元语言递归造出的诸取值被认同起来。剩下的、也是唯一新的那一步，是一条集合等式：合取处的取值确实是它下面两个取值的交，其余十一条同理。

那些等式便宜，而理由值得直说。元语言的递归是「用一条点名下层诸取值的条件雕出周遭集合」来定义某构造子处的取值的，故那条等式就是把那条条件读回来，而那正是那次分离自己的规格所说的话。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Sound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( module LCode; prʟ; prʟ-fst; andClauseAt; orClauseAt
        ; propClause-in; interAt; unionAt; envSetAt; envOverAt
        ; negClauseAt; negClause-in; impClauseAt; impClause-in
        ; topClauseAt; topClause-in; botClauseAt; botClause-in
        ; tmValAt; tmValAt-var; tmValAt-con; tmValAt-out
        ; memClauseAt; eqClauseAt; memRel; eqRel; atomClause-in
        ; existClauseAt; forallClauseAt; quantClause-in
        ; allInClauseAt; exInClauseAt; bndClause-in
        ; bodyAll; bodyAll-in; bodyAll-out; bodyEx; bodyEx-in; bodyEx-out
        ; body∃; body∃-in; body∃-out; body∀; body∀-in; body∀-out
        ; consAtL-transport
        ; atomBody; atomBody-in; atomBody-out
        ; envOverAt-transport; extAt-out; extAt-in; numL
        ; yc7; ya7; yb7 )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; Sat-mem; tmIs; tmIs-var-in; tmIs-var-out; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
        ; cond∀∈-in; cond∀∈-out; cond∃∈-in; cond∃∈-out )
open import L.Coding.EnvSet {ℓ} lem
  using ( envSet; envSet-in; envSet-out; envS; envOver; Ix; module Recover )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; keyʟ-shape; satTable; slot; slot-inv; entry-out )

open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Empty using ( isProp⊥ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Nat using ( snotz; znots )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## A clause's ambient set is the ambient set
<!--zh-->
## 子句的周遭集合就是那个周遭集合
<!--/-->

<!--en-->
Seven of the twelve bind their own ambient set and say only that its members are
the environments at the code's arity over the carrier. What a proof needs is that
this is the set the previous chapter built, and it is, in both directions: a
member of the clause's set satisfies the description, so it is recovered as an
environment; an environment satisfies the description, so it is a member.

Neither direction re-proves anything. The description moves between the clause's
frame and the chapter's by the transport, and the two halves of the recovery are
already there.
<!--zh-->
十二条里有七条绑定自己的周遭集合，只说它的成员就是「该码元数处、载体之上」的诸环境。证明需要的是「这就是上一章造出的那个集合」，而它确实是，两个方向都成立：那个子句的集合的成员满足那条描述，故被恢复为一个环境；而一个环境满足那条描述，故是它的成员。

两个方向都不重证任何东西。那条描述经搬运在子句的框架与本章的框架之间移动，而恢复的两半早已就位。
<!--/-->

```agda
private
  nn : ℕ → S
  nn j = # j , numL j

module Ambient (B : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k) (m : ℕ)
  (qd : fst (lookup di γ) ≡ # m) (qb : fst (lookup bi γ) ≡ fst B)
  (hE : ⟨ γ ⊨ envSetAt Ei di bi ⟩) where

  into : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
       → ⟨ fst z ∈ fst (envSet B m) ⟩
  into z hz = subst (λ w → ⟨ w ∈ fst (envSet B m) ⟩)
    (sym (Recover.recovers B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov))
    (envSet-in B (Recover.g B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov))
    where
    ov : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    ov = extAt-out Ei (envOverAt zero (suc di) (suc bi)) γ hE z hz

  asEnv : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
        → Σ[ g ∈ Ix B m ] (fst z ≡ fst (envS B g))
  asEnv z hz = Recover.g B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov
             , Recover.recovers B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov
    where
    ov : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    ov = extAt-out Ei (envOverAt zero (suc di) (suc bi)) γ hE z hz

  outof : (z : S) → ⟨ fst z ∈ fst (envSet B m) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
  outof z hz = PT.rec (snd (fst z ∈ fst (lookup Ei γ)))
    (λ { (g , eg) →
      extAt-in Ei (envOverAt zero (suc di) (suc bi)) γ hE z
        (envOverAt-transport (B ∷ nn m ∷ envS B g ∷ []) (z ∷ γ)
          (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
          (sym eg) (sym qd) (sym qb)
          (envOver B g)) })
    (envSet-out B m z hz)
```

<!--en-->
## The environment a clause is read in
<!--zh-->
## 子句被读入的那个环境
<!--/-->

<!--en-->
Three slots, in the order the clauses take them: the index, the table, the
carrier.
<!--zh-->
三个槽位，按诸子句取用的次序：索引、表、载体。
<!--/-->

<!--en-->
## The two term readers agree
<!--zh-->
## 两条词项读式一致
<!--/-->

<!--en-->
A clause reads a term's value off its code, because a clause has only the code;
the meta-level recursion reads it off the term, because it has the term. The two
have to say the same thing, and saying so is the only place in this chapter where
the two tags of a term code are separated: a variable's code is not a constant's,
because numerals are distinct, and that is what rules out the wrong disjunct.
<!--zh-->
子句从词项的**码**读出它的取值，因为子句只有码；元语言的递归从**词项**读出它，因为它有词项。两者必须说同一件事，而把这件事说出来，是本章唯一分开词项码那两个标签的地方：变元的码不是常元的码，因为诸数码两两相异，而正是这一点排除了错的那个析取项。
<!--/-->

```agda
module TermAgree {k : ℕ} (γ : S ^ k) (ti ei vi : Fin k) where
  private
    Tc = fst (lookup ti γ)
    Ev = fst (lookup ei γ)
    Vl = fst (lookup vi γ)

  fromVar : (i : ℕ) → Tc ≡ pr (# 1) (# i)
          → ⟨ pr (# i) Vl ∈ Ev ⟩ → ⟨ γ ⊨ tmValAt ti ei vi ⟩
  fromVar i q m = tmValAt-var ti ei vi γ (nn i) q m

  fromCon : (x : V ℓ) → Tc ≡ pr (# 0) x → Vl ≡ x → ⟨ γ ⊨ tmValAt ti ei vi ⟩
  fromCon x q e = tmValAt-con ti ei vi γ
    (q ∙ cong (pr (# 0)) (sym e))

  toVar : (i : ℕ) → Tc ≡ pr (# 1) (# i) → ⟨ γ ⊨ tmValAt ti ei vi ⟩
        → ⟨ pr (# i) Vl ∈ Ev ⟩
  toVar i q h = PT.rec (snd (pr (# i) Vl ∈ Ev))
    (λ { (inl (x , (qx , mx))) →
           subst (λ w → ⟨ pr w Vl ∈ Ev ⟩) (pr-inj (sym qx ∙ q) .snd) mx
       ; (inr qc) → Empty.rec (snotz (#-inj 1 0 (pr-inj (sym q ∙ qc) .fst))) })
    (tmValAt-out ti ei vi γ h)

  toCon : (x : V ℓ) → Tc ≡ pr (# 0) x → ⟨ γ ⊨ tmValAt ti ei vi ⟩ → Vl ≡ x
  toCon x q h = PT.rec (setIsSet Vl x)
    (λ { (inl (y , (qy , _))) →
           Empty.rec (znots (#-inj 0 1 (pr-inj (sym q ∙ qy) .fst)))
       ; (inr qc) → sym (pr-inj (sym q ∙ qc) .snd) })
    (tmValAt-out ti ei vi γ h)
```

<!--en-->
Put together, a meta term reads the same on both sides. The clause's reader is
handed the code and the two slots its own frame put things in; the recursion's
reader is handed the term and its own two slots; the statement says they agree
whenever the slots agree. Two cases, and each is the four readings above composed
with the two of `tmIs`{.Agda}.
<!--zh-->
合起来说：一个元语言的词项在两侧读起来一样。子句那条读式拿到的是码、以及它自己框架给的两个槽位；递归那条读式拿到的是词项与它自己的两个槽位；而这条陈述说：只要槽位一致，两者就一致。两种情形，而每种都是上面那四条读法与 `tmIs`{.Agda} 那两条的复合。
<!--/-->

```agda
private
  tmCode : ∀ {m} (t : Term S m)
         → Σ[ j ∈ ℕ ] (Σ[ x ∈ V ℓ ]
             ((fst LCode.⌜ t ⌝ᵗ ≡ pr (# j) x)))
  tmCode (con c) = 0 , fst c
    , (prʟ-fst (numeralL 0) c ∙ cong (λ w → pr w (fst c)) (numeralL-fst 0))
  tmCode (var i) = 1 , # (toℕ i)
    , (prʟ-fst (numeralL 1) (numeralL (toℕ i))
      ∙ cong₂ pr (numeralL-fst 1) (numeralL-fst (toℕ i)))

termAgree : ∀ {m} (t : Term S m) {k k'} (γ : S ^ k) (ti ei vi : Fin k)
            (γ' : S ^ k') (vi' ei' : Fin k')
          → fst (lookup ti γ) ≡ fst LCode.⌜ t ⌝ᵗ
          → fst (lookup ei γ) ≡ fst (lookup ei' γ')
          → fst (lookup vi γ) ≡ fst (lookup vi' γ')
          → (⟨ γ ⊨ tmValAt ti ei vi ⟩ → ⟨ γ' ⊨ tmIs t vi' ei' ⟩)
          × (⟨ γ' ⊨ tmIs t vi' ei' ⟩ → ⟨ γ ⊨ tmValAt ti ei vi ⟩)
termAgree (var i) γ ti ei vi γ' vi' ei' qt qe qv =
    (λ h → tmIs-var-in i γ' vi' ei'
      (subst2 (λ p q → ⟨ pr (# (toℕ i)) p ∈ q ⟩) qv qe
        (TermAgree.toVar γ ti ei vi (toℕ i) (qt ∙ tmCode (var i) .snd .snd) h)))
  , (λ h → TermAgree.fromVar γ ti ei vi (toℕ i)
      (qt ∙ tmCode (var i) .snd .snd)
      (subst2 (λ p q → ⟨ pr (# (toℕ i)) p ∈ q ⟩) (sym qv) (sym qe)
        (tmIs-var-out i γ' vi' ei' h)))
termAgree {m} (con c) γ ti ei vi γ' vi' ei' qt qe qv =
    (λ h → sym qv ∙ TermAgree.toCon γ ti ei vi (fst c)
             (qt ∙ tmCode {m} (con c) .snd .snd) h)
  , (λ h → TermAgree.fromCon γ ti ei vi (fst c)
      (qt ∙ tmCode {m} (con c) .snd .snd) (qv ∙ h))
```

<!--en-->
## The environment a clause is read in, continued
<!--zh-->
## 子句被读入的那个环境 (续)
<!--/-->

```agda
module _ (B : S) {n : ℕ} (φ : Formula S n) where
  private
    δ : S ^ 3
    δ = B ∷ satTable B φ ∷ slot B φ ∷ []

    Ci Ti Bi : Fin 3
    Ci = suc (suc zero)
    Ti = suc zero
    Bi = zero

    ai0 : ∀ {j} → Fin (suc j)
    ai0 = zero
    ai1 : ∀ {j} → Fin (suc (suc j))
    ai1 = suc zero
    ai2 : ∀ {j} → Fin (suc (suc (suc j)))
    ai2 = suc (suc zero)
    ai5 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc j))))))
    ai5 = suc (suc (suc (suc (suc zero))))
    ai6 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc (suc j)))))))
    ai6 = suc (suc (suc (suc (suc (suc zero)))))
```

<!--en-->
## Conjunction
<!--zh-->
## 合取
<!--/-->

<!--en-->
The first of the twelve, and the shortest, because the intersection needs no
ambient set: a member of both values is already a member of the ambient one, by
the specification of either.
<!--zh-->
十二条里的第一条，也是最短的，因为交不需要周遭集合：两个取值的共同成员，按其中任一个的规格，本来就是周遭那个的成员。
<!--/-->

```agda
  module Un (k : ℕ) (op : ∀ {m} → Formula S m → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ a' ∈ Formula S m ] (ψ ≡ op a'))
    (payOp : ∀ {m} (a' : Formula S m) → LCode.payOf (op a') ≡ LCode.⌜ a' ⌝)
    where
    Parts : (ar yc ya : S) → Type (ℓ-suc ℓ)
    Parts ar yc ya =
      Σ[ m ∈ ℕ ] (Σ[ a' ∈ Formula S m ]
        ((# m ≡ fst ar)
         × ((fst yc ≡ fst (Sat B (op a'))) × (fst ya ≡ fst (Sat B a')))))

    parts : (c ar a yc ya : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar yc ya ∥₁
    parts c ar a yc ya c∈ sh hc ha = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (fst a) (sym q ∙ sh)
            g  = get ψ (r .fst)
            a' = g .fst
            eψ = g .snd
            pay = cong fst (sym (payOp a'))
                ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
            ka = cong₂ pr (sym (r .snd .fst)) (sym pay)
               ∙ cong (λ w → pr w (fst LCode.⌜ a' ⌝)) (sym (numeralL-fst m))
               ∙ sym (prʟ-fst (numeralL m) LCode.⌜ a' ⌝)
        in m , a' , r .snd .fst
         , ( entry-out B φ (op a') (fst yc)
               (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
                 (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc)
           , entry-out B φ a' (fst ya)
               (subst (λ w → ⟨ pr w (fst ya) ∈ fst (satTable B φ) ⟩) ka ha) ) })
      (slot-inv B φ (fst c) c∈)

  module Bin (k : ℕ) (op : ∀ {m} → Formula S m → Formula S m → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ a' ∈ Formula S m ] (Σ[ b' ∈ Formula S m ] (ψ ≡ op a' b')))
    (payOp : ∀ {m} (a' b' : Formula S m)
           → LCode.payOf (op a' b') ≡ prʟ LCode.⌜ a' ⌝ LCode.⌜ b' ⌝)
    where
    Parts : (ar yc ya yb : S) → Type (ℓ-suc ℓ)
    Parts ar yc ya yb =
      Σ[ m ∈ ℕ ] (Σ[ a' ∈ Formula S m ] (Σ[ b' ∈ Formula S m ]
        ((# m ≡ fst ar)
         × ((fst yc ≡ fst (Sat B (op a' b')))
            × ((fst ya ≡ fst (Sat B a')) × (fst yb ≡ fst (Sat B b')))))))

    parts : (c ar a b yc ya yb : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar yc ya yb ∥₁
    parts c ar a b yc ya yb c∈ sh hc ha hb = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (pr (fst a) (fst b)) (sym q ∙ sh)
            g  = get ψ (r .fst)
            a' = g .fst
            b' = g .snd .fst
            eψ = g .snd .snd
            pay = sym (prʟ-fst LCode.⌜ a' ⌝ LCode.⌜ b' ⌝)
                ∙ cong fst (sym (payOp a' b'))
                ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
            ka = cong₂ pr (sym (r .snd .fst)) (sym (pr-inj pay .fst))
               ∙ cong (λ w → pr w (fst LCode.⌜ a' ⌝)) (sym (numeralL-fst m))
               ∙ sym (prʟ-fst (numeralL m) LCode.⌜ a' ⌝)
            kb = cong₂ pr (sym (r .snd .fst)) (sym (pr-inj pay .snd))
               ∙ cong (λ w → pr w (fst LCode.⌜ b' ⌝)) (sym (numeralL-fst m))
               ∙ sym (prʟ-fst (numeralL m) LCode.⌜ b' ⌝)
        in m , a' , b' , r .snd .fst
         , ( entry-out B φ (op a' b') (fst yc)
               (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
                 (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc)
           , ( entry-out B φ a' (fst ya)
                 (subst (λ w → ⟨ pr w (fst ya) ∈ fst (satTable B φ) ⟩) ka ha)
             , entry-out B φ b' (fst yb)
                 (subst (λ w → ⟨ pr w (fst yb) ∈ fst (satTable B φ) ⟩) kb hb) ) ) })
      (slot-inv B φ (fst c) c∈)

```

<!--en-->
## The two propositional clauses
<!--zh-->
## 两条命题子句
<!--/-->

<!--en-->
Conjunction and disjunction share the frame, so they share the hard half. What
is left is the set identity, and it is the separation's specification read back:
the value at a conjunction was cut out of the ambient set by "in this and in
that", so being in it is being in both. Neither direction needs the ambient set
in the conjunction's case; disjunction needs it once, in the direction that
builds, and gets it from whichever disjunct it was handed.
<!--zh-->
合取与析取共用框架，故共用难的那一半。剩下的是那条集合等式，而它就是那次分离的规格读回来：合取处的取值当初是用「在这个之中且在那个之中」从周遭集合雕出的，故落在其中就是落在两者之中。合取那边两个方向都不需要周遭集合；析取需要一次，在「造出来」的那个方向上，而它从被递来的那个析取项里拿到。
<!--/-->

```agda
  private
    module BinAnd = Bin 2 _∧̇_ (λ _ m → m) (λ _ _ → refl)
    module BinOr  = Bin 3 _∨̇_ (λ _ m → m) (λ _ _ → refl)

  andSound : ⟨ δ ⊨ andClauseAt Ci Ti ⟩
  andSound = propClause-in Ci Ti 2 (interAt yc7 ya7 yb7) δ
    (λ c ar a b yc ya yb c∈ sh hc ha hb →
      let P = BinAnd.parts c ar a b yc ya yb c∈ sh hc ha hb in
        (λ z hz → PT.rec (isProp× (snd (fst z ∈ fst ya)) (snd (fst z ∈ fst yb)))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            let s = subst ⟨_⟩ (Sat-mem B (a' ∧̇ b') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ea) (s .snd .fst)
             , subst (λ w → ⟨ fst z ∈ w ⟩) (sym eb) (s .snd .snd) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            let za = subst (λ w → ⟨ fst z ∈ w ⟩) ea (hz .fst)
                zb = subst (λ w → ⟨ fst z ∈ w ⟩) eb (hz .snd)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem B (a' ∧̇ b') z))
                   (subst ⟨_⟩ (Sat-mem B a' z) za .fst , (za , zb))) })
          P))

  orSound : ⟨ δ ⊨ orClauseAt Ci Ti ⟩
  orSound = propClause-in Ci Ti 3 (unionAt yc7 ya7 yb7) δ
    (λ c ar a b yc ya yb c∈ sh hc ha hb →
      let P = BinOr.parts c ar a b yc ya yb c∈ sh hc ha hb in
        (λ z hz → PT.rec squash₁
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) → PT.map
            (λ { (inl w) → inl (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w)
               ; (inr w) → inr (subst (λ v → ⟨ fst z ∈ v ⟩) (sym eb) w) })
            (subst ⟨_⟩ (Sat-mem B (a' ∨̇ b') z)
              (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .snd) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) → PT.rec (snd (fst z ∈ fst yc))
            (λ { (inl w) →
                   let za = subst (λ v → ⟨ fst z ∈ v ⟩) ea w in
                   subst (λ v → ⟨ fst z ∈ v ⟩) (sym ec)
                     (subst ⟨_⟩ (sym (Sat-mem B (a' ∨̇ b') z))
                       (subst ⟨_⟩ (Sat-mem B a' z) za .fst , ∣ inl za ∣₁))
               ; (inr w) →
                   let zb = subst (λ v → ⟨ fst z ∈ v ⟩) eb w in
                   subst (λ v → ⟨ fst z ∈ v ⟩) (sym ec)
                     (subst ⟨_⟩ (sym (Sat-mem B (a' ∨̇ b') z))
                       (subst ⟨_⟩ (Sat-mem B b' z) zb .fst , ∣ inr zb ∣₁)) })
            hz })
          P))

  module UnSucc (k : ℕ) (op : ∀ {m} → Formula S (suc m) → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ a' ∈ Formula S (suc m) ] (ψ ≡ op a'))
    (payOp : ∀ {m} (a' : Formula S (suc m)) → LCode.payOf (op a') ≡ LCode.⌜ a' ⌝)
    where
    Parts : (ar yc ya : S) → Type (ℓ-suc ℓ)
    Parts ar yc ya =
      Σ[ m ∈ ℕ ] (Σ[ a' ∈ Formula S (suc m) ]
        ((# m ≡ fst ar)
         × ((fst yc ≡ fst (Sat B (op a'))) × (fst ya ≡ fst (Sat B a')))))

    parts : (c ar a yc ya : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (sucV (fst ar)) (fst a)) (fst ya) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar yc ya ∥₁
    parts c ar a yc ya c∈ sh hc ha = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (fst a) (sym q ∙ sh)
            g  = get ψ (r .fst)
            a' = g .fst
            eψ = g .snd
            pay = cong fst (sym (payOp a'))
                ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
            ka = cong₂ pr (cong sucV (sym (r .snd .fst))) (sym pay)
               ∙ cong (λ w → pr w (fst LCode.⌜ a' ⌝))
                   (sym (numeralL-fst (suc m)))
               ∙ sym (prʟ-fst (numeralL (suc m)) LCode.⌜ a' ⌝)
        in m , a' , r .snd .fst
         , ( entry-out B φ (op a') (fst yc)
               (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
                 (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc)
           , entry-out B φ a' (fst ya)
               (subst (λ w → ⟨ pr w (fst ya) ∈ fst (satTable B φ) ⟩) ka ha) ) })
      (slot-inv B φ (fst c) c∈)

  module Atom (k : ℕ) (op : ∀ {m} → Term S m → Term S m → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ t ∈ Term S m ] (Σ[ u ∈ Term S m ] (ψ ≡ op t u)))
    (payOp : ∀ {m} (t u : Term S m)
           → LCode.payOf (op t u) ≡ prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ u ⌝ᵗ)
    where
    Parts : (ar a b yc : S) → Type (ℓ-suc ℓ)
    Parts ar a b yc =
      Σ[ m ∈ ℕ ] (Σ[ t ∈ Term S m ] (Σ[ u ∈ Term S m ]
        ((# m ≡ fst ar)
         × ((fst a ≡ fst LCode.⌜ t ⌝ᵗ)
            × ((fst b ≡ fst LCode.⌜ u ⌝ᵗ)
               × (fst yc ≡ fst (Sat B (op t u))))))))

    parts : (c ar a b yc : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar a b yc ∥₁
    parts c ar a b yc c∈ sh hc = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (pr (fst a) (fst b)) (sym q ∙ sh)
            g  = get ψ (r .fst)
            t  = g .fst
            u  = g .snd .fst
            eψ = g .snd .snd
            pay = sym (prʟ-fst LCode.⌜ t ⌝ᵗ LCode.⌜ u ⌝ᵗ)
                ∙ cong fst (sym (payOp t u))
                ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
        in m , t , u , r .snd .fst
         , ( sym (pr-inj pay .fst)
           , ( sym (pr-inj pay .snd)
             , entry-out B φ (op t u) (fst yc)
                 (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
                   (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc) ) ) })
      (slot-inv B φ (fst c) c∈)

  module BinSucc (k : ℕ)
    (op : ∀ {m} → Term S m → Formula S (suc m) → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ t ∈ Term S m ] (Σ[ a' ∈ Formula S (suc m) ] (ψ ≡ op t a')))
    (payOp : ∀ {m} (t : Term S m) (a' : Formula S (suc m))
           → LCode.payOf (op t a') ≡ prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ a' ⌝)
    where
    Parts : (ar a b yc yb : S) → Type (ℓ-suc ℓ)
    Parts ar a b yc yb =
      Σ[ m ∈ ℕ ] (Σ[ t ∈ Term S m ] (Σ[ a' ∈ Formula S (suc m) ]
        ((# m ≡ fst ar)
         × ((fst a ≡ fst LCode.⌜ t ⌝ᵗ)
            × ((fst yc ≡ fst (Sat B (op t a')))
               × (fst yb ≡ fst (Sat B a')))))))

    parts : (c ar a b yc yb : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (sucV (fst ar)) (fst b)) (fst yb) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar a b yc yb ∥₁
    parts c ar a b yc yb c∈ sh hc hb = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (pr (fst a) (fst b)) (sym q ∙ sh)
            g  = get ψ (r .fst)
            t  = g .fst
            a' = g .snd .fst
            eψ = g .snd .snd
            pay = sym (prʟ-fst LCode.⌜ t ⌝ᵗ LCode.⌜ a' ⌝)
                ∙ cong fst (sym (payOp t a'))
                ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
            kb = cong₂ pr (cong sucV (sym (r .snd .fst)))
                   (sym (pr-inj pay .snd))
               ∙ cong (λ w → pr w (fst LCode.⌜ a' ⌝))
                   (sym (numeralL-fst (suc m)))
               ∙ sym (prʟ-fst (numeralL (suc m)) LCode.⌜ a' ⌝)
        in m , t , a' , r .snd .fst
         , ( sym (pr-inj pay .fst)
           , ( entry-out B φ (op t a') (fst yc)
                 (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
                   (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc)
             , entry-out B φ a' (fst yb)
                 (subst (λ w → ⟨ pr w (fst yb) ∈ fst (satTable B φ) ⟩) kb hb) ) ) })
      (slot-inv B φ (fst c) c∈)

  module Const (k : ℕ) (c₀ : ∀ {m} → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ → ψ ≡ c₀)
    where
    Parts : (ar yc : S) → Type (ℓ-suc ℓ)
    Parts ar yc =
      Σ[ m ∈ ℕ ] ((# m ≡ fst ar) × (fst yc ≡ fst (Sat B (c₀ {m}))))

    parts : (c ar a yc : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ∥ Parts ar yc ∥₁
    parts c ar a yc c∈ sh hc = PT.map
      (λ { (m , ψ , q) →
        let r  = keyʟ-shape ψ k (fst ar) (fst a) (sym q ∙ sh)
            eψ = get ψ (r .fst)
        in m , r .snd .fst
         , entry-out B φ c₀ (fst yc)
             (subst (λ w → ⟨ pr w (fst yc) ∈ fst (satTable B φ) ⟩)
               (q ∙ cong (λ w → fst (keyʟ w)) eψ) hc) })
      (slot-inv B φ (fst c) c∈)

  private
    module ConstTop = Const 6 ⊤̇ (λ _ m → m)
    module ConstBot = Const 7 ⊥̇ (λ _ m → m)

  topSound : ⟨ δ ⊨ topClauseAt Ci Ti Bi ⟩
  topSound = topClause-in Ci Ti Bi δ
    (λ c ar a yc E c∈ sh hc hE →
      let P  = ConstTop.parts c ar a yc c∈ sh hc
          δ' = E ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc Bi))))
          ai = suc (suc (suc zero))
      in
        (λ z hz → PT.rec (snd (fst z ∈ fst E))
          (λ { (m , (qm , ec)) →
            Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z
              (subst ⟨_⟩ (Sat-mem B (⊤̇ {n = m}) z)
                (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .fst) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , (qm , ec)) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem B (⊤̇ {n = m}) z))
                ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z hz
                , tt* )) })
          P))

  botSound : ⟨ δ ⊨ botClauseAt Ci Ti ⟩
  botSound = botClause-in Ci Ti δ
    (λ c ar a yc c∈ sh hc →
      let P = ConstBot.parts c ar a yc c∈ sh hc in
        (λ z hz → PT.rec isProp⊥*
          (λ { (m , (qm , ec)) →
            subst ⟨_⟩ (Sat-mem B (⊥̇ {n = m}) z)
              (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .snd })
          P)
      , (λ z hz → Empty.rec* hz))

  private
    module BndAll = BinSucc 10 ∀̇∈ (λ _ m → m) (λ _ _ → refl)
    module BndEx  = BinSucc 11 ∃̇∈ (λ _ m → m) (λ _ _ → refl)

  allInSound : ⟨ δ ⊨ allInClauseAt Ci Ti Bi ⟩
  allInSound = bndClause-in Ci Ti Bi 10 (bodyAll Bi) δ
    (λ c ar a b yc yb E c∈ sh hc hb hE →
      let P  = BndAll.parts c ar a b yc yb c∈ sh hc hb
          δ' = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc Bi))))))
          ai = suc (suc (suc (suc (suc zero))))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ bodyAll Bi))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let s  = subst ⟨_⟩ (Sat-mem B (∀̇∈ t a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst)
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z z∈
            in bodyAll-in Bi (z ∷ δ') z∈
                 (λ w hw x e' x∈B x∈w hcs →
                   subst (λ v → ⟨ fst e' ∈ v ⟩) (sym eb)
                     (cond∀∈-out B t a' z (s .snd) w
                       (termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                          (w ∷ z ∷ []) ai0 ai1 ea refl refl .fst hw)
                       x e' x∈B x∈w
                       (consAtL-transport (e' ∷ x ∷ w ∷ z ∷ δ')
                         (e' ∷ x ∷ w ∷ z ∷ []) zero (suc zero)
                         (suc (suc (suc zero))) zero (suc zero)
                         (suc (suc (suc zero)))
                         (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                         refl refl refl hcs))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let r  = bodyAll-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem B (∀̇∈ t a') z))
                   ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                   , cond∀∈-in B t a' z
                       (λ w hw x e' x∈B x∈w hcs →
                         subst (λ v → ⟨ fst e' ∈ v ⟩) eb
                           (r .snd w
                             (termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                                (w ∷ z ∷ []) ai0 ai1 ea refl refl .snd hw)
                             x e' x∈B x∈w
                             (consAtL-transport (e' ∷ x ∷ w ∷ z ∷ [])
                               (e' ∷ x ∷ w ∷ z ∷ δ') zero (suc zero)
                               (suc (suc (suc zero))) zero (suc zero)
                               (suc (suc (suc zero)))
                               (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                               refl refl refl hcs))) )) })
          P))

  exInSound : ⟨ δ ⊨ exInClauseAt Ci Ti Bi ⟩
  exInSound = bndClause-in Ci Ti Bi 11 (bodyEx Bi) δ
    (λ c ar a b yc yb E c∈ sh hc hb hE →
      let P  = BndEx.parts c ar a b yc yb c∈ sh hc hb
          δ' = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc Bi))))))
          ai = suc (suc (suc (suc (suc zero))))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ bodyEx Bi))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let s  = subst ⟨_⟩ (Sat-mem B (∃̇∈ t a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst)
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z z∈
            in bodyEx-in Bi (z ∷ δ') z∈
                 (PT.map (λ { (w , (hw , hx)) → w
                    , ( termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                          (w ∷ z ∷ []) ai0 ai1 ea refl refl .snd hw
                      , PT.map (λ { (x , ((x∈B , x∈w) , (e' , (hcs , he)))) →
                          x , ((x∈B , x∈w) , (e'
                          , ( consAtL-transport (e' ∷ x ∷ w ∷ z ∷ [])
                                (e' ∷ x ∷ w ∷ z ∷ δ') zero (suc zero)
                                (suc (suc (suc zero))) zero (suc zero)
                                (suc (suc (suc zero)))
                                (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                                refl refl refl hcs
                            , subst (λ v → ⟨ fst e' ∈ v ⟩) (sym eb) he ))) })
                          hx ) })
                    (cond∃∈-out B t a' z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , a' , (qm , (ea , (ec , eb)))) →
            let r  = bodyEx-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem B (∃̇∈ t a') z))
                   ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                   , cond∃∈-in B t a' z
                       (PT.map (λ { (w , (hw , hx)) → w
                          , ( termAgree t (w ∷ z ∷ δ') ai6 ai1 ai0
                                (w ∷ z ∷ []) ai0 ai1 ea refl refl .fst hw
                            , PT.map (λ { (x , ((x∈B , x∈w) , (e' , (hcs , he)))) →
                                x , ((x∈B , x∈w) , (e'
                                , ( consAtL-transport (e' ∷ x ∷ w ∷ z ∷ δ')
                                      (e' ∷ x ∷ w ∷ z ∷ []) zero (suc zero)
                                      (suc (suc (suc zero))) zero (suc zero)
                                      (suc (suc (suc zero)))
                                      (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                                      refl refl refl hcs
                                  , subst (λ v → ⟨ fst e' ∈ v ⟩) eb he ))) })
                                hx ) })
                          (r .snd)) )) })
          P))

  private
    module UnEx  = UnSucc 8 ∃̇_ (λ _ m → m) (λ _ → refl)
    module UnAll = UnSucc 9 ∀̇_ (λ _ m → m) (λ _ → refl)

  existSound : ⟨ δ ⊨ existClauseAt Ci Ti Bi ⟩
  existSound = quantClause-in Ci Ti Bi 8 (body∃ Bi) δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P  = UnEx.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ body∃ Bi))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s  = subst ⟨_⟩ (Sat-mem B (∃̇ a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z
                       (Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst))
            in body∃-in Bi (z ∷ δ')
                 (Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst))
                 (PT.map
                   (λ { (x , (x∈ , (e' , (hcs , he)))) → x , x∈ , e'
                      , ( consAtL-transport (e' ∷ x ∷ z ∷ []) (e' ∷ x ∷ z ∷ δ')
                            zero (suc zero) (suc (suc zero))
                            zero (suc zero) (suc (suc zero))
                            (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                            refl refl refl hcs
                        , subst (λ w → ⟨ fst e' ∈ w ⟩) (sym ea) he ) })
                   (cond∃-out B a' z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            let r  = body∃-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem B (∃̇ a') z))
                   ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                   , cond∃-in B a' z (PT.map
                       (λ { (x , (x∈ , (e' , (hcs , he)))) → x , x∈ , e'
                          , ( consAtL-transport (e' ∷ x ∷ z ∷ δ') (e' ∷ x ∷ z ∷ [])
                                zero (suc zero) (suc (suc zero))
                                zero (suc zero) (suc (suc zero))
                                (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                                refl refl refl hcs
                            , subst (λ w → ⟨ fst e' ∈ w ⟩) ea he ) })
                       (r .snd)) )) })
          P))

  forallSound : ⟨ δ ⊨ forallClauseAt Ci Ti Bi ⟩
  forallSound = quantClause-in Ci Ti Bi 9 (body∀ Bi) δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P  = UnAll.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ body∀ Bi))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s  = subst ⟨_⟩ (Sat-mem B (∀̇ a') z)
                       (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
                z∈ = Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst)
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z z∈
            in body∀-in Bi (z ∷ δ') z∈
                 (λ x e' x∈ hcs → subst (λ w → ⟨ fst e' ∈ w ⟩) (sym ea)
                   (cond∀-out B a' z (s .snd) x e' x∈
                     (consAtL-transport (e' ∷ x ∷ z ∷ δ') (e' ∷ x ∷ z ∷ [])
                       zero (suc zero) (suc (suc zero))
                       zero (suc zero) (suc (suc zero))
                       (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                       refl refl refl hcs))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            let r  = body∀-out Bi (z ∷ δ') hz
                ae = Ambient.asEnv B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
                 (subst ⟨_⟩ (sym (Sat-mem B (∀̇ a') z))
                   ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                   , cond∀-in B a' z
                       (λ x e' x∈ hcs → subst (λ w → ⟨ fst e' ∈ w ⟩) ea
                         (r .snd x e' x∈
                           (consAtL-transport (e' ∷ x ∷ z ∷ []) (e' ∷ x ∷ z ∷ δ')
                             zero (suc zero) (suc (suc zero))
                             zero (suc zero) (suc (suc zero))
                             (λ i → ⟪ fst B ⟫↪ (ae .fst i)) (ae .snd)
                             refl refl refl hcs))) )) })
          P))

  private
    module AtomMem = Atom 0 _∈̇_ (λ _ m → m) (λ _ _ → refl)
    module AtomEq  = Atom 1 _≐_ (λ _ m → m) (λ _ _ → refl)

  memSound : ⟨ δ ⊨ memClauseAt Ci Ti Bi ⟩
  memSound = atomClause-in Ci Ti Bi 0 memRel δ
    (λ c ar a b yc E c∈ sh hc hE →
      let P  = AtomMem.parts c ar a b yc c∈ sh hc
          δ' = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ atomBody memRel))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let s = subst ⟨_⟩ (Sat-mem B (t ∈̇ u) z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in atomBody-in memRel (z ∷ δ')
                 (Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst))
                 (PT.map
                   (λ { (v , (w , (ht , (hu , hr)))) → v , w
                      , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                            (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .snd ht
                        , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                              (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .snd hu
                          , hr ) ) })
                   (cond∈-out B t u z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let r = atomBody-out memRel (z ∷ δ') hz in
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem B (t ∈̇ u) z))
                ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                , cond∈-in B t u z (PT.map
                    (λ { (v , (w , (ht , (hu , hr)))) → v , w
                       , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                             (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .fst ht
                         , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                               (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .fst hu
                           , hr ) ) })
                    (r .snd)) )) })
          P))

  eqSound : ⟨ δ ⊨ eqClauseAt Ci Ti Bi ⟩
  eqSound = atomClause-in Ci Ti Bi 1 eqRel δ
    (λ c ar a b yc E c∈ sh hc hE →
      let P  = AtomEq.parts c ar a b yc c∈ sh hc
          δ' = E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc Bi)))))
          ai = suc (suc (suc (suc zero)))
      in
        (λ z hz → PT.rec (snd ((z ∷ δ') ⊨ atomBody eqRel))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let s = subst ⟨_⟩ (Sat-mem B (t ≐ u) z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in atomBody-in eqRel (z ∷ δ')
                 (Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst))
                 (PT.map
                   (λ { (v , (w , (ht , (hu , hr)))) → v , w
                      , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                            (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .snd ht
                        , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                              (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .snd hu
                          , hr ) ) })
                   (cond≐-out B t u z (s .snd))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , t , u , (qm , (ea , (eb , ec)))) →
            let r = atomBody-out eqRel (z ∷ δ') hz in
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem B (t ≐ u) z))
                ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (r .fst)
                , cond≐-in B t u z (PT.map
                    (λ { (v , (w , (ht , (hu , hr)))) → v , w
                       , ( termAgree t (w ∷ v ∷ z ∷ δ') ai6 ai2 ai1
                             (w ∷ v ∷ z ∷ []) ai1 ai2 ea refl refl .fst ht
                         , ( termAgree u (w ∷ v ∷ z ∷ δ') ai5 ai2 ai0
                               (w ∷ v ∷ z ∷ []) ai0 ai2 eb refl refl .fst hu
                           , hr ) ) })
                    (r .snd)) )) })
          P))

  private
    module BinImp = Bin 4 _⇒̇_ (λ _ m → m) (λ _ _ → refl)

  impSound : ⟨ δ ⊨ impClauseAt Ci Ti Bi ⟩
  impSound = impClause-in Ci Ti Bi δ
    (λ c ar a b yc ya yb E c∈ sh hc ha hb hE →
      let P  = BinImp.parts c ar a b yc ya yb c∈ sh hc ha hb
          δ' = E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ δ
          Ea = suc (suc (suc (suc (suc (suc (suc (suc Bi)))))))
          ai = suc (suc (suc (suc (suc (suc zero)))))
      in
        (λ z hz → PT.rec
          (isProp× (snd (fst z ∈ fst E))
            (isPropΠ (λ _ → snd (fst z ∈ fst yb))))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            let s = subst ⟨_⟩ (Sat-mem B (a' ⇒̇ b') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in Ambient.outof B δ' zero ai Ea m (sym qm) refl hE z (s .fst)
             , (λ w → subst (λ v → ⟨ fst z ∈ v ⟩) (sym eb)
                 (s .snd (subst (λ v → ⟨ fst z ∈ v ⟩) ea w))) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (qm , (ec , (ea , eb)))) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem B (a' ⇒̇ b') z))
                ( Ambient.into B δ' zero ai Ea m (sym qm) refl hE z (hz .fst)
                , (λ w → subst (λ v → ⟨ fst z ∈ v ⟩) eb
                    (hz .snd (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w))) )) })
          P))

  private
    module UnNeg = Un 5 ¬̇_ (λ _ m → m) (λ _ → refl)

  negSound : ⟨ δ ⊨ negClauseAt Ci Ti Bi ⟩
  negSound = negClause-in Ci Ti Bi δ
    (λ c ar a yc ya E c∈ sh hc ha hE →
      let P = UnNeg.parts c ar a yc ya c∈ sh hc ha
          δ' = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ δ
      in
        (λ z hz → PT.rec
          (isProp× (snd (fst z ∈ fst E)) (isPropΠ (λ _ → isProp⊥)))
          (λ { (m , a' , (qm , (ec , ea))) →
            let s = subst ⟨_⟩ (Sat-mem B (¬̇ a') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in Ambient.outof B δ' zero (suc (suc (suc (suc zero))))
                 (suc (suc (suc (suc (suc (suc Bi))))))
                 m (sym qm) refl hE z (s .fst)
             , (λ w → s .snd (subst (λ v → ⟨ fst z ∈ v ⟩) ea w)) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , (qm , (ec , ea))) →
            subst (λ w → ⟨ fst z ∈ w ⟩) (sym ec)
              (subst ⟨_⟩ (sym (Sat-mem B (¬̇ a') z))
                ( Ambient.into B δ' zero (suc (suc (suc (suc zero))))
                    (suc (suc (suc (suc (suc (suc Bi)))))) m (sym qm) refl hE z
                    (hz .fst)
                , (λ w → hz .snd (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w)) )) })
          P))
```

<!--en-->
## Negation
<!--zh-->
## 否定
<!--/-->

<!--en-->
Written above with the frames it shares, and worth a word here. It is the first
clause that **uses** its ambient set rather than only naming it, and both
directions of the difference are the agreement of the section before it applied
once each. Nothing else is in them: the value at a negation was cut out of the
ambient set by "not in that", which is what a difference says.
<!--zh-->
它写在上面、与它共用的诸框架一起，但值得在此说一句。它是第一条真正**使用**它的周遭集合、而非只点名它的子句，而差的两个方向就是前一节那份一致性各施用一次。里面没有别的：否定处的取值当初是用「不在那个之中」从周遭集合雕出的，而那正是差所说的话。
<!--/-->

<!--en-->
## All twelve
<!--zh-->
## 十二条全部
<!--/-->

<!--en-->
The existence half, complete: the table built by recursion on a formula of the
meta-language satisfies every clause of the internal recursion, over the slot it
is indexed by and the carrier its environments range over.

What the twelve cost, and what they cost it in, is worth one line. Five frames
carry them, and a frame is paid for once: the shared half of a clause is
inverting its index to a formula, computing that formula's constructor from the
tag, and identifying the recorded values with the ones the recursion built. What
is left over is a set identity, and those are cheap because the recursion defined
its value by the very condition the identity reads back.
<!--zh-->
存在性那一半，完成：沿元语言公式递归造出的那张表，在它所索引的槽与其诸环境所落的载体之上，满足内部递归的每一条子句。

那十二条花了多少、花在什么上，值得写一行。五个框架托着它们，而一个框架只付一次：一条子句共用的那一半，是把它的索引求逆回一条公式、从标签算出那条公式的构造子、并把被记录的诸取值与递归造出的诸取值认同起来。剩下的是一条集合等式，而那些便宜，因为递归当初正是用那条等式所读回的那个条件来定义它的取值的。
<!--/-->

```agda
  soundness : ⟨ δ ⊨ memClauseAt Ci Ti Bi ⟩ × (⟨ δ ⊨ eqClauseAt Ci Ti Bi ⟩
            × (⟨ δ ⊨ andClauseAt Ci Ti ⟩ × (⟨ δ ⊨ orClauseAt Ci Ti ⟩
            × (⟨ δ ⊨ impClauseAt Ci Ti Bi ⟩ × (⟨ δ ⊨ negClauseAt Ci Ti Bi ⟩
            × (⟨ δ ⊨ topClauseAt Ci Ti Bi ⟩ × (⟨ δ ⊨ botClauseAt Ci Ti ⟩
            × (⟨ δ ⊨ existClauseAt Ci Ti Bi ⟩ × (⟨ δ ⊨ forallClauseAt Ci Ti Bi ⟩
            × (⟨ δ ⊨ allInClauseAt Ci Ti Bi ⟩
            × ⟨ δ ⊨ exInClauseAt Ci Ti Bi ⟩))))))))))
  soundness = memSound , (eqSound , (andSound , (orSound , (impSound , (negSound
            , (topSound , (botSound , (existSound , (forallSound
            , (allInSound , exInSound)))))))))) 
```
