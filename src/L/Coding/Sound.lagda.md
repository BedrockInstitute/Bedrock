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
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( module LCode; prʟ-fst; envSetAt; envOverAt; envOverAt-transport
        ; tmValAt; tmValAt-var; tmValAt-con; tmValAt-out
        ; extAt-out; extAt-in; extAt-in-both; numL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; Sat-mem; tmIs; tmIs-var-in; tmIs-var-out; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
        ; cond∀∈-in; cond∀∈-out; cond∃∈-in; cond∃∈-out )
open import L.Coding.EnvSet {ℓ} lem
  using ( envSet; envSet-in; envSet-out; envS; envOver; Ix
        ; module Recover; module Generic )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; keyʟ-shape; satTable; slot; slot-inv; entry-out )

open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
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

```

<!--en-->
And the same agreement in the producing direction. A clause that *binds* its
ambient set has to be handed one, and the only candidate is the set the previous
chapter built; this says it qualifies. The uniqueness half will want it at every
clause that binds an ambient set, which is seven of the twelve.
<!--zh-->
以及同一份一致性的「产出」方向。一条**绑定**自己周遭集合的子句必须被递一个进来，而唯一的候选就是上一章造出的那个集合；这条说它合格。唯一性那一半会在每条绑定周遭集合的子句处要它，而那是十二条里的七条。
<!--/-->

```agda
module AmbientHolds (B : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k) (m : ℕ)
  (qE : fst (lookup Ei γ) ≡ fst (envSet B m))
  (qd : fst (lookup di γ) ≡ # m) (qb : fst (lookup bi γ) ≡ fst B)
  where

  holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
  holds = extAt-in-both Ei (envOverAt zero (suc di) (suc bi)) γ fwd bwd
    where
    fwd : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    fwd z hz = PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
      (λ { (g , eg) → envOverAt-transport (B ∷ nn m ∷ envS B g ∷ []) (z ∷ γ)
             (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
             (sym eg) (sym qd) (sym qb) (envOver B g) })
      (envSet-out B m z (subst (λ w → ⟨ fst z ∈ w ⟩) qE hz))

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
    bwd z h = subst (λ w → ⟨ fst z ∈ w ⟩) (sym qE)
      (subst (λ w → ⟨ w ∈ fst (envSet B m) ⟩)
        (sym (Recover.recovers B m (z ∷ γ) zero (suc di) (suc bi) qd qb h))
        (envSet-in B (Recover.g B m (z ∷ γ) zero (suc di) (suc bi) qd qb h)))

module AmbientHoldsGen (B ar : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k)
  (qE : fst (lookup Ei γ) ≡ fst (Generic.envSetGen B ar))
  (qd : fst (lookup di γ) ≡ fst ar) (qb : fst (lookup bi γ) ≡ fst B)
  where

  holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
  holds = H.holds
    where
    module G = Generic B ar
    module H = G.Holds γ Ei di bi qE qd qb

module NumeralFromGeneric (B : S) (n : ℕ) where

  derived : fst (envSet B n) ≡ fst (Generic.envSetGen B (nn n))
  derived = extensionalV (λ w → ⇔toPath (fwd w) (bwd w))
    where
    Egen Enum : S
    Egen = Generic.envSetGen B (nn n)
    Enum = envSet B n

    γ : S ^ 4
    γ = Egen ∷ Enum ∷ B ∷ nn n ∷ []

    EiGen EiNum bi di : Fin 4
    EiGen = zero
    EiNum = suc zero
    bi = suc (suc zero)
    di = suc (suc (suc zero))

    qd : fst (lookup di γ) ≡ fst (nn n)
    qd = refl

    qb : fst (lookup bi γ) ≡ fst B
    qb = refl

    holdsNum : ⟨ γ ⊨ envSetAt EiNum di bi ⟩
    holdsNum = AmbientHolds.holds B γ EiNum di bi n refl qd qb

    module G = Generic B (nn n)
    module H = G.Holds γ EiGen di bi refl qd qb

    fwd : (w : V ℓ) → ⟨ w ∈ fst Enum ⟩ → ⟨ w ∈ fst Egen ⟩
    fwd w hw = H.bwd z
      (extAt-out EiNum (envOverAt zero (suc di) (suc bi)) γ holdsNum z hw)
      where
      z : S
      z = w , isL-trans {x = fst Enum} {y = w} hw (snd Enum)

    bwd : (w : V ℓ) → ⟨ w ∈ fst Egen ⟩ → ⟨ w ∈ fst Enum ⟩
    bwd w hw =
      subst (λ w → ⟨ w ∈ fst Enum ⟩)
        (sym (Recover.recovers B n (z ∷ γ) zero (suc di) (suc bi) qd qb h))
        (envSet-in B (Recover.g B n (z ∷ γ) zero (suc di) (suc bi) qd qb h))
      where
      z : S
      z = w , isL-trans {x = fst Egen} {y = w} hw (snd Egen)
      h : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
      h = H.fwd z hw
```
