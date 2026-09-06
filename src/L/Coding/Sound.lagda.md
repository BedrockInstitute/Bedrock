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
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( envSetAt; envOverAt; envOverAt-transport
        ; extAt-out; extAt-in; extAt-in-both; numL )
open import L.Coding.EnvSet {ℓ} lem
  using ( envSet; envSet-in; envSet-out; envS; envOver; module Recover )

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

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
```
