<!--en-->
# Agreement of environment sets

Semantic clauses describe an environment set by the property of its members. This chapter proves that any set satisfying that description has exactly the members of the constructed environment set, and that the constructed set satisfies the description. These two directions let satisfaction arguments move between a formula's description and the actual set.
<!--zh-->
# 环境集的一致性

语义子句通过成员的性质描述环境集。本章证明，满足该描述的任意集合，都与已构造的环境集具有相同成员；反过来，已构造的集合也满足该描述。这两个方向使满足关系的论证能够在公式描述与实际集合之间转换。
<!--ja-->
# 環境の集合の一致

意味論的な節は、要素の性質によって環境の集合を記述します。本章では、この記述を満たす集合が構成済みの環境の集合と同じ要素を持つことと、構成した集合が記述を満たすことを示します。この二方向の結果により、充足関係の議論で論理式による記述と実際の集合を行き来できます。
<!--/-->

<!--en-->
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
每次验证都是同样四步，而其中三步已经造好。索引被求逆回「它是谁的键」的那条公式；该公式的构造子由子句的标签算出；被记录的诸取值与元语言递归造出的诸取值被认同起来。剩下的、也是唯一新的那一步，是一条集合等式：合取处的取值确实是它下面两个取值的交，其余十一条同理。

那些等式便宜，而理由值得直说。元语言的递归是「用一条点名下层诸取值的条件雕出周遭集合」来定义某构造子处的取值的，故那条等式就是把那条条件读回来，而那正是那次分离自己的规格所说的话。
<!--/-->


```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.EnvironmentAgreement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envOverAt; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( envSetAt; extAt-out; extAt-in; extAt-in-both; numL )
open import L.Coding.EnvironmentSet {ℓ} lem
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
## From the description to membership

Fix the carrier and the arity in an environment. If a set satisfies the formula describing all environments at that arity, its members are precisely the members of the constructed environment set. Both inclusions follow by recovering a coded environment from the description and encoding it again.
<!--zh-->
## 从描述得到隶属关系

在环境中固定载体与元数。若一个集合满足描述该元数下全部环境的公式，它的成员就恰好是已构造环境集的成员。两个包含方向分别利用从描述恢复编码环境、再将环境编码的过程。
<!--ja-->
## 記述から所属関係へ

環境の中で台とアリティを固定します。ある集合がそのアリティの全環境を記述する論理式を満たすなら、その要素は構成済みの環境の集合の要素と一致します。記述から符号化された環境を復元し、再び符号化することで両方向の包含を示します。
<!--/-->

<!--en-->
Neither direction re-proves anything. The description moves between the clause's
frame and the chapter's by the transport, and the two halves of the recovery are
already there.
<!--zh-->
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
## The constructed set satisfies the description

Place the constructed environment set, its arity and its carrier in the designated positions of an environment. Its membership characterization proves the describing formula: every member encodes an environment, and every encoded environment is a member.
<!--zh-->
## 已构造的集合满足描述

将已构造的环境集、它的元数和载体放在环境的指定位置。该集合的隶属关系刻画证明了描述公式：每个成员都编码一个环境，而每个编码环境也都是其成员。
<!--ja-->
## 構成した集合が記述を満たすこと

構成した環境の集合、そのアリティ、台を環境の指定位置に置きます。各要素が環境を符号化し、符号化された各環境が要素になるという所属関係の特徴付けから、記述する論理式が成り立ちます。
<!--/-->

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
