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
open import FOL.Syntax using ( Formula; _∧̇_; _∨̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( module LCode; prʟ; prʟ-fst; andClauseAt; orClauseAt
        ; propClause-in; interAt; unionAt; envSetAt; envOverAt
        ; envOverAt-transport; extAt-out; extAt-in; numL
        ; yc7; ya7; yb7 )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Sat {ℓ} lem using ( Sat; Sat-mem )
open import L.Coding.EnvSet {ℓ} lem
  using ( envSet; envSet-in; envSet-out; envS; envOver; module Recover )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; keyʟ-shape; satTable; slot; slot-inv; entry-out )

open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
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

```agda
private
  nn : ℕ → S
  nn j = # j , numL j

module _ (B : S) {n : ℕ} (φ : Formula S n) where
  private
    δ : S ^ 3
    δ = B ∷ satTable B φ ∷ slot B φ ∷ []

    Ci Ti Bi : Fin 3
    Ci = suc (suc zero)
    Ti = suc zero
    Bi = zero
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
  module Bin (k : ℕ) (op : ∀ {m} → Formula S m → Formula S m → Formula S m)
    (get : ∀ {m} (ψ : Formula S m) → LCode.Match k ψ
         → Σ[ a' ∈ Formula S m ] (Σ[ b' ∈ Formula S m ] (ψ ≡ op a' b')))
    (payOp : ∀ {m} (a' b' : Formula S m)
           → LCode.payOf (op a' b') ≡ prʟ LCode.⌜ a' ⌝ LCode.⌜ b' ⌝)
    where
    Parts : (yc ya yb : S) → Type (ℓ-suc ℓ)
    Parts yc ya yb =
      Σ[ m ∈ ℕ ] (Σ[ a' ∈ Formula S m ] (Σ[ b' ∈ Formula S m ]
        ((fst yc ≡ fst (Sat B (op a' b')))
         × ((fst ya ≡ fst (Sat B a')) × (fst yb ≡ fst (Sat B b'))))))

    parts : (c ar a b yc ya yb : S)
          → ⟨ fst c ∈ fst (slot B φ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (satTable B φ) ⟩
          → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (satTable B φ) ⟩
          → ∥ Parts yc ya yb ∥₁
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
        in m , a' , b'
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
          (λ { (m , a' , b' , (ec , (ea , eb))) →
            let s = subst ⟨_⟩ (Sat-mem B (a' ∧̇ b') z)
                      (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz)
            in subst (λ w → ⟨ fst z ∈ w ⟩) (sym ea) (s .snd .fst)
             , subst (λ w → ⟨ fst z ∈ w ⟩) (sym eb) (s .snd .snd) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (ec , (ea , eb))) →
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
          (λ { (m , a' , b' , (ec , (ea , eb))) → PT.map
            (λ { (inl w) → inl (subst (λ v → ⟨ fst z ∈ v ⟩) (sym ea) w)
               ; (inr w) → inr (subst (λ v → ⟨ fst z ∈ v ⟩) (sym eb) w) })
            (subst ⟨_⟩ (Sat-mem B (a' ∨̇ b') z)
              (subst (λ w → ⟨ fst z ∈ w ⟩) ec hz) .snd) })
          P)
      , (λ z hz → PT.rec (snd (fst z ∈ fst yc))
          (λ { (m , a' , b' , (ec , (ea , eb))) → PT.rec (snd (fst z ∈ fst yc))
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
