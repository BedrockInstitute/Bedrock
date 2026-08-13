{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.84] probe A: is witK satisfiable?  THE REFUTATION.
--
-- witK (L.Condensation.lagda.md:6227-6229) states: every closed and
-- shaped code set over the carrier A, containing the key of the formula
-- at slot x, lies in the K slot.  The brief asks whether that statement
-- is satisfiable before any supply work.
--
-- The answer this probe machine-checks: NO, at every stage.  The
-- shapedness predicate does not constrain the ARITY slot of a member
-- (L.Coding.Shape.lagda.md:183-190: the arity is an existential and
-- nothing bounds it).  So from ANY closed and shaped code set D over A
-- containing the key X, build w = D union {c} where
--     c = pr (fst K) (pr (#6) (numeralL 0))
-- is a tag-6 constant key whose arity slot is the stage bound fst K
-- itself.  Tag 6 fires no closedness clause, and its shapedness clause
-- demands only that the payload is the numeral zero.  Hence w is still
-- closed and shaped over A, still contains X, and has rank at least the
-- rank of fst K; w is not a member of Lset lam.  witK's type is
-- uninhabited at the stage.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ184A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ⊤̇ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; layer-trans; Lset-layer )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.Model {ℓ}
  using ( closedAt; appAt; appAt-adequate; arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in
        ; sucAtL; sucAtL-adequate )
open import L.Coding.InL {ℓ}
  using ( key; keyL; key∈closure; cupʟ; sglʟ; cupʟ-inl; cupʟ-inr; cupʟ-out
        ; sglʟ-in; sglʟ-out )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ}
  using ( shapedAt; shapes; unForm; zeroPay; closureShaped )
open import L.Coding.Base {ℓ} using ( ∈sgl-intro; ∈pair-introL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Properties using ( znots )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Empty using ( ⊥ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- THE GENERIC REFUTATION.  Parameters: the carrier A0, the stage bound
-- K0, the formula key X0, and a delivered closed and shaped code set D
-- over A0 that contains X0 (at the stage, D is the subformula closure).
-- The proof needs nothing else: the junk member is built from K0 alone,
-- and the stage bound's transitivity and irreflexivity are the only
-- hypotheses about K0.
-- =====================================================================
module Refute
  (A₀ K₀ X₀ D : Sʟ)
  (hX : ⟨ fst X₀ ∈ˢ fst D ⟩)
  (hcl : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ closedAt zero ⟩)
  (hsh : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ shapedAt zero (suc zero) ⟩)
  (transK : {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ fst K₀ ⟩ → ⟨ y ∈ˢ fst K₀ ⟩)
  (Kirr : ⟨ fst K₀ ∈ˢ fst K₀ ⟩ → Empty.⊥)
  where

  γ₀ : Sʟ ^ 3
  γ₀ = A₀ ∷ K₀ ∷ X₀ ∷ []

  -- THE JUNK MEMBER.  Tag 6 (the constant truth key), payload the
  -- numeral zero, arity slot the stage bound itself.  The shapedness
  -- clause for tag 6 (zeroPay) demands only that the payload is zero;
  -- the closedness clauses name tags 2, 3, 4, 5, 8, 9, 10, 11 only, so
  -- tag 6 fires none of them.
  c₀ : Sʟ
  c₀ = prʟ K₀ (prʟ (numeralL 6) (numeralL 0))

  -- THE REFUTING WITNESS: the delivered code set plus the junk member.
  w : Sʟ
  w = cupʟ D (sglʟ c₀)

  fstC₀ : fst c₀ ≡ pr (fst K₀) (pr (# 6) (fst (numeralL 0)))
  fstC₀ = prʟ-fst K₀ (prʟ (numeralL 6) (numeralL 0))
        ∙ cong (pr (fst K₀))
            (prʟ-fst (numeralL 6) (numeralL 0)
              ∙ cong (λ q → pr q (fst (numeralL 0))) (numeralL-fst 6))

  -- The first premise conjunct: the formula key X0 lies in w.
  X∈w : ⟨ fst X₀ ∈ˢ fst w ⟩
  X∈w = cupʟ-inl D (sglʟ c₀) (fst X₀) hX

  -- The junk member lies in w.
  c₀∈w : ⟨ fst c₀ ∈ˢ fst w ⟩
  c₀∈w = cupʟ-inr D (sglʟ c₀) (fst c₀) (sglʟ-in c₀ (fst c₀) refl)

  -- The witness has rank at least the rank of the stage bound: the
  -- singleton of the bound lies in the junk member, and the bound lies
  -- in that singleton.  Two transitivity steps then put the bound in
  -- the stage, and irreflexivity refutes it.
  Y∈sgl : ⟨ fst K₀ ∈ˢ ⁅ fst K₀ ⁆s ⟩
  Y∈sgl = ∈sgl-intro refl

  sglY∈c₀ : ⟨ ⁅ fst K₀ ⁆s ∈ˢ fst c₀ ⟩
  sglY∈c₀ = subst (λ w → ⟨ ⁅ fst K₀ ⁆s ∈ˢ w ⟩) (sym fstC₀)
    (∈pair-introL {u = ⁅ fst K₀ ⁆s} {v = ⁅ fst K₀ , pr (# 6) (fst (numeralL 0)) ⁆}
      {y = ⁅ fst K₀ ⁆s} refl)

  w∉K : ⟨ fst w ∈ˢ fst K₀ ⟩ → Empty.⊥
  w∉K h =
    Kirr (transK Y∈sgl
      (transK sglY∈c₀ (transK c₀∈w h)))

  -- The clause tags are not 6.
  peel : {m n : ℕ} → suc m ≡ suc n → m ≡ n
  peel = cong Cubical.Data.Nat.predℕ

  2≠6 : 6 ≡ 2 → Empty.⊥
  2≠6 p = znots (sym (peel (peel p)))

  3≠6 : 6 ≡ 3 → Empty.⊥
  3≠6 p = znots (sym (peel (peel (peel p))))

  4≠6 : 6 ≡ 4 → Empty.⊥
  4≠6 p = znots (sym (peel (peel (peel (peel p)))))

  5≠6 : 6 ≡ 5 → Empty.⊥
  5≠6 p = znots (sym (peel (peel (peel (peel (peel p))))))

  8≠6 : 6 ≡ 8 → Empty.⊥
  8≠6 p = znots (peel (peel (peel (peel (peel (peel p))))))

  9≠6 : 6 ≡ 9 → Empty.⊥
  9≠6 p = znots (peel (peel (peel (peel (peel (peel p))))))

  10≠6 : 6 ≡ 10 → Empty.⊥
  10≠6 p = znots (peel (peel (peel (peel (peel (peel p))))))

  11≠6 : 6 ≡ 11 → Empty.⊥
  11≠6 p = znots (peel (peel (peel (peel (peel (peel p))))))

  -- A member equal to the junk member cannot have the shape of a
  -- clause tag: pairing is injective, numerals are injective, and the
  -- clause tag is not 6.
  c≡c₀ : (c : Sʟ) → ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩ → fst c ≡ fst c₀
  c≡c₀ c h = sglʟ-out c₀ (fst c) h

  binRefute : (k : ℕ) → (6 ≡ k → Empty.⊥) → (c ar a b : Sʟ)
            → ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → Empty.⊥
  binRefute k k≠6 c ar a b c∈ sh =
    k≠6 (#-inj′ (pr-inj (pr-inj (sym fstC₀ ∙ (sym (c≡c₀ c c∈) ∙ sh)) .snd) .fst))

  unRefute : (k : ℕ) → (6 ≡ k → Empty.⊥) → (c ar a : Sʟ)
           → ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (fst a))
           → Empty.⊥
  unRefute k k≠6 c ar a c∈ sh =
    k≠6 (#-inj′ (pr-inj (pr-inj (sym fstC₀ ∙ (sym (c≡c₀ c c∈) ∙ sh)) .snd) .fst))

  -- =============================================================
  -- CLOSEDNESS OF w.  Each clause: a member of D uses the delivered
  -- closedness of D (decoded to memberships in D, injected into w);
  -- the junk member fires no clause, because its tag is 6.
  -- =============================================================

  D⊆w : (x : V ℓ) → ⟨ x ∈ˢ fst D ⟩ → ⟨ x ∈ˢ fst w ⟩
  D⊆w x h = cupʟ-inl D (sglʟ c₀) x h

  -- One binary clause, tag k, at the w-env.  A member of D uses the
  -- delivered D-clause; the junk member fires no clause (tag 6).
  bin-clause : (k : ℕ) → (6 ≡ k → Empty.⊥) → ((c ar a b : Sʟ)
             → ⟨ fst c ∈ˢ fst D ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀) ⊨ bothSameAt zero ⟩)
             → (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩
  bin-clause k k≠6 dcl c ar a b c∈ sh =
    PT.rec (isProp× (snd (pr (fst ar) (fst a) ∈ˢ fst w))
                    (snd (pr (fst ar) (fst b) ∈ˢ fst w)))
      go (cupʟ-out D (sglʟ c₀) (fst c) c∈)
    where
    δD : Sʟ ^ 8
    δD = b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀
    premise : Type (ℓ-suc ℓ)
    premise = ⟨ fst c ∈ˢ fst D ⟩ ⊎ ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
    go : premise
       → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩
    go (inl c∈D) =
      let concl = dcl c ar a b c∈D sh
          a∈D : ⟨ pr (fst ar) (fst a) ∈ˢ fst D ⟩
          a∈D = subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
                    (suc (suc zero)) (suc zero) δD) (concl .fst)
          b∈D : ⟨ pr (fst ar) (fst b) ∈ˢ fst D ⟩
          b∈D = subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
                    (suc (suc zero)) zero δD) (concl .snd)
      in D⊆w (pr (fst ar) (fst a)) a∈D , D⊆w (pr (fst ar) (fst b)) b∈D
    go (inr c∈s) = Empty.rec
      {A = ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩}
      (binRefute k k≠6 c ar a b c∈s sh)

  and-g : (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
        → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
        → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩
  and-g = bin-clause 2 2≠6 (λ c ar a b c∈D sh →
    hcl .fst c c∈D ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
                (suc (suc (suc zero))) (suc (suc zero)) 2
                (suc zero) zero (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  and-closed : ⟨ (w ∷ γ₀) ⊨ binShapeAt zero 2 (bothSameAt zero) ⟩
  and-closed = binSameClosed-in zero 2 (w ∷ γ₀) and-g

  or-g : (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
       → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
       → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩
  or-g = bin-clause 3 3≠6 (λ c ar a b c∈D sh →
    hcl .snd .fst c c∈D ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
                (suc (suc (suc zero))) (suc (suc zero)) 3
                (suc zero) zero (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  or-closed : ⟨ (w ∷ γ₀) ⊨ binShapeAt zero 3 (bothSameAt zero) ⟩
  or-closed = binSameClosed-in zero 3 (w ∷ γ₀) or-g

  imp-g : (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
        → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
        → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩ × ⟨ pr (fst ar) (fst b) ∈ˢ fst w ⟩
  imp-g = bin-clause 4 4≠6 (λ c ar a b c∈D sh →
    hcl .snd .snd .fst c c∈D ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
                (suc (suc (suc zero))) (suc (suc zero)) 4
                (suc zero) zero (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  imp-closed : ⟨ (w ∷ γ₀) ⊨ binShapeAt zero 4 (bothSameAt zero) ⟩
  imp-closed = binSameClosed-in zero 4 (w ∷ γ₀) imp-g

  -- One unary same-arity clause, tag k, at the w-env.
  un-clause : (k : ℕ) → (6 ≡ k → Empty.⊥) → ((c ar a : Sʟ)
            → ⟨ fst c ∈ˢ fst D ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ (a ∷ ar ∷ c ∷ D ∷ γ₀) ⊨ oneSameAt zero ⟩)
            → (c ar a : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩
  un-clause k k≠6 dcl c ar a c∈ sh =
    PT.rec (snd (pr (fst ar) (fst a) ∈ˢ fst w)) go
      (cupʟ-out D (sglʟ c₀) (fst c) c∈)
    where
    δD : Sʟ ^ 7
    δD = a ∷ ar ∷ c ∷ D ∷ γ₀
    premise : Type (ℓ-suc ℓ)
    premise = ⟨ fst c ∈ˢ fst D ⟩ ⊎ ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
    go : premise → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩
    go (inl c∈D) =
      let concl = dcl c ar a c∈D sh
          a∈D : ⟨ pr (fst ar) (fst a) ∈ˢ fst D ⟩
          a∈D = subst ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc zero) zero δD) concl
      in D⊆w (pr (fst ar) (fst a)) a∈D
    go (inr c∈s) = Empty.rec
      {A = ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩}
      (unRefute k k≠6 c ar a c∈s sh)

  neg-g : (c ar a : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
        → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
        → ⟨ pr (fst ar) (fst a) ∈ˢ fst w ⟩
  neg-g = un-clause 5 5≠6 (λ c ar a c∈D sh →
    hcl .snd .snd .snd .fst c c∈D ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate
                (suc (suc zero)) (suc zero) 5 zero (a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  neg-closed : ⟨ (w ∷ γ₀) ⊨ unShapeAt zero 5 (oneSameAt zero) ⟩
  neg-closed = unSameClosed-in zero 5 (w ∷ γ₀) neg-g

  -- One unary successor-arity clause, tag k, at the w-env.
  up-clause : (k : ℕ) → (6 ≡ k → Empty.⊥) → ((c ar a : Sʟ)
            → ⟨ fst c ∈ˢ fst D ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ (a ∷ ar ∷ c ∷ D ∷ γ₀) ⊨ oneSuccAt zero ⟩)
            → (c ar a : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩
  up-clause k k≠6 dcl c ar a c∈ sh =
    PT.rec (snd (pr (sucV (fst ar)) (fst a) ∈ˢ fst w)) go
      (cupʟ-out D (sglʟ c₀) (fst c) c∈)
    where
    δD : Sʟ ^ 7
    δD = a ∷ ar ∷ c ∷ D ∷ γ₀
    premise : Type (ℓ-suc ℓ)
    premise = ⟨ fst c ∈ˢ fst D ⟩ ⊎ ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
    go : premise → ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩
    go (inl c∈D) = PT.rec (snd (pr (sucV (fst ar)) (fst a) ∈ˢ fst w))
      via (dcl c ar a c∈D sh)
      where
      via : Σ[ z ∈ Sʟ ] (⟨ (z ∷ δD) ⊨ (sucAtL (suc (suc zero)) zero
                            ∧̇ appAt (suc (suc (suc (suc zero)))) zero (suc zero)) ⟩)
          → ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩
      via (z , (sz , ap)) =
        let hz : fst z ≡ sucV (fst ar)
            hz = subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) zero (z ∷ δD)) sz
            ha : ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst D ⟩
            ha = subst (λ q → ⟨ pr q (fst a) ∈ˢ fst D ⟩) hz
                   (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero)))) zero
                         (suc zero) (z ∷ δD)) ap)
        in D⊆w (pr (sucV (fst ar)) (fst a)) ha
    go (inr c∈s) = Empty.rec
      {A = ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩}
      (unRefute k k≠6 c ar a c∈s sh)

  exist-g : (c ar a : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
          → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
          → ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩
  exist-g = up-clause 8 8≠6 (λ c ar a c∈D sh →
    hcl .snd .snd .snd .snd .fst c c∈D ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate
                (suc (suc zero)) (suc zero) 8 zero (a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  exist-closed : ⟨ (w ∷ γ₀) ⊨ unShapeAt zero 8 (oneSuccAt zero) ⟩
  exist-closed = unSuccClosed-in zero 8 (w ∷ γ₀) exist-g

  forall-g : (c ar a : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ pr (sucV (fst ar)) (fst a) ∈ˢ fst w ⟩
  forall-g = up-clause 9 9≠6 (λ c ar a c∈D sh →
    hcl .snd .snd .snd .snd .snd .fst c c∈D ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate
                (suc (suc zero)) (suc zero) 9 zero (a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  forall-closed : ⟨ (w ∷ γ₀) ⊨ unShapeAt zero 9 (oneSuccAt zero) ⟩
  forall-closed = unSuccClosed-in zero 9 (w ∷ γ₀) forall-g

  -- One binary successor-arity clause, tag k, at the w-env.
  up2-clause : (k : ℕ) → (6 ≡ k → Empty.⊥) → ((c ar a b : Sʟ)
             → ⟨ fst c ∈ˢ fst D ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀) ⊨ succSndAt zero ⟩)
             → (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩
  up2-clause k k≠6 dcl c ar a b c∈ sh =
    PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ˢ fst w)) go
      (cupʟ-out D (sglʟ c₀) (fst c) c∈)
    where
    δD : Sʟ ^ 8
    δD = b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀
    premise : Type (ℓ-suc ℓ)
    premise = ⟨ fst c ∈ˢ fst D ⟩ ⊎ ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
    go : premise → ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩
    go (inl c∈D) = PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ˢ fst w))
      via (dcl c ar a b c∈D sh)
      where
      via : Σ[ z ∈ Sʟ ] (⟨ (z ∷ δD) ⊨ (sucAtL (suc (suc (suc zero))) zero
                            ∧̇ appAt (suc (suc (suc (suc (suc zero))))) zero
                                       (suc zero)) ⟩)
          → ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩
      via (z , (sz , ap)) =
        let hz : fst z ≡ sucV (fst ar)
            hz = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc zero))) zero (z ∷ δD)) sz
            hb : ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst D ⟩
            hb = subst (λ q → ⟨ pr q (fst b) ∈ˢ fst D ⟩) hz
                   (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc zero))))) zero
                         (suc zero) (z ∷ δD)) ap)
        in D⊆w (pr (sucV (fst ar)) (fst b)) hb
    go (inr c∈s) = Empty.rec
      {A = ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩}
      (binRefute k k≠6 c ar a b c∈s sh)

  allIn-g : (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
          → fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
          → ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩
  allIn-g = up2-clause 10 10≠6 (λ c ar a b c∈D sh →
    hcl .snd .snd .snd .snd .snd .snd .fst c c∈D ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
                (suc (suc (suc zero))) (suc (suc zero)) 10
                (suc zero) zero (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  allIn-closed : ⟨ (w ∷ γ₀) ⊨ binShapeAt zero 10 (succSndAt zero) ⟩
  allIn-closed = binSuccClosed-in zero 10 (w ∷ γ₀) allIn-g

  exIn-g : (c ar a b : Sʟ) → ⟨ fst c ∈ˢ fst w ⟩
         → fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
         → ⟨ pr (sucV (fst ar)) (fst b) ∈ˢ fst w ⟩
  exIn-g = up2-clause 11 11≠6 (λ c ar a b c∈D sh →
    hcl .snd .snd .snd .snd .snd .snd .snd c c∈D ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
                (suc (suc (suc zero))) (suc (suc zero)) 11
                (suc zero) zero (b ∷ a ∷ ar ∷ c ∷ D ∷ γ₀))) sh))

  exIn-closed : ⟨ (w ∷ γ₀) ⊨ binShapeAt zero 11 (succSndAt zero) ⟩
  exIn-closed = binSuccClosed-in zero 11 (w ∷ γ₀) exIn-g

  wcl : ⟨ (w ∷ γ₀) ⊨ closedAt zero ⟩
  wcl = and-closed , ( or-closed , ( imp-closed , ( neg-closed
      , ( exist-closed , ( forall-closed , ( allIn-closed , exIn-closed ) ) ) ) ) )

  -- =============================================================
  -- SHAPEDNESS OF w.  A member of D is shaped by the delivered
  -- shapedness of D (the satisfaction of `shapes` never reads the set
  -- slot, so the D-env proof transfers to the w-env definitionally).
  -- The junk member is a tag-6 key with the numeral zero payload.
  -- =============================================================

  cun6 : (c : Sʟ) → fst c ≡ pr (fst K₀) (pr (# 6) (fst (numeralL 0)))
       → ⟨ (c ∷ w ∷ γ₀) ⊨ unForm 6 zeroPay ⟩
  cun6 c eq = ∣ K₀ , ∣ numeralL 0 , ( arity6 , zero6 ) ∣₁ ∣₁
    where
    δ : Sʟ ^ 7
    δ = numeralL 0 ∷ K₀ ∷ c ∷ w ∷ γ₀
    arity6 : ⟨ δ ⊨ arityTagAtL (suc (suc zero)) (suc zero) 6 zero ⟩
    arity6 = subst ⟨_⟩ (sym (arityTagAtL-adequate (suc (suc zero))
              (suc zero) 6 zero δ)) eq
    zero6 : ⟨ δ ⊨ (var zero ≐ con (numeralL 0)) ⟩
    zero6 = refl

  cshapes : (c : Sʟ) → fst c ≡ pr (fst K₀) (pr (# 6) (fst (numeralL 0)))
          → ⟨ (c ∷ w ∷ γ₀) ⊨ shapes {n = 4} (suc zero) ⟩
  cshapes c eq =
    ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl (cun6 c eq) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

  wsh : ⟨ (w ∷ γ₀) ⊨ shapedAt zero (suc zero) ⟩
  wsh c c∈ =
    PT.rec (snd ((c ∷ w ∷ γ₀) ⊨ shapes {n = 4} (suc zero))) go
      (cupʟ-out D (sglʟ c₀) (fst c) c∈)
    where
    premise : Type (ℓ-suc ℓ)
    premise = ⟨ fst c ∈ˢ fst D ⟩ ⊎ ⟨ fst c ∈ˢ fst (sglʟ c₀) ⟩
    go : premise → ⟨ (c ∷ w ∷ γ₀) ⊨ shapes {n = 4} (suc zero) ⟩
    go (inl c∈D) = hsh c c∈D
    go (inr c∈s) = cshapes c (c≡c₀ c c∈s ∙ fstC₀)

  -- =============================================================
  -- THE REFUTATION
  -- =============================================================

  witK-type : Type (ℓ-suc ℓ)
  witK-type = (w : Sʟ) → ⟨ (w ∷ γ₀) ⊨ ((var (suc (suc (suc zero))) ∈̇ var zero)
             ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
           → ⟨ fst w ∈ˢ fst K₀ ⟩

  witnessPremise : ⟨ (w ∷ γ₀) ⊨ ((var (suc (suc (suc zero))) ∈̇ var zero)
                    ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
  witnessPremise = X∈w , ( wcl , wsh )

  refute : witK-type → Empty.⊥
  refute witK = w∉K (witK w witnessPremise)

-- =====================================================================
-- THE STAGE INSTANTIATION.  K0 = LsetS lam, A0 = LsetS alpha, and the
-- formula is truth over the empty alphabet, so its key lies in the
-- delivered subformula closure, which is closed and shaped over A0 by
-- the delivered closureClosed and closureShaped.
-- =====================================================================
module StageRefute
  (lam : V ℓ) (ordλ : IsOrd lam)
  (α : V ℓ) (ordα : IsOrd α)
  where

  A₀ : Sʟ
  A₀ = LsetS α ordα

  K₀ : Sʟ
  K₀ = LsetS lam ordλ

  -- the empty alphabet: no constants, so every carrier is a carrier.
  K : Type ℓ
  K = Lift Empty.⊥

  ι : K → V ℓ
  ι = λ { (lift ()) }

  ιL : (k : K) → ⟨ isL (ι k) ⟩
  ιL = λ { (lift ()) }

  φ : Formula K zero
  φ = ⊤̇

  X₀ : Sʟ
  X₀ = key ι ιL φ , keyL ι ιL φ

  D : Sʟ
  D = clo ι ιL φ

  hX : ⟨ fst X₀ ∈ˢ fst D ⟩
  hX = key∈closure ι ιL φ

  hcl : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ closedAt zero ⟩
  hcl = closureClosed ι ιL φ (A₀ ∷ K₀ ∷ X₀ ∷ [])

  hsh : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ shapedAt zero (suc zero) ⟩
  hsh = closureShaped ι ιL φ zero (A₀ ∷ K₀ ∷ X₀ ∷ [])
    (λ { (lift ()) })

  transK : {x y : V ℓ} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ fst K₀ ⟩ → ⟨ y ∈ˢ fst K₀ ⟩
  transK = layer-trans (Lset-layer lam)

  Kirr : ⟨ fst K₀ ∈ˢ fst K₀ ⟩ → Empty.⊥
  Kirr = ∈-irrefl (fst K₀)

  module R = Refute A₀ K₀ X₀ D hX hcl hsh transK Kirr

  -- THE MACHINE-CHECKED REFUTATION AT THE STAGE: the witK type at the
  -- stage frame is uninhabited.
  stage-refute : R.witK-type → Empty.⊥
  stage-refute = R.refute

-- THE SAME REFUTATION AT A COMPOUND FORMULA.  This second instantiation
-- confirms the Refute module is generic in the formula: the junk member
-- does not depend on which formula's key the set must contain.
module StageRefute2
  (lam : V ℓ) (ordλ : IsOrd lam)
  (α : V ℓ) (ordα : IsOrd α)
  where

  K : Type ℓ
  K = Lift Empty.⊥

  ι : K → V ℓ
  ι = λ { (lift ()) }

  ιL : (k : K) → ⟨ isL (ι k) ⟩
  ιL = λ { (lift ()) }

  φ : Formula K zero
  φ = ⊤̇ ∧̇ ⊤̇

  A₀ : Sʟ
  A₀ = LsetS α ordα

  K₀ : Sʟ
  K₀ = LsetS lam ordλ

  X₀ : Sʟ
  X₀ = key ι ιL φ , keyL ι ιL φ

  D : Sʟ
  D = clo ι ιL φ

  hX : ⟨ fst X₀ ∈ˢ fst D ⟩
  hX = key∈closure ι ιL φ

  hcl : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ closedAt zero ⟩
  hcl = closureClosed ι ιL φ (A₀ ∷ K₀ ∷ X₀ ∷ [])

  hsh : ⟨ (D ∷ A₀ ∷ K₀ ∷ X₀ ∷ []) ⊨ shapedAt zero (suc zero) ⟩
  hsh = closureShaped ι ιL φ zero (A₀ ∷ K₀ ∷ X₀ ∷ [])
    (λ { (lift ()) })

  module R = Refute A₀ K₀ X₀ D hX hcl hsh
    (layer-trans (Lset-layer lam)) (∈-irrefl (fst K₀))

  stage-refute2 : R.witK-type → Empty.⊥
  stage-refute2 = R.refute
