{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.61] probe A: the leaf chain ports against the master.
--
-- The content of this probe is exactly what the master placement
-- carries: TagAgree/KeyAgree/EnvOneAgree/DefinesAgree (ProbeLJ154A),
-- the TwelveAgree composition (ProbeLJ155B), SatGraphAgree
-- (ProbeLJ156A section 7) and ShapedAgree/WitnessAgree/LeafAgree
-- (ProbeLJ157A sections 4 to 5), all re-pointed to the master's own
-- modules.  Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ161A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∧̇_; _∨̇_; _⇒̇_; _≐_; _∈̇_; ∃̇_; ∃̇∈; ∀̇∈; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; tagAtL; tagAtL-adequate; extAt
        ; closedAt; domAt; appAt; appAt-adequate; prʟ; prʟ-fst
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt
        ; forallClauseAt; allInClauseAt; exInClauseAt )
open import L.Coding.Shape {ℓ} using ( shapedAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
open import L.Condensation {ℓ} lem using
  ( tagBS; keyArBS; envOneBndS; DefinesBS; closedBS; domB
  ; shapedBS; hasWitnessBS; isCodeBS; DefBodyB
  ; extAtB→extAt; extAt→extAtB
  ; module Mem; module Eq; module And; module Or; module Imp
  ; module Neg; module Top; module Bot; module Exist; module Forall
  ; module AllIn; module ExIn; module SatGraphB
  ; module ShapesAgree; module ClosedAgree; module DomainAgree )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

-- =====================================================================
-- THE TAG TRANSFER.  tagBS s tag x K = "exists t in K: t is the tag
-- slot and the s-slot is the pair (t, x-slot)".  tagAtL s k x =
-- "exists t: t = #k and the s-slot is the pair (t, x-slot)".  The two
-- agree when the tag slot holds the numeral #k and the numeral lies in
-- K.
-- =====================================================================
module TagAgree {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ γ ⊨ tagBS s tag x K ⟩
  out h = ∣ numeralL k , ( numK , ( sym tagEq , hp ) ) ∣₁
    where
    h' : ⟨ PairIs (fst (lookup s γ)) (pr (fst (numeralL k)) (fst (lookup x γ))) ⟩
    h' = subst ⟨_⟩
           (cong (λ w → PairIs (fst (lookup s γ)) (pr w (fst (lookup x γ))))
             (sym (numeralL-fst k)))
           (subst ⟨_⟩ (tagAtL-adequate s k x γ) h)
    hp : ⟨ (numeralL k ∷ γ) ⊨ prAtL (suc s) zero (suc x) ⟩
    hp = subst ⟨_⟩ (sym (prAtL-adequate {suc n} (suc s) zero (suc x) (numeralL k ∷ γ))) h'

  back : ⟨ γ ⊨ tagBS s tag x K ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  back h = subst ⟨_⟩ (sym (tagAtL-adequate s k x γ))
    (subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
      (numeralL-fst k) go)
    where
    go : fst (lookup s γ) ≡ pr (fst (numeralL k)) (fst (lookup x γ))
    go = PT.rec (snd (PairIs (fst (lookup s γ))
                       (pr (fst (numeralL k)) (fst (lookup x γ)))))
      (λ { (t , (tK , (te , tp))) →
        subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
          (te ∙ tagEq)
          (subst ⟨_⟩ (prAtL-adequate {suc n} (suc s) zero (suc x) (t ∷ γ)) tp) })
      h

-- =====================================================================
-- THE KEY-ARITY TRANSFER.  keyArBS c tag K = "exists t ar in K: ar is
-- the tag slot and the c-slot is the pair (ar, t)".  keyArityAtL c k =
-- "exists t: the c-slot is the pair (#k, t)".  The two agree when the
-- tag slot holds #k, the numeral lies in K, and the machine's key
-- value lies in K.
-- =====================================================================
module KeyAgree {n : ℕ} (c tag K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
            → ⟨ fst t ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ keyArityAtL c k ⟩ → ⟨ γ ⊨ keyArBS c tag K ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
       → ⟨ γ ⊨ keyArBS c tag K ⟩
    go (t , ht) = ∣ t , ( keyValK t ht
        , ∣ numeralL k
            , ( numK , ( te' , hp ) ) ∣₁ ) ∣₁
      where
      te' : ⟨ (numeralL k ∷ t ∷ γ) ⊨ var zero ≐ var (suc (suc tag)) ⟩
      te' = sym tagEq
      hp : ⟨ (numeralL k ∷ t ∷ γ) ⊨ prAtL (suc (suc c)) zero (suc zero) ⟩
      hp = subst ⟨_⟩ (sym (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
             (numeralL k ∷ t ∷ γ)))
        (subst (λ u → fst (lookup (suc (suc c)) (numeralL k ∷ t ∷ γ)) ≡ pr u (fst t))
          (sym (numeralL-fst k))
          (subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (t ∷ γ)) ht))

  back : ⟨ γ ⊨ keyArBS c tag K ⟩ → ⟨ γ ⊨ keyArityAtL c k ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] (⟨ fst t ∈ fst (lookup K γ) ⟩
                    × ∥ Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩) ∥₁)
       → ⟨ γ ⊨ keyArityAtL c k ⟩
    go (t , tK , hw) = PT.rec squash₁ go₂ hw
      where
      go₂ : Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩)
          → ⟨ γ ⊨ keyArityAtL c k ⟩
      go₂ (ar , arK , (ae , ap)) =
        ∣ t , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (t ∷ γ)))
              (subst (λ w → fst (lookup (suc c) (t ∷ γ)) ≡ pr w (fst (lookup zero (t ∷ γ))))
                (numeralL-fst k)
                (subst (λ u → fst (lookup (suc (suc c)) (ar ∷ t ∷ γ)) ≡ pr u (fst t))
                  (ae ∙ tagEq)
                  (subst ⟨_⟩ (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
                    (ar ∷ t ∷ γ)) ap))) ∣₁


-- =====================================================================
-- THE ONE-ENTRY-ENVIRONMENT TRANSFER.  envOneBndS v K N0 at
-- E ∷ x' ∷ γ = "the set at E is exactly the satisfiers of tagBS in K",
-- envOneAt zero (suc zero) = "the set at E is exactly the satisfiers
-- of tagAtL".  The two agree when the N0 slot holds #0, the numeral
-- lies in K, and every machine satisfier lies in K.
-- =====================================================================
module EnvOneAgree {m : ℕ} (v K N0 : Fin m) (γ : S ^ (2 + m))
  (N0eq : fst (lookup (suc (suc N0)) γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc K)) γ) ⟩)
  (pairK : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst z ∈ fst (lookup (suc (suc K)) γ) ⟩) where

  φB : Formula S (3 + m)
  φB = tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K)))

  φ : Formula S (3 + m)
  φ = tagAtL zero 0 (suc (suc zero))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  fwd z = T.back
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  bwd z = T.out
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  out : ⟨ γ ⊨ envOneAt zero (suc zero) ⟩ → ⟨ γ ⊨ envOneBndS v K N0 ⟩
  out = extAt→extAtB zero (suc (suc K)) φB φ γ fwd bwd

  back : ⟨ γ ⊨ envOneBndS v K N0 ⟩ → ⟨ γ ⊨ envOneAt zero (suc zero) ⟩
  back = extAtB→extAt zero (suc (suc K)) φB φ γ fwd bwd pairK

-- =====================================================================
-- THE DEFINES TRANSFER.  DefinesBS x w v K N0 at γ = "the set at x is
-- exactly the z in w with a K-bounded one-entry environment E with z
-- in v"; DefinesAt x w v is the same with the bounds removed.  The
-- two agree when the N0 slot holds #0, the numeral and every
-- one-entry environment lie in K, and the machine satisfiers lie in
-- K.
-- =====================================================================
module DefinesAgree {m : ℕ} (x w v K N0 : Fin m) (γ : S ^ m)
  (N0eq : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (pairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst w' ∈ fst (lookup K γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨
             ((var zero ∈̇ var (suc w)) ∧̇
              ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  bodyB : Formula S (suc m)
  bodyB = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇∈ (var (suc K)) (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v))))

  bodyM : Formula S (suc m)
  bodyM = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyB ⟩ → ⟨ (z ∷ γ) ⊨ bodyM ⟩
  fwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] (⟨ fst E ∈ fst (lookup K γ) ⟩
                    × ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩)
       → ⟨ (z ∷ γ) ⊨ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (EK , hE)) = ∣ E , ( eOne , hE .snd ) ∣₁
      where
      eOne : ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
      eOne = EA.back (hE .fst)
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyM ⟩ → ⟨ (z ∷ γ) ⊨ bodyB ⟩
  bwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero)
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩
       → ⟨ (z ∷ γ) ⊨ ∃̇∈ (var (suc K))
             (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (hE , hv)) = ∣ E , ( envK E z hE , ( eB , hv ) ) ∣₁
      where
      eB : ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0 ⟩
      eB = EA.out hE
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  out : ⟨ γ ⊨ DefinesAt x w v ⟩ → ⟨ γ ⊨ DefinesBS x w v K N0 ⟩
  out = extAt→extAtB x K bodyB bodyM γ fwd bwd

  back : ⟨ γ ⊨ DefinesBS x w v K N0 ⟩ → ⟨ γ ⊨ DefinesAt x w v ⟩
  back = extAtB→extAt x K bodyB bodyM γ fwd bwd satK

-- =====================================================================
-- THE TWELVE-ROW CONJUNCTION AT THE TWELVE FRAME.  The row transfers
-- are parameters; the composition threads the conjunction.
-- =====================================================================
module TwelveAgree {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (mem-out : ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N0))))))
                 (suc (suc (suc (suc (suc (suc K))))))
                 (suc (suc (suc (suc (suc (suc t0))))))
                 (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (mem-back : ⟨ γ ⊨ Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N0))))))
                 (suc (suc (suc (suc (suc (suc K))))))
                 (suc (suc (suc (suc (suc (suc t0))))))
                 (suc (suc (suc (suc (suc (suc t1)))))) ⟩
           → ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (eq-out : ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩
          → ⟨ γ ⊨ Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N1))))))
                (suc (suc (suc (suc (suc (suc K))))))
                (suc (suc (suc (suc (suc (suc t0))))))
                (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (eq-back : ⟨ γ ⊨ Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N1))))))
                (suc (suc (suc (suc (suc (suc K))))))
                (suc (suc (suc (suc (suc (suc t0))))))
                (suc (suc (suc (suc (suc (suc t1)))))) ⟩
          → ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (and-out : ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩
           → ⟨ γ ⊨ And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N2))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (and-back : ⟨ γ ⊨ And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N2))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩)
  (or-out : ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩
          → ⟨ γ ⊨ Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N3))))))
                (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (or-back : ⟨ γ ⊨ Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N3))))))
                (suc (suc (suc (suc (suc (suc K)))))) ⟩
          → ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩)
  (imp-out : ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N4))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (imp-back : ⟨ γ ⊨ Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N4))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (neg-out : ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N5))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (neg-back : ⟨ γ ⊨ Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N5))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (top-out : ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N6))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (top-back : ⟨ γ ⊨ Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N6))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (bot-out : ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩
           → ⟨ γ ⊨ Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N7))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (bot-back : ⟨ γ ⊨ Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N7))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩)
  (exist-out : ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩
             → ⟨ γ ⊨ Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N8))))))
                   (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (exist-back : ⟨ γ ⊨ Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N8))))))
                   (suc (suc (suc (suc (suc (suc K)))))) ⟩
             → ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (forall-out : ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ γ ⊨ Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                    (suc (suc (suc (suc (suc (suc N9))))))
                    (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (forall-back : ⟨ γ ⊨ Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                    (suc (suc (suc (suc (suc (suc N9))))))
                    (suc (suc (suc (suc (suc (suc K)))))) ⟩
              → ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (allin-out : ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩
             → ⟨ γ ⊨ AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N10))))))
                   (suc (suc (suc (suc (suc (suc K))))))
                   (suc (suc (suc (suc (suc (suc t0))))))
                   (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (allin-back : ⟨ γ ⊨ AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N10))))))
                   (suc (suc (suc (suc (suc (suc K))))))
                   (suc (suc (suc (suc (suc (suc t0))))))
                   (suc (suc (suc (suc (suc (suc t1)))))) ⟩
             → ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (exin-out : ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩
            → ⟨ γ ⊨ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc t0))))))
                  (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (exin-back : ⟨ γ ⊨ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc t0))))))
                  (suc (suc (suc (suc (suc (suc t1)))))) ⟩
            → ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩) where

  twelveB : Formula S (11 + n)
  twelveB =
    Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N0))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N1))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N2))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N3))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N4))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N5))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N6))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N7))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N8))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N9))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N10))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N11))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      ((suc (suc (suc (suc (suc (suc t1)))))))))))))))))

  out : ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ twelveB ⟩
  out h =
    ( mem-out (h .fst)
    , ( eq-out (h .snd .fst)
      , ( and-out (h .snd .snd .fst)
        , ( or-out (h .snd .snd .snd .fst)
          , ( imp-out (h .snd .snd .snd .snd .fst)
            , ( neg-out (h .snd .snd .snd .snd .snd .fst)
              , ( top-out (h .snd .snd .snd .snd .snd .snd .fst)
                , ( bot-out (h .snd .snd .snd .snd .snd .snd .snd .fst)
                  , ( exist-out (h .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                    , ( forall-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                      , ( allin-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                        , exin-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) )))))))))))

  back : ⟨ γ ⊨ twelveB ⟩ → ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  back h =
    ( mem-back (h .fst)
    , ( eq-back (h .snd .fst)
      , ( and-back (h .snd .snd .fst)
        , ( or-back (h .snd .snd .snd .fst)
          , ( imp-back (h .snd .snd .snd .snd .fst)
            , ( neg-back (h .snd .snd .snd .snd .snd .fst)
              , ( top-back (h .snd .snd .snd .snd .snd .snd .fst)
                , ( bot-back (h .snd .snd .snd .snd .snd .snd .snd .fst)
                  , ( exist-back (h .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                    , ( forall-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                      , ( allin-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                        , exin-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) )))))))))))

-- =====================================================================
-- SatGraphAgree AT THE GRAPH FRAME.
-- SatGraphB.satGraphB w K Ns ts against satGraphAt (sh3 w) (suc zero)
-- zero at the 8-deep environment, composing TwelveAgree (parameters),
-- ClosedAgree, DomainAgree, the pin/appAt identities and the three
-- existential-frame transfers.
-- =====================================================================
module SatGraphAgree {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  (tagEq2 : fst (lookup (suc (suc (suc N2))) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc N3))) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc N4))) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc N5))) γ) ≡ fst (numeralL 5))
  (tagEq8 : fst (lookup (suc (suc (suc N8))) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc N9))) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc N10))) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc N11))) γ) ≡ fst (numeralL 11))
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (codesK : (d e f : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (unCodesK : (d e f : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (closedEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                    × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
               → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                 × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (witK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
             (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
             ∧̇ (closedAt (suc (suc zero))
               ∧̇ (domAt (suc zero) (suc (suc zero))
                 ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                   ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  body-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
           → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedBS (suc (suc zero))
                     (suc (suc (suc (suc (suc (suc K))))))
                     (suc (suc (suc (suc (suc (suc N2))))))
                     (suc (suc (suc (suc (suc (suc N3))))))
                     (suc (suc (suc (suc (suc (suc N4))))))
                     (suc (suc (suc (suc (suc (suc N5))))))
                     (suc (suc (suc (suc (suc (suc N8))))))
                     (suc (suc (suc (suc (suc (suc N9))))))
                     (suc (suc (suc (suc (suc (suc N10))))))
                     (suc (suc (suc (suc (suc (suc N11))))))
                 ∧̇ (domB (suc zero) (suc (suc zero))
                        (suc (suc (suc (suc (suc (suc K))))))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
  body-out d e f h = ( h .fst
                     , ( CA.out (h .snd .fst)
                       , ( DA.out (h .snd .snd .fst)
                         , ( h .snd .snd .snd .fst
                           , twelve-out d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11)))))) (f ∷ e ∷ d ∷ γ)
                  tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                  numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                  innerK innerPairK pairK (codesK d e f) (unCodesK d e f)
                  (closedEntryK d e f)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f) (domK d e f)

  body-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedBS (suc (suc zero))
                      (suc (suc (suc (suc (suc (suc K))))))
                      (suc (suc (suc (suc (suc (suc N2))))))
                      (suc (suc (suc (suc (suc (suc N3))))))
                      (suc (suc (suc (suc (suc (suc N4))))))
                      (suc (suc (suc (suc (suc (suc N5))))))
                      (suc (suc (suc (suc (suc (suc N8))))))
                      (suc (suc (suc (suc (suc (suc N9))))))
                      (suc (suc (suc (suc (suc (suc N10))))))
                      (suc (suc (suc (suc (suc (suc N11))))))
                  ∧̇ (domB (suc zero) (suc (suc zero))
                         (suc (suc (suc (suc (suc (suc K))))))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
            → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedAt (suc (suc zero))
                  ∧̇ (domAt (suc zero) (suc (suc zero))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
  body-back d e f h = ( h .fst
                      , ( CA.back (h .snd .fst)
                        , ( DA.back (h .snd .snd .fst)
                          , ( h .snd .snd .snd .fst
                            , twelve-back d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11)))))) (f ∷ e ∷ d ∷ γ)
                  tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                  numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                  innerK innerPairK pairK (codesK d e f) (unCodesK d e f)
                  (closedEntryK d e f)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f) (domK d e f)

  sh3 : ∀ {m} → Fin m → Fin (3 + m)
  sh3 i = suc (suc (suc i))

  out : ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
      → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out h = PT.rec squash₁
    (λ { (d , hT) → PT.rec squash₁
      (λ { (e , hb) → PT.rec squash₁
        (λ { (f , body) →
          let ks = witK d e f body
          in ∣ d , ( ks .fst
                   , ∣ e , ( ks .snd .fst
                           , ∣ f , ( ks .snd .snd , body-out d e f body ) ∣₁ )
                     ∣₁ ) ∣₁ })
        hb })
      hT })
    h

  back : ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
  back h = PT.rec squash₁
    (λ { (d , (dK , hT)) → PT.rec squash₁
      (λ { (e , (eK , hb)) → PT.rec squash₁
        (λ { (f , (fK , body)) →
          ∣ d , ∣ e , ∣ f , body-back d e f body ∣₁ ∣₁ ∣₁ })
        hb })
      hT })
    h

-- =====================================================================
-- ShapedAgree AND WitnessAgree.
-- =====================================================================
module ShapedAgree {n : ℕ} (C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (tagEq0 : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup N1 γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup N6 γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup N7 γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (unCodesK : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ shapedAt C A ⟩ → ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ)
          tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
          numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7 numK8 numK9 numK10 numK11
          innerK innerPairK pairK carrierK arityK codesK unCodesK
    in S.out c∈ (h c c∈)

  back : ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapedAt C A ⟩
  back h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ)
          tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
          numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7 numK8 numK9 numK10 numK11
          innerK innerPairK pairK carrierK arityK codesK unCodesK
    in S.back (h c c∈)

module WitnessAgree {n : ℕ} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (tagEq0 : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup N1 γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup N6 γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup N7 γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
         → ⟨ fst w ∈ fst (lookup K γ) ⟩)
  (codesK : (w : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (unCodesK : (w : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (entryK : (w x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w ⟩
           → ⟨ fst x' ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ hasWitnessAt A x ⟩
      → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
           ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
    go (w , (hxw , (hcl , hsh))) =
      ∣ w , ( witK w (hxw , (hcl , hsh))
            , ( hxw , ( CA.out hcl , SA.out hsh ) ) ) ∣₁
      where
      module CA = ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                    numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                    innerK innerPairK pairK (codesK w) (unCodesK w) (entryK w)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                    tagEq8 tagEq9 tagEq10 tagEq11
                    numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                    numK8 numK9 numK10 numK11
                    innerK innerPairK pairK carrierK arityK (codesK w) (unCodesK w)

  back : ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] (⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                         ∧̇ (closedBS zero (suc K) (suc N2) (suc N3) (suc N4) (suc N5)
                               (suc N8) (suc N9) (suc N10) (suc N11)
                           ∧̇ shapedBS zero (suc A) (suc K)
                                (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                                (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11))) ⟩)
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
    go (w , (wK , (hxw , (hcl , hsh)))) =
      ∣ w , ( hxw , ( CA.back hcl , SA.back hsh ) ) ∣₁
      where
      module CA = ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                    numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                    innerK innerPairK pairK (codesK w) (unCodesK w) (entryK w)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                    tagEq8 tagEq9 tagEq10 tagEq11
                    numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                    numK8 numK9 numK10 numK11
                    innerK innerPairK pairK carrierK arityK (codesK w) (unCodesK w)

-- =====================================================================
-- LeafAgree: THE DefBodyB / DefBody LEAF ADEQUACY.
-- =====================================================================
module LeafAgree {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (tagEq0 : fst (lookup (suc (suc (suc N0))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc N1))) γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc (suc (suc N2))) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc N3))) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc N4))) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc N5))) γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup (suc (suc (suc N6))) γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc (suc (suc N7))) γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc (suc (suc N8))) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc N9))) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc N10))) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc N11))) γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (witK : (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
         → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wCodesK : (w' : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wUnCodesK : (w' : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wEntryK : (w' x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w' ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                            N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  (gCodesK : (d e f : S) → (k : ℕ) → (c ar a b : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gUnCodesK : (d e f : S) → (k : ℕ) → (c ar a : S)
              → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
              → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
         → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (graphWitK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
            → ⟨ fst t ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
             → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨ ((var zero ∈̇ var (suc (suc (suc (suc w)))))
             ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc zero))))) ⟩
         → ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  module WA = WitnessAgree {8 + n} (suc (suc (suc w))) (suc zero) (suc (suc (suc K)))
                (suc (suc (suc N0))) (suc (suc (suc N1)))
                (suc (suc (suc N2))) (suc (suc (suc N3)))
                (suc (suc (suc N4))) (suc (suc (suc N5)))
                (suc (suc (suc N6))) (suc (suc (suc N7)))
                (suc (suc (suc N8))) (suc (suc (suc N9)))
                (suc (suc (suc N10))) (suc (suc (suc N11))) γ
                tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                tagEq8 tagEq9 tagEq10 tagEq11
                numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                numK8 numK9 numK10 numK11
                innerK innerPairK pairK carrierK arityK witK wCodesK wUnCodesK wEntryK

  module KA = KeyAgree {8 + n} (suc zero) (suc (suc (suc N1))) (suc (suc (suc K))) γ 1
                tagEq1 numK1 keyValK

  module SG = SatGraphAgree {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                twelve-out twelve-back
                tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                innerK innerPairK pairK gCodesK gUnCodesK gEntryK domEntryK domK graphWitK

  module DA = DefinesAgree {8 + n} (suc (suc zero)) (suc (suc (suc w))) zero
                (suc (suc (suc K))) (suc (suc (suc N0))) γ
                tagEq0 numK0 envK defPairK satK

  ic-out : ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
         → ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
  ic-out (hk , hw) = (KA.out hk , WA.out hw)

  ic-back : ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
         → ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
  ic-back (hk , hw) = (KA.back hk , WA.back hw)

  out : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out (hcode , (hgraph , hdef)) =
    ( ic-out hcode
    , ( SG.out hgraph
      , DA.out hdef ) )

  back : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  back (hcode , (hgraph , hdef)) =
    ( ic-back hcode
    , ( SG.back hgraph
      , DA.back hdef ) )
