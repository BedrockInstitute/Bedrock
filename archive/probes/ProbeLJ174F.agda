{-# OPTIONS --cubical --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ174F {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL; closedAt; domAt
        ; sucAtL-adequate
        ; extAt; extAt-in-both
        ; interAt; unionAt
        ; arityTagAtL; arityTagPairAtL
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; tagAtL; tagAtL-adequate; tagPairAtL-adequate; prAtL-adequate
        ; prʟ; prʟ-fst
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binShape-out; binShape-in; unShape-out; unShape-in
        ; emptyAt; botClauseAt
        ; subValAt; subValSuccAt; binClauseAt; propRel
        ; negClauseAt; topClauseAt; forallClauseAt; existClauseAt
        ; body∀; body∃; bodyAll; bodyEx
        ; tmValAt; envSetAt; envOverAt; envOverAt-transport; implAt
        ; atomBody; memClauseAt; eqClauseAt; impClauseAt
        ; allInClauseAt; exInClauseAt
        ; svAt-in; svAt-out; domAt-intro; domAt-out; domAt-in
        ; valuesInAt-in; valuesInAt-out )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay
        ; shapedAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S
-- =====================================================================

open import ProbeLJ174P0 {ℓ} lem using (module TwelveAgree3; someEnvDef; succU; keyU; envHypB2)
open import ProbeLJ174P1 {ℓ} lem using (module TwelveAgree3b)
open import ProbeLJ174P2 {ℓ} lem using (module TwelveAgree3c)
open import ProbeLJ174P3 {ℓ} lem using (module TwelveAgree3d)

module AbstractFrameSplit {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ' : S ^ (11 + n))
  (tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ') ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ') ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ') ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ') ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ') ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ') ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ') ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ') ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ') ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ') ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ') ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ') ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (innerK : (k : ℕ) (p : S) → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (fst a))
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ') ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ') ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ')
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-top : (yc a ar c E : S) → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc zero)))
                          (suc (suc (suc (suc (suc zero))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envSetAt zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (arSubK-mem : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                          (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (arSubK-neg : (ya yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                          (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (arSubK-top : (yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero))
                                        (yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (arSubK-imp : (ya yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero))))
                                          (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-top : (yc a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc zero))))
                              (suc (suc (suc (suc (suc (suc zero)))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
           → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                             (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
           → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                             (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
            → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          zero ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc zero)) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (someEnv : someEnvDef {n} K γ')
  (subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero)))
                         (suc zero) ⟩
              → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (keyK-neg : (E ya yc a ar c : S) → ⟨
                pr (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
                   (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
                ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (succK : (N : Fin (11 + n)) (E ya yc a ar c : S) →
             succU {11 + n} (suc (suc zero)) (suc zero) zero N (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c)
  (keyK-un : (N : Fin (11 + n)) (E ya yc a ar c : S) →
               keyU {11 + n} (suc (suc zero)) (suc zero) zero N (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c)
  (subK-un : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
               subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                            (suc zero) ⟩
             → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (consK-exist : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   consAtL zero (suc zero) (suc (suc zero))
                   ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                   (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (consK-forall : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero)) ⟩
                  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                    (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (succK-allin : (E ya yc b a ar c : S) → ⟨
                   sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                                (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
                   ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                             (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (keyK-allin : (E ya yc b a ar c : S) → ⟨
                  pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                                   (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'))))
                     (fst (lookup (suc (suc (suc zero)))
                             (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
                  ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (subK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                               (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc zero)))
                               (suc zero) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (consK-allin : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
                                   (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  where


  p0b : Formula S (11 + n)
  p0b = TwelveAgree3.twelveB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin

  p1b : Formula S (11 + n)
  p1b = TwelveAgree3b.twelveB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin

  p2b : Formula S (11 + n)
  p2b = TwelveAgree3c.twelveB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin

  p3b : Formula S (11 + n)
  p3b = TwelveAgree3d.twelveB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin

  twelveB : Formula S (11 + n)
  twelveB = p0b ∧̇ (p1b ∧̇ (p2b ∧̇ p3b))

  out : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ' ⊨ twelveB ⟩
  out h =
    ( TwelveAgree3.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin h
    , ( TwelveAgree3b.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin h
    , ( TwelveAgree3c.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin h
    , TwelveAgree3d.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
        tagEq1
        tagEq2
        tagEq3
        tagEq4
        tagEq5
        tagEq6
        tagEq7
        tagEq8
        tagEq9
        tagEq10
        tagEq11
        numK0
        numK1
        numK2
        numK3
        numK4
        numK5
        numK6
        numK7
        numK8
        numK9
        numK10
        numK11
        innerK
        pairK
        codesK
        codesK-un
        valK
        valK-un
        t0eq
        t1eq
        t0K
        tmKeyK
        num1K
        envK-mem
        envK-neg
        envK-top
        envK-imp
        envK-allin
        entryK
        arSubK-mem
        arSubK-neg
        arSubK-top
        arSubK-imp
        envInK-mem
        envInK-neg
        envInK-top
        envInK-imp
        valV
        valW
        wKfact
        transK
        subK₁-and
        subK₀-and
        subK₁-imp
        subK₀-imp
        someEnv
        subK-neg
        keyK-neg
        succK
        keyK-un
        subK-un
        consK-exist
        consK-forall
        succK-allin
        keyK-allin
        subK-allin
        consK-allin h )))

  back : ⟨ γ' ⊨ twelveB ⟩ → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  back h =
    let a = TwelveAgree3.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
            tagEq1
            tagEq2
            tagEq3
            tagEq4
            tagEq5
            tagEq6
            tagEq7
            tagEq8
            tagEq9
            tagEq10
            tagEq11
            numK0
            numK1
            numK2
            numK3
            numK4
            numK5
            numK6
            numK7
            numK8
            numK9
            numK10
            numK11
            innerK
            pairK
            codesK
            codesK-un
            valK
            valK-un
            t0eq
            t1eq
            t0K
            tmKeyK
            num1K
            envK-mem
            envK-neg
            envK-top
            envK-imp
            envK-allin
            entryK
            arSubK-mem
            arSubK-neg
            arSubK-top
            arSubK-imp
            envInK-mem
            envInK-neg
            envInK-top
            envInK-imp
            valV
            valW
            wKfact
            transK
            subK₁-and
            subK₀-and
            subK₁-imp
            subK₀-imp
            someEnv
            subK-neg
            keyK-neg
            succK
            keyK-un
            subK-un
            consK-exist
            consK-forall
            succK-allin
            keyK-allin
            subK-allin
            consK-allin (h .fst)
        b = TwelveAgree3b.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
            tagEq1
            tagEq2
            tagEq3
            tagEq4
            tagEq5
            tagEq6
            tagEq7
            tagEq8
            tagEq9
            tagEq10
            tagEq11
            numK0
            numK1
            numK2
            numK3
            numK4
            numK5
            numK6
            numK7
            numK8
            numK9
            numK10
            numK11
            innerK
            pairK
            codesK
            codesK-un
            valK
            valK-un
            t0eq
            t1eq
            t0K
            tmKeyK
            num1K
            envK-mem
            envK-neg
            envK-top
            envK-imp
            envK-allin
            entryK
            arSubK-mem
            arSubK-neg
            arSubK-top
            arSubK-imp
            envInK-mem
            envInK-neg
            envInK-top
            envInK-imp
            valV
            valW
            wKfact
            transK
            subK₁-and
            subK₀-and
            subK₁-imp
            subK₀-imp
            someEnv
            subK-neg
            keyK-neg
            succK
            keyK-un
            subK-un
            consK-exist
            consK-forall
            succK-allin
            keyK-allin
            subK-allin
            consK-allin (h .snd .fst)
        c = TwelveAgree3c.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
            tagEq1
            tagEq2
            tagEq3
            tagEq4
            tagEq5
            tagEq6
            tagEq7
            tagEq8
            tagEq9
            tagEq10
            tagEq11
            numK0
            numK1
            numK2
            numK3
            numK4
            numK5
            numK6
            numK7
            numK8
            numK9
            numK10
            numK11
            innerK
            pairK
            codesK
            codesK-un
            valK
            valK-un
            t0eq
            t1eq
            t0K
            tmKeyK
            num1K
            envK-mem
            envK-neg
            envK-top
            envK-imp
            envK-allin
            entryK
            arSubK-mem
            arSubK-neg
            arSubK-top
            arSubK-imp
            envInK-mem
            envInK-neg
            envInK-top
            envInK-imp
            valV
            valW
            wKfact
            transK
            subK₁-and
            subK₀-and
            subK₁-imp
            subK₀-imp
            someEnv
            subK-neg
            keyK-neg
            succK
            keyK-un
            subK-un
            consK-exist
            consK-forall
            succK-allin
            keyK-allin
            subK-allin
            consK-allin (h .snd .snd .fst)
        d = TwelveAgree3d.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'     tagEq0
            tagEq1
            tagEq2
            tagEq3
            tagEq4
            tagEq5
            tagEq6
            tagEq7
            tagEq8
            tagEq9
            tagEq10
            tagEq11
            numK0
            numK1
            numK2
            numK3
            numK4
            numK5
            numK6
            numK7
            numK8
            numK9
            numK10
            numK11
            innerK
            pairK
            codesK
            codesK-un
            valK
            valK-un
            t0eq
            t1eq
            t0K
            tmKeyK
            num1K
            envK-mem
            envK-neg
            envK-top
            envK-imp
            envK-allin
            entryK
            arSubK-mem
            arSubK-neg
            arSubK-top
            arSubK-imp
            envInK-mem
            envInK-neg
            envInK-top
            envInK-imp
            valV
            valW
            wKfact
            transK
            subK₁-and
            subK₀-and
            subK₁-imp
            subK₀-imp
            someEnv
            subK-neg
            keyK-neg
            succK
            keyK-un
            subK-un
            consK-exist
            consK-forall
            succK-allin
            keyK-allin
            subK-allin
            consK-allin (h .snd .snd .snd)
    in ( a .fst , ( a .snd .fst , ( a .snd .snd
       , ( b .fst , ( b .snd .fst , ( b .snd .snd
       , ( c .fst , ( c .snd .fst , ( c .snd .snd
       , ( d .fst , ( d .snd .fst , d .snd .snd )))))))))))
