```agda
{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.112] probe A: the repaired composer, instantiated at last.
--
-- [LJ-1.110] restated all three frames.  The eleven refuted hypotheses
-- are gone from TwelveAgree.AbstractFrame
-- (src/L/Condensation/TwelveAgree.lagda.md:45-243): tmKeyK, entryK,
-- arSubK-mem/neg/top/imp, keyK-neg, succK, keyK-un, succK-allin,
-- keyK-allin.  arityK is derived from transK inside the frame; the five
-- tied key facts are derivations from sucK and pairK.  The frame's fact
-- count fell from 69 to 59.  The consumer must now supply sucK, the
-- successor closure, which [LJ-1.110] section 2 named as the one new
-- obligation (INFERRED supply, P-x: a telescope fact, never a KFacts
-- field).
--
-- This probe re-points the [LJ-1.100] extended consumer frame at the
-- CURRENT telescope (the codesK/codesK-un shapes dropped the d e f
-- binders; sucK sits between subK-neg and subK-un) and re-runs the
-- instantiation.  The addition to the extended frame is exactly one new
-- hypothesis, sucK, and it is a new hypothesis, not a discharge (C-38).
-- The refutation attempt is the [LJ-1.109] RefuteAttempts shape: at the
-- abstract frame the only candidate premise is the K-slot element's own
-- membership, X ∈ X, refuted by the delivered ∈-irrefl, so no
-- contradiction can be forced (MEASURED premise barrier; NOT REFUTED,
-- INFERRED).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1112A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; var; _≐_; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Coding.Model {ℓ}
  using ( appAt; closedAt; domAt; envSetAt; envOverAt; tmValAt
        ; subValAt; subValSuccAt; consAtL; tagAtL )
open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module SatGraphB; KFactsCons; succU; keyU )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import L.Condensation.TwelveAgree {ℓ} lem using ( module AbstractFrame )
open import ProbeLJ199A {ℓ} lem using ( module ChainZ )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open KFactsNS
open KFacts

-- =====================================================================
-- THE REFUTATION ATTEMPT ON sucK, the one addition of this dispatch.
-- The closure is conditional: (a : S) → a ∈ K-slot → sucV a ∈ K-slot.
-- At the abstract frame the only way to force the premise is at the
-- K-slot element X itself, whose premise is X ∈ X, refuted by the
-- delivered ∈-irrefl (src/V/Hierarchy.lagda.md:155).  The premise
-- barrier is MEASURED; the non-refutation is INFERRED, exactly the
-- verdict [LJ-1.109] recorded for the same shape.
-- =====================================================================
module SucKRefute (n : ℕ) (K : Fin (5 + n)) (γ' : S ^ (11 + n)) where

  A : V ℓ
  A = fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ')

  sucK-premise-refuted :
    ⟨ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ')
       ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    → Empty.⊥
  sucK-premise-refuted = ∈-irrefl A

-- The consumer's exact telescope, copied from
-- src/L/Condensation.lagda.md:6682-6768 (same as ProbeLJ193B and
-- ProbeLJ1100A).
module PackAttempt (n : ℕ)
  (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (codesK : (d e f : S) → (k : ℕ) → (c ar a b : S)
           → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (unCodesK : (d e f : S) → (k : ℕ) → (c ar a : S)
             → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (closedEntryK : (d e f : S) → (x y : S)
                 → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                 → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                   × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x y : S)
              → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
              → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S)
         → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
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

  -- Copied verbatim from src/L/Condensation.lagda.md:6720-6768.
  lift3 : (x y z : S) → KFacts {11 + n}
            (suc (suc (suc (suc (suc (suc w))))))
            (suc (suc (suc (suc (suc (suc K))))))
            (suc (suc (suc (suc (suc (suc N0))))))
            (suc (suc (suc (suc (suc (suc N1))))))
            (suc (suc (suc (suc (suc (suc N2))))))
            (suc (suc (suc (suc (suc (suc N3))))))
            (suc (suc (suc (suc (suc (suc N4))))))
            (suc (suc (suc (suc (suc (suc N5))))))
            (suc (suc (suc (suc (suc (suc N6))))))
            (suc (suc (suc (suc (suc (suc N7))))))
            (suc (suc (suc (suc (suc (suc N8))))))
            (suc (suc (suc (suc (suc (suc N9))))))
            (suc (suc (suc (suc (suc (suc N10))))))
            (suc (suc (suc (suc (suc (suc N11))))))
            (z ∷ y ∷ x ∷ γ)
  lift3 x y z =
    KFactsCons
      (suc (suc (suc (suc (suc w))))) (suc (suc (suc (suc (suc K)))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11))))) (y ∷ x ∷ γ) z
      (KFactsCons
        (suc (suc (suc (suc w)))) (suc (suc (suc (suc K))))
        (suc (suc (suc (suc N0)))) (suc (suc (suc (suc N1))))
        (suc (suc (suc (suc N2)))) (suc (suc (suc (suc N3))))
        (suc (suc (suc (suc N4)))) (suc (suc (suc (suc N5))))
        (suc (suc (suc (suc N6)))) (suc (suc (suc (suc N7))))
        (suc (suc (suc (suc N8)))) (suc (suc (suc (suc N9))))
        (suc (suc (suc (suc N10)))) (suc (suc (suc (suc N11))))
        (x ∷ γ) y
        (KFactsCons
          (suc (suc (suc w))) (suc (suc (suc K)))
          (suc (suc (suc N0))) (suc (suc (suc N1)))
          (suc (suc (suc N2))) (suc (suc (suc N3)))
          (suc (suc (suc N4))) (suc (suc (suc N5)))
          (suc (suc (suc N6))) (suc (suc (suc N7)))
          (suc (suc (suc N8))) (suc (suc (suc N9)))
          (suc (suc (suc N10))) (suc (suc (suc N11))) γ x f))

  -- THE EXTENDED CONSUMER FRAME, at the rows' own layout.  Every
  -- parameter below is a NEW HYPOTHESIS of the extended frame, never a
  -- discharge (C-38).  The types are copied verbatim from the CURRENT
  -- AbstractFrame (src/L/Condensation/TwelveAgree.lagda.md:45-243)
  -- where the rows state them; the K-slot matches because
  -- lookup (suc^6 K) γ' ≡ lookup (suc^3 K) γ.
  --
  -- The eleven refuted hypotheses are GONE from the frame, so the
  -- extended frame no longer needs their untied forms; the six tied
  -- forms of [LJ-1.100] remain below as a record of what the consumer
  -- can hold, but the frame derives its own tied facts from sucK and
  -- pairK and consumes none of them.  The addition of THIS dispatch is
  -- sucK alone.
  module At (d e f : S) where

    γ' : S ^ (11 + n)
    γ' = f ∷ e ∷ d ∷ γ

    kf : KFacts {11 + n} (suc (suc (suc (suc (suc (suc w))))))
           (suc (suc (suc (suc (suc (suc K))))))
           (suc (suc (suc (suc (suc (suc N0))))))
           (suc (suc (suc (suc (suc (suc N1))))))
           (suc (suc (suc (suc (suc (suc N2))))))
           (suc (suc (suc (suc (suc (suc N3))))))
           (suc (suc (suc (suc (suc (suc N4))))))
           (suc (suc (suc (suc (suc (suc N5))))))
           (suc (suc (suc (suc (suc (suc N6))))))
           (suc (suc (suc (suc (suc (suc N7))))))
           (suc (suc (suc (suc (suc (suc N8))))))
           (suc (suc (suc (suc (suc (suc N9))))))
           (suc (suc (suc (suc (suc (suc N10))))))
           (suc (suc (suc (suc (suc (suc N11)))))) γ'
    kf = lift3 d e f

    module Extended
      (t0eq : fst (lookup (suc (suc (suc t0))) γ) ≡ fst (numeralL 0))
      (t1eq : fst (lookup (suc (suc (suc t1))) γ) ≡ fst (numeralL 1))
      (t0K : ⟨ fst (lookup (suc (suc (suc t0))) γ)
               ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
      (valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
              → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
      (valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
                 → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                 → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
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
      -- THE NEW HYPOTHESIS OF THIS DISPATCH (C-38): the successor
      -- closure, stated as a telescope fact of the extended consumer
      -- frame, at the consumer's own K-slot.  The frame states the
      -- same type at TwelveAgree.lagda.md:186-188.  What would supply
      -- it: a constructibility level closed under V-successor
      -- (sucV a = a ∪ ⁅a⁆s; for a ∈ L β at β < α with α limit,
      -- a ∪ ⁅a⁆s ∈ L (β+1) ⊆ L α), named at
      -- _build/lj-1.109-report.md section 2, INFERRED.  It is NOT a
      -- KFacts field (P-x): a record field carrying sucV (fst a)
      -- walls the master, MEASURED at [LJ-1.109] section 2.
      (sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
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
      -- THE TIED FORMS, [LJ-1.99], kept as a record of what the
      -- consumer can hold.  The repaired frame derives its own tied
      -- facts from sucK and pairK, so none of these is consumed by the
      -- instantiation below.
      (keyValK : (t : S) → ⟨ (t ∷ γ') ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
                → ⟨ fst t ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
      (succK-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
                  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  → succU {11 + n} (suc (suc zero)) (suc zero) zero N
                           (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c)
      (keyK-un-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
                    → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                    → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                    → keyU {11 + n} (suc (suc zero)) (suc zero) zero N
                             (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c)
      (keyK-neg-tied : (E ya yc a ar c : S)
                     → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                     → ⟨ pr (fst (lookup (suc (suc (suc (suc zero))))
                                     (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
                            (fst (lookup (suc (suc (suc zero)))
                                     (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
                         ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))
                                   (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
      (succK-allin-tied : (E ya yc b a ar c : S)
                        → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                        → ⟨ sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
                             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
      (keyK-allin-tied : (E ya yc b a ar c : S)
                       → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                       → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                       → ⟨ pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'))))
                              (fst (lookup (suc (suc (suc zero)))
                                      (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
                           ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                                     (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩) where

      -- The derivable tied forms, proved from the frame's own arityK
      -- (src/ProbeLJ199A.agda).  They cost ZERO hypotheses.
      entryK-tied : (E : S) → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  → (z x y : S) → ⟨ fst z ∈ fst E ⟩
                  → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                    × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
      entryK-tied E EK z x y z∈E p =
        ChainZ.entryK-tied-zK (suc (suc (suc (suc (suc (suc K)))))) γ' (kf .arityK)
          z x y (kf .arityK E z z∈E EK) p

      arSubK-tied : (ar x : S) → ⟨ fst x ∈ fst ar ⟩
                  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
      arSubK-tied ar x hxar arK = kf .arityK ar x hxar arK

      -- The AbstractFrame application at the EXTENDED consumer frame,
      -- re-pointed at the CURRENT telescope
      -- (src/L/Condensation/TwelveAgree.lagda.md:45-243).  All 59
      -- facts are supplied: the 26 KFacts fields and six site facts,
      -- the 26 satisfier-in-K / slot facts of the [LJ-1.100] extended
      -- frame, and the ONE new sucK.  The eleven refuted names no
      -- longer exist in the frame; the five tied key facts are
      -- derivations inside the frame and cost nothing.
      module F = AbstractFrame {n}
        N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        (kf .tagEq0) (kf .tagEq1) (kf .tagEq2) (kf .tagEq3)
        (kf .tagEq4) (kf .tagEq5) (kf .tagEq6) (kf .tagEq7)
        (kf .tagEq8) (kf .tagEq9) (kf .tagEq10) (kf .tagEq11)
        (kf .numK0) (kf .numK1) (kf .numK2) (kf .numK3)
        (kf .numK4) (kf .numK5) (kf .numK6) (kf .numK7)
        (kf .numK8) (kf .numK9) (kf .numK10) (kf .numK11)
        (kf .innerK) (kf .pairK)
        (codesK d e f) (unCodesK d e f)
        valK valK-un
        t0eq t1eq t0K
        (kf .numK1) -- num1K
        envK-mem envK-neg envK-top envK-imp envK-allin
        envInK-mem envInK-neg envInK-top envInK-imp
        valV valW wKfact
        (λ x a hxa haK → kf .arityK a x hxa haK) -- transK
        subK₁-and subK₀-and subK₁-imp subK₀-imp
        someEnv
        subK-neg
        sucK
        subK-un
        consK-exist consK-forall
        subK-allin
        consK-allin

      -- The instantiation is not merely accepted: the composer's out is
      -- usable at the consumer's frame (C-35, C-40).  This line forces
      -- F's body to elaborate, not only its telescope.
      consume-out : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
                  → ⟨ γ' ⊨ F.twelveB ⟩
      consume-out = F.out
```
