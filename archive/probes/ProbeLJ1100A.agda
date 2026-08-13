{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.100] probe A: the consumer's frame EXTENDED by the facts the
-- rows hold, and the [LJ-1.93] instantiation re-run against it.
--
-- The consumer (SatGraphAgree, src/L/Condensation.lagda.md:6476-6513)
-- holds KFacts (29 fields, :5734-5770) plus the six site facts.  The
-- rows (TopAgree etc.) hold, beyond that, the satisfier-in-K family,
-- the t0/t1 facts, and valK/valK-un; ten of the shared frame's facts
-- are REFUTED as stated ([LJ-1.97]) and are added here in their TIED
-- forms ([LJ-1.99]).  Every addition is a NEW HYPOTHESIS of the
-- extended frame, never a discharge; the two derivable tied forms
-- (entryK-tied, arSubK-tied) are proved below from the frame's own
-- arityK, which costs zero hypotheses.
--
-- The instantiation (module At, module F) leaves a hole at exactly
-- the composer hypotheses whose stated types are still empty:
-- tmKeyK, entryK, arSubK-mem/neg/top/imp, keyK-neg, succK, keyK-un,
-- succK-allin, keyK-allin.  The unsolved-meta error list IS the
-- measured list.  Exit 42 expected, 11 unsolved metas.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1100A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; var; _≐_; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
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
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open KFactsNS
open KFacts

-- The consumer's exact telescope, copied from
-- src/L/Condensation.lagda.md:6476-6522 (same as ProbeLJ193B).
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

  -- Copied verbatim from src/L/Condensation.lagda.md:6520-6575.
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

  -- THE EXTENDED CONSUMER FRAME, at the rows' own layout.
  --
  -- Every parameter below is a NEW HYPOTHESIS of the extended frame,
  -- never a discharge (C-38).  The types are copied verbatim from
  -- AbstractFrame (src/L/Condensation/TwelveAgree.lagda.md:86-243)
  -- where the rows state them; the K-slot matches because
  -- lookup (suc^6 K) γ' ≡ lookup (suc^3 K) γ.
  --
  -- The rows hold these facts at their own telescopes (e.g. TopAgree
  -- src/L/Condensation.lagda.md:3488-3504, ForallAgree :3658-3671,
  -- AllInAgree :4709-4730).  None of the refutation recipes of
  -- [LJ-1.97] applies to any of them: the satisfier-in-K conclusions
  -- are pinned by a satisfaction premise, and the t0/t1 facts are
  -- slot equalities and a slot membership.
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
      -- THE TIED FORMS, [LJ-1.99].  Each is a NEW HYPOTHESIS of the
      -- extended frame, in the shape the row sites supply.  None of
      -- them has the type of the refuted AbstractFrame fact it repairs,
      -- so none can supply that fact in the instantiation below.
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
  
      -- The AbstractFrame application at the EXTENDED consumer frame.
      -- The 28 new frame facts supply their exact AbstractFrame
      -- hypotheses; transK comes from arityK by a binder swap as in
      -- [LJ-1.93].  The 11 holes are exactly the hypotheses whose
      -- stated types are refuted ([LJ-1.95], [LJ-1.97]); their tied
      -- forms above are different types and cannot supply them.
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
        {!!} -- tmKeyK : refuted at every frame ([LJ-1.95]); the tied
              --           keyValK shape is a different type
        (kf .numK1) -- num1K
        envK-mem envK-neg envK-top envK-imp envK-allin
        {!!} -- entryK : refuted ([LJ-1.97]); entryK-tied needs z ∈ E
              --           and E ∈ K, absent from this type
        {!!} -- arSubK-mem : refuted; arSubK-tied needs ar ∈ K
        {!!} -- arSubK-neg : refuted
        {!!} -- arSubK-top : refuted
        {!!} -- arSubK-imp : refuted
        envInK-mem envInK-neg envInK-top envInK-imp
        valV valW wKfact
        (λ x a hxa haK → kf .arityK a x hxa haK) -- transK
        subK₁-and subK₀-and subK₁-imp subK₀-imp
        someEnv
        subK-neg
        {!!} -- keyK-neg : refuted; keyK-neg-tied needs ar ∈ K, a ∈ K
        {!!} -- succK : refuted; succK-tied needs ar ∈ K
        {!!} -- keyK-un : refuted; keyK-un-tied needs ar ∈ K, a ∈ K
        subK-un
        consK-exist consK-forall
        {!!} -- succK-allin : refuted; succK-allin-tied needs ar ∈ K
        {!!} -- keyK-allin : refuted; keyK-allin-tied needs ar ∈ K, b ∈ K
        subK-allin
        consK-allin
