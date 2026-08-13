{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.93] probe B: can the consumer (SatGraphAgree) instantiate
-- TwelveAgree.AbstractFrame?
--
-- The consumer's telescope is src/L/Condensation.lagda.md:6476-6522:
-- KFacts (29 fields) plus codesK, unCodesK, closedEntryK, domEntryK,
-- domK and witK.  AbstractFrame's telescope
-- (src/L/Condensation/TwelveAgree.lagda.md:45-243) is 69 facts.
--
-- This probe supplies the 30 facts the consumer holds (27 KFacts
-- fields, num1K = numK1, codesK, unCodesK, and transK from arityK by
-- a binder swap) and leaves a hole at every AbstractFrame hypothesis
-- the consumer does not hold.
-- The unsolved-meta error list IS the measured list of hypotheses
-- with no supplier.  The two isolated attempts at the bottom (t0eq
-- from tagEq0, entryK from closedEntryK) show the concrete type
-- mismatches for two representative rows.
--
-- This probe is expected NOT to typecheck.  Untracked probe; never
-- committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ193B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; var; _≐_; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Coding.Model {ℓ} using ( appAt; closedAt; domAt )
open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module SatGraphB; KFactsCons )
open import L.Condensation.TwelveAgree {ℓ} lem using ( module AbstractFrame )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open KFactsNS
open KFacts

-- The consumer's exact telescope, copied from
-- src/L/Condensation.lagda.md:6476-6522.
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

  -- The AbstractFrame application at the consumer's frame.  The 29
  -- facts the consumer holds are supplied; the other 40 are holes.
  -- The unsolved-meta list below names every hypothesis that has no
  -- supplier in the consumer telescope.
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
      {!!} -- valK : (k : ℕ) (c ar a b yc : S) → c ∈ code-slot → shape →
            --         yc ∈ K-slot
      {!!} -- valK-un
      {!!} -- t0eq
      {!!} -- t1eq
      {!!} -- t0K
      {!!} -- tmKeyK
      (kf .numK1) -- num1K
      {!!} -- envK-mem
      {!!} -- envK-neg
      {!!} -- envK-top
      {!!} -- envK-imp
      {!!} -- envK-allin
      {!!} -- entryK
      {!!} -- arSubK-mem
      {!!} -- arSubK-neg
      {!!} -- arSubK-top
      {!!} -- arSubK-imp
      {!!} -- envInK-mem
      {!!} -- envInK-neg
      {!!} -- envInK-top
      {!!} -- envInK-imp
      {!!} -- valV
      {!!} -- valW
      {!!} -- wKfact
      (λ x a hxa haK → kf .arityK a x hxa haK) -- transK from arityK (binder swap)
      {!!} -- subK₁-and
      {!!} -- subK₀-and
      {!!} -- subK₁-imp
      {!!} -- subK₀-imp
      {!!} -- someEnv
      {!!} -- subK-neg
      {!!} -- keyK-neg
      {!!} -- succK
      {!!} -- keyK-un
      {!!} -- subK-un
      {!!} -- consK-exist
      {!!} -- consK-forall
      {!!} -- succK-allin
      {!!} -- keyK-allin
      {!!} -- subK-allin
      {!!} -- consK-allin
