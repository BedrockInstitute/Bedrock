{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.691] PROBE.  The three site facts that [LJ-1.681]'s
-- `bnd-vs-unbnd` takes as hypotheses: the witness in K (`fK`), the
-- domain transfer (`domOut`), and the leaf rows (the four step rows).
-- It runs in agents/tasks/LJ-1-691/ and lands nothing in src/.
--
--   NOT DELIVERED  `site-facts`, the briefed obligation, IS NOT
--                  CONSTRUCTIBLE HERE AND CANNOT BE: the first site
--                  fact `fK` is false at the allowed environment
--                  where every slot holds the coded empty set
--                  (`fK-void`, section 2), and the `Lset-defines`
--                  context saves it not at all.  The brief's own stop
--                  condition is met and this file is the evidence.
--                  review-of-site-facts.md states the NO-GO.
--   DELIVERED      the three site facts, verbatim the hypotheses of
--                  `bnd-vs-unbnd` (section 1), and the refutation
--                  (section 2).
--
-- THE FINDING IN ONE SENTENCE.  `fK` says that EVERY element of the
-- class carrier lies in the `K` slot of the environment; at the
-- environment `∅ʟ ∷ ∅ʟ ∷ []` that slot is the coded empty set, so
-- `fK` at `∅ʟ` asserts `∅ ∈ ∅`, which the landed `∅-empty`
-- discharges to a contradiction.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-691.Probe691 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import FOL.Syntax using ( Formula; ∃̇_ )
  import FOL.Absoluteness
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
  open import L.Coding.Model {ℓ} using ( domAt )
  open import L.Coding.Sequence {ℓ} lem using ( StepBody )
  open import L.Condensation {ℓ} lem using
    ( module StepB; module ApproxB; domB )
  open import L.Axioms.Basic using ( ∅ʟ )
  import Cubical.Data.Empty as Empty
  open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
  open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ; _∈ₛ_ )
  open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ∅-empty )
  open import Cubical.Data.Vec using ( lookup; _∷_; [] )
  open import Cubical.Data.Nat using ( _+_ )

  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  open hPropStructure 𝒮ʟ

  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

  -- -----------------------------------------------------------------
  -- SECTION 1.  THE THREE SITE FACTS, VERBATIM.
  --
  -- The six lines below are the first six arguments of
  -- `bnd-vs-unbnd` (agents/tasks/LJ-1-681/Probe681.agda:64-103):
  -- the witness in K, the domain transfer, and the four leaf rows.
  -- Their types are copied, not paraphrased.
  -- -----------------------------------------------------------------

  module Facts {n : ℕ} (w b K : Fin n) (γ : S ^ n)
    (ψs : Formula S (8 + n)) (ψa : Formula S (10 + n)) where

    module SB  = StepB {1 + n} ψs (suc w) (suc b) zero (suc K)
    module AB  = ApproxB {1 + n} ψa zero (suc b) (suc K)
    module SBA = AB.S

    fK : Type (ℓ-suc ℓ)
    fK = (f₀ : S) → ⟨ fst f₀ ∈ fst (lookup K γ) ⟩

    domOut : Type (ℓ-suc ℓ)
    domOut = (f₀ : S)
          → ⟨ (f₀ ∷ γ) ⊨ domAt zero (suc b) ⟩
          → ⟨ (f₀ ∷ γ) ⊨ domB zero (suc b) (suc K) ⟩

    stepBwd : Type (ℓ-suc ℓ)
    stepBwd = (f₀ z : S)
          → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩
          → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩

    stepFwd : Type (ℓ-suc ℓ)
    stepFwd = (f₀ z : S)
          → ⟨ (z ∷ f₀ ∷ γ) ⊨ SB.witB ⟩
          → ⟨ (z ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc b) zero))) ⟩

    apxStepBwd : Type (ℓ-suc ℓ)
    apxStepBwd = (z' z c f₀ : S)
          → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩
          → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩

    apxStepFwd : Type (ℓ-suc ℓ)
    apxStepFwd = (z' z c f₀ : S)
          → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ SBA.witB ⟩
          → ⟨ (z' ∷ z ∷ c ∷ f₀ ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody (suc zero) (suc (suc zero))))) ⟩

    SiteFacts : Type (ℓ-suc ℓ)
    SiteFacts = fK × (domOut × (stepBwd × (stepFwd × (apxStepBwd × apxStepFwd))))

  -- -----------------------------------------------------------------
  -- SECTION 2.  THE REFUTATION.  Put the coded empty set in every
  -- slot of the environment.  The K slot is then the coded empty
  -- set, and `fK` at `∅ʟ` asserts `∅ ∈ ∅`.  The landed `∅-empty`
  -- discharges that to a contradiction.  The two `Lset-defines`
  -- hypotheses of the composition context are carried and touch
  -- nothing here: they constrain the w and b slots, not K.
  -- -----------------------------------------------------------------

  fK-void : (w b K : Fin 2)
    → (ψs : Formula S (8 + 2)) → (ψa : Formula S (10 + 2))
    → IsOrd (fst (lookup b (∅ʟ ∷ ∅ʟ ∷ [])))
    → fst (lookup w (∅ʟ ∷ ∅ʟ ∷ [])) ≡ Lset (fst (lookup b (∅ʟ ∷ ∅ʟ ∷ [])))
    → Facts.SiteFacts {2} w b K (∅ʟ ∷ ∅ʟ ∷ []) ψs ψa
    → Empty.⊥
  fK-void w b zero ψs ψa ob q s =
    Empty.rec (∅-empty ∅ h0)
    where
      h0 : ⟨ ∅ ∈ₛ ∅ ⟩
      h0 = ∈∈ₛ {a = ∅} {b = ∅} .fst (fst s ∅ʟ)

  fK-void w b (suc zero) ψs ψa ob q s =
    Empty.rec (∅-empty ∅ h0)
    where
      h0 : ⟨ ∅ ∈ₛ ∅ ⟩
      h0 = ∈∈ₛ {a = ∅} {b = ∅} .fst (fst s ∅ʟ)
