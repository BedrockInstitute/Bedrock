{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.688] PROBE.  HierInK at one environment, as [LJ-1.684] names
-- the CORRECTED membership.  Lands nothing in src/.
--
--   THE OBLIGATION  hier-in-K.  NOT INHABITED.  W3 measured that
--                   DOWN at one environment CONSUMES the membership
--                   and does not produce it.  review-of-hier-in-K.md
--                   states the stop.
--   NOT INHABITED   ApproxInK (532 FALSE, Probe532.agda:206-209).
--                   HierInK (Probe532.agda:274-277) remains a type.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-688.Probe688 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_; ∃̇∈; _∧̇_; var )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt; ApproxAt; StepAt )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Condensation {ℓ} lem using
  ( module GraphB; module ApproxB; module StepB )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  THE TYPE [LJ-1.532] DELIVERED AND DID NOT INHABIT.
--
-- Verbatim from Probe532.agda:84-87 and :274-277.  The report is
-- NO-GO at ApproxInK, not at this type.  This file does not inhabit
-- ApproxInK.
-- =====================================================================

IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

HierInK : Type (ℓ-suc ℓ)
HierInK = (α : V ℓ) → IsLimit α
        → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
        → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

-- =====================================================================
-- SECTION 2.  THE SAME MEMBERSHIP AT ONE ENVIRONMENT.
--
-- [LJ-1.684] (lj-1.684-report.md:36-38, Probe684.agda:67-72): a BARE
-- ∀K form is false if K may be empty.  The hypothesized bridge is at
-- ONE environment, K a slot of GraphB.  The packaging below is that
-- slot, with K ≡ Lset α.  It does not quantify over every K.
--
-- P-l.  The type names Lset α, which is opaque
-- (src/L/Constructible.lagda.md:221-223).  It does not name a
-- transparent presentation of the stage.
-- =====================================================================

module Pin {m : ℕ}
  (ψs : Formula S (suc (suc (suc (5 + m)))))
  (ψa : Formula S (suc (suc (suc (7 + m)))))
  (w b K : Fin m) (γ : S ^ m) where

  module G = GraphB {m} ψs ψa w b K

  -- The corrected membership at THIS environment.  K is a slot.
  -- Transport along qK is the only difference from HierInK.
  HierInKAt : (α : V ℓ) → IsLimit α
            → fst (lookup K γ) ≡ Lset α
            → (oβ : IsOrd (fst (lookup b γ)))
            → ⟨ fst (lookup b γ) ∈ α ⟩
            → Type (ℓ-suc ℓ)
  HierInKAt α lim qK oβ b∈α =
    ⟨ fst (hierL (fst (lookup b γ)) (lookup b γ .snd) oβ)
        ∈ fst (lookup K γ) ⟩

  -- HierInK feeds the one-environment form.  The one-environment form
  -- does not feed HierInK.
  from-HierInK :
      HierInK
    → (α : V ℓ) (lim : IsLimit α)
    → (qK : fst (lookup K γ) ≡ Lset α)
    → (oβ : IsOrd (fst (lookup b γ)))
    → (b∈α : ⟨ fst (lookup b γ) ∈ α ⟩)
    → HierInKAt α lim qK oβ b∈α
  from-HierInK H α lim qK oβ b∈α =
    subst (λ u → ⟨ fst (hierL (fst (lookup b γ)) (lookup b γ .snd) oβ) ∈ u ⟩)
      (sym qK)
      (H α lim (fst (lookup b γ)) (lookup b γ .snd) oβ b∈α)

  -- =====================================================================
  -- SECTION 3.  THE GENERIC QUANTIFIER KIT, DOWN HALF.
  --
  -- Restated from [LJ-1.162] (ProbeLJ1162A.agda:69-73).  A bounded
  -- existential is reached from an unbounded one exactly when the
  -- witness is shown to lie in the bound.  That membership is the
  -- whole of DOWN's extra premise.
  -- =====================================================================

  ∃-down : (φB φ : Formula S (suc m))
         → ((x : S) → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩)
         → ((x : S) → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ (x ∷ γ) ⊨ φB ⟩)
         → ⟨ γ ⊨ ∃̇ φ ⟩ → ⟨ γ ⊨ ∃̇∈ (var K) φB ⟩
  ∃-down φB φ k f = PT.map (λ { (x , h) → x , (k x h , f x h) })

  -- =====================================================================
  -- SECTION 4.  DOWN AT THIS ENVIRONMENT.
  --
  -- Reverse of Graph.up (ProbeLJ1162A.agda:218-222).  UP is not rebuilt.
  -- The inner frames approx-down and step-down are hypotheses, as
  -- [LJ-1.162] took approx-up and step-up.  powK (ProbeLJ1162A.agda:
  -- 140-141) is a step-frame site fact and is not a stage membership
  -- for the approximation table.
  --
  -- witK is the membership of the graph witness in K.  At an arbitrary
  -- witness that is ApproxInK, which is FALSE.  At the canonical
  -- witness it is HierInKAt.
  -- =====================================================================

  Unb : Formula S (suc m)
  Unb = ApproxAt zero (suc b) ∧̇ StepAt (suc w) (suc b) zero

  Bnd : Formula S (suc m)
  Bnd = ApproxB.approxBndAt {1 + m} ψa zero (suc b) (suc K)
      ∧̇ StepB.stepBndAt {1 + m} ψs (suc w) (suc b) zero (suc K)

  Down : Type (ℓ-suc ℓ)
  Down =
      ((h : S) → ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
               → ⟨ (h ∷ γ) ⊨ ApproxB.approxBndAt {1 + m} ψa zero (suc b) (suc K) ⟩)
    → ((h : S) → ⟨ (h ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩
               → ⟨ (h ∷ γ) ⊨ StepB.stepBndAt {1 + m} ψs (suc w) (suc b) zero (suc K) ⟩)
    → ((h : S) → ⟨ (h ∷ γ) ⊨ Unb ⟩ → ⟨ fst h ∈ fst (lookup K γ) ⟩)
    → ⟨ γ ⊨ LsetGraphAt w b ⟩
    → ⟨ γ ⊨ G.graphBndAt ⟩

  -- GO as a composition.  The membership premise is not discharged.
  down : Down
  down approx-down step-down witK =
    ∃-down Bnd Unb witK
      (λ h hh → approx-down h (hh .fst) , step-down h (hh .snd))

-- =====================================================================
-- SECTION 5.  W3, LIFTED.  DOWN at one environment is the composition
-- above.  It reaches graphBndAt from LsetGraphAt if and only if the
-- witness lies in K.  That membership is HierInKAt after
-- canonicalisation, and HierInKAt is HierInK transported along qK.
-- DOWN does not construct HierInK.
-- =====================================================================

down = Pin.down
from-HierInK = Pin.from-HierInK
Down = Pin.Down
HierInKAt = Pin.HierInKAt
