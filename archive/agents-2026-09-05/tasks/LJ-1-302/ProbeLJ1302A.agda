{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.302] probe, file 1 of the answer.  THE COMPOSITE'S TYPE.
--
-- THE QUESTION: what would a composite over the thirty `Agree` modules
-- have to state to give `q'`?  THE ANSWER THIS FILE MEASURES: `q'`'s own
-- type.  The composite over the thirty IS the ambient bridge; it is not
-- a lemma beside it.  Its type is written below and typechecks against
-- delivered machinery: `φ₀` from `[LJ-1.241]`, the sequence graph from
-- `[LJ-1.238]`'s generic port applied at the ambient class by
-- `[LJ-1.297]`'s probe D.
--
-- THE FEEDING: `Fed` passes a hypothetical composite term into
-- `[LJ-1.244]`'s `AmbientStep` at its `q'` slot, with the six readings
-- probe D supplied.  `amb` comes out.  So a term of this type is the
-- one missing input to the machine that makes `amb`.
--
-- WHAT THE THIRTY GIVE IT: the leaf stem (`extAt→extAtB`/`extAtB→extAt`
-- at `src/L/Condensation.lagda.md:2511-2529`, fed by `LeafAgree`'s two
-- directions at `:7231-7241`).  WHAT THEY DO NOT: the three stems
-- above the leaf (`StepAgree`, `ApproxAgree`, `GraphAgree`), which do
-- not exist anywhere in the tree.  See the report, section 0.
--
-- The Def-step trio stays a hypothesis, as in probe D: the statement
-- holds for every Def-step coding.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )

module LJ-1-302.ProbeLJ1302A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( 𝒟ₒ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.Data.Vec using ( Vec; lookup )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-244.ProbeLJ1244A {ℓ} lem as P1244A
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297D {ℓ} lem as D

module A = P184.Ambient
module P1241 = P1297A.P1241
open P1297A.AbsL using ( _⊨ᵐ_ )

-- =====================================================================
-- THE COMPOSITE'S TYPE.  This is the deliverable: it typechecks, so the
-- composite's type IS writable at the carrier and reading `q'` lives
-- at, with the two sides named by delivered machinery.
-- =====================================================================
module CompositeTy
  (DefAt : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (DefAt-in : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ᵐ DefAt u w ⟩)
  (DefAt-out : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
             → D.GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ᵐ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X)) where

  module S = D.Supply DefAt DefAt-in DefAt-out

  Composite : Type (ℓ-suc ℓ)
  Composite = (γ : Vec A.R.SC 2)
            → ⟨ A.ambient γ (embed P1241.φ₀) ⟩
            → ⟨ A.ambient γ (S.Graph* {2} zero (suc zero)) ⟩

  -- ===================================================================
  -- THE FEEDING.  A composite term discharges `AmbientStep`'s `q'` slot;
  -- `amb` is then a term, not a target.
  -- ===================================================================
  module Fed (comp : Composite) where

    module AS = P1244A.AmbientStep S.Step* S.Approx* S.Graph*
                  S.step-out S.step-back S.approx-dom S.approx-value
                  S.approx-step S.graph-out P1241.φ₀ comp

    -- `amb`, with the composite in the `q'` slot.  The type is
    -- `AmbientStep`'s own (`amb : (P : S) (Ptr : isTrans P) →
    -- AmbientCross.AmbientRead P Ptr φ₀`, `ProbeLJ1244A.agda:120-121`);
    -- it is left to inference so the module's statement is the
    -- authority, not a restatement.
    amb-from-composite = AS.amb
