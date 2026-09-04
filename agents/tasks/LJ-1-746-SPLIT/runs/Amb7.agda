{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.746] runs/Amb7.  The 732 Amb7 rewritten so approx-part SPENDS
-- the generic vacuity hypothesis instead of running a fresh PT.rec at
-- the concrete instance (W2; the cure the 732 critic named,
-- review-of-LJ-1-732-1.md:163-180).  The truncation elimination lives
-- in the hypothesis, so this file types no numeral-bound motive and
-- runs no PT.rec at all: the 732 wall was shape-local, as LJ-1.745
-- measured for the implication leaf (Probe745.agda:64-77, rc 0 in
-- 7.27 s under this caliber).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-746-SPLIT.runs.Amb7 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Coding.Model {ℓ} using ( appAt )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Vec using ( Vec; _∷_ )
import Cubical.Data.Empty as Empty
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem
open import LJ-1-732.runs.Amb5 {ℓ} lem
open import LJ-1-732.runs.Amb7a {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the erased appAt leaf of the step row, verbatim from
-- runs/Amb7b.agda:32-39
AppC : Formula CS.S 18
AppC = appAt (suc (suc zero)) (suc zero) zero

countAppC : countFo AppC ≡ 0
countAppC = refl

App : Formula (⊥* {ℓ-suc ℓ}) 18
App = CntS.erase AppC countAppC

-- THE GENERIC VACUITY HYPOTHESIS, the 732 critic's type
-- (review-of-LJ-1-732-1.md:163-166) in the spelling LJ-1.745 measured
-- green (Probe745.agda:64-76): γ is written Vec S 15, and the prose
-- negation is its carrier, ⟨ env ⊨ₚ App ⟩ → Empty.⊥.  Named once so
-- the four consumers (Amb4, Amb2, Probe746, the meter witness) share
-- one spelling (W2).
StepKilledGen : Type (ℓ-suc ℓ)
StepKilledGen =
    (u v : S)
    → (γ : Vec S 15)
    → ⟨ u ∈ˢ n 12 ⟩
    → ⟨ v ∈ˢ n 12 ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ) P652.⊨ₚ App ⟩
    → Empty.⊥

-- THE APPROXIMATION HALF of the graph at the empty table: the domain
-- row from Amb5, and the step row handing its antecedent to the
-- hypothesis.  The body is the LJ-1.745 instance call: γ stays
-- symbolic in the type and lands at γ15 only inside Empty.rec's
-- erased argument, so no motive is normalized here.
approx-part : StepKilledGen → ApproxAt
approx-part gen = domB-part , (λ u u∈ v v∈ ant → Empty.rec (gen u v γ15 u∈ v∈ ant))
