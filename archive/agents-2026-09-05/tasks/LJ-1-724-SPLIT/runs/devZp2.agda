{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.724-SPLIT] PROBE.  The corrected-scope target `table-sat` at the
-- [LJ-1.698] Carved frame (Probe698.agda:107-123).  Lands nothing in src/.
--
--   OBLIGATION   table-sat at the SPLIT scope (omega <= gamma, x+2 < gamma).
--                NOT INHABITED, AND NOT INHABITABLE AT THIS SCOPE.  The
--                Step conjunct's DefAt membrane
--                (src/L/Coding/Powerset.lagda.md:437-443) demands its code,
--                its satisfaction graph, its index set and its table INSIDE
--                A = Lset gamma once relativized
--                (src/FOL/Manipulation/Relativize.lagda.md:55-56,142-148),
--                and the rank chain then forces rank z + 6 < gamma for every
--                z the Step's extAt clause reaches:  envOne z lies in the
--                graph (DefinesAt, Powerset.lagda.md:217-220), the graph's
--                record pair lies in the table
--                (src/L/Coding/Graph.lagda.md:140-147), the table lies in A.
--                A member of Lset x has rank below x at the top, so the
--                reading needs x+5 < gamma where the SPLIT scope gives
--                x+3 <= gamma.  At gamma = sucV (sucV (sucV x)) with x >=
--                omega all three hypotheses of the brief hold and the
--                reading is FALSE, so pr x (Lset x) is not in carved there.
--                review-of-table-sat.md carries the chain with file:line.
--   DELIVERED    dφ: the Delta-0 certificate, [LJ-1.724]'s leg, re-measured
--                here;  γ∈σ: the frame's own stage is past gamma, read off
--                the bounding certificate's first constant;  pair-in-Lσ:
--                pr x (Lset x) inside Lset sigma at the SPLIT scope -- the
--                leg 724's scope could not give, because 724 had no x+2
--                hypothesis and the pair's rank is x+2 at the top;  the
--                pair's fiber m/qm/xL inside the frame's stage -- the
--                environment the door is stated at.
--   MEASURED OUT the door (to-reading / from-reading, both the pair-stated
--                and the fiber-stated form) does NOT fit the wide caliber
--                together with its own frame.  Every assembly walls:
--                a second application of Carved alone
--                (runs/devI-r1..3.out, 2.03 GB), the fiber context alone
--                (runs/devG-r2..4.out, 1.81 GB), the merged one-application
--                file with the pair-stated door (runs/devW-r2..5.out,
--                1.99 GB) and with the fiber-stated door
--                (runs/devX-r2..5.out, 1.82 GB).  The door's own statement
--                names the satisfaction type of the relativized recording,
--                and that elaboration is the object that does not fit.
--                The reduction it carried is carried by the review instead,
--                through the in-tree imageOut/imageIn
--                (src/L/Axioms/Separation.lagda.md:219-229), which are
--                checked where they are defined.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-724-SPLIT.runs.devZp2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL; Lset-mono; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset-suc; ord∈Lset→∈; suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import LJ-1-698.Probe698 {ℓ} lem using ( recorded-at; module Carved )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

------------------------------------------------------------------------------
-- The bare frame application:  the floor this file's legs stand on.

module Bare (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where
  open Carved γ oγ hγ using ( σ; oσ; φᵣ; hφ; carved )

  Lset-self : (δ : V ℓ) → ⟨ Lset δ ∈ˢ Lset (sucV δ) ⟩
  Lset-self δ =
    subst (λ w → ⟨ Lset δ ∈ˢ w ⟩) (sym (Lset-suc δ))
      (𝒟ₒ-intro (Lset δ) (Lset δ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁)

  pair-in-Lγ : (x : V ℓ) (ox : IsOrd x)
             (hx2 : ⟨ sucV (sucV x) ∈ˢ γ ⟩)
           → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
  pair-in-Lγ x ox hx2 = ?

-- THE OBLIGATION IS ABSENT ON PURPOSE.
--
--   table-sat : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
--                 (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--               → ⟨ ω ∈ˢ γ ⟩
--               → ⟨ sucV (sucV x) ∈ˢ γ ⟩
--             → ⟨ pr x (Lset x) ∈ˢ Carved.carved γ oγ hγ ⟩
--
-- FALSE at the SPLIT scope:  at gamma = sucV (sucV (sucV x)), x >= omega,
-- all three hypotheses hold, and the reading is FALSE by the DefAt-membrane
-- rank chain (review-of-table-sat.md).  No postulate stands in for it and
-- no weaker form is inhabited under its name.  The door that would reduce
-- the obligation to the A-bounded reading is stated in runs/devX.agda and
-- runs/devW.agda with the runs that measured it out of caliber beside them.
