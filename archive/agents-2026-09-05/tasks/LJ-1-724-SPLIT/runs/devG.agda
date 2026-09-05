{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.724-SPLIT] PROBE.  The corrected-scope target `table-sat` at the
-- [LJ-1.698] Carved frame (Probe698.agda:107-123).  Lands nothing in src/.
--
--   OBLIGATION   table-sat at the SPLIT scope (omega <= gamma, x+2 < gamma).
--                NOT INHABITED, AND NOT INHABITABLE AT THIS SCOPE.  The
--                Step conjunct's DefAt membrane
--                (src/L/Coding/Powerset.lagda.md:437-442) demands its code,
--                its satisfaction graph, its index set and its table INSIDE
--                A = Lset gamma once relativized
--                (src/FOL/Manipulation/Relativize.lagda.md:56-57,66-67), and
--                the rank chain then forces rank z + 6 < gamma for every
--                z the Step's extAt clause reaches:  envOne z lies in the
--                graph (DefinesAt, Powerset.lagda.md:217-221), the graph's
--                record pair lies in the table
--                (src/L/Coding/Graph.lagda.md:154-164), the table lies in A.
--                A member of Lset x has rank x-1 at the top, so the reading
--                needs x+5 < gamma where the SPLIT scope gives x+3 <= gamma.
--                At gamma = sucV (sucV (sucV x)) with x >= omega all three
--                hypotheses of the brief hold and the reading is FALSE, so
--                pr x (Lset x) is not in carved there.
--                review-of-table-sat.md carries the chain with file:line.
--   DELIVERED    dφ: the Delta-0 certificate, [LJ-1.724]'s leg, re-measured
--                here;  gamma-in-sigma: the frame's own stage is past gamma,
--                read off the bounding certificate's first constant;
--                pair-in-sigma: pr x (Lset x) inside Lset sigma at the SPLIT
--                scope -- the leg 724's scope could not give, because 724
--                had no x+2 hypothesis and the pair's rank is x+2 at the top;
--                to-reading / from-reading: the door at the pair's own
--                fiber, both directions.  Together they reduce the
--                obligation EXACTLY to the A-bounded reading of the
--                recording at the pair's environment.
--   ABSENT       table-sat:  false at the SPLIT scope.  No postulate stands
--                in for it.  The scope the chain demands is
--                omega <= gamma and x+6 <= gamma (or a frame re-bounded at
--                a limit, where src/L/Coding/Bound.lagda.md's BoundOver
--                closure engine applies).
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-724-SPLIT.runs.devG {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL; Lset-mono; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset-suc; ord∈Lset→∈; suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage; module AbsL )
open import LJ-1-698.Probe698 {ℓ} lem using ( recorded-at; module Carved )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
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
-- The frame, the certificate, and the scope arithmetic.

module Frame (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where

  open Carved γ oγ hγ using ( σ; oσ; φᵣ; hφ; carved )

  dφ : Δ₀ φᵣ
  dφ = recorded-at γ oγ hγ

  -- The stage the frame is bounded at is past gamma itself:  the recording's
  -- outer constant is (gamma, hgamma), and its bounding certificate says that
  -- constant lies in Lset sigma;  an ordinal of a stage is a member of the
  -- stage (src/L/Ordinal/Stages.lagda.md:168-171).
  γ∈σ : ⟨ γ ∈ˢ σ ⟩
  γ∈σ = ord∈Lset→∈ σ oσ γ oγ (hφ .fst)

  -- A stage is its own definable subset, hence sits in the next stage
  -- (src/L/Axioms/Basic.lagda.md:153-159, src/L/Definability.lagda.md:178).
  Lset-self : (δ : V ℓ) → ⟨ Lset δ ∈ˢ Lset (sucV δ) ⟩
  Lset-self δ =
    subst (λ w → ⟨ Lset δ ∈ˢ w ⟩) (sym (Lset-suc δ))
      (𝒟ₒ-intro (Lset δ) (Lset δ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁)

  -- The pair's rank is x+2 at the top, so the SPLIT scope (x+2 in gamma)
  -- is exactly what places pr x (Lset x) in Lset gamma.  This is the leg
  -- 724's scope could not give.
  pair-in-Lγ : (x : V ℓ) (ox : IsOrd x)
             (hx2 : ⟨ sucV (sucV x) ∈ˢ γ ⟩)
           → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
  pair-in-Lγ x ox hx2 =
    Sum.rec (λ x3∈γ → Lset-mono x3∈γ pair∈Lx3)
            (λ eq → subst (λ w → ⟨ pr x (Lset x) ∈ˢ Lset w ⟩) (sym eq) pair∈Lx3)
            (suc∈or≡ (sucV (sucV x)) γ (suc-ord (suc-ord ox)) oγ hx2)
    where
    pair∈Lx3 : ⟨ pr x (Lset x) ∈ˢ Lset (sucV (sucV (sucV x))) ⟩
    pair∈Lx3 = pr∈Lset-suc (sucV x) x (Lset x)
                 (ord∈Lset-suc x ox) (Lset-self x)

  pair-in-Lσ : (x : V ℓ) (ox : IsOrd x)
             (hx2 : ⟨ sucV (sucV x) ∈ˢ γ ⟩)
           → ⟨ pr x (Lset x) ∈ˢ Lset σ ⟩
  pair-in-Lσ x ox hx2 = Lset-mono γ∈σ (pair-in-Lγ x ox hx2)

------------------------------------------------------------------------------
-- The door at the pair's own fiber.  The obligation reduces to the
-- A-bounded reading of the recording at the pair's environment;  the
-- reading is what the SPLIT scope fails to secure (see the header).

module AtPair (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
              (x : V ℓ) (ox : IsOrd x)
              (hω : ⟨ ω ∈ˢ γ ⟩) (hx2 : ⟨ sucV (sucV x) ∈ˢ γ ⟩) where

  open Carved γ oγ hγ using ( σ; oσ; φᵣ; hφ; carved )

  dφ : Δ₀ φᵣ
  dφ = recorded-at γ oγ hγ

  pair∈Lσ : ⟨ pr x (Lset x) ∈ˢ Lset σ ⟩
  pair∈Lσ = Frame.pair-in-Lσ γ oγ hγ x ox hx2

  -- The pair as a member of the frame's stage, and its fiber.
  m : ⟪ Lset σ ⟫
  m = ∈-asFiber {a = pr x (Lset x)} {b = Lset σ} pair∈Lσ .fst

  qm : ⟪ Lset σ ⟫↪ m ≡ pr x (Lset x)
  qm = ∈-asFiber {a = pr x (Lset x)} {b = Lset σ} pair∈Lσ .snd

  xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
  xL = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
    (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

  -- The pair carrying its own constructibility:  the environment the
  -- reading is stated at.
  pairS : CS.S
  pairS = pr x (Lset x) , Lset→isL γ oγ (pr x (Lset x))
    (Frame.pair-in-Lγ γ oγ hγ x ox hx2)

  u : CS.S
  u = ⟪ Lset σ ⟫↪ m , xL

  qenv : u ≡ pairS
  qenv = Σ≡Prop (λ z → snd (isL z)) qm

-- THE OBLIGATION IS ABSENT ON PURPOSE.
--
--   table-sat : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
--                 (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--               → ⟨ ω ∈ˢ γ ⟩
--               → ⟨ sucV (sucV x) ∈ˢ γ ⟩
--             → ⟨ pr x (Lset x) ∈ˢ Carved.carved γ oγ hγ ⟩
--
-- FALSE at the SPLIT scope:  at gamma = sucV (sucV (sucV x)), x >= omega,
-- all three hypotheses hold, and the reading from-reading reduces the goal
-- to is FALSE by the DefAt-membrane rank chain (review-of-table-sat.md).
-- No postulate stands in for it and no weaker form is inhabited under
-- its name.
