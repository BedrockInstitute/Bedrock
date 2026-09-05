{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.514] PROBE.  Does the level graph name any constant at all?
-- It runs in agents/tasks/LJ-1-514/ and lands nothing in src/.
--
--   W3, FIRST      the constant census of LsetGraphAt.  MEASURED 664.
--   OBLIGATION     graphFo-at-SL, the level graph over the stage carrier.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-514.Probe514 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset; IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Axioms.Separation {ℓ} lem using ( Below′; liftFoTo; mkBoundedFo )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt; ApproxAt; StepAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Model {ℓ} using ( domAt; appAt; prAtL; tagAtL; closedAt )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefinesAt; envOneAt; isCodeAt )
open import L.Coding.CodeSet {ℓ} lem using ( keyArityAtL; hasWitnessAt )
open import L.Coding.Shape {ℓ} using ( shapedAt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- W3.  THE CENSUS, AND IT COMES FIRST.
--
-- satGraphAt is sealed (src/L/Coding/Graph.lagda.md:203), so the count is
-- stuck behind the seal until it is unfolded here.  The seal is that
-- chapter's, not this probe's: unfolding it is reading and not editing.
opaque
  unfolding satGraphAt

  census : {n : ℕ} (w b : Fin n) → ℕ
  census w b = countFo (LsetGraphAt w b)

  -- DELIBERATE PROBE, run and kept as a comment.  Agda reported the normal
  -- form of the left side in the mismatch: MEASURED 664, runs/w3-0.out:3-4.
  -- THE CENSUS IS NOT EMPTY, so the brief's cheap branch does not apply.
  -- census-is-zero : {n : ℕ} (w b : Fin n) → census w b ≡ 0
  -- census-is-zero w b = refl

  -- ATTRIBUTION.  One entry per naming site on the unfolding path, so the
  -- 664 is charged to the sites that spend it.  Every number below is
  -- machine-checked by the single refl at the end of this block.
  breakdown : {n : ℕ} (w b : Fin n) → Vec ℕ 16
  breakdown w b = countFo (LsetGraphAt w b)      -- Sequence:291,349
                ∷ countFo (ApproxAt w b)         -- Sequence:286
                ∷ countFo (StepAt w b w)         -- Sequence:119
                ∷ countFo (domAt w b)            -- Model:278
                ∷ countFo (appAt w b w)          -- Model:160
                ∷ countFo (prAtL w b w)          -- Model:122
                ∷ countFo (DefAt w b)            -- Powerset:442
                ∷ countFo (isCodeAt w b)         -- Powerset:297
                ∷ countFo (satGraphAt w b w)     -- Graph:204
                ∷ countFo (DefinesAt w b w)      -- Powerset:217
                ∷ countFo (keyArityAtL w 1)      -- CodeSet:135
                ∷ countFo (hasWitnessAt w b)     -- CodeSet:240
                ∷ countFo (envOneAt w b)         -- Powerset:128
                ∷ countFo (tagAtL w 0 b)         -- Model:586, THE ROOT SITE
                ∷ countFo (closedAt w)           -- Model:2191
                ∷ countFo (shapedAt w b)         -- Shape:189
                ∷ []

  expected : Vec ℕ 16
  expected = 664 ∷ 332 ∷ 332 ∷ 0 ∷ 0 ∷ 0 ∷ 166 ∷ 35 ∷ 44 ∷ 4
           ∷ 1 ∷ 34 ∷ 2 ∷ 1 ∷ 8 ∷ 26 ∷ []

  breakdown-is : {n : ℕ} (w b : Fin n) → breakdown w b ≡ expected
  breakdown-is w b = refl

-- THE TRANSPORT.
--
-- The census is not empty, so mapFo along a TOTAL map is the wrong
-- instrument, and the brief is right that no total CS.S → SL exists.  The
-- tree does not use mapFo for this.  It uses Relabel
-- (src/FOL/Manipulation/Bounding.lagda.md:146), which spends a
-- per-occurrence certificate, and mkBoundedFo BUILDS that certificate for
-- ANY formula together with the stage it needs
-- (src/L/Axioms/Separation.lagda.md:449).  So the partial map's domain is
-- the finite set of constants and not the carrier, exactly as the brief
-- demands.
--
-- Both carriers project into V ℓ and the projections agree on the nose,
-- because 𝒮ᵥ's carrier IS V ℓ (src/V/Hierarchy.lagda.md:79-82).  That is
-- why down-correct is refl.
module Transport (α : S) (ordα : IsOrd α) where

  module ASt = AtStage α ordα
  open ASt using ( SL )

  module RL = Relabel {K = CS.S} {K' = SL} {W = V ℓ}
                fst fst (Below′ α)
                (λ c h → fst c , h)
                (λ c h → refl)

  -- THE GENERAL FORM, at an ARBITRARY stage.  One named side condition,
  -- and it is a bound on the stage, not a fact about hierL.  [LJ-1.494]'s
  -- first blocker is untouched by it.
  module _ (inStage : {n : ℕ} (w b : Fin n)
                    → ⟨ fst (mkBoundedFo (LsetGraphAt w b)) ∈ α ⟩) where

    cert : {n : ℕ} (w b : Fin n) → BoundedFo (Below′ α) (LsetGraphAt w b)
    cert w b = liftFoTo (inStage w b) (LsetGraphAt w b)
                        (snd (snd (mkBoundedFo (LsetGraphAt w b))))

    graphFo-at-anyStage : {n : ℕ} (w b : Fin n) → Formula SL n
    graphFo-at-anyStage w b = RL.liftFo (LsetGraphAt w b) (cert w b)

-- THE SIDE CONDITION IS NOT A GAP.  It is discharged by CHOOSING the
-- stage, and mkBoundedFo already computed which one.  sucV puts that stage
-- inside the next one (src/V/Model.lagda.md:236,
-- src/L/Ordinal.lagda.md:96), so the transport needs NO hypothesis at all
-- at the stage the formula itself names.  Nothing here is normalised:
-- every step is an application.
module Stage {n : ℕ} (w b : Fin n) where

  bnd : Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) (LsetGraphAt w b))
  bnd = mkBoundedFo (LsetGraphAt w b)

  σ : V ℓ
  σ = fst bnd

  α : V ℓ
  α = sucV σ

  ordα : IsOrd α
  ordα = suc-ord (fst (snd bnd))

  module TR = Transport α ordα

  SL : Type (ℓ-suc ℓ)
  SL = TR.ASt.SL

  cert : BoundedFo (Below′ α) (LsetGraphAt w b)
  cert = liftFoTo (self∈sucV σ) (LsetGraphAt w b) (snd (snd bnd))

-- THE OBLIGATION.  UNCONDITIONAL: no module hypothesis, no postulate, no
-- reflection principle.  SL is the stage carrier of src/L/Hull.lagda.md:153,
-- at the stage this very formula names.
graphFo-at-SL : {n : ℕ} (w b : Fin n) → Formula (Stage.SL w b) n
graphFo-at-SL w b = Stage.TR.RL.liftFo w b (LsetGraphAt w b) (Stage.cert w b)
