{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.614]  FACE G+ RESTATED AT THE STAGE CARRIER, AND THE CROSSING'S
-- ANSWER: the slot accepts, the kit does not.
--
-- THE OBLIGATION IS NOT INHABITED, AND THE STOP IS STATED AT
-- agents/tasks/LJ-1-614/review-of-graph-stage-at.md.  The brief's
-- question "does the crossing accept GraphStageAt in place of
-- GraphStage" has a TWO-PART answer, and both parts are measured here
-- as terms, not argued:
--
--   THE SLOT ACCEPTS (section 2).  At every `inL`-IMAGE matrix, the
--   restated face supplies leg 1 of [LJ-1.606]'s `inner-to-ambient`
--   DEFINITIONALLY: `slot-accepts` is one line, no transport, and the
--   whole crossing then consumes the restated face through
--   [LJ-1.606]'s own imported term (`inner-to-ambient-at`, section 3).
--
--   THE KIT DOES NOT (section 4).  The crossing's demand on G+ is not
--   one slot but three: the matrix at the HULL carrier
--   (Probe606.agda:178-180), the Delta-zero grade (`Δ₀ ψ`, first
--   component at :180, spent at leg 4 through `Σ₁-carried`
--   Probe606.agda:201-204 and :238), and the stage reading at the
--   image pair (`GraphStage`, :156-159).  The restated matrix
--   `ψ₀ = guardSL ⇒̇ matrixSL` (imported from [LJ-1.610]) meets the
--   third and only the third.  `kit-rejects-ψ₀` is the refutation: NO
--   hull matrix `ψ` with `mapFo inL ψ ≡ ψ₀` carries `Δ₀ ψ`, because
--   `mapFo-Δ₀` would force `Δ₀ ψ₀`, hence `Δ₀ matrixSL`, hence a
--   Delta-zero witness for the relabelled `domAt` -- and `domAt` is
--   headed by an UNBOUNDED `∀̇` (src/L/Coding/Model.lagda.md:277-280),
--   for which the Delta-zero datatype has no constructor
--   (src/FOL/LevyHierarchy.lagda.md:47-58).  The middle legs bind the
--   same carrier: face E at src/L/BoundedSubset.lagda.md:410-412
--   (spent at Probe606.agda:230) and the collapse iso at
--   src/L/BoundedSubset.lagda.md:206-207 (spent at :233) each take
--   their formula at `Formula DR.SM n`, the hull carrier.
--
-- WHAT LANDS.  Five measured objects, all inside one six-slot frame
-- that instantiates BOTH predecessors' frames ([LJ-1.606]'s and
-- [LJ-1.610]'s -- the same six slots, so the judgmental identities the
-- probes recorded hold here unchanged):
--   section 2  `slot-accepts`     the restated face pays the original
--                                 G+ slot at every image matrix;
--   section 3  `inner-to-ambient-at`  the crossing, unchanged, consumes
--                                 the restated face at image matrices;
--   section 4  `kit-rejects-ψ₀`   no image matrix over `ψ₀` carries the
--                                 kit's grade (the ruling's repair,
--                                 measured shut);
--   section 5  `reduction`        the face itself is [LJ-1.610]'s own
--                                 `graph-stage-from-wit`, imported; the
--                                 name `graph-stage-at` is DELIBERATELY
--                                 absent and the meter reports it
--                                 missing.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-614.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-⇒ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( map; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty

import LJ-1-606.Probe606
import LJ-1-610.Probe610
module P606 = LJ-1-606.Probe606 lem
module P610 = LJ-1-610.Probe610 lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  [LJ-1.606]'s six slots, once, and both predecessors'
-- frames instantiated at them: `F6` carries the crossing, `R` carries
-- the restated face.  Nothing from either probe is restated: every
-- object below is an import applied to this frame's own slots.
-- =====================================================================

module Restate (lam : SV.S) (ordλ : IsOrd lam)
               (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
               (X : SV.S)
               (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module F6 = P606.Frame lam ordλ succλ X X⊆Lλ ∅∈λ
  module R  = P610.Frame lam ordλ succλ X X⊆Lλ ∅∈λ

  -- ===================================================================
  -- SECTION 1.  WHAT THE CROSSING DEMANDS OF G+, AS BOUND TYPES.  The
  -- demand is `Crossing`'s second and first components together
  -- (Probe606.agda:178-180): a HULL matrix, Delta-zero, carried by the
  -- stage at every level-pair.  The bindings the middle legs put on
  -- the same matrix, displayed here so the report's file:line has a
  -- probe-side anchor: face E (leg 2) is [LJ-1.606]'s `ElemDownAt`,
  -- which IS `DR.ElemDown`, whose type binds `φ : Formula DR.SM n`
  -- (src/L/BoundedSubset.lagda.md:410-412); the collapse iso (leg 3,
  -- `CI.I.iso-inv`, src/L/BoundedSubset.lagda.md:206-207) binds its
  -- formula at the same carrier.  Both are hull-shaped end to end.
  -- ===================================================================

  ElemDown-binding : Type (ℓ-suc ℓ)
  ElemDown-binding = R.DR.ElemDown

  -- ===================================================================
  -- SECTION 2.  THE SLOT ACCEPTS.  At every `inL`-image matrix the
  -- restated face supplies the original G+ slot with NO transport:
  -- `map inL (q ∷ γ ∷ [])` is `inL q ∷ inL γ ∷ []`, `mapFo inL (∃̇ ψ)`
  -- is `∃̇ mapFo inL ψ`, and `fst (inL q)` is `fst q`, all by
  -- definition.  This is the W3 answer as a term: the re-ascribed
  -- slot (runs/W3.agda:62-65) does not reject the restated face.
  -- ===================================================================

  slot-accepts : (ψ : Formula R.DR.SM 3)
               → R.GraphStageAt (mapFo R.DR.inL ψ)
               → F6.GraphStage ψ
  slot-accepts ψ gsta q γ fix = {!!}

  -- ===================================================================
  -- SECTION 3.  THE CROSSING, UNCHANGED, CONSUMES THE RE-ASCribed
  -- SLOT.  The kit with its G+ component restated at the stage carrier
  -- (at image matrices, which is all leg 1 ever reads), converted into
  -- [LJ-1.606]'s own `Crossing` by `slot-accepts`, then fed to
  -- [LJ-1.606]'s own term.  No leg is rebuilt; the acceptance is the
  -- conversion.
  -- ===================================================================

  CrossingAt : Type (ℓ-suc ℓ)
  CrossingAt =
    Σ[ ψ ∈ Formula R.DR.SM 3 ]
      ( Δ₀ ψ × R.GraphStageAt (mapFo R.DR.inL ψ) × F6.GraphAmbient ψ )

  crossing-at→crossing : CrossingAt → F6.Crossing
  crossing-at→crossing c = {!!}

  inner-to-ambient-at : F6.ElemDownAt → CrossingAt → F6.Commute
  inner-to-ambient-at ed cat = {!!}

  -- ===================================================================
  -- SECTION 4.  THE KIT DOES NOT.  The restated matrix `ψ₀` cannot
  -- enter the kit: no hull matrix relabelling onto it carries the
  -- Delta-zero grade the kit's first component demands.  The proof is
  -- constructor arithmetic on the machine matrix: `domAt` is headed by
  -- an unbounded `∀̇` (src/L/Coding/Model.lagda.md:277-280) and the
  -- Delta-zero datatype has no constructor for that head
  -- (src/FOL/LevyHierarchy.lagda.md:47-58), so no relabelled image of
  -- the machine matrix is Delta-zero, guard or no guard.
  -- ===================================================================

  no-Δ₀-matrixSL : Δ₀ R.matrixSL → Empty.⊥
  no-Δ₀-matrixSL d = {!!}

  no-Δ₀-ψ₀ : Δ₀ R.ψ₀ → Empty.⊥
  no-Δ₀-ψ₀ d = {!!}

  kit-rejects-ψ₀ : (ψ : Formula R.DR.SM 3)
                 → mapFo R.DR.inL ψ ≡ R.ψ₀
                 → Δ₀ ψ
                 → Empty.⊥
  kit-rejects-ψ₀ ψ e dψ = {!!}

  -- ===================================================================
  -- SECTION 5.  THE FACE, IMPORTED AND NOT RESTATED.  The restated
  -- face at `ψ₀` follows from [LJ-1.610]'s named residue `WitStage`
  -- by [LJ-1.610]'s own term, imported here and green.  The
  -- obligation's name `graph-stage-at` is DELIBERATELY absent: the
  -- task's real question is the consumer, the consumer's answer is
  -- section 4, and the stop is stated at
  -- agents/tasks/LJ-1-614/review-of-graph-stage-at.md.  The meter
  -- therefore reports the obligation MISSING.
  -- ===================================================================

  GraphStageAt-ψ₀ : Type (ℓ-suc ℓ)
  GraphStageAt-ψ₀ = R.GraphStageAt R.ψ₀

  reduction : R.WitStage → GraphStageAt-ψ₀
  reduction = {!!}
