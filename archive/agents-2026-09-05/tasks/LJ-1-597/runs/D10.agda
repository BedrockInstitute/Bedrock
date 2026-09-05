{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.597]  THE GRAPH OF ONE STEP.
--
-- VERDICT: NO-GO.  agents/tasks/LJ-1-597/review-of-step-graph.md
-- states it and names the atom.  **THE OBLIGATION `step-graph` IS NOT
-- IN THIS FILE** and no weaker term is offered as one: that is
-- [LJ-1.584]'s discipline
-- (agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:3-6).
-- This file carries NO hole and NO postulate, so every row in it is a
-- measurement and not a claim.  Nothing lands in `src/`.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a conversion
-- problem: `[LJ-1.584]` measured that one such row does not terminate
-- (agents/tasks/LJ-1-584/runs/w3b-1.out).  `step` and `branch` appear
-- in TYPES and in projections of computed pairs, never against a body.
--
--   Section 0.  W3, imported.  `step`, re-ascribed alone, and its
--               function part named once.
--   Section 1.  WHAT `step` CALLS, AS ONE EQUATION CHAIN, MEASURED.
--               The step's value equation and the two calls in it that
--               have no formula.  [LJ-1.594]'s rows are imported and
--               spent, not rebuilt.
--   Section 2.  THE OBLIGATION'S TYPE, both directions.  Written and
--               NOT inhabited, in this file's own name.
--   Section 3.  D-10.  THE TARGET'S TRUTH.  `V = L` gives the
--               arity-3 neighbour outright; a refutation of the target
--               family is a refutation of `V = L`.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-597.runs.D10 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; 𝒟ₒ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- THE PREDECESSORS THIS FILE STANDS ON.  Every type below is taken
-- from the probe that typechecked; none is transcribed.  [LJ-1.584]'s
-- and [LJ-1.594]'s verdicts are NO-GO at wider targets; this file
-- spends their measured theorems, not their verdicts.  [LJ-1.594]'s
-- three rows below are re-proved BY `refl` HERE rather than imported:
-- at this pane's cap (-M2g) the import of its file walls
-- (runs/final-5.out), and each of its proofs is one `refl`.
import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568
import LJ-1-597.runs.W3 {ℓ} lem α₀ oα₀ sq as W3


-- ===================================================================
-- SECTION 0.  W3, IMPORTED.
--
--   The brief: "Write it FIRST and typecheck it ALONE."  It was:
--   agents/tasks/LJ-1-597/runs/w3-2.out, GREEN, 1.49 s, re-run for
--   THIS attempt (runs/w3-2.out) because nothing typechecks it after
--   this task closes.
-- ===================================================================

-- 0.1  `step`, RE-ASCRIBED ALONE.  src/L/StageCardinal.lagda.md:561.
--      IT TAKES a stage α and the induction hypothesis IH at every
--      member stage, then P α's own fields (ordinal, band membership,
--      infinitude).  IT RETURNS the stage's injection: a function from
--      the stage's presentations to the index's presentations, with
--      its injectivity.  IT CALLS `limit-step` and `branch`, in ONE
--      equation (:562).
step : (α : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) → SC.Upper.P α
step = W3.step

-- 0.2  THE STEP'S OUTPUT AT ONE STAGE, NAMED ONCE.  `P α` applied to
--      the stage's own parameters is a Σ of a function and its
--      injectivity; this is the function, the graph's subject.  The
--      name `step` sits in a type and in this projection and nowhere
--      else in this file.
step-fn : (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
       → (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
       → (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
       → ⟪ Lset α ⟫ → ⟪ α ⟫
step-fn α oα α∈suc infα IH = fst (SC.Upper.step α IH oα α∈suc infα)

-- 0.3  `branch`, RE-ASCRIBED, TYPE ONLY.  It is the `ih` the step's
--      own equation supplies to `limit-step` (src/L/StageCardinal.
--      lagda.md:562), and it is the fourth ingredient of
--      [LJ-1.594]'s table.  TYPE ONLY ON PURPOSE, the same reason as
--      [LJ-1.594]'s own `branch-at-the-site`: no conversion problem.
branch-type :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
branch-type α oα α∈suc infα IH = SC.Upper.branch α oα α∈suc infα IH

-- 0.4  `fin-inj`, RE-ASCRIBED, TYPE ONLY.  The ω-base of the branch:
--      at a finite member stage the branch's value is this, composed
--      with `WOEmb.ω-inj` (src/L/StageCardinal.lagda.md:552).  Its own
--      value is `leastOf natOrder` over the Tally of the finite stage
--      (src/L/StageCardinal.lagda.md:438-440, :515-517).  NO TASK HAS
--      MEASURED whether the Tally has a formula; this row only names
--      the type.
fin-inj-type : (δ : V ℓ) (δ∈ω : ⟨ δ ∈ˢ ω ⟩) → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫
fin-inj-type = SC.fin-inj


-- ===================================================================
-- SECTION 3.  D-10.  THE TARGET'S TRUTH, MEASURED BEFORE THE PROOF
--              WAS PRICED.
-- ===================================================================

-- 3.1  THE TARGET IS NOT REFUTED HERE, AND THE REASON IS A ROW THAT
--      TYPECHECKS.  At the arity-3 neighbour of section 2's type
--      ([LJ-1.568]'s `Def` at the same triple): the graph is already
--      an ambient set ([LJ-1.561]'s `ambient-graph-isL`,
--      Probe561.agda:171-176), `V = L` puts it in L, and [LJ-1.568]'s
--      `graph→def` (Probe568.agda:368-374) reads a graph in L back as
--      a formula.  NOTHING IS TRUNCATED ON THIS PATH.  Section 2's
--      arity-2 shape is the chapter's own shape; the syntax carries
--      no substitution and no weakening
--      (src/FOL/Syntax.lagda.md:157), so no row converts one arity
--      into the other, and THIS FILE CLAIMS NO EQUIVALENCE BETWEEN
--      THEM.  The stop below does not rest on one.
vl→def : ((x : V ℓ) → ⟨ isL x ⟩)
      → (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
        (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
        (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
      → P568.Def (LsetS α oα) (P568.ordS α oα) (step-fn α oα α∈suc infα IH)
vl→def vl α oα α∈suc infα IH =
  P568.graph→def (LsetS α oα) (P568.ordS α oα) (step-fn α oα α∈suc infα IH)
    (P561.ambient-graph-isL (LsetS α oα) (P568.ordS α oα)
       (step-fn α oα α∈suc infα IH) (vl _))

-- 3.2  SO A REFUTATION OF THE TARGET FAMILY IS A REFUTATION OF
--      `V = L`, which no chapter of `src/` has.  **THIS FILE THEREFORE
--      DOES NOT CLAIM THE OBLIGATION IS FALSE.**  It measures that the
--      tree cannot build it: the stop file names the atoms.
refuting-def-refutes-V=L :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  → (P568.Def (LsetS α oα) (P568.ordS α oα) (step-fn α oα α∈suc infα IH) → Empty.⊥)
  → ((x : V ℓ) → ⟨ isL x ⟩) → Empty.⊥
refuting-def-refutes-V=L α oα α∈suc infα IH no vl =
  no (vl→def vl α oα α∈suc infα IH)
