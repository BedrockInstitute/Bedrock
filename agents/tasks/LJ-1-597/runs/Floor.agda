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

module LJ-1-597.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
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
-- SECTION 1.  WHAT `step` CALLS, AS ONE EQUATION CHAIN, MEASURED.
--
--   `step α IH oα α∈suc infα` is ONE EQUATION
--   (src/L/StageCardinal.lagda.md:562):
--     limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)
--   and `limit-step` (:396-403) is `LimitStep.h` with
--   D := DefOf.defSet and inv := 𝒟ₒ-inv.  `h x` (:350-351) is
--   `leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x)`,
--   so the step's value at x is the ORDINAL-LEAST y with
--   `class-pred x y`, and `class-pred` (:319-323) is the truncated
--   existence of m and φ with
--       D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x   and   B.pair m (cnt m φ) ≡ y.
--   THE SECOND EQUATION IS THE VALUE EQUATION.  [LJ-1.594] measured
--   that it has FIVE ingredients and wrote it out by `refl`
--   (`class-pred-is`, Probe594.agda:283-300, imported below).  This
--   section spends that row and the two rows under it.
-- ===================================================================

-- 1.1  THE PAIRING IN THE VALUE EQUATION IS THE MODULE PARAMETER `sq`
--      APPLIED, AND NOTHING ELSE.  [LJ-1.594]'s row, imported:
--      `refl` at this site.  `sq` carries injectivity and nothing else
--      (src/L/StageCardinal.lagda.md:17-19): no formula, no Levy
--      grade, no stage.  [LJ-1.533]'s wall, measured three times
--      (agents/tasks/LJ-1-533/lj-1.533-report.md:42-43).
pair-is-sq :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (x y : ⟪ α ⟫)
  → SC.Bound.pair α oα infα (sq α α∈suc infα) x y ≡ fst (sq α α∈suc infα) (x , y)
pair-is-sq _ _ _ _ _ _ = refl

-- 1.2  THE COUNT IN THE VALUE EQUATION, TYPE ONLY.
--      `SC.LimitStep.cnt` (src/L/StageCardinal.lagda.md:288-289)
--      re-ascribed.  [LJ-1.594] measured BY `refl` that it is
--      `fst (Bound.formula-bound (ih m))` and nothing else
--      (agents/tasks/LJ-1-594/Probe594.agda:252-263, GREEN under
--      -M8g).  THAT ROW IS NOT RE-PROVED HERE: at this pane's cap
--      (-M2g) re-elaborating its two sides drained the machine
--      (runs/final-9.out, runs/final-10.out, SIGKILL, exit 137, no
--      RTS heap message), so this probe carries the call's TYPE and
--      takes the equation from the probe that typechecked it.
--      `cnt m φ` is `tuple-g`/`count-bound` packing
--      (src/L/StageCardinal.lagda.md:128-130, :196-206) of the
--      formula's code through `ih m`; `count-bound` itself packs
--      through `pair` (1.1) and through `g = ih m`.
cnt-type :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ)
    (inv : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
    (m : ⟪ α ⟫) → Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 → ⟪ α ⟫
cnt-type = SC.LimitStep.cnt

-- 1.3  THE VALUE EQUATION ITSELF.  [LJ-1.594] measured BY `refl`, at
--      the SAME module instance, that `class-pred x y` is the
--      truncated existence of m and φ with
--          D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x   and
--          fst (sq α α∈suc infα) (m , cnt m φ) ≡ y,
--      so the only occurrence of the value y is the second equation
--      (agents/tasks/LJ-1-594/Probe594.agda:283-300, GREEN under
--      -M8g; the same re-elaboration drain as 1.2 applies here).
--      FIVE ingredients, [LJ-1.594]'s upheld table: (i) D, (ii) the
--      ordinal order in `leastOf`, (iii) the pairing `sq`, (iv) the
--      branch `ih`, (v) the meta syntax `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`
--      the existential ranges over.  The predicate's TYPE, re-ascribed
--      here; its written-out equation, taken from the green probe.
class-pred-type :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ)
    (inv : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
    (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
class-pred-type = SC.LimitStep.class-pred

-- 1.4  EVERY VALUE OF THE STEP IS A VALUE OF THAT PAIRING.  THIS IS
--      [LJ-1.584]'s MEASURED THEOREM, GREEN IN ITS OWN PROBE
--      (agents/tasks/LJ-1-584/Probe584.agda:186-206), at the inductive
--      input the step itself supplies, `branch`
--      (src/L/StageCardinal.lagda.md:562).  IT IS CITED AND NOT
--      RE-APPLIED AS A ROW HERE: the row that applied it (attempt 1's
--      `step-values-are-sq-values`) elaborated under -M4g
--      (agents/tasks/LJ-1-597/runs/final-4.out, exit 42 at its hole,
--      111 s), and under this pane's -M2g on this loaded machine the
--      P584 import's instantiation was the drain the OS killed
--      (runs/final-9.out to runs/final-11.out, SIGKILL, exit 137, no
--      RTS heap message, system swap near full and load above 30).
--      The theorem, its proof line and its green runs are [LJ-1.584]'s
--      record.  At the STEP, not only at the whole injection, every
--      value of the graph's subject is an `sq`-packed value: the
--      value equation 1.3 already says so, since its only occurrence
--      of y is the `sq`-application side.


-- ===================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE, BOTH DIRECTIONS.  WRITTEN, NOT
--              INHABITED.
--
--   THE GRAPH THE BRIEF ASKS FOR.  The step's output at α is
--   `step-fn α ... : ⟪ Lset α ⟫ → ⟪ α ⟫`.  Its graph is a relation
--   between the stage's members and the index's members, read as ONE
--   formula in TWO free variables, value first and index second, in
--   the order the internalization chapter itself states
--   (src/L/Recursion.lagda.md:273-274: `graph : Formula S 2`), with
--   the two directions its own `Definition` fields demand
--   (`defines`, `only`, :275-278).  THIS TYPE IS THAT SHAPE at
--   `fn := step-fn` read on members of `dom := LsetS α oα`.
--
--   IT IS NOT INHABITED HERE, and the stop file names the two calls
--   in the value equation that no formula can express.  No weaker
--   term is offered under the obligation's own name.
-- ===================================================================

Graph : (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
      → (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
      → Type (ℓ-suc ℓ)
Graph α oα α∈suc infα IH =
  Σ[ ψ ∈ Formula S 2 ]
    ( ((x y : S) (m : ⟨ fst x ∈ fst δL ⟩)
       → fst y ≡ fst (val x m) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
    × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (m : ⟨ fst x ∈ fst δL ⟩)
       → fst y ≡ fst (val x m)) )
  where
  δL : S
  δL = LsetS α oα
  bO : S
  bO = P568.ordS α oα
  val : (x : S) → (m : ⟨ fst x ∈ fst δL ⟩) → S
  val x m = P561.up bO (step-fn α oα α∈suc infα IH (P549.ixOf δL x m))


-- end of floor slice
