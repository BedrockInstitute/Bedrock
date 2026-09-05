{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.600]  keyS AT THIS CARRIER, THE FIRST PIECE OF THE ORDERED ROUTE.
--
-- VERDICT: GO.  The obligation `key-at-stage` IS in this file, at 1.1.
-- It is `keyS` from the LIVE chapter src/L/Coding/CodeSet.lagda.md
-- instantiated at `A := LsetS δ oδ` (src/L/Axioms/Basic.lagda.md:160-161),
-- which is ingredient (v) of the `class-pred` formula at this carrier:
-- the coded copy of the meta syntax the existential ranges over.  This
-- file carries NO hole and NO postulate, so every row in it is a
-- measurement and not a claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-600/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE under a two-minute cap (runs/w3-1.out to w3-3.out,
-- GREEN, 1.17 to 1.19 s; one negative control at runs/w3-neg-1.out,
-- exit 42 at the planted error).  IT IS IMPORTED below, not restated.
-- The FLOOR was measured with holes in this file's full import frame
-- (runs/Floor.agda, runs/floor-1.out: exit 42 at the two holes and
-- nowhere else, 1.17 s, cap 300 s never approached).
--
--   Section 0.  D-10, BEFORE ANY AGDA, AND IT IS THE STAGE.  AllCodes
--               at this carrier HAS a named stage: the earliest one,
--               by L.Stage's three projections.  The [LJ-1.86] wall
--               was never "no stage exists"; it was "the frame fixes
--               lam", and no consumer of (v) on this route fixes one.
--   Section 1.  W3, IMPORTED, and the obligation itself: `keyS` at
--               `A := LsetS δ oδ`, re-bound in this file's own name.
--   Section 2.  THE COLLECTION ROWS that make it ingredient (v): the
--               arity the site uses, every meta formula at this
--               carrier has a key in AllCodes, and every member of
--               AllCodes is a key.  NOTHING HERE ATTEMPTS (i), (ii),
--               (iii) OR (iv).
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a conversion
-- problem ([LJ-1.584]'s measurement, agents/tasks/LJ-1-584/runs/
-- w3b-1.out); this file does not import L.StageCardinal at all.  The
-- site is cited from [LJ-1.594]'s green probe, which wrote
-- `class-pred` out by refl (agents/tasks/LJ-1-594/Probe594.agda:283-300).
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-600.Probe600 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; key∈AllCodes; AllCodes-out )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-600.runs.W3 {ℓ} lem as W3


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY AGDA, AND IT IS THE STAGE.
--
--   The brief orders the stage named before anything is built, because
--   [LJ-1.86] measured that "the proof cannot choose" the stage holding
--   AllCodes (archive/dev/LJ-dispatch-index.md:160).  [LJ-1.86]'s own
--   split of that measurement is the one that survives here
--   (agents/tasks/archive/LJ-1-86/lj-1.86-report.md:7-19):
--
--   - HALF 1, MEASURED TRUE: a stage exists and IS nameable, by the
--     earliest-stage function.  `AllCodes A` is an `S`, a constructible
--     set whose `.snd` is the certificate, so `stage` applies.  Row 0.1
--     re-measures that half AT THIS CARRIER, and it is green.
--   - HALF 2, MEASURED FALSE, and it does not bind this route: what
--     could not be chosen was a stage ADMISSIBLE for `lam` fixed
--     upstream as a module parameter of the condensation frames.  No
--     consumer of ingredient (v) on the class-pred route fixes a `lam`:
--   - where the stage DOES enter AllCodes's own construction, it is
--     chosen and sealed already: `smallDom` returns
--     `LsetS β oβ` for the bounding ordinal β of the family's earliest
--     stages (src/L/Recursion.lagda.md:133-143), and separation cuts
--     AllCodes out of that stage with `isCodeAny`
--     (src/L/Coding/CodeSet.lagda.md:304-310).  Nothing in this file
--     re-chooses it; `AllCodes` is opaque, so it stays an atom.
-- ===================================================================

-- 0.1  THE STAGE, NAMED.  For every carrier of this shape, AllCodes at
--      it is a member of the stage `stage (AllCodes A .fst)
--      (AllCodes A .snd)`, the EARLIEST such stage, with ordinality and
--      membership from the three projections of src/L/Stage.lagda.md
--      (`stage` :180, `stage-ord` :185-186, `stage-mem` :188-189).
--      [LJ-1.86]'s AllCodes-stage term at the older tree
--      (agents/tasks/archive/LJ-1-86/lj-1.86-report.md:18-19), at THIS
--      carrier.  `stage` is sealed, so this row never unfolds the
--      well-founded descent behind it.
allcodes-stage : (δ : V ℓ) (oδ : IsOrd δ)
               → Σ[ σ ∈ V ℓ ]
                   ( IsOrd σ × ⟨ AllCodes (LsetS δ oδ) .fst SV.∈ˢ Lset σ ⟩ )
allcodes-stage δ oδ =
  stage (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)
    , stage-ord (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)
    , stage-mem (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)


-- ===================================================================
-- SECTION 1.  W3, IMPORTED, AND THE OBLIGATION.
--
--   The widest unmeasured term, measured alone first
--   (agents/tasks/LJ-1-600/runs/W3.agda): `keyS` at this carrier, TYPE
--   ONLY, and the carrier equation that says the alphabet is the
--   stage's members with no bridge.  The obligation below IS that row,
--   re-bound in this file's own name: the body is the chapter's own
--   application, and it elaborates only under the written type.
-- ===================================================================

-- 1.1  THE OBLIGATION.  `keyS` (src/L/Coding/CodeSet.lagda.md:300-301)
--      instantiated at `A := LsetS δ oδ`: the coded copy of the meta
--      syntax over `⟪ Lset δ ⟫`, ingredient (v) at this carrier.
key-at-stage : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
key-at-stage δ oδ = keyS (LsetS δ oδ)

-- 1.2  AND IT IS THE ALONE-TYPECHECKED W3 ROW, which ties the import to
--      the measurement and re-states that the obligation and the
--      widest term are ONE term here, not two.
key-at-stage-is-w3 : key-at-stage ≡ W3.key-at-stage
key-at-stage-is-w3 = refl

-- 1.3  THE CARRIER'S FIRST COMPONENT IS THE STAGE ITSELF, imported
--      from W3 rather than restated: `LsetS δ oδ = Lset δ , _` is
--      literal (src/L/Axioms/Basic.lagda.md:160-161), so the alphabet
--      `Formula ⟪ Lset δ ⟫ n` in every row below is the chapter's own
--      `Formula ⟪ fst (LsetS δ oδ) ⟫ n` by ONE definitional
--      projection.  ONE spelling throughout, R-41's cure
--      (dev/LESSONS.md:4762); no `sucV` chain, no iterate, depth one.
stage-carrier : (δ : V ℓ) (oδ : IsOrd δ) → LsetS δ oδ .fst ≡ Lset δ
stage-carrier = W3.stage-carrier


-- ===================================================================
-- SECTION 2.  THE COLLECTION ROWS.
--
--   What makes the bare function of 1.1 into ingredient (v), the coded
--   copy the existential ranges over, is that its image is COLLECTED
--   as one element of L with both directions: the chapter exports
--   exactly those two facts, and the rows below instantiate them at
--   this carrier.  [LJ-1.594] measured the generic forms green
--   (agents/tasks/LJ-1-594/Probe594.agda:392-401); the instantiation
--   at THIS carrier is what no task had measured, and it is these
--   rows.
--
--   NOT ATTEMPTED: (i) `D` and its `inv`, (ii) the leastness, (iii)
--   the pairing `sq`, (iv) the branch `ih` and its `Recursion`
--   instance.  AD12 gives this brief one obligation.
-- ===================================================================

-- 2.1  THE ARITY THE SITE USES.  The `class-pred` existential ranges at
--      arity ONE (`Formula ⟪ Lset δ ⟫ 1`,
--      src/L/StageCardinal.lagda.md:286, :321); the obligation is
--      arity-generic because AllCodes is, and this row names the
--      instance the site plugs into.
key-at-stage-1 : (δ : V ℓ) (oδ : IsOrd δ) → Formula ⟪ Lset δ ⟫ 1 → S
key-at-stage-1 δ oδ = key-at-stage δ oδ

-- 2.2  EVERY META FORMULA AT THIS CARRIER HAS A KEY, AND AllCodes AT
--      THIS CARRIER HOLDS IT.  `key∈AllCodes`
--      (src/L/Coding/CodeSet.lagda.md:443-447) applied at
--      `A := LsetS δ oδ`.  This is the introduction half of the coded
--      copy: the object-language existential can range over AllCodes
--      without losing any meta formula.
key-collected :
    (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} (φ : Formula ⟪ Lset δ ⟫ n)
  → ⟨ key-at-stage δ oδ φ SL.∈ˢ AllCodes (LsetS δ oδ) ⟩
key-collected δ oδ φ = key∈AllCodes (LsetS δ oδ) φ

-- 2.3  AND EVERY MEMBER OF AllCodes AT THIS CARRIER IS THE KEY OF A
--      META FORMULA AT THIS CARRIER.  `AllCodes-out`
--      (src/L/Coding/CodeSet.lagda.md:449-455) applied at
--      `A := LsetS δ oδ`.  This is the elimination half: the
--      object-language existential gains nothing it cannot decode.
--      The truncation's payload is WRITTEN OUT, the law the CodeSet
--      chapter itself recorded for `PT.rec` at a concrete environment.
coded-member :
    (δ : V ℓ) (oδ : IsOrd δ) (x : S)
  → ⟨ x SL.∈ˢ AllCodes (LsetS δ oδ) ⟩
  → ∥ (Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ Lset δ ⟫ n ]
        (x .fst ≡ key-at-stage δ oδ ψ .fst)) ∥₁
coded-member δ oδ x x∈ = AllCodes-out (LsetS δ oδ) x x∈
