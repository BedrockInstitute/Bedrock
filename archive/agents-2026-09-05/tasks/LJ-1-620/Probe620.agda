{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.620]  WHERE THE FOUR PAID INGREDIENTS WOULD LIVE: A SURVEY,
-- NOT A LANDING.
--
-- VERDICT: GO.  The obligation `landing-survey` IS in this file, at
-- section 5.  Nothing lands in `src/`: this file carries the four
-- paid `class-pred` ingredients as type-only rows (sections 1 and 2)
-- and as the imported paid terms of their probes (sections 3 and 4),
-- so that each ingredient's import closure is MEASURED by the file
-- that typechecks it, and the obligation states, for each of the
-- four, the chapter that could host it and the import edge the
-- landing would add.  This brief SURVEYS the landing, it does not
-- perform one.
--
-- THE FOUR, AS PAID (agents/tasks/LJ-1-594/
-- review-of-pairing-suffices.md:40-44):
--   (i)   `D` and its inversion, paid by [LJ-1.613],
--         agents/tasks/LJ-1-613/Probe613.agda:137-154.
--   (ii)  the least-element selection, paid by [LJ-1.613],
--         agents/tasks/LJ-1-613/Probe613.agda:180-192.
--   (iv)  the branch `ih` and its Recursion instance: base paid by
--         [LJ-1.601], agents/tasks/LJ-1-601/Probe601.agda section 4;
--         limit paid by [LJ-1.608], agents/tasks/LJ-1-608/
--         Probe608.agda section 3.
--   (v)   `keyS`, paid by [LJ-1.600],
--         agents/tasks/LJ-1-600/Probe600.agda:129-130, with its
--         collection `AllCodes`, agents/tasks/LJ-1-600/Probe600.agda
--         section 0.
--
-- W3 IS agents/tasks/LJ-1-620/runs/W3.agda AND IT WAS WRITTEN FIRST
-- AND TYPECHECKED ALONE under the two-minute cap the brief sets
-- (runs/w3-1.out): the import closure of ingredient (v), the smallest
-- of the four.  It is IMPORTED below, not restated.  IF EVEN THE
-- SMALLEST HAD A CLOSURE LIKE `CardAboveL`'S (the import-graph
-- measurement of [LJ-1.555], agents/tasks/LJ-1-555/
-- review-of-CardAboveL-landing.md:81), THAT WOULD ANSWER THE WHOLE
-- SURVEY IN ONE RUNG; IT DID NOT, AND THE ANSWER IS IN THE REPORT.
--
--   Section 1.  (i), TYPE ONLY, AT THE CARRIER.
--   Section 2.  (ii), TYPE ONLY, AT THE CARRIER.
--   Section 3.  (v), THE W3 TIE, IMPORTED.
--   Section 4.  (iv), THE PAID TERMS, IMPORTED, BASE AND LIMIT.
--   Section 5.  THE OBLIGATION: THE LANDING SURVEY.
--
-- NO ROW PUTS `step`, `branch` OR `stage-card-upper` INTO A CONVERSION
-- PROBLEM ([LJ-1.584]'s measurement, agents/tasks/LJ-1-584/runs/
-- w3b-1.out).  Sections 1 and 2 are type-only; sections 3 and 4
-- reference the paid probe terms and never normalize them.
--
-- DO NOT LAND ANYTHING AND DO NOT RUN `make check` (the brief): two
-- landing attempts heap-walled and [LJ-1.619] is measuring why; this
-- survey must not step into that.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty

module LJ-1-620.Probe620 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import L.StageCardinal
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- The paid terms, imported, never restated: W3 is this task's (v)
-- closure, measured alone first; G601 and P601 are the paid base
-- half of (iv) and its statement; G608 and P608 are the paid limit
-- half and its statement.
import LJ-1-620.runs.W3 {ℓ} lem as W3
import LJ-1-601.runs.W3 {ℓ} lem α₀ oα₀ sq as G601
import LJ-1-601.Probe601 {ℓ} lem α₀ oα₀ sq as P601
import LJ-1-608.runs.W3 {ℓ} lem α₀ oα₀ sq as G608
import LJ-1-608.Probe608 {ℓ} lem α₀ oα₀ sq as P608


-- ===================================================================
-- SECTION 1.  (i), TYPE ONLY, AT THE CARRIER.
--
--   The two terms [LJ-1.613] paid (agents/tasks/LJ-1-613/Probe613.
--   agda:137-154), restated here type-only for this file's own
--   closure measurement: `D` is the chapter's own `defSet` at the
--   stage, and its inversion is the chapter's own `𝒟ₒ-inv` at the
--   stage.  The closure this measurement needs is stated by the
--   import block above; the host question is answered in the report.
-- ===================================================================

-- 1.1  `D`, THE DEFINABLE POWER SET, AT THIS CARRIER.
i-D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → S
i-D δ φ = DefOf.defSet (Lset δ) φ

-- 1.2  THE INVERSION, AT THIS CARRIER.
i-inv : (δ : V ℓ) (y : S)
      → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
      → ∥ Σ[ φ ∈ Formula ⟪ Lset δ ⟫ 1 ] (i-D δ φ ≡ y) ∥₁
i-inv δ y h = 𝒟ₒ-inv (Lset δ) y h


-- ===================================================================
-- SECTION 2.  (ii), TYPE ONLY, AT THE CARRIER.
--
--   The selection [LJ-1.613] paid (agents/tasks/LJ-1-613/Probe613.
--   agda:180-192), restated here type-only: `leastOf` over the site's
--   own ordinal order, with the leastness certified by `IsLeast` in
--   the result type.  THIS IS THE ONE OF THE FOUR WHOSE STATEMENT
--   NAMES A STAGECARDINAL MODULE: the order is `SC.OrdSWO.ordSWO`,
--   and no landing of this ingredient can avoid that line.
-- ===================================================================

-- 2.1  THE SELECTION, AT THIS CARRIER.
ii-least : (δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
        → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
        → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a
ii-least δ oδ = leastOf (SC.OrdSWO.ordSWO δ oδ) lem


-- ===================================================================
-- SECTION 3.  (v), THE W3 TIE, IMPORTED.
--
--   The two rows [LJ-1.600] paid, at this carrier, in the W3 file
--   that typechecked them alone: the key of every meta formula, and
--   the stage that holds the collection.
-- ===================================================================

-- 3.1  THE KEY, IMPORTED.
v-key : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
v-key δ oδ = W3.key-at-stage δ oδ

-- 3.2  THE CODES AND THE STAGE THAT HOLDS THEM, IMPORTED.
v-codes : (δ : V ℓ) (oδ : IsOrd δ)
        → Σ[ σ ∈ V ℓ ] ( IsOrd σ × ⟨ AllCodes (LsetS δ oδ) .fst SV.∈ˢ Lset σ ⟩ )
v-codes δ oδ = W3.codes-stage δ oδ


-- ===================================================================
-- SECTION 4.  (iv), THE PAID TERMS, IMPORTED, BASE AND LIMIT.
--
--   The base half [LJ-1.601] paid as the table
--   (agents/tasks/LJ-1-601/Probe601.agda, `finite-base-measured`),
--   the limit half [LJ-1.608] paid as `rec-graph-at-infinite`.  Both
--   are referenced here at their paid statement types, so this file's
--   import block MEASURES the closure of (iv) as well: it is the
--   union of the two paid probes' closures.
-- ===================================================================

-- 4.1  THE FINITE BASE, AT ITS PAID STATEMENT.
iv-base : (n : ℕ) → G601.TallyGraph n
iv-base n = P601.finite-base-measured n

-- 4.2  THE LIMIT, AT ITS PAID STATEMENT.
iv-limit : (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
  (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩)
  → G608.Site.At.RecGraph∞ α oα α∈suc infα IH m ω∈δ
iv-limit α oα α∈suc infα IH m ω∈δ =
  P608.rec-graph-at-infinite α oα α∈suc infα IH m ω∈δ


-- ===================================================================
-- SECTION 5.  THE OBLIGATION: THE LANDING SURVEY.
--
--   For each of the four, the chapter of src/ that could host it,
--   stated as a term naming the module and the import edge it would
--   add; for any that cannot be hosted, what blocks it.  A "new
--   master" answer is a real answer, not a failure ([LJ-1.555]
--   reached exactly one for CardAboveL).  The counts are the number
--   of import LINES the host would add, measured over the 102
--   masters; every number is re-derivable from the import lines the
--   report cites at file:line.
-- ===================================================================

-- 5.1  THE CHAPTERS THE SURVEY NAMES.  One constructor per chapter;
--      the line above each names the master it means.
data Chapter : Type where
  constructible : Chapter   -- src/L/Constructible.lagda.md
  boundedSubset : Chapter   -- src/L/BoundedSubset.lagda.md
  faithful      : Chapter   -- src/L/Choice/Faithful.lagda.md
  stageCardinal : Chapter   -- src/L/StageCardinal.lagda.md
  ordinal       : Chapter   -- src/L/Ordinal.lagda.md
  recursion     : Chapter   -- src/L/Recursion.lagda.md
  codeSet       : Chapter   -- src/L/Coding/CodeSet.lagda.md
  definability  : Chapter   -- src/L/Definability.lagda.md

-- 5.2  THE IMPORT EDGES A LANDING ADDS, NAMED.
--      `none` means the host already contains every import line the
--      row needs.  The constructors name the lines below them.
data Edge : Type where
  -- no new import lines
  none              : Edge
  -- add: import L.Stage
  import-stage      : Edge
  -- add: import L.WellOrder.Base, import L.StageCardinal
  import-wo-stagec  : Edge
  -- add: import L.Recursion, import L.Choice.Finite
  import-rec-finite : Edge
  -- add: import L.Choice.Finite, import L.Ordinal.Stages, import L.StageCardinal, import V.Presentation
  import-four       : Edge
  -- add: import L.Stage, import L.Axioms.Basic
  import-stage-basic: Edge
  -- the host CANNOT land: L.Definability cannot import L.Constructible
  cycle-definability: Edge

record Landing : Type where
  field
    chapter : Chapter   -- the cheapest measured host
    edge    : Edge      -- the import lines it adds
    count   : ℕ         -- how many import lines it adds
    note    : Edge      -- the next-cheapest alternate, or the blocker

open Landing

record Survey : Type where
  field
    i  : Landing   -- (i) D and its inversion
    ii : Landing   -- (ii) the least-element selection
    iv : Landing   -- (iv) the branch and its Recursion instance
    v  : Landing   -- (v) keyS, the coded copy

open Survey

landing-survey : Survey
landing-survey = record
  { i  = record { chapter = constructible; edge = none; count = 0
                ; note = cycle-definability }
  ; ii = record { chapter = boundedSubset; edge = none; count = 0
                ; note = import-wo-stagec }
  ; iv = record { chapter = boundedSubset; edge = import-rec-finite; count = 2
                ; note = import-four }
  ; v  = record { chapter = faithful; edge = none; count = 0
                ; note = import-stage }
  }
