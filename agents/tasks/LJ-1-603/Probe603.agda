{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  INGREDIENT (iv) AT THE INFINITE MEMBER STAGES.
--
-- VERDICT: NO-GO.  agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md
-- states it and names the atom: THE LIMIT CASE REACHES `sq`.  **THE
-- OBLIGATION `rec-graph-at-infinite` IS NOT IN THIS FILE** and no weaker
-- term is offered as one: that is [LJ-1.597]'s discipline
-- (agents/tasks/LJ-1-597/Probe597.agda:5-8).  This file carries NO hole
-- and NO postulate, so every row in it is a measurement and not a
-- claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-603/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3-2.out`, GREEN, 1.42 s, cap 120 s; the
-- record spelling of the same index WALLS the pane's 2 GB, four runs,
-- `runs/w3-1.out` and `runs/bisect-a.out` to `bisect-c.out`, and the
-- Sigma spelling is the cure `runs/bisect-d.out` measured, 1.32 s).
-- It is IMPORTED below, not restated, and so is [LJ-1.601]'s table
-- term: the brief's order, and the two halves stand at their own
-- types with no respelling of either.  (The brief cites rule "R-42"
-- at dev/LESSONS.md:4404 for the respelling price; NO RULE R-42 IS IN
-- THE TREE, and dev/LESSONS.md:4404 is C-53's related-names line.  The
-- report states this defect; the order stands on its own.)
--
-- THE FLOOR WAS MEASURED BEFORE THE ROWS (owner's ruling of
-- 2026-08-23): `runs/floor-1.out` is this file's frame WITHOUT
-- section 1 (imports, [LJ-1.601]'s term, the type rows), GREEN at
-- 11.27 s.  The delivered file is GREEN at 112.67 s cold and 1.27 s
-- warm (`runs/final-4.out`, `runs/final-5.out`, cap 300 s, peak
-- 898 MB under the pane's 2 GB).  THE ROWS 1.1 TO 1.3 CARRY THE COST:
-- alone, on the same frame, they run 113.22 s (`runs/bisect-g.out`),
-- so the written-out class-pred type at the member stage is the
-- price, exactly as it was at the ambient stage for [LJ-1.594].
-- One error of mine is on record: `runs/final-1.out`, exit 42, a
-- missing module argument to `SC.Bound.numeral` in row 1.7, found by
-- the isolated arm `runs/bisect-e.out` (GREEN at 1.64 s after the
-- fix) and fixed by one edit.
--
--   Section 0.  W3, imported, and the statement's shape.
--   Section 1.  THE VALUE EQUATION AT AN INFINITE MEMBER STAGE, seven
--               `refl` rows.  [LJ-1.594]'s discipline, one stage down:
--               every row is at the MEMBER stage `δ`, where [LJ-1.594]
--               wrote its rows at the ambient stage `α`.  Rows 1.3,
--               1.4 and 1.7 are the `sq` arrival, measured.
--   Section 2.  THE FINITE BASE BESIDE IT, imported, one row.  The two
--               halves of ingredient (iv) compose at one type with no
--               respelling: [LJ-1.601]'s table term at [LJ-1.601]'s own
--               statement, under this pane's parameters.
--   Section 3.  THE BRANCH'S LIMIT CASE, TYPE ONLY, and `P` is the
--               injection: the reading that ties section 1 to
--               ingredient (iv), with its sites named.
--   Section 4.  THE OBLIGATION'S TYPE, stated by import and NOT
--               inhabited.  The stop file carries the verdict.
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

module LJ-1-603.Probe603 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import FOL.Count {ℓ} using ( composed-count; code )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- THE STATEMENT, imported from the slice that typechecked it alone.
import LJ-1-603.runs.W3 {ℓ} lem α₀ oα₀ sq as W3


-- ===================================================================
-- SECTION 0.  W3, IMPORTED.
--
--   `W3.InfStage` is the limit case's own index: a member stage δ
--   with `ω ∈ δ` (its fifth component).  `W3.Ih i` is the branch below
--   the member stage, abstract.  `W3.RecGraphInf i ih` is the
--   obligation's type: a `Formula S 2`, value first and index second,
--   with both directions, at the step's function part AT the member
--   stage, read on the members of `Lset δ` (`W3.val`).
-- ===================================================================


-- ===================================================================
-- SECTION 1.  THE VALUE EQUATION AT AN INFINITE MEMBER STAGE, BY
--              `refl`.
--
--   WHAT THE RECURSION'S VALUE IS AT AN INFINITE MEMBER STAGE.  The
--   step at the member stage is `limit-step` at it (1.1); `limit-step`
--   is `LimitStep.h` with the site's `D` and `inv` (src/L/
--   StageCardinal.lagda.md:396-403); `h x` is the ORDINAL-LEAST y with
--   `class-pred x y` (1.2, src/L/StageCardinal.lagda.md:349-351); and
--   `class-pred x y` is the truncated existence of a stage index m and
--   a formula φ with `D ... ≡ x` and THE PACKED VALUE EQUAL TO y
--   (1.3).  THE PACKING IS `sq δ δ∈suc infδ` APPLIED (1.4), AND THE
--   COUNT INSIDE IT PACKS THROUGH THE SAME PARAMETER (1.5 to 1.7).
--   So the ONLY occurrence of the value y in the value equation sits
--   on the `sq`-application side, TWICE.
--
--   THE FINITE BASE, FOR CONTRAST.  At a finite member stage the value
--   is `numeralω (least x x∈)`
--   (src/L/StageCardinal.lagda.md:459, a numeral: NO `sq`), measured
--   GO by [LJ-1.601].  The limit case is NOT a transcription of that
--   table: the selection changes from a natural-number least over a
--   finite tally to an ordinal least over a class whose every witness
--   is packed through the bare pairing parameter at the member stage.
--
--   EVERY ROW IS AT THE MEMBER STAGE.  [LJ-1.594] wrote its rows at
--   the ambient stage α (Probe594.agda:227-341); these are the same
--   rows one stage down, at δ, which is what ingredient (iv) supplies
--   to the count when the member stage is infinite.
-- ===================================================================

-- 1.1  THE STEP AT THE MEMBER STAGE IS `LimitStep.h` AT IT, with the
--      site's `D` and `inv` supplied.  [LJ-1.594]'s `D-at-the-site`
--      (Probe594.agda:227-234), one stage down.
step-at-member :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
  → fst (SC.limit-step δ δ∈suc oδ infδ ih)
    ≡ SC.LimitStep.h δ δ∈suc oδ infδ (λ ε φ → DefOf.defSet (Lset ε) φ)
        (λ ε y h → 𝒟ₒ-inv (Lset ε) y h) ih
step-at-member _ _ _ _ _ = refl

-- 1.2  THE VALUE IS THE ORDINAL-LEAST WITNESS.  [LJ-1.594]'s
--      `h-is-leastOf` (Probe594.agda:305-317), one stage down.
value-is-leastOf :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (D : (ε : V ℓ) → Formula ⟪ Lset ε ⟫ 1 → V ℓ)
    (inv : (ε : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset ε) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset ε ⟫ 1 ] (D ε φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
    (x : ⟪ Lset δ ⟫)
  → SC.LimitStep.h δ δ∈suc oδ infδ D inv ih x
    ≡ fst (leastOf (SC.OrdSWO.ordSWO δ oδ) lem
             (SC.LimitStep.class-pred δ δ∈suc oδ infδ D inv ih x)
             (SC.LimitStep.nonempty δ δ∈suc oδ infδ D inv ih x))
value-is-leastOf _ _ _ _ _ _ _ _ = refl

-- 1.3  **THE ROW: THE CLASS, WRITTEN OUT, AND THE VALUE SITS ON THE
--      `sq`-APPLICATION SIDE.**  [LJ-1.594]'s `class-pred-is`
--      (Probe594.agda:283-300), one stage down.  READ THE RIGHT HAND
--      SIDE: the second conjunct of the witness is
--          `fst (sq δ δ∈suc infδ) (m , cnt m φ) ≡ y`,
--      and y occurs NOWHERE ELSE.  A `Formula` for this graph must
--      express THAT equation, and `sq` is the bare module parameter
--      (src/L/StageCardinal.lagda.md:17-20): injectivity and nothing
--      else, no formula, no Levy grade, no stage.
class-pred-at-member :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (D : (ε : V ℓ) → Formula ⟪ Lset ε ⟫ 1 → V ℓ)
    (inv : (ε : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset ε) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset ε ⟫ 1 ] (D ε φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
    (x : ⟪ Lset δ ⟫) (y : ⟪ δ ⟫)
  → SC.LimitStep.class-pred δ δ∈suc oδ infδ D inv ih x y
    ≡ ( ∥ Σ[ m ∈ ⟪ δ ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪ δ ⟫↪ m) ⟫ 1 ]
            ( ( D (⟪ δ ⟫↪ m) φ ≡ ⟪ Lset δ ⟫↪ x )
            × ( fst (sq δ δ∈suc infδ)
                  ( m
                  , SC.LimitStep.cnt δ δ∈suc oδ infδ D inv ih m φ )
                ≡ y ) ) ∥₁
      , squash₁ )
class-pred-at-member _ _ _ _ _ _ _ _ _ = refl

-- 1.4  THE PACKING IS `sq` APPLIED AND NOTHING ELSE.  [LJ-1.584]'s
--      `pair-is-sq` (its runs/W3a.agda:41-46, imported by [LJ-1.594]
--      at Probe594.agda:238-243), re-proved here at the MEMBER STAGE
--      by the same one `refl`, [LJ-1.597]'s choice for the same reason
--      (Probe597.agda:180-184): one delta, and the import is not
--      bought for it.
pair-is-sq-at-member :
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥) (x y : ⟪ δ ⟫)
  → SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ) x y
    ≡ fst (sq δ δ∈suc infδ) (x , y)
pair-is-sq-at-member _ _ _ _ _ _ = refl

-- 1.5  THE COUNT IS INGREDIENT (iv) ITSELF.  [LJ-1.594]'s
--      `cnt-is-the-IH` (Probe594.agda:252-263), one stage down: `cnt`
--      at the member stage is the formula bound computed from `ih m`,
--      the injection at the stage BELOW THE MEMBER STAGE, and from
--      nothing else the pairing controls.
cnt-is-the-IH-at-member :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (D : (ε : V ℓ) → Formula ⟪ Lset ε ⟫ 1 → V ℓ)
    (inv : (ε : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset ε) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset ε ⟫ 1 ] (D ε φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
    (m : ⟪ δ ⟫) (φ : Formula ⟪ Lset (⟪ δ ⟫↪ m) ⟫ 1)
  → SC.LimitStep.cnt δ δ∈suc oδ infδ D inv ih m φ
    ≡ fst (SC.Bound.formula-bound δ oδ infδ (sq δ δ∈suc infδ)
             {K = ⟪ Lset (⟪ δ ⟫↪ m) ⟫} (ih m)) φ
cnt-is-the-IH-at-member _ _ _ _ _ _ _ _ _ = refl

-- 1.6  THE BOUND IS THE COUNT OF THE DESTRUCTURED FORMULA, one delta.
formula-bound-is-count :
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    {K : Type ℓ}
    (g : Σ[ f ∈ (K → ⟪ δ ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
    (φ : Formula K 1)
  → fst (SC.Bound.formula-bound δ oδ infδ (sq δ δ∈suc infδ) {K = K} g) φ
    ≡ SC.Bound.count-bound δ oδ infδ (sq δ δ∈suc infδ) g
         (fst (composed-count {K = K}) φ)
formula-bound-is-count _ _ _ _ _ _ = refl

-- 1.7  **THE COUNT'S OWN PACKING.**  `count-bound` at the member stage
--      is `pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n))
--      (tuple-g g k cs))` (src/L/StageCardinal.lagda.md:124-128), and
--      by 1.4 EVERY `pair` there is `sq δ δ∈suc infδ` applied.  This is
--      the SECOND `sq` arrival inside one value equation: the outer
--      packing (1.3) and the count's inner packing (this row) are the
--      same bare parameter at the same member stage.
count-bound-is-sq-packs :
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    {K : Type ℓ}
    (g : Σ[ f ∈ (K → ⟪ δ ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
    (k : ℕ) (ψ : Formula (⊥* {ℓ}) k) (n : ℕ) (cs : Vec K k)
  → SC.Bound.count-bound δ oδ infδ (sq δ δ∈suc infδ) g (k , (ψ , (n , cs)))
    ≡ SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
         (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) k)
         (SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
           (SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
             (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) (code ψ))
             (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) n))
           (SC.Bound.tuple-g δ oδ infδ (sq δ δ∈suc infδ) g k cs))
count-bound-is-sq-packs _ _ _ _ _ _ _ _ _ = refl


-- ===================================================================
-- SECTION 2.  THE FINITE BASE BESIDE IT, IMPORTED.
--
--   [LJ-1.601]'s delivered table term, at [LJ-1.601]'s own statement
--   type, under THIS pane's parameters: the finite half of ingredient
--   (iv) and this probe's infinite half stand in one file at their own
--   types, with no respelling of either.  The two halves do NOT join:
--   the stop file says why, and the reason is in section 1.
-- ===================================================================

import LJ-1-601.runs.W3 {ℓ} lem α₀ oα₀ sq as W601
import LJ-1-601.Probe601 {ℓ} lem α₀ oα₀ sq as P601

the-finite-base-has-a-formula : (n : ℕ) → W601.TallyGraph n
the-finite-base-has-a-formula = P601.finite-base-measured


-- ===================================================================
-- SECTION 3.  THE BRANCH'S LIMIT CASE, TYPE ONLY, AND THE TIE.
--
--   Ingredient (iv) at an infinite member stage is the branch's limit
--   case: `go (inr (inr ω∈δ)) = comp-inj (IH δ δ∈α oδ δ∈suc infδ)
--   (Emb.emb α oα δ δ∈α)` (src/L/StageCardinal.lagda.md:555-556), and
--   `stage-card-upper = ∈-induction step` (:566) makes `IH δ ...` the
--   step's own output at δ, which is section 1's subject.  THIS FILE
--   STATES THE TIE AS A READING WITH ITS SITES, and re-ascribes the
--   two rows the reading needs, TYPE ONLY: `ord-tri` is well-founded
--   induction under LEM (src/L/Ordinal/Linear.lagda.md:136-137), so no
--   `refl` can select the limit case at an abstract stage, and
--   [LJ-1.584] measured that `branch` in a conversion problem does not
--   terminate (agents/tasks/LJ-1-584/runs/w3b-1.out).
-- ===================================================================

-- 3.1  THE BRANCH, RE-ASCRIBED, TYPE ONLY.  [LJ-1.594]'s
--      `branch-at-the-site` (Probe594.agda:327-332).
branch-type :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((ε : V ℓ) → ⟨ ε ∈ˢ α ⟩ → SC.Upper.P ε)
  → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
branch-type = SC.Upper.branch

-- 3.2  AND `P` IS THE INJECTION ITSELF, so the induction hypothesis
--      the limit case hands to the member stage IS the thing whose
--      graph section 1 prices.  [LJ-1.594]'s `P-is-the-injection`
--      (Probe594.agda:337-341), and this one row IS `refl`.
P-is-the-injection :
    (ε : V ℓ) → SC.Upper.P ε
              ≡ ( IsOrd ε → ⟨ ε ∈ˢ sucV α₀ ⟩ → (⟨ ε ∈ˢ ω ⟩ → Empty.⊥)
                → (⟪ Lset ε ⟫ ↪ ⟪ ε ⟫) )
P-is-the-injection _ = refl


-- ===================================================================
-- SECTION 4.  THE OBLIGATION'S TYPE, STATED AND NOT INHABITED.
--
--   The obligation `rec-graph-at-infinite` is a term of
--   `W3.RecGraphInf i ih` at an index `i : W3.InfStage` and a branch
--   `ih : W3.Ih i`.  NO SUCH TERM IS IN THIS FILE and no weaker term
--   is offered under the obligation's name.  The stop is
--   agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md, and its
--   atoms are section 1's rows: the value equation at an infinite
--   member stage carries `sq δ δ∈suc infδ` in the ONLY occurrences of
--   the value (1.3, outer; 1.7 with 1.4, inner), and `sq` is the bare
--   parameter no formula can name.
-- ===================================================================
