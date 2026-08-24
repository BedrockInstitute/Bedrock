{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  THE LANDING SURVEY: WHERE THE FOUR PAID `class-pred`
-- INGREDIENTS WOULD LIVE.
--
-- VERDICT: GO.  The obligation `landing-survey` IS in this file, at
-- section 5.  It is a SURVEY and not a landing: nothing lands in
-- `src/`, `make check` is not run, and every row below re-derives its
-- ingredient from `src/` names only, at the delivered type, inside a
-- fresh module.  THE PROBE ITSELF IS THE MEASUREMENT: a row whose
-- imports are a subset of an existing master's import lines is a row
-- that master can spell, and the import-graph reading in the report
-- says which masters those are.
--
-- W3 IS agents/tasks/LJ-1-625/runs/W3.agda AND IT WAS WRITTEN FIRST
-- AND TYPECHECKED ALONE under a 60 s cap (runs/w3-3.out: exit 42 at
-- exactly ONE unsolved interaction meta, the hole, and no other
-- error, 1.71 s, 386,842,624 bytes).  THE OBLIGATION BELOW HAS THAT
-- VERY TYPE, imported, so the stated survey and the delivered one
-- cannot drift.  Two earlier W3 runs are the record of the parse cure
-- (runs/w3-1.out, the constructor block; runs/w3-2.out, one arity
-- row).  The four per-ingredient frames were priced BEFORE this file
-- was assembled (runs/floorI-1.out to runs/floorV-1.out, all green,
-- 1.28 to 1.81 s, 233,652,224 to 345,325,568 bytes).
--
--   Section 0.  D-10, the four rows' truth, priced before the terms.
--   Section 1.  (i) AT `L.Constructible`: `D` and its inversion,
--               spelled from that chapter's own import lines.
--   Section 2.  (ii) AT `L.StageCardinal`: `leastOf` over the site's
--               own ordinal well-order, whose instance already
--               elaborates inside the site's `h`
--               (src/L/StageCardinal.lagda.md:351).
--   Section 4.  (iv) AT `L.BoundedSubset`: the branch's graph at a
--               strictly infinite member stage, statement restated
--               from `src/` names only and term re-derived from
--               [LJ-1.608]'s green rows.
--   Section 3.  (v) AT `L.Choice.Faithful`: `keyS` at the certified
--               stage with both collection halves.
--   Section 5.  THE OBLIGATION: one Row per ingredient, the measured
--               host, the measured edges (none for any of the four),
--               the blocker the brief gave for (i), and the
--               re-derived ingredient.
--
-- THE GENERAL ANSWER THE BRIEF ASKED TO BE TESTED, measured here:
-- NO ingredient of the four NEEDS a new master.  Each has an existing
-- edge-free host, and the two surveys' shape (terms sitting above
-- every chapter that wants them) holds ONLY of (i)'s natural home
-- `L.Definability`, which is one half of one row, not the survey.
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
open import Cubical.Data.List using ( [] )
import Cubical.Data.Empty as Empty

module LJ-1-625.Probe625 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

import LJ-1-625.runs.W3 {ℓ} lem α₀ oα₀ sq as W3
open W3 using ( Row; lands-at; Chapter; definibility; constructible
              ; stageCardinal; boundedSubset; choiceFaithful
              ; Blocker; unblocked; cycle-definability )


-- ===================================================================
-- SECTION 0.  D-10, THE FOUR ROWS' TRUTH, PRICED BEFORE THE TERMS.
--
--   Every witness below is a substitution instance of a green `src/`
--   chapter (`DefOf.defSet`, `𝒟ₒ-inv`, `leastOf`, `keyS`) or a copy
--   of a green probe row ([LJ-1.608]'s `Rows.the-graph`), so no
--   Tarskian or cardinality obstruction can reach any of them.  What
--   CAN fail is the survey's reading, and that is checked the other
--   way: by the import-graph count in the report and by the fact that
--   every open in sections 1 to 4 names a module the row's host
--   already imports.
--
--   THE ONE ROW TAKEN AS GIVEN (the brief's quote, not re-derived):
--   (i)'s natural home `L.Definability` is blocked, because the rows
--   need `Lset` and `𝒟ₒ` from `L.Constructible`, and
--   `L.Constructible` already imports `L.Definability`
--   (src/L/Constructible.lagda.md:37); the reverse edge is a cycle.
--   The blocker field of row (i) carries exactly this.
-- ===================================================================


-- ===================================================================
-- SECTION 1.  INGREDIENT (i), AT `L.Constructible`.
--
--   The host already imports every name this section opens:
--   `FOL.ZFStructure`, `FOL.Syntax`, `V.Hierarchy` and
--   `L.Definability` at src/L/Constructible.lagda.md:34-37, and
--   `Lset`, `𝒟ₒ`, `𝒟ₒ-inv` are the chapter's own definitions.  The
--   two rows are [LJ-1.613]'s `D-carrier` and `inv-carrier`
--   (agents/tasks/LJ-1-613/Probe613.agda:137-154), verbatim in body.
-- ===================================================================

module Section-1 where

  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
  open import L.Definability {ℓ} using ( module DefOf )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )
  open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

  d-and-inv : W3.Ingredient-I.DInvType
  d-and-inv =
    (λ δ φ → DefOf.defSet (Lset δ) φ) ,
    (λ δ y h → 𝒟ₒ-inv (Lset δ) y h)


-- ===================================================================
-- SECTION 2.  INGREDIENT (ii), AT `L.StageCardinal`.
--
--   The host is the site chapter itself: `OrdSWO.ordSWO` is its own
--   definition (src/L/StageCardinal.lagda.md:258-264), `leastOf` is
--   already imported (src/L/StageCardinal.lagda.md:35-36), and the
--   very instance this row generalises already elaborates inside the
--   site's `h` (src/L/StageCardinal.lagda.md:351).  The row is
--   [LJ-1.613]'s `least-at-carrier`
--   (agents/tasks/LJ-1-613/Probe613.agda:180-184), verbatim in body.
--   The landing widens ONE using clause (`IsLeast` joins the
--   L.WellOrder.Base line) and adds NO import edge.
-- ===================================================================

module Section-2 where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )
  open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
  import L.StageCardinal
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
  open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

  least-at : W3.Ingredient-II.LeastType
  least-at δ oδ = leastOf (SC.OrdSWO.ordSWO δ oδ) lem


-- ===================================================================
-- SECTION 4.  INGREDIENT (iv), AT `L.BoundedSubset`.
--
--   The host already imports every name this section opens, and it
--   already instantiates the site at its own parameters:
--   `module SC = L.StageCardinal {ℓ} lem α ordα sq` inside
--   `BoundedSubsetAt` (src/L/BoundedSubset.lagda.md:1397), with
--   `import L.StageCardinal` at src/L/BoundedSubset.lagda.md:882.
--   The statement is [LJ-1.608]'s (restated in W3 above, from `src/`
--   names only), and the term is [LJ-1.608]'s `Rows.the-graph`
--   (agents/tasks/LJ-1-608/Probe608.agda:111-161), verbatim in body.
-- ===================================================================

module Section-4 where

  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
  open import V.Presentation {ℓ} using ( member; fiber )
  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import FOL.Absoluteness
  open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL; Lset )
  open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord )
  open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
  open import L.Axioms.Basic {ℓ} using ( LsetS )
  import L.StageCardinal
  open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
  open InfinitySet {ℓ} using ( ω; sucV )
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module SV = hPropStructure 𝒮ᵥ
  module SL = hPropStructure 𝒮ʟ
  open SV using ( _∈ˢ_ )
  open SL using ( S )
  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
  open SC using ( _↪_ )

  -- The lifts and the statement are W3's own, used at this section's
  -- identical spelling, so the term below discharges the very type the
  -- survey row carries.
  module TheSite = W3.Ingredient-IV

  comp-fst : {A B C : Type ℓ} (g : A ↪ B) (h : B ↪ C) (j : A)
    → fst (SC.Upper.comp-inj g h) j ≡ fst h (fst g j)
  comp-fst (f , _) (g , _) j = refl

  module Rows
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
    (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩) where

    module AT = TheSite.Site.At α oα α∈suc infα IH m ω∈δ
    open AT

    val-eq : (x : S) (k : ⟨ fst x ∈ fst δL ⟩)
      → fst (val x k) ≡ fst (valδ x k)
    val-eq x k =
      cong (⟪ α ⟫↪)
        ( comp-fst IHδ (SC.Upper.Emb.emb α oα δ δ∈α) (TheSite.ixOf δL x k) )
      ∙ fiber α {x = ⟪ δ ⟫↪ (fst IHδ (TheSite.ixOf δL x k))}
          ( oα .fst (member δ (fst IHδ (TheSite.ixOf δL x k))) δ∈α ) .snd

    the-graph : RecGraph∞
    the-graph G = ψ , (defines-side , only-side)
      where
      ψ : Formula S 2
      ψ = fst G
      IHd : (x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
        → fst y ≡ fst (valδ x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
      IHd = fst (snd G)
      IHo : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
        → (k : ⟨ fst x ∈ fst δL ⟩) → fst y ≡ fst (valδ x k)
      IHo = snd (snd G)
      defines-side : (x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
        → fst y ≡ fst (val x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
      defines-side x y k e = IHd x y k (e ∙ val-eq x k)
      only-side : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
        → (k : ⟨ fst x ∈ fst δL ⟩) → fst y ≡ fst (val x k)
      only-side x y sat k = IHo x y sat k ∙ sym (val-eq x k)

  rec-graph-at-infinite : W3.Ingredient-IV.RecGraphType
  rec-graph-at-infinite α oα α∈suc infα IH m ω∈δ =
    Rows.the-graph α oα α∈suc infα IH m ω∈δ


-- ===================================================================
-- SECTION 3.  INGREDIENT (v), AT `L.Choice.Faithful`.
--
--   The host already imports every name this section opens:
--   `L.Coding.CodeSet` at src/L/Choice/Faithful.lagda.md:63-65
--   (whose using list carries `keyS`, `AllCodes`, `AllCodes-out`),
--   `L.Axioms.Basic` at :51 (`LsetS`), `L.Constructible` at :46-47
--   (`Lset`, `IsOrd`, `𝒮ʟ`), `V.Hierarchy` at :44, `FOL.Syntax` at
--   :42, `FOL.ZFStructure` at :41.  The rows are [LJ-1.600]'s
--   `key-at-stage-1`, `key-collected` and `coded-member`
--   (agents/tasks/LJ-1-600/Probe600.agda:160-189), verbatim in body.
--   The landing widens ONE using clause (`key∈AllCodes` joins the
--   CodeSet line) and adds NO import edge.
-- ===================================================================

module Section-3 where

  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
  open import L.Axioms.Basic {ℓ} using ( LsetS )
  open import L.Coding.CodeSet {ℓ} lem
    using ( keyS; AllCodes; key∈AllCodes; AllCodes-out )
  module SL = hPropStructure 𝒮ʟ
  open SL using ( S )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )

  key-and-collection : W3.Ingredient-V.KeyType
  key-and-collection =
    (λ δ oδ φ → keyS (LsetS δ oδ) φ) ,
    (λ δ oδ φ → key∈AllCodes (LsetS δ oδ) φ) ,
    (λ δ oδ x x∈ → AllCodes-out (LsetS δ oδ) x x∈)


-- ===================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   One Row per paid ingredient, in the table's order (i), (ii),
--   (iv), (v).  Every `new-edges` is the empty list: the reading in
--   the report found an existing host for each ingredient whose
--   direct imports already cover the section's opens.  The blocker
--   field carries the brief's given cycle on row (i) and `unblocked`
--   on the other three.
-- ===================================================================

landing-survey : W3.Survey
landing-survey =
  (lands-at constructible [] cycle-definability Section-1.d-and-inv)
  , (lands-at stageCardinal [] unblocked Section-2.least-at)
  , (lands-at boundedSubset [] unblocked Section-4.rec-graph-at-infinite)
  , (lands-at choiceFaithful [] unblocked Section-3.key-and-collection)
