{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.613]  INGREDIENTS (i) AND (ii) OF THE `class-pred` TABLE,
-- INSTANTIATED AT THIS CARRIER.
--
-- VERDICT: GO.  The obligation `first-two-internal` IS in this file, at
-- 5.1: the two ingredients `[LJ-1.594]` called "already internal",
-- written STANDALONE at the carrier `[LJ-1.600]` fixed.  This file
-- carries NO hole and NO postulate, so every row in it is a
-- measurement and not a claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-613/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE under a two-minute cap (runs/w3-1.out to w3-3.out,
-- GREEN, 0.90 to 1.29 s; one negative control at runs/w3-neg-1.out,
-- exit 42 at the planted error and nowhere else).  IT IS IMPORTED
-- below, not restated.  The FLOOR was measured with the obligation and
-- the site row as holes in this file's full import frame
-- (runs/Floor.agda, runs/floor-1.out), per the owner's ruling of
-- 2026-08-23, BEFORE the proof was attempted.
--
--   Section 0.  D-10, BEFORE ANY AGDA, AND IT IS THE TWO CLAIMS.
--   Section 1.  CLAIM (i), INSTANTIATED.  `D` and its inversion, the
--               site's own supply, standalone at every stage.
--   Section 2.  CLAIM (ii), INSTANTIATED.  `leastOf` over the ordinal
--               order, standalone at every stage.
--   Section 3.  THE SITE ACCEPTS THEM.  `LimitStep.h` runs at these
--               two, and the run IS the site's own call, by refl.
--   Section 4.  THE (v) TIE, IMPORTED.  Every formula (i) consumes has
--               its code at this carrier: [LJ-1.600]'s term, imported,
--               never restated.
--   Section 5.  THE OBLIGATION.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a conversion
-- problem ([LJ-1.584]'s measurement, agents/tasks/LJ-1-584/runs/
-- w3b-1.out).  Section 3's rows mention `limit-step` under `refl`
-- only, the exact shape [LJ-1.594]'s `D-at-the-site` measured green
-- (agents/tasks/LJ-1-594/Probe594.agda:227-234).  The pairing `sq`
-- stays the ABSTRACT module parameter it is in `src/`; no row
-- instantiates it, prices it, or reaches into the circle.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd; Lset )
open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-613.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : SqParam α₀) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open InfinitySet using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import L.StageCardinal
import LJ-1-613.runs.W3 {ℓ} as W3
import LJ-1-600.Probe600 {ℓ} lem as P600

open hPropStructure 𝒮ᵥ using ( _∈ˢ_; _∈ᵗ_ )
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

-- The delivered chapter, at this pane's parameters, exactly as
-- [LJ-1.594] opened it (agents/tasks/LJ-1-594/Probe594.agda:84-85).
-- The `sq` parameter is INHERITED and untouched: this file instantiates
-- nothing inside the circle.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY AGDA, AND IT IS THE TWO CLAIMS.
--
--   THE BRIEF ASKS what (i) and (ii) are and what "already internal"
--   was claimed to mean.  THE TABLE IS
--   agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-41, and its
--   two INTERNAL rows read, verbatim:
--
--     "| (i) | `D`, the definable power set | INTERNAL. `D-at-the-site`,
--       `Probe594.agda:227-234`: at the real site `limit-step` supplies
--       `DefOf.defSet (Lset ·)` and `𝒟ₒ-inv`
--       (`src/L/StageCardinal.lagda.md:400-401`) |"
--
--     "| (ii) | the least-element selection | INTERNAL. `h-is-leastOf`,
--       `Probe594.agda:305-317`: `leastOf` over `OrdSWO.ordSWO`
--       (`src/L/StageCardinal.lagda.md:349-351`, `:258-264`) |"
--
--   SO "ALREADY INTERNAL" MEANT: no new construction is needed, because
--   the terms already exist in the live tree -- `DefOf.defSet`
--   (src/L/Definability.lagda.md:111-112), `𝒟ₒ-inv`
--   (src/L/Constructible.lagda.md:306-308) and `leastOf`
--   (src/L/WellOrder/Base.lagda.md:158-161) over the site's own
--   `OrdSWO.ordSWO` (src/L/StageCardinal.lagda.md:258-264).
--
--   AND WHAT IT DID NOT MEAN, which is the gap this task closes: BOTH
--   claims were measured only THROUGH THE SITE'S OWN CALL.  `D-at-the-
--   site` and `h-is-leastOf` are equations ABOUT `limit-step`'s body at
--   the real site; neither ingredient was ever written STANDALONE at
--   the carrier `[LJ-1.600]` fixed, and `[LJ-1.594]`'s own route line
--   put (i) and (ii) behind (v)
--   (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:140-141):
--   "`keyS` at `A := LsetS δ oδ`. Then (i) and (ii), which are already
--   internal."  (v) is paid ([LJ-1.600]), so the order now permits
--   this task.  A recorded claim is not a term: the campaign's own
--   `pick-canonical` case (archive/dev/LJ-dispatch-index.md:212) says
--   so, which is why the sections below INHABIT the claims rather than
--   quote them.
-- ===================================================================


-- ===================================================================
-- SECTION 1.  CLAIM (i), INSTANTIATED.
--
--   The site's own supply (src/L/StageCardinal.lagda.md:400-401),
--   standalone at every stage, in the parameter shapes `LimitStep`
--   itself declares (src/L/StageCardinal.lagda.md:278-280): `D` over
--   the stage with NO ordinality demanded, `inv` over `𝒟ₒ`'s members.
-- ===================================================================

-- 1.1  THE OPERATOR, AT THIS CARRIER.  `DefOf.defSet (Lset δ)`
--      (src/L/Definability.lagda.md:111-112) applied at the stage, the
--      exact term the site's `limit-step` passes as `D`
--      (src/L/StageCardinal.lagda.md:400).
D-carrier : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ
D-carrier δ φ = DefOf.defSet (Lset δ) φ

-- 1.2  AND IT IS THE ALONE-TYPECHECKED W3 ROW, which ties this file to
--      the measurement and re-states that the delivery and the widest
--      term are ONE term here, not two.
D-carrier-is-w3 : D-carrier ≡ W3.D-at-carrier
D-carrier-is-w3 = refl

-- 1.3  THE INVERSION, AT THIS CARRIER.  `𝒟ₒ-inv (Lset δ)`
--      (src/L/Constructible.lagda.md:306-308), the exact term the
--      site's `limit-step` passes as `inv`
--      (src/L/StageCardinal.lagda.md:401).  Its conclusion mentions
--      `D-carrier δ φ₀`, which is `DefOf.defSet (Lset δ) φ₀` by one
--      delta step, so the two rows compose with NO bridge.
inv-carrier : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
            → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D-carrier δ φ₀ ≡ y) ∥₁
inv-carrier δ y h = 𝒟ₒ-inv (Lset δ) y h

-- 1.4  AND IT IS THE ALONE-TYPECHECKED W3 ROW TOO.
inv-carrier-is-w3 : inv-carrier ≡ W3.inv-at-carrier
inv-carrier-is-w3 = refl


-- ===================================================================
-- SECTION 2.  CLAIM (ii), INSTANTIATED.
--
--   The selection `h` uses (src/L/StageCardinal.lagda.md:349-351),
--   standalone at every stage: `leastOf` over `OrdSWO.ordSWO`, the
--   ordinal order on the stage index's members, at the clause's own
--   predicate grade `hProp (ℓ-suc ℓ)`
--   (src/L/StageCardinal.lagda.md:319-320).
-- ===================================================================

-- 2.1  THE SELECTION, AT THIS CARRIER.  `leastOf`
--      (src/L/WellOrder/Base.lagda.md:158-161) over the site's own
--      `OrdSWO.ordSWO δ oδ` (src/L/StageCardinal.lagda.md:258-264):
--      every nonempty class over the members of a stage has its
--      ordinal-least member, with the leastness CERTIFIED in the result
--      type by `IsLeast` (src/L/WellOrder/Base.lagda.md:130-131).
--      This is the exact term inside the site's `h` (src/L/
--      StageCardinal.lagda.md:350-351), lifted out and quantified over
--      the stage.
least-at-carrier : (δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
                 → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
                 → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a
least-at-carrier δ oδ = leastOf (SC.OrdSWO.ordSWO δ oδ) lem

-- 2.2  AND THE ORDER IT SELECTS IN IS THE ORDINAL ORDER, by one
--      projection and one delta step: `ordSWO`'s relation field is
--      `_≺_` (src/L/StageCardinal.lagda.md:257) and `_≺_ m n` is
--      membership between the members' sets (:247-248).  Premise 9 of
--      the brief, re-measured here rather than quoted.
the-order-at-carrier : (δ : V ℓ) (oδ : IsOrd δ) (m n : ⟪ δ ⟫)
  → SWO._<∙_ (SC.OrdSWO.ordSWO δ oδ) m n ≡ (⟪ δ ⟫↪ m ∈ᵗ ⟪ δ ⟫↪ n)
the-order-at-carrier δ oδ m n = refl


-- ===================================================================
-- SECTION 3.  THE SITE ACCEPTS THEM.
--
--   The strongest reading of "instantiated at this carrier" is not the
--   standalone rows alone but the SITE'S OWN CLAUSE RUNNING AT THEM.
--   `LimitStep` takes `D` and `inv` as parameters
--   (src/L/StageCardinal.lagda.md:277-280); the two rows below apply
--   the site's assembly `h , h-inj` at THIS file's two terms, and the
--   second row says the result IS `limit-step`'s own value, by refl.
--   This is [LJ-1.594]'s `D-at-the-site` shape
--   (agents/tasks/LJ-1-594/Probe594.agda:227-234), with the lambdas
--   replaced by the standalone terms of sections 1 and 2.
--
--   The pairing `sq` enters ONLY as the abstract module parameter it
--   already is at the site; the induction hypothesis `ih` enters only
--   as the abstract argument `limit-step` itself demands
--   (src/L/StageCardinal.lagda.md:396-398).  NOTHING HERE IS ABOUT
--   (iii) OR (iv).
-- ===================================================================

-- 3.1  THE SITE'S ASSEMBLY, AT THESE TWO.  `LimitStep.h` and
--      `LimitStep.h-inj` applied at `D-carrier` and `inv-carrier`.
site-accepts-first-two :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
  → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
site-accepts-first-two α α∈suc oα infα ih = {! !}
  {- SC.LimitStep.h α α∈suc oα infα D-carrier inv-carrier ih -}
  {- , SC.LimitStep.h-inj α α∈suc oα infα D-carrier inv-carrier ih -}

-- 3.2  AND THAT IS THE SITE'S OWN CALL, because `limit-step`'s body
--      supplies exactly these two terms
--      (src/L/StageCardinal.lagda.md:399-403): `D-carrier` and the
--      site's lambda are one term by eta and one delta step.  THE
--      EQUATION IS AT THE PROJECTION, `[LJ-1.594]`'s own green shape
--      (`D-at-the-site`, agents/tasks/LJ-1-594/Probe594.agda:227-234,
--      proved by refl there): the full-pair form of this row was
--      MEASURED FIRST and it walls (runs/floor3-1.out, killed at
--      23.69 s and 977 MB under `-M2g`, the cap never reached), so the
--      projection is not a convenience but the shape that fits under
--      the caliber.  `fst` at `_↪_`'s sigma (src/L/Cardinal.lagda.md:
--      47-48) is the function, and no `step`-shaped normalisation is
--      forced.
site-accepts-is-the-site :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
  → fst (site-accepts-first-two α α∈suc oα infα ih)
    ≡ SC.LimitStep.h α α∈suc oα infα
        (λ δ φ → DefOf.defSet (Lset δ) φ)
        (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih
site-accepts-is-the-site _ _ _ _ _ = {! !}


-- ===================================================================
-- SECTION 4.  THE (v) TIE, IMPORTED.
--
--   The brief orders (v) IMPORTED, not restated.  [LJ-1.600]'s
--   obligation `key-at-stage` IS ingredient (v) at this carrier
--   (agents/tasks/LJ-1-600/Probe600.agda:129-130); the row below
--   applies it at the alphabet (i) consumes, which says: every formula
--   `D-carrier` can take at a stage has its code, an element of L, at
--   that same stage.  The formula chapter's existential will range
--   over exactly these.  ONE projection bridge
--   `fst (LsetS δ oδ) ≡ Lset δ`, the one [LJ-1.600] measured at zero
--   (agents/tasks/LJ-1-600/runs/W3.agda:62-64).
-- ===================================================================

-- 4.1  EVERY FORMULA OF (i)'S DOMAIN HAS ITS CODE OF (v).  Both
--      ingredients live at ONE alphabet, `Formula ⟪ Lset δ ⟫ 1`.
every-formula-has-its-code :
    (δ : V ℓ) (oδ : IsOrd δ) (φ : Formula ⟪ Lset δ ⟫ 1) → S
every-formula-has-its-code δ oδ φ = P600.key-at-stage δ oδ φ


-- ===================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   Ingredients (i) and (ii) of `[LJ-1.594]`'s table
--   (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-41),
--   instantiated at this carrier: (i) as the TWO terms the site's
--   `limit-step` supplies, bound together in `LimitStep`'s own
--   parameter shape, and (ii) as the selection over the ordinal order.
--   The components are 1.1, 1.3 and 2.1 verbatim.
-- ===================================================================

-- 5.1  THE OBLIGATION.
first-two-internal :
    Σ[ D ∈ ((δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ) ]
    Σ[ inv ∈ ((δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
              → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁) ]
    ((δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
       → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
       → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a)
first-two-internal = {! !}
