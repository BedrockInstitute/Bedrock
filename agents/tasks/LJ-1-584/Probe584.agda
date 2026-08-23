{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.584]  THE FORMULA FOR THE STAGE-CARDINALITY BOUND.
--
-- VERDICT: NO-GO.  `agents/tasks/LJ-1-584/review-of-stage-bound-definable.md`
-- states it.  THE OBLIGATION IS NOT IN THIS FILE and no weaker term is
-- offered as one.  This file carries NO hole and NO postulate, so every
-- reduction in it is a measurement and not a claim.  Nothing lands in
-- `src/`.
--
-- W3 IS agents/tasks/LJ-1-584/runs/W3a.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3a-1.out`, GREEN, 1.22 s).  It is IMPORTED
-- below, not restated.  Its sibling `runs/W3b.agda` is the row that does
-- NOT terminate; section 1.3 records what that measured.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA.  The obligation is NOT
--               refutable and NOT vacuous, and both are typechecked.
--   Section 1.  W3, IMPORTED.  What `step` is, and the one term its
--               value is computed from.
--   Section 2.  THE BLOCK.  EVERY VALUE OF THE INJECTION IS A VALUE OF
--               THE MODULE'S AMBIENT PAIRING PARAMETER `sq`.
--   Section 3.  WHAT THE OBLIGATION WOULD BUY, AND WHAT THE REOPENER
--               ACTUALLY ASKS FOR.  THE TWO ARE NOT THE SAME TYPE.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-584.Probe584 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.GCH {ℓ} lem using ( InjL )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- THE PREDECESSORS THIS FILE STANDS ON.  Each is GO and each probe is
-- green and carries no hole, so every type below is IMPORTED from the
-- file that typechecked and none is transcribed.
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568

-- W3, MINE, IMPORTED RATHER THAN RESTATED.
import LJ-1-584.runs.W3a {ℓ} lem α₀ oα₀ sq as W3


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA.
--
--   THE FLOOR IS THE REPORT'S `## THE FLOOR` and it was measured
--   first: `runs/floor-cold-1.out` and `runs/floor-warm-1.out`, the
--   obligation's type with a hole in the smallest import set that
--   holds it.
--
--   THE QUESTION D-10 ASKS IS WHETHER THE TARGET IS TRUE.  Two rows
--   below answer it, and neither is a reading.
-- ===================================================================

-- 0.1  THE OBLIGATION'S TYPE, NAMED ONCE.  `Def` is [LJ-1.568]'s
--      (agents/tasks/LJ-1-568/Probe568.agda:189-190), IMPORTED.  `a` is
--      the stage as an L-set, `b` is the ordinal as an L-set, and `g`
--      is the ambient bound (src/L/StageCardinal.lagda.md:564-566).
Obligation : (α : V ℓ) (oα : IsOrd α) → ⟨ α ∈ˢ sucV α₀ ⟩
           → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Type (ℓ-suc ℓ)
Obligation α oα α∈suc α∉ω =
  P568.Def (LsetS α oα) (P568.ordS α oα)
    (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω))

-- 0.2  THE OBLIGATION IS NOT REFUTABLE HERE, AND THE REASON IS A ROW
--      THAT TYPECHECKS.  `V = L` GIVES IT OUTRIGHT AND UNTRUNCATED.
--      Both halves are imported: [LJ-1.561]'s `ambient-graph-isL`
--      (Probe561.agda:171-176) says the graph is ALREADY an ambient
--      set, so `V = L` puts it in L; [LJ-1.568]'s `graph→def`
--      (Probe568.agda:368-374) reads a graph in L back as a formula.
--      NOTHING IS TRUNCATED ON THIS PATH.
vl→obligation : ((x : V ℓ) → ⟨ isL x ⟩)
              → (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
                (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → Obligation α oα α∈suc α∉ω
vl→obligation vl α oα α∈suc α∉ω =
  P568.graph→def a b g (P561.ambient-graph-isL a b g (vl _))
  where
  a b : S
  a = LsetS α oα
  b = P568.ordS α oα
  g : ⟪ fst a ⟫ → ⟪ fst b ⟫
  g = fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω)

-- 0.3  SO A REFUTATION OF THE OBLIGATION IS A REFUTATION OF `V = L`.
--      That is 0.2 contraposed and nothing more.  The tree is the study
--      of what holds INSIDE L and carries no non-constructible set.
--      **THIS FILE THEREFORE DOES NOT CLAIM THE OBLIGATION IS FALSE.**
--      It measures that the module cannot build it.
refuting-obligation-refutes-V=L :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (Obligation α oα α∈suc α∉ω → Empty.⊥)
  → ((x : V ℓ) → ⟨ isL x ⟩) → Empty.⊥
refuting-obligation-refutes-V=L α oα α∈suc α∉ω no vl =
  no (vl→obligation vl α oα α∈suc α∉ω)


-- ===================================================================
-- SECTION 1.  W3, IMPORTED.
--
--   The brief: "Write it FIRST and typecheck it ALONE.  If `step`
--   cannot be described by a formula, neither can the injection."
-- ===================================================================

-- 1.1  `step`, RE-ASCRIBED ALONE.  W3's own row, imported.
step : (α : SV.S) → ((δ : SV.S) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) → SC.Upper.P α
step = W3.step

-- 1.2  AND THE MODULE'S PAIRING IS `sq` APPLIED, AND NOTHING ELSE.
--      W3's own row, imported; it is `refl` there.
pair-is-sq :
    (α : SV.S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) (x y : ⟪ α ⟫)
  → SC.Bound.pair α oα infα (sq α α∈suc infα) x y
    ≡ fst (sq α α∈suc infα) (x , y)
pair-is-sq = W3.pair-is-sq

-- 1.3  WHAT DOES **NOT** TYPECHECK, AND IT IS A MEASUREMENT.
--      `runs/W3b.agda` is one row: `step α IH oα α∈suc infα` against
--      `limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)` by
--      `refl`, which is src/L/StageCardinal.lagda.md:562 read back.
--      IT DOES NOT TERMINATE.  `runs/w3b-1.out` is a 180 s bound that
--      the run did not reach the end of, at 98.8% CPU with the resident
--      set pinned: a conversion loop and NOT a heap event.  So NO ROW OF
--      THIS FILE PUTS `step` INTO A CONVERSION PROBLEM.  Section 2
--      measures `limit-step` instead, which is the same value at every
--      stage the induction visits and costs 1.22 s.


-- ===================================================================
-- SECTION 2.  THE BLOCK, MEASURED.
--
--   EVERY VALUE OF THE INJECTION IS A VALUE OF THE MODULE'S AMBIENT
--   PAIRING PARAMETER.  This is the row the whole verdict rests on, and
--   it is a theorem and not a reading of the source.
--
--   `limit-step` (src/L/StageCardinal.lagda.md:396-403) is the body of
--   every stage `step` visits (`:562`), so a statement about it is a
--   statement about the injection at every α the induction reaches.
-- ===================================================================

-- 2.1  THE TWO ARGUMENTS `limit-step` SUPPLIES TO `LimitStep`, named
--      once so section 2.2 can mention `cnt`.  Copied from
--      src/L/StageCardinal.lagda.md:400-403 and checked by use: if
--      either drifted, 2.2 would not typecheck.
Dfn : (δ : SV.S) → Formula ⟪ Lset δ ⟫ 1 → SV.S
Dfn δ φ = DefOf.defSet (Lset δ) φ

Inv : (δ : SV.S) (y : SV.S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
    → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (Dfn δ φ₀ ≡ y) ∥₁
Inv δ y h = 𝒟ₒ-inv (Lset δ) y h

-- 2.2  THE THEOREM.  For every stage α and every inductive input `ih`,
--      the value of the injection at `x` is a value of
--      `fst (sq α α∈suc infα)`, the module's TWELFTH-LINE PARAMETER
--      (src/L/StageCardinal.lagda.md:17-19).
--
--      The proof is one projection: `leastOf` returns the least element
--      TOGETHER WITH the predicate at it (src/L/WellOrder/Base.lagda.md
--      :158-160), and the predicate IS `class-pred`
--      (src/L/StageCardinal.lagda.md:319-324), whose only occurrence of
--      the value is `B.pair m (cnt m φ) ≡ y`.
value-is-a-sq-value :
    (α : SV.S) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ SC.↪ ⟪ α ⟫)
    (x : ⟪ Lset α ⟫)
  → ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 ]
        ( (Dfn (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x)
        × ( fst (sq α α∈suc infα)
              (m , SC.LimitStep.cnt α α∈suc oα infα Dfn Inv ih m φ)
            ≡ fst (SC.limit-step α α∈suc oα infα ih) x ) ) ∥₁
value-is-a-sq-value α α∈suc oα infα ih x =
  fst (snd (leastOf (SC.OrdSWO.ordSWO α oα) lem
             (SC.LimitStep.class-pred α α∈suc oα infα Dfn Inv ih x)
             (SC.LimitStep.nonempty α α∈suc oα infα Dfn Inv ih x)))


-- ===================================================================
-- SECTION 3.  WHAT THE OBLIGATION WOULD BUY, AND WHAT THE REOPENER
--             ACTUALLY ASKS FOR.  THE TWO ARE NOT THE SAME TYPE.
--
--   THIS IS THE FINDING THE NEXT BRIEF NEEDS.  [LJ-1.580]'s reopener
--   (agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:117) is
--   an internal stage bound.  The brief turned that into `Def` AT ONE
--   NAMED `g`.  Those are different demands and the difference is
--   visible in the two type signatures below.
-- ===================================================================

-- 3.1  THE OBLIGATION IS SUFFICIENT, and this is [LJ-1.568]'s theorem
--      at this pair and not a new one.  `def-restricted`
--      (Probe568.agda:252-253) is IMPORTED.
obligation→graph :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → Obligation α oα α∈suc α∉ω
  → ∥ Σ[ G ∈ S ] P561.IsGraph (LsetS α oα) (P568.ordS α oα)
                   (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω)) G ∥₁
obligation→graph α oα α∈suc α∉ω =
  P568.def-restricted (LsetS α oα) (P568.ordS α oα)
    (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω))
    (snd (SC.Upper.stage-card-upper α oα α∈suc α∉ω))

-- 3.2  AND THE REOPENER'S OWN TARGET.  `InjL` is src/L/GCH.lagda.md:38,
--      `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`.
--
--      **READ THE TWO SIGNATURES AGAINST EACH OTHER.**  `Obligation`
--      (0.1) takes `α∈suc` and `α∉ω` because it must NAME
--      `stage-card-upper`, and `stage-card-upper` is computed from
--      `sq α α∈suc α∉ω` (section 2).  `Reopener` takes neither.  It
--      names no injection, so it constrains no injection, and IT IS A
--      TRUNCATION: any coded injection pays it.
Reopener : (α : V ℓ) → IsOrd α → Type (ℓ-suc ℓ)
Reopener α oα = InjL (LsetS α oα) (P568.ordS α oα)

-- 3.3  SO THE TRUNCATION IS NOT A LOSS AT THIS SITE.  [LJ-1.568]'s
--      `def∥-restricted` (Probe568.agda:261-262) pays the same
--      conclusion from the TRUNCATED hypothesis, and 3.2's target is
--      itself a truncation.  A next brief that asks for `Def`
--      UNTRUNCATED at one named `g` is therefore asking for strictly
--      more than the reopener can spend.
obligation∥→graph :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Obligation α oα α∈suc α∉ω ∥₁
  → ∥ Σ[ G ∈ S ] P561.IsGraph (LsetS α oα) (P568.ordS α oα)
                   (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω)) G ∥₁
obligation∥→graph α oα α∈suc α∉ω =
  P568.def∥-restricted (LsetS α oα) (P568.ordS α oα)
    (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω))
    (snd (SC.Upper.stage-card-upper α oα α∈suc α∉ω))


-- ===================================================================
-- SECTION 4.  THE VERDICT.
--
--   NO TERM OF `Obligation` IS OFFERED, AND NOTHING ABOVE IS OFFERED AS
--   ONE.  `vl→obligation` (0.2) carries `V = L` to the left of its
--   arrow, which the obligation does not have.
--
--   THE REASON IS SECTION 2 AND IT IS ONE SENTENCE.  Every value of the
--   injection is a value of `fst (sq α α∈suc infα)`; `sq` is a module
--   parameter of `L.StageCardinal` (src/L/StageCardinal.lagda.md:17-19)
--   carrying injectivity and nothing else; and by [LJ-1.568]'s
--   `graph→def` and `def-restricted` the obligation is EQUIVALENT to
--   putting the graph of that function into L
--   (`def∥↔conclusion`, Probe568.agda:387-393).  A formula for this `g`
--   is therefore a code for an arbitrary ambient function, which is
--   [LJ-1.533]'s wall.
--
--   `agents/tasks/LJ-1-584/review-of-stage-bound-definable.md` states
--   the NO-GO and what would reopen it.
-- ===================================================================
