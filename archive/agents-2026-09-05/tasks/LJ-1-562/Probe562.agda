{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.562] PROBE.  `AtStage`'s SECOND hypothesis, `BoundedFo Below`.
-- It runs in agents/tasks/LJ-1-562/ and lands nothing in src/.
--
--   D-10, FIRST    which constants ACTUALLY occur in the formula
--                  [LJ-1.536] needed at `𝒟ₒ-intro`.  Section 1.
--                  MEASURED: 2.  Not 664: that is [LJ-1.514]'s count of
--                  a DIFFERENT formula (`LsetGraphAt`) and no line of
--                  this file carries it.
--   W3, SECOND     runs/W3.agda, written and typechecked ALONE before
--                  this file existed.  Section 1 reruns its two rows.
--   OBLIGATION     `constants-bounded`, section 3, at the probe's own
--                  TOP LEVEL so that it resolves from outside
--                  (scripts/pod/witness.py, and the lesson
--                  agents/tasks/LJ-1-514/lj-1.514-report.md).
--
-- THE BRIEF ORDERS ONE THING RE-MEASURED AND HERE IS THE ANSWER EARLY:
-- `Relabel` is NOT the instrument at this site and this task did not
-- use it as a cure.  [LJ-1.514] used it against the Formula CARRIER.
-- Here the certificate is what `Relabel` CONSUMES, not what it
-- produces, so the cure did not transfer and nothing was carried over
-- by analogy (AGENTS.md:45).  Section 4 spends `RL.liftFo` for one
-- purpose only: to show the certificate built here is exactly the
-- relabelling [LJ-1.536] performed by hand.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-562.Probe562 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∨̇_ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Axioms.Separation {ℓ} lem
  using ( module AtStage; Below′; mkBoundedFo )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )

-- THE PREDECESSOR'S OWN TERMS, IMPORTED AND NOT COPIED.  The audit's
-- F1/F3 rule (dev/pod/audit-2026-08-20.md) says a hypothesis taken
-- from a predecessor is the type that predecessor DELIVERED, so both
-- files below are that task's own green artefacts.
open import LJ-1-536.runs.W3 {ℓ} lem using ( adjoin; Below-adjoin )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; pr-at; HierBelow )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- ===================================================================
-- SECTION 1.  D-10, BEFORE ANY OBLIGATION: WHICH CONSTANTS OCCUR.
--
-- The brief warns that 664 is the CARRIER's count and orders the count
-- of THIS formula.  These two rows are runs/W3.agda's, rerun here so
-- that the finding and the obligation stand in one file.  Both are
-- `refl` against the tree's own recursions
-- (src/FOL/Manipulation/Parameters.lagda.md:74, :105), so neither
-- number nor name below is a reading.
--
-- MEASURED FIRST AS A MISMATCH: runs/w3-count.out reports
-- `2 != 0 of type ℕ`.  The count was obtained from Agda and not from
-- the syntax by eye, and no command containing `head` was involved.
-- ===================================================================

the-formula : (h q : S) → Formula S 1
the-formula = adjoin

count : (h q : S) → countFo (the-formula h q) ≡ 2
count h q = refl

enumerated : (h q : S) → constantsFo (the-formula h q) ≡ h ∷ q ∷ []
enumerated h q = refl


-- ===================================================================
-- SECTION 2.  THE TWO CONSTANTS OF THE ACTUAL SITE, AS `S` ELEMENTS.
--
-- [LJ-1.536] instantiates its adjunction at `σ = step 3 γ` with
-- `H = hierL γ …` and `Q = pr γ (Lset γ)`
-- (agents/tasks/LJ-1-536/Probe536.agda:300, :303, :336).  `H` is
-- already an `S`.  `Q` is a bare `V ℓ`, and the `isL` half it needs is
-- read off `pr-at` (:163-164), which is delivered unconditionally.
-- ===================================================================

o3 : (γ : V ℓ) → IsOrd γ → IsOrd (step 3 γ)
o3 γ oγ = suc-ord (suc-ord (suc-ord oγ))

hierS : (γ : V ℓ) → IsOrd γ → S
hierS γ oγ = hierL γ (isL-ord γ oγ) oγ

prS : (γ : V ℓ) (oγ : IsOrd γ) → S
prS γ oγ = pr γ (Lset γ)
         , Lset→isL (step 3 γ) (o3 γ oγ) (pr γ (Lset γ)) (pr-at γ oγ)


-- ===================================================================
-- SECTION 3.  THE OBLIGATION, AND IT CARRIES NO HYPOTHESIS.
--
-- THE BRIEF'S URGENCY IS "IF THOSE CONSTANTS CANNOT BE BOUNDED BY A
-- STAGE, THE SECOND HYPOTHESIS FAILS".  They can, and the reason is
-- not about this formula at all: `mkBoundedFo`
-- (src/L/Axioms/Separation.lagda.md:449) is a TOTAL recursion that
-- takes ANY formula over the class carrier and returns a stage
-- together with the certificate.  A constant contributes its own
-- earliest stage, a variable contributes nothing, and a branching node
-- merges the two by `bound2`.
--
-- `Below′ σ` (:415-416) and `AtStage.Below σ oσ` (:128-129) are two
-- spellings of `⟨ fst c ∈ Lset σ ⟩`.  The row below is typeable ONLY
-- because they are the same, so the obligation is stated against the
-- door's own `Below` and not against a lookalike.
-- ===================================================================

constants-bounded :
  (h q : S) → Σ[ σ ∈ V ℓ ] Σ[ oσ ∈ IsOrd σ ]
                BoundedFo (AtStage.Below σ oσ) (the-formula h q)
constants-bounded h q =
    r .fst , (r .snd .fst , r .snd .snd)
  where r = mkBoundedFo (the-formula h q)

Below-is-Below′ : (σ : V ℓ) (oσ : IsOrd σ) → AtStage.Below σ oσ ≡ Below′ σ
Below-is-Below′ σ oσ = refl


-- ===================================================================
-- SECTION 3b.  AND AT THE SITE'S OWN STAGE, WHICH IS THE REAL
-- QUESTION, THE PRICE IS NAMED.
--
-- Section 3 buys a stage of its own choosing.  [LJ-1.536] does not get
-- to choose: it carves at `step 3 γ`
-- (agents/tasks/LJ-1-536/Probe536.agda:336).  `Below-adjoin` is that
-- task's own generic row (agents/tasks/LJ-1-536/runs/W3.agda:162-163),
-- written, typechecked and then never mentioned in its report or in
-- its stop, so W2 IS ANSWERED BY NOT WRITING IT A SECOND TIME: only
-- its two hypotheses are discharged here.
--
-- THE SECOND CONSTANT IS PAID OUTRIGHT, WITH NO HYPOTHESIS AT ALL.
-- ===================================================================

constant-q-bounded : (γ : V ℓ) (oγ : IsOrd γ)
                   → AtStage.Below (step 3 γ) (o3 γ oγ) (prS γ oγ)
constant-q-bounded γ oγ = pr-at γ oγ

-- AND THE FIRST CONSTANT'S DEMAND IS, ON THE NOSE, [LJ-1.536]'S OWN
-- RECORDED RESIDUE (agents/tasks/LJ-1-536/Probe536.agda:186-187).
-- This row is `refl`, so it is an identity of TYPES and not a
-- resemblance: at this stage the second hypothesis asks for the
-- residue and it asks for nothing else.

constant-h-is-residue : (γ : V ℓ) (oγ : IsOrd γ)
                      → AtStage.Below (step 3 γ) (o3 γ oγ) (hierS γ oγ)
                        ≡ HierBelow γ oγ
constant-h-is-residue γ oγ = refl

constants-bounded-at-site :
  (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ
  → BoundedFo (AtStage.Below (step 3 γ) (o3 γ oγ))
              (the-formula (hierS γ oγ) (prS γ oγ))
constants-bounded-at-site γ oγ hyp =
  Below-adjoin (step 3 γ) (o3 γ oγ) (hierS γ oγ) (prS γ oγ)
    hyp (constant-q-bounded γ oγ)


-- ===================================================================
-- SECTION 4.  AND THE CERTIFICATE IS EXACTLY THE RELABELLING
-- [LJ-1.536] PERFORMED BY HAND.
--
-- That task did not call `AtStage`.  It built its formula straight at
-- `⟪ Lset σ ⟫` from two `∈-asFiber` indices
-- (agents/tasks/LJ-1-536/Probe536.agda:201, :207, :212-213).  `RL`'s
-- `down` is that same `∈-asFiber` (src/L/Axioms/Separation.lagda.md
-- :131-135), so the two constructions are ONE construction, and the
-- row below says so by `refl` rather than by resemblance.
--
-- P-l (dev/LESSONS.md:2357) IS WHY THIS SECTION IS AT A VARIABLE
-- STAGE.  `⟪ Lset σ ⟫` in a type at `σ = step 3 γ` is what exhausted
-- 8 GB in [LJ-1.536]'s first form (Probe536.agda:281-291).  Section 3
-- above never names `⟪ _ ⟫`, which is why it may use the concrete
-- stage; this section names it, so it may not.
-- ===================================================================

module _ (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ using ( Below; module RL )

  φ536 : ⟪ Lset σ ⟫ → ⟪ Lset σ ⟫ → Formula ⟪ Lset σ ⟫ 1
  φ536 mₕ mQ = (var zero ∈̇ con mₕ) ∨̇ (var zero ≐ con mQ)

  lift-is-536 : (h q : S) (hh : Below h) (hq : Below q)
              → RL.liftFo (the-formula h q) (Below-adjoin σ oσ h q hh hq)
                ≡ φ536 (∈-asFiber {a = fst h} {b = Lset σ} hh .fst)
                       (∈-asFiber {a = fst q} {b = Lset σ} hq .fst)
  lift-is-536 h q hh hq = refl
