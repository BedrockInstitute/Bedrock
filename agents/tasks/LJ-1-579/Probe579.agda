{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] PROBE.  StageHigh once more, in a frame that fits under
-- the cap.  It runs in agents/tasks/LJ-1-579/ and lands nothing in src/.
--
--   D-10, FIRST    the floor, measured before any other Agda.
--                  runs/W3.agda.  6.38 percent of the cap warm.
--   W3, SECOND     that same file.  The brief names the floor itself as
--                  the widest unmeasured term and it is measured.
--   OBLIGATION     stage-high.  Section 10 says it is NOT written and
--                  section 11 gives the weakest hypothesis found for
--                  it.  Sections 4 to 7 are [LJ-1.565]'s, re-measured.
--
-- THE HEADLINE, AND IT IS A CORRECTION TO THE BRIEF.  The brief says
-- "[LJ-1.565] left a park and no report.  Do not be the fourth."  That
-- task left BOTH, in its own worktree, at
-- ../LJ-1-565/agents/tasks/LJ-1-565/lj-1.565-report.md and
-- ../LJ-1-565/agents/tasks/LJ-1-565/review-of-stage-high.md.  Its
-- verdict is NO-GO with ONE open statement, and section 2 says what
-- that changes here.
--
-- THE SECOND HEADLINE IS SECTION 3 AND IT IS THE FINDING OF THIS TASK.
-- `StageHigh` is not an EXISTENCE.  The tree already puts `hierL γ` in
-- a stage for free, with no hypothesis and no induction.  The whole of
-- the obligation is an ORDINAL BOUND on that stage.  So every route
-- that delivers "some stage", and [LJ-1.560]'s reflection is exactly
-- such a route, is worth zero lines at this site.  Section 8 spends
-- [LJ-1.560]'s term anyway, because the brief ordered it tried.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-579.Probe579 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Relativize using ( relativize )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isPropIsOrd; Lset; 𝒟ₒ; Lset-mono )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; Recorded )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; LsetS )
open import L.Reflect {ℓ} lem using ( Below )
open import L.ReflectFo {ℓ} lem using ( mkReflect )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; seq; HierBelow; HierBelowAll; StageHigh; reduction
        ; IsLimit; Door; door; pr-at; module Adjoin )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )


-- ===================================================================
-- SECTION 1.  THE FLOOR, WHICH IS ALSO W3.
--
-- The brief: "D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.  Write the
-- smallest import set under which `stage-high` can be STATED, and
-- record its typecheck time and peak RSS on an empty body."
--
-- runs/W3.agda, 44 lines, three imports, exit 0 on its FIRST run.
--   cold, [LJ-1.536] and [LJ-1.520] rebuilt: 13.03 s, 733,331,456 B,
--                                            8.54 percent of the cap
--   warm:                              1.94 s, 547,700,736 B,
--                                            6.38 percent of the cap
--
-- A HOLE IS NOT AVAILABLE UNDER `--safe` and the flag was not dropped
-- to buy one, because a number measured under a different flag set is
-- not comparable with this probe's.  The floor is the obligation's
-- TYPE, FORMED, which is what an empty body costs.
--
-- THE FRAME IS NOT THE OBSTACLE.  Over nine tenths of the cap is left.
-- ===================================================================

Obligation : Type (ℓ-suc ℓ)
Obligation = StageHigh


-- ===================================================================
-- SECTION 2.  THE BRIEF'S PREMISE 1, CHECKED.
--
-- Premise 1 reads "[LJ-1.565] parked at the heap wall.  Basis:
-- dev/pod/transitions/2026-08.jsonl:3169".  That file has 157 lines,
-- so the citation resolves to nothing.  The task itself is in a
-- sibling worktree and it left a full report and a full stop.
--
-- WHAT IT DELIVERED, AND THIS TASK DOES NOT INHERIT IT AS A TERM:
-- its directory is untracked in its own worktree, so nothing in it is
-- importable from here.  Sections 4 to 6 REBUILD its chain rather than
-- cite it, and every number below is measured on this pane.
-- ===================================================================


-- ===================================================================
-- SECTION 3.  THE FINDING.  THE OBLIGATION IS A BOUND, NOT AN
-- EXISTENCE, AND EXISTENCE IS ALREADY FREE.
--
-- `hierL γ` is an element of `S`, so it carries `isL`, and `stage`
-- (src/L/Stage.lagda.md:180-193) turns that into the LEAST stage that
-- holds it, with the membership and the minimality both projected out.
-- No hypothesis, no induction, no limit case, and no reflection.
--
-- runs/Control579a.agda is these three rows alone: exit 0 on the FIRST
-- run, 2.23 s, 612,286,464 B (runs/ctla-0.time).
--
-- SO WHAT `StageHigh` ASKS FOR IS AN ORDINAL INEQUALITY, and rows 2
-- and 3 pin it from both sides.
-- ===================================================================

private
  hset : (γ : V ℓ) → IsOrd γ → V ℓ
  hset γ oγ = fst (hierL γ (isL-ord γ oγ) oγ)

  hL : (γ : V ℓ) (oγ : IsOrd γ) → ⟨ isL (hset γ oγ) ⟩
  hL γ oγ = snd (hierL γ (isL-ord γ oγ) oγ)

  hstage : (γ : V ℓ) → IsOrd γ → V ℓ
  hstage γ oγ = stage (hset γ oγ) (hL γ oγ)

-- ROW 1.  EXISTENCE IS FREE.
hier-somewhere : (γ : V ℓ) (oγ : IsOrd γ)
               → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ hset γ oγ ∈ Lset σ ⟩)
hier-somewhere γ oγ =
  hstage γ oγ , (stage-ord (hset γ oγ) (hL γ oγ)
                , stage-mem (hset γ oγ) (hL γ oγ))

-- ROW 2.  THE BOUND BUYS THE OBLIGATION.
bound→hier : (γ : V ℓ) (oγ : IsOrd γ)
           → ⟨ hstage γ oγ ∈ step 3 γ ⟩ → HierBelow γ oγ
bound→hier γ oγ lt = Lset-mono lt (stage-mem (hset γ oγ) (hL γ oγ))

-- ROW 3.  AND THE OBLIGATION IS THE BOUND: nothing below can hold it.
hier→bound : (γ : V ℓ) (oγ : IsOrd γ) → IsOrd (step 3 γ)
           → HierBelow γ oγ → ⟨ step 3 γ ∈ hstage γ oγ ⟩ → Empty.⊥
hier→bound γ oγ o3 = stage-earliest (hset γ oγ) (hL γ oγ) (step 3 γ) o3


-- ===================================================================
-- SECTION 4.  [LJ-1.565]'S TWO CURES, REBUILT HERE.
--
-- A MEASURED CURE DOES NOT TRANSFER BY ANALOGY (AGENTS.md:45), and
-- these were measured in another worktree, so they are re-measured
-- here at their own site.  The CREDIT IS [LJ-1.565]'S, and the design
-- is that task's:
--
--   the stage    prove `step n (sucV α) ≡ sucV (step n α)` at a
--                VARIABLE n, so `step` is stuck at every row and
--                `sucV` is never unfolded
--                (../LJ-1-565/agents/tasks/LJ-1-565/Probe565.agda
--                :140-146)
--   the witness  hold the `isL` argument of `hierL` ABSTRACT, so the
--                `∈-induction` inside `ord∈Lset-suc` is never applied
--                to a transparent successor (:185-193)
-- ===================================================================

step-suc : (n : ℕ) (α : V ℓ) → step n (sucV α) ≡ sucV (step n α)
step-suc zero    α = refl
step-suc (suc n) α = cong sucV (step-suc n α)

move : (x α : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
move x α p = subst (λ w → ⟨ x ∈ Lset w ⟩) (sym (step-suc 3 α)) p

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ h o = ⟨ fst (hierL γ h o) ∈ Lset (step 3 γ) ⟩

-- `hierL` is unique against its own specification
-- (src/L/Hierarchy.lagda.md:507-508), so two witnesses name ONE set
-- and the move between them is a PATH and never a conversion.
hierL-irr : (β : V ℓ) (h₁ h₂ : ⟨ isL β ⟩) (o₁ o₂ : IsOrd β)
          → hierL β h₁ o₁ ≡ hierL β h₂ o₂
hierL-irr β h₁ h₂ o₁ o₂ i =
  hierL β (snd (isL β) h₁ h₂ i) (isPropIsOrd β o₁ o₂ i)


-- ===================================================================
-- SECTION 5.  THE SUCCESSOR STEP, AND THE BRIDGE BACK.
-- ===================================================================

successor-step : (α : V ℓ) (oα : IsOrd α)
                 (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
               → HierBelow α oα → HierBelowH (sucV α) h o
successor-step α oα h o hyp =
  subst (λ w → ⟨ fst w ∈ Lset (step 3 (sucV α)) ⟩)
        (hierL-irr (sucV α) _ h _ o)
        (move (fst (seq α oα)) α (Adjoin.seq∈ α oα hyp))

bridge : (γ : V ℓ) (oγ : IsOrd γ) → HierBelowH γ (isL-ord γ oγ) oγ
       → HierBelow γ oγ
bridge γ oγ x = x

Motive : V ℓ → Type (ℓ-suc ℓ)
Motive γ = (h : ⟨ isL γ ⟩) (o : IsOrd γ) → HierBelowH γ h o

HierBelowAllH : Type (ℓ-suc ℓ)
HierBelowAllH = (γ : V ℓ) → Motive γ

allH→all : HierBelowAllH → HierBelowAll
allH→all f γ oγ = bridge γ oγ (f γ (isL-ord γ oγ) oγ)


-- ===================================================================
-- SECTION 6.  THE ORDINAL SPLIT AND THE INDUCTION.
-- ===================================================================

Succ : V ℓ → hProp (ℓ-suc ℓ)
Succ γ = ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × (sucV δ ≡ γ)) ∥₁ , PT.squash₁

not-succ→limit : (γ : V ℓ) (oγ : IsOrd γ)
               → (⟨ Succ γ ⟩ → Empty.⊥) → IsLimit γ
not-succ→limit γ oγ ¬s δ δ∈γ = Sum.rec
  (λ s∈γ → s∈γ)
  (λ s≡γ → Empty.rec (¬s ∣ δ , (δ∈γ , s≡γ) ∣₁))
  (suc∈or≡ δ γ (mem-ord {A = γ} oγ δ δ∈γ) oγ δ∈γ)

HierBelowLimitH : Type (ℓ-suc ℓ)
HierBelowLimitH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ)
                → IsLimit γ → HierBelowH γ h o

-- THE LIMIT CASE IS GIVEN THE INDUCTION HYPOTHESIS.  [LJ-1.565]'s
-- `closing` discards it (../LJ-1-565/agents/tasks/LJ-1-565/Probe565
-- .agda:307-308) and its residue is therefore stronger than the proof
-- needs.  `dev/literature/devlin-II5.md:218-222` says which form the
-- source actually uses: at a limit α the level function is uniformly
-- Δ₁ FOR γ < α, and "the forward half needs the witnessing z to live
-- inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
-- γ < α".  THAT IS THE INDUCTION HYPOTHESIS, VERBATIM.
HierBelowLimitIH : Type (ℓ-suc ℓ)
HierBelowLimitIH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
                 → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → Motive δ)
                 → HierBelowH γ h o

closingIH : HierBelowLimitIH → HierBelowAllH
closingIH lim = ∈-induction {P = Motive} go
  where
  go : (γ : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → Motive δ) → Motive γ
  go γ IH h o = Sum.rec succ-case limit-case (lem (Succ γ))
    where
    succ-case : ⟨ Succ γ ⟩ → HierBelowH γ h o
    succ-case = PT.rec (snd (fst (hierL γ h o) ∈ Lset (step 3 γ))) pick
      where
      pick : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × (sucV δ ≡ γ)) → HierBelowH γ h o
      pick (δ , (δ∈γ , p)) = subst Motive p
        (λ h' o' → successor-step δ oδ h' o'
                     (bridge δ oδ (IH δ δ∈γ (isL-ord δ oδ) oδ)))
        h o
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = γ} o δ δ∈γ

    limit-case : (⟨ Succ γ ⟩ → Empty.⊥) → HierBelowH γ h o
    limit-case ¬s = lim γ h o (not-succ→limit γ o ¬s) IH

-- ONE INDUCTION, NOT TWO.  [LJ-1.565]'s form is this one with the
-- hypothesis thrown away, so nothing it proved is lost.
closing : HierBelowLimitH → HierBelowAllH
closing lim = closingIH (λ γ h o l _ → lim γ h o l)


-- ===================================================================
-- SECTION 7.  [LJ-1.565]'S RESULT, REBUILT AND RE-MEASURED HERE.
-- ===================================================================

stage-high-from-limit : HierBelowLimitH → StageHigh
stage-high-from-limit lim = reduction (allH→all (closing lim))


-- ===================================================================
-- SECTION 8.  THE BRIEF ORDERED [LJ-1.560]'S TERM TRIED HERE, AND IT
-- IS TRIED.  "[LJ-1.560] is GO and its reflection step was an
-- instantiation of something already in the tree.  Try it here: nobody
-- has."
--
-- IT INSTANTIATES.  `mkReflect` (src/L/ReflectFo.lagda.md:525) takes
-- [LJ-1.520]'s level formula, Σ₁ and thirteen unbounded existentials
-- (agents/tasks/LJ-1-520/Probe520.agda:162-169), with NO grade
-- hypothesis, and returns a stage where it agrees with its
-- relativization.  runs/Control579b.agda is this row alone: exit 0,
-- 168.23 s, 1,494,056,960 B, 17.4 percent of the cap
-- (runs/ctlb-1.time).  NOBODY HAD PRICED IT.
--
-- AND IT DOES NOT REACH THE OBLIGATION, FOR A REASON THE TYPE STATES.
-- Its certificate is `⟨ γ ∈ β ⟩`: the stage it names is ABOVE the
-- ordinal the caller hands it.  Section 3 measured that the obligation
-- is a BOUND on `stage (hierL γ)`, and section 3's row 1 already puts
-- that set in a stage for free.  So a route whose whole output is
-- "some stage, above γ" adds nothing that row 1 did not already have.
-- ===================================================================

level-reflected :
    {n : ℕ} (w b : Fin n) (γ : V ℓ) (oγ : IsOrd γ)
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ( ⟨ γ ∈ β ⟩
      × ((ρ : S ^ n) → Below β ρ
         → (ρ ⊨ fst (levelFo-Σ₁ w b))
           ≡ (ρ ⊨ relativize (LsetS β oβ) (fst (levelFo-Σ₁ w b)))) )
level-reflected w b γ oγ = mkReflect (fst (levelFo-Σ₁ w b)) γ oγ

-- WHAT THE LIMIT CASE NEEDS IS THE SAME SENTENCE AT `γ` ITSELF, WITH
-- NO NEW ORDINAL.  STATED AND NOT INHABITED.  It is not a weakening of
-- the row above; it is a different statement, and `mkReflect` cannot
-- be asked for it.
LevelAtGamma : Type (ℓ-suc (ℓ-suc ℓ))
LevelAtGamma = {n : ℕ} (w b : Fin n) (γ : V ℓ) (oγ : IsOrd γ)
             → (ρ : S ^ n) → Below γ ρ
             → (ρ ⊨ fst (levelFo-Σ₁ w b))
               ≡ (ρ ⊨ relativize (LsetS γ oγ) (fst (levelFo-Σ₁ w b)))


-- ===================================================================
-- SECTION 9.  AND HERE IS WHAT THE ONE OPEN STATEMENT REALLY COSTS.
--
-- TWO ROWS, BOTH GREEN, AND TOGETHER THEY REPLACE `HierBelowLimitH`
-- BY A DEFINABILITY STATEMENT AT A STAGE THE SET IS ALREADY INSIDE.
--
--   9a  AT A LIMIT THE TABLE IS A SUBSET OF THE STAGE.  Every member
--       is `pr c (Lset c)` for c ∈ γ (src/L/Hierarchy.lagda.md
--       :497-502), that pair lies in `Lset (step 3 c)`
--       (agents/tasks/LJ-1-536/Probe536.agda:163-164), and a limit is
--       closed under the successor three times over.
--       runs/Control579d.agda alone: exit 0 on its FIRST run, 12.78 s
--       (runs/ctld-0.time).
--
--   9b  AND DEFINABILITY OVER THAT STAGE PAYS THE WHOLE CASE, TWO
--       STAGES UNDER BUDGET.  The door is `𝒟ₒ-intro` and it asks for
--       a formula at ⟪ Lset γ ⟫ and NOTHING else, which is
--       [LJ-1.565]'s `door-free` finding.  The result lands at
--       `sucV γ` and the obligation allows `step 3 γ`.
--       runs/Control579c.agda alone: exit 0, 12.61 s
--       (runs/ctlc-1.time).
--
-- SO DEVLIN'S THREE IS SLACK AT THE LIMIT.  The limit case does not
-- need to find a bound.  IT NEEDS A FORMULA.
-- ===================================================================

-- 9a.
hier-sub : (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
         → (z : V ℓ) → ⟨ z ∈ fst (hierL γ h o) ⟩ → ⟨ z ∈ Lset γ ⟩
hier-sub γ h o lim z z∈ = PT.rec (snd (z ∈ Lset γ)) use rec
  where
  zS : S
  zS = z , isL-trans {x = fst (hierL γ h o)} {y = z} z∈ (snd (hierL γ h o))

  rec : ⟨ Recorded γ z ⟩
  rec = subst ⟨_⟩ (hierL-spec γ h o zS) z∈

  use : Σ[ c ∈ S ] (⟨ fst c ∈ γ ⟩ × (z ≡ pr (fst c) (Lset (fst c))))
      → ⟨ z ∈ Lset γ ⟩
  use (c , (c∈γ , eq)) =
    subst (λ w → ⟨ w ∈ Lset γ ⟩) (sym eq)
      (Lset-mono step3∈γ (pr-at (fst c) oc))
    where
    oc : IsOrd (fst c)
    oc = mem-ord {A = γ} o (fst c) c∈γ
    step3∈γ : ⟨ step 3 (fst c) ∈ γ ⟩
    step3∈γ = lim _ (lim _ (lim _ c∈γ))

-- 9b.
LimitDefinable : Type (ℓ-suc ℓ)
LimitDefinable = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
               → Door (Lset γ) (fst (hierL γ h o))

suc∈step3 : (γ : V ℓ) → ⟨ sucV γ ∈ step 3 γ ⟩
suc∈step3 γ = ∈sucV-inl {A = sucV (sucV γ)} {x = sucV γ}
                (self∈sucV (sucV γ))

definable→limit : LimitDefinable → HierBelowLimitH
definable→limit d γ h o lim = Lset-mono (suc∈step3 γ) in-suc
  where
  x : V ℓ
  x = fst (hierL γ h o)
  in-𝒟 : ⟨ x ∈ 𝒟ₒ (Lset γ) ⟩
  in-𝒟 = door (Lset γ) x (d γ h o lim)
  in-suc : ⟨ x ∈ Lset (sucV γ) ⟩
  in-suc = subst (λ w → ⟨ x ∈ w ⟩) (sym (Lset-suc γ)) in-𝒟


-- ===================================================================
-- SECTION 10.  THE OBLIGATION.
--
-- `stage-high : StageHigh` IS NOT WRITTEN BELOW AND NO POSTULATE
-- STANDS IN FOR IT.  agents/tasks/LJ-1-579/review-of-stage-high.md
-- states the stop.
--
-- WHAT IS DELIVERED IS THE OBLIGATION FROM ONE STATEMENT, AND THAT
-- STATEMENT IS STRICTLY WEAKER THAN THE ONE [LJ-1.565] LEFT.
-- ===================================================================

stage-high-from-definable : LimitDefinable → StageHigh
stage-high-from-definable d = stage-high-from-limit (definable→limit d)


-- ===================================================================
-- SECTION 11.  AND THE SAME STATEMENT WITH THE INDUCTION HYPOTHESIS,
-- WHICH IS THE FORM THE SOURCE'S PROOF ACTUALLY USES.
--
-- `dev/literature/devlin-II5.md:218-222` gives the limit case its
-- hypothesis: at a limit the level function is uniformly Δ₁ FOR
-- γ < α, and the forward half wants the witness inside L_α, "that is
-- 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for γ < α".  So the
-- formula the limit stage needs may USE the tables below it.
--
-- `LimitDefinableIH` is strictly weaker than `LimitDefinable` and
-- `stage-high-from-definable-ih` is the obligation from it.
-- ===================================================================

LimitDefinableIH : Type (ℓ-suc ℓ)
LimitDefinableIH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
                 → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → Motive δ)
                 → Door (Lset γ) (fst (hierL γ h o))

definable→limit-ih : LimitDefinableIH → HierBelowLimitIH
definable→limit-ih d γ h o lim IH = Lset-mono (suc∈step3 γ) in-suc
  where
  x : V ℓ
  x = fst (hierL γ h o)
  in-𝒟 : ⟨ x ∈ 𝒟ₒ (Lset γ) ⟩
  in-𝒟 = door (Lset γ) x (d γ h o lim IH)
  in-suc : ⟨ x ∈ Lset (sucV γ) ⟩
  in-suc = subst (λ w → ⟨ x ∈ w ⟩) (sym (Lset-suc γ)) in-𝒟

stage-high-from-definable-ih : LimitDefinableIH → StageHigh
stage-high-from-definable-ih d =
  reduction (allH→all (closingIH (definable→limit-ih d)))

-- AND NOTHING IS LOST GOING TO THE WEAKER STATEMENT.
weaken : LimitDefinable → LimitDefinableIH
weaken d γ h o lim _ = d γ h o lim
