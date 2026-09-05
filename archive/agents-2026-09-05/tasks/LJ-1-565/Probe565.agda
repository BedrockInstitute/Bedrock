{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] PROBE.  StageHigh again, and what was really in the way.
-- It runs in agents/tasks/LJ-1-565/ and lands nothing in src/.
--
--   D-10, FIRST    what step [LJ-1.536] could not take, now that the
--                  door is known to be payable.  Sections 1 and 2.
--   W3, SECOND     runs/W3.agda, written and typechecked ALONE before
--                  this file existed.  Section 1 reruns its rows.
--   OBLIGATION     stage-high.  Section 6 states `StageHigh` and does
--                  NOT inhabit it.  review-of-stage-high.md states the
--                  stop.  Sections 3 to 5 pay the successor case of
--                  the induction that was standing in the way, and
--                  section 7 says what is left.
--
-- THE HEADLINE, AND IT IS A CORRECTION.  [LJ-1.536] reports that its
-- successor step "asks Agda for nothing but a conversion.  IT EXHAUSTS
-- 8 GB", and attributes the cost to two spellings of a finite
-- successor tower: "98 PERCENT OF THE COST IS `sucV`"
-- (agents/tasks/LJ-1-536/lj-1.536-report.md, `## THE WALL`).  THAT
-- DIAGNOSIS DOES NOT HOLD AT THE REAL SITE.  runs/Control565c.agda
-- makes NO stage move at all, spells the stage the SAME way on both
-- sides, and still exhausts 11.0 GB (runs/ctlc-0.time).  The cost is
-- the `isL` WITNESS, and section 4 measures it as a controlled pair.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.Probe565 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; hier-unique )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; seq; HierBelow; HierBelowAll; StageHigh; reduction
        ; IsLimit; HierBelowLimit; module Adjoin )
open import LJ-1-565.runs.W3 {ℓ} lem using ( module DoorIsFree; module Applied )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- ===================================================================
-- SECTION 1.  D-10, BEFORE ANY AGDA: THE DOOR WAS NEVER THE BLOCKER,
-- AND [LJ-1.536] NEVER STOOD AT IT.
--
-- The brief's premise is that [LJ-1.536] "STOPPED AT A DOOR THAT
-- [LJ-1.562] THEN FOUND OPEN".  Read against that task's own code the
-- premise does not hold, and the correction is worth more than the
-- premise was.
--
-- [LJ-1.536] NEVER CALLED `AtStage`.  Its adjunction goes straight
-- through `𝒟ₒ-intro` with a formula built at ⟪ Lset σ ⟫ from two
-- `∈-asFiber` indices (Probe536.agda:212-213, :293-295), and that row
-- is GREEN.  [LJ-1.562] says the same from the outside:
-- "`[LJ-1.536]` never called `AtStage`" (lj-1.562-report.md, section
-- `## AND THE CERTIFICATE IS EXACTLY THE RELABELLING …`).
--
-- AND THE DOOR ASKS FOR NEITHER HYPOTHESIS.  `carve∈𝒟ₒ`
-- (src/L/Axioms/Separation.lagda.md:198-199) takes a formula at
-- ⟪ Lset σ ⟫ and NOTHING else: no `Δ₀`, no `BoundedFo`, and no
-- restriction on its quantifiers.  The two hypotheses buy `carveSat`
-- (:163-168), the satisfaction bridge from an EXTERNAL `Formula S 1`.
-- They buy the ability to say WHICH set was carved.  They do not buy
-- the way in.
-- ===================================================================

module _ (σ : V ℓ) (oσ : IsOrd σ) where
  open DoorIsFree σ oσ using ( door-free )

  -- NO HYPOTHESIS.  Rerun from runs/W3.agda, which typechecked alone.
  rerun-door-free : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ AtStage.carve σ oσ ψ ∈ 𝒟ₒ (Lset σ) ⟩
  rerun-door-free = door-free


-- ===================================================================
-- SECTION 2.  AND `AtStage` DOES APPLY AT [LJ-1.536]'S FORMULA, WITH
-- BOTH HYPOTHESES FED.  [LJ-1.562]'S FINDING REACHES THIS SITE.
--
-- The brief names this W3 and states the stake: "If it will not apply
-- even with both hypotheses in hand, [LJ-1.562]'s finding does not
-- reach this site and you say so at once."  IT APPLIES.
-- runs/W3.agda is green on its first run, 2.15 s (runs/w3-0.time).
--
-- SO THE FINDING REACHES THE SITE AND CHANGES NOTHING THERE, because
-- section 1 is what the site actually uses.  That is the D-10 answer.
-- ===================================================================

module _ (σ : V ℓ) (oσ : IsOrd σ) where
  open Applied σ oσ using ( applied )
  open AtStage σ oσ using ( Below )

  rerun-applied : (h q : S) (hh : Below h) (hq : Below q)
                → ⟨ AtStage.carve σ oσ (Applied.lifted σ oσ h q hh hq)
                    ∈ 𝒟ₒ (Lset σ) ⟩
  rerun-applied = applied


-- ===================================================================
-- SECTION 3.  THE FIRST CURE, AND THE REFUTATION OF THE DIAGNOSIS.
--
-- [LJ-1.536] prices `refl : step 4 α ≡ step 3 (sucV α)` at 417.18 s
-- alone (runs/Control536f.agda, runs/ctlf-0.time) and concludes that
-- the successor step "is priced above the caliber"
-- (Probe536.agda:370-393).
--
-- IT IS NOT.  Prove the identity at a VARIABLE `n`: `step` is then
-- stuck at every row, `sucV` is never unfolded, and every line matches
-- syntactically.  runs/Control565a.agda is that task's own
-- Control536e.agda with ONE line changed, and it costs 0.84 s
-- (runs/ctla-0.time) against that file's 425.73 s.
--
-- A MEASURED CURE DOES NOT TRANSFER BY ANALOGY (AGENTS.md:45), SO IT
-- WAS RE-MEASURED AT ITS OWN SITE, AND THERE IT FAILED.
-- runs/Control565b.agda spends this cure at the real successor step
-- and exhausts 11.0 GB (runs/ctlb-0.time).  Section 4 is why.
-- ===================================================================

step-suc : (n : ℕ) (α : V ℓ) → step n (sucV α) ≡ sucV (step n α)
step-suc zero    α = refl
step-suc (suc n) α = cong sucV (step-suc n α)

move : (x α : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
move x α p = subst (λ w → ⟨ x ∈ Lset w ⟩) (sym (step-suc 3 α)) p


-- ===================================================================
-- SECTION 4.  WHAT ACTUALLY BLOCKED IT, AS A CONTROLLED PAIR.
--
-- FOUR FILES BRACKET IT, and every one is in runs/:
--
--   Control565d  `HierBelow` at a successor FORMED, no proof at all
--                                          exit 0, 1.93 s
--   Control565e  `hierL (sucV α) h o` compared with ITSELF, `h` and
--                `o` abstract              exit 0, 1.44 s
--   Control565c  `HierBelow (sucV α) (suc-ord oα)` against the same
--                set spelled the other way, NO stage move
--                                          HEAP WALL, 11.05 GB
--   Control565f  the same with `seq` written out locally, so the name
--                cannot be the cause       HEAP WALL, 10.94 GB
--
-- So it is not the stage spelling, not forming the type, and not
-- `hierL` at a transparent successor.  The ONE thing (e) holds
-- abstract and (c) and (f) make concrete is the `isL` WITNESS:
-- `HierBelow` computes it with `isL-ord` (Probe536.agda:135-136), and
-- `isL-ord` is `Lset→isL … (ord∈Lset-suc (sucV α) …)`, where
-- `ord∈Lset-suc` is `∈-induction` (src/L/Ordinal/Stages.lagda.md
-- :434-435) applied to a TRANSPARENT `sucV α`.
--
-- runs/Control565g.agda is (c) with that ONE variable changed back,
-- and it is exit 0 at 1.93 s (runs/ctlg-0.time).  A controlled pair
-- inside one task.
--
-- I DID NOT READ THE MECHANISM OUT OF AGDA AND I DO NOT ASSERT IT.
-- What is measured is the differential: concrete witness walls,
-- abstract witness does not.
--
-- AND THE WITNESS COSTS NOTHING TO HOLD ABSTRACT.  `hierL` is unique
-- against its own specification (src/L/Hierarchy.lagda.md:507-508), so
-- two witnesses name ONE set and the move between them is a PATH,
-- never a conversion.
-- ===================================================================

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ hγ oγ = ⟨ fst (hierL γ hγ oγ) ∈ Lset (step 3 γ) ⟩

hierL-irr : (β : V ℓ) (h₁ h₂ : ⟨ isL β ⟩) (o₁ o₂ : IsOrd β)
          → hierL β h₁ o₁ ≡ hierL β h₂ o₂
hierL-irr β h₁ h₂ o₁ o₂ =
  hier-unique β (hierL β h₁ o₁) (hierL β h₂ o₂)
    (hierL-spec β h₁ o₁) (hierL-spec β h₂ o₂)


-- ===================================================================
-- SECTION 5.  THE ROW [LJ-1.536] COULD NOT WRITE, AND ATTEMPT 1 OF
-- THIS TASK COULD NOT WRITE EITHER.
--
-- [LJ-1.536] states it in a comment and prices it above the caliber
-- (Probe536.agda:370-393).  ATTEMPT 1 OF [LJ-1.565] BUILT FOUR ROUTES
-- TO IT AND ALL FOUR WALLED (runs/attempt-1-review-of-stage-high.md
-- .preserved, `## What blocks it, measured`).  Every one of those four
-- targets `HierBelow (sucV α) (suc-ord oα)`, whose `isL` witness is
-- COMPUTED at a transparent successor.
--
-- THIS ROW TARGETS `HierBelowH` INSTEAD, and it is exit 0 at 27.37 s
-- (runs/Control565h.agda, runs/ctlh-0.time).  Both cures are spent:
-- the stage by section 3, the witness by section 4.  NEITHER ALONE IS
-- ENOUGH: runs/Control565b.agda spends the first and walls at 11.0 GB.
-- ===================================================================

successor-step : (α : V ℓ) (oα : IsOrd α)
                 (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
               → HierBelow α oα → HierBelowH (sucV α) h o
successor-step α oα h o hyp =
  subst (λ w → ⟨ fst w ∈ Lset (step 3 (sucV α)) ⟩)
        (hierL-irr (sucV α) _ h _ o)
        (move (fst (seq α oα)) α (Adjoin.seq∈ α oα hyp))


-- ===================================================================
-- SECTION 5b.  AND IT COMPOSES, WHICH IS THE HALF THAT MATTERS.
--
-- A green row in a weaker statement is worth nothing if the wall only
-- moves to where the witness must be supplied.  It does not.  The
-- witness is a redex ONLY when its argument is a transparent
-- successor; at a VARIABLE γ it is stuck, so the bridge back to
-- [LJ-1.536]'s own statement is free: 1.95 s
-- (runs/Control565w.agda, runs/ctlw-0.time).
-- ===================================================================

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
-- SECTION 6.  THE ORDINAL SPLIT.  ATTEMPT 1 BUILT THIS AND IT IS FREE.
--
-- Its file survives at runs/Control565v.agda, 1.84 s
-- (runs/ctlv-0.out), and the rows are restated here because that file
-- is a control and not a module to import from.  THE CREDIT IS
-- ATTEMPT 1'S.  `suc∈or≡` (src/L/Ordinal/Stages.lagda.md:137-139)
-- says a member's successor either stays inside the ordinal or IS it,
-- so refusing an immediate predecessor is exactly [LJ-1.519]'s
-- `IsLimit`.  ZERO NEEDS NO CASE OF ITS OWN: `IsLimit ∅` holds with
-- nothing to prove, so the limit statement already covers it.
-- ===================================================================

Succ : V ℓ → hProp (ℓ-suc ℓ)
Succ γ = ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × (sucV δ ≡ γ)) ∥₁ , PT.squash₁

not-succ→limit : (γ : V ℓ) (oγ : IsOrd γ)
               → (⟨ Succ γ ⟩ → Empty.⊥) → IsLimit γ
not-succ→limit γ oγ ¬s δ δ∈γ = Sum.rec
  (λ s∈γ → s∈γ)
  (λ s≡γ → Empty.rec (¬s ∣ δ , (δ∈γ , s≡γ) ∣₁))
  (suc∈or≡ δ γ (mem-ord {A = γ} oγ δ δ∈γ) oγ δ∈γ)


-- ===================================================================
-- SECTION 7.  THE INDUCTION, AND THE TRANSPORT THAT WALLED TWICE.
--
-- Attempt 1's `MoveAlong` carries the obligation along `sucV δ ≡ γ`,
-- and TWO independent forms of it walled at 8 GB: a `PathP` built with
-- `isProp→PathP` (runs/ctls-0.out) and the chapter's uniqueness law
-- (runs/ctlt-0.out).
--
-- HERE THERE IS NO `PathP` AND NO UNIQUENESS LAW AT THE TRANSPORT.
-- `Motive` QUANTIFIES over both witnesses, so moving it along the
-- equation is a plain `subst` on a motive that never names a computed
-- witness.  The whole induction is exit 0 at 24.34 s
-- (runs/Control565x.agda, runs/ctlx-0.time).
-- ===================================================================

HierBelowLimitH : Type (ℓ-suc ℓ)
HierBelowLimitH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ)
                → IsLimit γ → HierBelowH γ h o

closing : HierBelowLimitH → HierBelowAllH
closing lim = ∈-induction {P = Motive} go
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
    limit-case ¬s = lim γ h o (not-succ→limit γ o ¬s)


-- ===================================================================
-- SECTION 8.  THE OBLIGATION.
--
-- `StageHigh` is [LJ-1.519]'s type, carried unchanged through
-- [LJ-1.536] (Probe536.agda:350-352), IMPORTED here and not restated.
--
-- `stage-high : StageHigh` IS NOT WRITTEN BELOW AND NO POSTULATE
-- STANDS IN FOR IT.  agents/tasks/LJ-1-565/review-of-stage-high.md
-- states the stop.
--
-- WHAT IS DELIVERED INSTEAD IS THE WHOLE OF IT EXCEPT ONE STATEMENT.
-- `reduction` is [LJ-1.536]'s green route from `HierBelowAll` to
-- `StageHigh`; sections 5 to 7 pay everything between the limit case
-- and `HierBelowAll`.  So:
-- ===================================================================

stage-high-from-limit : HierBelowLimitH → StageHigh
stage-high-from-limit lim = reduction (allH→all (closing lim))


-- ===================================================================
-- SECTION 9.  THE RESIDUE, AND IT IS AN UNBOUNDED SEARCH.
--
-- `HierBelowLimitH` is the ONLY hypothesis of section 8, and it is
-- [LJ-1.536]'s `HierBelowLimit` with the witness held abstract, which
-- section 5b shows costs nothing.
--
-- AT A LIMIT γ the members of `hierL γ` are the pairs `pr c (Lset c)`
-- for c ∈ γ.  To carve that set out of a stage, the formula must say
-- "w is the tower's value at c" INSIDE the stage, and that is the
-- level formula: `Σ₁`, with the existential over an approximation
-- UNBOUNDED at the ambient level (dev/literature/devlin-II5.md:217).
-- The stage's own satisfaction is what bounds it
-- (dev/literature/devlin-II5.md:221-222, "witnessed inside the
-- carrier"), and paying that is the step nothing in src/ delivers.
-- [LJ-1.536] says the same from the other side
-- (lj-1.536-report.md, `## FOR THE NEXT BRIEF` point 2).
--
-- THE BRIEF ORDERS THE STOP HERE: "IF THE REAL BLOCKER IS AN UNBOUNDED
-- SEARCH, SAY SO AND STOP.  [LJ-1.560] is running on exactly that
-- question and this brief must not duplicate it."  So this file states
-- the residue and builds nothing against it.
--
-- AND I DO NOT OVERSTATE IT.  Attempt 1 wrote that it "did not reach
-- the limit case and it measured nothing about it".  NEITHER DID THIS
-- ATTEMPT.  What changed is that the limit case is now the ONLY thing
-- in front of `StageHigh`, which attempt 1 could not say because two
-- walls stood between.  The claim that the limit case IS [LJ-1.560]'s
-- question is an argument from the two sources above, not a
-- measurement, and section 8 does not depend on it.
-- ===================================================================

the-residue : Type (ℓ-suc ℓ)
the-residue = HierBelowLimitH

-- [LJ-1.536]'s own spelling of it, for the next brief to compare.
residue-536 : Type (ℓ-suc ℓ)
residue-536 = HierBelowLimit
