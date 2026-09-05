# Review of `bound-in-tower`: NOT INHABITED

**Verdict: NO-GO.** The obligation
`agents/tasks/LJ-1-711/Probe711.agda::bound-in-tower`, the placement row
`fst (bound-of γ oγ hγ) ∈ˢ step 3 γ` at [LJ-1.698]'s frame
(`agents/tasks/LJ-1-698/Probe698.agda:97-101`, type restated
`agents/tasks/LJ-1-706/Probe706.agda:65-67`), is not inhabited by this
dispatch. The statement is priced FALSE at the named target under D-10 below;
no term of its negation is built. The green probe lives beside this file and
typechecks (`agents/tasks/LJ-1-711/runs/p-final.out`, EXIT=0).

## What was asked and what closed

One term: place `mkBoundedFo`'s bounding stage inside the tower at
`step 3 γ`. Delivered instead:

- the obligation TYPE, verbatim (`Probe711.agda:66-68`);
- the supply type of `[LJ-1.710]`, imported and named, never inhabited,
  per the coder clause governing a predecessor NO-GO
  (`agents/tasks/LJ-1-710/lj-1.710-report.md:5-8`) (`Probe711.agda:81-86`);
- green ceiling planks any corrected shape reuses:
  `raise1`/`raise2`/`raise3` via `Lset-mono ∘ self∈sucV`
  (`src/L/Constructible.lagda.md:365`,
  `src/V/Model.lagda.md:236-237`) (`Probe711.agda:99-113`);
- the leaf certificate constants contribute, quoted from src
  (`src/L/Axioms/Separation.lagda.md:431-433`,
  `src/L/Stage.lagda.md:188-189`) (`Probe711.agda:119-120`);

## Why the funded supply cannot pay this row

Premise 5 funds merge interiority at LIMITS (`bound2-in-limit`). Every
ceiling on this route is a successor stage: `step k γ = sucV (step (k-1) γ)`
(`agents/tasks/LJ-1-693/Probe693.agda:82-84`). A limit's union-closure clause
is typed over arbitrary families at ONE stage `α`
(`agents/tasks/LJ-1-710/Probe710.agda:38-44`); it never instances against a
successor ceiling, whatever funding it receives. The wall is also re-measured
at this site for the Boundary's no-transfer rule:
`agents/tasks/LJ-1-711/runs/p-attempt.out`, exit 42, `[UnequalTerms]` with
bound2's internal where-bound family printed in the mismatch, 0.81 s, 278 MB.

## D-10: the target's truth

The member-slack analysis of the target leaves TWO raising steps past a
`sucV γ`-floor constant: an ordinal inside `Lset (step 3 γ)` sits at or below
the `step 2 γ` level (`agents/tasks/LJ-1-693/Probe693.agda:82-84`;
`src/L/Ordinal/Stages.lagda.md:265-266` converts tower-membership of ordinals
to member-ordinals). Against that headroom:

1. relativize plants a fresh bound-constant at EVERY unbounded quantifier
   (`src/FOL/Manipulation/Relativize.lagda.md:57-58`);
2. each planted constant then enters a merge node, since every converted
   quantifier is now bounded and each bounded node merges both child stages
   (`src/L/Axioms/Separation.lagda.md:460-461`, `:450-454`);
3. merge outputs contain both inputs and stay ordinal
   (`src/L/Ordinal.lagda.md:185-188`), so the stage climbs strictly once per
   merge level above the deepest heavy constant;
4. the recorded graph formula nests unbounded quantifiers through SIX verified
   levels before anything unaudited begins:
   root `∃̇∈ (con γ)` (`agents/tasks/LJ-1-698/Probe698.agda:84-85`),
   PairGraphAt's `∃̇` plus prAtL-conjunction
   (`src/L/Coding/Sequence.lagda.md:329`),
   GraphAt's `∃̇` plus its conjunction (`:292`),
   ApproxAt's `domAt ∧̇ ∀̇ (∀̇ …)` (`:287-289`),
   with GraphAt's step slot standing at
   `StepAt = extAt v (∃̇ (∃̇ (∃̇ …)))` instantiated at `:349`, `:120`,
   itself still deeper.

Four verified planted `Lset γ` constants already sit past the fourth and
fifth merge levels; even the FOURTH-level planting consumes more than two
raising steps of headroom, so the row overshoots at or before `step 4 γ`.
Deeper subtrees only push further out; nothing on any branch pulls it back.
Classically granted monotone facts about `stage` in size turn this into an
outright refutation of the placement at `step 3 γ`; the tree types none of
those facts today, which is why the falsity stands PRICED, not proved.

**The exact step `[LJ-1.712]` asked for**: the audited minimum puts the
overshoot boundary between `step 3 γ` and `step 4 γ`; the true landing index
waits on one depth audit over `StepBody`/`extAt`/prAtL, which no probe has
carried yet. Do not treat any larger index as known.

**The corrected target beside the original**, as D-10 asks: drop the
placement row entirely and run the engine on the carve re-bounded at
`τ := step 2 γ`, per lj-1.706-report.md section 2. That shape closes to
`Below` with NO row like this existing anywhere: the door lands the carve at
exactly `Below`'s ceiling, and the planks here lift what little membership
still needs lifting.

## What would reopen the route

Two surfaces, both prerequisites, neither exists today:

1. the src rename-cure named by
   `agents/tasks/LJ-1-710/review-of-bound2-in-limit.md` (one public name for
   bound2's merge family, or the direct src lemma), without which a
   placement induction cannot even state its own merge rule;
2. a typed merge-height audit of `φᵣ := relativize (LsetS γ oγ)
   (recordedFo (γ , hγ))` covering `RecShape`/`StepBody`/`extAt`/prAtL,
   producing the exact depth datum as a TERM.

With both in hand, the placement row becomes a finite induction whose price
should be FLOORED first (coder clause, owner 2026-08-23) against the full
`mkBoundedFo` case tree, not attempted cold.

Nothing in `src/` changed in this dispatch.
