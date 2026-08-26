# [LJ-1-671] Report

## VERDICT

**NO-GO.** The obligation `sat-at-packed : SatAtPacked delivered`
cannot be built in this probe. The target is **true** — the bounded
zero-instance matrix is the intended level-hood reading, and its step
clause is the same clause the unbounded, already-proven chapter
builds (`src/L/Condensation.lagda.md:2405-2416` vs
`src/L/Coding/Sequence.lagda.md:114-118`, fourth conjunct
`var 3 ∈̇ var 0` in both). The wall is a **delivery gap**: the tree
carries no satisfaction lemma for `approxBndAt` / `stepBndAt` / the
row leaf, the delivered `KFacts` bridge wants fourteen slots against
two, and the measured cost of one frame step at this site exceeds the
1200 s run cap.

The full argument is `agents/tasks/LJ-1-671/review-of-sat-at-packed.md`.

## WHAT IS GREEN

- `agents/tasks/LJ-1-671/Probe671.agda` — green
  (`runs/probe-5.out`, 3.56 s, EXIT=0). Carries the verbatim
  `SatAtPacked` from `agents/tasks/LJ-1-663/Probe663.agda:135-138`,
  the obligation under the brief's name, and the stop.
- `agents/tasks/LJ-1-671/runs/ATK-1.agda` — green attempt record
  (`runs/atk-6.out`, 3.21 s, EXIT=0).
- `agents/tasks/LJ-1-671/runs/ATK-1-red.agda.txt` — the red version
  (structural skeleton, residue open), preserved under the
  `.agda.txt` naming rule.
- Nothing lands in `src/`. Nothing is postulated.

## THE MEASUREMENT THAT DECIDES

`runs/atk-3.out`: the deep witness attempt — the inner truncated
existential with the step variable instantiated to the packed value
and a reflexive matrix satisfaction asserted — ran the full **1200 s
cap** (EXIT=142, peak 946,241,536 bytes). Agda spent the whole budget
reducing one clause of the wrapped matrix to report an inequality.
The residue is not a witness search: it is the full satisfaction of
the bounded frames (approxBndAt, stepBndAt with its three ∃̇∈ binders,
the leafB row, the Δ₀ leaf), all at the stage. That is a new module
of chapter scale (review, section 6), not a probe.

## CORRECTION OF RECORD

Mid-attempt, this task derived the matrix **unsatisfiable**, from a
reading of the fourth conjunct as `var 6 ∈̇ var 0` (a free slot
`u ≈ˢ γ` lying in `d` against `d ∈ γ` — a rank contradiction). The
verbatim source is `var 3` — the step variable `z` — in both the
bounded and the unbounded body. The unsatisfiability claim was an
artifact of a misquoted clause in this task's working notes. It is
retracted and recorded in the review (section 2.3) so that no future
reader mistakes it for a measured fact.

## FOR THE NEXT BRIEF

Two routes, both chapter scale, both new modules under `src/`
(review, section 6):

1. A satisfaction module for the bounded frames, transferring the
   unbounded chapter's `fill` / `readBody` machinery
   (`src/L/Coding/Sequence.lagda.md:203-231`) across the ∃̇∈ binders
   and the `extAtB` clause.
2. A re-derivation of the level-hood at the arity the `KFacts` wants;
   the [LJ-1-666] review shows the tension is structural, at any
   arity (`agents/tasks/LJ-1-666/review-of-sat-at-level.md`, section 3).

The W3 estimate in the brief (120 to 260 lines) prices the
satisfaction as if the frame machinery were delivered. It is not: the
frame itself — the ∃̇ / ∃̇∈ / extAtB clause structure — is what no
lemma covers, and one clause of it already exceeds the run cap.

## RUNS

See `agents/tasks/LJ-1-671/runs/runs.md`.

## ARCHIVE USED

None read. All five named candidates declined in writing
(`archive/dev/ORCHESTRATION.md`, `archive/dev/DD-archived.md`,
`archive/dev/PLAN-archived.md`, `archive/dev/TASKS-archived.md`,
`archive/dev/STATUS-archived.md`); the per-file reasons are in the
review, section `## ARCHIVE USED`.

## LITERATURE USED

None read. All five named candidates declined in writing
(`dev/literature/level-formula-slot-roles.md`,
`dev/literature/devlin-errata.md`,
`dev/literature/glossary-review-2026-08.md`,
`dev/literature/BIBLIOGRAPHY.md`,
`dev/literature/formalizations-landscape.md`); the per-file reasons
are in the review, section `## LITERATURE USED`.
