# Report, task LJ-1.715-SPLIT-SPLIT

coder, head `coder`, machine `shared`, agda tier `heavy`.
`GHCRTS=-A64m -I0 -M4g` was set on the pane by the program and was never
changed here. One Agda process per run; runs were sequential. Before the
floor runs I waited out a foreign agent's probe (`LJ-1-721`) so no other
Agda process was live in any measured run.

## What was built

- `src/L/Ordinal/Limit.lagda.md`, new. Exports `IsLimit` and
  `bound2-in-limit` with the same types as the 715-SPLIT worktree
  (`.pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md:205-231`, fence
  transcribed verbatim, only the import block adapted to the new module).
  It imports `bound2` from `L.Ordinal` and nothing else from it.
  `src/L/Ordinal.lagda.md` is untouched.
- `src/Everything.lagda.md`: one import line next to the other `L.Ordinal.*`
  imports, and one catalog bullet in the en block and one in the zh block,
  each next to the `L.Ordinal` bullet. No `ja` block exists in this file.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/Probe715SS.agda`: the obligation,
  mirrored, discharged through the src lemma; plus the small-layer mirror
  of the hole route, as in the predecessor probe.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/`: all outputs cited below.
- No module was retired; nothing went to `archive/` (W4: no action).
- W2: the lemma is stated once at a generic limit `α`; nothing was
  specialized to a consumer, so there is no second proof to share.

## Measurements

All runs on this worktree at the pane caliber.

| run | tree | state | verdict | seconds | evidence |
|---|---|---|---|---|---|
| M | new master alone | cold | EXIT=0 | 1.07 | runs/limit-master.out |
| P | probe alone | after M | EXIT=0 | 1.02 | runs/probe715ss.out |
| 1 | Everything + module | interfaces cached from earlier builds; tail re-checked | EXIT=0 | 18.67 | runs/everything-floor.out |
| 2 | Everything + module | full cold (`_build/2.8.0` deleted) | EXIT=251 at `L.Condensation` | 275.19 | runs/everything-floor-cold.out |
| 3 | Everything + module | one step warmer, after run 2 | EXIT=251 at `L.Condensation` | 123.48 | runs/everything-floor-warm.out |
| 4 | pristine HEAD, module absent | one step warmer, same protocol as 3 | EXIT=251 at `L.Condensation` | 125.40 | runs/everything-pristine-bprot.out |
| 5 | pristine HEAD, module absent | full cold | EXIT=251 at `L.Condensation` | 256.38 | runs/everything-pristine-cold.out |

## The finding that corrects premise 4

Premise 4 said Everything without the 33 lines closes at the heavy cap,
111.91 s. That number does not reproduce on today's tree. Runs 4 and 5 are
pristine HEAD (my import line reverted, my master's interface deleted, my
master unreferenced on disk) and both die at `L.Condensation` at the cap,
in the one-step-warm state and full cold. The wall is HEAD's own at
`L.Condensation` in every non-fully-warm state measured, with and without
this task's landing.

The landing's marginal cost at the wall site is zero to measurement:
run 3 (with module) 123.48 s against run 4 (without) 125.40 s, same
verdict, same site. The brief's GO criterion "Everything should match the
111.91 s control" is therefore unsatisfiable for any landing, including
no landing at all. The criterion that can be met is met: with the module
imported, one Agda process, pane caliber, Everything closes EXIT=0
(run 1). The predecessor's control was taken in a machine state no longer
reproducible here; I did not rerun the same code to chase its number.

No restructuring of my own scope was attempted against the `L.Condensation`
wall, for a specific reason: runs 4 and 5 are the wall surviving the total
absence of my change, so no reshape of my module can cure it. The cure is a
frame decision above this task's scope (`L.Condensation`, the cap, or a
seal in `L.Ordinal`), and it belongs to the mathematician and the owner.

## Prices for the ledger

- New master: 42 non-blank in-fence lines, 1.07 s cold isolated.
- Everything: 1 added in-fence line (the import); bullets are prose.
- Probe: raw `.agda`, counts 0; 1.02 s.
- The 1.07 s is a cold price: it rebuilds the whole import chain. The
  content is the same 33-line fence the 715-SPLIT worktree priced at
  0.82 s warm in place.

## What the next brief needs

- The obligation is landed and has supply 1. The hole route survives the
  move out of `L.Ordinal`: the probe (P) and the master (M) both close with
  `bound2` only imported.
- The `L.Condensation` wall at heavy `-M4g` is a standing tree property on
  this machine, present on pristine HEAD (runs 4, 5). Any brief that gates
  on a cold or one-step-warm full-tree floor at the heavy cap will park
  until that frame decision is taken. The predecessor's 111.91 s control
  should not be cited as a live number.
- `L.Ordinal.Limit` sits in the catalog between `L.Ordinal` and `L.Rank`,
  where the brief placed it. Its first real consumer may move it; the
  reading-order rule puts it where that consumer needs it.

## ARCHIVE USED

- `archive/dev/PLAN-archived.md:243`, read for the live authority for the
  catalog placement: "the two-catalog doctrine and the named-hypothesis
  debt form are in `dev/STYLE-agda.md`". Used to confirm the placement
  follows `dev/STYLE-agda.md` section 2, not the archive.
- `archive/dev/DD-archived.md:24`, read for the probe rule this task
  followed: "A probe IS committed, in `agents/tasks/<TASK>/` beside its
  brief and its report, and never under `src/`".
- `archive/dev/ORCHESTRATION.md`: declined, not used. It is canonical for
  the orchestrator's operating rules; this slot's rules live in the coder
  instruction file and the brief.
- `archive/dev/STATUS-archived.md`: declined, not used. It is the archived
  goal table of the internalization route, which this transcription task
  does not touch.
- `archive/dev/TASKS-archived.md`: declined, not used. It indexes the
  retired `L3.32-T` task series, superseded before this campaign.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not surveyed. No
  glossary term was added, disputed or needed by this task.
- `dev/literature/primary-sources.md`: declined, not surveyed. No
  mathematical prose was written; the fence is a verbatim transcription.
- `dev/literature/devlin-errata.md`: declined, not surveyed. Nothing in
  this task reads Devlin; the statement came from the brief and the
  predecessor's probe.
- `dev/literature/formalizations-landscape.md`: declined, not surveyed.
  The task makes no formalization choice; it re-homes an existing one.
- `dev/literature/rudimentary-functions.md`: declined, not surveyed. No
  rudimentary function is used by the lemma or its proof.
