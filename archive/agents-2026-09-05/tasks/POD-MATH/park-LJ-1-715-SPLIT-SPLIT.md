# Park judgement, LJ-1.715-SPLIT-SPLIT, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-715-split-split-heap-wall-park`
**REASON:** `row:task-lj-1-715-split-split-heap-wall-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile as a term. No shelve of this task.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/accept-1.out:10-23`. Conjunct 1 FAILED. Target `src/Everything.lagda.md`, rc 251, 114.96 s, `error_class heap_wall`, concurrency 2. `obligations_delta -1`, `obligations_open 0`. Own files include `src/L/Ordinal/Limit.lagda.md` and `src/Everything.lagda.md`.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/accept-1.out:25`. `verdict_files_refused` names `review-of-bound2-in-limit.md`. That file is the author's. The record is the report.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/lj-1.715-SPLIT-SPLIT-report.md:32-40`. The measurement table.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/limit-master.out:1`. Checking `L.Ordinal.Limit`. No heap-exhausted line. Report: EXIT=0, 1.07 s.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/probe715ss.out:1`. Checking the probe. No heap-exhausted line. Report: EXIT=0, 1.02 s.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/everything-floor.out:1-8`. Warm tail through `L.CardinalAbove`. No heap-exhausted line. Report: EXIT=0, 18.67 s.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/everything-floor-cold.out:97-100`. Checking `L.Condensation`, heap exhausted, 4 GB.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/everything-floor-warm.out:2-5`. Same site, same wall.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/everything-pristine-cold.out:96-99`. Pristine HEAD, module absent. Same site, same wall.
- `agents/tasks/LJ-1-715-SPLIT-SPLIT/runs/everything-pristine-bprot.out:2-5`. Pristine HEAD, one-step warm. Same site, same wall.
- `.pod-state/worktrees/LJ-1-715-SPLIT-SPLIT/src/L/Ordinal/Limit.lagda.md:45-53`. `bound2-in-limit` is there. It imports `bound2` from `L.Ordinal`.
- `.pod-state/worktrees/LJ-1-715-SPLIT-SPLIT/src/Everything.lagda.md:334`. One catalog import of `L.Ordinal.Limit`.
- `src/L/Ordinal.lagda.md:185`. Live tree. That line is `bound2`. No `bound2-in-limit`. No `IsLimit`.
- `src/L/Ordinal/`. Four siblings: Linear, SquareLaw, StageArith, Stages. No `Limit.lagda.md`.
- `src/Everything.lagda.md:327-332`. Live catalog. `L.Ordinal` then Linear, Stages, StageArith, SquareLaw. No Limit import.
- `dev/pod/queue.toml:7426-7430`. Auto request `LJ-1.715-SPLIT-SPLIT-SPLIT`. No brief.
- `.pod-state/state.json:35812`. `LJ-1.715-SPLIT` status PARKED.
- `.pod-state/state.json:35939`. `LJ-1.715-SPLIT-SPLIT` status PARKED.

## WHY THIS IS NOT A SHELVE OF 715-SPLIT-SPLIT

1. **Not delivered elsewhere.** No other task's `obligations` line names `bound2-in-limit` and closed GO. Live `src/` still lacks the lemma and the module.
2. **Not proven futile as a term.** The sibling hole is GO. The isolated master checks. The probe discharges through the src lemma (`Probe715SS.agda:67-72`). Warm Everything with the module imported closes at 18.67 s. A heap wall is not a proof the statement is false.

A30 situation 2 needs a different task's proof that this route cannot succeed as a term. The HEAD wall at `L.Condensation` is this task's own runs 4 and 5. That cannot shelve this task.

## WHAT THE WALL IS NOW

Accept conjunct 1 always runs Everything after a `src/` write. That arm died at concurrency 2, 114.96 s. The coder's one-process floors show the same wall on pristine HEAD, with and without the module. The landing's cost at the wall site is zero to measurement: 123.48 s with the module against 125.40 s without, same site (`lj-1.715-SPLIT-SPLIT-report.md:51-53`). The 111.91 s control from 715-SPLIT does not reproduce. Do not cite it as live.

The hole the brief asked about is measured GO. A fourth landing is the thing I forbade.

## THE AUTO-SPLIT REQUEST

I write no brief for `LJ-1.715-SPLIT-SPLIT-SPLIT`. Rule (a1) skips that request until a brief exists. Leave it empty.

## WHAT I SHELVE

`LJ-1.715-SPLIT`, still PARKED. One A30 request, situation 2. The different task is this one: HEAD Everything-cold already dies at `L.Condensation` at `-M4g`. Retrying the 33-line `L.Ordinal.lagda.md` landing cannot close at this cap.

## FOR THE MAINTAINER

The five-case trigger for superheavy was a NO-GO on this hole. The hole is GO. The new cap question is HEAD itself.

When no omlx task is RUNNING, run by hand:

```
.venv/bin/python scripts/pod/superheavy-check.py src/Everything.lagda.md
```

That is live HEAD, no Limit module. If that closes at 8 GB, a second run on the 715-SPLIT-SPLIT worktree's Everything measures whether the landing fits. If HEAD still walls at 8 GB, the close waits on `L.Condensation`, not on another landing.
