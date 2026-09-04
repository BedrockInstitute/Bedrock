# Park judgement, LJ-1.715, 2026-08-27

**TO:** maintainer
**ROW:** `task-lj-1-715-heap-wall-park`
**REASON:** `row:task-lj-1-715-heap-wall-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-715/runs/accept-1.out:10-23`. Conjunct 1 FAILED. Conjuncts 2 to 6 held. Target `src/Everything.lagda.md`, rc 251, 206.66 s, `error_class heap_wall`, `heap_wall true`, concurrency 2. `obligations_delta -1`, `obligations_open 0`.
- `dev/pod/transitions/2026-08.jsonl:4925`. The PARKED line, same facts.
- `src/L/Ordinal.lagda.md:221-229`. Live tree. That span is `mem-ord`. No `bound2-in-limit`. No `IsLimit`.
- `.pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md:205-229`. `IsLimit` and `bound2-in-limit` are there.
- `agents/tasks/LJ-1-715/Probe715.agda:60-65`. The obligation forwards to the src lemma.
- `agents/tasks/LJ-1-715/runs/probe715.out`. EXIT=0, 0.82 s, checked the worktree probe.
- `agents/tasks/LJ-1-715/runs/ordinal-final.out`. EXIT=0, 0.80 s, isolated master.
- `agents/tasks/LJ-1-715/lj-1.715-report.md:10-20` and `:149`. Report says GO and "heap wall none". That "none" is the isolated master, not conjunct 1.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task's `obligations` line names `bound2-in-limit` and closed GO. Supply in live `src/` is 0.
2. **Not proven futile.** The worktree proof is four lines and the isolated master checks in 0.80 s. The statement is not shown false.

A parked close does not commit. The live tree still lacks the lemma. `[LJ-1.711]` still needs it.

## WHAT THE WALL IS

Section 4.3.2 case 1: a `src/` write makes conjunct 1 run `src/Everything.lagda.md` (`scripts/pod/facts.py:492-519`). `[LJ-1.715]` never ran that target. The brief forbade writing Everything. The accept arm ran it at concurrency 2 against `-M4g`. `L.Ordinal` has 40 dependents.

`Diag715c.agda` is a live diagnostic under the task home. It is not the accept target. Case 1 does not typecheck task-home `.agda` when a master changed.

## WHAT I QUEUED

`[LJ-1.715-SPLIT]`, brief `agents/tasks/LJ-1-715-SPLIT/LJ-1.715-SPLIT.md`. Preflight: 23 checks, no refusal.

The split transcribes the worktree bodies. It does not re-invent the lemma. It floors Everything with one Agda process before a GO. A second Everything wall, after that transcription and no extra `.agda`, is a finding about the 40-dependent host at this cap, not about the term.

## FOR THE MAINTAINER

The isolated master was 0.80 s. Everything at concurrency 2 was rc 251 at 206.66 s. If a later landing in `L.Ordinal` repeats this with one Agda slot, the cap is the host. If it closes with one slot, the 715 park was a concurrency collision. I cannot tell those apart from this record.
