# Park judgement, LJ-1.715-SPLIT, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-715-split-heap-wall-park`
**REASON:** `row:task-lj-1-715-split-heap-wall-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-715-SPLIT/runs/accept-1.out:10-23`. Conjunct 1 FAILED. Everything, rc 251, 117.86 s, heap wall, concurrency 2. Obligations delta −1.
- `src/L/Ordinal.lagda.md`. Live tree. No `bound2-in-limit`. Supply 0.
- `.pod-state/worktrees/LJ-1-715-SPLIT/src/L/Ordinal.lagda.md:205-229`. `IsLimit` and `bound2-in-limit` are there.
- `runs/probe715split.out:11`. EXIT=0, 1.04 s, one process.
- `runs/ordinal-final.out:9`. EXIT=0, 0.82 s.
- `runs/everything-floor.out:56-63`. One process, `-M4g`. Checking `L.Condensation`, heap exhausted, EXIT=251, 217.07 s.
- `runs/everything-floor-nolines.out:8-11`. Same cap, lines reverted. EXIT=0, 111.91 s.
- `runs/everything-floor-warm.out:6-13`. Lines restored, warmer. Checking `L.Condensation`, heap exhausted, EXIT=251, 196.66 s.
- `review-of-bound2-in-limit.md:20-33`. The controlled pair: B closes, C dies at the same site as A.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `bound2-in-limit`. Live `src/` still lacks it.
2. **Not proven futile.** A heap wall is not a proof the term cannot succeed. The isolated master checks in 0.82 s. The statement is not shown false.

## WHAT THE WALL IS NOW

The 715 park knew the wall only at concurrency 2. This dispatch reproduced it at one process and added the without-lines control. The 33 lines in `L.Ordinal` are the difference: without them Everything closes at 111.91 s; with them it dies in `L.Condensation` at 4 GB. Import-trim has nothing to cut. A third transcription into `L.Ordinal` is the attempt I forbade in the 715-SPLIT brief.

## WHAT I QUEUED

`[LJ-1.715-SPLIT-SPLIT]`, brief `agents/tasks/LJ-1-715-SPLIT-SPLIT/LJ-1.715-SPLIT-SPLIT.md`. Preflight: 23 checks, no refusal.

The lemma moves to a new sibling `src/L/Ordinal/Limit.lagda.md`. `L.Ordinal.lagda.md` is not edited. `bound2` is imported. W3 is whether the family hole still solves from another module. Everything is in scope only to add that module's catalog line.

A NO-GO on that hole means the lemma must sit in `L.Ordinal.lagda.md`, and the close waits on a cap ruling. I will not queue a fourth landing.

## FOR THE MAINTAINER

Accept was again concurrency 2. The coder's own floors were one process. The one-process wall is now measured. The cap, not the sibling slot, is what tips `L.Condensation` when `L.Ordinal` grows two public names.
