# Park judgement, LJ-1.746, 2026-08-29

**TO:** maintainer
**ROW:** `task-lj-1-746-transfer-park`
**REASON:** `row:task-lj-1-746-transfer-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.746-SPLIT`.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-746/runs/accept-1.out:16-24`. Exit 0. `obligations_delta 0`, `obligations_open 1`. `heap_wall false`. `Amb7.agda` rc 0, `EraseIrr.agda` rc 0. `verdict_files_refused` names `review-of-bound-in-stage-at-empty.md`.
- `agents/tasks/LJ-1-746/lj-1.746-report.md:10-16`. NO-GO stated on the obligation. The named leaf is green. Probe is `.agda.txt`.
- `lj-1.746-report.md:86-93`. W3: the remaining chain does not land. The wall is `Amb4`, not the 732 `PT.rec`.
- `lj-1.746-report.md:110-118`. Next brief: candidate 1, shared split-spelling of the row types. Stay wide.
- `runs/Amb7.agda:55-70`. `StepKilledGen` and `approx-part` as one `Empty.rec`.
- `.pod-state/worktrees/LJ-1-746/agents/tasks/LJ-1-746/lj-1.746-report.md:10`. Same HEAD.
- `dev/pod/queue.toml` already holds `LJ-1.746-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `bound-in-stage-at-empty`. Supply 0. `[LJ-1.745]` closed GO on `step-killed`, a different name.
2. **Not proven futile.** The D-10 reading at empty is still TRUE (`lj-1.732-report.md:126`). An `Amb4` unifier wall is not a proof the implication is false. The report names a next shape.

The author's `review-of-*.md` was refused, so this is not a critic-closed NO-GO. F9 still holds: the close of a stated NO-GO is the critic's return.

## WHAT I QUEUE

`[LJ-1.746-SPLIT]`, brief `agents/tasks/LJ-1-746-SPLIT/LJ-1.746-SPLIT.md`. Import green `Amb7` and `EraseIrr`. Close `Amb4` by candidate 1. Do not rebuild `approx-part`. Do not retry the direct `Amb4` term. Do not inhabit `Completeness`. Wide. Floor first. One Agda process.
