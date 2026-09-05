# Park judgement, LJ-1.753-SPLIT, 2026-08-29

**TO:** maintainer
**ROW:** `task-lj-1-753-split-transfer-park`
**REASON:** `row:task-lj-1-753-split-transfer-park`
**VERDICT:** still open on the meter. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.753-SPLIT-SPLIT`.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-753-SPLIT/runs/accept-1.out:16-23`. Exit 0. All six conjuncts held. Probe rc 0 in 3.01 s. `obligations_delta 0`. `obligations_open 1`. `heap_wall false`. `verdict_files_refused` empty.
- `agents/tasks/LJ-1-753-SPLIT/lj-1.753-SPLIT-report.md:8-15`. Disposition GO. The term typechecks at the brief's signature. Cold run rc 0, 147.28 s, peak RSS 1,885,126,656 B (`runs/probe753split-29.out:20`). Warm recheck rc 0 in 3.25 s (`runs/probe753split-30.out:19`). No hole. Nothing postulated. `GraphAt`, `Completeness` and `AT.read` never appear.
- `lj-1.753-SPLIT-report.md:111-117`. W3: `erase-cong` at the domB-annotation converts at wide. The inline 21-node chain is gone at this site.
- `Probe753Split.agda:80`. The name sits inside `module At`.
- `Probe753Split.agda:138-144`. The inhabited term.
- `.pod-state/worktrees/LJ-1-753-SPLIT/.pod-state/witness/Witness-LJ-1-753-SPLIT-e0ddfee2.agda:44`. The meter asked for `Target.bound-in-stage-from-mirror` at the file top. That name is not there.
- `dev/pod/queue.toml` already holds `LJ-1.753-SPLIT-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `bound-in-stage-from-mirror`. `src/` supply is 0. This task inhabited the term. The meter did not close, because the witness used the bare name.
2. **Not proven futile.** D-10 at empty is still TRUE. The probe is green. A dotted-name miss is not a proof the implication is false.

The author wrote no `review-of-*.md`. This is not a critic-closed NO-GO. F9 still holds.

This is the 744 shape: the term is inhabited, accept records delta 0, the split puts the name where the meter reads it.

## WHAT I QUEUE

`[LJ-1.753-SPLIT-SPLIT]`, brief `agents/tasks/LJ-1-753-SPLIT-SPLIT/LJ-1.753-SPLIT-SPLIT.md`. Transcribe the inhabited file. Keep `module At`. Name `At.bound-in-stage-from-mirror`. Do not rewrite the body. Do not retry `erase-cong`. Do not inhabit `GraphAt`. Wide. Floor first. One Agda process.
