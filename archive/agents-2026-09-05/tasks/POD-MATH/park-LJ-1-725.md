# Park judgement, LJ-1.725, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-725-transfer-park`
**REASON:** `row:task-lj-1-725-transfer-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.725-SPLIT` with `stage-read`.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-725/runs/accept-2.out:10-23`. Exit 0. Delta 0. Open 1. Probe rc 0, 2.03 s. `verdict_files_refused` names `review-of-carved-is-hier.md`. That file is the author's. The record is the report.
- `agents/tasks/LJ-1-725/lj-1.725-report.md:9-23`. NO-GO on `carved-is-hier`. Probe green, EXIT=0, 23.55 s, 37 percent of the wide cap. Name absent on purpose.
- `lj-1.725-report.md:47-58`. First inclusion `hierL-into-carved` is real from `table-sat`. Reverse inclusion costs `stage-read`. `carved-is-hier-from` assembles from both.
- `Probe725.agda:251-258`. `stage-read` stated, not inhabited.
- `Probe725.agda:286-299`. `carved-is-hier-from` real, from `table-sat` and `stage-read`.
- `.pod-state/state.json` row `task-lj-1-725-transfer-park`, PARKED.
- `dev/pod/queue.toml` already holds `LJ-1.725-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `carved-is-hier`.
2. **Not proven futile as a term.** The report says the statement is not false. The tree lacks `stage-read`. 724 measured unscoped `table-sat` false; that is the first inclusion's hyp, not a proof the equation is false. A30 situation 2 needs a different task proving this route cannot succeed. 724 did not prove `carved-is-hier` false.

## THE OTHER FOUR

- `LJ-1.715-SPLIT-SPLIT`: still open. No fourth landing.
- `LJ-1.724`: continuation already queued as `LJ-1.724-SPLIT`.
- `LJ-1.727`: continuation already queued as `LJ-1.727-SPLIT`.
- `LJ-1.728`: continuation already queued as `LJ-1.728-SPLIT`.

## WHAT I QUEUE

`[LJ-1.725-SPLIT]`, brief `agents/tasks/LJ-1-725-SPLIT/LJ-1.725-SPLIT.md`. Obligation `stage-read`. Do not inhabit `carved-is-hier`. Do not inhabit `table-sat`. `Lset-trans-set` is the first half of W3, not a second obligation.
