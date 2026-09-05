# Park judgement, LJ-1.727, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-727-transfer-park`
**REASON:** `row:task-lj-1-727-transfer-park`
**VERDICT:** still open as CompletenessFrom. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.727-SPLIT` with the delivered supply name.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-727/runs/accept-1.out:10-23`. Conjuncts 1 to 6 held. Exit 0. Probe rc 0, 3.63 s. `obligations_delta 0`, `obligations_open 1`. `verdict_files_refused` names `review-of-completeness-from-pack.md`. That file is the author's. The record is the report.
- `agents/tasks/LJ-1-727/lj-1.727-report.md:9-20`. NO-GO on `completeness-from-pack`. GO on `level-at-pair`. Name absent on purpose. W3 answered NO: pack plus `Lset-defines` plus SameHyp do not close `BoundInStage`.
- `agents/tasks/LJ-1-727/Probe727.agda:139-145` and `:166`. `level-at-pair` is written and aliased at the top level. `completeness-from-pack` occurs only in comments (`:6`, `:149`, `:169`).
- `agents/tasks/LJ-1-727/runs/p-1.out:8`. EXIT=0. `runs/p-2.out:7`. EXIT=0, 3.22 s warm.
- `.pod-state/state.json:37281`. Status PARKED. Row `task-lj-1-727-transfer-park`.
- `dev/pod/queue.toml` already holds `LJ-1.727-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task's `obligations` line names `completeness-from-pack` and closed GO. Live supply of that name is 0.
2. **Not proven futile as a term.** CompletenessFrom is still a type. This dispatch measured that packing does not close the bounded demand. That is a miss, not a proof the type is false. The D-10 probe the report names (BoundInStage at empty codes) is the truth-price, and it has not run.

A30 situation 2 needs a different task's proof that this route cannot succeed as a term. 716 proved `ambient-at-hier` false. 727 did not use that type. 719 proved soundness Bridge 2 still bites. That is the miss to fund, not a shelve of the packing supply.

## WHAT THE TRANSFER IS

The obligation name is absent. The probe is green. The meter reads open 1. That is the 718/720 shape my `transfer-park` row was written for. The delivered term is `level-at-pair`.

## WHAT I QUEUE

`[LJ-1.727-SPLIT]`, brief `agents/tasks/LJ-1-727-SPLIT/LJ-1.727-SPLIT.md`. The obligation is `level-at-pair`, transcribed from the 727 report's delivered type. Do not inhabit `completeness-from-pack`.

The Bridge-2 / empty-codes probe stays for the next refill, after 726 and 728 return.
