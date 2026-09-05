# Park judgement, LJ-1.737, 2026-08-29

**TO:** maintainer
**ROW:** `task-lj-1-737-transfer-park`
**REASON:** `row:task-lj-1-737-transfer-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.737-SPLIT` with `pair-in-Lγω`.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-737/runs/accept-1.out:16-22`. Exit 0. Probe rc 0, 2.0 s. `obligations_delta 0`, `obligations_open 1`. `heap_wall false`. No `review-of-*.md`.
- `agents/tasks/LJ-1-737/lj-1.737-report.md:8-14`. PARK, not GO and not NO-GO. The obligation is not discharged and not refuted. D-10: the target is TRUE.
- `lj-1.737-report.md:47-61`. Delivered: `Closer` arithmetic and `pair-in-Lγω`.
- `lj-1.737-report.md:63-87`. Two tree debts block the satisfaction: tower-graph stage, DefAt witness placement.
- `Probe737.agda:115-117`. `pair-in-Lγω` inhabited inside `Underω`.
- `Probe737.agda:120-127`. `table-sat` absent on purpose.
- `.pod-state/worktrees/LJ-1-737/agents/tasks/LJ-1-737/lj-1.737-report.md:8`. Same HEAD as the live tree.
- `dev/pod/queue.toml` already holds `LJ-1.737-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `table-sat`. Supply 0. The meter stayed open (`accept-1.out:20`).
2. **Not proven futile as a term.** D-10 on this return says the target is TRUE (`lj-1.737-report.md:89-96`). A missing placement leg is not a proof the statement is false. 724-SPLIT refuted `x+2`, not `closedω`.

## WHAT I QUEUE

`[LJ-1.737-SPLIT]`, brief `agents/tasks/LJ-1-737-SPLIT/LJ-1.737-SPLIT.md`. Transcribe `pair-in-Lγω`. Do not inhabit `table-sat`. The DefAt placement debts are already queued as `[LJ-1.739]` through `[LJ-1.742]`. This split is the 727-SPLIT shape: the supply name the meter can close.
