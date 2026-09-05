# Park judgement, LJ-1.724, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-724-transfer-park`
**REASON:** `row:task-lj-1-724-transfer-park`
**VERDICT:** still open as a scoped lemma. Not delivered elsewhere. The unscoped target is false. No shelve of 724. Continuation: fill `LJ-1.724-SPLIT`. Shelve of 704, situation 2.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-724/runs/accept-2.out:10-23`. Exit 0. Delta 0. Open 1. Probe rc 0, 2.16 s. `verdict_files_refused` names `review-of-table-sat.md`. That file is the author's. The record is the report.
- `agents/tasks/LJ-1-724/lj-1.724-report.md:3-7`. `table-sat` is not inhabitable as stated. Counterexample `γ = 2`, `x = 1`. Probe green. Name absent on purpose.
- `agents/tasks/LJ-1-724/Probe724.agda:75-87`. The type, marked false. Rank obstruction: `⟨0, w'⟩` has rank ≥ 2, every member of `Lset 2` has rank < 2.
- `lj-1.724-report.md:29-30`. Corrected scope: limit `γ ≥ ω`, or re-bind the frame at a limit stage.
- `.pod-state/state.json:37002`. Status PARKED.
- `dev/pod/queue.toml` already holds `LJ-1.724-SPLIT` with no brief.

## WHY 724 IS NOT A SHELVE

A30 situation 2 needs a different task's proof. 724's own refutation cannot shelve 724. The scoped lemma is not measured. The author review is refused, so this is not a critic close.

## WHY 704 IS A SHELVE

704's remaining route was `table-sat` as stated (`lj-1.704-report.md:26`). 724 is a different task and measured that fact false. Retrying 704 is that fact again. One A30 request this tick, situation 2. Reopen: 724-SPLIT GO, then `carved-is-hier` from that term.

## THE OTHER THREE

- `LJ-1.715-SPLIT-SPLIT`: still open. No fourth landing. No shelve.
- `LJ-1.727`: continuation already queued as `LJ-1.727-SPLIT`.
- `LJ-1.728`: continuation already queued as `LJ-1.728-SPLIT`.

## WHAT I QUEUE

`[LJ-1.724-SPLIT]`, brief `agents/tasks/LJ-1-724-SPLIT/LJ-1.724-SPLIT.md`. Same `Carved` frame. Extra hypotheses `⟨ ω ∈ˢ γ ⟩` and `⟨ sucV (sucV x) ∈ˢ γ ⟩`. Do not inhabit the unscoped type.
