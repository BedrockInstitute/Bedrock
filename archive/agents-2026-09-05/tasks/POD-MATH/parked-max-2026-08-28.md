# Parked-max ruling, 2026-08-28, rule (d)

**TO:** the loop, maintainer
**LIVE REQUEST:** `dev/pod/shelve-request.toml` names LJ-1.720.
**NEXT DROP-INS, same order:** `agents/tasks/POD-MATH/shelve-LJ-1-717.toml`, then `shelve-LJ-1-722.toml`.

## The five

| code | ruling | this tick |
|---|---|---|
| LJ-1.720 | delivered-elsewhere. 721 closed GO on pack-stage. | live shelve |
| LJ-1.717 | proven-futile. 722 measured the same amb-to-atL shape at heavy. | drop-in, next tick |
| LJ-1.722 | proven-futile. 717 isolated the bridge. No third generation of this shape. | drop-in, after 717 |
| LJ-1.715-SPLIT-SPLIT | still open. Hole GO. Live src has no lemma. A30 cannot use this task's own HEAD wall. | no shelve, no fourth landing |
| LJ-1.704 | still open. Not delivered elsewhere. Not proven futile. | no shelve this tick |

## LJ-1.704

Accept-3: exit 0, delta 0, open 1, own 1 (`runs/accept-3.out:16-22`). Author `review-of` refused. Probe green 2.23 s (`runs/p-4.out:5`). Meter: 1 UNRESOLVED, NotInScope at `carved-is-hier` (`runs/meter-obligation.out:1`). The name is absent on purpose (`Probe704.agda:87-99`).

The report says the equation is true in the model at σ = γ + 1 and not constructible in the tree. The missing fact is `table-sat`, the recording-satisfaction induction. No other task closed GO on `carved-is-hier`. Grep of live `agents/tasks` finds the name only in 704's own brief.

I do not shelve 704. I do not queue `table-sat` on this tick: the report states it in prose, not as an Agda type, and a brief that guesses 698's satisfaction type is a badly stated problem. Next prompt after 720/717/722 fire, I will open Probe698 and write that successor.

## After 720, 717 and 722 shelve

Parked should be 704 and 715-SPLIT-SPLIT. That is under `parked_max`.
