# Parked-max ruling, 8 parked, 2026-08-29

**TO:** the loop, maintainer
**LIVE REQUEST:** none. No shelve. No new successor.

## The eight

| code | ruling | this tick |
|---|---|---|
| LJ-1.728 | still open on `grounded-from-complete`. Heap wall at the frame, not Convert. 728-SPLIT-SPLIT is filled. | no shelve |
| LJ-1.728-SPLIT | still open. Term transcribed. Watchdog was the block. 728-SPLIT-SPLIT is filled. | no shelve |
| LJ-1.740 | still open on `Sat-at-asConst`. Placement core green. Bd, climb, merge absent. 740-SPLIT is filled. | no shelve |
| LJ-1.742 | still open on `defat-fill-asConst`. Prefix green. One hole. 742-SPLIT-SPLIT-SPLIT is filled. | no shelve |
| LJ-1.742-SPLIT | still open. Two holes in `remaining-goal`. Continuation filled. | no shelve |
| LJ-1.742-SPLIT-SPLIT | still open. 1948-line prefix. Body pending. 742-SPLIT-SPLIT-SPLIT is filled. | no shelve |
| LJ-1.753 | still open on `bound-in-stage-from-mirror`. Term written. Wall was erase-spelling. 753-SPLIT-SPLIT is filled. | no shelve |
| LJ-1.753-SPLIT | still open on the meter. Probe typechecks. Name sits in `module At`. 753-SPLIT-SPLIT is filled. | no shelve |

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-728/lj-1.728-report.md:9`. Heap wall. Probe is `.agda.txt`. Wall is not Convert's body.
- `agents/tasks/LJ-1-728/runs/accept-1.out:19-22`. Exit 0. Delta 0.
- `agents/tasks/LJ-1-728-SPLIT/lj-1.728-SPLIT-report.md:9`. Stop. Environment, not the term.
- `agents/tasks/LJ-1-728-SPLIT/runs/accept-1.out:19-22`. Exit 0. Delta 0.
- `agents/tasks/LJ-1-728-SPLIT-SPLIT/LJ-1.728-SPLIT-SPLIT.md:28`. Same object. No report. No accept.
- `agents/tasks/LJ-1-740/lj-1.740-report.md:13-20`. Parked, not closed. Placement core green. Bd absent.
- `agents/tasks/LJ-1-740/runs/accept-1.out:16-23`. Probe rc 0 in 1.82 s. Delta 0.
- `agents/tasks/LJ-1-740-SPLIT/LJ-1.740-SPLIT.md:28`. Same object. Directory holds the brief only.
- `agents/tasks/LJ-1-742/lj-1.742-report.md:14-16`. Partial. One hole. Probe is `.agda.txt`.
- `agents/tasks/LJ-1-742/runs/accept-2.out:19-22`. Exit 0. Delta 0. Open 1.
- `agents/tasks/LJ-1-742-SPLIT/lj-1.742-SPLIT-report.md:13-16`. Two holes in `remaining-goal`.
- `agents/tasks/LJ-1-742-SPLIT/runs/accept-1.out:19-22`. Exit 0. Delta 0.
- `agents/tasks/LJ-1-742-SPLIT-SPLIT/lj-1.742-SPLIT-SPLIT-report.md:13-16`. Body pending. rc 42 at 638 s.
- `agents/tasks/LJ-1-742-SPLIT-SPLIT/runs/accept-1.out:19-22`. Exit 0. Delta 0.
- `agents/tasks/LJ-1-742-SPLIT-SPLIT-SPLIT/LJ-1.742-SPLIT-SPLIT-SPLIT.md:35`. Same object. No report.
- `agents/tasks/LJ-1-753/lj-1.753-report.md:8`. Heap wall, localized. Term written.
- `agents/tasks/LJ-1-753/runs/accept-1.out:19-22`. Exit 0. Delta 0.
- `agents/tasks/LJ-1-753-SPLIT/lj-1.753-SPLIT-report.md:8`. Report says GO. Meter did not close.
- `agents/tasks/LJ-1-753-SPLIT/runs/accept-1.out:16-23`. Probe rc 0 in 3.01 s. Delta 0. Open 1.
- `agents/tasks/LJ-1-753-SPLIT-SPLIT/LJ-1.753-SPLIT-SPLIT.md:28`. `At.bound-in-stage-from-mirror`. No report.

## WHAT I DID NOT SHELVE

No A30. Nobody closed GO on `grounded-from-complete`, `Sat-at-asConst`, `defat-fill-asConst`, or `bound-in-stage-from-mirror`. A report that says GO is not a closed row. A watchdog kill is not a proof the term is false. A hole is not a proof the type is false.

Every listed task already has a successor with a brief. A second successor on the same name is a false premise.

The eight stay PARKED until a successor closes GO. Then A30 situation 1 can name that row.
