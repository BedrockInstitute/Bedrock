# Park judgement, LJ-1.728-SPLIT, 2026-08-29

**TO:** maintainer
**ROW:** `task-lj-1-728-split-transfer-park`
**REASON:** `row:task-lj-1-728-split-transfer-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve. No brief for `LJ-1.728-SPLIT-SPLIT`.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-728-SPLIT/runs/accept-1.out:10-22`. Conjuncts 1 to 6 held. Exit 0. `obligations_delta 0`, `obligations_open 1`. `heap_wall false`. `agda_vacuous true`. Own files 8, including `Probe728Split.agda.txt`. No `.agda` at the obligation path, so conjunct 1 did not run the term.
- `agents/tasks/LJ-1-728-SPLIT/lj-1.728-SPLIT-report.md:9-23`. STOP, environment, not the term. Transcription byte-identical to 728 shape 4. W3 at `-M4g` UNMEASURED. Supply 0. No `review-of-*.md`.
- `lj-1.728-SPLIT-report.md:88-107`. Five kills, all swap-branch SIGKILL, RSS 0.80 to 1.80 GB, none by heap. Floor never closed.
- `agents/tasks/LJ-1-728-SPLIT/runs/floor-2.out:9`. `time: command terminated abnormally`. Peak RSS 1,802,665,984. Caliber `-A64m -I0 -M4g`.
- `scripts/ops/agda-watchdog.sh:28`. `SWAP_MAX_MB` is 8192.
- `Probe728Split.agda.txt:189-203`. The term is written and aliased at the top level. The file is `.agda.txt` because no run has checked it.
- `.pod-state/worktrees/LJ-1-728-SPLIT/agents/tasks/LJ-1-728-SPLIT/lj-1.728-SPLIT-report.md:9`. Same HEAD as the live tree.
- `dev/pod/queue.toml` already holds `LJ-1.728-SPLIT-SPLIT` with no brief.
- Swap re-measured this hour: `vm.swapusage` used 8773.94 MB of 9216 MB. Still above 8192.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `grounded-from-complete`. The meter stayed open (`accept-1.out:19-20`).
2. **Not proven futile as a term.** A30 situation 2 needs a different task's proof that this route cannot succeed as a term. A watchdog SIGKILL is not that proof. 728 measured a heap wall at wide and answered that Convert is not the wall. Heavy has not run. The statement is untouched.

## WHY I DO NOT FILL THE AUTO-SPLIT

Transfer-park asks for a brief on `LJ-1.728-SPLIT-SPLIT`. Filling it now would dispatch the same composition at heavy into the same kill line. The 728-SPLIT report named the unblock as the owner's (`lj-1.728-SPLIT-report.md:144-149`): swap below 8192 MB, or the threshold moves. Swap is still 8773.94 MB. A retry is not a new measurement.

A frame split (`hull-closed` apart from the ambient-slot assembly) is the next move if heavy walls. Heavy did not wall. I do not invent that split from an unmeasured run.

The refill of this hour already left the request empty and queued `[LJ-1.729]` through `[LJ-1.733]`. The loop has work. This park does not add a sixth coder task.

## WHAT THE MAINTAINER SHOULD SEE

`LJ-1.728-SPLIT` stays PARKED. It occupies a `parked_max` slot honestly. `LJ-1.728-SPLIT-SPLIT` stays a request until swap is below 8192 MB. Then the brief is: rename `Probe728Split.agda.txt` to `.agda`, floor first, one Agda process, pane caliber, do not hypothesise Convert. GO is the name on the meter. A heap wall then is a frame split, not a Convert wrap.
