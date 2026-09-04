# Park judgement, LJ-1.728, 2026-08-28

**TO:** maintainer
**ROW:** `task-lj-1-728-transfer-park`
**REASON:** `row:task-lj-1-728-transfer-park`
**VERDICT:** still open. Not delivered elsewhere. Not proven futile. No shelve. Continuation: fill `LJ-1.728-SPLIT` at heavy.

## THE ARTIFACTS I OPENED

- `agents/tasks/LJ-1-728/runs/accept-1.out:10-22`. Conjuncts 1 to 6 held. Exit 0. `obligations_delta 0`, `obligations_open 1`. `agda_vacuous true`. `heap_wall false`. No `.agda` at the obligation path, so conjunct 1 did not run the term. Own files 22, including `Probe728.agda.txt`.
- `agents/tasks/LJ-1-728/lj-1.728-report.md:9-21`. Heap wall at wide. The obligation is not inhabited. The probe is `.agda.txt`. The wall is not Convert's body: every walling run hole-shielded the conversion.
- `lj-1.728-report.md:97-107`. Ladder: frame hole-body 1.62 GB EXIT=42 (`sd-1`); membership 1.68 GB EXIT=42 (`sh-1`); `si-2` and `full-1` EXIT=251 at the 2 GB cap.
- `runs/full-1.out:4-8`. Heap exhausted, 4 GB RTS asked, 2 GB cap, 382.82 s, RSS 2,505,392,128.
- `runs/si-2.out:4-8`. Same cap, 499.25 s, RSS 2,561,998,848. Conversion hole-shielded.
- `runs/sd-1.out:8`. RSS 1,622,016,000, designed hole.
- `Probe728.agda.txt:196-210`. The term is written and aliased at the top level.
- `.pod-state/state.json:37534`. Status PARKED.
- `dev/pod/queue.toml` already holds `LJ-1.728-SPLIT` with no brief.

## WHY THIS IS NOT A SHELVE

1. **Not delivered elsewhere.** No other task closed GO on `grounded-from-complete`. Supply 0.
2. **Not proven futile as a term.** The report refuses a `review-of` for that reason (`lj-1.728-report.md:160-166`). The statement is untouched. W3's Convert-application question is answered: the wall precedes the application. A heap wall at wide is not a proof the term is false.

A30 situation 2 needs a different task's proof that this route cannot succeed as a term. 718 walled the hypothesised Convert. 728 measured that Convert is not the wall. That does not settle the constructed composition. Heavy has not run.

## WHAT I QUEUE

`[LJ-1.728-SPLIT]`, brief `agents/tasks/LJ-1-728-SPLIT/LJ-1.728-SPLIT.md`, `agda_tier: heavy`. Transcribe the written term. One Agda process. Do not hypothesise Convert. If heavy closes, rename to `.agda` and the meter reads the name. If heavy walls, the next move is a frame split, not a fourth Convert wrap.
