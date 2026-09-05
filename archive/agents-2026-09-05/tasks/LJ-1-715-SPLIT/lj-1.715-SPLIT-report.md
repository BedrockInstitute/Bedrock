# LJ-1.715-SPLIT report: the worktree landing transcribed, Everything floored

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.715-SPLIT
obligation: agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda::bound2-in-limit
verdict: **GO on the term, PARK on the accept arm** (branch `heap-wall-park`).
The obligation typechecks: `runs/probe715split.out`, EXIT=0, 1.04 s, one Agda
process at the pane's heavy caliber `-A64m -I0 -M4g`. The landed master checks
in place: `runs/ordinal-final.out`, EXIT=0, 0.82 s. The transcription is
verbatim: `diff` against the 715 worktree master reports the files identical,
and `bound2` is untouched. The floor the brief commissioned closed the open
question: Everything at this cap and one process does NOT accept the 33 lines.
It dies at `L.Condensation`, heap exhausted, EXIT=251, and the controlled
rerun without the lines CLOSES, EXIT=0, 111.91 s. Full split verdict and the
attribution control: `agents/tasks/LJ-1-715-SPLIT/review-of-bound2-in-limit.md`.

## 1. WHAT THE DISPATCH BUILT

Three deliverables, in the brief's write scope only.

1. `src/L/Ordinal.lagda.md`, one new fence inserted after `bound2`'s, before
   `## Members`, now at `src/L/Ordinal.lagda.md:199-230`. It carries the two
   names verbatim from the worktree: `IsLimit` at `:205-211` and
   `bound2-in-limit` at `:221-229`, with their comments. The brief's
   `Transcribe. Do not re-invent.` was enforced by tooling: after the edit,
   `diff` against `.pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md`
   reports the two masters identical. `bound2` at `:185-197` is byte-identical
   to its pre-change state. The file gained 33 lines by `git diff --stat`, 27
   of them non-blank in-fence lines the ledger's way.
2. `agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda`, the mirror of the worktree
   probe: the obligation stated over the exported `IsLimit` and discharged by
   `bound2-in-limit-src`, plus the small-layer second theorem the worktree
   probe measured, transcribed and re-checked here rather than assumed. Two
   comment path updates only: the module is `LJ-1-715-SPLIT.Probe715Split`,
   and the predecessor run citations now name the worktree path, because the
   715 `runs/` directory is not present in this worktree.
3. `agents/tasks/LJ-1-715-SPLIT/runs/`, five run records, every one one Agda
   process under the pane caliber, taken sequentially.

No extra `.agda` diagnostic was written. Nothing outside the write scope was
modified; `src/Everything.lagda.md` was floored and never edited.

## 2. THE LADDER, MEASURED

| id | question | verdict | evidence |
|---|---|---|---|
| probe715split | does the mirror close against the landed master? | YES, both theorems, EXIT=0, 1.04 s | runs/probe715split.out |
| ordinal-final | does the delivered master check in place? | YES, EXIT=0, 0.82 s | runs/ordinal-final.out |
| everything-floor (A) | does Everything at heavy `-M4g`, one process, accept the 33 lines? | NO: `L.Condensation` heap exhausted, EXIT=251, 217.07 s | runs/everything-floor.out |
| everything-floor-nolines (B) | does the same build close WITHOUT the lines? | YES: EXIT=0, 111.91 s | runs/everything-floor-nolines.out |
| everything-floor-warm (C) | does A's wall survive a warmer build? | YES it survives: same site, EXIT=251, 196.66 s | runs/everything-floor-warm.out |

**The attribution, stated because it changes what the next brief owns.** Runs
B and C are the controlled pair: identical warmth profile, identical build
order, and one source difference, the 33 lines. B closes; C dies where A died.
So the wall is the marginal cost of two exported names on `L.Ordinal`'s
forty-dependent frame at the 4 GB cap, and it is not a cold-build accident.
The 2026-08-23 import-trim cure was re-measured at its own site first: the new
fence consumes only names the file already imported (`sett`, `⋃_` and `sucV`
stand at `src/L/Ordinal.lagda.md:52-56`, and `suc-ord` at `:96` already uses
`sucV`), so there was nothing to trim. No fence restructuring was attempted:
the brief mandates verbatim transcription, forbids touching `bound2`, and
pre-declares this wall as the split's expected finding, so an `abstract` seal
or a restated `IsLimit` would be the third landing the brief forbids.

## 3. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief asked whether Everything at heavy `-M4g` and one Agda process
accepts the 33 lines. Measured: NO, at two build states, at a cost of 217.07 s
and 196.66 s to the wall, against 111.91 s for the whole tree without them.
The brief's own frame already priced this outcome: premise 3 recorded the
accept arm's rc 251 at 206.66 s under concurrency 2
(`dev/pod/transitions/2026-08.jsonl:4925`, which I read at the main tree,
`/Users/alsg/Agentic/Bedrock`, where the line stands; this worktree's copy has
4840 lines). This dispatch reproduces the wall at ONE process and measures the
without-lines control the park never had.

## 4. W2 ANSWER

The mathematics is written once at the generic carrier and instantiated once.
`IsLimit`'s closure clauses quantify over arbitrary index types and families;
`bound2-in-limit` instantiates them at `Lift Bool`; the probe states the
obligation verbatim and forwards to the src lemma, holding no copy of the
proof. The one duplication risk, the small-layer theorem in the probe, states
its own clauses locally and was transcribed from the worktree probe with its
measurement role intact. No deadline conflict arose and nothing was weakened.

## 5. HANDOFF

- **GO on the term unblocks `[LJ-1.711]` exactly as the brief projected**, and
  the landing sits in the working tree ready for the program's commit.
- **The park now has its missing measurement.** The 715 park knew the wall
  only at concurrency 2; it now has the one-process wall, the without-lines
  control, and the warm rerun. The finding is about the frame: at heavy
  `-M4g`, `L.Ordinal`'s forty dependents sit close enough to the cap that two
  small exported names tip `L.Condensation` over. The cure is a frame
  decision, and it is outside this task's write scope.
- **Price of the landing, for the ratio record.** 27 non-blank in-fence lines
  added (ledger's way), 33 by `git diff --stat`; the master checks at 0.82 s
  warm, 1.04 s through the probe. The bar row `sys-dd24-ratio-bar` requires
  `exit_code = 0` and `heap_wall = false`; this dispatch parks on
  `heap_wall = true`, so the bar cannot fire, and the figures are recorded
  here for the ledger rather than claimed under it.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: READ, at `:34`, the DD24 row. Quote at that
  line: "THE QUALITY BAR IS SECONDS PER LINE". Used for the bar's provenance,
  which the brief invokes against this dispatch's return.
- `archive/dev/ORCHESTRATION.md`: declined, not read. The report form this
  return follows is the live one in the slot file and the 715 precedent; no
  archived orchestrator rule bears on a transcription and a floor.
- `archive/dev/PLAN-archived.md`: declined, not read. The brief's scope was
  executed as named and no planning question arose.
- `archive/dev/STATUS-archived.md`: declined, not read. Standing status lives
  in `dev/pod/screen.toml`, which the program injected.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor record
  this task needed is the live 715 worktree and the 710 review, both named in
  the brief.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. The naming
  of the new exports was settled by transcription from the worktree and the
  chapter's `IsOrd` family precedent; no glossary question was open, and this
  slot may not add glossary entries.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. The task
  states no formula and fills no level slot.
- `dev/literature/primary-sources.md`: declined, not read. The proof came from
  the worktree, not from a primary source.
- `dev/literature/devlin-errata.md`: declined, not read. No Devlin passage was
  consulted; the lemma channels `IsLimit`'s own clauses.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No citation duty arose
  in a code-only dispatch.
