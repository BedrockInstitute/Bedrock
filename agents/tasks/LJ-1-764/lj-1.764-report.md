# LJ-1.764 report: conv0, the un-ascribed hull convert, exported at top level

## THE VERDICT

**GO.** `conv0` typechecks in this task's module with NO codomain ascription and
a top-level export, rc 0 in 10.41 s at peak RSS 1873444864 B, pane caliber
`-A64m -I0 -M4g` (runs/probe764-2.out:1,4,5,22). The obligation closes:
obligations 1 to 0. No heap wall: the peak is 1.87 GB against the 4 GB cap,
and no run approached the 1800 s cap. No file in `src/` was touched
(`git status --short src/` is empty; the only tree change is
`agents/tasks/LJ-1-764/`, untracked before this dispatch). No
`review-of-conv0.md` is written, because there is no NO-GO to state. Nothing
is postulated; the tree stays `--safe`.

## THE DELIVERABLE

- `Probe764.agda` -- the obligation. The imports and the `Build` scaffolding
  are the vendor file's, verbatim (runs/vendor.diff: every code row is
  context, no code row changed). The body is the opened Spend term, type
  inferred, at Probe764.agda:55. The export is one row at column 0,
  `conv0 = Build.conv0`, at Probe764.agda:59. The spelled record
  `⟨ _ ∷ _ ∷ _ ∷ [] P652.⊨ₚ P667.matrix₃ ⟩` appears nowhere in the file. No
  `Convert` hypothesis. No `grounded-from-complete`.
- `runs/Floor764.agda.txt` -- the floor instrument: the probe's exact frame
  with a hole standing in for the term (coder law, owner ruling 2026-08-23).
  Named `.agda.txt` because it cannot typecheck by design. The hole is the
  only difference from the probe's shape (Floor764.agda.txt:47).
- `runs/run.sh` -- the run instrument: one Agda process per invocation, the
  caliber read from the pane and never set, 1800 s `timeout` wrapped inside
  `/usr/bin/time -l`.
- `runs/vendor.diff` -- the verbatim-ness record of the vendor step.
- `runs/*.out` -- every run record this report cites.

## THE VENDOR DECISION

The brief's premise basis files under
`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT/` do not exist in this
worktree: `find agents/tasks -name "*728*"` returns nothing, and the
admitting commits touched only `dev/pod/table.toml` (51b14580, 26443f41,
`git show --stat`). The vendor file itself needs no absent directory: the
program delivered `VendorB4.agda.txt` inside this task's directory, and its
header carries the measured verdict this brief cites, green at `-M4g`,
12.51 s at RSS 1.93 GB (VendorB4.agda.txt:10). The transcription is a rename
of the module line plus a rewritten header plus the 3-line export
(runs/vendor.diff); every import, the whole `Build` telescope, the `Spend`
opening and the body row are byte-identical. Re-measured here per the
Boundary rule that a measured cure is re-measured at its own site.

## MEASUREMENTS

ONE Agda process at a time, sequential, never two. `GHCRTS` was read from the
pane at every run and never set by this task; every `.out` line 1 shows
`-A64m -I0 -M4g`, the heavy caliber. This worktree's `_build` held no task
interfaces, so the cone was warmed bottom-up first, each module its own
process. All numbers below are WARM.

| run | file | rc | wall | peak RSS | evidence |
|---|---|---|---|---|---|
| warm Probe652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 4.75 s | 1083523072 B | runs/warm-p652.out:5,6,23 |
| warm Probe520 | `agents/tasks/LJ-1-520/Probe520.agda` | 0 | 2.04 s | 644743168 B | runs/warm-p520.out:4,5,22 |
| warm Probe680 | `agents/tasks/LJ-1-680/Probe680.agda` | 0 | 0.75 s | 273645568 B | runs/warm-p680.out:4,5,22 |
| warm W3 | `agents/tasks/LJ-1-667/runs/W3.agda` | 0 | 7.58 s | 1588723712 B | runs/warm-w3.out:4,5,22 |
| warm Probe667 | `agents/tasks/LJ-1-667/Probe667.agda` | 0 | 7.84 s | 1489879040 B | runs/warm-p667.out:4,5,22 |
| warm Probe673 | `agents/tasks/LJ-1-673/Probe673.agda` | 0 | 100.48 s | 1419018240 B | runs/warm-p673.out:4,5,22 |
| warm Probe686 | `agents/tasks/LJ-1-686/Probe686.agda` | 0 | 2.69 s | 669843456 B | runs/warm-p686.out:4,5,22 |
| warm Probe689 | `agents/tasks/LJ-1-689/Probe689.agda` | 0 | 0.75 s | 262717440 B | runs/warm-p689.out:4,5,22 |
| warm Probe692 | `agents/tasks/LJ-1-692/Probe692.agda` | 0 | 109.51 s | 1839054848 B | runs/warm-p692.out:4,5,22 |
| FLOOR | `runs/Floor764.agda.txt` | 42, designed | 10.47 s | 1838989312 B | runs/floor764.out:155,156,173 |
| probe, run 1 | `Probe764.agda` (pre-fix header) | 0 | 10.68 s | 1873477632 B | runs/probe764.out:4,5,22 |
| **PROBE** | `Probe764.agda` | **0** | **10.41 s** | **1873444864 B** | runs/probe764-2.out:4,5,22 |

Floor discipline: the floor ran before the probe. Its only diagnostics are
the designed hole: UnsolvedConstraints at floor764.out:4 and the unsolved
metas at the body, floor764.out:148,152. Frame floor 10.47 s against probe
10.41 s: the term and the export add nothing measurable, which is what a
pure reference should cost. The frame, not the term, is the whole price, and
the frame is Probe692's interface plus the section scaffold. No import was
trimmed: the frame is the vendor file's own frame, and the brief orders that
file transcribed.

One invocation defect, corrected in the same dispatch: Agda 2.8.0 rejects the
`.agda.txt` extension, so the floor instrument ran as a temporary same-stem
`.agda` copy, deleted after the run; the tracked artifact stays `.agda.txt`.
No file that cannot typecheck rests at a `.agda` path (`ls
agents/tasks/LJ-1-764/runs/`: only `Floor764.agda.txt` and the `.out`
records).

The probe ran twice: run 1 measured the file before a comment-only citation
fix in its header (the vendor measurement's line cite, 12 to 10). Run 2 is
the tracked text; the two agree, 10.68 s against 10.41 s.

## W2 ANSWER

Honored by consumption, not by rewriting. The generic transport is
`hull-convert` in `LJ-1-689.Probe689`; `[LJ-1.692]` instantiated it at
`matrix₃` and delivered `hull-convert-at-matrix` (Probe692.agda:63 through
Probe692.agda:68). This dispatch wrote no lemma, no duplicate of any generic
statement, and no new mathematics: the write scope holds one reference row,
one export row, and measurement instruments. That is DD4's own discipline,
maximum reuse: `archive/dev/DD-archived.md:22`.

## W3 ANSWER

**YES.** The un-ascribed convert, exported at top level, checks at `-M4g` in
this task's module: rc 0 in 10.41 s, peak 1873444864 B
(runs/probe764-2.out:4,5,22). The export costs nothing measurable against the
floor (10.41 s against 10.47 s). A later brief may consume `conv0` from
`LJ-1-764.Probe764` without spelling the record type, and the next named
step, `grounded-from-complete` through this export, is unblocked. The B8
comparison stays the wall it was four times measured; this dispatch
retouched nothing of that shape.

## SURVEY CHECK

This worktree has no `.venv`; the pinned interpreter is the repository's own
at `/Users/alsg/Agentic/Bedrock/.venv/bin/python` (Python 3.11.16). The
command run, before return:

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-764
    check-survey-quotes: LJ-1-764 clean (0 note(s), 0 defect(s))

## ARCHIVE USED

- archive/dev/DD-archived.md:22: READ, the reuse rule the W2 answer
  reports against. "MAXIMUM REUSE is the architecture's objective, and it is
  the same rule as WRITE IT GENERIC."
- `archive/dev/ORCHESTRATION.md`: declined, not read. The one-process and
  caliber rules have their canonical home in the coder slot file, and this
  task needed no loop-operation history.
- `archive/dev/PLAN-archived.md`: declined, not read. No plan-level question
  arose for a one-reference probe.
- `archive/dev/TASKS-archived.md`: declined, not read. Closed task history of
  the retired route; this task's predecessors are named in its own brief.
- `archive/dev/STATUS-archived.md`: declined, not read. Standing status is
  `dev/pod/screen.toml` alone, and no L3-era row bears on a packaging probe.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read beyond a
  relevance grep. This task wrote no mathematical prose and needed no term.
- `dev/literature/rudimentary-functions.md`: declined, not surveyed. The
  task is a packaging probe over delivered Agda; no Devlin content was
  consulted.
- `dev/literature/primary-sources.md`: declined, not surveyed. Same reason:
  no mathematical prose was written or checked.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not surveyed. No source question
  arose.
- `dev/literature/devlin-errata.md`: declined, not surveyed. Same reason.
