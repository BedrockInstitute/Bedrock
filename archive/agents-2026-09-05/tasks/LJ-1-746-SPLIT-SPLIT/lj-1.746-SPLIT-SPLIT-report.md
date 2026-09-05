# LJ-1.746-SPLIT-SPLIT report: graph-mirror, the green spelling packaged

## THE VERDICT

**GO.** `graph-mirror : StepKilledGen → ApproxSlot × StepSlot` typechecks in a
fresh file, body `approx-split gen , step-split gen`
(Probe746SplitSplit.agda:27-28). rc 0 in 3.17 s, peak RSS 778534912 B
(runs/probe746splitsplit.out:4,5,22), pane caliber `-A64m -I0 -M2g` echoed at
runs/probe746splitsplit.out:1. The obligation closes: obligations 1 to 0. No
heap wall. No file in `src/` touched (`git status --short src/` is empty). Not
inhabited, as the brief demands: `GraphAt`, `bound-in-stage-at-empty`,
`Completeness`, `completeness-from-pack`; the names occur only inside
comments in this task's files. `review-of-graph-mirror.md` is not written,
because there is no NO-GO to state.

## THE DELIVERABLE

- `Probe746SplitSplit.agda` -- the obligation. Two imports
  (Probe746SplitSplit.agda:24-25), one signature and one one-line body
  (Probe746SplitSplit.agda:27-28). No proof, no conversion, no assembly.
- `runs/Amb7.agda`, `runs/EraseIrr.agda`, `runs/PT.agda` -- verbatim vendor
  copies of 746-SPLIT's three green modules, renamed to this task's namespace.
  See THE VENDOR DECISION.
- `runs/Floor746SplitSplit.agda.txt` -- the floor instrument: the probe's
  exact imports and signature with a hole for the body
  (Floor746SplitSplit.agda.txt:25-26). Named `.agda.txt` because it cannot
  typecheck by design.
- `runs/ScopePT.agda` and `runs/ScopePT-PTonly.agda.txt` -- the two scope
  instruments that measure the scoping fact below.
- `runs/vendor.diff` -- the verbatim-ness record of the vendor step.
- `runs/*.out` -- every run record this report cites.

## THE VENDOR DECISION

The brief's named import `LJ-1-746-SPLIT.runs.PT` has no file to resolve to in
this worktree: `agents/tasks/LJ-1-746-SPLIT/` is uncommitted in the tree at
this worktree's HEAD (`79efb74a`), so the directory is absent here. This is
the same defect 746-SPLIT measured for its own predecessor, and the cure is
the same one that task measured: vendor the green modules verbatim under the
consuming task's namespace. Re-applied at this site and re-measured, per the
Boundary rule that a measured cure is re-measured at its own site.

Copied from the 746-SPLIT working files, with `sed
s/LJ-1-746-SPLIT/LJ-1-746-SPLIT-SPLIT/g` and nothing else:

- `runs/Amb7.agda`: the module line only (vendor.diff:24-32).
- `runs/EraseIrr.agda`: the module line only (vendor.diff:34-42).
- `runs/PT.agda`: the module line and its two self-namespace imports
  (vendor.diff:3-22); bodies verbatim. `ApproxSlot` stays at runs/PT.agda:63,
  `StepSlot` at runs/PT.agda:67, `approx-split` at runs/PT.agda:72,
  `step-split` at runs/PT.agda:78, the same rows the predecessor reported.

No rebuild: the three bodies are diff-verbatim, and every one re-measured
green here (warm-EraseIrr.out:22, warm-Amb7.out:22, warm-PT.out:22). PT's own
price reproduced: 90.62 s here against the 90.92 s the predecessor measured
(runs/warm-PT.out:4).

## THE SCOPING FACT (new, measured; for the next brief)

**`runs/PT` does not re-export `Amb7`'s `StepKilledGen` into a consumer's
scope, in Agda 2.8.0, although PT's import of Amb7 is an `open import`
(runs/PT.agda:33).** A file importing PT alone and asking for `StepKilledGen`
fails scope: NotInScope at 11.5-18, rc 42 (runs/scope-pt.out:4,27). The same
file with the direct `open import LJ-1-746-SPLIT-SPLIT.runs.Amb7` added is
rc 0 in 3.12 s (runs/scope-pt2.out:4,22). The probe therefore imports Amb7
directly beside PT (Probe746SplitSplit.agda:24-25), which is the spelling
PT2 used at the predecessor's site (main-tree
`agents/tasks/LJ-1-746-SPLIT/runs/PT2.agda.txt:26-27`, read this dispatch).

This cost one 3.28 s measurement to find and one 3.12 s measurement to close.
Later consumers of PT should import Amb7 beside it and not spend the
NotInScope round.

## MEASUREMENTS

ONE Agda process at a time, sequential, never two. `GHCRTS` was read from the
pane at every run and never set by this task; every `.out` line 1 shows
`-A64m -I0 -M2g`, the wide caliber. All runs are WARM: this worktree's
`_build` held no task interfaces, so the cone was warmed bottom-up first, each
module its own process. These numbers are comparable to each other and to the
predecessor's warm numbers, not to cold numbers.

| run | file | rc | wall | peak RSS | evidence |
|---|---|---|---|---|---|
| warm P652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 5.66 s | 900972544 B | runs/warm-p652.out:5,6,23 |
| warm Num | `agents/tasks/LJ-1-732/runs/Num.agda` | 0 | 1.07 s | 284196864 B | runs/warm-Num.out:4,5,22 |
| warm Amb1 | `agents/tasks/LJ-1-732/runs/Amb1.agda` | 0 | 17.65 s | 1409662976 B | runs/warm-Amb1.out:7,8,25 |
| warm Amb4a | `agents/tasks/LJ-1-732/runs/Amb4a.agda` | 0 | 3.65 s | 749289472 B | runs/warm-Amb4a.out:4,5,22 |
| warm Amb5 | `agents/tasks/LJ-1-732/runs/Amb5.agda` | 0 | 3.83 s | 693256192 B | runs/warm-Amb5.out:4,5,22 |
| warm Amb6 | `agents/tasks/LJ-1-732/runs/Amb6.agda` | 0 | 3.96 s | 694321152 B | runs/warm-Amb6.out:4,5,22 |
| warm Amb7a | `agents/tasks/LJ-1-732/runs/Amb7a.agda` | 0 | 3.62 s | 679198720 B | runs/warm-Amb7a.out:4,5,22 |
| warm EraseIrr (vendored) | `runs/EraseIrr.agda` | 0 | 0.86 s | 262225920 B | runs/warm-EraseIrr.out:4,5,22 |
| warm Amb7 (vendored) | `runs/Amb7.agda` | 0 | 3.32 s | 633143296 B | runs/warm-Amb7.out:4,5,22 |
| warm PT (vendored) | `runs/PT.agda` | 0 | 90.62 s | 1131560960 B | runs/warm-PT.out:4,5,22 |
| scope, PT only | `runs/ScopePT.agda` (variant 1) | 42 | 3.28 s | 696336384 B | runs/scope-pt.out:9,10,27 |
| scope, PT + Amb7 | `runs/ScopePT.agda` (variant 2) | 0 | 3.12 s | 778502144 B | runs/scope-pt2.out:4,5,22 |
| FLOOR | `runs/Floor746SplitSplit.agda.txt` | 42, designed | 3.22 s | 778403840 B | runs/floor746splitsplit-2.out:7,8,25 |
| **PROBE** | `Probe746SplitSplit.agda` | **0** | **3.17 s** | **778534912 B** | runs/probe746splitsplit.out:4,5,22 |

Floor discipline: the floor ran before the probe. Its only diagnostic is the
designed hole, UnsolvedInteractionMetas at the body
(runs/floor746splitsplit-2.out:4). Frame floor 3.22 s against probe 3.17 s:
the alias adds nothing measurable, exactly what a pure packaging should cost.
No import was trimmed: the probe's frame is PT's own frame, and PT is the
green module the brief orders consumed, not this task's to slim.

One invocation defect, corrected in the same dispatch: Agda 2.8.0 rejects the
`.agda.txt` extension outright (InvalidExtensionError,
runs/floor746splitsplit.out:3), so the floor instruments run as temporary
same-stem `.agda` copies, deleted after the run; the tracked artifact stays
`.agda.txt`. The predecessor's `.out` records show the same procedure
(main-tree `runs/floorB1.out:3`, "Checking ... FloorB1.agda").

## W2 ANSWER

Honored by reuse, not by rewriting. The generic vacuity mathematics stays in
746-SPLIT's green rows: `approx-part` and `step-part` are Amb7's and PT's,
consumed through PT's two transports (`approx-split`, runs/PT.agda:72;
`step-split`, runs/PT.agda:78). This dispatch wrote no lemma, no duplicate of
any generic statement, and no new mathematics: the write scope holds one
alias, three verbatim vendor copies, and measurement instruments.

## W3 ANSWER

**YES.** The packaged alias converts in a fresh file. The named mirror
`graph-mirror` is green at Probe746SplitSplit.agda:27-28 under the wide
caliber, and later briefs may consume it without spelling `GraphAt`. The NO-GO
binder the brief feared is not in the packaging: the one binder this task
found is the scope fact above, and it is closed with a one-line cure.

## ARCHIVE USED

- archive/dev/DD-archived.md: declined, not read. The vendor cure this task
  re-measured comes from the predecessor's live report at its own site, not
  from archived decisions.
- archive/dev/ORCHESTRATION.md: declined, not read. No question about loop
  operation arose; the brief fixed the whole target.
- archive/dev/PLAN-archived.md: declined, not read. No plan-level question
  arose for a one-alias packaging.
- archive/dev/TASKS-archived.md: declined, not read. Closed task history is
  not evidence here; the live predecessor report is.
- archive/dev/STATUS-archived.md: declined, not read. Standing status is
  screen.toml only, and no status question arose.

## LITERATURE USED

- dev/literature/devlin-errata.md: declined, not read. No Devlin citation is
  in play; the task packs an already measured spelling.
- dev/literature/glossary-review-2026-08.md: declined, not read. No
  translation term was chosen or queried.
- dev/literature/primary-sources.md: declined, not read. This is a code-only
  task and cites no primary source.
- dev/literature/rudimentary-functions.md: declined, not read. No new
  function is defined; the alias reuses PT's rows.
- dev/literature/BIBLIOGRAPHY.md: declined, not read. Nothing bibliographic
  is claimed.
