# LJ-1.767-SPLIT-SPLIT report: grounded-from-complete, reading the only packed factor

## THE VERDICT

**GO.** `grounded-from-complete` at the brief's SPLIT-SPLIT Sigma, the
reading the only packed factor, typechecks at `-M4g`: rc 0 in 210.63 s at
peak RSS 1865793536 B, pane caliber `-A64m -I0 -M4g`
(runs/probe767splitsplit-1.out:4,5,22). The obligation closes:
obligations 1 to 0, `grounded-from-complete` supplied at the file's top
level (Probe767SplitSplit.agda:148). No heap wall: the peak is 1.87 GB
against the 4 GB cap, and no run approached the 1800 s cap. No file in
`src/` was touched (`git status --short src/` is empty; the only tree
change is `agents/tasks/LJ-1-767-SPLIT-SPLIT/`, untracked before this
dispatch). No `review-of-grounded-from-complete.md` is written, because
there is no NO-GO to state.

The W3 probe is thereby settled: the widest unmeasured term was this
Sigma, and the brief's own estimate, "S5 plus conv0 in that slot", was
right in kind and near in price. The wall law of 767-SPLIT held at this
site with no exception: a first factor real with no other real component
costs about twice the floor (210.63 s against the floor's 110.70 s), and
the wall condition, a real first factor WITH a further real component,
could not arise, because the Sigma has no further component.

`Completeness` stays a HYPOTHESIS, never inhabited. The soundness
argument `sound` stays bound and unused by the composition. `conv-at-Lδ`
was never approached; `amb` was never tried; `mkWit`'s spelled codomain
was never restored; no subst along either code equation stands anywhere
in the term.

## THE DELIVERABLE

- `Probe767SplitSplit.agda` -- the obligation, GREEN. The imports and the
  `Build` scaffolding are the vendor pack's, verbatim. The obligation's
  type is the brief's type, spelled once at
  Probe767SplitSplit.agda:105-112: the reading alone packed under the two
  `PT.rec` binders. `conv0` is un-ascribed, its codomain a solved meta
  (Probe767SplitSplit.agda:119-122). The packing stands inline
  (Probe767SplitSplit.agda:134-144): the tuple is `ca , cp , fst a ,
  conv0 ca cp a sat`, nothing else; the hull-membership witness of
  `hullClosed` is discharged by the wildcard and names no slot. The
  export is one row at column 0, `grounded-from-complete =
  Build.grounded-from-complete`, at Probe767SplitSplit.agda:148.
- `runs/FrameSplit.agda` -- the vendored frame, transcribed. Typechecks:
  GREEN at this site (runs/framesplit.out:4,5,22).
- `runs/HullHalfSplit.agda` -- the vendored hull half, transcribed,
  import retargeted. Typechecks: GREEN at this site
  (runs/hullhalfsplit.out:4,5,22).
- `runs/S5Remain.agda.txt` -- the brief's re-measure instrument, the
  vendor S5 shape at this site, its four designed holes intact. Its only
  diagnostics are the designed holes
  (runs/s5remain.out:4-9, at `S5Remain.agda:166.28-167.33`).
- `runs/FloorSplit.agda.txt` -- the floor instrument of the NEW type,
  the probe with the body a designed hole. Its only diagnostic is the
  designed hole (runs/floorsplit.out:4-6, at `FloorSplit.agda:135.55-56`).
- `runs/run.sh` (protocol runner, 1800 s cap). No diagnostics ran; no
  wall met the restructure clause, so no `diag.sh` instrument was
  needed. The runner stays for any re-dispatch.
- The tree carries exactly two `.agda` files plus the green obligation:
  the two interfaces. A `.agda.txt` file cannot typecheck (both by
  design); a temporary same-stem `.agda` copy ran each of them and was
  deleted at once after its run.

## THE VENDOR DECISION

The premise basis directories `agents/tasks/LJ-1-767-SPLIT/`,
`agents/tasks/LJ-1-765-SPLIT/` and `agents/tasks/LJ-1-764/` do not all
exist in this worktree (only `LJ-1-764/` does). The 767-SPLIT and
765-SPLIT reports were read in the main checkout:
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-767-SPLIT/lj-1.767-SPLIT-report.md`
and
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-765-SPLIT/lj-1.765-SPLIT-report.md`.
The vendor files delivered in this task directory carry the measured
verdicts in their own headers, and no absent directory is needed.

- `VendorFrame.agda.txt` transcribed to `runs/FrameSplit.agda`: module
  renamed to `LJ-1-767-SPLIT-SPLIT.runs.FrameSplit`, header rewritten;
  `diff` from the module line down shows exactly one differing line, the
  module line.
- `VendorHull.agda.txt` transcribed to `runs/HullHalfSplit.agda`: module
  renamed, the Frame import retargeted to
  `LJ-1-767-SPLIT-SPLIT.runs.FrameSplit`, header rewritten; `diff` shows
  exactly two further differing lines, the module line and the import.
- `VendorS5.agda.txt` transcribed to `runs/S5Remain.agda.txt`: module
  renamed to `LJ-1-767-SPLIT-SPLIT.runs.S5Remain`, the two interface
  imports retargeted, header rewritten; `diff` from the OPTIONS line down
  shows exactly three differing lines, the module line and the two
  imports. The designed holes stay.
- `runs/FloorSplit.agda.txt` is this task's floor instrument: the NEW
  obligation file with the body a designed hole (everything the probe
  elaborates besides the packing stands above it).
- `Probe767SplitSplit.agda.txt` starts as the obligation at the brief's
  type, reading the only packed factor; renamed to `.agda` for its run
  once the floor is priced.

## 1. THE PRICES

All runs under `runs/run.sh`, one Agda process per row, pane caliber,
1800 s cap. The warm-up rows paid this worktree's cold closure (its
`_build/2.8.0/agda/agents/tasks/` held none of the four probes) and are
environment, not prices.

| run | file | exit | time | peak RSS | evidence |
|---|---|---|---|---|---|
| warm Probe652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 4.43 s | 900562944 B | runs/warm-p652.out:5,6,23 |
| warm Probe667 | `agents/tasks/LJ-1-667/Probe667.agda` | 0 | 13.04 s | 2057322496 B | runs/warm-p667.out:6,7,24 |
| warm Probe673 | `agents/tasks/LJ-1-673/Probe673.agda` | 0 | 96.65 s | 1402241024 B | runs/warm-p673.out:4,5,22 |
| warm Probe692 | `agents/tasks/LJ-1-692/Probe692.agda` | 0 | 107.28 s | 1872199680 B | runs/warm-p692.out:7,8,25 |
| frame | `runs/FrameSplit.agda` | 0 | 12.06 s | 2008989696 B | runs/framesplit.out:4,5,22 |
| hull half | `runs/HullHalfSplit.agda` | 0 | 205.54 s | 1781334016 B | runs/hullhalfsplit.out:4,5,22 |
| S5 re-measure | `runs/S5Remain.agda.txt` | 42, designed | 112.04 s | 1857421312 B | runs/s5remain.out:4,10,11,28 |
| floor, new type | `runs/FloorSplit.agda.txt` | 42, designed | 110.70 s | 1868316672 B | runs/floorsplit.out:4,7,8,25 |
| THE RUN | `Probe767SplitSplit.agda` | 0 | 210.63 s | 1865793536 B | runs/probe767splitsplit-1.out:4,5,22 |

S5 re-measured at this site matches the vendor site within noise (112.04 s
here, 112.41 s there). Its only diagnostics are the four designed holes
(runs/s5remain.out:4-9, the `UnsolvedInteractionMetas` block at
`S5Remain.agda:166.28-167.33`): the first factor's real check alone is
free at this site, as the 767-SPLIT grid law predicted.

The floor of the new type is 110.70 s with about 2.1 GB of headroom
(runs/floorsplit.out:7,8; its only diagnostic is the designed hole,
runs/floorsplit.out:4, at `FloorSplit.agda:135.55-56`), so the probe run
went ahead. It is GREEN, and the bracket closes: the interfaces, the
type, `conv0`'s inferred codomain and the export cost about 110 s; the
complete tuple elaborated under the two `PT.rec` binders, with the
reading REAL in its only slot, costs about 211 s. The delta of the real
reading over the holed one is about 100 s, one floor again. The wall
never appeared: 1.87 GB peak against the 4 GB cap.

## 2. THE W2 ANSWER

DD4's rule is "MAXIMUM REUSE is the architecture's objective, and it is
the same rule as WRITE IT GENERIC" (archive/dev/DD-archived.md:22). The
dispatch answers it: the mathematics stands ONCE at the generic carrier
and this probe instantiates it. The carrier is the vendored hull frame,
one hull stage, whose interfaces carry the repaired telescope,
`Completeness`, `SatIn`, `HullM`, `codeOf` and `hullClosed`; both towers
share Probe652, Probe667, Probe673 and Probe692 through it. The
obligation's type is spelled exactly once (Probe767SplitSplit.agda:105),
and the packing is four inline components over those shared names. No
AC-or-GCH-specific fact is duplicated; nothing was written fixed that
the carrier already carried.

## 3. THE ENVIRONMENT AT DISPATCH

- No Agda process at dispatch (`pgrep -x agda` empty); the same check
  empty between every run.
- Pane caliber `GHCRTS=[-A64m -I0 -M4g]` (heavy), read at dispatch, never
  set or changed by this task.
- This worktree's `_build/2.8.0/agda/src/` is warm (305 `.agdai` files),
  and `_build/2.8.0/agda/agents/tasks/` held none of Probe652, Probe667,
  Probe673, Probe692, so the cold closure was paid in the warm-up runs of
  section 1, not inside any price row.
- `sysctl vm.swapusage` at dispatch: total 5120.00M, used 3945.31M, free
  1174.69M.

## 4. WHAT THE NEXT BRIEF NEEDS

- The obligation is CLOSED at this site. The GO outcome the brief named
  stands: a later brief may price `LsetGrounded` FROM this reading,
  without packing a second real factor under the two `PT.rec` binders.
- The wall law of 767-SPLIT now has its constructive half measured at
  this site too: first factor real, NO further real component, about 2x
  the floor (210.63 s against 110.70 s). The walling half (first factor
  real WITH a further real component) is unchanged and stays measured
  only at the SPLIT site; this dispatch never met it, because the Sigma
  has no further component.
- The supplied pieces stay on the meter at this site: frame 12.06 s
  (runs/framesplit.out:4,5), hull half 205.54 s
  (runs/hullhalfsplit.out:4,5), S5 112.04 s (runs/s5remain.out:10,11),
  floor 110.70 s (runs/floorsplit.out:7,8), the run 210.63 s
  (runs/probe767splitsplit-1.out:4,5). The cone is now WARM: a
  re-dispatch here starts in the 8 to 12 s class, not at 226 s.
- The four walls of the ascribed shape (B2, B8, conv-1, amb-1) stand
  untouched; `conv-at-Lδ` was never approached; `mkWit`'s spelled
  codomain was never restored; `amb` was never tried; `Completeness`
  was never inhabited; `sound` was never used.

## 5. THE RATIO BAR

The write scope of this task carries no ` ```agda ` fence: the obligation
and the instruments are raw `.agda` and `.agda.txt` files (each counts 0
by the bar's own rule) and this report is prose. The divisor of this
return is 0 and the bar cannot fire.

## 6. SURVEY CHECK

Ran before return, as ordered, after the two survey blocks below were
written. This worktree has no `.venv` of its own; the pinned interpreter
of the main checkout (`/Users/alsg/Agentic/Bedrock/.venv/bin/python`,
Python 3.11.16) ran the gate. One run, clean:

```text
check-survey-quotes: LJ-1-767-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - READ. DD4's row, the rule the W2
  answer reports against: "| DD4 | **MAXIMUM REUSE is the architecture's
  objective, and it is the same rule as WRITE IT GENERIC.**"
- archive/dev/ORCHESTRATION.md - declined, not read. The one-process and
  caliber rules have their canonical home in the coder slot file, and
  this task needed no loop-operation history.
- archive/dev/PLAN-archived.md - declined, not read. No plan-level
  question arose in a measurement dispatch.
- archive/dev/TASKS-archived.md - declined, not read. This task's
  predecessors are named in its own brief, and their reports were read
  in the main checkout (the vendor decision section above).
- archive/dev/STATUS-archived.md - declined, not read. Standing status
  is `dev/pod/screen.toml` alone, and no pre-pod row bears on a packing
  probe.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md` - declined, not read
  beyond a relevance grep. This dispatch wrote no mathematical prose and
  coined no term.
- `dev/literature/rudimentary-functions.md` - declined, not surveyed.
  The dispatch is a measurement over delivered Agda; no Devlin content
  was consulted.
- `dev/literature/fine-structure.md` - declined, not surveyed. Same
  reason: no fine-structure content was interpreted or judged.
- `dev/literature/BIBLIOGRAPHY.md` - declined, not surveyed. No source
  question arose in a transcription, a re-measure and a green run.
- `dev/literature/primary-sources.md` - declined, not surveyed. Same
  reason: no literature content was consulted or judged.
