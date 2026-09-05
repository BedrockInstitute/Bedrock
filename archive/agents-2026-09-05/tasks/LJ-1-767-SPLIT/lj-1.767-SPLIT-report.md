# LJ-1.767-SPLIT report: grounded-from-complete at code coordinates, no membership slot

## THE VERDICT

**NO-GO. HEAP WALL. THE MEMBERSHIP COMPONENT WAS NOT THE WALL.**
`grounded-from-complete` at the brief's SPLIT Sigma does not typecheck at
`-M4g`: the ordered run hit the 1800 s cap with peak RSS 4638425088 B, above
the 4 GB cap (runs/probe767split-1.out:4,5,22, `EXIT=124`). The wall
signature is the 767 protocol run's own (1800.11 s, 4642603008 B,
`runs/probe767-1.out:4,5,22` of that task): dropping `⟨ z ∈ˢ HS.M ⟩` from
the Sigma and `a∈H` from the packing changed nothing measurable at the wall.

The brief's premise 1 is FALSIFIED by measurement. The wall is not the
membership slot; it is the SIGMA'S FIRST FACTOR. Seven in-dispatch
instruments (section 3) state the law: **a packing walls iff its first
factor is a real term and at least one further component is real; it greens
iff the first factor itself is a hole.** At this Sigma the first factor
`⟨ Lset δ ∈ˢ HS.M ⟩` admits exactly one filler in scope, the hypothesis
variable `Lδ∈M`, and the deliverable must supply it real with no hole
permitted. So no permitted shape can carry the term, and the shapes that
would be permitted all wall (R1, R4).

Per the brief: this NO-GO is a heap wall, so it stops this Sigma at `-M4g`.
It is a RESOURCE WALL, not a stated refutation, so no
`review-of-grounded-from-complete.md` is written. `conv-at-Lδ` stays
uninhabited, `amb` stays untried, `mkWit`'s spelled codomain stays
unrestored, `Completeness` stays a hypothesis, and nothing landed in `src/`
(`git status --short src/` is empty; the only tree change is
`agents/tasks/LJ-1-767-SPLIT/`). `obligations` stay at 1:
`grounded-from-complete` keeps supply 0. The program should route this
return to `heap-wall-park` (park_and_split).

## THE DELIVERABLE

- `Probe767Split.agda.txt` -- the W3 term at the brief's SPLIT shape: the
  two loaded interfaces, the obligation's type spelled once with the
  membership component dropped, `conv0` un-ascribed (codomain a solved
  meta), the packing inline, no `mkWit`, the witness's membership proof
  discharged by the wildcard pattern, the top-level export. It does not
  typecheck (the wall), so it rests at `.agda.txt`, never `.agda`.
- `runs/FrameSplit.agda` -- the vendored frame, transcribed. Typechecks:
  GREEN at this site (runs/framesplit.out:4,5,22).
- `runs/HullHalfSplit.agda` -- the vendored hull half, transcribed, import
  retargeted. Typechecks: GREEN at this site
  (runs/hullhalfsplit.out:4,5,22).
- `runs/D7MemHoledSplit.agda.txt` -- the D7 re-measure instrument the brief
  ordered (membership slot holed, `conv0` real, OLD Sigma). Designed hole;
  run under the protocol runner, so its number is a price.
- `runs/FloorSplit.agda.txt` -- the floor instrument of the NEW type, the
  probe with the body a designed hole. Protocol runner.
- `runs/S1ReadingHoled.agda.txt`, `runs/S2FirstFactorHoled.agda.txt`,
  `runs/S3ZSlotHoled.agda.txt`, `runs/S4EqHoled.agda.txt`,
  `runs/S5FirstFactorOnlyReal.agda.txt`, `runs/R1TruncRec.agda.txt`,
  `runs/R4Projection.agda.txt` -- the seven in-dispatch instruments of
  section 3, each differing from the delivered probe only in its module
  line, its banner, and the one named change (measured with diff).
- `runs/run.sh` (protocol runner, 1800 s cap) and `runs/diag.sh`
  (diagnostic runner, 420 s cap). Diagnostic numbers are NEVER quoted as
  prices; the prices this report states are the section 1 rows only.
- One `.agda` file that could not typecheck existed only as the temporary
  same-stem copy of a run, deleted at once after each run (Agda 2.8.0
  rejects the `.agda.txt` extension; the 764 finding). The tree now carries
  exactly two `.agda` files, the two GREEN interfaces.

## 0. THE VENDOR DECISION

The premise basis directories `agents/tasks/LJ-1-767/` and
`agents/tasks/LJ-1-765-SPLIT/` do not exist in this worktree; their reports
were read in their own worktrees
(`.pod-state/worktrees/LJ-1-767/agents/tasks/LJ-1-767/lj-1.767-report.md`
and `.pod-state/worktrees/LJ-1-765-SPLIT/agents/tasks/LJ-1-765-SPLIT/lj-1.765-SPLIT-report.md`).
The vendor files delivered in this task directory carry the measured
verdicts in their own headers, and no absent directory is needed.

- `VendorFrame.agda.txt` transcribed to `runs/FrameSplit.agda`: module
  renamed to `LJ-1-767-SPLIT.runs.FrameSplit`, header rewritten; `diff`
  from the first import line down shows exactly one differing line, the
  module line.
- `VendorHull.agda.txt` transcribed to `runs/HullHalfSplit.agda`: module
  renamed, the Frame import retargeted to `LJ-1-767-SPLIT.runs.FrameSplit`,
  header rewritten; `diff` shows exactly two further differing lines, the
  module line and the import, and the vendor's duplicated header comment
  block kept byte for byte.
- `VendorD7.agda.txt` transcribed to `runs/D7MemHoledSplit.agda.txt`:
  module renamed, the two interface imports retargeted, one comment-line
  cite retargeted, header rewritten; the designed hole intact; every other
  line byte-identical.
- `VendorPack.agda.txt` transcribed to `Probe767Split.agda.txt`: module
  renamed, the two interface imports retargeted, header rewritten, and the
  brief's ordered SPLIT delta taken: the `⟨ z ∈ˢ HS.M ⟩` factor dropped
  from the Sigma, the `a∈H` component dropped from the packing, the
  witness pattern `(a , a∈H , sat)` becoming `(a , _ , sat)`. Every other
  code row byte-identical to the vendor.

## 1. THE PROTOCOL RUNS

ONE Agda process at a time, sequential, `pgrep -x agda` empty between runs.
`GHCRTS` was read from the pane at every run and never set by this task;
each `.out` line 1 shows `-A64m -I0 -M4g`, the heavy caliber. Cap 1800 s.
This worktree's `_build/2.8.0/agda/agents/tasks/` held none of the cone's
interfaces, so the cone was warmed bottom-up first, each module its own
process. All numbers below are WALL CLOCK, WARM where the cone was already
built, and each is a price (protocol runner).

| run | file | rc | wall | peak RSS | evidence |
|---|---|---|---|---|---|
| warm Probe652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 4.47 s | 900694016 B | runs/warm-p652.out:5,6,23 |
| warm Probe667 | `agents/tasks/LJ-1-667/Probe667.agda` | 0 | 12.69 s | 1955610624 B | runs/warm-p667.out:6,7,24 |
| warm Probe673 | `agents/tasks/LJ-1-673/Probe673.agda` | 0 | 96.55 s | 1494433792 B | runs/warm-p673.out:4,5,22 |
| warm Probe692 | `agents/tasks/LJ-1-692/Probe692.agda` | 0 | 107.61 s | 1678245888 B | runs/warm-p692.out:7,8,25 |
| frame | `runs/FrameSplit.agda` | 0 | 12.28 s | 1756266496 B | runs/framesplit.out:4,5,22 |
| hull half | `runs/HullHalfSplit.agda` | 0 | 206.54 s | 1771880448 B | runs/hullhalfsplit.out:4,5,22 |
| D7 re-measure | `runs/D7MemHoledSplit.agda.txt` | 42, designed | 214.45 s | 1876279296 B | runs/d7memholedsplit.out:7,8,25 |
| floor, new type | `runs/FloorSplit.agda.txt` | 42, designed | 110.53 s | 1852571648 B | runs/floorsplit.out:7,8,25 |
| THE RUN | `Probe767Split.agda.txt` | 124, CAP | 1800.09 s | 4638425088 B | runs/probe767split-1.out:4,5,22 |

D7 re-measured at this site matches the 767 site within noise (214.45 s
here, 213.09 s there, that number diagnostic and never a price). Its only
diagnostics are the designed hole (runs/d7memholedsplit.out:4, the
`UnsolvedInteractionMetas` block at `D7MemHoledSplit.agda:112.36-44`). The
floor of the new type is 110.53 s with 2.1 GB of headroom
(runs/floorsplit.out:7,8; its only diagnostic is the designed hole,
runs/floorsplit.out:4, at `FloorSplit.agda:123.55-56`), so the probe run
went ahead. It walled: `EXIT=124` at the 1800 s cap, peak RSS 4638425088 B
(runs/probe767split-1.out:4,5,22). The floor and the D7 price bracket the
run: the interfaces, the type, `conv0`'s inferred codomain and the export
cost about 110 s; the tuple elaborated under the two truncation binders
with one hole costs about 215 s; no complete tuple finished inside 1800 s.

## 2. THE ENVIRONMENT AT DISPATCH

- No Agda process at dispatch (`pgrep -x agda` empty); the same check empty
  between every run.
- Pane caliber `GHCRTS=[-A64m -I0 -M4g]` (heavy), read at dispatch, never
  set or changed by this task.
- `sysctl vm.swapusage` at dispatch: total 5120.00M, used 3945.31M, free
  1174.69M. The `agda-watchdog` was running (`scripts/ops/agda-watchdog.sh`)
  and never fired.
- This worktree's `_build/2.8.0/agda/agents/tasks/` held none of Probe652,
  Probe667, Probe673, Probe689, Probe692, so the cold closure was paid in
  the warm-up runs of section 1, not inside any price row.
- This worktree has no `.venv`; the pinned interpreter of the main checkout
  (`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, Python 3.11.16) ran the
  survey gate (section 5).

## 3. THE IN-DISPATCH GRID, AND THE LAW

The coder clause (owner ruling 2026-08-23) makes the wall a signal to
restructure in the same dispatch. Seven instruments were built, run and
measured at a 420 s diagnostic cap (`runs/diag.sh`; the cap line is printed
inside each `.out`). NOTHING in this section is a price; only section 1
states prices. Each instrument differs from the delivered probe ONLY in its
module line, its banner comment, and the change named below (measured with
`diff`).

| instrument | delta from the delivered probe | rc | peak RSS | evidence |
|---|---|---|---|---|
| S1 | reading slot (`conv0`) holed, rest real | 124 | 3977854976 B | runs/s1-reading-holed.out:5,6,23 |
| S2 | FIRST FACTOR (`Lδ∈M`) holed, rest real | 42, designed | 1888845824 B | runs/s2-firstfactor-holed.out:8,9,26 |
| S3 | z slot (`fst a`) holed, rest real | 251, HEAP | 4771807232 B | runs/s3-zslot-holed.out:8,9,26 |
| S4 | ca equation (`ca≡Lδ`) holed, rest real | 124 | 3959013376 B | runs/s4-eq-holed.out:5,6,23 |
| S5 | FIRST FACTOR the only real slot; z, both equations, reading holed | 42, designed | 1873149952 B | runs/s5-firstfactor-only-real.out:11,12,29 |
| R1 | same-type restructure: innermost `PT.rec` + `∣_∣₁` instead of `PT.map`, no hole | 124 | 3969449984 B | runs/r1-truncrec.out:5,6,23 |
| R4 | same-type restructure: witness by projections, never pattern-bound, no hole | 124 | 3959046144 B | runs/r4-projection.out:5,6,23 |

S3 is the sharpest wall form: `agda: Heap exhausted; Current maximum heap
size is 4294967296 bytes (4096 MB).` (runs/s3-zslot-holed.out:5,6,7). The
other walls were time-cap walls at 3.9 to 4.0 GB and still climbing at the
420 s cut.

### The law the grid states

**WALL iff the packed tuple's FIRST factor is a real term and at least one
further component is real. GREEN iff the first factor is a hole. A first
factor real with no other real component costs the floor.**

- First factor real, four further real components: the protocol run, WALL
  at 1800 s; S1, S4, WALL; S3, HEAP EXHAUSTED (the reading, z, or an
  equation holed changes nothing).
- First factor real, nothing else real: S5, GREEN, 112.41 s, the floor's
  own price class (110.53 s). The first factor's real check alone is free.
- First factor holed: S2, GREEN, 215.22 s, whatever else is real.

The 767 grid re-reads under the same law with zero exceptions. Its green
instruments were exactly those with the OLD first factor (`⟨ z ∈ˢ HS.M ⟩`,
its slot 4) holed (D6 all holed, D7 membership holed, D12, D15); its walls
were exactly those with the old first factor real in any form (D1, D11,
D13, D14, D17, the protocol run). The old grid's phrase "the membership
slot" named the old FIRST factor. The wall tracks the POSITION, not the
membership proposition: at the old site a real `Lset`-delta-membership at
the SECOND factor was green (D7), while at this site the same proposition
real at the FIRST factor walls (S1).

### What is ruled out

- NOT the witness-membership component. This Sigma has none anywhere, and
  the delivered probe walls at the same RSS signature as 767's.
- NOT the reading comparison. S1 walls with the reading holed.
- NOT the truncation plumbing. The floor and S5 put the two `PT.rec`
  binders, both `codeOf` applications, `PT.map`/`PT.rec`, and the
  `hullClosed` application inside green prices.
- NOT the tuple's realness as such. S5 is real at the first factor and
  greens at the floor price.

### Why no permitted shape can carry the term

The obligation's Sigma puts `⟨ Lset δ ∈ˢ HS.M ⟩` at its first factor. The
only term of that type in scope is the hypothesis variable `Lδ∈M` supplied
by the obligation's own telescope. Any other filler would be new
mathematics (a hull lemma) or a postulate; both are outside this brief, and
a hole is not a deliverable. So every permitted packing supplies `Lδ∈M`
real at the first factor, and every shape that does so was measured
walling: the inline `PT.map` packing (the protocol run), the `PT.rec` +
`∣_∣₁` packing (R1), the projection packing (R4), each also with the
reading holed (S1), z holed (S3), or an equation holed (S4). The clause's
restructuring duty is thereby met: two no-hole restructurings were built,
run and measured, and the specific reason none can carry the term is the
first-factor law above.

### Mechanism, unconfirmed

The working hypothesis for the mechanism: with the first factor real, the
constraint solver's final conversion of the complete tuple against the
truncated Sigma forces the hull's sett-membership structure at `Lset δ`,
and that forcing compounds over each further real component (S3, three
further real components including the FOL reading, died hardest; S5, no
further real component, free; S2's first-factor hole parks the whole
constraint). The hypothesis is NOT confirmed. What is confirmed is the
grid, and the grid is the finding.

## 4. WHAT THE NEXT BRIEF NEEDS

- The wall is the FIRST FACTOR of the packed Sigma, at both sites measured.
  Any next attack on this obligation should name the grid row it
  contradicts.
- The grid leaves one direction open that this dispatch could not take
  without changing the obligation's type: give the first factor a CHEAP
  filler or none. Concretely: reorder the Sigma's factors so a code
  equation or the reading stands first, state the first factor through a
  definitionally-cheaper alias, or drop it. All are type changes, the
  mathematician's call (the same call the 767 report recorded, now with
  the correct site). Pricing any of them is a fresh dispatch, never an
  analogy from this grid.
- The supplied pieces stay on the meter at this site: frame 12.28 s
  (runs/framesplit.out:4,5), hull half 206.54 s
  (runs/hullhalfsplit.out:4,5), D7 214.45 s
  (runs/d7memholedsplit.out:7,8), floor 110.53 s
  (runs/floorsplit.out:7,8). The cone is now WARM: a re-dispatch here
  starts in the 8 to 12 s class, not at 226 s.
- The four walls of the ascribed shape (B2, B8, conv-1, amb-1) stand
  untouched; `conv-at-Lδ` was never approached; `mkWit`'s spelled codomain
  was never restored; `amb` was never tried.

## 5. SURVEY CHECK

Ran before return, as ordered, after the two survey blocks below were
written. This worktree has no `.venv` of its own; the pinned interpreter of
the main checkout ran the gate. One run, clean:

```text
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-767-SPLIT
check-survey-quotes: LJ-1-767-SPLIT clean (0 note(s), 0 defect(s))
```

## 6. W2 ANSWER

Honored by consumption. The dispatch wrote no new mathematics: the frame is
the vendored frame byte for byte below the module line, the hull half is
the vendored hull half with one import retargeted, `conv0` is the opened
`Spend` term of LJ-1.692, and `grounded-from-complete` is a composition of
those with `codeOf` and the truncation combinators. The generic carrier is
LJ-1.689's `hull-convert`, instantiated by LJ-1.692 at `matrix₃` and
re-exported through the frame; nothing was rewritten at a fixed form. The
rule's home names it: MAXIMUM REUSE is the architecture's objective, and it
is the same rule as WRITE IT GENERIC (archive/dev/DD-archived.md:22).

## 7. W3 ANSWER

**NO-GO.** Whether `grounded-from-complete` checks at `-M4g` at this Sigma,
with no membership proof in the tuple: it does not. The delivered shape
walls at the cap with peak RSS 4638425088 B
(runs/probe767split-1.out:4,5,22), and no permitted no-hole shape carried
it (R1, R4, section 3). The brief's estimate, "D7 plus the dropped slot",
was wrong in the informative direction: the dropped component was not the
wall's site. The wall moved with the first factor (section 3's law), and
the first factor's only legal filler walls in every measured shape.

## 8. RATIO BAR

The write scope of this task carries no ` ```agda ` fence: the probe and
the instruments are raw `.agda.txt` files (each counts 0 by the bar's own
rule) and this report is prose. The divisor of this return is 0 and the bar
cannot fire.

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - READ. DD4's row, the rule the W2 answer
  reports against: "MAXIMUM REUSE is the architecture's objective, and it
  is the same rule as WRITE IT GENERIC."
- archive/dev/ORCHESTRATION.md - declined, not read. The one-process and
  caliber rules have their canonical home in the coder slot file, and this
  task needed no loop-operation history.
- archive/dev/PLAN-archived.md - declined, not read. No plan-level question
  arose in a measurement dispatch.
- archive/dev/TASKS-archived.md - declined, not read. This task's
  predecessors are named in its own brief, and their reports were read in
  their own worktrees.
- archive/dev/STATUS-archived.md - declined, not read. Standing status is
  `dev/pod/screen.toml` alone, and no L3-era row bears on a packaging
  probe.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md` - declined, not read beyond
  a relevance grep. This dispatch wrote no mathematical prose and coined no
  term.
- `dev/literature/rudimentary-functions.md` - declined, not surveyed. The
  dispatch is a measurement over delivered Agda; no Devlin content was
  consulted.
- `dev/literature/fine-structure.md` - declined, not surveyed. Same reason:
  no fine-structure content was interpreted or judged.
- `dev/literature/BIBLIOGRAPHY.md` - declined, not surveyed. No source
  question arose in a transcription, a run grid and a wall report.
- `dev/literature/primary-sources.md` - declined, not surveyed. Same
  reason: no literature content was consulted or judged.
