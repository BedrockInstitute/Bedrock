# LJ-1.769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT report: push-raw-at-vars, gate stop, instruments delivered

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/Probe769S5.agda::push-raw-at-vars
verdict: **STOP AT THE BRIEF'S GATE, FIFTH CONSECUTIVE ON THIS LINE. NO
AGDA RAN, NOTHING IS MEASURED, AND NO VERDICT ABOUT THE TERM IS
CLAIMED.** Swap used was 9756.19 MB against the brief's 8192 MB line,
read twice in this dispatch, the second time immediately before the
launch the gate forbids. The transcription duty survived the gate, as
the brief orders it: the obligation and its frame are TRANSCRIBED into
this task's own namespace at `.agda.txt`, diff-verified, beside a
retargeted run harness, so the next dispatch needs no cross-checkout
reads. The obligation stays open at supply 0. This row is ENVIRONMENT
and claims neither `heap_wall` nor a mathematical NO-GO.

## 1. The gate

Two readings, one command: `sysctl vm.swapusage`.

- At dispatch start, before any transcription: `vm.swapusage: total =
  11264.00M  used = 9756.19M  free = 1507.81M  (encrypted)`.
- At 00:37:16 +0800, after the transcription and immediately before
  the would-be canary launch: `used = 9756.19M`, byte-identical.

9756.19 MB is at or above 8192 MB both times. The gate fired, and this
dispatch ran no Agda: no canary, no obligation, no new process.

The box's watchdog is the same one the predecessor reports saw. Its
log holds 662 kill rows; the last three carry the swap-spiral format,
and the last is `_build/tools/agda-watchdog.log:672`: `2026-09-03
21:33:39 KILLED agda pid=51946 (swap 10090MB >= 8192MB)`, about three
hours before this dispatch started. The pressure is external and
sustained: the four earlier stops on this line read 9779.19, 9771.19
and 9772.19 MB (agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/
lj-1.769-SPLIT-SPLIT-SPLIT-report.md, section THE GATE, THE NUMBERS),
then 9756.19 MB
(agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT/
lj-1.769-SPLIT-SPLIT-SPLIT-SPLIT-report.md:5). This dispatch's
reading equals the fourth one to the decimal.

Premise 4's citation home, named as the predecessor named it: the
running watchdog executes the MAIN CHECKOUT's
`scripts/ops/agda-watchdog.sh`, whose line 28 is
`SWAP_MAX_MB=$((8*1024))`. This worktree's tracked copy of that
script is an older text with no swap branch: its guards are a 6 GB
per-process backstop (`scripts/ops/agda-watchdog.sh:17`) and an 8
percent free floor (`scripts/ops/agda-watchdog.sh:21`). The brief's
premise resolves only against the main checkout's text.

## 2. The transcription, and how it was checked

Both sources were read from the main checkout by absolute path, as
the brief orders. This worktree has no `agents/tasks/
LJ-1-769-SPLIT-SPLIT-SPLIT/` directory (premise 2 re-verified).
Transcription was mechanical: byte copy plus `sed` on the retargeted
lines, never a retyping. The check: strip comment lines from source
and target, run `diff`, and read the whole residue. Nothing landed in
`src/`, and no `.agda` file exists anywhere under this task's
directory, because nothing typechecked (the naming rule).

- `Probe769S5.agda.txt` (task top level), from
  `agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/Probe769SSS.agda.txt`.
  Stripped diff: exactly two lines. The module line is now
  `LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT.Probe769S5 {ℓ : Level}
  (lem : LEM (ℓ-suc ℓ)) where` (line 34) and the Frame import line is
  now `import LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT.runs.Frame769S5
  {ℓ} lem as Frame` (line 50). The term stands at lines 73 to 81:
  `push-raw-at-vars :` at line 73, declared with the brief's
  obligation type verbatim, and its body at line 80 is
  `Cy.push P667.Δ₀-matrix₃ ((x₁ , m₁) ∷ (x₂ , m₂) ∷ (x₃ , m₃) ∷ [])
  rd`, byte-identical to the source. No HullHalf import, no inhabited
  `commute-from-reading`, no copied `Carry` (the file opens
  Probe652's `F.Carry`, it does not restate it), no `amb`, no
  `conv0`, no hole, no postulate.
- `runs/Frame769S5.agda.txt`, from
  `agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/runs/Frame769SSS.agda.txt`.
  Stripped diff: exactly one line, the module line, now
  `LJ-1-769-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT.runs.Frame769S5 {ℓ : Level}
  (lem : LEM (ℓ-suc ℓ)) where` (line 54). The frame's lineage reaches
  a green run: `LJ-1-769-SPLIT.runs.Frame769Split` checked at 15.77 s
  cold, peak 1743634432 B, caliber `-A64m -I0 -M4g`.
- `runs/run.sh`, the harness retargeted to this task's paths: one
  Agda process per row, caliber echoed from the pane and never set in
  the script, 1800 s cap, `/usr/bin/time -l` around it.
- `runs/run-obligation.sh`, the promotion protocol retargeted, gate
  restated in its header. One defect of the predecessor's copy is
  fixed: its failure path deleted the mistyped stem `Probe769SS.agda`,
  one character short; this copy deletes `Probe769S5.agda`, the file
  it actually created.

Not written: `Probe769S5.agda` and `runs/Frame769S5.agda` (a name is
earned by an `EXIT=0` run), `review-of-push-raw-at-vars.md` (section
5), anything under `runs/*.out` (no Agda ran), and anything under
`src/`.

## 3. The runs

None. The gate orders the stop before any Agda, and the reading was
at or above the line both times. The run order is staged and
unchanged for the next dispatch: canary first, on a same-stem `.agda`
copy of `runs/Frame769S5.agda.txt` through `runs/run.sh`; then, green
there, the obligation through `runs/run-obligation.sh`, which re-copies
the probe to its `.agda` stem, runs it under the same cap, promotes
the name on `EXIT=0`, and deletes the copy on every other exit.

## 4. W3, the widest unmeasured term

Whether `push-raw-at-vars` checks at `-M4g` when swap used is below
8192 MB. Still unmeasured; this dispatch adds no number, because no
Agda ran. Two standing figures do bear on the next attempt, and this
report corrects one pointer the fourth report left:

- The frame canary is priced in the 3 to 16 s class
  (agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/
  lj-1.769-SPLIT-SPLIT-SPLIT-report.md:103, `3 to 16 s class`). That
  number is the cheap probe of the kill line, not the obligation's
  price.
- The conversion alone, measured at the neighbour task, was killed at
  1626.38 s and peak RSS 4478189568 B
  (agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:100-104,
  `killed at 1626.38 s`). That is the next wall candidate if the push
  lands cheap.
- The fourth report cites the obligation's own estimate at
  SSS report line 210. That line is a run-order bullet and holds no
  number; the readable class figures on this line are the two above.
  The next brief should carry the numbers it needs in its own text.

## 5. Why there is no `review-of`

The brief rules a gate stop environment, and forbids a `review-of`
for a resource wall. This stop is one environment fact read twice.
No mathematical claim is made, so no `review-of-push-raw-at-vars.md`
exists, and the branch that fits this return is `transfer-park`.

## 6. What the next brief needs

1. **Gate first, again.** Five consecutive stops have now met swap
   used above 8192 MB, and the last two read the same 9756.19 MB. The
   moment to fire is a reading just under the line with a quiet
   recent log (`_build/tools/agda-watchdog.log`; today's last kill is
   21:33:39 at line 672).
2. **No cross-checkout reads are needed.** The probe, the frame and
   the harness sit in this task's directory, diff-verified. The run
   order in section 3 is the whole procedure.
3. **Read the outcome by the brief's own branches.** `EXIT=0`
   promotes the obligation file and is GO. Exit 251 or a
   Heap-exhausted message is a true wall: the coder clause then
   orders a restructure in the same dispatch, not a rerun. A kill in
   the watchdog's own format is environment again: re-park,
   re-dispatch, claim nothing.
4. **If GO lands**, a later brief prices the conversion alone, and
   the standing 1626.38 s kill is its floor question.

## THE PREMISES, RE-VERIFIED

1. The gate fired a fourth time, no Agda ran. Stands, and this
   dispatch makes it five: readings in section 1.
2. A fresh worktree does not see untracked predecessor files.
   Stands: the source directory is absent here; both files were read
   from the main checkout by absolute path.
3. The sources live in the main checkout. Stands: both reads
   succeeded at the paths THE OBLIGATION names.
4. The watchdog kills Agda at swap used 8192 MB. Stands, at the main
   checkout's `scripts/ops/agda-watchdog.sh:28`, with the tracked-copy
   caveat recorded in section 1.

## THE W2 ANSWER

DD4's rule is MAXIMUM REUSE, the same rule as WRITE IT GENERIC
(archive/dev/DD-archived.md:22, `MAXIMUM REUSE is the architecture's
objective, and it is the same rule as WRITE IT GENERIC`). This
dispatch writes no mathematics at all: the term's body stays the
predecessor's one-liner over Probe652's generic `Carry` opened at the
frame, the frame is a diff-verified transcription of a green file,
and no definition, lemma or proof was copied, re-spelled or weakened.
The only new bytes are the retargeted module lines and the rewritten
headers. The probe sits beside its brief and report, never under
`src/`, per DD8 (archive/dev/DD-archived.md:24, `Every block is gated
before it is funded, and an estimate is ONE best-effort number`). No
fixed form was chosen, because no form was written; W2 costs nothing
here.

## ARCHIVE USED

- archive/dev/DD-archived.md: READ, at :22 (`MAXIMUM REUSE is the
  architecture's objective, and it is the same rule as WRITE IT
  GENERIC`, the DD4 rule this report's W2 answer turns on) and at :24
  (`Every block is gated before it is funded, and an estimate is ONE
  best-effort number`, the DD8 row whose probe-commitment clause this
  task's layout follows).
- archive/dev/ORCHESTRATION.md: declined, not read. This dispatch
  wrote no build; the standing brief clauses already sit in the slot
  file the program injected.
- archive/dev/PLAN-archived.md: declined, not read. A gate stop
  plans nothing, and campaign planning is not this slot's input.
- archive/dev/TASKS-archived.md: declined, not read. Retired task
  lists cannot bear on a swap reading or on a file transcription.
- archive/dev/STATUS-archived.md: declined, not read. The only
  standing status is the screen, which the program already injected.

## LITERATURE USED

All five candidates declined, none read: this dispatch ran no Agda,
wrote no mathematics, no chapter prose and no glossary text, so no
literature candidate can bear on a gate stop and a transcription.

- dev/literature/devlin-errata.md: declined, not used. The
  do-not-repeat list for chapter mathematics, of which this dispatch
  wrote none.
- dev/literature/glossary-review-2026-08.md: declined, not used. No
  term in this stop is contested.
- dev/literature/BIBLIOGRAPHY.md: declined, not used. No source is
  cited beyond the tree's own files.
- dev/literature/primary-sources.md: declined, not used. Same
  reason: no reading duty survived the gate.
- dev/literature/level-formula-slot-roles.md: declined, not used.
  The level formula is untouched; the stop is environmental.
