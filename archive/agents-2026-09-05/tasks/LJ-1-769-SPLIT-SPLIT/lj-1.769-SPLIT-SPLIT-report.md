# LJ-1.769-SPLIT-SPLIT report: push-raw-at-vars, gate stop

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.769-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-769-SPLIT-SPLIT/Probe769SS.agda::push-raw-at-vars
verdict: **STOP AT THE BRIEF'S OWN GATE. NO AGDA RAN, NOTHING IS
MEASURED, AND NO VERDICT ABOUT THE TERM IS CLAIMED.** The gate clause
orders a swap reading before any Agda and a stop when swap used is at
or above 8192 MB. This dispatch's readings are 9779.19 MB used at
dispatch and 9771.19 MB used minutes later
(`vm.swapusage: total = 11264.00M  used = 9779.19M  free = 1484.81M`,
re-read `used = 9771.19M` at 23:35 +08), both far above the line, and
the box's agda watchdog was still armed with its last logged kill at
2026-09-03 21:33:39, `KILLED agda pid=51946 (swap 10090MB >= 8192MB)`
(`_build/tools/agda-watchdog.log`, last line). Any Agda process this
dispatch started would have been killed at the next 20 s tick by the
same swap-spiral branch that killed eight rows of the predecessor
task (agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:10,
section 4). This row is ENVIRONMENT and claims neither `heap_wall`
nor a mathematical NO-GO; no `review-of` is written, which the brief
itself forbids for a resource stop. What this dispatch delivered
instead: the obligation and its frame are TRANSCRIBED and parked at
`.agda.txt` in this task's own namespace, with a promotion protocol,
so the next dispatch on a settled box starts from this worktree and
does not need the predecessor's untracked files. The obligation stays
open at supply 0.

## THE GATE, THE NUMBERS

The brief's GATE clause orders a `sysctl vm.swapusage` reading before
any Agda, and a stop when swap used is at or above 8192 MB. The
readings this dispatch took:

- At dispatch, before any work: `vm.swapusage: total = 11264.00M
  used = 9779.19M  free = 1484.81M (encrypted)`. Used is 1587 MB
  above the line.
- At 23:35 +08, minutes later: `used = 9771.19M`. The pressure is
  sustained, not a spike.
- The box's agda watchdog (`scripts/ops/agda-watchdog.sh`, the
  swap-spiral branch the predecessor's report section 4 documents)
  was armed the whole time. Its log's last line, line 672 of the
  file, is a kill: `2026-09-03 21:33:39 KILLED agda pid=51946 (swap
  10090MB >= 8192MB)` (`_build/tools/agda-watchdog.log:672`), two
  hours before this dispatch started. Any Agda process this dispatch started
  would have been the biggest agda on the box and would have died at
  the next 20 s tick.

So the gate fired, and this dispatch ran no Agda at all: no probe,
no floor, no canary. That is the clause working as designed. The
predecessor's eight watchdog kills (section 4 of its report) are the
measured proof that a row run under this pressure ends as a kill
with no diagnostic, and its dip-fire protocol (runs/dipfire.sh,
runs/dipfire2.sh) found no dip in its own final two hours. This
dispatch does not repeat that wait. The swap number belongs to an
external workload (node render-chunk renderers, a par2 repair,
desktop applications, named in the predecessor's section 4), not to
the pod, so the gate is a wait for the box, and a re-dispatch is
cheap because the instruments now sit ready here.

Classification: this is a gate stop, the same class the brief's own
branches call environment. It claims no `heap_wall`: the program's
classifier (scripts/pod/facts.py:158-159) reads `heap_wall` from
exit 251 or a Heap-exhausted message, and this dispatch produced no
Agda exit at all. It states no mathematical NO-GO and writes no
`review-of`, which the brief forbids for a resource stop.

## THE DELIVERABLE

No Agda ran, so nothing here typechecked, and every Agda file rests
at `.agda.txt`, never `.agda` (the naming rule). The instruments the
next dispatch needs are transcribed and parked, because the
predecessor's copies are untracked and absent from this worktree
(section THE WORKTREE GAP below). All four files are inside the
brief's write scope. Nothing landed in `src/`.

- `Probe769SS.agda.txt` (task top level) -- the obligation, the push
  at the carry's own literal codomain, exported at the file's top
  level under the brief's name `push-raw-at-vars`. Source:
  `LJ-1-769-SPLIT/runs/RawOnly769Split.agda.txt`, the file the brief
  names. Diff-measured at delivery: below the OPTIONS line exactly
  four lines differ, the module line (now
  `LJ-1-769-SPLIT-SPLIT.Probe769SS`, matching the obligation path),
  the Frame import line (now
  `LJ-1-769-SPLIT-SPLIT.runs.Frame769SS`), and the term's two name
  lines (`push-raw-at-vars` replacing the instrument's `raw`, so
  promotion is a pure file rename). Every other line is
  byte-identical. The term's body is the brief's body verbatim:
  `Cy.push P667.Δ₀-matrix₃ ((x₁ , m₁) ∷ (x₂ , m₂) ∷ (x₃ , m₃) ∷ [])
  rd`. No HullHalf import, no inhabited `push-matrix3-at-vars`, no
  inhabited `commute-from-reading`, no copied `Carry`, no `amb`, no
  `conv0`: every prohibition in the brief holds.
- `runs/Frame769SS.agda.txt` -- the vendored frame, transcribed from
  `LJ-1-769-SPLIT/runs/Frame769Split.agda`, which is GREEN in that
  task's worktree at 15.77 s, peak 1743634432 B, caliber
  `-A64m -I0 -M4g` (agents/tasks/LJ-1-769-SPLIT/runs/frame769split.out:1,4,5).
  Diff-measured at delivery: below the first OPTIONS line exactly
  one line differs, the module line (now
  `LJ-1-769-SPLIT-SPLIT.runs.Frame769SS`). It is this dispatch's
  canary row: a frame-level file priced in the 3 to 16 s class, so
  it is the cheap probe of the watchdog's kill line.
- `runs/run.sh` -- the run harness, the predecessor's retargeted:
  one Agda process per row, caliber echoed from the pane and never
  set here, 1800 s cap, `/usr/bin/time -l` around it.
- `runs/run-obligation.sh` -- the promotion protocol, the
  predecessor's runs/run-obligation.sh retargeted, with the gate
  restated in its header: gate on `vm.swapusage` first, then copy
  `Probe769SS.agda.txt` to the same-stem `.agda`, run it, write the
  rc to `runs/.obligation-rc`, PROMOTE on `EXIT=0`, delete the copy
  on every other exit.

Not written: `Probe769SS.agda` (a name is earned by an `EXIT=0`
run), `review-of-push-raw-at-vars.md` (forbidden for a resource
stop, and no mathematical claim is made), and anything under
`agents/tasks/LJ-1-769-SPLIT-SPLIT/runs/*.out` (no Agda ran).

## THE PREMISES, RE-VERIFIED

All four premises were checked against the files before the report
was written. The predecessor's report and runs live only in the main
checkout (section THE WORKTREE GAP); the paths below are the brief's
own repo-relative spellings.

1. Floor green, 8.34 s, 977 MB. Verified at
   agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:133, the
   price-table row `| floor | runs/Floor769Split.agda.txt (same-stem
   copy) | 42, designed | 8.34 s | 976977920 B |`. Stands.
2. Spelled-π body unsettled, watchdog SIGKILL, no wall claimed.
   Verified at
   agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:10, the
   verdict line `NO-GO, UNSETTLED AT A CAPPED KILL; THE MEASUREMENT
   IS GATED BY THE BOX'S OWN AGDA WATCHDOG`. Stands.
3. Next run is the push alone, then the conversion, then the
   composite. Verified at
   agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:269: `A
   re-dispatch on a SETTLED box (swap used below 8192 MB, watch the
   log's kill cadence) runs the three instruments IN ORDER`, and the
   order named there is RawOnly, ConvOnly, Raw. This brief's
   obligation IS the RawOnly step, so the order starts here. Stands.
4. `Carry.push` green at a variable formula in Probe652. Verified at
   agents/tasks/LJ-1-652/Probe652.agda:185-192 (the `push` body,
   chained `atM`, `iso-inv`, `atπ`) and its use at :228 inside
   `commute₃`, where `fo` is a bound variable. Stands, with the
   predecessor's caution (its report section 2, end): Probe652's
   green is at a VARIABLE formula, so it never priced a concrete
   twelve-wrap one.

## THE WORKTREE GAP

A finding the program should see. The predecessor task's directory
`agents/tasks/LJ-1-769-SPLIT/` does not exist in this worktree, and
never existed in git: the commits that admitted those tasks touched
only `dev/pod/table.toml` (f36317f5, pod: admit LJ-1.769-SPLIT;
f950b4ca, pod: admit LJ-1-769-SPLIT-SPLIT), and no commit anywhere
git-adds a task file (`git log --all --diff-filter=A --
"*RawOnly769Split*"` is empty). The report, the green frame, and the
three `.agda.txt` instruments named by this brief exist only as
untracked files in the main checkout at `/Users/alsg/Agentic/Bedrock`,
which this dispatch could read because the machine is shared
(`machine: shared` in both heads). Every citation this report makes
to the predecessor was verified there. The transcription into THIS
task's directory (section THE DELIVERABLE) is the fix for the next
dispatch: if it runs in this worktree, it no longer depends on the
main checkout's untracked files.

## THE W2 ANSWER

DD4's rule is `MAXIMUM REUSE is the architecture's objective, and it
is the same rule as WRITE IT GENERIC`
(archive/dev/DD-archived.md:22). The dispatch answers it by writing
no mathematics at all: the term's body is the brief's own one-liner
at Probe652's generic `Carry` opened at the frame, the frame is a
diff-measured transcription of a green file, and no definition, no
lemma and no proof was copied, re-spelled or weakened. The only new
bytes are headers and the four measured renames. The probe sits
beside its brief and report per DD8
(archive/dev/DD-archived.md:24), never under `src/`. This stop costs
W2 nothing: no fixed form was chosen, because no form was written.

## 5. WHAT THE NEXT DISPATCH NEEDS

- **Gate first, again.** Read `sysctl vm.swapusage` before anything.
  The predecessor's section 5 already said it: the watchdog's spiral
  branch fires while swap used is at or above 8192 MB, the external
  workload owns that number, and even a 640 MB canary died at exec
  while the spiral was armed. Watch the log's kill cadence too
  (`_build/tools/agda-watchdog.log`): a quiet log at a swap reading
  just under the line is the moment to fire.
- **Run order.** Canary first: `runs/run.sh` on a same-stem copy of
  `runs/Frame769SS.agda.txt` (3 to 16 s class). Green there says the
  kill line is quiet. Then the obligation, one command:
  `agents/tasks/LJ-1-769-SPLIT-SPLIT/runs/run-obligation.sh`.
- **Read the outcome by the brief's own branches.** `EXIT=0`
  promotes the obligation file and is the brief's GO: the term is on
  the meter, and a later brief prices the conversion alone.
  Exit 251 or a Heap-exhausted message is a true wall and, by the
  predecessor's section 5 localization logic, a RawOnly cap localizes
  the site inside the carry body (Probe652.agda:188-192 is the
  `atM`/`iso-inv`/`atπ` chain at the concrete twelve-wrap formula).
  A SIGKILL in the watchdog's own log format
  (`swap NNNNMB >= 8192MB`) is environment again: re-park, re-dispatch,
  claim nothing.
- **Do not re-run the same code to chase a different result.** If the
  obligation caps at `-M4g` on a settled box, the next move is the
  coder clause's restructure-in-the-same-dispatch rule, not a rerun:
  split the carry's three semantic unfoldings into separate rows
  first.
- **The predecessor's ConvOnly datum stands.** The conversion alone
  is a multi-GB elaboration that outlasted 27 minutes
  (agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:100-105,
  the deep row, killed at 1626.38 s and peak RSS 4478189568 B). If RawOnly lands cheap, that row is the next
  wall candidate, and a ConvOnly transcription into this task can
  follow the same four-line diff discipline.

## ARCHIVE USED

- archive/dev/DD-archived.md -- READ, at :22 (DD4, the W2 rule this
  report answers: `MAXIMUM REUSE is the architecture's objective,
  and it is the same rule as WRITE IT GENERIC`) and at :24 (DD8, a
  probe is committed beside its brief and report, never under
  `src/`).
- archive/dev/ORCHESTRATION.md -- declined, not read: the
  orchestration standing rules are already restated in this brief's
  slot file, and this dispatch wrote no build to audit.
- archive/dev/PLAN-archived.md -- declined, not read: campaign
  planning is the program's input, and a gate stop plans nothing.
- archive/dev/TASKS-archived.md -- declined, not read: retired task
  lists cannot bear on a swap-gate stop.
- archive/dev/STATUS-archived.md -- declined, not read: retired
  status records; the only standing status is the screen, which the
  program already injected.

## LITERATURE USED

All five candidates declined, none read: this dispatch ran no Agda
and wrote no mathematics, no chapter prose and no glossary text, so
no literature candidate can bear on a swap-gate stop.

- dev/literature/glossary-review-2026-08.md -- declined, not used.
- dev/literature/primary-sources.md -- declined, not used.
- dev/literature/BIBLIOGRAPHY.md -- declined, not used.
- dev/literature/devlin-errata.md -- declined, not used: the
  do-not-repeat list for chapter mathematics, of which this dispatch
  wrote none.
- dev/literature/level-formula-slot-roles.md -- declined, not used:
  the level-hood formula's slot roles, untouched by a gate stop.
