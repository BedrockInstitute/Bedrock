# LJ-1.769-SPLIT-SPLIT-SPLIT report: push-raw-at-vars, gate stop

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.769-SPLIT-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/Probe769SSS.agda::push-raw-at-vars
verdict: **STOP AT THE BRIEF'S OWN GATE. NO AGDA RAN, NOTHING IS
MEASURED, AND NO VERDICT ABOUT THE TERM IS CLAIMED.** The gate clause
orders a swap reading before any Agda and a stop when swap used is at
or above 8192 MB. This dispatch's readings are 9771.19 MB used at
23:56 +08 and 9772.19 MB used minutes later, both far above the line,
and the box's agda watchdog was running the whole time with its last
logged kill at 2026-09-03 21:33:39, `KILLED agda pid=51946 (swap
10090MB >= 8192MB)` (`_build/tools/agda-watchdog.log:672`). Any Agda
process this dispatch started would have died at the next 20 s tick
of the same swap-spiral branch that killed eight rows of
`[LJ-1.769-SPLIT]` and would have ended this task with no diagnostic.
This row is ENVIRONMENT and claims neither `heap_wall` nor a
mathematical NO-GO; no `review-of` is written, which the brief itself
forbids for a resource stop. What this dispatch delivered instead: the
obligation and its frame are TRANSCRIBED into this task's own
namespace at `.agda.txt`, with the promotion protocol, so the next
dispatch on a settled box starts from this task and needs no
cross-checkout reads. The obligation stays open at supply 0.

## THE GATE, THE NUMBERS

The brief's GATE clause orders a `sysctl vm.swapusage` reading before
any Agda, and a stop when swap used is at or above 8192 MB. The
readings this dispatch took:

- At 23:56 +08, before any work: `vm.swapusage: total = 11264.00M
  used = 9771.19M  free = 1492.81M (encrypted)`. Used is 1579 MB
  above the line.
- Minutes later: `used = 9772.19M`. The pressure is sustained, not a
  spike.
- The box's agda watchdog is up: pid 1964, started 2026-08-31
  16:21:43 (`_build/tools/agda-watchdog.log:649`, `watchdog started
  pid=1964`), executing the main checkout's
  `scripts/ops/agda-watchdog.sh` (read from `ps`, command
  `/bin/zsh /Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh`).
  Its log holds 551 swap-format kills, 8 of them today, the last at
  21:33:39 (line 672), two and a half hours before this dispatch
  started.

So the gate fired, and this dispatch ran no Agda at all: no canary,
no floor, no obligation. That is the clause working as designed.
Three dispatches in a row (`[LJ-1.769-SPLIT]`, this task's
predecessor, this task) have now stopped at the same wall of external
pressure. The swap number belongs to an external workload, not to the
pod, so the gate is a wait for the box, and a re-dispatch is cheap
because the instruments now sit in THIS task's directory.

Classification: this is a gate stop, the class the brief's own text
calls environment ("A watchdog SIGKILL, or a gate stop, is
environment: report it, do not claim a wall"). It claims no
`heap_wall`: no Agda exit code exists, and exit 251 or a
Heap-exhausted message is what a wall is read from. It states no
mathematical NO-GO and writes no `review-of`, which the brief forbids
for a resource stop.

## THE DELIVERABLE

No Agda ran, so nothing here typechecked, and every Agda file rests
at `.agda.txt`, never `.agda` (the naming rule). The instruments the
next dispatch needs are transcribed into this task's namespace,
because the predecessor's copies are untracked and absent from this
worktree (section THE WORKTREE GAP). All four files are inside the
brief's write scope. Nothing landed in `src/`.

- `Probe769SSS.agda.txt` (task top level) -- the obligation, the push
  at the carry's own literal codomain, under the brief's name
  `push-raw-at-vars`. Source:
  `agents/tasks/LJ-1-769-SPLIT-SPLIT/Probe769SS.agda.txt` in the main
  checkout, the file the brief names; NOT a re-copy from
  `[LJ-1.769-SPLIT]`. Diff-measured at delivery: below the OPTIONS
  line exactly two lines differ, the module line (now
  `LJ-1-769-SPLIT-SPLIT-SPLIT.Probe769SSS`, matching the obligation
  path) and the Frame import line (now
  `LJ-1-769-SPLIT-SPLIT-SPLIT.runs.Frame769SSS`). The term's name is
  already the brief's `push-raw-at-vars` in the source, so no name
  line differs, and the declared type is the brief's obligation type
  verbatim. The term's body is the brief's one-liner: `Cy.push
  P667.Δ₀-matrix₃ ((x₁ , m₁) ∷ (x₂ , m₂) ∷ (x₃ , m₃) ∷ []) rd`. No
  HullHalf import, no inhabited `push-matrix3-at-vars`, no inhabited
  `commute-from-reading`, no copied `Carry` (the file opens
  Probe652's `F.Carry`, it does not restate it), no `amb`, no `conv0`,
  no hole, no postulate: every prohibition in the brief holds.
- `runs/Frame769SSS.agda.txt` -- the vendored frame, transcribed from
  `agents/tasks/LJ-1-769-SPLIT-SPLIT/runs/Frame769SS.agda.txt`, which
  is itself a diff-measured transcription of
  `LJ-1-769-SPLIT/runs/Frame769Split.agda`, GREEN in that task's
  worktree at 15.77 s, peak 1743634432 B, caliber `-A64m -I0 -M4g`
  (agents/tasks/LJ-1-769-SPLIT/runs/frame769split.out:1,4,5, as
  recorded at
  agents/tasks/LJ-1-769-SPLIT-SPLIT/lj-1.769-SPLIT-SPLIT-report.md:80).
  Diff-measured at this delivery: below the first OPTIONS line
  exactly one line differs, the module line (now
  `LJ-1-769-SPLIT-SPLIT-SPLIT.runs.Frame769SSS`). It is the canary
  row: a frame-level file priced in the 3 to 16 s class, so it is the
  cheap probe of the watchdog's kill line.
- `runs/run.sh` -- the run harness, the predecessor's retargeted:
  one Agda process per row, caliber echoed from the pane and never
  set here, 1800 s cap, `/usr/bin/time -l` around it.
- `runs/run-obligation.sh` -- the promotion protocol, the
  predecessor's retargeted, gate restated in its header: gate on
  `vm.swapusage` first, then copy `Probe769SSS.agda.txt` to the
  same-stem `.agda`, run it, write the rc to `runs/.obligation-rc`,
  PROMOTE on `EXIT=0`, delete the copy on every other exit.

Not written: `Probe769SSS.agda` (a name is earned by an `EXIT=0`
run), `review-of-push-raw-at-vars.md` (forbidden for a resource
stop, and no mathematical claim is made), anything under
`agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/runs/*.out` (no Agda ran),
and anything under `src/`.

## THE PREMISES, RE-VERIFIED

All four premises were checked against files before the report was
written. The predecessor's report and runs live only in the main
checkout (section THE WORKTREE GAP); the paths below are the brief's
own repo-relative spellings.

1. THE GATE FIRED, NO AGDA RAN. Verified twice over: the predecessor's
   verdict line says its own dispatch ran none
   (agents/tasks/LJ-1-769-SPLIT-SPLIT/lj-1.769-SPLIT-SPLIT-report.md:10,
   `verdict: **STOP AT THE BRIEF'S OWN GATE. NO AGDA RAN, NOTHING IS`),
   and THIS dispatch's readings re-fire the same gate (9771.19 MB,
   then 9772.19 MB). The term is unmeasured and supply stays 0.
   Stands.
2. THE INSTRUMENTS SIT IN `[LJ-1.769-SPLIT-SPLIT]`; PROMOTION IS A
   RENAME. Verified at
   agents/tasks/LJ-1-769-SPLIT-SPLIT/lj-1.769-SPLIT-SPLIT-report.md:80,
   the deliverable row for `Probe769SS.agda.txt`, and proven by this
   dispatch's own diffs: the probe needs only the module line and the
   Frame import line retargeted (the term name is already the brief's),
   the frame needs only the module line. Promotion of the obligation
   on a green run is a copy to the same stem. Stands.
3. CANARY FIRST, THEN THE OBLIGATION. Verified at
   agents/tasks/LJ-1-769-SPLIT-SPLIT/lj-1.769-SPLIT-SPLIT-report.md:192,
   `**Run order.** Canary first: runs/run.sh on a same-stem copy of`.
   This dispatch ran neither, because the gate orders the stop before
   any Agda. Stands, and binds the next dispatch.
4. THE WATCHDOG KILLS AGDA AT SWAP USED 8192 MB. Verified in the main
   checkout's working copy:
   `/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28` is
   `SWAP_MAX_MB=$((8*1024))`, and the spiral branch that reads it and
   kills is at lines 61 to 70 of that file, logging exactly the
   `(swap NNNNMB >= 8192MB)` format the log carries. The RUNNING
   watchdog executes that file (pid 1964, command path the main
   checkout's). ONE CAVEAT the program should see: this worktree's
   tracked copy of `scripts/ops/agda-watchdog.sh` is an older text,
   last touched by commit 9de9c337 (2026-08-25), whose kill lines are
   a 6 GB per-process backstop (line 26) and a free-percentage floor
   (line 32), with no swap branch; the main checkout's copy carries
   the newer text uncommitted. The premise's citation resolves
   against the main checkout's text, which is also the running
   watchdog's text. Stands, with the citation's home named.

## THE WORKTREE GAP, ONE LAYER DEEPER

The predecessor's report named this as a finding the program should
see, and it recurred exactly. The directory
`agents/tasks/LJ-1-769-SPLIT-SPLIT/` does not exist in this worktree
and exists nowhere in git (the admitting commits touch only
`dev/pod/table.toml`: f36317f5, f950b4ca; `git log --all
--diff-filter=A` finds no task file). Its files exist only as
untracked files in the main checkout, and this dispatch could read
them because the machine is shared. The transcription into THIS
task's directory is again the fix for the next dispatch. One more
observation for the program: the main checkout already holds this
task's directory with `.pod` and the brief, written at dispatch time
(23:50 to 23:54 +08), so dispatch inputs do reach the main checkout;
how dispatch outputs return from a worktree is the program's move,
and this report does not guess it. Also recorded under premise 4
above: the tracked `scripts/ops/agda-watchdog.sh` in a fresh worktree
is behind the main checkout's working copy, so a premise citing an
uncommitted script line resolves only at the main checkout.

## THE W2 ANSWER

DD4's rule is `MAXIMUM REUSE is the architecture's objective, and it
is the same rule as WRITE IT GENERIC`
(archive/dev/DD-archived.md:22). This dispatch answers it by writing
no mathematics at all: the term's body stays the brief's one-liner
over Probe652's generic `Carry` opened at the frame, the frame is a
diff-measured transcription of a green file, and no definition, no
lemma and no proof was copied, re-spelled or weakened. The only new
bytes are the retargeted headers and the four measured module-line
renames. The probe sits beside its brief and report per DD8
(archive/dev/DD-archived.md:24), never under `src/`. This stop costs
W2 nothing: no fixed form was chosen, because no form was written.

## 5. WHAT THE NEXT DISPATCH NEEDS

- **Gate first, again.** Read `sysctl vm.swapusage` before anything.
  Three consecutive dispatches have met swap used above 8192 MB
  (9779.19, 9771.19, 9772.19). The pressure is external and
  sustained. Watch the log's kill cadence too
  (`_build/tools/agda-watchdog.log`): the last swap kill is 21:33:39
  and the log is quiet only because nothing has run. A reading just
  under the line with a quiet recent log is the moment to fire.
- **Run order.** Canary first: `runs/run.sh` on a same-stem copy of
  `runs/Frame769SSS.agda.txt` (3 to 16 s class). Green there says the
  kill line is quiet. Then the obligation, one command:
  `agents/tasks/LJ-1-769-SPLIT-SPLIT-SPLIT/runs/run-obligation.sh`.
- **Read the outcome by the brief's own branches.** `EXIT=0` promotes
  the obligation file and is the brief's GO: the term is on the
  meter, and a later brief prices the conversion alone. Exit 251 or a
  Heap-exhausted message is a true wall; by the predecessor's
  localization logic a RawOnly cap localizes the site inside the
  carry body (Probe652.agda:188-192, the `atM`/`iso-inv`/`atπ` chain
  at the concrete twelve-wrap formula). A kill in the watchdog's own
  format (`swap NNNNMB >= 8192MB`) is environment again: re-park,
  re-dispatch, claim nothing.
- **Do not re-run the same code to chase a different result.** If the
  obligation caps at `-M4g` on a settled box, the move is the coder
  clause's restructure-in-the-same-dispatch rule, not a rerun: split
  the carry's three semantic unfoldings into separate rows first.
- **The ConvOnly datum stands.** The conversion alone is a multi-GB
  elaboration that outlasted 27 minutes (deep row killed at 1626.38 s,
  peak RSS 4478189568 B:
  agents/tasks/LJ-1-769-SPLIT/lj-1.769-SPLIT-report.md:100-105). If
  RawOnly lands cheap, that row is the next wall candidate, and a
  ConvOnly transcription into this task can follow the same
  retarget-and-diff discipline this dispatch used.

## ARCHIVE USED

- archive/dev/DD-archived.md -- READ, at :22 (DD4, the W2 rule this
  report answers: `MAXIMUM REUSE is the architecture's objective, and
  it is the same rule as WRITE IT GENERIC`) and at :24 (DD8, a probe
  is committed beside its brief and report, never under `src/`).
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
- dev/literature/BIBLIOGRAPHY.md -- declined, not used.
- dev/literature/devlin-errata.md -- declined, not used: the
  do-not-repeat list for chapter mathematics, of which this dispatch
  wrote none.
- dev/literature/primary-sources.md -- declined, not used.
- dev/literature/level-formula-slot-roles.md -- declined, not used:
  the level-hood formula's slot roles, untouched by a gate stop.
