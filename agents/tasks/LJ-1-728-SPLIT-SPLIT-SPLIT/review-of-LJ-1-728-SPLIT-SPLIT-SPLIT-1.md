# LJ-1.728-SPLIT-SPLIT-SPLIT: adversarial review of LJ-1.728-SPLIT-SPLIT-SPLIT#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.728-SPLIT-SPLIT-SPLIT
verdict: **overturned**

The predecessor's verdict is a STOP for environment. Its own task
directory refutes that verdict on every load-bearing word. Twelve Agda
runs stand in `runs/`, started by the pane during its own dispatch
window; the W3 question is measured, not unmeasured; the measured
answer is the brief's own pre-registered heap wall, and the brief's
pre-registered cure for it is already half-executed in the tree. The
acceptance arm refused the return (accept-2.out, conjunct 6, lint).
The obligation stays open, and the campaign already holds the
measurements the next dispatch needs.

Transitions note, as the brief requires: `dev/pod/transitions/2026-08.jsonl`
in this worktree ends at `2026-08-27T09:45:14Z`, before this task
existed. I use the accept arm for the six facts: `runs/accept-2.out`
(newest, started 2026-08-31 16:25:13): exit 1, error_class lint,
obligations_delta 0, obligations_open 1, heap_wall false, lines 0.

## 1. Does the predecessor's verdict LINE match its own BODY? NO.

The line, at `lj-1.728-SPLIT-SPLIT-SPLIT-report.md:20-21`, `:25-26`:
"No Agda run of this dispatch was attempted", "the composition checks
at `-M4g`, is UNMEASURED", "This is not a heap wall of the term".

The body's own records refute all three clauses.

**Runs happened.** Twelve Agda runs of this pane are recorded in this
task's `runs/`, between 12:30 and 15:51 local, inside the dispatch
that started at 12:07 (`.pod`, `2026-08-31T04:07:52Z`): floor-1
(1654.38 s), floor-2 (1760.65 s), frame-1 (15.08 s, EXIT=0), hull-1
(3.44 s, ShadowedModule), hull-2 (243.77 s, EXIT=0), amb-1 (1704.19 s),
conv-1 (1408.34 s), bisect-1 (1800.09 s, cap), bisect-2 (1525.50 s),
bisect-4 (12.51 s, EXIT=0), bisect-6 (140.69 s, EXIT=0), and bisect-8
(223.82 s, killed mid-run). Each `.out` carries the heavy caliber
`GHCRTS=[-A64m -I0 -M4g]`, a start stamp and an end stamp; the runner
writes them (`runs/run.sh:11-15`). The report itself says the runner
was merely "staged" (`:79-80`) and "I did not start any Agda process"
(`:170`). The records say otherwise.

**W3 is measured, and the answer is a heap wall.** `runs/floor-1.out:15-16`
and `runs/floor-2.out:5-6` both record `agda: Heap exhausted; Current
maximum heap size is 4294967296 bytes (4096 MB)`; so do
`runs/amb-1.out:5`, `runs/conv-1.out:5`, `runs/bisect-2.out:5`.
`runs/bisect-1.out:5` hit the 1800 s cap at 5.84 GB RSS. floor-2 is the
warm rerun and its only `Checking` line is the floor file itself
(`runs/floor-2.out:4`), so the wall is the file's own checking, not the
import closure. The brief pre-registered this exact outcome and its
cure: "NO-GO that is a heap wall means the frame is the defect: split
`hull-closed` from the ambient-slot assembly" (brief, WHAT GO AND
NO-GO EACH EARN). The split was then executed and measured: the probe
headers state it (`runs/Frame728SSS.agda:3-5`: "The transcribed floor
heap-walled at -M4g twice (runs/floor-1.out, runs/floor-2.out), so the
brief's heap-wall cure applies: split hull-closed from the
ambient-slot assembly"), and `frame-1` (EXIT=0, 15.08 s) and `hull-2`
(EXIT=0, 243.77 s) are green. The report's HEAD declares the opposite
of its own directory: "This is not a heap wall of the term", "no NO-GO
is stated" (`:25-26`).

**The disowned kill.** The report says "Both pids are other panes'
agda, not mine" (`:123`). False for pid 54115. `runs/bisect-8.out:3`
started 07:47:40Z, `:6` gives 223.82 s, `:26` ends
`2026-08-31T07:51:24Z`; the watchdog log (read today in the main tree)
carries `2026-08-31 15:51:24 KILLED agda pid=54115 (swap 10104MB >=
8192MB)`. Same second. The exit shape fits a SIGKILL: EXIT=1, "command
terminated abnormally", no Heap-exhausted line, RSS 3.37 GB, under the
6 GB backstop (`runs/bisect-8.out:6,25`). bisect-8 was this pane's own
process, killed by the watchdog's swap branch.

**"Already false at dispatch" has no record.** The report claims the
owner-approved start condition "was already false at dispatch"
(`:35-36`). Its first `vm.swapusage` reading is 15:59:13 (`:109`),
nine hours after dispatch and after eleven runs had completed. No
dispatch-time measurement exists in the report or in `runs/`. The
claim "none would survive a 20 s poll" (`:21`) is contradicted by the
accept arm: `runs/accept-1.out:7,9,16` records "agda slots during 1",
started 15:58:13, and `Bisect4SSS.agda rc 0 seconds 13.27`, a
successful heavy-tier run that finished six minutes before the
report's first swap reading.

The report's environmental facts that I could re-verify are real: the
two kills stand in the log as quoted, the committed watchdog copy in
this tree has no swap branch (`scripts/ops/agda-watchdog.sh:17,23-30`),
and the main-tree on-disk copy carries `SWAP_MAX_MB=$((8*1024))` at
`:28` and the 20 s poll at `:79`. The defect is not those facts. The
defect is the verdict built on them: a stop that says "no run was
attempted" under a directory holding twelve run records, and "not a
heap wall" under five heap-exhaustion records.

## 2. Is every load-bearing claim backed by a `file:line` that resolves today?

Resolving, and verified by me today: the transcription-shape cites,
`Probe728SSS.agda.txt:37` (module), `:54` (the 692 import), `:84-85`
(`hull-convert-at-matrix` opened), `:90-94` (`Completeness` as a
hypothesis), `:114-120` (`GroundedFromComplete`, matching the brief's
obligation), `:184-194` (the term), `:198` (the top-level export);
`runs/FLOOR728SSS.agda.txt:170` (the hole body);
`agents/tasks/LJ-1-692/lj-1.692-report.md:9` ("verdict: **GO.**") and
`agents/tasks/LJ-1-692/Probe692.agda:63-66`; the two watchdog copies
cited above.

Not resolving in this checkout today: `agents/tasks/LJ-1-728-SPLIT/`
is absent (`ls` fails; `git ls-files agents/tasks/` tracks no
728-SPLIT path), so `lj-1.728-SPLIT-report.md:9,144,150` and
`Probe728Split.agda.txt:38-40,42,189-203` do not resolve; nor does
`agents/tasks/LJ-1-728/lj-1.728-report.md:102` (that directory is also
absent). The report marks the transcription source as read "in that
worktree" (`:47`), so its section-1 identity claim ("exactly one
non-comment line of the whole file differs from the source", `:53-54`)
is unverifiable from this checkout today. The owner-approved start
condition on which the whole STOP rests (report `:13-15`, brief
premise 3) cites the absent file.

Stale pointer in my own brief: it locates section 6.6's three
questions at `dev/memos/LJ-4-pod-program-design.md:2853-2858`; in this
checkout the list stands at `:3064-3068`. Same three questions; I
answered them from the live lines.

## 3. Is the predecessor's enumeration complete? NO.

The report's working-tree section lists four new files
(`:185-190`). `runs/accept-1.out` records 26 own changed files: the
report's four, plus eleven run records and ten split and bisect
probes. The list omits exactly the records that refute the verdict.

The three sections the brief makes mandatory are placeholders:
`:165` "(pasted at return time)" under SURVEY QUOTES CHECK, `:195` and
`:199` "(filled at return time)" under ARCHIVE USED and LITERATURE
USED. The brief orders the survey-quotes check run and pasted before
returning. The newest accept arm refused the return on it:
`runs/accept-2.out`, conjunct 6 FAILED, error_class lint, exit 1,
lint_detail naming the ten unanswered ARCHIVE and LITERATURE paths. A
return refused by its own acceptance arm cannot carry a verdict the
program may route on.

One assertion has no record either way: the second kill (pid 66737,
15:58:07) has no run record in `runs/`, and the report's "other
panes'" attribution for it (`:123`) rests on nothing. For pid 54115
the record contradicts the attribution (section 1).

## The lens (the four questions, `archive/dev/DD-archived.md:35`) and the cure

Verdict correct on its own numbers: no; its own run records refute the
line. Measurement sound: the run records are sound and decisive; the
environmental narrative is not (no dispatch-time measurement; the
first reading postdates eleven runs; a 13.27 s success at 15:58:26
contradicts the "would not survive" claim). Brief caused the outcome:
no; the brief pre-registered the measured outcome and its cure, and
the return departed from the brief. Cure missed: yes, and it is
half-executed.

The machine was rebooted after the report: swap now reads 0 MB used,
pressure level 1, and the watchdog restarted 2026-08-31 16:21:43 as
pid 1964 (log, read today), on the same 8192 MB swap line (on-disk
script `:28`). The bisection is one run from its answer: B4 (no
ascription) green in 12.51 s (`runs/bisect-4.out`), B6 (the domain
half) green in 140.69 s (`runs/bisect-6.out`), B8 (the codomain half,
the mirror) died at 224 s to the watchdog's swap branch, not to the
heap. The next coder dispatch should re-run B8 at heavy on the clean
machine; then either the fatal comparison gets its fix and the split
composition is retried, or the brief's pre-registered heap-wall NO-GO
lands with the split as the frame cure. Either way the return must
paste the survey-quotes output and fill the ARCHIVE and LITERATURE
sections the brief mandates. No new architecture question is raised;
every record the next dispatch needs is already in `runs/`.

## ARCHIVE USED

- archive/dev/DD-archived.md - read. `:35`: "The questions are: is the
  refusal correct on its own numbers; is the measurement sound; did
  the BRIEF cause the outcome; and is there a cure the return missed."
- archive/dev/ORCHESTRATION.md - read. `:87`: "A refusal, a NO-GO, a
  RED gate, a stop taken as the"; `:93`: "Four questions: is the
  refusal correct on its own".
- archive/dev/measurements/README.md - read. `:3`: "A **measurement
  record** is the raw output of a timing run, a profile or a". A
  report that quotes numbers must cite the record; here the report
  quotes none of the twelve records its own directory holds.
- archive/dev/PLAN-archived.md - declined: an archived plan index;
  nothing in it bears on this return's run records.
- archive/dev/TASKS-archived.md - declined: the archived L3.32-T task
  index; predates LJ-1 and this task.

## LITERATURE USED

- dev/literature/BIBLIOGRAPHY.md - declined: a source list for the rud
  route; no literature question is at stake in a report-vs-records audit.
- dev/literature/glossary-review-2026-08.md - declined: a glossary
  review; this review measures no term's provenance.
- dev/literature/devlin-errata.md - declined: Devlin errata classes;
  no mathematical content of the probe is judged here.
- dev/literature/primary-sources.md - declined: source fetch notes;
  not used by this audit.
- dev/literature/level-formula-slot-roles.md - declined: level-formula
  exposition; the attack never reaches the mathematics of the probe.
