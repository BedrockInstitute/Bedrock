# LJ-1.728-SPLIT report: the term is transcribed; the heavy measurement is blocked by the machine watchdog

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.728-SPLIT
obligation: agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda::grounded-from-complete
verdict: **STOP. Environment, not the term.** The written composition is
transcribed byte-identically
(`agents/tasks/LJ-1-728-SPLIT/Probe728Split.agda.txt`, module name and
header excepted; 0 non-comment line differs from 728's shape 4). No
Agda process on this machine can now survive long enough to check
anything: `scripts/ops/agda-watchdog.sh` kills every `agda` within its
20 s poll while system swap stays at or above 8192 MB
(`scripts/ops/agda-watchdog.sh:28,61-69,79`), swap is pinned at
8781.94 MB used of 9216 MB, and it has not dropped below 8192 MB since
at least 23:12 local. Five runs of this dispatch, floor shapes and
diagnostic, all died by SIGKILL from that branch, at 0.80 to 1.80 GB
RSS, none by heap. The W3 question, whether the composition checks at
`-M4g`, is UNMEASURED. This is not a heap wall of the term and no
NO-GO is stated; supply stays 0 and the obligation stays open. No
`review-of-*.md` is written, per the brief.

## 0. THE RUN

Written as a skeleton before any Agda run (C-22), filled as each fact
landed. No commit, no push. I wrote only inside
`agents/tasks/LJ-1-728-SPLIT/`. The pane caliber is
`-A64m -I0 -M4g`, the HEAVY tier
(`agents/tasks/LJ-1-728-SPLIT/runs/floor-2.out:1`,
`dev/pod/heads.toml:336-338`); I did not set `GHCRTS`; ONE Agda
process at a time, sequential. No postulate. Nothing lands in `src/`.

## 1. THE TRANSCRIPTION

The brief's term (`agents/tasks/LJ-1-728/Probe728.agda.txt:196-210`,
read in the main tree, read-only) already existed in full at shape 4.
`Probe728Split.agda.txt` is that file with exactly two changes:

- the module name, `LJ-1-728-SPLIT.Probe728Split`
  (`Probe728Split.agda.txt:34`);
- the header comment, which states this dispatch's record.

A diff of the file against its source, module line normalised, shows
0 differing non-comment lines. The obligation's type stands at
`Probe728Split.agda.txt:111`, the term at `:181`, the top-level export
at `:203`, the 692 pattern the brief names
(`agents/tasks/LJ-1-692/Probe692.agda:66`). `Completeness` is a
hypothesis (`:87-91`); `Convert` is never hypothesised: the plain
import of 692 and the opened constructed
`hull-convert-at-matrix` stand as 728 wrote them.

The file is delivered as `.agda.txt`: no run of it has ever completed
a typecheck, so the naming rule binds. If a later run checks, the
rename back is one `mv`.

## 2. THE BLOCKADE, MEASURED

**The killer.** `scripts/ops/agda-watchdog.sh` polls every 20 s
(`scripts/ops/agda-watchdog.sh:79`). Its death-spiral branch fires
when used swap is at or above `SWAP_MAX_MB`, 8192 MB
(`scripts/ops/agda-watchdog.sh:28,59,61-62`), and then kills the
biggest agda by RSS (`scripts/ops/agda-watchdog.sh:66-69`). With one
agda running, that one is the biggest. The kill is SIGKILL: no Agda
message, no crash report, `/usr/bin/time` prints
`command terminated abnormally`
(`agents/tasks/LJ-1-728-SPLIT/runs/floor-2.out:9`). A perl parent
forked for diagnosis reported `WIFSIGNALED`, `sig=9`, after 16 s, on
the run whose transcript is `runs/floor-2`'s successor state.

**The machine state.** At report time:
`vm.swapusage` reads
`total = 9216.00M  used = 8781.94M  free = 434.06M (encrypted)`.
System free memory is 81 percent and
`kern.memorystatus_vm_pressure_level` is 1, so only the swap branch
fires. The watchdog's own log has killed agda without interruption
since 23:12 local on this criterion
(`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log:190-218`,
93 kills dated 2026-08-28). The gap to the threshold at report time is
589.94 MB; the drift in the log is near 36 MB per hour downward. No
agda run of this campaign's closure fits in a 20 s poll window: the
warm floor shape alone needs about 15 s to load and check, and the
full composition at wide ran 382.82 s before ITS heap death
(`agents/tasks/LJ-1-728/lj-1.728-report.md:102`), two orders past the
window.

**My five killed runs.** All at the pane caliber, all killed by the
swap branch, none by heap:

| run | shape | s before kill | peak RSS B | kill record |
|---|---|---|---|---|
| `runs/floor-1.out` | floor, hole body | 4.04 | 810,647,552 | log:213, pid 5402 |
| `runs/floor-2.out` | floor, hole body | 13.19 | 1,802,665,984 | log:214, pid 7002 |
| perl diagnostic | same file | 16 | n/a | log:215, pid 8858 |
| `runs/floor-3.out` | floor, hole body | 4.93 | 804,683,776 | log:217, pid 41324 |
| `runs/floor-4.out` | floor, hole body | 12.53 | 1,319,550,976 | log:218, pid 44346 |

`floor-1` first read as a crash of `LJ-1-641.Probe641`
(`runs/floor-1.out:5-6`); the log line at `:213` names the same
second, so that attribution dissolves: every death is the watchdog.
Each run advanced the warm interface cache, and the kill interval my
watcher measured between the poll that freed the pane and the poll
that killed `floor-4` was about 14 s. Two further attempts after the
first kill were timed starts, disclosed here as such; they were not
restructures of a walling shape, because no shape of mine had walled.
I stopped the lottery at `floor-4`: a fifth run measures nothing new.

**The reach is machine-wide.** The worktree's own watchdog log, from
a second watchdog instance whose lock is dated 21:05 and whose last
entry is 00:02:27 (`_build/tools/agda-watchdog.log`, 198 kill lines,
ending `2026-08-29 00:02:27 KILLED agda pid=97461`), records other
workers' pids dying on the same criterion. The main log's `:216`
kills pid 40449 at 00:16:58, which is not mine: another pane's agda is
dying too. The single-instance lock
(`scripts/ops/agda-watchdog.sh:41-45`) is per-tree, so two checkouts
ran two killers at once until 00:02:27; only the main instance, pid
14720, runs now.

**Why I did not route around it.** Renaming the binary, or any other
evasion of the `agda$` match, would defeat a backstop the owner
installed after a measured seizure and hard reboot
(`scripts/ops/agda-watchdog.sh:2-3,28-34`). The blocker is the
owner's to lift.

## 3. WHAT THE RUNS STILL MEASURED

Partial, and only partial. The closure through 673 elaborates warm in
about 13 s (`runs/floor-4.out:8`, killed at 12.53 s inside 673's
check). Partial RSS peaks sit at 0.80 to 1.80 GB, far under the 4 GB
cap, but no run completed, so no floor price and no wall exist. The
brief's premise 3 numbers remain 728's wide-tier measurements; this
dispatch measured no heap wall and confirms none.

## 4. W2

Nothing is written twice. `hull-convert` is 689's generic transport;
692 instantiates it at `matrix₃` (`Probe692.agda:63-66`); this file
restates no predecessor statement and adds no new one. The only lines
that are not 728's are the header and the module name.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **The unblock is the owner's.** Swap must fall below 8192 MB, a
   gap of 589.94 MB at report time, or the threshold must move.
   Reclaim or reboot. My `vmmap` spot checks of the resident
   suspects found small swapped footprints (Bitcoin-Qt, the largest,
   about 136 MB), so the holder is diffuse or unlisted; a full sweep
   is the owner's follow-up.
2. **Then W3 is one run away.** The term stands transcribed. The
   sequence per the 2026-08-23 ruling: floor shape first
   (`runs/FLOOR728SPLIT.agda.txt`, hole body), then the full file
   renamed to `.agda`, one Agda process, cap 1800 s. GO is
   `grounded-from-complete` on the meter; a heap wall now HAS the
   restructure record behind it (728's six shapes at wide, this
   dispatch's five kills at heavy).
3. **Do not re-read the wall attribution from 728 as heavy fact.**
   Premises 1 to 3 of this brief are wide-tier numbers
   (`agents/tasks/LJ-1-728/lj-1.728-report.md:19,90`). At 4 GB the
   floor region has margin; the assembly region may pass.

## SURVEY QUOTES CHECK

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT
check-survey-quotes: LJ-1-728-SPLIT FAILS the survey duty:
  unanswered: the return never names archive/dev/DD-archived.md
  unanswered: the return never names archive/dev/ORCHESTRATION.md
  unanswered: the return never names archive/dev/PLAN-archived.md
  unanswered: the return never names archive/dev/STATUS-archived.md
  unanswered: the return never names archive/dev/TASKS-archived.md
  unanswered: the return never names dev/literature/BIBLIOGRAPHY.md
  unanswered: the return never names dev/literature/devlin-errata.md
  unanswered: the return never names dev/literature/glossary-review-2026-08.md
  unanswered: the return never names dev/literature/primary-sources.md
  unanswered: the return never names dev/literature/rudimentary-functions.md

A return names every path the program injected, and quotes one line read per
file: the quote must occur AT the cited line in the cited file. A written
decline is compliance.
CHECKER EXIT=1
```

This run predates the ARCHIVE USED and LITERATURE USED sections below.
Those sections answer the duty; the paste above is the before-state the
brief asked for.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not run a second Agda process.
- I did not write in `src/`.
- I did not rewrite any predecessor term.
- I did not inhabit `Completeness`, and I did not hypothesise `Convert`.
- I did not postulate, and no delivered file carries a hole except the
  floor shape, whose hole is its design.
- I did not touch the watchdog, its lock, its log, or any other
  pane's processes.
- I did not write a `review-of-*.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-728-SPLIT/`:

- `Probe728Split.agda.txt`, 728's shape 4 transcribed (module name and
  header only)
- `lj-1.728-SPLIT-report.md`, this report
- `runs/run.sh`, the runner copied from 725-SPLIT's, cap added
- `runs/FLOOR728SPLIT.agda.txt`, the floor shape, hole body
- `runs/floor-1.out` to `runs/floor-4.out`, the killed transcripts

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: declined, not read. This stop is a
  machine resource blockade measured at my own pane; no archived
  dispatching rule bears on it.
- `archive/dev/DD-archived.md`: declined, not read. The coder clauses
  this dispatch answers to live in the slot file and the brief; the
  archived DD series was not opened.
- `archive/dev/PLAN-archived.md`: declined, not read. The live
  direction is `dev/pod/direction.md`; no plan phase bears on a
  single-probe blockade stop.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`; no archived status was consulted.
- `archive/dev/TASKS-archived.md`: declined, not read. The
  predecessors this task transcribes and imports (728, 692, 718) were
  read at their live sites under `agents/tasks/`.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. A
  raw `.agda.txt` probe coins no term and proposes no glossary entry.
- `dev/literature/devlin-errata.md`: declined, not read. The probe
  coins no reading of Devlin 5.2; the term is 728's, unchanged.
- `dev/literature/primary-sources.md`: declined, not read. This
  dispatch fetched no source beyond the tree's own files.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No external
  source is cited by this dispatch.
- `dev/literature/rudimentary-functions.md`: declined, not read. The
  obligation's statement and its pieces come from the 728, 692 and 718
  task records, not from the literature extracts.
