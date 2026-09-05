# LJ-1.728-SPLIT-SPLIT-SPLIT-SPLIT report: B8, the codomain-ascribed convert, heap-walls at -M4g; the floor is green, so the wall is the comparison

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.728-SPLIT-SPLIT-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT/Probe728SSSS.agda::conv0
verdict: **NO-GO. Heap wall, not a statement.** `conv0` does not check
at `-M4g`: `runs/probe-1.out:5,8,26` (Heap exhausted at 4096 MB after
1593.73 s, EXIT=251). The floor is green
(`runs/floor-1.out:22-23,40`: 246.48 s, 2.51 GB), so the wall is the
codomain comparison and not the frame. This is the brief's
pre-registered heap-wall outcome: the split composition waits for a
later brief, Convert's body is not retried (premise 5), and no
`review-of-*.md` is written because a resource wall states nothing
about the mathematics. Supply stays 0; the obligation stays open.

Written as a skeleton before anything ran (C-22), filled as each fact
landed. No commit, no push. Only this task directory is touched.

## 0. THE ENVIRONMENT, MEASURED AT DISPATCH

Dispatch-time readings, taken before any Agda process was started:

- `sysctl vm.swapusage`: total 3072.00M, used 1584.75M, free 1487.25M.
  The on-disk watchdog's swap-spiral line is 8192 MB
  (`/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`), and
  the branch is live in the on-disk copy, so the margin at dispatch was
  about 6.6 GB.
- `kern.memorystatus_vm_pressure_level`: 1 (normal).
- Free percentage: 90.
- No agda process running at dispatch (`ps ax -o pid=,rss=,comm=`,
  empty for agda).
- The watchdog runs as main-tree pid 1964, restarted 2026-08-31
  16:21:43 local (`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`,
  last line), and its log names no kill after that restart. Both runs
  of this dispatch landed with no kill recorded.
- Pane caliber, read at dispatch: `GHCRTS=[-A64m -I0 -M4g]`, the HEAVY
  tier. It was never set or changed by me; the runner only echoes it
  into each `.out` (`runs/run.sh:11`). Both `.out` files carry it.

## 1. THE TRANSCRIPTION

Source: `VendorB8.agda.txt`, this task directory, delivered by the
program (the worktree's `Bisect8SSS.agda.txt`). Target:
`Probe728SSSS.agda.txt`. Measured with comments and blank lines
stripped from both sides: **exactly two non-comment lines differ**,
the module line (`VendorB8.agda.txt:22` to
`Probe728SSSS.agda.txt:28`) and the added top-level export
`conv0 = Build.conv0` (`Probe728SSSS.agda.txt:66`), the export the
brief orders and the vendor, a runs/ bisect file, did not carry. The
plain `import ... as P692` stands (`Probe728SSSS.agda.txt:41`), the
AmbiguousName correction the predecessor measured
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/FLOOR728SSS.agda.txt:36-38`):
the unqualified alias of the same spelling must not enter short scope
beside the Spend-opened name.
The supplier is [LJ-1.692]'s constructed `hull-convert-at-matrix`,
opened from `P692.Spend` (`Probe728SSSS.agda.txt:55-56`), never
hypothesised; its own verdict is GO
(`agents/tasks/LJ-1-692/lj-1.692-report.md:9`).

The file is delivered as `.agda.txt`: no run of it has completed a
typecheck, so the naming rule binds. The obligation name
`Probe728SSSS.agda::conv0` is stale until a later run checks and the
file is renamed back; the rename is one `mv`.

## 2. THE FLOOR

`runs/FLOOR728SSSS.agda.txt`: the probe with only the term's body
holed, the top-level export kept (the FLOOR728SSS pattern, the
predecessor's frame floor with its obligation body holed at
`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/FLOOR728SSS.agda.txt:170`).
Because the obligation's domain is a SOLVED meta, the holed floor
reports unsolved metas at the end of its check; the elapsed time and
peak heap before that error are the frame's own cost.

**MEASURED (runs/floor-1.out): 246.48 s, peak RSS 2.51 GB
(2508128256 B), EXIT=42, no Heap-exhausted line.** The exit is the two
by-construction unsolved metas
(`runs/floor-1.out:15-21`: the domain meta at `FLOOR728SSSS.agda:53`
and the holed body's interaction meta at `:55`), reported only after
the whole frame checked. The run also paid the one-time cold closure
of this fresh worktree (`runs/floor-1.out:5-14`: Probe652, Probe641,
Probe667, Probe667's W3, Probe520, Probe673, Probe692, Probe686,
Probe689, Probe680) and still
fit `-M4g` with 1.5 GB to spare. For scale: the predecessor's floor,
the SSS frame alone, heap exhausted at 1760.65 s
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/floor-2.out:5,8`); B6,
the mirror term, whole file warm, ran 140.69 s / 1.85 GB
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-6.out:5,6,23`).

**The frame is not the defect.** The floor is green under the cap, so
the probe run proceeded.

## 3. THE RUNS

### runs/floor-1.out (the floor, section 2)

started 2026-08-31T09:26:19Z, ended 2026-08-31T09:30:25Z, cap 1800 s,
`GHCRTS=[-A64m -I0 -M4g]` (`runs/floor-1.out:1-3,40,41`). EXIT=42,
246.48 s real, maximum resident set size 2508128256 B
(`runs/floor-1.out:22-23`). Machine swap before the run: used
1528.69 MB. The temp run copy `runs/FLOOR728SSSS.agda` was removed
after the run; the delivered floor is `runs/FLOOR728SSSS.agda.txt`
(it cannot typecheck by construction, so the naming rule binds).

### runs/probe-1.out (THE W3 RUN)

started 2026-08-31T09:31:01Z, ended 2026-08-31T09:57:35Z, cap 1800 s,
`GHCRTS=[-A64m -I0 -M4g]` (`runs/probe-1.out:1-3,26,27`). The only
`Checking` line names the probe module itself
(`runs/probe-1.out:4`): the interfaces the floor left were reused, so
**1593.73 s is the probe module's own check, cold-closure-free**
(`runs/probe-1.out:8`). `agda: Heap exhausted; Current maximum heap
size is 4294967296 bytes (4096 MB)` (`runs/probe-1.out:5-6`), maximum
resident set size 5333729280 B (`runs/probe-1.out:9`), EXIT=251
(`runs/probe-1.out:26`). Machine swap before the run: used 1257.56 MB.
No watchdog kill was logged in the window; the wall is the GHC heap
cap, reached from inside the run. After the run the probe was renamed
to `.agda.txt` (section 1).

## 4. WHAT THE NEXT BRIEF NEEDS

**W3 is measured, and the answer is NO.** The codomain-ascribed
convert does not check at `-M4g`. The bisection of the fatal
comparison is now complete, every arm measured:

| arm | shape | verdict | record |
|---|---|---|---|
| B4 | no ascription | green 12.51 s | `agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-4.out:5,23` |
| B6 | domain spelled, codomain solved | green 140.69 s | `agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-6.out:5,23` |
| B8 | domain solved, codomain spelled | **heap wall 1593.73 s** | `runs/probe-1.out:5,8` |
| B2 | both ascribed inline | heap wall 1525.50 s | `agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-2.out:5,8` |

**The wall's site is now pinned by two runs of this dispatch.** The
floor carries the same imports, the same `P673.At` application, the
same `P692.Spend` application, the same `Build` scaffold, the same
spelled codomain TYPE and the same solved-meta domain, and it fits
`-M4g` in 246.48 s with the whole cold closure inside that figure.
The probe differs from the floor by exactly one thing, the body
application `hull-convert-at-matrix ca cp a sat` checked against the
spelled codomain, and it walls. The heap is spent in the W3
comparison: elaborating [LJ-1.692]'s constructed Convert against the
freshly spelled `⟨ _ ∷ _ ∷ _ ∷ [] P652.⊨ₚ P667.matrix₃ ⟩` at this
file's own module parameters.

**Why no restructuring was tested in this dispatch.** The clause asks
for a restructure tested under the same cap, or a specific reason none
is possible; here the reason is measured, twice over. (1) A frame
restructure cannot cure `conv0`: the frame already fits at one sixth
of the cap, measured on this task's own floor. (2) The comparison-side
restructures are the split the predecessor series already measured at
their own sites: the ambient half heap-walled at 1704.19 s
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/amb-1.out:5,8`) and the
ascribed-conversion shape heap-walled at 1408.34 s
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/conv-1.out:5,8`), while
the frame and hull halves are green
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/frame-1.out:5,23`,
`.../runs/hull-2.out:5,23`). A fourth Convert wrap is what premise 5
forbids, and B2, B8, conv-1 and amb-1 are its four measured walls.

**What the cure must be, and who owns it.** The brief pre-registered
it: a heap-wall NO-GO lands the frame split, and a LATER brief retries
the split composition. The split's two green halves and two walled
halves are on the meter (numbers above); the missing composition is
`grounded-from-complete`, and its next attempt should reuse the
split's named interface types, not Convert's body. This report writes
no `review-of-*.md`: a resource wall is not a statement about the
mathematics, and the brief orders exactly that.

**Prices, measured, for the next brief's estimates.** This frame
family, warm: 140.69 s to check whole when the comparison is solved
(B6); 1593.73 s to wall when the codomain is ascribed (B8, this
dispatch); floor of the frame itself, cold closure included,
246.48 s / 2.51 GB. The probe chain's one-time closure in a fresh
worktree is inside the floor's figure and is paid once per worktree.

**DD4 / W2 answer.** The reuse rule's home names it: MAXIMUM REUSE is
the architecture's objective and the same rule as WRITE IT GENERIC
(`archive/dev/DD-archived.md:22`). This dispatch wrote no mathematics
at all: the probe instantiates [LJ-1.689]'s generic `hull-convert`
through [LJ-1.692]'s instantiation at `matrix₃`, and the transcription
is byte-faithful to the vendor except the module line and the export
(section 1). The fixed form was never in play, so there is no conflict
to report and no price to re-state.

**What could not close.** `conv0` stays open with supply 0; a heap
wall inhabits nothing. The file is `.agda.txt` until a green run
renames it. No hypothesis about `Convert`'s truth is stated or
implied by this NO-GO in either direction: B6 green and B8 walled
together say the two halves of the comparison are priced apart, and
nothing more.

## 5. THE RE-DISPATCH OF 2026-09-02

The program re-dispatched this task on 2026-09-02 (a park-episode
replay; this task had sat PARKED under the transfer-park row since
2026-08-31). This episode ran NO Agda process and re-measured
nothing, for one measured reason: the coder clause forbids rerunning
the SAME code hoping for a different result, and nothing here changed
(the probe file, its caliber `-M4g`, the 1800 s cap, the machine).
The episode verified every `file:line` in this report against the
files and corrected seven stale pointers (section 1's four probe-file
pointers, the AmbiguousName pointer, section 2's meta lines, the
floor-pattern pointer; the probe's header comment was edited after
the runs recorded here, which had shifted the numbers the first
writing used). No measured figure changed.

Environment at re-dispatch, measured before any decision: no agda
process (`ps ax`), the watchdog still pid 1964 started 2026-08-31
16:21:42 (`ps ax -o pid,lstart,command`), pressure level 2, swap
used 2503.31 MB of 4096 MB (the on-disk death-spiral line stays 8192
MB, `/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`),
pane caliber read `GHCRTS=[-A64m -I0 -M4g]`, HEAVY, unchanged.

One fact this episode adds, for the next brief: the split this park
funded has run and its un-ascribed `conv0` is committed in the main
tree (`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/Probe728SSSSS.agda`,
done commit ebec66be; its GO run is 11.76 s warm, RSS 1.88 GB,
EXIT=0, `agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/runs/probe-1.out:4,5,6,23`).
That is the B4 shape at
a successor path; it does not discharge THIS obligation, whose W3
question was the CODOMAIN-ASCRIBED convert at heavy. The answer here
stands: NO at `-M4g`, heap wall, and the successor's GO is the
measured proof that the ascription, not the term, is what walls.
Verdict, supply and the `.agda.txt` naming are unchanged.

A second replay episode landed the same day, 21:35 local. It ran NO
Agda process, for the same measured reason as the first: the probe
file, its pane caliber `-M4g`, the 1800 s cap and the machine are
unchanged since the 2026-08-31 runs, and rerunning the SAME code is
forbidden. The episode re-verified every pointer this report carries:
the two-line transcription diff (module line and the `conv0` export,
nothing else); `runs/probe-1.out:4,5,8,9,26,27`; the floor's metas,
time and exit (`runs/floor-1.out:15,19,22,23,40`); all eight
predecessor runs behind section 4's table (bisect-4 12.51 s EXIT=0,
bisect-6 140.69 s EXIT=0, bisect-2 1525.50 s EXIT=251, amb-1
1704.19 s EXIT=251, conv-1 1408.34 s EXIT=251, frame-1 15.08 s
EXIT=0, hull-2 243.77 s EXIT=0, floor-2 1760.65 s EXIT=251); the
successor's committed GO (`git show ebec66be`; its
`runs/probe-1.out:5,6,23` reads 11.76 s, 1880752128 B, EXIT=0); and
the spiral line (`scripts/ops/agda-watchdog.sh:28`,
`SWAP_MAX_MB=$((8*1024))`). Environment at this episode, read before
any decision: no agda process (`ps ax`); pane caliber
`GHCRTS=[-A64m -I0 -M4g]`, HEAVY, unchanged; swap used 4105.31 MB of
5120 MB, below the 8192 MB spiral line; pressure level 1; free
81 percent; watchdog pid 1964, no kill logged since its 16:21:43
start. The verdict, the supply figure and the `.agda.txt` naming are
unchanged.

A third replay episode landed the same day, 23:14 local. It ran NO
Agda process, for the same measured reason as the first two: the
probe file, its pane caliber `-M4g` and the 1800 s cap are unchanged,
and every input the probe reads is byte-identical (`git log --oneline
--since="2026-08-31 17:00"` over `agents/tasks/LJ-1-692/Probe692.agda`,
`agents/tasks/LJ-1-652`, `agents/tasks/LJ-1-667`,
`agents/tasks/LJ-1-673` and `src/` is empty), so a rerun would rerun
the SAME code, which is forbidden. The episode adds one measured
fact, one measured correction and one measured path note.

**The fact: the B8 wall is no longer single-site.** The sibling
worktree re-ran the same shape the same morning as
`runs/bisect-8b.out`, 2026-08-31 10:13:54Z to 10:40:51Z, module
`LJ-1-728-SPLIT-SPLIT-SPLIT.runs.Bisect8SSS`, same caliber `-M4g`:
Heap exhausted at 4096 MB in 1617.03 s, peak RSS 5194448896 B,
EXIT=251
(`.pod-state/worktrees/LJ-1-728-SPLIT-SPLIT-SPLIT/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-8b.out:5,8,9,26`).
It started 16 minutes after this task's probe-1 walled. Section 4's
B8 row now rests on two independent heap walls of one comparison
under one cap, which is stronger evidence that the wall follows the
codomain ascription and not this worktree's file.

**The correction: the vendor equals the predecessor's Bisect8SSS in
code, not in comments.** Section 1 calls `VendorB8.agda.txt` "the
worktree's `Bisect8SSS.agda.txt`". Measured now, the two differ in
comments only: the sibling's copy carries a postscript at its lines
10-16 recording the 8b rerun, which the vendor, snapshotted earlier,
predates (a diff of the two files shows the vendor's lines 10-12
against the sibling's 10-16, and every differing line is a `--`
comment). The code-line identity behind section 1's two-line
transcription diff is unchanged.

**The path note.** The predecessor task directory is tracked nowhere
in this repository (`git log --all --
agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/` is empty; its admit commit
`80ceb280` touches only `dev/pod/table.toml`), so section 4's
predecessor citations resolve only inside the sibling worktree at
`.pod-state/worktrees/LJ-1-728-SPLIT-SPLIT-SPLIT/`. All eight rows of
section 4's table were re-read there this episode and match: bisect-4
12.51 s EXIT=0, bisect-6 140.69 s EXIT=0, bisect-2 1525.50 s
EXIT=251, amb-1 1704.19 s EXIT=251, conv-1 1408.34 s EXIT=251,
frame-1 15.08 s EXIT=0, hull-2 243.77 s EXIT=0, floor-2 1760.65 s
EXIT=251. The successor's committed GO was re-read at `ebec66be`
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/runs/probe-1.out:4,5,6,23`:
11.76 s, 1880752128 B, EXIT=0).

Environment at this episode, read before any decision: no agda
process (`ps ax`); pane caliber `GHCRTS=[-A64m -I0 -M4g]`, HEAVY,
unchanged; swap used 4049.31 MB of 5120 MB, below the 8192 MB spiral
line (`/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`,
`SWAP_MAX_MB=$((8*1024))`); pressure level 1; watchdog pid 1964
alive, no kill logged since its 2026-08-31 16:21:43 start
(`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`, last
line). The verdict, the supply figure and the `.agda.txt` naming are
unchanged.

A fourth replay episode landed the same day, 23:42 local. It ran NO
Agda process, for the same measured reason as the first three: the
probe file, its pane caliber and the 1800 s cap are unchanged, and
every input the probe reads is byte-identical (`git log --oneline
--since="2026-08-31 17:00"` over `agents/tasks/LJ-1-692/Probe692.agda`,
`agents/tasks/LJ-1-652`, `agents/tasks/LJ-1-667`,
`agents/tasks/LJ-1-673` and `src/` is empty), so a rerun would rerun
the SAME code, which is forbidden. The episode adds one operational
finding about the acceptance tool.

**The finding: `accept.py` picks the tree it measures from its own
file path.** The episode's first acceptance invocation named the MAIN
checkout's copy by absolute path. The script resolves
`ROOT = find_root(__file__)` (`scripts/pod/accept.py:69`), so that run
measured the MAIN tree's working state and not this worktree: its fact
list carried the program's own in-flight edits (`dev/pod/queue.toml`,
`dev/pod/maintainer-backlog.md`, `dev/pod/transitions/2026-09.jsonl`),
conjunct 6 failed lint on `dev/pod/maintainer-backlog.md:69`, a file
this task never touched, and the record was written into the MAIN
tree's mirror of this runs directory. That record is false for this
task, and it was removed. The re-run through this worktree's own
script path is the episode's record: `runs/accept-5.out`, started
2026-09-02 23:55:03 (`runs/accept-5.out:9`), caliber `-A64m -I0 -M4g`
(`runs/accept-5.out:5`), all six conjuncts held
(`runs/accept-5.out:11-16`), EXIT=0 (`runs/accept-5.out:23`),
obligations delta 0, wall 0.0 s, error class None
(`runs/accept-5.out:20-22`), and `agda_vacuous: true` because the
obligation's file is `.agda.txt` and conjunct 1 has no runnable
target. The record reads `# agda slots during 1`
(`runs/accept-5.out:7`): the launcher registry held one OTHER live
Agda slot during the measurement, not this task's, which started no
process.

Environment at this episode, read before any decision: no agda process
under this task (`ps ax`); pane caliber `GHCRTS=[-A64m -I0 -M4g]`,
HEAVY, unchanged; swap used 4033.31 MB of 5120 MB, below the 8192 MB
spiral line
(`/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`,
`SWAP_MAX_MB=$((8*1024))`); pressure level 1; watchdog pid 1964 alive,
no kill logged since its 2026-08-31 16:21:43 start
(`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`, last
line). The verdict, the supply figure and the `.agda.txt` naming are
unchanged.

## SURVEY QUOTES CHECK

Ran before return, as ordered. This worktree has no `.venv` of its
own; the pinned interpreter of the main checkout ran the gate, as in
the 2026-08-31 episode. Fresh output of the second 2026-09-02
episode (21:35 local), run after this episode's section 5 paragraph
was written:

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT
check-survey-quotes: LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

Fresh output of the third 2026-09-02 episode (23:14 local), run after
the third-episode paragraph was written:

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT
check-survey-quotes: LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

Fresh output of the fourth 2026-09-02 episode (23:59 local), run after
the fourth-episode paragraph was written:

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT
check-survey-quotes: LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - read, and it is the rule my return
  answers (DD4/W2, section 4): "**MAXIMUM REUSE is the architecture's
  objective, and it is the same rule as WRITE IT GENERIC.**"
- archive/dev/ORCHESTRATION.md - declined: archived orchestration
  notes; nothing in it bears on a build-and-measure dispatch.
- archive/dev/PLAN-archived.md - declined: an archived plan index;
  this dispatch plans nothing.
- archive/dev/TASKS-archived.md - declined: the archived L3.32-T task
  index; it predates LJ-1 and this task.
- archive/dev/STATUS-archived.md - declined: archived L3 status rows;
  they predate LJ-1 and name no open obligation of this campaign.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md - declined: a glossary
  provenance review; this report coins no term.
- dev/literature/fine-structure.md - declined: Devlin II.5 notes; the
  dispatch runs a probe and reads no set theory.
- dev/literature/BIBLIOGRAPHY.md - declined: the retired rud route's
  source list; no literature question is at stake in a heap-wall
  measurement.
- dev/literature/devlin-errata.md - declined: Devlin error classes;
  no Devlin text is judged here.
- dev/literature/primary-sources.md - declined: source fetch notes;
  not used.
