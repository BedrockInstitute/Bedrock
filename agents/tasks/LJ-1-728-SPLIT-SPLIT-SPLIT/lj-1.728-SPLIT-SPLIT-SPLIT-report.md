# LJ-1.728-SPLIT-SPLIT-SPLIT report: the transport is the wall, terminal at -M4g in every shape tried

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.728-SPLIT-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/Probe728SSS.agda::grounded-from-complete
verdict: **NO-GO, heap wall, pre-registered. The transport is the wall, and it is terminal at this caliber in every shape tried.**
The term is not closed. This dispatch ran nine cells at the heavy
caliber: the B8 mirror, two composition floors, two interface
refreshes, and four ambient-assembly cells. Every cell that contains
a transport or a spelled-codomain comparison walls; every cell that
contains neither is green. The bisect localized the
wall to ONE site: `amb`, the transport of the conversion's output
from the hull codes' values to `(Lset δ, δ)` (B8 closed the
codomain-comparison question first, section 3). The split the brief
pre-registered as the cure was executed and measured: the ambient
slot ITSELF walls. This is a resource wall, so no `review-of-*.md`
is written, per the brief. The obligation stays open,
`Probe728SSS.agda` does not exist, and the meter name keeps
supply 0.

## 0. THE ENVIRONMENT AT DISPATCH, MEASURED BEFORE ANY RUN

The two predecessor stops of this task were refused for, among other
things, having no dispatch-time environment reading. This one is taken
before the first run, and again mid-flight with the first run at peak
RSS. Both readings:

- `vm.swapusage`: total 2048.00M, used 1145.50M then 1129.50M, free
  902.50M then 918.50M. Used swap is **6846.5 MB below the 8192 MB
  kill line**, and the swap TOTAL is now 2048 MB: it was 30720 MB at
  the second stop's reading and 17408 MB at the first critic's.
- `kern.memorystatus_vm_pressure_level`: 1.
- `memory_pressure -Q`: free percentage 68 percent then 66.
- The watchdog: pid 1964, `/bin/zsh
  /Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh`, started
  2026-08-31 16:21:42 local (`ps ax -o pid,lstart,command`), the
  on-disk script with `SWAP_MAX_MB=$((8*1024))` at
  `/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`, the
  swap branch at `:61-62`, the 20 s poll at `:79`. This is the same
  operative copy the second critic identified; no agda process was
  running at dispatch and no kill appears in
  `/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log` today.
- No agda process of any pane was running at dispatch (`pgrep -x
  agda` empty).

Premise 3's owner-approved start condition, "swap below 8192 MB, then
one heavy run", is TRUE at dispatch for the first time in this task's
history. The reboot the first critic recorded
(review-of-LJ-1-728-SPLIT-SPLIT-SPLIT-1.md, "The machine was rebooted
after the report") has held: the owner lifted the blockade. No run of
this dispatch was killed by the watchdog, and the log carries no kill
today.

## 1. WHAT THIS DISPATCH DID

In order, one Agda process at a time, pane caliber `-A64m -I0 -M4g`
(read from the environment, never set by me), cap 1800 s each:

1. Preserved the second dispatch's byte-identical transcription as
   `runs/Ascribed728SSS.agda.txt` (it is the only record of
   [LJ-1.728-SPLIT]'s term in this worktree; the source worktree is
   absent here, as the first critic measured).
2. Re-ran **B8**, the codomain-mirror bisect with no verdict
   (killed by the swap branch at 223.82 s in the second dispatch's
   window, `runs/bisect-8.out:5,26`), as `runs/Bisect8SSS.agda`, out
   to `runs/bisect-8b.out`: **heap wall** (section 3.1).
3. Wrote the cured single-file composition (the transcription minus
   the spelled-codomain comparison; preserved at
   `runs/Cure1File728SSS.agda.txt`) and ran its floor
   `runs/CureFloor728SSS.agda.txt`: **heap wall**
   (`runs/curefloor-1.out`, 1673.38 s, RSS 5.26 GB).
4. Refreshed the two stale interfaces (`frame-2`: green 14.41 s;
   `hull-3`: green 235.43 s; the sources carry post-run header edits,
   so the second dispatch's interfaces were stale at
   `_build/2.8.0/agda/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/`,
   sources 15:54:53 local against interfaces 13:38:40 and 13:44:15).
5. Wrote the split composition `Probe728SSS.agda.txt` (imports the
   two green halves as interfaces, the obligation type declared
   locally, `conv0`/`amb`/`mkWit` local) and ran its floor
   `runs/Cure2Floor728SSS.agda.txt`: **heap wall**
   (`runs/cure2floor-1.out`, 1349.39 s, RSS 5.55 GB).
6. Bisected the composition floor by RESTRUCTURING (never a rerun):
   interfaces alone green in 5.34 s (`runs/load-1.out`, 763 MB);
   ambient assembly without `conv0` **heap wall**
   (`runs/ambonly-1.out`, 1261.96 s); `amb` alone **heap wall**
   (`runs/amb2-1.out`, 1725.96 s); `amb` rebuilt as ONE compound
   subst over `ΣPathP` **heap wall** (`runs/ambcompound-1.out`,
   1571.71 s). The wall is `amb`, the transport, and it is terminal
   at this caliber in every shape tried.

Two scope notes measured on a 2 s toy before any heavy run was spent
on them: a plain open of Frame.Build followed by a local declaration
of the same name is ClashingDefinition; module aliases do enter
`using`-lists. Files that cannot typecheck are named `.agda.txt` per
the naming rule; every run record in `runs/` carries GHCRTS, a start
stamp, an end stamp and EXIT= (`runs/run.sh:9-17`).

## 2. THE MEASUREMENTS

Second dispatch's matrix (the background this dispatch started from;
each row's record stands in `runs/`):

| run | shape | verdict |
|---|---|---|
| `runs/bisect-4.out` | bare term, no ascription | green 12.51 s |
| `runs/bisect-6.out` | domain spelled, codomain `_` | green 140.69 s |
| `runs/bisect-2.out` | bare term, both ends spelled | wall 1525 s |
| `runs/conv-1.out` | applied, both ends spelled | wall 1408 s |
| `runs/amb-1.out` | conv + amb + mkWit, AmbientAt-spelled | wall 1704 s |
| `runs/floor-1.out`, `runs/floor-2.out` | frame + ascribed conv, body holed | wall 2x |
| `runs/frame-1.out` | frame without the ascribed conv | green 15.08 s |
| `runs/hull-2.out` | hullClosed alone | green 243.77 s |

This dispatch's cells:

| run | shape | verdict |
|---|---|---|
| `runs/bisect-8b.out` | B8: domain `_`, codomain spelled | wall 1617.03 s, 5.19 GB |
| `runs/curefloor-1.out` | single-file cure, body holed | wall 1673.38 s, 5.26 GB |
| `runs/frame-2.out` | frame interface refresh | green 14.41 s |
| `runs/hull-3.out` | hull interface refresh | green 235.43 s |
| `runs/cure2floor-1.out` | split composition, body holed | wall 1349.39 s, 5.55 GB |
| `runs/load-1.out` | the two interfaces, nothing local | green 5.34 s, 763 MB |
| `runs/ambonly-1.out` | obligation type + amb + mkWit (h abstract) | wall 1261.96 s, 5.5 GB |
| `runs/amb2-1.out` | obligation type + amb only | wall 1725.96 s, 5.5 GB |
| `runs/ambcompound-1.out` | amb as one compound subst over `ΣPathP` | wall 1571.71 s, 5.15 GB |

Every run: heavy caliber `-A64m -I0 -M4g` from the pane, cap 1800 s,
one Agda process at a time, runner `runs/run.sh`.

## 3. WHAT THE WALL IS, AND WHAT IT IS NOT

**The B8 verdict, and the completed bisection.** `runs/bisect-8b.out`:
Heap exhausted at 4096 MB in 1617.03 s, peak RSS 5.19 GB, EXIT=251,
on a machine with swap used 1113-1145 MB of 2048 MB total, pressure
level 1, free 66-68 percent, no watchdog kill. With
`runs/bisect-6.out` green at 140.69 s, the bisection the second
dispatch started is COMPLETE: **the codomain comparison alone is
fatal.**

**The wall this dispatch adds is the transport.** The mathematics
forces a transport: the hull code search (`runs/Frame728SSS.agda`,
`codeOf`) delivers the codes only PROPOSITIONALLY at `δ` and
`Lset δ`, so the conversion's output at
`(fst (val ca), fst (val cp), fst a)` must be carried to
`(Lset δ, δ, fst a)` inside the obligation's Sigma. Four shapes of
the ambient assembly measured wall across the two dispatches:
AmbientAt-spelled two-subst (`runs/amb-1.out`), literal two-subst
(`runs/amb2-1.out`), one compound subst over `ΣPathP`
(`runs/ambcompound-1.out`), and the assemblies containing them
(`runs/ambonly-1.out`, `runs/cure2floor-1.out`,
`runs/curefloor-1.out`). No shape of the composition that contains a
transport checks at `-M4g`; every cell that does not contain one is
green.

**What this measurement does NOT cover** (C-42, its own law): other
architectures, in particular any frame where the transport's family
carries no `⊨ₚ matrix₃` elaboration (for example a row-free or
code-level statement of the ambient reading, the mathematician's
call, not mine); calibers other than `-M4g` (I may not set
`GHCRTS`); and other SITES of the same transport shape, which this
task never named. The target itself shows no Tarskian or cardinality
obstruction: every piece around the transport is measured
constructible at this caliber (frame, hullClosed, conv0's domain
check, interfaces), so the obstruction is elaboration cost, not the
statement's truth (D-10).

## 4. WHAT THE NEXT BRIEF NEEDS

1. **The decision is the owner's, and it is a caliber-or-architecture
   fork.** (a) A wider heap for this frame: the wall peaks sit
   consistently at 5.15-5.55 GB RSS against the 4096 MB cap, so a
   heavy tier at roughly `-M8g` would re-open the composition
   question on TODAY'S tree with no new mathematics; that is a
   ruling against `dev/pod/heads.toml`, not something I may set.
   (b) An architecture where the transport's family never carries
   the `⊨ₚ matrix₃` elaboration: the mathematician's move; the split
   files and this dispatch's cells are its measurements.
2. **The split stands and is green**: `runs/Frame728SSS.agda` and
   `runs/HullHalf728SSS.agda` typecheck at heavy (frame-2 14.41 s,
   hull-3 235.43 s) with FRESH interfaces; any future frame that
   needs the hull half or the frame should import them rather than
   restate (W2), and any future heavy object prices its floor first
   (2026-08-23 ruling).
3. **The transcription record is intact**:
   `runs/Ascribed728SSS.agda.txt` is the second dispatch's
   byte-identical transcription; `runs/Cure1File728SSS.agda.txt` is
   this dispatch's single-file cure; `Probe728SSS.agda.txt` is the
   split composition, staged and unrun (its floor is the wall). If
   any fork re-opens the term, start from the split composition, not
   from the single file: its floor is 20 percent cheaper and its
   pieces are interface-fresh.

## SURVEY QUOTES CHECK

Ran before returning, as the brief orders:

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT-SPLIT-SPLIT
check-survey-quotes: LJ-1-728-SPLIT-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

(This worktree carries no `.venv`; the pinned venv is the main
checkout's, invoked by absolute path.)

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. The pane caliber is `-A64m -I0 -M4g`.
- I did not write in `src/`.
- I did not rewrite any predecessor term: the transcription is
  preserved byte-exactly at `runs/Ascribed728SSS.agda.txt`, and every
  predecessor declaration that survives into the staged composition
  is consumed from a checked interface, not restated.
- I did not inhabit `Completeness`, and I did not hypothesise
  `Convert`. I did not postulate: every unverified file's only hole
  is the floor's body hole, which is its design.
- I did not rerun the same code hoping for a different result: every
  heavy run after B8 was a NEW shape (section 1, items 3-6).
- I did not touch the watchdog, its lock, its log, or any other
  pane's processes. I started no more than one Agda process at a
  time.
- I did not write a `review-of-*.md`: this is a resource wall, and
  the brief forbids a review-of for one.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.
All new files are inside `agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/`:

- `Probe728SSS.agda.txt`, the split composition, staged (never
  typechecked; its floor is the wall)
- `lj-1.728-SPLIT-SPLIT-SPLIT-report.md`, this report
- `runs/Ascribed728SSS.agda.txt`, the preserved transcription
- `runs/Cure1File728SSS.agda.txt`, the single-file cure, staged
- `runs/CureFloor728SSS.agda.txt`, its floor (walled,
  `runs/curefloor-1.out`)
- `runs/Cure2Floor728SSS.agda.txt`, the split composition's floor
  (walled, `runs/cure2floor-1.out`)
- `runs/Load728SSS.agda.txt`, the interface load cell
  (`runs/load-1.out`, green)
- `runs/AmbOnly728SSS.agda.txt` (`runs/ambonly-1.out`, wall),
  `runs/Amb2Only728SSS.agda.txt` (`runs/amb2-1.out`, wall),
  `runs/AmbCompound728SSS.agda.txt` (`runs/ambcompound-1.out`, wall)
- `runs/Bisect8SSS.agda.txt`, header updated with the B8 verdict
- run records: `runs/bisect-8b.out`, `runs/curefloor-1.out`,
  `runs/frame-2.out`, `runs/hull-3.out`, `runs/cure2floor-1.out`,
  `runs/load-1.out`, `runs/ambonly-1.out`, `runs/amb2-1.out`,
  `runs/ambcompound-1.out`
- `runs/Frame728SSS.agda`, `runs/HullHalf728SSS.agda`: untouched
  sources; their `_build` interfaces refreshed by frame-2 and hull-3

## ARCHIVE USED

- archive/dev/DD-archived.md:33 - read. "NO MATHEMATICAL PROSE until
  both trophies land. The prose phase comes AFTER." This dispatch's
  deliverable is code and its comments plus this record; no
  mathematical prose was written.
- archive/dev/DD-archived.md:35 - read, and it is the route this
  verdict takes when it lands: "A NEGATIVE RETURN IS ADVERSARIALLY
  REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ
  TOGETHER", the questions being "is the refusal correct on its own
  numbers; is the measurement sound; did the BRIEF cause the outcome;
  and is there a cure the return missed". Section 3 is written so
  those four have what they need.
- archive/dev/ORCHESTRATION.md:87 - read, the trigger list this
  verdict is one of: "A refusal, a NO-GO, a RED gate, a stop taken as
  the" deliverable. A heap-wall NO-GO is the second form.
- archive/dev/ORCHESTRATION.md:93 - read, the reviewer's brief:
  "not a second attempt. Four questions: is the refusal correct on
  its own" numbers, and the rest as in DD25.
- archive/dev/PLAN-archived.md - declined: the construction registry
  as it stood on archival day; no row of it bears on a probe's run
  records.
- archive/dev/STATUS-archived.md - declined: the archived goal table
  of the retired internalization route; nothing in it is live for
  this task.
- archive/dev/TASKS-archived.md - declined: the archived L3.32-T
  task index; it predates LJ-1.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md - declined: a glossary
  provenance review; this dispatch names no new term.
- dev/literature/BIBLIOGRAPHY.md - declined: a source list for the
  retired rud route; no literature question is at stake in an
  elaboration-cost measurement.
- dev/literature/fine-structure.md - declined: fine-structure
  reading notes; the wall judged here is elaboration cost, and no
  mathematics of the probe is in question.
- dev/literature/primary-sources.md - declined: source fetch notes;
  not used.
- dev/literature/level-formula-slot-roles.md - declined: an
  exposition of level-formula slot roles; the bisect never reaches
  the probe's mathematics.
