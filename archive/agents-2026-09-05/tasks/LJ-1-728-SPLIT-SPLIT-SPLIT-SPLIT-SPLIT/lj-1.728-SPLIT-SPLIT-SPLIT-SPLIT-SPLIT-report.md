# LJ-1.728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT report: conv0, the un-ascribed convert, named at top level

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/Probe728SSSSS.agda::conv0
verdict: **GO. `conv0` checks at `-M4g`.** The un-ascribed convert,
exported at top level, typechecks in this task's module:
`runs/probe-1.out:5,6,23` (11.76 s, peak RSS 1.88 GB, EXIT=0, warm
interfaces, the only `Checking` line the probe module itself,
`runs/probe-1.out:4`).  The floor ran first and priced the frame:
234.84 s, 2.56 GB, the one-time cold closure of this worktree's
probe chain inside that figure (`runs/floor-1.out:4-14,166,167`),
EXIT=42 from the by-construction unsolved metas of the holed body
only (`runs/floor-1.out:159-166`) and no Heap-exhausted line
anywhere.  The missing named export is supplied: `conv0` had supply
0 and now has a witness in the tree, named exactly as the brief's
obligation reads.  The ascribed shape was never retried (premise 3
held); no `review-of-*.md` is written, because a GO is not a NO-GO
statement and the brief orders that file only for the NO-GO
channel.

Written as a skeleton before anything ran (C-22), filled as each
fact landed.  No commit, no push.  Only this task directory is
touched.

## 0. THE ENVIRONMENT, MEASURED AT DISPATCH

Taken before the first Agda process started:

- `sysctl vm.swapusage`: total 2048.00M, used 1017.44M, free
  1030.56M.  The watchdog's swap-spiral line is 8192 MB
  (`/Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh:28`), so
  the margin at dispatch was about 7.2 GB.
- `kern.memorystatus_vm_pressure_level`: 1 (normal).
- No agda process running at dispatch (`ps ax -o pid=,rss=,comm=`
  and `pgrep -x agda`, both empty for agda).
- The watchdog runs as main-tree pid 1964, started 2026-08-31
  16:21:42 local (`ps ax -o pid,lstart,command`), and its log names
  no kill after that start
  (`/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`, last
  line).
- Pane caliber, read at dispatch: `GHCRTS=[-A64m -I0 -M4g]`, the
  HEAVY tier.  It was never set or changed by me; the runner only
  echoes it into each `.out` (`runs/run.sh:9`).
- Build state of this worktree, measured: `_build/2.8.0/agda/src`
  carries 305 `.agdai` and `_build/2.8.0/agda/agents` carries 381,
  but no interface exists for the probe chain
  (`find _build/2.8.0/agda -name 'Probe652*' -o -name 'Probe673*' -o
  -name 'Probe692*'` is empty), so the floor pays this worktree's
  one-time cold closure of the task-probe chain.
- This worktree has no `.venv` of its own (`ls -d .venv`: absent);
  the survey gate at the end runs under the main checkout's pinned
  interpreter, as in the predecessor dispatch.

## 1. THE TRANSCRIPTION

Source: `VendorB4.agda.txt`, this task directory, delivered by the
program.  Measured first: it is byte-identical to the SSS worktree's
green `Bisect4SSS.agda`
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/Bisect4SSS.agda`,
`diff` exit 0), the file behind B4's 12.51 s green run
(`agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-4.out:5,23`).
Target: `Probe728SSSSS.agda.txt` at write time; the delivered file
is `Probe728SSSSS.agda` (section 3, the green run's rename).
Measured with comments and blank lines stripped from both sides:
**exactly two non-comment lines differ** — the module line
(`VendorB4.agda.txt:18` to `Probe728SSSSS.agda:28`) and the added
top-level export `conv0 = Build.conv0`
(`Probe728SSSSS.agda:62`), the export the brief orders and the
vendor, a runs/ bisect file, did not carry; it follows
Probe692.agda:68's in-tree pattern.  The brief's three prohibitions
hold by construction: no codomain ascription (the body is
`conv0 = hull-convert-at-matrix`, type inferred,
`Probe728SSSSS.agda:58`), no spelled
`⟨ _ ∷ _ ∷ _ ∷ [] P652.⊨ₚ P667.matrix₃ ⟩` (no P667 import at all,
`Probe728SSSSS.agda:38-40`), no `Convert` hypothesis and no
`grounded-from-complete`.  The supplier is [LJ-1.692]'s constructed
`hull-convert-at-matrix`, opened from `P692.Spend`
(`Probe728SSSSS.agda:54-55`), never hypothesised; its own verdict
is GO (`agents/tasks/LJ-1-692/lj-1.692-report.md:9`).

Predecessor records cited in this report (the SSS and SSSS run
outputs and reports) live in untracked task directories of the
main checkout, so their `file:line` evidence is absolute:
`/Users/alsg/Agentic/Bedrock/agents/tasks/<task>/...`.  This
worktree carries none of them (`ls agents/tasks` lists no
`LJ-1-728-SPLIT*` entry); the byte-identity claim in this section
was measured across the two trees with one `diff`.

The file was delivered as `.agda.txt` until a run of it completed
a typecheck.  The green run renamed it: the delivered file is
`Probe728SSSSS.agda`, and the `.txt` is gone (one `mv`).

## 2. THE FLOOR

`runs/FLOOR728SSSSS.agda.txt`: the probe with the term's body holed
(`conv0 = ?` inside `Build`), the top-level export kept (the
FLOOR728SSSS pattern:
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT/runs/FLOOR728SSSS.agda.txt`).
The floor prices the frame: imports, the `P673.At` application, the
`P692.Spend` application and the `Build` scaffold, everything except
the W3 term.  Measured first, per the 2026-08-23 ruling.  Because
the holed bodies are unsolved metas, the floor reports them at the
END of its check; the elapsed time and peak heap before that error
are the frame's own cost.  Delivered as `.agda.txt`: by construction
it cannot complete a typecheck.  NO POSTULATE.  One Agda process,
caliber from the pane, never set here.

**MEASURED (runs/floor-1.out): 234.84 s real, peak RSS 2.56 GB
(2561327104 B), EXIT=42, no Heap-exhausted line**
(`runs/floor-1.out:166,167,184`).  The exit is the holed body's two
by-construction unsolved metas, at `FLOOR728SSSSS.agda:52.3-8` and
`:52.11-12`, reported only after the whole frame checked
(`runs/floor-1.out:159-166`).  The run paid this fresh worktree's
one-time cold closure of the probe chain
(`runs/floor-1.out:4-14`): FLOOR728SSSSS itself, Probe652, Probe641,
Probe673, Probe667, Probe667.runs.W3, Probe520, Probe692, Probe686,
Probe689, Probe680, and still fit `-M4g` with about 1.5 GB to
spare.  For scale: the SSSS predecessor's floor, same pattern with
the spelled codomain on top, was 246.48 s / 2.51 GB
(`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT/lj-1.728-SPLIT-SPLIT-SPLIT-SPLIT-report.md`,
section 2).

**The frame is not the defect.** The floor fits the cap, so the
probe run proceeded.  After the run the temp copy
`runs/FLOOR728SSSSS.agda` was removed; the delivered floor is
`runs/FLOOR728SSSSS.agda.txt`.

## 3. THE RUNS

### runs/floor-1.out (the floor, section 2)

started 2026-08-31T13:42:22Z, ended 2026-08-31T13:46:17Z, cap
1800 s, `GHCRTS=[-A64m -I0 -M4g]` (`runs/floor-1.out:1-3,184,185`).
EXIT=42, 234.84 s real, maximum resident set size 2561327104 B
(`runs/floor-1.out:166,167,184`).  Machine swap before the run:
used 1017.44 MB (section 0).  No watchdog kill was logged in the
window; the log's last line is still the 16:21:43 start line.

### runs/probe-1.out (THE W3 RUN)

started 2026-08-31T13:46:34Z, ended 2026-08-31T13:46:45Z, cap
1800 s, `GHCRTS=[-A64m -I0 -M4g]` (`runs/probe-1.out:1-3,23,24`).
**EXIT=0, 11.76 s real, maximum resident set size 1880752128 B**
(`runs/probe-1.out:5,6,23`).  The only `Checking` line names the
probe module itself (`runs/probe-1.out:4`): the interfaces the
floor left were reused, so 11.76 s is the probe module's own check,
cold-closure-free.  No other heavy process ran between the two
runs and no watchdog kill was logged in the window; the log's last
line is still the 16:21:43 start line.  After the run the
probe was renamed to `Probe728SSSSS.agda` (section 1): a file that
typechecks is named `.agda`, never `.txt`.

One Agda process at a time throughout: the floor run ended before
the probe run started (`pgrep -x agda` empty between them).

## 4. WHAT THE NEXT BRIEF NEEDS

**W3 is measured, and the answer is GO.** The un-ascribed convert,
exported at top level, checks at `-M4g` in this task's module.  The
brief's estimate, the B4 file plus one export, was right: B4 green
at 12.51 s in the SSS worktree
(`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-4.out:5,23`),
this file green at 11.76 s here (`runs/probe-1.out:5`), the export
itself free.

**`conv0` is on the meter.** The obligation name
`Probe728SSSSS.agda::conv0` now has a witness in the tree.  The
export is the already-metered pattern: Probe692.agda:68 is the same
qualified reference into a parameterised submodule, which
`scripts/pod/witness.py` reaches without discharging the module's
parameters, and the meter builds `witness = Target.<name>` for it
(`scripts/pod/witness.py:278`).  The meter's own reading at return
is the program's figure, not mine.

**What a later brief may now do.** Retry `grounded-from-complete`
through this named export (premise 5's split composition), reusing
the named interface and never Convert's body.  The ascribed shape's
four measured walls stand unchanged (B2, B8, conv-1, amb-1;
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT/lj-1.728-SPLIT-SPLIT-SPLIT-SPLIT-report.md`,
section 4 table); premise 3 held, nothing of that shape was retried
here.

**Prices, measured, for the next brief's estimates.** Probe module
warm: 11.76 s / 1.88 GB (`runs/probe-1.out:5,6`).  This worktree's
one-time probe-chain closure: inside the floor's 234.84 s / 2.56 GB
(`runs/floor-1.out:4-14,166,167`), paid once per worktree and now
paid here, so a later probe in THIS worktree starts warm.  Frame
alone, cold closure excluded: the SSSS floor's 246.48 s figure
bounds it from above and B4's 12.51 s from below.

**No heap wall, so the restructuring clause had nothing to
restructure.**  The clause's rerun prohibition was never tested:
both shapes ran once each, and the second run was a different file.

**Ratio bar, stated rather than discovered.** The write scope of
this task carries no ` ```agda ` fence: the probe is a raw `.agda`
(counts 0) and the report is prose.  A raw probe carries no fence
and the bar cannot fire on it; the divisor of this return is 0.

**DD4 / W2 answer.** The reuse rule's home names it: MAXIMUM REUSE
is the architecture's objective and the same rule as WRITE IT
GENERIC (`archive/dev/DD-archived.md:22`, quoted in ARCHIVE USED).
This dispatch wrote no mathematics: the probe is a byte-faithful
transcription of the vendor file, which is itself the SSS worktree's
green B4 probe, plus one export line (section 1).  The generic
carrier is [LJ-1.689]'s `hull-convert`, instantiated by [LJ-1.692]
and re-exported here; nothing was rewritten at a fixed form, so
there is no conflict to report and no price to re-state.

**What could not close.** Nothing named by the brief is open.
`grounded-from-complete` was never in this dispatch's scope and
stays with the later brief (premise 5).  Nothing landed in `src/`.

## SURVEY QUOTES CHECK

Ran before return, as ordered.  This worktree has no `.venv` of its
own (section 0); the pinned interpreter of the main checkout ran
the gate:

```text
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT
check-survey-quotes: LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT clean (0 note(s), 0 defect(s))
```

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - read, and it is the rule my
  return answers (DD4/W2, section 4): "MAXIMUM REUSE is the
  architecture's objective, and it is the same rule as WRITE IT
  GENERIC."
- archive/dev/ORCHESTRATION.md - declined: not read; archived
  orchestration notes, and every clause that binds this dispatch is
  in the brief and the slot file.
- archive/dev/PLAN-archived.md - declined: not read; an archived
  plan index, and this dispatch plans nothing.
- archive/dev/TASKS-archived.md - declined: not read; the archived
  task index predates LJ-1 and names no obligation of this
  campaign.
- archive/dev/STATUS-archived.md - declined: not read; archived
  status rows predate LJ-1 and bear on no probe run.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md - declined: not read; a
  glossary provenance review, and this dispatch coins no term.
- dev/literature/primary-sources.md - declined: not read; no
  primary-source question is at stake in a transcription-and-run.
- dev/literature/BIBLIOGRAPHY.md - declined: not read; a source
  list, and no literature question is at stake here.
- dev/literature/rudimentary-functions.md - declined: not read; the
  retired rud route's notes bear on no probe of this shape.
- dev/literature/devlin-errata.md - declined: not read; no Devlin
  text is judged in this dispatch.
