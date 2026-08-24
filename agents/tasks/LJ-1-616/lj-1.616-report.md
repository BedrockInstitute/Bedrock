# [LJ-1.616] report: `CardAboveL`, landed at `src/L/CardinalAbove.lagda.md`

**DONE. Written as a skeleton, filled as runs land.**

## D-10: THE FILE WAS ALREADY ON DISK, AND I TOOK IT

`src/L/CardinalAbove.lagda.md` exists in this worktree at 586 lines. It is the
file `[LJ-1.555]` wrote (agents/tasks/LJ-1-555/lj-1.555-report.md:1).
I took all of it, unmodified. Verification against that report:

- Telescope: `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`, `src/L/CardinalAbove.lagda.md:18`,
  same as the probe's (`agents/tasks/LJ-1-528/Probe528.agda:15`). The
  predecessor's review cited that line at `:10`; in the file I have, it is at
  `:18`. One line of drift, same content.
- The obligation term `CardAboveL` is at `src/L/CardinalAbove.lagda.md:580-585`,
  byte-identical in type and body to
  `agents/tasks/LJ-1-528/Probe528.agda:638-643`.
- The one aggregator line `import L.CardinalAbove` is already in place at
  `src/Everything.lagda.md:397`, after `import L.StageBound`.
- Line count: 586 by `wc -l` here; the predecessor reported 587. The difference
  is one line of count, not of content; I cite my own measurement.

I did not write, edit or reformat any line of the master or of the aggregator.

## THE MODULE ALONE

W3, run FIRST, outside `make check`, under the pane's own caliber
`GHCRTS=-A64m -I0 -M4g` (heavy tier, set by the program; I did not set it).

**PROTOCOL.** Agda keeps this tree's interfaces in a mirror at
`_build/2.8.0/agda/` (verified: deleting
`_build/2.8.0/agda/src/L/CardinalAbove.agdai` forces a re-check, and agda
rewrites it there; touching the source alone does not, because freshness is
by content). I deleted that one interface and checked the master with its
dependencies warm. Exit 0, output `Checking L.CardinalAbove (...)` and then
clean. Log: `agents/tasks/LJ-1-616/runs/typecheck-module-alone.log`.

**PEAK RSS: 933,445,632 bytes (890.4 MiB). SECONDS: 4.68 real, 4.02 user.**
The cap for this tier is 4,294,967,296 bytes (4 GiB). The module uses
**one fifth of the cap** and has a four-to-one margin. It fits.

**THE FIRST MEASUREMENT IN THIS TASK WAS A NO-OP, AND I RECORD IT AS SUCH.**
The first `-l` run (3.11 s real, 765,231,104 bytes peak) found the interface
the program's witness had written at dispatch (mtime 12:44, pre-dating this
dispatch) fresh by content, printed nothing, and wrote no file. It measured
the cache, not the module. The valid number is the fresh one above.
[LJ-1.555]'s 3.727 s is a different caliber (-M8g, its pane) and a different
machine day; it is a comparable of shape, not of number.

**RATIO.** 4.68 s over the master's 494 non-blank in-fence lines (the count in
agents/tasks/LJ-1-555/lj-1.555-report.md, "WHAT THE LANDING COST") is 0.00947 s
per line, under the 0.0123 bar. My own raw fence count of the same file is 498
(0.00940 s per line); the difference is counting method, not content.

**WHAT I DID NOT MEASURE: THE MODULE COLD.** Deleting the whole interface
cache and rebuilding the dependency closure from scratch is the cold number.
Nothing in this task needs it: the module's own elaboration at 4.68 s and 890 MiB
is the quantity the caliber question asks about, and 555's cold whole-tree run
(28.312 s, 102 masters, its runs/make-check-before.log) already prices the
class of cold work at this tree.

## AND THEN make check

**RAN ONLY AFTER THE MODULE PASSED, PER THE BRIEF'S REVERSED ORDER.**

**ALL NON-AGDA TARGETS OF THE GATE ARE GREEN.** `make venv-check markers lint
lint-agda glossary ledger probes closure fences reuse ruleids specsurface`,
exit 0, 9.82 s real (log: `runs/make-check-non-agda-waiver.log`; an earlier
recording of the same set is `runs/make-check-non-agda.log`, exit 0, 9.95 s).
REUSE: 7680/7680 files compliant; spec-surface: 8 surface files, 499 in-fence
lines.

**THE TYPECHECK TARGET FIRST REFUSED ON THE MECHANICAL GUARD.** `make check`,
attempted 23:15 local, exited 2 in 0.05 s before any Agda: `omlxquiet` refused
because `omlx-server` (qwen's local inference server) is live (log:
`runs/make-check-owner-waiver-attempt.log`). Measured at the refusal the server
was under active service, 49.7% CPU, 15.6 GB RSS. It is not a heap wall and not
a defect of the landing: the module had already passed on its own, and the
refusal is the owner's own ruling of 2026-08-23 (whole-tree typecheck and
qwen's local inference never at the same time), refused on the daemon's
existence, so polling could not have cleared it either.

**THE OWNER WAIVED THE GUARD BY DIRECT INSTRUCTION AT 23:15 LOCAL.** This is a
one-off instruction binding this task; the guard in the Makefile stands for
the next run. The typecheck target was then run exactly as the Makefile recipe
runs it (lock touched, Agda, trap removing the lock on exit), with the owner's
waiver in force:

- **FIRST RUN, the measurement: exit 0, 16.65 s real, 15.73 s user, peak RSS
  2,479,276,032 bytes (2.31 GiB)** (verbatim transcript: log:
  `runs/make-check-typecheck-owner-waiver.log`). It re-checked `Everything` and
  `L.StageBound` and loaded the other 101 masters from their dispatch-time
  interfaces under `_build/2.8.0/agda/`. **The whole tree fits under the heavy
  tier's 4 GiB cap with 45% headroom.**
- **CONFIRM RUN: exit 0, 3.71 s real, peak 900,530,176 bytes** (log:
  `runs/make-check-typecheck-waiver-confirm.log`). A warm no-op; it is the
  steady-state floor, not the cost.

**ANSWER TO THE BRIEF'S QUESTION: THE WALL IS NOT THIS LANDING, AND IT IS NOT
THE WHOLE-TREE GATE EITHER.** The module alone costs 4.68 s / 890 MiB fresh;
the whole tree costs 16.65 s / 2.31 GiB warm-but-partial; both sit well under
the 4 g cap. What kept the tree gate from running was the owner's omlx guard,
an environment, and the owner resolved it by direct instruction.

**COMPOSITION, for the record, at waiver time:** venv-check + eleven non-Agda
targets, exit 0 (9.82 s); typecheck, exit 0 (16.65 s, 2.31 GiB). Together that
is `make check` with the one guard the owner waived. **A complete `make check` through the guard without the waiver was not run
after 23:15; the guard outcome is upstream of this task, and the campaign
should know it.**

**A CANDIDATE FOR THE NEXT BRIEF, MEASURED, NOT INFERRED:** the guard refuses
on the daemon's existence, and the daemon was observed alive at 0.1% CPU with
flat CPU time (9:03.97 to 9:04.03 over 20 s) while qwen's slot was idle.
`make check` is therefore blocked on a machine whose inference slot is done,
until somebody who owns the daemon stops it or the guard gains a measured
threshold. The guard's own comment names this as the open question
(`scripts/gate/check-omlx-quiet.py`, "an always-on idle daemon that this
refuses needlessly, that is a threshold to add LATER, from a measured
baseline"). I did not stop the daemon and I did not edit the guard: both are
outside this scope, and the second is guarded code.

## WHAT THE LANDING COST AND WHAT RESISTED

**WHAT IT COST (this dispatch, this caliber, all numbers in `runs/`):**

| Run | Wall | Peak RSS | Exit | Log |
|---|---|---|---|---|
| Module alone, fresh, deps warm | 4.68 s | 933,445,632 B (890 MiB) | 0 | `typecheck-module-alone.log` |
| Whole tree, waiver, Everything+StageBound re-checked | 16.65 s | 2,479,276,032 B (2.31 GiB) | 0 | `make-check-typecheck-owner-waiver.log` |
| Whole tree, warm no-op confirm | 3.71 s | 900,530,176 B (859 MiB) | 0 | `make-check-typecheck-waiver-confirm.log` |
| Gate, eleven non-Agda targets | 9.82 s | n/a (Python) | 0 | `make-check-non-agda-waiver.log` |

**WHAT RESISTED WAS NOT THE MATHEMATICS AND NOT THE MEMORY.** The term landed
unchanged; it uses a fifth of the module cap and the tree a little over half of
the tree cap. What resisted was, in order: the predecessor's scope defect
(which this scope repairs), the mechanical omlx guard (which the owner waived),
and one measurement of my own making, in that the first `-l` run measured the
cache and not the module, because Agda's freshness is by content and the
dispatch-time witness had already checked this master.

**FOR THE NEXT BRIEF, WHAT THIS CHANNEL OWES IT:**

1. The standing numbers under the heavy tier's `-A64m -I0 -M4g`: the module is
   4.68 s / 890 MiB fresh; the tree is 16.65 s / 2.31 GiB warm-partial. A
   future landing that adds a second leaf master can price itself against
   these without a 1800-second timeout.
2. The omlx guard blocks `make check` on the daemon's existence after qwen's
   slot is idle. See "AND THEN make check" above. This will hit the next
   `build`-kind dispatch the same way if the daemon outlives its session.
3. The `[LJ-1.555]` duplication remains: `CardAboveL` exists at
   `agents/tasks/LJ-1-528/Probe528.agda:638-643` and at
   `src/L/CardinalAbove.lagda.md:580-585`, and nothing keeps the two in
   agreement. Its cure (one line, `open import L.CardinalAbove`) was named by
   [LJ-1.555] and is outside this scope by AD12.
4. `cardAboveAnyOrd` is still free in the probe
   (`agents/tasks/LJ-1-528/Probe528.agda:669-678`), ten lines on top of what is
   now landed. AD12 gave this brief one obligation; I did not land it.

**NOTHING WAS WEAKENED. NOTHING WAS POSTULATED. NOTHING WAS COMMITTED OR
PUSHED.** The working tree is left exactly as this report describes it: the
master and the aggregator line as [LJ-1.555] wrote them, verified byte-for-byte
against the probe, plus this task's report, review and logs under
`agents/tasks/LJ-1-616/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ AND USED. `:170` is
  `| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |`.
  The comparable is the ambient Hartogs of `[LJ-1.94]` at 1058 lines and 27 s
  against the landed route's 494 in-fence lines and 4.68 s. Different calibers
  and different shapes (order types dropped, as [LJ-1.555] says), so nothing
  is funded against it. The chapter cites this line at
  `src/L/CardinalAbove.lagda.md:239-240`.
- `archive/dev/JOURNAL.md`: NOT READ, DECLINED. Closed history; live facts are in the task directories.
- `archive/dev/JOURNAL-archived.md`: NOT READ, DECLINED. Same reason, one layer older.
- `archive/dev/DECISIONS-archived.md`: NOT READ, DECLINED. Closed decisions; the rulings that bind this task live in `AGENTS.md` and the brief.
- `archive/dev/ORCHESTRATION.md`: NOT READ, DECLINED. Archived operating document, superseded by the program.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: NOT READ BY THIS TASK,
  DECLINED. [LJ-1.555] used it for the reason the landed statement keeps its
  `∥_∥₁` truncation (`src/L/CardinalAbove.lagda.md:585`); this task changed no
  statement, so the reason stands as recorded and re-reading it would add
  nothing measurable.
- `dev/literature/devlin-II5.md`: NOT READ, DECLINED. Devlin II.5 content lives in `L.StageCardinal`, the chapter this term cannot sit in.
- `dev/literature/digest.md`: NOT READ, DECLINED. No new mathematics was written here; this task verified and measured a landed term.
- `dev/literature/terms-2026-08.md`: NOT READ, DECLINED. No new term was named and no glossary entry was added.
- `dev/literature/geology.md`: NOT READ, DECLINED. Set-theoretic geology is not on this route.
