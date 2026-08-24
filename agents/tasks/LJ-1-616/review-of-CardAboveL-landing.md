# Review of the `CardAboveL` landing at `src/L/CardinalAbove.lagda.md`

**VERDICT: VERIFIED.** The file the brief names is the term the probe proved,
at the corrected path, unmodified since [LJ-1.555] wrote it.

## What this task did, in one paragraph

The obligation `src/L/CardinalAbove.lagda.md::CardAboveL` was already green in
the worktree when this dispatch started: [LJ-1.555] wrote the 586-line master
and the one aggregator line, its `make check` ran green on that tree
(agents/tasks/LJ-1-555/runs/make-check-final.log), and the program never
committed either path because its write scope named neither
(agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md, section 4). This
dispatch's scope names both, and this dispatch re-measured the landing under
the current heavy-tier caliber instead of trusting the predecessor's numbers.

## What was verified, line by line

- **The statement is the probe's statement.** `CardAboveL` at
  `src/L/CardinalAbove.lagda.md:580-585` is byte-identical in type and body to
  `agents/tasks/LJ-1-528/Probe528.agda:638-643`. Not weakened by one hypothesis:
  the telescope is `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`
  (`src/L/CardinalAbove.lagda.md:18`), the probe's own
  (`agents/tasks/LJ-1-528/Probe528.agda:15`).
- **No postulate, no choice, no hole.** `--safe` flag at
  `src/L/CardinalAbove.lagda.md:3`; the fresh check ran clean (see the report).
- **The import graph is the one [LJ-1.555] measured.** The master's imports are
  its lines 14-52; `L.BoundedSubset` sits above `L.StageCardinal`
  (`src/L/BoundedSubset.lagda.md:882`, instantiated at `:1397`), so the new
  leaf master is still the only cycle-free home, and the aggregator carries the
  one line `import L.CardinalAbove` (`src/Everything.lagda.md:397`).
- **The line-count drift is one.** 586 by `wc -l` here against the 587 the
  predecessor reported; the content is the content.

## What this task measured that the campaign did not have

Under the pane's own heavy-tier caliber `-A64m -I0 -M4g` (the predecessor
measured under `-M8g`): fresh elaboration of the master with dependencies warm
cost **4.68 s real and 933,445,632 bytes peak RSS** (890.4 MiB, one fifth of
the 4 GiB cap), exit 0. That is the number the next landing prices against.
See `agents/tasks/LJ-1-616/lj-1.616-report.md`, sections "THE MODULE ALONE"
and "AND THEN make check", with logs under `agents/tasks/LJ-1-616/runs/`.

## What is open when this file is read

Nothing mathematical. The `make check` typecheck ran green under the
owner's direct waiver of the omlx quiet guard (owner, 2026-08-24 23:15
local): exit 0, 16.65 s, peak RSS 2,479,276,032 bytes. The guard itself
stands in the Makefile and still refuses on the daemon's existence, which
is a standing condition for the next dispatch, not a condition on this
landing. The full record is in the report's "AND THEN make check".
