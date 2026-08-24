# LJ-1.626 report: confirm the landed row, re-measure the floor and the chapter at the heavy tier

Obligation delivered: `src/L/StageCardinal.lagda.md::least-at-site` —
the brief's proposed name, unchanged. The row in the tree is named
`least-at-site` (`src/L/StageCardinal.lagda.md:271`), and the tie probe
calls it `SC.least-at-site` (`agents/tasks/LJ-1-626/Probe626.agda:60`).
The obligation this brief carries is the brief's: ONE term into
`src/`, ingredient (ii) of `class-pred` as [LJ-1.613] proved it and
[LJ-1.625] sited it, at `src/L/StageCardinal.lagda.md`, as a
standalone row.

Status: COMPLETE. GO. No commit, no push. Written as a skeleton before
any Agda run (C-22) and filled as each run landed; no cell is a
placeholder.

## CASE FOUND: THE ROW WAS ALREADY PRESENT

The brief declared the case: "An earlier attempt under this same code
landed the row ... If the row `least-at-site` and the widened `using`
at line 36 are already present, do not redo the edit: confirm it,
re-run the floor and the chapter, and report the numbers at the new
tier." That is the case found, confirmed before any measurement:

- The row: `src/L/StageCardinal.lagda.md:266-274` (five comment
  lines, three signature lines, one body line).
- The one widened `using`: `IsLeast` in
  `src/L/StageCardinal.lagda.md:36`.
- `git diff --stat` at dispatch: 11 insertions, 1 deletion, in that
  one file; nothing else changed in `src/`.
- The file's sha256 at dispatch:
  `51df1c725a9d6ca3fcc082216f6bc471dc077106027dfc3798043a3c24b4877a`.
  It reads the same after the whole measurement sequence, so this
  dispatch made NO content edit. The floor run temporarily restores
  the HEAD version for the unchanged-chapter measurement and restores
  this byte-identical version afterwards.
- The earlier report of this task names the row `least-at` in several
  places. The tree disagrees: the landed name is `least-at-site`, and
  the earlier report's own probe uses `SC.least-at-site`
  (`agents/tasks/LJ-1-626/Probe626.agda:60`, green in its own
  `runs/probe626.out`). The queue's obligation name was
  `least-at-site`, so the delivered name and the obligation agree.

The park record of the earlier attempt is
`agents/tasks/LJ-1-626/runs/accept-1.out`: tier `wide`, caliber
`-A64m -I0 -M2g`, conjunct 1 FAILED,
`run src/Everything.lagda.md rc 251 seconds 20.35`,
`error class heap_wall`, obligations delta -1, changed files 9. The
park was the whole-tree conjunct at the WIDE cap, not the landing.
This dispatch runs at the pane's heavy-tier caliber
`-A64m -I0 -M4g` (set by the program; I did not set `GHCRTS`). One
Agda process at a time, every run under a wall-clock cap I set and
report.

## THE VERDICT

**GO.** The first term of this campaign is in the worktree, and this
dispatch confirms it at the tier the brief now declares. The row
`least-at-site` landed by the earlier attempt is present, byte-identical
before and after my measurement sequence, and the chapter
typechecks green with the row: `runs/heavy-2-with-row.out`, exit 0,
2.45 s, peak RSS 470,777,856 bytes, 11.0 percent of the 4 GB heavy
cap. No hole, no postulate, `--safe` on, no probe imported into
`src/`, no other ingredient landed, no file reordered. The tie probe
re-runs green at the new tier (`runs/heavy-4-probe626.out`, exit 0,
1.06 s, 320,372,736 bytes). The park reason is cleared by
measurement: the whole-tree run that walled under WIDE now completes
under the heavy cap (`runs/heavy-5-everything.out`, exit 0, 28.62 s,
peak RSS 2,602,418,176 bytes, 60.6 percent of the 4 GB cap).
`review-of-least-at-site.md` is NOT written because there is no stop
to state, following [LJ-1.625]'s precedent. `make check` was NOT run;
the individual gates were, and all are green (THE GATES).

## THE FLOOR, THEN THE ROW

The brief's D-10 and its W3, executed as the FIRST Agda run of this
dispatch, before any file state change of my own: the chapter
UNCHANGED (the HEAD version, which has no row), its own `.agdai`
deleted first so the chapter re-elaborates, the dependencies warm.
Then the chapter WITH the row, same caliber, same method. All five
runs below are fresh, from `runs/`, each ONE Agda process under the
pane's heavy-tier caliber `-A64m -I0 -M4g`, each under a wall cap I
set and each log records.

| run | condition | exit | seconds | peak RSS (bytes) | percent of 4,294,967,296 cap | log |
|---|---|---|---|---|---|---|
| heavy-1-floor | chapter UNCHANGED (HEAD, no row), module-cold, `Checking L.StageCardinal` in the log | 0 | 2.75 | 456,065,024 | 10.6 | `runs/heavy-1-floor.out` |
| heavy-2-with-row | chapter WITH the row, module-cold, `Checking L.StageCardinal` in the log | 0 | 2.45 | 470,777,856 | 11.0 | `runs/heavy-2-with-row.out` |
| heavy-3-warm | chapter WITH the row, warm interface load, zero `Checking` lines | 0 | 1.00 | 320,962,560 | 7.5 | `runs/heavy-3-warm.out` |
| heavy-4-probe626 | the tie probe, module-cold, `Checking LJ-1-626.Probe626` in the log | 0 | 1.06 | 320,372,736 | 7.5 | `runs/heavy-4-probe626.out` |
| heavy-5-everything | whole tree, `Checking Everything` in the log, all 102 master interfaces warm | 0 | 28.62 | 2,602,418,176 | 60.6 | `runs/heavy-5-everything.out` |

**The D-10 stop condition did not fire.** The floor reads 2.75 s /
456,065,024 bytes. The brief's alarm is [LJ-1.622]'s ~766 MB / 3 s
for a comparable frame (`agents/tasks/LJ-1-622/lj-1.622-report.md:114`
and `:130`). The worktree floor sits BELOW that alarm in both numbers
and is byte-identical in peak RSS to this worktree's own earlier
floor run under the wide tier (`runs/floor-reelab.out`: 2.74 s /
456,065,024 bytes). The wall is not in this worktree's `_build`.

**The row's own price.** Against the module-cold floor, the with-row
run reads 2.45 s / 470,777,856 bytes. The seconds are inside the
instrument's run-to-run spread (the earlier attempt's same pair read
2.74 s and 2.84 s, `runs/floor-reelab.out` and `runs/with-row.out`);
the peak RSS is 14,712,832 bytes higher, and that delta is
byte-identical across both attempts (both pairs read
456,065,024 → 470,777,856). No new normalisation shape entered:
the row is one line over a call the chapter already makes in `h`
(`src/L/StageCardinal.lagda.md:361`), and the delta measures that.
The warm interface load of the delivered state reads 1.00 s /
320,962,560 bytes, within the earlier attempt's warm load
(`runs/floor-load.out`: 1.37 s / 321,994,752 bytes).

## WHAT IS NOW IN SRC

- Path: `src/L/StageCardinal.lagda.md`
- The row's name: `least-at-site`, a standalone row at
  `src/L/StageCardinal.lagda.md:266-274`, placed after the `OrdSWO`
  module (the order it selects over,
  `src/L/StageCardinal.lagda.md:228-264`, `ordSWO` at `:258`) and
  before its consumer, the `LimitStep` module
  (`src/L/StageCardinal.lagda.md:287`). Nine in-fence lines: five
  comment lines, three signature lines, one body line.
- The one widened `using`: `IsLeast` joins the `L.WellOrder.Base`
  using list at `src/L/StageCardinal.lagda.md:36`. No import line
  was added anywhere; the file was not reordered; `git diff --stat`
  is 11 insertions, 1 deletion in that one file.
- In-fence lines of the master: 482 at HEAD, 491 with the row,
  counted the ledger's way (non-blank lines inside ```agda fences,
  `scripts/measure/ledger.py:94`).
- Nothing else changed in `src/`. `src/Everything.lagda.md` needed
  no line: no new module entered the book, so the reading catalog
  is untouched (`check-closure: clean (102 masters; closure,
  archive)`).

The row, as landed:

    least-at-site : (δ : S) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
                  → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
                  → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (OrdSWO.ordSWO δ oδ) P a
    least-at-site δ oδ = leastOf (OrdSWO.ordSWO δ oδ) lem

It is RE-STAATED, not imported. The body is six tokens of names the
chapter already has (`leastOf` and `lem` from its own telescope,
`OrdSWO.ordSWO` its own module), and the statement names three more
(`IsLeast` from a using list it already carries, `OrdSWO.ordSWO`,
and the `hProp`/`∥_∥₁` spellings the chapter's own rows already
write). The term it states is [LJ-1.613]'s `least-at-carrier`
(`agents/tasks/LJ-1-613/Probe613.agda:180-184`) and [LJ-1.625]'s
sited `least-at` (`agents/tasks/LJ-1-625/Probe625.agda:149-150`),
both with the body `leastOf (OrdSWO.ordSWO δ oδ) lem`. The chapter's
diff contains no import line. This is the one place where re-typing
beats importing, the opposite of the usual advice: the surveyed term
is shorter than the import graph that carries it, and [LJ-1.622]
measured that importing a 14 s probe module is what walled two
landings (`agents/tasks/LJ-1-528/Probe528.agda:99`).

## THE TIE, RE-RUN AT THE NEW TIER

`agents/tasks/LJ-1-626/Probe626.agda` imports the landed chapter
only, so both sides of its two rows are names of the live tree:

- `survey-spelling`
  (`agents/tasks/LJ-1-626/Probe626.agda:57-60`): the surveyed
  statement for (ii), at the chapter's own carrier `S`, is
  inhabited by the landed row. The landing IS the surveyed term.
- `landed-tie` (`agents/tasks/LJ-1-626/Probe626.agda:65-78`): the
  site's own `h` projection (`src/L/StageCardinal.lagda.md:361`)
  equals `fst (SC.least-at-site ...)` by `refl`, for arbitrary `D`,
  `inv` and `ih`. The projection shape is the one [LJ-1.613]
  measured green; its full-pair form walled there, so the
  projection is the load-bearing shape, not a convenience.

Re-run at the heavy tier: `runs/heavy-4-probe626.out`, exit 0,
1.06 s, 320,372,736 bytes, its module-cold. The earlier wide-tier
run of the same file read 1.13 s / 320,372,736 bytes
(`runs/probe626.out`): the probe is byte-stable across the tier
change. The probe is tracked evidence, not standing: the ledger
counts no line of it.

## THE WHOLE TREE AT THE NEW TIER

The park was the whole-tree conjunct at the WIDE cap
(`runs/accept-1.out`: `src/Everything.lagda.md`, rc 251, 20.35 s,
heap_wall). The brief's tier change is the route around it, and the
route needed a measured confirmation before this report claims GO.
I ran the same file at the heavy cap: `runs/heavy-5-everything.out`,
exit 0, 28.62 s, peak RSS 2,602,418,176 bytes. That peak is 60.6
percent of the 4 GB heavy cap, and it is 121 percent of the 2 GB
wide cap: the wide wall was real, the heavy route holds with 39
percent of headroom, and the single `Checking Everything` line in
the log shows the run re-elaborated only the aggregator over warm
master interfaces.

**A standing consequence for the queue:** every landing task in this
campaign carries this same whole-tree conjunct. Until the tree's
peak falls under the wide cap, every landing brief needs
`agda_tier: heavy`. That is a measurement, not a guess: 2.60 GB
measured this dispatch, 20.35 s to the wall measured at the park.

## THE RATIO

The bar is 0.0123 s per in-fence line of this task's write scope
(`dev/pod/table.toml:100` row `sys-dd24-ratio-bar`, `:113`). The
write scope's in-fence count is 491, the chapter's own (the report
carries no agda fence, the earlier report's convention; the ledger
scopes the count to `src/*.lagda.md`,
`scripts/measure/ledger.py:94`). The with-row run, the
module-cold/dependencies-warm measurement, is 2.45 s over 491 lines:
**0.0050 s per in-fence line, 0.41 times the bar.** The unchanged
chapter read 2.75 s over 482 lines, 0.0057, within the same spread.
The bar cannot fire on this return.

## THE GATES

`make check` was NOT run in this dispatch. It is the gate before a
commit, and the program commits, not this slot. The individual
checks were run from this worktree with the main tree's virtualenv
python (this worktree has no `.venv`; the earlier attempt set this
precedent):

- `scripts/gate/lint-agda.py --check`: exit 0 (the using-list
  change is legal)
- `scripts/gate/check-fences.py --check`: clean (102 masters, run
  threshold 3)
- `scripts/pod/check-closure.py --check closure`: clean (102
  masters; closure, archive)
- `scripts/gate/check-probes.py --check`: clean (7949 tracked
  files, no probe outside `agents/tasks/`, no generated file)
- `scripts/pod/check-spec-surface.py --check`: clean (8 surface
  files, 201 declarations, 499 in-fence lines over those 8 files;
  `StageCardinal` is not one of them, so the count reads the same
  before and after)
- `scripts/site/weave-i18n.py --check`: exit 0 (no prose touched)
- `scripts/gate/check-glossary.py --check`: exit 0 (no new term;
  `least-at-site` is a chapter-local name)
- `reuse lint`: 7761 / 7761 files compliant

## W2, ANSWERED

The rule: write the mathematics once at a generic carrier and
instantiate it, so both proofs share the maximum code. This landing
instantiates nothing: `least-at-site` is stated at the chapter's own
generic telescope (the module parameters `{ℓ}`, `lem`, `α₀`, `oα₀`,
`sq` are all abstract, and the row's `δ` and `oδ` are bound
variables), and its body applies the book's own generic `leastOf`
over the book's own generic `OrdSWO.ordSWO`. Both trophies share it
through the one line, exactly as they share `leastOf` itself. No
fixed form, no second copy. The deadline asked no fixed form of this
row, so there is no conflict to report.

## WHAT THE NEXT BRIEF NEEDS

The mechanics of a landing are now PROVEN and RE-PROVEN at the tier
the program actually runs: floor first (2.75 s / 456 MB
module-cold, 1.00 s / 321 MB warm), re-state rather than import,
one using token, the chapter re-elaborates at 2.45 s module-cold,
the tie probe closes at 1.06 s, the ratio holds at 0.41 times the
bar, and the whole tree completes at 28.62 s / 2.60 GB. Three facts
bind the next brief:

1. **Keep `agda_tier: heavy` on every landing brief until the
   tree's peak falls under the wide cap.** The whole-tree
   conjunct needs 2.60 GB measured; the wide cap is 2 GB. A wide
   landing brief parks itself at the acceptance, as this task's
   earlier attempt did.
2. **Name obligations from the tree, not from a report paragraph.**
   The earlier report of this task misnamed the row (`least-at`);
   the tree, the probe, and the queue's obligation all agree on
   `least-at-site`. A brief that copies a report cell instead of
   the `file:line` will carry a wrong name into the next task.
3. **The remaining landings from [LJ-1.625]'s survey, in its
   measured order** (`agents/tasks/LJ-1-625/lj-1.625-report.md:157`,
   "THE CHEAPEST ONE" and the two runs up it): (i) at
   `L.Constructible`, zero new edges but 71 transitive dependents
   invalidated — price the cone's interface load as the floor
   before the proof; (iv) at `L.BoundedSubset`, zero new edges,
   the body is a 50-line term, so expect its real price; (v) at
   `L.Choice.Faithful`, zero new edges plus one `using` widening,
   8 transitive dependents. Each should carry this task's floor
   discipline: if the host's re-elaboration floor reads far above
   its warm load, the wall is the worktree's `_build`, not the
   term.

What resisted, for the record: nothing resisted in this dispatch.
The work was a confirmation and a re-measurement, and every run
landed on the first try.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`, declined: not read. The
  landing precedent it indexes is already recorded in this task's
  own earlier run logs, and this dispatch makes no routing decision
  that needs a dispatch-history lookup.
- `archive/dev/JOURNAL-archived.md`, declined: not read. The
  campaign history it holds is not a premise of a confirmation.
- `archive/dev/JOURNAL.md`, declined: not read. Same reason.
- `archive/dev/DECISIONS-archived.md`, declined: not read. No
  decision cited by this brief lives there.
- `dev/ARCHIVE.md`, declined: not surveyed. No module retires in
  this task, so W4's register is not consulted.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`, declined: not read.
  The truncation behaviour of `leastOf` is settled in
  `L.WellOrder.Base` and only loaded, not adjudicated, by this
  dispatch.
- `dev/literature/devlin-II5.md`, declined: not read. The Devlin
  II.5 content lives in the chapters this task loads; no
  mathematical statement is settled by a confirmation.
- `dev/literature/terms-2026-08.md`, declined: not read. No term is
  coined here; every name is a chapter's own.
- `dev/literature/geology.md`, declined: not read. No layering or
  stratification question is open in this task.
- `dev/literature/digest.md`, declined: not read. No mathematical
  statement is settled by this dispatch.
