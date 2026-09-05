# LJ-1.737-SPLIT return: pair-in-Lγω at the name the meter reads

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation is inhabited at
`agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:154`, the file typechecks
at the pane caliber (`runs/green-1.out`, rc 0, 1.01 s, no warnings), and
`table-sat` stays absent as the brief demands.

## What the obligation is

The delivered term of `[LJ-1.737]` (`agents/tasks/LJ-1-737/Probe737.agda:115-117`),
transcribed into a fresh file at the top-level name the meter reads, with
`Underω`'s telescope as leading arguments:

    pair-in-Lγω :
        (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (clγ : closedω γ)
        (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩

Body: `pair-in-Lγω γ oγ hγ clγ = Underω.pair-in-Lγω γ oγ hγ clγ`, the
delivered term applied at the telescope. `table-sat` is NOT inhabited
(premise 4; the two tree debts of the 737 return are not this obligation).

## Shape kept, shape changed

- KEPT: the `Closer` legs (`no-succ`, `suc∈γ`) and the `Underω` module,
  verbatim transcription, because the delivered term stands on them.
  The file is 154 lines; the inlined breadth leg sits at
  `Probe737Split.agda:69` (`module Frameγ`).
- TRIMMED: `iter∈γ` and `block∈Lγ` are NOT transcribed. They served the
  `table-sat` route (finite-iterate absorption), which this obligation does
  not name; with them went the `sucIter` / `+ω-iter` / `boundCloses` /
  `Lset-mono` / `ω` imports (import-trim ruling).
- ADDED: the top-level definition, the obligation itself.
- **ONE DEVIATION, measured:** `Frame.pair-in-Lγ` is INLINED verbatim
  (module `Frameγ`, `Probe737Split.agda:47-77`) instead of imported from
  `LJ-1-724-SPLIT.Probe724Split`. The import drags the 698/693/520 probe
  chain into every check, and on 2026-08-29 05:24-05:41 the box's
  agda-watchdog killed every agda process within one sweep while system
  swap sat at 8758 MB (`/Users/alsg/Agentic/Bedrock/_build/tools/
  agda-watchdog.log`), so the cold chain could never land its interfaces
  (`runs/s1-floor-1.out` through `runs/warm-chain-2.out`: four kills,
  rc 1, RSS at death 707 MB, 11 to 19 s). `src/` chapters are hash-warm in
  `_build`, so the inlined leg checks in seconds. W2 note: the leg is now
  written twice in the tree; the canonical home stays the 724-SPLIT probe,
  and a later chapter-sized placement leg should absorb it. No deadline
  forced this form; the machine did.
- CITED LATER: `Probe737Split.agda:154` is the top-level pair placement
  later briefs may cite.

## What the next brief needs

- The machine finding, not the mathematics, is the transferable result:
  while `swapusage used >= 8192 MB`, ANY agda process on this box is
  SIGKILLed within one watchdog sweep (`vm.swapusage` read 8758.88 MB at
  05:43:26), so no task whose import chain holds a cold agent-probe
  interface can typecheck. Chain shape, not caliber, decides survival:
  `src/`-only chains stay under the window. Briefs built while the kill
  storm lasts should keep their probes' imports inside `src/`.
- This obligation has supply 1 at the meter's name and costs 1.01 s warm.
  Later briefs may cite `Probe737Split.agda:151` as the closedω pair
  placement instead of re-deriving it from the 737 probe's nested module.

## W3 answer

The brief's W3: whether the transcribed alias still converts in a fresh
file (estimated 40 to 120 lines). IT CONVERTS. The file is 154 lines with
the inlined breadth leg; the transcription proper (telescope prepend plus
body) needed three lines. No binder resisted: the nested `Underω` hid no
implicit, because module parameters are leading arguments under the hook
and the body's free names (`Frame.pair-in-Lγ`, `mem-ord`, `x²∈γ`) all
resolve at the module application.

## Runs (wide caliber, pane GHCRTS untouched, one Agda process per run,
/usr/bin/time -p, warm `_build` interfaces for the src/ chain)

- `runs/s1-floor-1.out`, `s1-floor-2.out`: the 724-SPLIT-importing first
  shape, killed at 13.0 s / 10.8 s, rc 1, mid-chain (698/520 cold).
  Signatures match the recorded cap walls (`LJ-1-541/runs/bisB.out`:
  "signal: Invalid argument", exit 1), but RSS at death (707 MB,
  `warm-chain-2.out`) clears both the 2 GB wide cap and the 6 GB
  watchdog backstop; the operative rule is the swap floor.
- `runs/warm-chain-1.out`, `warm-chain-2.out`: the same shape under a
  per-process `-M12g` warming override, killed at 19.2 s / 12.6 s. No
  price is reported from these runs (the override is not a caliber); they
  exist to classify the killer.
- `runs/floor-1.out`: floor, Sections 0-2 without the obligation block,
  rc 0, 1.02 s.
- `runs/green-1.out`: FULL file, rc 0, 1.01 s, no warnings. THE PRICE.
- `runs/green-2.out`, `green-3.out`: re-certifications of the restored
  full file after the floor measurement, rc 0 both.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-737-SPLIT
    check-survey-quotes: LJ-1-737-SPLIT clean (0 note(s), 0 defect(s))

    (The interpreter is the main tree's .venv; the worktree carries none.
    The script resolved the repo root from the worktree's scripts/pod and
    checked THIS worktree's brief and report.)

## ARCHIVE USED

- `archive/dev/DD-archived.md:30`: "**A return carries an ARCHIVE USED
  section** naming what it actually read and what it took from each item,
  at `file:line`." READ. This row is the mechanism this block runs under.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch and landing
  are the program's business; this return writes files and reports.
- `archive/dev/PLAN-archived.md`: declined, not read. The GO disposition
  follows the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing status
  is `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is the 737 probe and report, cited at
  `file:line` above.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  return adds no glossary term and cites none.
- `dev/literature/devlin-errata.md`: declined, not read. The task is a
  transcription of tree-internal code; no primary-text error class bears.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. That
  digest prices the level-hood formula's variable slots; this obligation
  states no formula.
- `dev/literature/primary-sources.md`: declined, not read. No fetched text
  backs any step of this return.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No source is cited
  beyond the tree's own files.
