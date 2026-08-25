# LJ-1.631: land ingredient (v) in L.Choice.Faithful

**VERDICT: GO.** The obligation `src/L/Choice/Faithful.lagda.md::class-pred-v` is
discharged. One row, no new import line, no `using` change, no probe import.
Exit 0 under `-A64m -I0 -M4g`.

## THE FLOOR, THEN THE ROW

Both runs at HEAVY caliber `GHCRTS="-A64m -I0 -M4g"`, single Agda process, warm
interface cache (the worktree cache from the prior campaign), same file, same
command `agda src/L/Choice/Faithful.lagda.md`. Logs:
`agents/tasks/LJ-1-631/runs/D10-floor.log` and
`agents/tasks/LJ-1-631/runs/row-landed.log`.

| run | wall | peak RSS |
|---|---|---|
| chapter UNCHANGED (the D-10 floor, W3) | 1.84 s | 411 631 616 B (392.7 MiB) |
| chapter WITH the row | 3.85 s | 596 410 368 B (568.8 MiB) |

Delta: 2.01 s and 184.8 MiB for five in-fence lines. The 4 GiB cap held with
86 percent to spare; there was no heap wall at any point, so no restructuring
was needed and none was attempted.

## DID THE DEPENDENT COUNT PREDICT IT

The cost tracked it. The host's dependent count is 2, verified today by
`grep -rl "import L.Choice.Faithful" src/` (src/Everything.lagda.md and
src/L/Choice/Order.lagda.md), the same class as `L.StageCardinal`, and the
landing peaked at 568.8 MiB, 13.8 percent of the 4 GiB cap, at 3.85 s warm,
against `L.StageCardinal`'s recorded 21.9 percent of a 2 GB cap and
`L.Constructible`'s (71 dependents) wall. The low-dependent host landed easily
again, so the dependent-count reading of the cost model holds on a second host.

## WHAT IS NOW IN SRC

- Path: `src/L/Choice/Faithful.lagda.md`.
- Name delivered: `class-pred-v`, the brief's proposal, kept. It is the name
  the family already uses: `class-pred-i` landed in `src/L/Constructible.lagda.md`
  under its family name, and `[LJ-1.625]`'s survey
  (agents/tasks/LJ-1-625/Probe625.agda:270) sites this ingredient as
  `class-pred`-family content at `L.Choice.Faithful`.
- The row, top-level of the chapter module, at the file's end (line 962):

      class-pred-v : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
      class-pred-v δ oδ = keyS (LsetS δ oδ)

- Line count: 8 lines added in total, 5 in-fence (2 code, 3 comment).
- No import line added or removed. No `using` list changed. Both factors were
  in the host's scope exactly as `[LJ-1.625]` measured: `keyS` at
  src/L/Choice/Faithful.lagda.md:65, `LsetS` at src/L/Axioms/Basic.lagda.md:160
  opened by the host's `L.Axioms.Basic` line, `Lset` and `IsOrd` from the host's
  `L.Constructible` line.

**Siting correction, one place.** The brief's shape (agents/tasks/LJ-1-600/
Probe600.agda:129-130) places the row at top level. The chapter's final
fence is inside `module Ordered` (src/L/Choice/Faithful.lagda.md:518), which
closes only at the end of the file. Placing the row in that fence would have
made it a member of `Ordered` and not an importable top-level term. The row
therefore lands in a NEW top-level agda fence appended after the final prose
block, column 0, where it closes `Ordered` by the indentation rule and sits
in the chapter module body. No prose was added or changed; the fence carries
its comments only.

**No probe import, on purpose.** Per the brief's reversal of R-42's usual
advice: `[LJ-1.622]` measured that importing a 14 s probe is what walled two
landings, and `[LJ-1.626]` landed a sibling row by re-stating it in the
chapter. This row is re-stated the same way: its body is the chapter's own
application of `keyS` to `LsetS`, written under the full type. It elaborates
only under the written type, as `[LJ-1.600]`'s W3 measured at its own probe
(agents/tasks/LJ-1-600/Probe600.agda:129), and the landing reproduces that
without importing anything from `agents/tasks/`.

**Ratio facts for the bar.** Five in-fence lines were added. Whole chapter:
3.85 s over 524 in-fence lines (counted the ledger's way) is 0.0073 s per
line, under the 0.0123 bar. Increment view: 2.01 s over the 5 added in-fence
lines is 0.402 s per line; both views are reported, and the increment is the
warm-cache price of re-checking this one chapter with one new top-level row.

**Not done, by the brief.** No `make check` in the landing run (the program
commits and gates). No other ingredient landed. Nothing postulated. Nothing
committed or pushed; the working tree holds exactly the 8-line change above
plus this report and the two run logs.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` not read, declined: a dispatch index is
  not evidence for a one-row naming landing.
- `archive/dev/JOURNAL-archived.md` not read, declined: the brief supplied its
  measured premises with `file:line`, and none of them point into the archive.
- `archive/dev/JOURNAL.md` not read, declined, same reason.
- `dev/ARCHIVE.md` not read, declined: no module retired in this task, so no
  archive row is owed.
- `archive/dev/DECISIONS-archived.md` not read, declined: no ruling conflict
  arose; the brief and the probes agree.

## LITERATURE USED

- `dev/literature/devlin-II5.md` not read, declined: no set-theoretic
  judgement is open in a naming landing.
- `dev/literature/truncation-and-selection.md` not read, declined: the row
  touches no truncation or selection content.
- `dev/literature/digest.md` not read, declined: no open mathematical question
  needs the digest.
- `dev/literature/terms-2026-08.md` not read, declined: no glossary term is
  introduced.
- `dev/literature/geology.md` not read, declined: no route-level decision was
  made.
