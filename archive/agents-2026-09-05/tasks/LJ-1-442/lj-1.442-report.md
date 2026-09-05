# LJ-1.442 report: land the truncated consumer in the tree

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. No heap event.

TARGET: land ONE term in a NEW master, `src/L/StageBound.lagda.md`:

    bounded-from-trunc :
        ∥ ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
             → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
                 ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)) ∥₁
      → ⟨ x ∈ˢ Lset κ ⟩

at the telescope `[LJ-1.434]` carries
(`agents/tasks/LJ-1-434/Probe434.agda:100-118`).

## D-10, BEFORE ANY AGDA

The premise file exists. Its VERDICT line is at
`agents/tasks/LJ-1-434/lj-1.434-report.md:52`:

    **GO.** The obligation typechecks (`agents/tasks/LJ-1-434/Probe434.agda:127-128`,

Neither of the two stop conditions held: the file exists, and the verdict is
`GO`.

The type it says it inhabited is at
`agents/tasks/LJ-1-434/lj-1.434-report.md:10-14`:

    bounded-from-trunc :
        ∥ ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
             → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
                 ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)) ∥₁
      → ⟨ x ∈ˢ Lset κ ⟩

That is the obligation type of this brief. No mismatch. No stop.

The body is one `PT.rec` of the chapter's own `theorem`, with the chapter's
own witness `snd (x ∈ˢ Lset κ)`
(`agents/tasks/LJ-1-434/lj-1.434-report.md:55-57`).

`[LJ-1.434]`'s MEASURED line count, which replaces the brief's estimate of
about 110 in-fence lines: non-blank non-comment lines in the probe are 76
(`agents/tasks/LJ-1-434/lj-1.434-report.md:193-195`). Distance is 6 of those
and is not landed here. Instantiation is 21. The truncated form is 24.
`SqFam` is 5.

`[LJ-1.434]`'s MEASURED median on three forced rechecks of the full probe
is 15.01 s (`agents/tasks/LJ-1-434/lj-1.434-report.md:184-186`). That is
the W3 estimate this report quotes at `file:line`.

## VERDICT

**GO.** The obligation typechecks at
`src/L/StageBound.lagda.md:100-101` (exit 0, median 15.29 s on three
forced rechecks of the master, dependencies warm, caliber
`-A64m -I0 -M8g`). The witness meter PASSes:
`src/L/StageBound.lagda.md::bounded-from-trunc`, exit 0, 3.61 s, 0
UNRESOLVED of 1, `probe_red=False`
(`agents/tasks/LJ-1-442/runs/witness-1.out`). The body is one `PT.rec` of
`Instantiation.Co.theorem`, with the chapter's own witness
`snd (x ∈ˢ Lset κ)`. `make check` is green after the landing.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in conflict.
The prose freeze (`AGENTS.md:69`) and the style checks did not conflict:
`lint-agda.py --check`, `weave-i18n.py --check` and `make check` all
exit 0 on a title, the code, and the comments inside the code, with no
narrative section.

## 1. What was built

- `src/L/StageBound.lagda.md`, module `L.StageBound {ℓ} (lem)`.
  79 in-fence non-blank lines, of which 71 are non-blank non-comment.
  `SqFam` (`:33-37`) is copied from
  `src/L/BoundedSubset.lagda.md:1388-1390`. `Instantiation` (`:42-66`)
  takes `sq : SqFam α` as data and applies `Devlin55.BoundedSubsetAt`
  then `BSA.Co`. `go` (`:89-96`) applies `Instantiation` then `Co`.
  `bounded-from-trunc` (`:100-101`) is one `PT.rec` of `go`.
- `src/Everything.lagda.md:394`, `import L.StageBound`, on the line
  after `import L.BoundedSubset` (`:393`).
- `dev/ledger.toml` `gch_wing` row for `src/L/StageBound.lagda.md`.

`Distance` is not in the chapter. `[LJ-1.443]` lands it.

The chapter's module telescope is the probe's: `{ℓ : Level}` then
`(lem : LEM (ℓ-suc ℓ))`. The inner anonymous modules keep the probe's
parameters unchanged (`Probe434.agda:100-118`).

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `κ`, `α`, `x` and `lam` stay parameters. No ordinal is
fixed. No band, no numeral, no site. Both halves of the truncated route
name `SqFam`. Instantiation is the untruncated reading. `bounded-from-trunc`
is the truncated reading. They share `SqFam` and they share
`Instantiation`.

## W3, THE WIDEST UNMEASURED TERM

It is `go` at `src/L/StageBound.lagda.md:89-96`, whose body applies
`Instantiation` then `Co`. Caliber `-A64m -I0 -M8g`, one Agda process
at a time, the `StageBound` interface removed before each run,
dependencies warm, from the repository root.

**STEP ONE, obligation omitted.** Three forced rechecks of the chapter
with `go` present and `bounded-from-trunc` absent. Each printed
`Checking`. Exit 0 every time.

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/w3-1.out` | 14.58 | 2365931520 |
| `runs/w3-2.out` | 14.58 | 2365947904 |
| `runs/w3-3.out` | 14.65 | 2365931520 |

Median wall **14.58 s**. Median peak RSS **2365931520** bytes.

**STEP TWO, obligation present.** Three forced rechecks of the chapter
with `bounded-from-trunc` added. Each printed `Checking`. Exit 0 every
time.

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/full-recheck-1.out` | 15.42 | 2370174976 |
| `runs/full-recheck-2.out` | 15.17 | 2370191360 |
| `runs/full-recheck-3.out` | 15.29 | 2370191360 |

Median wall **15.29 s**. Median peak RSS **2370191360** bytes.

The truncation itself costs 15.29 − 14.58 = **0.71 s**. That is not
zero against the recheck spreads (0.07 s on step one, 0.25 s on step
two). Heap movement is 4087808 bytes. No heap event.

The W3 estimate was 15.01 s at
`agents/tasks/LJ-1-434/lj-1.434-report.md:184-186`. The measured
median 15.29 s differs from that by a factor of 15.29/15.01 = 1.02,
not a factor of two. No finding on the estimate.

## THE RATIO

Measured seconds: **15.29** (median of three forced rechecks of the
landed master). In-fence line count: **79** (non-blank lines inside
the ` ```agda ` fence of `src/L/StageBound.lagda.md`; `Everything` is
uncounted by `accept.py:274-278`). Rate: 15.29 / 79 = **0.1935**
seconds per in-fence line. The bar is 0.0123. The rate is above the
bar.

This content belongs to class **P-m** (`dev/LESSONS.md:2512`):
instantiation content. The chapter applies `Devlin55.BoundedSubsetAt`
and `BSA.Co` at the consumer's carrier. The bar firing is the
certificate that class predicts, not a defect, and the chapter is
not padded.

## WHAT THIS DOES NOT MEASURE

Landing the CONSUMER measures nothing about the SUPPLY, and nothing
about the statement between them.

The untruncated module parameter of
`src/L/StageCardinal.lagda.md:17-20` is still untruncated:

    (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
        → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

This task does not change it.

It does not inhabit `Distance`.
It does not pay `levelIn` or `cover`. They stay module parameters,
copied from `module Co`.
It does not land `sq-trunc-closed`. That is `[LJ-1.440]`'s master.

## make check

This worktree had no `.venv`. The first `make check` stopped at
`venv-check` in 0.02 s. That log was overwritten. `make venv` installed
the pinned set from `requirements-dev.txt`. Then `make check` ran
under the pane's caliber, one Agda process. The saved
`runs/make-check-before.out` is that successful run.

- Before any write under `src/`: **13.24 s**, exit 0, peak RSS
  909934592 bytes. Everything was already cached; Agda printed no
  `Checking` line. `runs/make-check-before.out`.
- After the chapter lands: **12.42 s**, exit 0, peak RSS 924467200
  bytes. Agda printed `Checking Everything`. `StageBound` was warm
  from the three full rechecks, so the gate did not recheck it.
  `runs/make-check-after.out`. Closure moved from 99 masters to 100.
  `ledger.py --check` still reports standing 33,078 lines over 97
  masters, because it reads HEAD and the new master is uncommitted.

`scripts/measure/ledger.py --brief` at this working tree:

    standing 33,078 lines over 97 masters, measured from HEAD

That figure does not include `src/L/StageBound.lagda.md`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task lands a live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used. Retired-route
  journal. The consumer is the live `BoundedSubset` chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history of
  this task is this directory.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. Declined, not used.
  The live operating rules are `AGENTS.md` and the slot file.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined, not
  used. The live clauses that bind this slot are W2 and W4.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:92`. Quote:
  `HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.`
  Used: that is why one `PT.rec` into `⟨ x ∈ˢ Lset κ ⟩` is legal. Also
  read at `:227`. Quote: `(∏x ∥Y x∥) → ∥∏x Y x∥`. That is `Distance`,
  which this task does not land. Also read at `:230`. Quote:
  `that consumes `f` is not a proposition, AC does not help.** This is worth`
  The conclusion here IS a proposition, so the rec is the digest's free
  case.
- `dev/literature/devlin-II5.md`: read at `:1`. Quote:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. Declined, not
  used. This task copies a measured probe into a master, not II.5's prose.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not this consumer.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not land `Distance`.
- I did not write `review-of-bounded-from-trunc.md`. The verdict is GO.
- I did not pad the chapter to beat the ratio bar.
- I did not change `src/L/StageCardinal.lagda.md`.
