# LJ-1.453 report: state the truncated route's one open statement ONCE, in the tree

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term in `src/L/StageBound.lagda.md`:

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

with `SqCollect` stated in that same chapter, generic in `α`.

## 0. GATES, BEFORE ANY AGDA

`agents/tasks/LJ-1-442/lj-1.442-report.md:55`:

    **GO.** The obligation typechecks at

`src/L/StageBound.lagda.md` is in the tree (module header at `:10`).
Gate one PASSES.

`agents/tasks/LJ-1-445/lj-1.445-report.md:47`:

    **GO.** The obligation typechecks at the delivered type

`src/L/SquareLawClosed.lagda.md` is in the tree (module header at `:19-20`).
Gate two PASSES.

I did not read `[LJ-1.443]` or `[LJ-1.449]`. I did not take a type from either.

## D-10, BEFORE ANY AGDA

Supply type, in the tree today, `src/L/SquareLawClosed.lagda.md:325-327`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

Predecessor that delivered it, `agents/tasks/LJ-1-437/Probe437.agda:345-348`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

Consumer family, in the tree today, `src/L/StageBound.lagda.md:35-39`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

Predecessor that delivered it, `agents/tasks/LJ-1-434/Probe434.agda:44-48`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

The two spellings of the carrier and of membership:

- `S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
- `_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`src/V/Hierarchy.lagda.md:83`).
- `sq` is the Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).
- `StageBound` opens `hPropStructure 𝒮ᵥ` (`src/L/StageBound.lagda.md:30`).

Whether those two telescopes are the same type, definitionally, is W3.
The probe is the identity. The measured answer is below. I do not hide a
gap in a `subst`.

## VERDICT

**GO.** The obligation typechecks at
`src/L/StageBound.lagda.md:114-116` (exit 0, median 16.95 s on three
forced rechecks of the master, dependencies warm, caliber
`-A64m -I0 -M8g`). `SqCollect` is stated at
`src/L/StageBound.lagda.md:43-46`, generic in `α`, and is not inhabited.
The body is two applications: the hypothesis applied to
`SLC.sq-trunc-closed`, then `bounded-from-trunc` applied to that result.
No postulate. No `subst`. No `--safe` off.

`src/Everything.lagda.md:387` is `import L.SquareLawClosed`.
`src/Everything.lagda.md:395` is `import L.StageBound`.
The supply master is registered before this one. The import is legal.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in conflict.

## 1. What was built

- `src/L/StageBound.lagda.md`: added `open import L.Ordinal.SquareLaw`
  for `sq` (`:17`), `import L.SquareLawClosed` (`:18`), `SqCollect`
  (`:43-46`), and `bounded-modulo-collect` (`:114-116`). Instantiation
  of the supply is `module SLC = L.SquareLawClosed {ℓ} lem α ordα`
  (`:112`), inside the consumer telescope that already has `α` and
  `ordα`. Working-tree in-fence non-blank count is **90** (HEAD is 79).
  Added non-blank in-fence lines: 11. The estimate was about 25.
- `dev/ledger.toml` `gch_wing` row for `src/L/StageBound.lagda.md`,
  comment updated from 79 in-fence to 90.
- `agents/tasks/LJ-1-453/Probe453.agda`, W3 only. `src/` has no probe.
- `src/Everything.lagda.md` already imported `L.StageBound` at `:395`
  from `[LJ-1.442]`. I did not add a second import.

`SqCollect` is a module parameter of the obligation and nothing else.
I did not inhabit it.

## W2 (DD4)

`SqCollect` is written once, generic in `α`. No band, no numeral, no
site. The module stays generic in `ℓ`. `bounded-modulo-collect` lives
in the chapter's existing anonymous telescope and instantiates the
supply at that same `α`. Both proofs share `SqFam` and
`bounded-from-trunc`. There is no fixed form to report.

W4 does not fire: no module was retired.

## W3, THE WIDEST UNMEASURED TERM

`domains-meet` as the identity, in
`agents/tasks/LJ-1-453/Probe453.agda:39-42`. Obligation omitted from
the chapter. Body is `domains-meet z = z`. Caliber `-A64m -I0 -M8g`,
one Agda process at a time, from the repository root.

**GO. The identity typechecks.** Every run printed `Checking`. Exit 0
every time. No heap event. The two landed telescopes are the same type
definitionally. The join is free.

First check:

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/w3-1.out` | 1.42 | 348241920 |

Three forced rechecks:

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/w3-2.out` | 1.59 | 348258304 |
| `runs/w3-3.out` | 1.38 | 348258304 |
| `runs/w3-4.out` | 1.32 | 348241920 |

Median wall of the three rechecks **1.38 s**. Median peak RSS
**348258304** bytes. The W3 estimate was three lines and under one
second on top of the chapter's own cost. The probe is 43 lines and the
median is 1.38 s; that is the measured number, not the guess. It is
not a factor of two against one second, and it is not a chapter cost.
The probe does not import `L.StageBound`.

## WHAT THE JOIN COST

Nothing. The identity is the join. No repackaging. No `subst`. The
supply spelling `(δ : V ℓ)` with `∈` and the consumer spelling
`(δ : S)` with `∈ˢ` convert by the two record fields of `𝒮ᵥ` named
above. `sq-trunc-closed` applies to `SqCollect`'s hypothesis as a
function argument.

`Distance` in `agents/tasks/LJ-1-434/Probe434.agda:56-59` expands the
Sigma. `SqCollect` names `∥ sq δ ∥₁`. Those are the same payload
because `sq` is that Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).
The brief named `SqCollect` with `sq`, and that is the type I landed.

## THE LANDED OBLIGATION

Full file, first check after the join landed: 16.66 s, peak RSS
2246262784 bytes, exit 0, printed `Checking`. `runs/full-1.out`.

Full file, three forced rechecks, same caliber, one Agda process:

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/full-recheck-1.out` | 16.95 | 2236137472 |
| `runs/full-recheck-2.out` | 17.05 | 2003927040 |
| `runs/full-recheck-3.out` | 16.48 | 2289156096 |

Median wall **16.95 s**. Median peak RSS **2236137472** bytes. Exit 0
every time. Each printed `Checking`.

`[LJ-1.442]` measured a median of 15.29 s on the same master before
this join (`agents/tasks/LJ-1-442/lj-1.442-report.md:130`). The
difference is 16.95 − 15.29 = **1.66 s**. That is the measured cost of
importing `L.SquareLawClosed` and applying `SqCollect`. It is not
zero against the recheck spreads (0.57 s on this three, 0.25 s on
`[LJ-1.442]`'s three). No heap event.

## THE RATIO

Write-scope in-fence non-blank lines of the master: **90**
(`src/L/StageBound.lagda.md`, ledger caliber: non-blank lines inside
the ` ```agda ` fence). `Everything` is uncounted.

Median wall of the three forced rechecks: **16.95 s**.

Seconds per in-fence line: **16.95 / 90 = 0.1883**. The live bar is
0.0123. The rate is above the bar.

This task's accept record carries `"concurrency": 1`
(`agents/tasks/LJ-1-453/runs/accept-1.out`). Exclusive. The seconds
keys in the rule table are guarded by `concurrency == 1`
(`scripts/pod/table.py:575`).

The two predecessor numbers the brief names, with this record's
concurrency beside them:

- `[LJ-1.442]` recorded **0.19519**. This task's concurrency is **1**.
  The `[LJ-1.442]` report itself states 15.29 / 79 = 0.1935
  (`agents/tasks/LJ-1-442/lj-1.442-report.md:146`) and does not carry
  a concurrency field.
- `[LJ-1.445]` recorded **0.01243**. This task's concurrency is **1**.
  The `[LJ-1.445]` report itself states 2.01 / 280 = 0.00718
  (`agents/tasks/LJ-1-445/lj-1.445-report.md:174`) and does not carry
  a concurrency field.

This content belongs to class **P-m** (`dev/LESSONS.md:2512`): the
chapter still contains instantiation of `Devlin55.BoundedSubsetAt`.
The new lines are parameterized composition. The measured rate is of
the whole write-scope chapter, not of the eleven added lines. The bar
firing is the certificate that class predicts, not a defect, and the
chapter is not padded.

## WHAT IS LEFT

`[LJ-1.447]` and `[LJ-1.448]` state the same counting leg's residue as
a statement about two ordinals instead of a choice principle. This
task does not rank the two routes.

`SqCollect` is now one type in the tree for `[LJ-2.5]` to rule on.
It is not inhabited. A route to it is refuted at
`agents/tasks/LJ-1-408/Probe408.agda:95-104`. Nothing in this tree
refutes the type.

The untruncated module parameter of
`src/L/StageCardinal.lagda.md:17-20` is still untruncated. This task
does not change it.

## make check

- Before any write under `src/`: **16.35 s**, exit 0, peak RSS
  910065664 bytes. Agda printed `Checking Everything` and
  `Checking L.SquareLawClosed`. `StageBound` was the `[LJ-1.442]`
  master, cached. `runs/make-check-before.out`.
- After the chapter lands: **26.17 s**, exit 0, peak RSS
  2054619136 bytes. Agda printed `Checking L.StageBound` then
  `Checking Everything`. `runs/make-check-after.out`. Closure is
  still 101 masters. `lint-agda.py --check src/L/StageBound.lagda.md`
  exits 0.

`scripts/measure/ledger.py --brief` at this working tree:

    standing 33,437 lines over 99 masters, measured from HEAD

That figure does not include the uncommitted eleven lines.

## WHAT GO EARNS

**A GO gives `[LJ-2.5]` one type to rule on.** The bounded-subset
lemma's conclusion follows from `SqCollect` alone, with the supply
half already proved unconditionally at
`src/L/SquareLawClosed.lagda.md:325-328`.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not inhabit `SqCollect`. I did not postulate it.
- I did not claim `SqCollect` is false.
- I did not write `review-of-bounded-modulo-collect.md`. The verdict
  is GO.
- I did not pad the chapter to beat the ratio bar.
- I did not change `src/L/StageCardinal.lagda.md`.
- I did not rank the truncated route against the two-ordinal route.
- I did not write a narrative section in the chapter. The master is a
  title, the code, and the comments inside the code.

## Working tree

- `src/L/StageBound.lagda.md` (`SqCollect` at `:43-46`,
  `bounded-modulo-collect` at `:114-116`)
- `dev/ledger.toml` (`gch_wing` row comment, 90 in-fence)
- `agents/tasks/LJ-1-453/Probe453.agda`
- `agents/tasks/LJ-1-453/lj-1.453-report.md`
- `agents/tasks/LJ-1-453/runs/` (W3, full, make-check logs)

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task lands a type in a live
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. Declined, not
  used. The live operating rules are `AGENTS.md` and the slot file.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bind this slot are W2 and W4.
- `archive/dev/DECISIONS-archived.md`: read at `:1`. Quote:
  `# Archived decisions: the D series`. Declined, not used. The live
  decision list is not this landing's input.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:158`. Quote:
  `A type X has a constant endomap if and only if it has split`.
  Used: that is the Kraus criterion the brief names as premise 9.
  `SqCollect` is the collection type, not an endomap, and this task
  does not pay the endomap.
- `dev/literature/devlin-II5.md`: read at `:1`. Quote:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. Declined,
  not used. This task composes two landed terms. It does not consult
  II.5's prose.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not this join.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
