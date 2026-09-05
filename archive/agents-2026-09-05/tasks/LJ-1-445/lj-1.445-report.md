# LJ-1.445 report: land the truncated square law

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote in `src/L/SquareLawClosed.lagda.md`,
`src/Everything.lagda.md`, `dev/ledger.toml` and `agents/tasks/LJ-1-445/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term in a NEW master `src/L/SquareLawClosed.lagda.md`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

at a GENERIC band, under the module parameters `{ℓ} (lem) (α₀) (oα₀)` and
NOTHING else. Register the master in `src/Everything.lagda.md`.

## 0. D-10, before any Agda

**Predecessor report verdict**, `agents/tasks/LJ-1-437/lj-1.437-report.md:17`:

> **GO.** The obligation typechecks (`agents/tasks/LJ-1-437/Probe437.agda:345-348`,

The report is GO. It does not name the statement FALSE. I did not stop.

**Delivered type**, `agents/tasks/LJ-1-437/Probe437.agda:345-348`:

```agda
sq-trunc-closed :
    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → ∥ sq δ ∥₁
```

**The type this task lands is that type, character for character.** The brief
at `agents/tasks/LJ-1-445/LJ-1.445.md:11-13` writes the same four lines. I
did not name a difference. I did not stop.

The predecessor module parameters are `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))
(α₀ : V ℓ) (oα₀ : IsOrd α₀)` (`Probe437.agda:35-36`) and nothing else. That
is the telescope this master takes (`src/L/SquareLawClosed.lagda.md:19-20`).

`[LJ-1.440]` is not a mathematical result. I did not cite it as one.

## VERDICT

**GO.** The obligation typechecks at the delivered type
(`src/L/SquareLawClosed.lagda.md:325-328`, exit 0, median 2.01 s on three
forced rechecks) and it PASSes the program's witness meter
(`.venv/bin/python scripts/pod/witness.py --code LJ-1-445 --brief
agents/tasks/LJ-1-445/LJ-1.445.md`, exit 0, 1.71 s, 0 UNRESOLVED of 1,
`probe_red=False`). The master has no inner hypothesis module.

The term's telescope is `(δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁`
(`src/L/SquareLawClosed.lagda.md:325-327`), under the module parameters
`{ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀)`
(`src/L/SquareLawClosed.lagda.md:19-20`) and nothing else.

`make check` was green before the chapter landed (exit 0) and green after
(exit 0, `check-closure: clean (101 masters; closure, archive)`).

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict.

## 1. What was built

New master `src/L/SquareLawClosed.lagda.md`, module
`L.SquareLawClosed {ℓ} (lem) (α₀) (oα₀)` (`:19-20`). No inner hypothesis
module. No import under `agents/`. 280 non-blank in-fence lines. The
estimate was about 300.

The two `opaque` blocks are the probe's blocks, unchanged:

- `isL-ord` at `src/L/SquareLawClosed.lagda.md:50-52`
  (probe `Probe437.agda:67-69`)
- five projections `κL`, `κoL`, `κ∈sucL`, `κ-injL`, `κ-min-atL` at
  `:72-89` (probe `:90-107`)

`sq-trunc-closed` (`:325-328`) is `∈-induction` at motive `Goal` (`:271-272`).
The four cases of `step` (`:274-323`) are the four cases the probe already
closed. The descent case is still `PT.map2` (`:314-318`). The positive case
still spends `init-at-kappa` as data (`:165-174`) and then `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`). Nothing untruncates.

Registered in `src/Everything.lagda.md:387`, after `import L.Absorption`
(`:376`) and before `import L.StageCardinal` (`:388`).

Declared on the GCH wing in `dev/ledger.toml:3243`, so a later commit of
this master does not join the AC baseline by subtraction.

The shape did not resist. I did not weaken a type. I did not add a
hypothesis. I did not postulate.

## 2. W3: the seal in the master

**GO.** The widest unmeasured term was whether the five-projection seal
survives a master that imports `L.Cardinal` directly. The file written first
carried the two `opaque` blocks and omitted the band induction and
`sq-trunc-closed`. It imported `L.Cardinal` for `LeastCardInjL` and `_↪_`.

Three forced rechecks, master interface deleted, dependencies warm, caliber
`-A64m -I0 -M8g`, one Agda process. Each printed `Checking`. Exit 0 every
time. No heap event.

| run | wall s | peak RSS bytes | log |
|---|---|---|---|
| 1 | 1.60 | 390873088 | `runs/w3-1.out` / `w3-1.time` |
| 2 | 1.56 | 390856704 | `runs/w3-2.out` / `w3-2.time` |
| 3 | 1.63 | 390889472 | `runs/w3-3.out` / `w3-3.time` |

Median wall **1.60 s**. Median peak RSS **390873088 bytes**. Under the
estimate (under 3 s and under 500 MB). The probe's own W3 measured 1.72 s
and 425902080 bytes (`lj-1.437-report.md:136-137`) on a longer prefix that
ran through `init-at-kappa`. The master sits closer to `L.Cardinal` and the
seal still checks. It did not cost more. The elaborator did not refuse the
five-projection block.

## 3. The landed obligation

Full file, first check after the recursion landed: 2.13 s, peak RSS
460947456 bytes, exit 0, printed `Checking`. `runs/full-1.out`.

Full file, three forced rechecks, interface deleted, same caliber, one Agda
process:

| run | wall s | peak RSS bytes | log |
|---|---|---|---|
| 1 | 2.02 | 460980224 | `runs/full-recheck-1.out` / `full-recheck-1.time` |
| 2 | 2.01 | 460947456 | `runs/full-recheck-2.out` / `full-recheck-2.time` |
| 3 | 1.99 | 460996608 | `runs/full-recheck-3.out` / `full-recheck-3.time` |

Median wall **2.01 s**. Median peak RSS **460980224 bytes**. Exit 0 every
time. Each printed `Checking`.

The probe measured a median of 1.91 s (`lj-1.437-report.md:17-18`). The
master measured 2.01 s. The difference is 0.10 s. That is the measured cost
of sitting next to `L.Cardinal` and `L.Absorption` as a chapter, not as a
probe.

## WHAT THE MOVE COST

No rebuilt block was deleted. None of them has a supplier in `src/` that
this chapter may import.

| rebuilt name | why it stayed |
|---|---|
| `isL-ord` | no hit in `src/**/*.lagda.md` |
| `mem-incl` | no hit in `src/**/*.lagda.md` |
| `inf-member` | local to this proof |
| `comp-inj` | the same combinator lives in `src/L/BoundedSubset.lagda.md:1365` and inside `L.StageCardinal`. Both sit after this chapter in `src/Everything.lagda.md` (`:394` and `:388`). Importing either would reverse reading order. The seal does not mention it, but `clause4-at-kappa` and `kappa-limit` do, and those bodies sit next to the seal. |
| `κL` and the four siblings | the measured seal. Deleting it would open `fst (LeastCardInjL.κ a oa)` |
| `clause4-at-kappa`, `Shiftω`, `shift-at`, `kappa-limit`, `init-at-kappa`, `kappa-not-fin`, `kappa-decides`, `descent-core`, `band-ord`, `Goal`, `step` | the proof. Not in `src/` |

What the master takes straight from `src/`, where the probe already did:

- `sq`, `Init`, `via-col-square` from `L.Ordinal.SquareLaw`
- `module ShiftAbs` from `L.Absorption`
- `_↪_`, `module LeastCardInjL` from `L.Cardinal`
- `ω-limit`, `ω∉β`, `squareω`, `finite-excl-ω` from `L.InjChain`

The import list changed (module name, `using` lists, no probe header). The
mathematics did not.

## THE RATIO

Write-scope in-fence non-blank lines of the new master: **280**
(`src/L/SquareLawClosed.lagda.md`, ledger caliber: non-blank lines inside
` ```agda ` fences).

Median wall of the three forced rechecks: **2.01 s**.

Seconds per in-fence line: **2.01 / 280 = 0.00718**. The live bar is
0.0123. The return is under the bar.

The probe's 1.91 s over 349 raw lines was 0.0055 s per line. The master
counts comments inside the fence, so the divisor is not the same class as
the probe's raw line count. The number to price the next brief against is
**2.01 s over 280 in-fence lines**.

## W2 and DD4

The term is written once at a generic band. The module is
`L.SquareLawClosed {ℓ} (lem) (α₀) (oα₀)`. No numeral and no site is named
except `ω`, which the predecessor already put in the same places. There is
no fixed form to report.

W4 does not fire: no module was retired.

## Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The master interface was deleted before each timed run
(`_build/2.8.0/agda/src/L/SquareLawClosed.agdai`).

- `make check` BEFORE the chapter: exit 0. `ledger.py --check` printed
  standing 33,157 lines over 98 masters. `check-closure: clean (100
  masters)`. `.venv` was missing in this worktree; `make venv` built it
  from `requirements-dev.txt`. I added no unpinned dependency.
- W3 alone, three forced rechecks: 1.60 s, 1.56 s, 1.63 s. Median
  **1.60 s**. Median peak RSS **390873088 bytes**. Exit 0 every time.
- Full file, first check: 2.13 s, 460947456 bytes, exit 0.
- Full file, three forced rechecks: 2.02 s, 2.01 s, 1.99 s. Median
  **2.01 s**. Median peak RSS **460980224 bytes**. Exit 0 every time.
- Witness meter, the one obligation: PASS, exit 0, 1.71 s, 0 UNRESOLVED
  of 1, `probe_red=False`.
- `lint-agda.py --check src/L/SquareLawClosed.lagda.md`: exit 0.
- `make check` AFTER the chapter: exit 0. `check-closure: clean (101
  masters; closure, archive)`. `check-fences: clean (101 masters)`.
  `reuse lint` clean. Spec surface unchanged.
- No heap event.

## WHAT GO EARNS

**A GO puts this campaign's first term in `src/`.** The truncated square
law holds at every infinite band ordinal with an empty hypothesis
telescope, as a chapter. A later brief can cite
`src/L/SquareLawClosed.lagda.md:325-328` instead of a probe.

## WHAT THIS DOES NOT MEASURE

This task lands the SUPPLY of the truncated square law. It measures
nothing about the CONSUMER. The consumer's module parameter is the
untruncated Sigma today (`src/L/StageCardinal.lagda.md:17-19`):

```agda
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where
```

This task does not untruncate `κ-inj`. The injection stays truncated
(`src/L/Cardinal.lagda.md:132-133`). It does not prove
`⟨ ω ∈ˢ fst (κL a oa) ⟩`. That remains a hypothesis of `init-at-kappa`
(`src/L/SquareLawClosed.lagda.md:167-168`).

This task does not claim the trophy. It does not touch
`src/Landmarks.lagda.md`.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not import a file under `agents/`.
- I did not write `review-of-sq-trunc-closed.md`. The landing is GO.
- I did not add a consumer-match term. The consumer stays out of this
  measurement.
- I did not write a narrative section in the chapter. The master is a
  title, the code, and the comments inside the code.

## Working tree

- `src/L/SquareLawClosed.lagda.md` (new)
- `src/Everything.lagda.md` (`import L.SquareLawClosed` at `:387`)
- `dev/ledger.toml` (`gch_wing` row at `:3243`)
- `agents/tasks/LJ-1-445/lj-1.445-report.md`
- `agents/tasks/LJ-1-445/runs/` (W3 and full logs)

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: named, not used. Opened at the head
  (`archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18").
  This task lands a live LJ-1 probe into `src/`. It is not a row from the
  archived dispatch index.
- `archive/dev/JOURNAL.md`: named, not used. Opened at the head
  (`archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20"). The
  per-episode journal is retired. This task's record is the master and
  this report.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The bound that entry named is the law this master now supplies in
  truncated form, with an empty hypothesis telescope, in `src/`.
- `archive/dev/ORCHESTRATION.md`: named, not used. Opened at the head
  (`archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules").
  This task is a chapter landing. It does not consult the archived
  orchestrator rules.
- `archive/dev/PLAN-archived.md`: named, not used. Opened at the head
  (`archive/dev/PLAN-archived.md:1`, read: "# ARCHIVED 2026-08-20"). The
  construction registry is retired. The live producer is
  `dev/pod/queue.toml`.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**,". Read to resolve the injected archive
  paths. W4 does not fire: no module was retired.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  The landed term spends a truncated injection and a truncated square. It
  does not untruncate either.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that
  only needs cardinal arithmetic never needs an injection as". The four
  cases of `step` never take an injection as data.
- `dev/literature/terms-2026-08.md`: named, not used. Opened at the head
  (`dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling").
  No glossary work in this task.
- `dev/literature/devlin-II5.md`: named, not used. Opened at the head
  (`dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L").
  The landing copies a delivered probe. No step consults a condensation
  argument.
- `dev/literature/digest.md`: named, not used. Opened at the head
  (`dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature").
  This task is the L-band truncated law, not the rud-route architecture.
- `dev/literature/geology.md`: named, not used. Opened at the head
  (`dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions").
  Geology is not this landing.
