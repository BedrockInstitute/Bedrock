# LJ-1.459 report: land the counting leg's implication, and state its residue as a type

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term in `src/L/StageBound.lagda.md`:

    bounded-from-data :
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)
      → ⟨ x ∈ˢ Lset κ ⟩

in the module that already carries `bounded-from-trunc`, and state `Residue`
in that same chapter as a type beside `SqCollect`. The body is the identity
adapter, then `∣_∣₁`, then the chapter's own `bounded-from-trunc`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 5.

## PREDECESSOR VERDICT, BEFORE ANY AGDA

`agents/tasks/LJ-1-456/lj-1.456-report.md:89`:

    **GO.** `bounded-from-residue` typechecks

The brief cites `:89`. The report is GO. It does not name the statement
FALSE. I did not stop. I did not inhabit a FALSE type.

Delivered adapter, `agents/tasks/LJ-1-456/Probe456.agda:55-58`:

    adapter :
        ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
      → SqFam α
    adapter f = f

The brief forbids landing `bounded-from-residue` as 456 stated it.
`Probe456.agda:102` is `bounded-from-residue _ = ...`. The `Residue`
parameter is unused. I land the implication that has content, and I
state `Residue` separately as a type.

## D-10, BEFORE ANY AGDA

Side by side.

`SqFam` at `src/L/StageBound.lagda.md:36-40` (was `:35-39` before this landing):

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

`[LJ-1.456]` adapter domain, `agents/tasks/LJ-1-456/Probe456.agda:56-58`:

    ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
  → SqFam α
    adapter f = f

Obligation hypothesis, as the brief names it:

    ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)

Conversion facts, already in the tree:

- `S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
- `_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`src/V/Hierarchy.lagda.md:83`).
- `sq` is that Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).
- `StageBound` opens `hPropStructure 𝒮ᵥ` (`src/L/StageBound.lagda.md:30`).

**The obligation's hypothesis IS `SqFam α` after the identity adapter.**
The adapter is the identity (`Probe456.agda:58`). The obligation writes
the adapter's domain with the chapter's `S` and `∈ˢ`. Those convert to
`V ℓ` and `∈`. `sq δ` converts to the Sigma that `SqFam` writes out.
No `subst`. No corrected target. Original target stands on paper. W3
measured whether the chapter's own telescope admits the wrap
`bounded-from-trunc ∣ f ∣₁` with no new module. It does.

## VERDICT

**GO.** `bounded-from-data` typechecks at
`src/L/StageBound.lagda.md:136-139` (exit 0, median 14.02 s on three
forced rechecks of the master, dependencies warm, caliber
`-A64m -I0 -M8g`). `Residue` is stated at
`src/L/StageBound.lagda.md:52-60`, generic in the ordinal `y` and in
the three maps the 447 Pi names, and is not inhabited. The body is
the identity adapter, then `inside`, and `inside` is `∣_∣₁` then
`bounded-from-trunc`. No postulate. No `subst`. No `--safe` off.

W3 GO: the chapter telescope carries `inside` with no new module
(`src/L/StageBound.lagda.md:128-129`). `[LJ-1.456]`'s probe telescope
is the chapter's.

A GO puts both routes' residues in one chapter, which is what
`[LJ-2.5]` must rule on. The conclusion holds under the DATA family,
and that family is what `[LJ-1.452]` inhabits under `Residue`.
Nothing in this tree proves `Residue`. This task does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not
claim a trophy.

I did not write `review-of-bounded-from-data.md`. The verdict is GO.

## 1. What was built

- `src/L/StageBound.lagda.md`: added `isL` and `𝒮ʟ` to the Constructible
  import (`:14`), `open hPropStructure 𝒮ʟ` as `Sʟ` (`:31`), `Residue`
  (`:52-60`), `∣_∣₁` on the PT using line (`:23`), `inside` (`:128-129`),
  `adapter` (`:131-134`), and `bounded-from-data` (`:136-139`). Working-tree
  in-fence non-blank count is **114** (HEAD is 90). Added non-blank
  in-fence lines: 24. The estimate was about 20.
- `dev/ledger.toml` `gch_wing` row for `src/L/StageBound.lagda.md`,
  comment updated from 90 in-fence to 114.
- `agents/tasks/LJ-1-459/lj-1.459-report.md` and `runs/`. W3 ran in the
  chapter, as the brief ordered. No probe file. `src/` has no probe.

`Residue` is a type. I did not inhabit it.

## 2. W3: `inside`, first

**GO.** The chapter telescope admits the wrap with no new module.
Evidence: `src/L/StageBound.lagda.md:128-129`.

    inside : SqFam α → ⟨ x ∈ˢ Lset κ ⟩
    inside f = bounded-from-trunc ∣ f ∣₁

`bounded-from-data` and `Residue` were omitted for this measurement.
No extra module application. `[LJ-1.456]` rebuilt the telescope in a
probe. The chapter does not.

Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda process.
The StageBound interface was deleted before every kept run
(`_build/2.8.0/agda/src/L/StageBound.agdai`). Dependencies warm.
Every run printed `Checking`. Exit 0 every time. No heap event.

First landing, obligation omitted: 13.91 s, peak RSS 2113273856 bytes,
exit 0. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 13.85 | 2113257472 |
| `runs/w3-3.out` / `w3-3.time` | 13.98 | 2113273856 |
| `runs/w3-4.out` / `w3-4.time` | 13.97 | 2113290240 |

Median wall **13.97 s**. Median peak RSS **2113273856** bytes.

The W3 estimate was three lines and under 20 seconds on top of the
chapter. Measured, it is four in-fence lines (`inside` plus its two
comment lines) and 13.97 s for the whole chapter, not a delta on top
of a separate import. Nothing is funded against the estimate. The
obligation is not outranked.

P-l did not fire: the type names `SqFam α`. It does not name a
transparent `sucV`-chain.

## 3. The obligation

`bounded-from-data` (`:136-139`) is three steps:

| step | supplier | file:line |
|---|---|---|
| adapter | identity, from 456 | `:134`, spent at `:139` |
| `inside` | W3, `∣_∣₁` then `bounded-from-trunc` | `:129`, spent at `:139` |
| consumer | landed `bounded-from-trunc` | `:123-124`, spent at `:129` |

Nothing was weakened in the implication. Nothing failed to close. I
did not inhabit `Residue`. I did not postulate it. I did not rebuild
`κL` or `κC`. I did not rebuild the band induction. I did not land
`bounded-from-residue` as 456 stated it.

**The shape that resisted.** Restating `Residue` at the delivered
type names `κL`, `κC` and `isL-ord` (`Probe447.agda:208-210`). `κC`
has no home in `src/` (search of `src/` for `κC` is empty).
`SquareLawClosed` carries sealed `isL-ord` and `κL` but is
parameterized by a stage, and `Residue` must not depend on a dummy
stage. I did not rebuild either seal. I stated `Residue` as a type
of those three maps (`:52-60`). The body is the 447 Pi, with `S` for
`V ℓ` because `S` of `𝒮ᵥ` is `V ℓ`. The maps are parameters of the
type, not chapter parameters, and not postulated. If a later brief
wants a closed `Residue : Type _` with the names absent, it must
land `κC` first or give a type that does not mention them.

## 4. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| `Residue` (`:52-60`) | `Probe447.agda:208-210`, as a type of the three maps | not inhabited. Stated. Not an argument of `bounded-from-data`. |
| `levelIn` (`:107`) | `src/L/StageBound.lagda.md:107` | yes, already a parameter of `bounded-from-trunc` |
| `cover` (`:108-109`) | `src/L/StageBound.lagda.md:108-109` | yes, already a parameter of `bounded-from-trunc` |
| the DATA family | the obligation's hypothesis, which IS `SqFam α` after `adapter` | yes, at `:139` through `adapter` then `inside` |

Rebuilt, not hypothesized: nothing. Local `UK`, `HS` and `SLC` were
already in the chapter. I did not import a probe.

## 5. W2 and DD4

Everything is written once at a generic carrier. The chapter stays
generic in `ℓ`. `inside`, `adapter` and `bounded-from-data` live in
the existing anonymous telescope and are generic in `κ`, `α`, `x`
and `lam`. `Residue` is generic in the ordinal `y` and in the three
maps the 447 Pi names. No cardinal, no numeral and no site is named
except `ω`, which is where the obligation's own statement puts it.
There is no fixed form to report.

W4 does not fire: no module was retired.

## 6. Runs, floor

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **13.97 s**, median peak RSS
  **2113273856 bytes**, exit 0. Section 2.
- Full file, first check after the obligation landed: 14.04 s, exit 0,
  peak RSS 2104885248 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (StageBound interface deleted
  before each run, dependencies warm): 14.00 s, 14.06 s, 14.02 s.
  Peak RSS 2104885248, 2104901632, 2104901632 bytes. Median wall
  **14.02 s**. Median peak RSS **2104901632 bytes**. Exit 0 every
  time. Each printed `Checking`. `runs/full-recheck-{1,2,3}.out`.
- `lint-agda.py --check src/L/StageBound.lagda.md`: exit 0.
- No heap event.

The jump from W3's 13.97 s to 14.02 s is the obligation and
`Residue`. It is inside the recheck spread. The next brief prices a
follow-on against 14.02 s, not against an estimate.

## WHAT THE CHAPTER NOW OWES

The bounded-subset conclusion `⟨ x ∈ˢ Lset κ ⟩` still rests on these
hypotheses after this landing:

1. `Residue`, at `src/L/StageBound.lagda.md:52-60`:

       Residue :
           (isL-ord : (y : S) → IsOrd y → ⟨ isL y ⟩)
           (κL : (a : Sʟ) (oa : IsOrd (fst a)) → Sʟ)
           (κC : (a : Sʟ) (oa : IsOrd (fst a)) → Sʟ)
         → Type (ℓ-suc ℓ)
       Residue isL-ord κL κC =
           (y : S) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
         → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
         → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

   Stated. Not inhabited. `[LJ-1.452]` spends it inside
   `sq-data-closed`. This term does not.

2. `levelIn`, at `src/L/StageBound.lagda.md:107`:

       (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩

3. `cover`, at `src/L/StageBound.lagda.md:108-109`:

       (y : S) → ⟨ y ∈ˢ HS.M ⟩
     → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

**The condensation pair is unpaid. This task does not touch it.**
`levelIn` and `cover` are that pair. They were already parameters of
`bounded-from-trunc`. They stay parameters of `bounded-from-data`
because that term lives in the same module.

`SqCollect` (`:44-47`) remains the truncated route's unpaid type. I
do not rank the two routes. That ranking is `[LJ-2.5]`'s.

## THE RATIO

Write-scope in-fence non-blank lines of the master: **114**
(`src/L/StageBound.lagda.md`, ledger caliber: non-blank lines inside
the ` ```agda ` fence). `Everything` is uncounted.

Median wall of the three forced rechecks: **14.02 s**.

Seconds per in-fence line: **14.02 / 114 = 0.1230**. The live bar is
0.0123. The rate is above the bar. I did not pad.

`[LJ-1.453]` measured two rates, both above 0.0123, with concurrency
**1**:

- Accept record: 3.55 s over 90 in-fence lines = **0.0394**.
  `concurrency` is **1** at the LJ-1.453 record
  (`/Users/alsg/Agentic/Bedrock/.pod-state/state.json:5741`),
  `facts.lines` 90 (`:5781`), `facts.seconds` 3.55 (`:5784`).
- Own three rechecks: **16.95 / 90 = 0.1883**
  (`agents/tasks/LJ-1-453/lj-1.453-report.md:196`).

This task's chapter rechecks are the 14.02 s figure above, not an
accept-record seconds key. Exclusive. The seconds keys in the rule
table are guarded by `concurrency == 1`
(`scripts/pod/table.py:575`).

This content belongs to class **P-m** (`dev/LESSONS.md:2512`): the
chapter still contains instantiation of `Devlin55.BoundedSubsetAt`.
The new lines are parameterized composition. The measured rate is of
the whole write-scope chapter, not of the twenty-four added lines.
The bar firing is the certificate that class predicts, not a defect,
and the chapter is not padded.

## make check

- Before any write under `src/`: **12.11 s**, exit 0, peak RSS
  951713792 bytes. Agda printed `Checking Everything`. `StageBound`
  was cached. `runs/make-check-before.out`.
- After the chapter lands: **22.36 s**, exit 0, peak RSS
  2024210432 bytes. Agda printed `Checking L.StageBound`. Closure is
  still 101 masters. `lint-agda.py --check src/L/StageBound.lagda.md`
  exits 0. `runs/make-check-after.out`.

`scripts/measure/ledger.py --brief` at this working tree:

    standing 33,448 lines over 99 masters, measured from HEAD

That figure does not include the uncommitted twenty-four lines.

## WHAT GO EARNS

**A GO puts both routes' residues in one chapter**, which is what
`[LJ-2.5]` must rule on. The truncated residue is `SqCollect`
(`:44-47`). The DATA residue is `Residue` (`:52-60`). The
bounded-subset conclusion follows from the DATA family by
`bounded-from-data`, once `[LJ-1.452]` is taken as the supply half
under `Residue`.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not land `bounded-from-residue` as 456 stated it.
- I did not inhabit `Residue`. I did not postulate it.
- I did not rebuild `[LJ-1.452]`'s recursion. I did not rebuild either
  seal.
- I did not write `review-of-bounded-from-data.md`. The verdict is GO.
- I did not rank the DATA route against the truncated route.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.
- I did not pad the chapter to beat the ratio bar.
- I did not write a narrative section in the chapter. The master is a
  title, the code, and the comments inside the code.

## Working tree

- `src/L/StageBound.lagda.md` (`Residue` at `:52-60`,
  `bounded-from-data` at `:136-139`, `inside` at `:128-129`,
  `adapter` at `:131-134`)
- `dev/ledger.toml` (`gch_wing` row comment, 114 in-fence)
- `agents/tasks/LJ-1-459/lj-1.459-report.md`
- `agents/tasks/LJ-1-459/runs/` (W3, full, make-check logs)

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This landing does
  not consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task lands a type in a live chapter. It does not
  consult the retired-route journal.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry".
  Declined. This task does not retire a module. W4 does not fire.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18".
  Declined. This task does not change a DD row. The live clauses that
  bind this slot are W2 and W4.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used to keep the two routes distinct: a cardinal inequality is a
  truncated injection, and `bounded-from-trunc` takes `∥ SqFam α ∥₁`.
  The DATA family is truncated with `∣_∣₁`. That wrapper is the
  consumer's, not a new supply.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that only needs cardinal arithmetic never needs an injection as".
  The landed `SqFam` (`src/L/StageBound.lagda.md:36-40`) asks for the
  injection as data. That is why this file composes the DATA supply
  with the truncated consumer, and why it does not spend `SqCollect`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L".
  Declined. This task composes two delivered terms against a landed
  chapter. It does not ask for a condensation.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling".
  Not used. No glossary work in this task.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Not used. This landing is the L-tower counting leg, not the rud-route
  architecture.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries".
  Not used. No glossary work in this task.
