# LJ-1.456 report: the counting leg end to end, against the landed chapter

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-456/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-456/Probe456.agda`:

    bounded-from-residue : Residue → ⟨ x ∈ˢ Lset κ ⟩

where `Residue` is `[LJ-1.447]`'s hypothesis at the type the probe
delivered, and the body composes `[LJ-1.452]`'s `sq-data-closed` with
the landed `bounded-from-trunc`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 5.

## PREDECESSOR VERDICTS, BEFORE ANY AGDA

`agents/tasks/LJ-1-452/lj-1.452-report.md:77`:

    **GO.** `sq-data-closed` typechecks

The brief cites `:75`. Line 75 is the heading `## VERDICT`. The GO sentence
is at `:77`. The report is GO. It does not name the statement FALSE.

Delivered type, `agents/tasks/LJ-1-452/Probe452.agda:92-96`:

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

`agents/tasks/LJ-1-447/lj-1.447-report.md:136`:

    **GO.** `descent-both` typechecks

The brief cites `:53`. Line 53 of that report quotes `[LJ-1.432]`'s GO,
not 447's own verdict. 447's own GO is at `:136`. The report is GO. It
does not name the statement FALSE.

Delivered `Residue`, `agents/tasks/LJ-1-447/Probe447.agda:208-210`:

    (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
  → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
  → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

Neither predecessor is NO-GO. I did not stop. I did not inhabit a FALSE
type. I took both types from the probes that typechecked, not from a
brief.

## D-10, BEFORE ANY AGDA

Side by side.

`sq-data-closed` at `agents/tasks/LJ-1-452/Probe452.agda:92-96`:

    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → sq δ

`SqFam` at `src/L/StageBound.lagda.md:35-39`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

Conversion facts, already in the tree:

- `S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
- `_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`src/V/Hierarchy.lagda.md:83`).
- `sq` is that Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).

`[LJ-1.452]` reports the adapter as the identity
(`agents/tasks/LJ-1-452/lj-1.452-report.md:88`). That is a claim. This
file is where it becomes a term. W3 writes it as the identity and runs
it. If the elaborator refuses, that error is the finding and it outranks
the obligation.

Corrected target: none. Original target stands on paper. W3 measured it
as the identity. Section 2.

## VERDICT

**GO.** `bounded-from-residue` typechecks
(`agents/tasks/LJ-1-456/Probe456.agda:101-106`, exit 0, median 3.49 s
on three forced rechecks) and PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-456
--brief agents/tasks/LJ-1-456/LJ-1.456.md`, exit 0, 2.95 s, 0 UNRESOLVED
of 1, `probe_red=False`). `.venv/bin/python` is absent in this worktree.
`/usr/bin/python3` is 3.9.6 and has no `tomllib`. The meter ran under
`/opt/homebrew/bin/python3.11`. I added no dependency.

I did not write `review-of-bounded-from-residue.md`. The verdict is GO.

A GO gives `[LJ-2.5]` one type: the bounded-subset lemma's conclusion
follows from `Residue` against a chapter that is in `src/`, once
`sq-data-closed` is taken as the supply half `[LJ-1.452]` already
delivered. The conclusion holds under `Residue`, which nothing in this
tree proves. It does not touch `src/Landmarks.lagda.md`. It does not
close the campaign. It does not claim a trophy.

## 1. What was built

All in `agents/tasks/LJ-1-456/Probe456.agda`, module
`LJ-1-456.Probe456 {ℓ} (lem) (α)` (`:34-35`).

- `adapter` (`:55-58`). W3. Four lines. The identity.
- The landed telescope of `bounded-from-trunc`
  (`src/L/StageBound.lagda.md:79-110`), applied as module parameters
  (`:69-78`) plus `levelIn` and `cover` (`:85-87`). Local `UK` and `HS`
  (`:81-82`) are module applications of the landed `UnionKit` and
  `HullStage`, so those two hypotheses have the same types as
  `src/L/StageBound.lagda.md:93-95`. They are not a new proof.
- One module hypothesis `sq-data-closed` (`:88-89`) at
  `Probe452.agda:92-96`. I did not rebuild the band induction.
- Three module hypotheses `isL-ord`, `κL`, `κC` (`:90-92`) so
  `Residue` can be restated at `Probe447.agda:208-210`. I did not
  rebuild either seal. The file holds their types, not their bodies.
- `Residue` (`:95-99`) at that delivered type.
- `bounded-from-residue` (`:101-106`). Adapter, then `∣_∣₁`, then
  `bounded-from-trunc`. The `Residue` argument is not spent.

**62 non-blank non-comment lines** in the probe. The obligation from
`module _` through the term is 34 of those. The brief's estimate was
about 80 lines, of which the obligation was about 12, comparables of
SHAPE. The extra is the landed telescope, not a new proof. Nothing is
funded against the estimate.

## 2. W3: `adapter`, first

**GO.** The adapter is the identity. Evidence: `Probe456.agda:55-58`.

    adapter :
        ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
      → SqFam α
    adapter f = f

No `subst`. No repackaging. One side quantifies `(δ : V ℓ)` with `∈`.
The landed side quantifies `(δ : S)` with `∈ˢ`. They convert by
`src/V/Hierarchy.lagda.md:80` and `:83`, and by `sq` at
`src/L/Ordinal/SquareLaw.lagda.md:685-687`. `[LJ-1.452]`'s claim at
`lj-1.452-report.md:88` is now a term.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. The first landing rebuilt
`L.StageBound` and `L.SquareLawClosed` (`runs/w3-1.out`). The probe
interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-456/Probe456.agdai`).

First landing, obligation omitted: 15.09 s, peak RSS 2123284480 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`. That wall
is the cold chapter import, not the adapter.

Three forced rechecks, dependencies warm, exit 0 every time, each
printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 3.01 | 697892864 |
| `runs/w3-3.out` / `w3-3.time` | 2.97 | 697892864 |
| `runs/w3-4.out` / `w3-4.time` | 2.96 | 697892864 |

Median wall **2.97 s**. Median peak RSS **697892864 bytes**. No heap
event.

FOUR non-blank code lines for `adapter` (type plus body). The estimate
was three lines and under 5 seconds on top of the chapter import.
Measured, it is that size and in that second. Nothing is funded against
the estimate. The adapter is the identity. The obligation is not
outranked.

P-l did not fire: the type names `sq` and `SqFam α`. It does not name
a transparent `sucV`-chain.

## 3. The obligation

`bounded-from-residue` (`:101-106`) is three steps:

| step | supplier | file:line |
|---|---|---|
| adapter | identity, W3 | `:58`, spent at `:106` |
| `∣_∣₁` | `Cubical.HITs.PropositionalTruncation` | `:106` |
| consumer | landed `bounded-from-trunc` | `src/L/StageBound.lagda.md:109-110`, spent at `:103-106` |

The body does not spend `Residue`. `[LJ-1.452]` already spent it, through
`descent-both`, to inhabit `sq-data-closed`. This file does not rebuild
that recursion, so it cannot spend `Residue` again. The named type is
still `Residue → ⟨ x ∈ˢ Lset κ ⟩`. The unpaid statement of the counting
leg is that argument. The supply half is a hypothesis at the type
452 delivered.

Nothing was weakened. Nothing failed to close. I did not inhabit
`Residue`. I did not postulate it. I did not rebuild `κL` or `κC`. I
did not rebuild the band induction.

**The shape that resisted.** Restating `Residue` at the delivered type
names `κL`, `κC` and `isL-ord` (`Probe447.agda:208-210`). The brief
forbids rebuilding either seal and says the file holds no `κL` and no
`κC`. I hypothesized the three names (`:90-92`) and I did not write
their bodies. That is how 452 hypothesized `descent-both` without
rebuilding 447. If a later brief wants those names absent from the
file, it must give a type for `Residue` that does not mention them.

## 4. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| `sq-data-closed` (`:88-89`) | `Probe452.agda:92-96` | yes, at `:106` through `adapter` |
| `Residue` (`:95-99`) | `Probe447.agda:208-210` | not inhabited. Argument of the obligation. Not spent in the body. |
| `isL-ord` (`:90`) | `Probe447.agda:60-61`, type only | no. Needed to write `Residue`. |
| `κL` (`:91`) | `Probe447.agda:90-91`, type only | no. Needed to write `Residue`. |
| `κC` (`:92`) | `Probe447.agda:155-156`, type only | no. Needed to write `Residue`. |
| `levelIn`, `cover` (`:85-87`) | `src/L/StageBound.lagda.md:93-95` | yes, passed to `bounded-from-trunc` |
| the outer StageBound telescope (`:69-78`) | `src/L/StageBound.lagda.md:80-87` | yes, passed to `bounded-from-trunc` |

Rebuilt, not hypothesized: nothing. Local `UK` and `HS` (`:81-82`) are
applications of landed modules. I did not import a probe.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ` and in `α`. `adapter` is generic in the family. `Residue` is
generic in the ordinal `y`. `bounded-from-residue` is generic in the
landed telescope (`κ`, `x`, `lam`). No cardinal, no numeral and no
site is named anywhere in the file except `ω`, which is where the
obligation's own statement puts it. There is no fixed form to report.

W4 does not fire: no module was retired.

## 6. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **2.97 s**, median peak RSS
  **697892864 bytes**, exit 0. Section 2. First landing 15.09 s is
  the cold `L.StageBound` import (`runs/w3-1.out`).
- Full file, first check after the obligation landed: 3.45 s, exit 0,
  peak RSS 706707456 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 3.33 s, 3.49 s, 3.54 s. Peak RSS
  706691072, 706707456, 706723840 bytes. Median wall **3.49 s**.
  Median peak RSS **706707456 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 2.95 s, 0 UNRESOLVED
  of 1, `probe_red=False`. `runs/witness-1.out`.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event.

The next brief prices a `src/` landing against 3.49 s, not against an
estimate. The jump from W3's 2.97 s is the obligation's use of
`bounded-from-trunc`, not a new recursion. The adapter itself does
not re-measure the chapter.

## WHAT IS LEFT

`Residue` as a type, at `agents/tasks/LJ-1-447/Probe447.agda:208-210`,
restated at `agents/tasks/LJ-1-456/Probe456.agda:95-99`:

    (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
  → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
  → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

In words: when the ambient least cardinal of an infinite ordinal lies
strictly below that ordinal, so does the coded one.

This is the DATA route. The TRUNCATED route's residue is `SqCollect`,
already landed at `src/L/StageBound.lagda.md:43-46`. This file does
not use `SqCollect`. I do not rank the two routes. That ranking is
`[LJ-2.5]`'s.

Nothing in this tree proves `Residue`. Nothing in this tree refutes
it. This file takes it as an argument and does not inhabit it.

After this GO, the counting leg's remaining unpaid statement, on the
DATA route and against the landed consumer, is that one statement
about two ordinals. `[LJ-2.5]` is not this task.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This probe does
  not consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task measures the live-route counting leg against the
  landed chapter. It does not consult the retired-route journal.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry".
  Declined. This task does not retire a module. W4 does not fire.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18".
  Declined. This task does not change a DD row.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used to keep the two routes distinct: a cardinal inequality is a
  truncated injection, and `bounded-from-trunc` takes `∥ SqFam α ∥₁`.
  The DATA family is truncated with `∣_∣₁` at `:106`. That wrapper is
  the consumer's, not a new supply.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that only needs cardinal arithmetic never needs an injection as".
  The landed `SqFam` (`src/L/StageBound.lagda.md:35-39`) asks for the
  injection as data. That is why this file composes the DATA supply
  with the truncated consumer, and why it does not spend `SqCollect`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L".
  Declined. This task composes two delivered terms against a landed
  chapter. It does not ask for a condensation.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling".
  Not used. No glossary work in this task.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Not used. This probe is the L-tower counting leg, not the rud-route
  architecture.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries".
  Not used. No glossary work in this task.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import a probe.
- I did not rebuild `[LJ-1.452]`'s recursion. I did not rebuild either
  seal.
- I did not inhabit `Residue`. I did not postulate it. I did not
  weaken it to a truncation.
- I did not write `review-of-bounded-from-residue.md`. The verdict is
  GO.
- I did not rank the DATA route against the truncated route.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.
