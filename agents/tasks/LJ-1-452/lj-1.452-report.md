# LJ-1.452 report: the square law as DATA over the band, under one hypothesis

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-452/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-452/Probe452.agda`:

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

under the module parameters `{ℓ} (lem) (α₀) (oα₀)`, ONE module hypothesis
`descent-both` at `[LJ-1.447]`'s delivered type after its `residue`
argument, and `residue` carried at the module level of the story. No
truncation in the conclusion. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:318`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 5.

## PREDECESSOR VERDICT, BEFORE ANY AGDA

`agents/tasks/LJ-1-447/lj-1.447-report.md:53`:

    **GO.** `descent-both` typechecks

Delivered type, `agents/tasks/LJ-1-447/Probe447.agda:207-213`:

    descent-both :
        (residue : (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
                 → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
                 → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩)
      → (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

The report is GO. It does not name the statement FALSE. I did not stop. I
did not inhabit a FALSE type. I took the type from the probe that
typechecked, not from `[LJ-1.447]`'s brief.

`agents/tasks/LJ-1-437/lj-1.437-report.md:17`:

    **GO.** The obligation typechecks (`agents/tasks/LJ-1-437/Probe437.agda:345-348`,

## D-10, BEFORE ANY AGDA

The two motives, side by side:

    Goal437 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁
    Goal452 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

Branches of `Probe437.agda:305-310`:

- `inl` (finite): `Empty.rec (infx x∈ω)` at `:307`. Does not change.
  `Empty.rec` inhabits any type.
- `inr (inl)` (`ω`): `:308` wraps `subst sq (sym x≡ω) squareω` in `∣_∣₁`.
  The wrapper drops. The term under it is already data. That is W3, not
  a new supplier.
- `inr (inr)` (the third): `:309` splits on a cardinal. This is the only
  branch that changes its supplier. It becomes `descent-both` at the
  delivered type.

The plan is not wrong. Only the third branch changes its supplier. The
`ω` branch drops a constructor that the untruncated motive no longer
asks for.

Corrected target: none. Original target stands.

## VERDICT

**GO.** `sq-data-closed` typechecks
(`agents/tasks/LJ-1-452/Probe452.agda:92-96`, exit 0, median 3.46 s
on three forced rechecks) and PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-452
--brief agents/tasks/LJ-1-452/LJ-1.452.md`, exit 0, 3.74 s, 0 UNRESOLVED
of 1, `probe_red=False`). `.venv/bin/python` is absent in this worktree.
`/usr/bin/python3` is 3.9.6 and has no `tomllib`. The meter ran under
`/opt/homebrew/bin/python3.11`. I added no dependency.

I did not write `review-of-sq-data-closed.md`. The verdict is GO.

A GO puts the counting leg's supply half in DATA form under one named
hypothesis. With the landed consumer, the adapter is the identity, so
the bounded-subset lemma's conclusion follows from `residue` alone.
The conclusion holds under `residue`, which nothing in this tree proves.
It does not touch `src/Landmarks.lagda.md`. It does not close the
campaign. It does not claim a trophy.

## 1. What was built

All in `agents/tasks/LJ-1-452/Probe452.agda`, module
`LJ-1-452.Probe452 {ℓ} (lem) (α₀) (oα₀)` (`:28-29`).

- `omega-branch` (`:49-50`). W3. Two lines.
- `band-ord` (`:54-57`). Copied from `Probe437.agda:284-288`.
- One module hypothesis `descent-both` (`:67-70`) at
  `Probe447.agda:211-213`, which is 447's delivered term after its
  `residue` argument. The file holds no `κL` and no `κC`. The four
  cases are not restated. I did not import a probe.
- `Goal`, `step`, `sq-data-closed` (`:73-96`).
- The IH adapter `ih∈ˢ` (`:88-90`). A lambda. No `subst`.
- The consumer adapter `sq-data-to-SqFam` (`:101-102`). The identity.

**55 non-blank non-comment lines** in the probe. The obligation from
`module _` through the adapter is 26 of those. The brief's estimate was
about 120 lines, of which the obligation and its recursion were about
30, comparables of SHAPE. Measured, the file is smaller. Nothing is
funded against the estimate.

## 2. W3: `omega-branch`, first

**GO.** `squareω` is data. Evidence: `src/L/InjChain.lagda.md:184-185`,
`squareω : sq ω` / `squareω = pairω , pairω-inj`. The branch is

    omega-branch : (x : V ℓ) → x ≡ ω → sq x
    omega-branch x x≡ω = subst sq (sym x≡ω) squareω

at `Probe452.agda:49-50`. It is `Probe437.agda:308` with `∣_∣₁` dropped.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. Dependencies warm. The probe
interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-452/Probe452.agdai`).

First landing, obligation omitted: 2.18 s, peak RSS 404176896 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.77 | 404160512 |
| `runs/w3-3.out` / `w3-3.time` | 1.73 | 404209664 |
| `runs/w3-4.out` / `w3-4.time` | 1.84 | 380715008 |

Median wall **1.77 s**. Median peak RSS **404160512 bytes**. No heap
event.

TWO non-blank code lines for `omega-branch` (type plus body). The
estimate was two lines and under 3 seconds. Measured, it is that size
and in that second. Nothing is funded against the estimate. The
truncation at the `ω` branch of `[LJ-1.437]` was not the arrow's. The
untruncated motive closes there.

P-l did not fire: the type names `sq x` and `x ≡ ω`. It does not name
a transparent `sucV`-chain.

## 3. The obligation

`sq-data-closed` (`:92-96`) is `∈-induction` at motive `Goal` (`:73-74`).
The three branches of `step` (`:79-90`):

| branch | supplier | file:line |
|---|---|---|
| finite | `Empty.rec (infx x∈ω)` | `:80` |
| `ω` | `omega-branch` | `:81` |
| infinite, not `ω` | `descent-both x ox ω∈x ih∈ˢ` | `:82` |

The finite branch did not change. The `ω` branch dropped `∣_∣₁`. The
third branch spends `descent-both` and does not restate a cardinal
split.

**The IH adapter**, at `:88-90`:

    ih∈ˢ : (y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y
         → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y
    ih∈ˢ y y∈x oy infy = ih y y∈x oy infy

`∈-induction` supplies `(y) → ⟨ y ∈ x ⟩ → Goal y`, and `Goal` puts the
certificate first (`:74`). `descent-both` wants
`(y) → ⟨ y ∈ˢ x ⟩ → IsOrd y → infinite y → sq y` (`:69`). The order
matches. The two memberships convert: `_∈ˢ_` on `𝒮ᵥ` is `_∈_`
(`src/V/Hierarchy.lagda.md:83`). No `subst`. That is not a finding.

Nothing was weakened. Nothing failed to close. `residue` stays an
unproved hypothesis of the story. Its type is not restated in this
file: restating it names `κL` and `κC`, which the brief forbids
(`LJ-1.452.md:81-82`). The module hypothesis is 447's remaining type
after that argument (`Probe447.agda:211-213`).

## DOES IT MEET THE CONSUMER

`sq-data-closed` at `agents/tasks/LJ-1-452/Probe452.agda:92-96`:

    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → sq δ

`SqFam` at `src/L/StageBound.lagda.md:33-37`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

The adapter, typechecked at `Probe452.agda:101-102`:

    sq-data-to-SqFam : SqFam α₀
    sq-data-to-SqFam = sq-data-closed

**It is the identity.** `S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
`_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`:83`). `sq` is that Sigma
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). No `subst`. No
repackaging.

The counting leg's consumer is fed under one hypothesis. Instantiating
`L.StageBound.Instantiation` at `α₀` with `sq-data-to-SqFam` is
`SqFam α₀` as data, and that data is `sq-data-closed`. The
bounded-subset lemma's conclusion then follows from `residue` alone.

## 4. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| `descent-both` (`:67-70`) | `Probe447.agda:211-213`, after `residue` | yes, third branch at `:82` |
| `residue` | `Probe447.agda:208-210`. Not restated: the type names `κL` and `κC`. Carried as the argument 447 spends to inhabit the hypothesis above. | not inhabited |

Rebuilt, not hypothesized:

| term | copied from |
|---|---|
| `band-ord` | `Probe437.agda:284-288` |
| `omega-branch` | `Probe437.agda:308` with `∣_∣₁` dropped |
| `Goal`, `step`, `sq-data-closed` | `Probe437.agda:297-348` at the untruncated motive, third branch replaced |

I did not rebuild either seal. I did not restate the four cases. I did
not import a probe.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ` and in `α₀`. `omega-branch` is generic in `x`. `band-ord` is
generic in the band member. `Goal`, `step` and `sq-data-closed` are
generic in the band ordinal. No cardinal, no numeral and no site is
named anywhere in the file except `ω`, which is where the obligation's
own statement puts it. There is no fixed form to report.

W4 does not fire: no module was retired.

## 6. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **1.77 s**, median peak RSS
  **404160512 bytes**, exit 0. Section 2.
- Full file, first check after the obligation landed: 3.75 s, exit 0,
  peak RSS 728875008 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 3.54 s, 3.46 s, 3.35 s. Peak RSS
  726597632, 685424640, 728875008 bytes. Median wall **3.46 s**.
  Median peak RSS **726597632 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 3.74 s, 0 UNRESOLVED
  of 1, `probe_red=False`. `runs/witness-1.out`.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event.

The next brief prices a `src/` landing against 3.46 s, not against an
estimate. The jump from W3's 1.77 s is the `L.StageBound` import that
the consumer adapter spends. The recursion itself does not re-measure
the cardinal seals.

## WHAT IS LEFT

`residue` as a type, at `agents/tasks/LJ-1-447/Probe447.agda:208-210`:

    (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
  → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
  → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

Nothing in this tree proves it. Nothing in this tree refutes it. This
file spends `descent-both` after that argument and does not inhabit
the argument.

The supply half of the counting leg is now DATA under that one
statement. The consumer adapter is the identity. A `src/` landing of
`sq-data-closed` as `SqFam` is a copy, not a new proof. `[LJ-2.5]` is
not this task.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This probe does
  not consult the archived dispatch index.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task measures the live-route band induction. It does
  not consult the retired-route journal.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18".
  Declined. This task does not change a DD row.
- `archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules".
  Declined. This task is a probe. It does not consult the archived
  orchestrator rules.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used to keep W3 honest: a cardinal inequality is a truncated
  injection, but `squareω` is not an inequality. It is `sq ω` as data
  (`src/L/InjChain.lagda.md:184`). The `∣_∣₁` at `Probe437.agda:308`
  was not forced by the arrow.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that only needs cardinal arithmetic never needs an injection as".
  The consumer `SqFam` (`src/L/StageBound.lagda.md:33-37`) asks for
  the injection as data. That is why this task untruncates. Cardinal
  arithmetic would have stopped at `[LJ-1.437]`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L".
  Declined. This task runs a band induction already written. It does
  not ask for a condensation.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Not used. This probe is the L-tower band step, not the rud-route
  architecture.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling".
  Not used. No glossary work in this task.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions".
  Not used. Geology is not this measurement.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import a probe.
- I did not rebuild `κL` or `κC`. I did not restate the four cases.
- I did not inhabit `residue`. I did not postulate it. I did not
  weaken it to a truncation. I did not restate its type, because that
  type names the two seals.
- I did not write `review-of-sq-data-closed.md`. The verdict is GO.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.
