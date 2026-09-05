# LJ-1.448 report: the square law as DATA over the whole band

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-448/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-448/Probe448.agda`, at a
GENERIC band:

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

under `{ℓ} (lem) (α₀) (oα₀)`, ONE module hypothesis `descent-both` at
`[LJ-1.447]`'s delivered type, and its `residue` parameter.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 4.

## GATE

The brief orders two tests before anything else
(`agents/tasks/LJ-1-448/LJ-1.448.md:20-25`).

Test 1, relative to this worktree: `test -f agents/tasks/LJ-1-447/lj-1.447-report.md`
exits 1. HEAD is `76c0f2f` (`pod: admit LJ-1.448`). That commit predates
`ef44a34` (`pod: LJ-1.447 done, row task-lj-1-447-go`).

Test 1, against the committed predecessor: the report exists at
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-447/lj-1.447-report.md`
and in git object `ef44a34`. This dispatch is the re-queue after that
commit. I opened that report and its probe. I did not copy a type out
of `[LJ-1.447]`'s brief
(`dev/pod/audit-2026-08-20.md:41-42`, "the brief, not the result";
`:49`, "398 copied the brief type without saying so").

Test 2: `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-447/lj-1.447-report.md:136`
reads "**GO.** `descent-both` typechecks". It does not name the statement
FALSE. I did not stop.

The delivered type, `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-447/Probe447.agda:207-213`:

    descent-both :
        (residue : (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
                 → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
                 → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩)
      → (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

The remaining telescope after residue is applied is `:211-213`. That is
the type this file takes as the module hypothesis. See section 3.

The first dispatch of this task stopped because Test 1 failed in this
worktree. That STOP is the file
`agents/tasks/LJ-1-448/review-of-sq-data-closed.md`. This dispatch does
not rest on it. The current verdict is GO, below.

## 0. D-10, before any Agda

The two motives, side by side (`LJ-1.448.md:77-79`):

    Goal437 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁
    Goal448 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

`Goal437` is the motive at `agents/tasks/LJ-1-437/Probe437.agda:297-298`.
`[LJ-1.437]` is GO (`agents/tasks/LJ-1-437/lj-1.437-report.md:17`). That
report does not name the statement FALSE.

The three branches at `Probe437.agda:305-310`:

| branch | line | body in 437 | body at Goal448 |
|---|---|---|---|
| finite | `:307` | `Empty.rec (infx x∈ω)` | the same. `Empty.rec` inhabits any type |
| `ω` | `:308` | `∣ subst sq (sym x≡ω) squareω ∣₁` | drop `∣_∣₁`. That is W3 |
| cardinal | `:309` | `splitOwn (kappa-decides a ox)` | spend `descent-both` as data |

One line: the finite body does not change; the `ω` body drops only the
motive constructor; the third body is the one that needs a new
supplier. The plan is not wrong on D-10. W3 then measured the `ω`
body, and the obligation measured the third.

Corrected target: none. Original target stands.

## VERDICT

**GO.** `sq-data-closed` typechecks
(`agents/tasks/LJ-1-448/Probe448.agda:105-109`, exit 0, median 1.57 s
on three forced rechecks) and PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-448 --brief agents/tasks/LJ-1-448/LJ-1.448.md`, exit 0,
1.43 s, 0 UNRESOLVED of 1, `probe_red=False`).
`.venv/bin/python` is absent in this worktree. The witness meter ran
under the main checkout's `.venv/bin/python` (Python 3.11.16). This
worktree's `python3` is 3.9.6 and has no `tomllib`. I added no
dependency.

I did not write a new `review-of-*.md` for this dispatch. The verdict
is GO. The file `review-of-sq-data-closed.md` is the first dispatch's
STOP on the missing predecessor, not this dispatch's verdict.

A GO puts the counting leg's supply half in DATA form, under one named
hypothesis. It does not inhabit `residue`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not
claim a trophy.

## 1. What was built

All in `agents/tasks/LJ-1-448/Probe448.agda`, module
`LJ-1-448.Probe448 {ℓ} (lem) (α₀) (oα₀)`.

- `omega-branch` (`:50-51`). W3. Two lines.
- `band-ord` (`:55-58`). Copied from `Probe437.agda:284-288`.
- `SqFam` (`:61-65`). Copied from `Probe434.agda:44-48`.
- Inner module hypothesis `descent-both` (`:74-78`) at the remaining
  telescope of `Probe447.agda:211-213`.
- `ih-adapt` (`:91-95`). The call-site adapter. Body is η-expansion.
  Not a `subst`.
- `Goal`, `step`, `sq-data-closed` (`:81-109`).
- `meets-consumer` (`:113-116`). Body is the identity.
- `meets-closed` (`:118-119`). The identity applied to the obligation.

I did not import a probe. I did not rebuild `κL` or `κC`. I did not
restate the four cases. I did not write in `src/`.

119 lines in the file (`wc -l`). The estimate was about 120. Nothing is
funded against the estimate.

## 2. W3: `omega-branch`, first

**GO.** `squareω` is not truncated. The `ω` branch untruncates.

Type: `(x : V ℓ) → x ≡ ω → sq x`. Body:
`subst sq (sym x≡ω) squareω` (`Probe448.agda:50-51`). `squareω` comes
from `L.InjChain` (`src/L/InjChain.lagda.md:184`, `squareω : sq ω`).
`Probe437.agda:308` is the same line under `∣_∣₁`.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. Dependencies warm. The probe
interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-448/Probe448.agdai`).

First landing, obligation omitted: 1.37 s, peak RSS 378175488 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.43 | 378175488 |
| `runs/w3-3.out` / `w3-3.time` | 1.48 | 378224640 |
| `runs/w3-4.out` / `w3-4.time` | 1.42 | 378208256 |

Median wall **1.43 s**. Median peak RSS **378208256 bytes**. No heap
event.

TWO non-blank code lines (type plus body). The estimate was two lines
and under 3 seconds. Measured, it is the same two lines and 1.43 s.
Nothing is funded against the estimate. The plan does not fail at its
cheapest point.

## 3. The obligation

`sq-data-closed` (`:105-109`) is `∈-induction` at motive `Goal`
(`:81-82`). The three branches of `step` (`:97-103`):

| branch | supplier | file:line |
|---|---|---|
| finite | `Empty.rec (infx x∈ω)` | `:101` |
| `ω` | `omega-branch` | `:102` |
| cardinal | `descent-both x ox ω∈x (ih-adapt x ih)` | `:103` |

Nothing was weakened in the conclusion. The conclusion is `sq δ`, not
`∥ sq δ ∥₁`. The third branch does not split on a cardinal.

**The residue parameter.** The delivered type of `descent-both` takes
`residue` as its first argument (`Probe447.agda:208-210`). That
argument's type names `κL` and `κC`. The brief forbids rebuilding
either seal and says this file holds no `κL` and no `κC`
(`LJ-1.448.md:89-92`). I therefore take the remaining telescope
(`Probe447.agda:211-213`) as the module hypothesis. Residue is carried
by whoever instantiates that hypothesis: they supply
`P447.descent-both residue`. I did not inhabit `residue`. I did not
postulate it. I did not weaken it to a truncation.

That is not a change of the conclusion. It is the type the third
branch spends. Writing residue's type in this file would have named
the two seals the brief forbids.

**The induction-hypothesis adapter.** Named `ih-adapt` at `:91-95`.
Body `ih y y∈x oy infy`. On `𝒮ᵥ`, `_∈ˢ_` is `_∈_`
(`src/V/Hierarchy.lagda.md:83`, read: `; _∈ˢ_   = _∈_ }`). Unfolding
`Goal` makes 447's IH telescope (`Probe447.agda:212`) the same as
what `∈-induction` supplies. The adapter is η-expansion. It is not a
`subst`. I did not hide a `subst`.

## 4. W2 and DD4

The module is generic in `ℓ` and in `α₀`. `omega-branch`, `band-ord`,
`Goal`, `step`, `sq-data-closed` and both adapters quantify over a
generic carrier. No cardinal, no band and no numeral is named anywhere
in the file except `ω`, which is where the obligation's own statement
puts it. There is no fixed form to report.

W4 does not fire: no module was retired.

## 5. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **1.43 s**, median peak RSS
  **378208256 bytes**, exit 0. Section 2.
- Full file, first check after the obligation landed: 1.53 s, exit 0,
  peak RSS 410992640 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 1.57 s, 1.49 s, 1.57 s. Peak RSS
  411009024, 410976256, 410943488 bytes. Median wall **1.57 s**.
  Median peak RSS **410976256 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.43 s, 0 UNRESOLVED
  of 1, `probe_red=False`. `runs/witness-1.out`.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event.

## 6. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| `descent-both` (`:75-78`) | remaining telescope of `Probe447.agda:211-213` | yes, at `:103` |

No other hypothesis. `residue` is not a parameter of this file. See
section 3.

Rebuilt, not hypothesized:

| term | copied from |
|---|---|
| `band-ord` | `Probe437.agda:284-288` |
| `SqFam` | `Probe434.agda:44-48` |
| `omega-branch` | `Probe437.agda:308` without `∣_∣₁` |
| `Goal` / `step` / the induction | `Probe437.agda:297-348` at the untruncated motive |

I did not import a probe. I did not rebuild `init-at-kappa`. I did not
rebuild either seal.

## DOES IT MEET THE CONSUMER

The two types, as they stand, and the adapter that typechecks.

**Supply, inhabited** (`Probe448.agda:105-109`):

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

**Consumer, as `[LJ-1.434]` delivered it**
(`agents/tasks/LJ-1-434/Probe434.agda:44-48`):

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

Copied at `Probe448.agda:61-65`. `[LJ-1.434]` is GO on the truncated
consumer (`agents/tasks/LJ-1-434/lj-1.434-report.md:52`). The chapter's
module parameter is the same Sigma
(`src/L/BoundedSubset.lagda.md:1388-1390`).

**The adapter** (`Probe448.agda:113-116`):

    meets-consumer :
        ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
      → SqFam α₀
    meets-consumer z = z

Body is the identity. It typechecks. `meets-closed`
(`Probe448.agda:118-119`) is `meets-consumer sq-data-closed`. On `𝒮ᵥ`,
`S` is `V ℓ` and `_∈ˢ_` is `_∈_` (`src/V/Hierarchy.lagda.md:80-83`).
`sq` is the Sigma that `SqFam` writes in place
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). There is no repackaging.
There is no `subst`.

**The counting leg's consumer is fed under one hypothesis.** That
hypothesis is `descent-both` at the remaining telescope of
`[LJ-1.447]`, which is `P447.descent-both residue` at the instantiator.
`residue` is not discharged. The trophy is not claimed. The campaign
does not close.

## WHAT THE NEXT BRIEF NEEDS

1. `residue` remains an undischarged type at
   `Probe447.agda:208-210`. Nothing in this tree proves it. Nothing in
   this tree refutes it. C-42: `[LJ-1.441]`'s NO-GO measures that site,
   not this one.
2. This file does not re-type `residue`, because that type names `κL`
   and `κC`. A landing that must mention `residue` by name in a
   telescope has to take those seals as parameters, or import them, or
   rebuild them. The brief of this task forbade the rebuild.
3. The consumer adapter is the identity at this spelling of `S` (the
   `𝒮ᵥ` carrier). If a later consumer opens `𝒮ʟ` instead, re-measure
   the adapter. A measured cure does not transfer by analogy.
4. Do not claim the trophy from this GO.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import a probe.
- I did not inhabit `residue`. I did not postulate it.
- I did not rebuild `κL` or `κC`. I did not restate the four cases.
- I did not hide a `subst` in either adapter.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: named, not used. Opened at the
  head (`archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18").
  The live producer is `dev/pod/queue.toml`. This probe does not
  consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md`: named, not used. Opened at the
  head (`archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route").
  This task measures a live band induction. It does not consult the
  retired-route journal.
- `archive/dev/JOURNAL.md`: named, not used. Opened at the head
  (`archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20"). The
  per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md`: named, not used. Opened at the head
  (`dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry").
  W4 does not fire: no module was retired.
- `archive/dev/DD-archived.md`: named, not used. Opened at the head
  (`archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18").
  The W2 and W3 duties I applied come from the slot file and the
  brief, not from an archived DD row.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: named, not used. Opened at the
  head (`dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L").
  No condensation argument was consulted. The band induction spends
  a delivered descent, not a collapse.
- `dev/literature/truncation-and-selection.md`: named, not used.
  Opened at the head (`dev/literature/truncation-and-selection.md:1`,
  read: "# Truncation and selection: how the two literatures pick a witness").
  W3 measured `squareω` at the chapter (`src/L/InjChain.lagda.md:184`),
  not a `leastOf` payload. The truncation that this task drops is the
  motive constructor, not a selection.
- `dev/literature/digest.md`: named, not used. Opened at the head
  (`dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature").
  This probe is the L-tower band step, not the rud-route architecture.
- `dev/literature/terms-2026-08.md`: named, not used. Opened at the
  head (`dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling").
  No glossary work in this task.
- `dev/literature/geology.md`: named, not used. Opened at the head
  (`dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions").
  Geology is not this measurement.
