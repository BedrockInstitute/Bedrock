# LJ-1.461 report: land the counting leg's implication, and state its residue as a type

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term in `src/L/StageBound.lagda.md`, in the module that
already carries `bounded-from-trunc`:

    bounded-from-data :
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)
      → ⟨ x ∈ˢ Lset κ ⟩

and state `Residue` in that same chapter as a type, beside `SqCollect`.
The body is the identity adapter, then `∣_∣₁`, then `bounded-from-trunc`.
Do not land `bounded-from-residue` as `[LJ-1.456]` states it.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 5.

## PREDECESSOR VERDICTS, BEFORE ANY AGDA

`agents/tasks/LJ-1-456/lj-1.456-report.md:89`:

    **GO.** `bounded-from-residue` typechecks

The report is GO. It does not name the statement FALSE. I take the type
from the probe that typechecked, `agents/tasks/LJ-1-456/Probe456.agda:55-58`
(adapter, identity) and `:101-106` (obligation). I do not land
`bounded-from-residue`: that term takes `Residue` and never spends it
(`Probe456.agda:102`).

`agents/tasks/LJ-1-452/lj-1.452-report.md:77`:

    **GO.** `sq-data-closed` typechecks

The brief cites `:75`. Line 75 is the heading `## VERDICT`. The GO
sentence is at `:77`. The report is GO. It does not name the statement
FALSE.

`agents/tasks/LJ-1-447/lj-1.447-report.md:136`:

    **GO.** `descent-both` typechecks

The brief cites `:53`. Line 53 of that report quotes `[LJ-1.432]`'s GO,
not 447's own verdict. 447's own GO is at `:136`. The report is GO. It
does not name the statement FALSE.

Delivered `Residue` shape, `agents/tasks/LJ-1-447/Probe447.agda:208-210`:

    (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
  → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
  → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

None of the three reports is NO-GO. I did not stop. I did not inhabit a
FALSE type.

## D-10, BEFORE ANY AGDA

`SqFam` at `src/L/StageBound.lagda.md:35-41` as the chapter stood before
this landing:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

`[LJ-1.456]` adapter domain, `agents/tasks/LJ-1-456/Probe456.agda:56-58`:

    ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
  → SqFam α
    adapter f = f

The obligation's hypothesis:

    ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)

Conversion facts, already in the tree:

- `S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
- `_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`src/V/Hierarchy.lagda.md:83`).
- `sq` is that Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).

**The obligation's hypothesis IS `SqFam α` after the adapter.** The
adapter is the identity (`Probe456.agda:58`). The hypothesis already
uses the consumer spelling `S` and `∈ˢ`, and `sq δ` is the Sigma that
`SqFam` writes in full. W3 writes `inside : SqFam α → ⟨ x ∈ˢ Lset κ ⟩`
in the existing module and runs it. If the elaborator refuses, that
error is the finding and it outranks the obligation.

Corrected target: none. Original target stands on paper. W3 measured
that the chapter telescope already carries the type. Section 2.

## VERDICT

**GO.** `bounded-from-data` typechecks
(`src/L/StageBound.lagda.md:130-133`, exit 0, median 14.99 s on three
forced rechecks of the master, dependencies warm, caliber
`-A64m -I0 -M8g`) and PASSes the program's witness meter
(`.venv/bin/python scripts/pod/witness.py --code LJ-1-461 --brief
agents/tasks/LJ-1-461/LJ-1.461.md`, exit 0, 4.00 s, 0 UNRESOLVED of 1,
`probe_red=False`). `Residue` is stated at
`src/L/StageBound.lagda.md:51-59`, generic in the three seal
parameters, and is not inhabited. The body is three steps: the identity
adapter, then `∣_∣₁`, then `bounded-from-trunc`. No postulate. No
`subst`. No `--safe` off.

`.venv/bin/python` was absent at dispatch. I ran `make venv` from the
pinned `requirements-dev.txt` so `make check` could pass
`venv-check`. I added no dependency.

I did not write `review-of-bounded-from-data.md`. The verdict is GO.

A GO puts both routes' residues in one chapter, which is what
`[LJ-2.5]` must rule on. The DATA implication is now a term in `src/`.
The conclusion still rests on `Residue`, `levelIn` and `cover`. Nothing
in this tree proves `Residue`. This task does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not
claim a trophy.

## 1. What was built

- `src/L/StageBound.lagda.md`: added `isL` and `𝒮ʟ` to the Constructible
  import (`:14`), `∣_∣₁` to the truncation open (`:23`),
  `open hPropStructure 𝒮ʟ using () renaming (S to Sʟ)` (`:31`),
  `Residue` (`:51-59`), `adapter` (`:125-128`) and
  `bounded-from-data` (`:130-133`). Working-tree in-fence non-blank
  count is **109** (HEAD is 90). Added non-blank in-fence lines: 19.
  The estimate was about 20.
- `dev/ledger.toml` `gch_wing` row for `src/L/StageBound.lagda.md`,
  comment updated from 90 in-fence to 109.
- W3 term `inside` was written in the existing inner module, measured,
  then removed. It is not in the landed chapter. `src/` has no probe.
- `src/Everything.lagda.md` already imported `L.StageBound` at `:395`.
  I did not add a second import.

`Residue` is a type and nothing else. I did not inhabit it. I did not
postulate it. I did not land `bounded-from-residue`.

## 2. W3: `inside`, first

**GO.** The chapter's own telescope admits the term without a new
module. Evidence: `inside : SqFam α → ⟨ x ∈ˢ Lset κ ⟩` with body
`inside = go`, written in the existing inner module that already
carries `go` (`src/L/StageBound.lagda.md:111-118` today; during the
W3 run it sat immediately after `go`). Obligation and `Residue` were
omitted. No new module application. `[LJ-1.456]` rebuilt the telescope
in a probe; this chapter did not.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. The chapter interface was
deleted before every kept recheck
(`_build/2.8.0/agda/src/L/StageBound.agdai`).

First landing, obligation omitted: 16.91 s, peak RSS 2349236224 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, dependencies warm, exit 0 every time, each
printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 14.96 | 2349252608 |
| `runs/w3-3.out` / `w3-3.time` | 14.55 | 2349203456 |
| `runs/w3-4.out` / `w3-4.time` | 14.71 | 2349219840 |

Median wall **14.71 s**. Median peak RSS **2349219840** bytes. No heap
event.

THREE non-blank code lines for `inside` (comment, type, body). The
estimate was three lines and under 20 seconds on top of the chapter.
Measured, the whole chapter with `inside` is 14.71 s. That is the
chapter's own cost, not a new recursion. Nothing is funded against the
estimate. The telescope already carries the type. The obligation is
not outranked.

`inside` was removed after the measurement. Leaving an alias of `go`
would pad the chapter. The landed body goes through `∣_∣₁` and
`bounded-from-trunc`, not through `go` directly.

P-l did not fire: the type names `SqFam α`. It does not name a
transparent `sucV`-chain.

## 3. The obligation

`bounded-from-data` (`:130-133`) is three steps:

| step | supplier | file:line |
|---|---|---|
| adapter | identity, W3 of `[LJ-1.456]` restated | `:128`, spent at `:133` |
| `∣_∣₁` | `Cubical.HITs.PropositionalTruncation` | `:133` |
| consumer | landed `bounded-from-trunc` | `:122-123`, spent at `:133` |

The body does not spend `Residue`. `[LJ-1.452]` already spent it,
through `descent-both`, to inhabit `sq-data-closed`. This chapter does
not rebuild that recursion, so it cannot spend `Residue` again. The
named type is the data family, not `Residue → ⟨ x ∈ˢ Lset κ ⟩`. A
landed signature with an unused `Residue` parameter would overstate
what the term proves. That is why `bounded-from-residue` did not land.

Nothing was weakened. Nothing failed to close. I did not inhabit
`Residue`. I did not postulate it. I did not rebuild `κL` or `κC`. I
did not rebuild the band induction.

**The shape that resisted.** Restating `Residue` at the delivered type
names `κL`, `κC` and `isL-ord` (`Probe447.agda:208-210`). The chapter
does not import those seals. I parameterized `Residue` over the three
names (`:51-59`) and I did not write their bodies. That is how 456
hypothesized the three names without rebuilding either seal. If a
later brief wants those names absent from the file, it must give a
type for `Residue` that does not mention them.

## 4. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| data-family argument of `bounded-from-data` (`:130-132`) | obligation hypothesis; IS `SqFam α` after `adapter` | yes, at `:133` through `adapter` then `∣_∣₁` |
| `Residue` (`:51-59`) | `Probe447.agda:208-210`, generic in the three seals | not inhabited. Stated as a type. Not an argument of the obligation. |
| `isL-ord`, `κL`, `κC` | parameters of `Residue` (`:52-54`) | no. Needed to write `Residue`. No bodies. |
| `levelIn`, `cover` (`:106-108`) | `src/L/StageBound.lagda.md:106-108` | yes, already parameters of `bounded-from-trunc` |
| the outer StageBound telescope (`:93-100`) | same as `bounded-from-trunc` | yes, inherited |

Rebuilt, not hypothesized: nothing. Local `UK` and `HS` (`:102-103`)
are applications of landed modules. I did not import a probe.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `Residue` is generic in the ordinal `y` and in the three seal
parameters. `adapter` is generic in the family. `bounded-from-data`
lives in the chapter's existing anonymous telescope, including
`levelIn` and `cover`, and is generic in `κ`, `α`, `x` and `lam`. No
cardinal, no numeral and no site is named anywhere in the new terms
except `ω`, which is where the residue's own statement puts it. There
is no fixed form to report.

W4 does not fire: no module was retired.

## WHAT THE CHAPTER NOW OWES

The bounded-subset conclusion `⟨ x ∈ˢ Lset κ ⟩` still rests on these
hypotheses after this landing. Each is a type at `file:line`. None is
inhabited here.

1. **`Residue`**, `src/L/StageBound.lagda.md:51-59`.

       Residue :
           ((y : S) → IsOrd y → ⟨ isL y ⟩)
         → ((a : Sʟ) → IsOrd (fst a) → Sʟ)
         → ((a : Sʟ) → IsOrd (fst a) → Sʟ)
         → Type (ℓ-suc ℓ)

   After those three parameters it is `[LJ-1.447]`'s delivered shape
   (`Probe447.agda:208-210`). Nothing in this tree proves it. Nothing
   in this tree refutes it. `[LJ-1.452]` spends it, off-tree, to
   inhabit `sq-data-closed`. This chapter takes the data family as an
   argument and does not mention `Residue` in `bounded-from-data`.

2. **`levelIn`**, `src/L/StageBound.lagda.md:106`.

       (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩

3. **`cover`**, `src/L/StageBound.lagda.md:107-108`.

       (y : S) → ⟨ y ∈ˢ HS.M ⟩
     → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

**The condensation pair is unpaid and this task does not touch it.**
`levelIn` and `cover` are that pair. They stay module parameters of
the inner telescope. I did not inhabit them. I did not move them. I
did not import a condensation chapter.

## THE RATIO

Write-scope in-fence non-blank lines of the master: **109**
(`src/L/StageBound.lagda.md`, ledger caliber: non-blank lines inside
the ` ```agda ` fence). `Everything` is uncounted. `dev/ledger.toml`
and the report carry no fence.

Median wall of the three forced rechecks: **14.99 s**.

Seconds per in-fence line: **14.99 / 109 = 0.1375**. The live bar is
0.0123. The rate is above the bar.

This task ran `machine: exclusive`. One Agda process. The seconds
keys in the rule table are guarded by `concurrency == 1`
(`scripts/pod/table.py:575`). I did not write an accept record. The
concurrency of this run is **1**.

The two predecessor numbers the brief names, with this run's
concurrency beside them:

- `[LJ-1.453]` measured **0.0394** on its accept record. This run's
  concurrency is **1**.
- `[LJ-1.459]` measured **0.0266** on its own. This run's concurrency
  is **1**.

This content belongs to class **P-m** (`dev/LESSONS.md:2512`): the
chapter still contains instantiation of `Devlin55.BoundedSubsetAt`.
The new lines are parameterized composition. The measured rate is of
the whole write-scope chapter, not of the nineteen added lines. The
bar firing is the certificate that class predicts, not a defect, and
the chapter is not padded.

## THE LANDED OBLIGATION, RUNS

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

Full file, first check after the obligation landed: 14.96 s, exit 0,
peak RSS 2104901632 bytes, printed `Checking`. `runs/full-1.out` /
`full-1.time`.

Full file, three forced rechecks (chapter interface deleted before
each run, dependencies warm):

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 16.82 | 2002993152 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 14.89 | 2104868864 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 14.99 | 2104868864 |

Median wall **14.99 s**. Median peak RSS **2104868864** bytes. Exit 0
every time. Each printed `Checking`. No heap event.

The jump from W3's 14.71 s is 0.28 s. That is inside the recheck
spread of this three (1.93 s). The obligation is the identity plus
one `∣_∣₁` plus the already-landed `bounded-from-trunc`. It is not a
new recursion.

## make check

- Before any write under `src/`: **13.95 s**, exit 0, peak RSS
  951730176 bytes. Agda printed `Checking Everything`. `StageBound`
  was the `[LJ-1.453]` master, cached. `runs/make-check-before.out` /
  `make-check-before.time`.
- After the chapter lands: **12.37 s**, exit 0, peak RSS
  804929536 bytes. Agda printed `Checking Everything`. The chapter
  interface was current from the last recheck.
  `runs/make-check-after.out` / `make-check-after.time`. Closure is
  still 101 masters. `lint-agda.py --check src/L/StageBound.lagda.md`
  exits 0.

`scripts/measure/ledger.py --brief` at this working tree:

    standing 33,448 lines over 99 masters, measured from HEAD

That figure does not include the uncommitted nineteen lines.

## WHAT GO EARNS

**A GO puts both routes' residues in one chapter**, which is what
`[LJ-2.5]` must rule on. The truncated route's residue is `SqCollect`
at `:45-48`. The DATA route's residue is `Residue` at `:51-59`. The
DATA implication is `bounded-from-data` at `:130-133`. The truncated
implication remains `bounded-modulo-collect` at `:137-139`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This landing
  does not consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task lands the live-route counting implication in
  the chapter. It does not consult the retired-route journal.
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
  The DATA family is truncated with `∣_∣₁` at `:133`. That wrapper is
  the consumer's, not a new supply.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that only needs cardinal arithmetic never needs an injection as".
  The landed `SqFam` (`src/L/StageBound.lagda.md:36-40`) asks for the
  injection as data. That is why this file composes the DATA supply
  with the truncated consumer, and why `bounded-from-data` does not
  spend `SqCollect`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L".
  Declined. The condensation pair is unpaid and this task does not
  touch it.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling".
  Not used. No glossary work in this task.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Not used. This landing is the L-tower counting leg, not the rud-route
  architecture.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries".
  Not used. No glossary work in this task.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not inhabit `Residue`. I did not postulate it. I did not
  weaken it to a truncation.
- I did not land `bounded-from-residue`.
- I did not rebuild `[LJ-1.452]`'s recursion. I did not rebuild either
  seal.
- I did not import a probe.
- I did not write `review-of-bounded-from-data.md`. The verdict is GO.
- I did not rank the DATA route against the truncated route.
- I did not inhabit `levelIn` or `cover`. I did not touch the
  condensation pair.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.
- I did not pad the chapter for the ratio bar.
