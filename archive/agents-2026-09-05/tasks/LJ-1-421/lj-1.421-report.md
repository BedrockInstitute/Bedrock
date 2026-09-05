# LJ-1.421 report: is the campaign's residue a coding problem, or is it one untruncation

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-421/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-421/Probe421.agda`, at a
GENERIC ordinal:

    descent-from-data :
        (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

ONE question-hypothesis: `kappa-arrow-data`, the untruncated form of
`κ-injL`. No `amb-to-coded`, no `coded-descent`, no `IsCardinalL` in
that telescope.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`kappa-arrow-data` is the untruncation of `κ-injL`
(`agents/tasks/LJ-1-406/Probe406.agda:88-89`,
`src/L/Cardinal.lagda.md:133`). The tree already delivers

    ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁

That is existence of the injection. The untruncated form asks for the
same injection as data. The statement is not false. A cardinal
inequality is truncated existence of an injection
(`dev/literature/truncation-and-selection.md:75-80`). `leastOf` delivers
the least index untruncated; a data payload does not come out
(`dev/literature/truncation-and-selection.md:148-149`). What is in doubt
is the data, not the truth.

`[LJ-1.414]` is NO-GO on `amb-to-coded`
(`agents/tasks/LJ-1-414/lj-1.414-report.md:51`). I did not take that
type as a hypothesis and I did not inhabit it. `[LJ-1.406]` is GO on
`init-at-kappa` and on the truncated `κ-injL`
(`agents/tasks/LJ-1-406/lj-1.406-report.md:13-16`). `[LJ-1.413]` is GO
on `sq-data` (`agents/tasks/LJ-1-413/lj-1.413-report.md:16`). The
predecessor types this file copies are those GO deliveries.

Corrected target: none. Original target stands.

## VERDICT

**GO.** `d := κ` serves. `descent-from-data` typechecks
(`agents/tasks/LJ-1-421/Probe421.agda:225-263`, exit 0, median 1.66 s
on three forced rechecks) and PASSes the program's witness meter
(`scripts/pod/witness.py --code LJ-1-421 --brief
agents/tasks/LJ-1-421/LJ-1.421.md`, exit 0, 1.53 s, 0 UNRESOLVED of 1,
`probe_red=False`).

The campaign's residue is one untruncated arrow at a named ordinal,
`kappa-arrow-data` at `κL a oa`. That is a different object from
`[LJ-1.414]`'s general implication `amb-to-coded`. `[LJ-1.422]` prices
that object.

## 1. What was built

All in `agents/tasks/LJ-1-421/Probe421.agda`, module
`LJ-1-421.Probe421 {ℓ} (lem)`.

- `isL-ord`, sealed (`:62-63`), `mem-incl` (`:65-78`), `comp-inj`
  (`:80-82`). Rebuilt from `[LJ-1.413]`.
- `descent-data` at `[LJ-1.413]`'s delivered form (`:111-118`,
  `agents/tasks/LJ-1-413/Probe413.agda:123-129`).
- The ambient least cardinal, sealed at the call site: `κL`, `κoL`,
  `κ∈sucL`, `κ-injL` (`:125-135`). Same seal as `[LJ-1.406]`
  (`Probe406.agda:81-90`) and `[LJ-1.413]` (`Probe413.agda:135-146`).
  This site does not re-measure the wall.
- W3: `d-is-kappa` (`:144-150`).
- Plumbing, rebuilt: `kappa-not-fin` (`:167-183`) and `kappa-decides`
  (`:185-204`), from `[LJ-1.413]` `Probe413.agda:150-195`.
- Two module hypotheses (`:213-222`): `kappa-arrow-data` is the
  question; `init-at-kappa` is listed plumbing at `[LJ-1.406]`'s
  delivered type. No `amb-to-coded`, no `coded-descent`, no
  `IsCardinalL`. Those three names occur only in comments.
- `descent-from-data` (`:225-263`).

## 2. W3: `d-is-kappa`, first

**The failing argument is the DATA arrow, at type
`⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫`.**

`descent-data` at `[LJ-1.413]`'s delivered form
(`Probe413.agda:123-129`, rebuilt here at `:111-118`):

    descent-data : (x d : S) (ox : IsOrd (fst x))
                 → ⟨ fst d ∈ˢ fst x ⟩
                 → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
                 → sq (fst d)
                 → sq (fst x)

`d-is-kappa` (`:144-150`) applies that telescope with `d := κ` and
nothing else supplied:

    d-is-kappa x ox = descent-data x (κL x ox) ox

The remaining telescope is membership, the DATA arrow, and `sq` at `κ`.
That partial application elaborates.

The diagnostic then filled the arrow slot from the tree's truncated
`κ-injL`. Agda refused (`agents/tasks/LJ-1-421/runs/w3-from-tree.out:2-7`,
exit 42, 1.61 s, `UnequalTerms`):

    κ-injL x ox has type
      ∥ ⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫ ∥₁
    and descent-data wants
      ⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫

No other argument failed. Membership at `κ` is `kappa-decides`'s second
branch (`Probe413.agda:173-175`, rebuilt `:185-187`). `sq` at `κ` is
the induction hypothesis, once `κ` is a member and infinite.
`kappa-not-fin` (`:167-168`) spends the truncated `κ-injL` into
`Empty.⊥` and does not untruncate it. `coded-descent` is not needed
for membership, for infiniteness, or for `sq`.

The one argument `κ` does not carry as data is the descending arrow.
`kappa-arrow-data` is exactly that argument.

## 3. The obligation

`descent-from-data` (`:225-263`) splits on `kappa-decides`.

| case | supplier |
|---|---|
| `fst κ ≡ x` | `init-at-kappa` then `via-col-square`, transported. DATA. `:246-250`. Paid by `[LJ-1.406]`. No `Formula`, no `InjCode`, no Def tower. |
| `fst κ ∈ x` | `d-is-kappa` with `d := κ`, the arrow from `kappa-arrow-data`, `sq` from the IH at `κ`. DATA. `:253-259`. No `amb-to-coded`. No `coded-descent`. No `IsCardinalL`. |

**32 non-blank code lines** for `descent-from-data` (type plus body).
The brief's estimate was about 30, a comparable of SHAPE from
`[LJ-1.413]`'s case four with the `notCard` and `pack` blocks removed.
Nothing is funded against the estimate.

## 4. Extra hypotheses beyond `kappa-arrow-data`

The question-hypothesis is one, and it is `kappa-arrow-data`
(`:214-216`), the untruncated form of `κ-injL` at
`agents/tasks/LJ-1-406/Probe406.agda:88-89`.

One further hypothesis, listed as required:

| hypothesis | delivered type | why |
|---|---|---|
| `init-at-kappa` (`:217-222`) | `agents/tasks/LJ-1-406/Probe406.agda:180-185` | Case three is paid and needs no code. The brief names it so. |

Rebuilt, not hypothesized, copied from the delivered types:

| term | copied from |
|---|---|
| `κL`, `κoL` | `agents/tasks/LJ-1-406/Probe406.agda:82-86` and `agents/tasks/LJ-1-413/Probe413.agda:136-140` |
| `κ∈sucL` | `agents/tasks/LJ-1-413/Probe413.agda:142-143` |
| `kappa-decides` | `agents/tasks/LJ-1-413/Probe413.agda:173-175` |
| `kappa-not-fin` | `agents/tasks/LJ-1-413/Probe413.agda:150-151` |
| `descent-data` | `agents/tasks/LJ-1-413/Probe413.agda:123-129` |

The brief permits `κL`, `κoL` and `kappa-decides` as further
hypotheses. I rebuilt them at those types instead.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `kappa-arrow-data` is generic in `a`. `descent-from-data` is
generic in `x`. No site, no ordinal and no numeral is named anywhere
in the file except `ω`, which is the base. There is no fixed form to
report.

W4 does not fire: no module was retired.

## 6. WHAT THE ROUND TRIP BUYS

**What enters case four** (`agents/tasks/LJ-1-413/Probe413.agda:282-283`):
the truncated ambient arrow `κ-injL a ox` of type
`∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁` (`Probe413.agda:145`,
`src/L/Cardinal.lagda.md:133`), together with `κ ∈ x` from
`kappa-decides` (`Probe413.agda:278`) and infiniteness of `κ` from
`kappa-not-fin` (`Probe413.agda:282-283`).

**What leaves case four** (`agents/tasks/LJ-1-413/Probe413.agda:296-297`):
an untruncated ambient arrow `down : ⟪ fst a ⟫ ↪ ⟪ fst d ⟫` as DATA,
with `d ∈ x` and `d` infinite, packaged by `coded-descent`
(`Probe413.agda:226-231`, `agents/tasks/LJ-1-412/Probe412.agda:148-153`).

**The ONE property that differs:** truncation of the arrow. The round
trip starts at `∥ ↪ ∥₁` and ends at `↪`. Membership at a strictly
smaller ordinal and infiniteness are already on `κ` itself in this
branch. `descent-data` (`Probe413.agda:123-129`) does not ask for a
code and does not ask for `IsCardinalL`.

**The campaign's residue is an untruncation problem:** one untruncated
arrow at the named ordinal `κL a oa`. It is not a coding problem.

## 7. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 diagnostic, `d := κ` with the tree's truncated arrow: exit 42,
  1.61 s, `UnequalTerms` at the DATA arrow.
  `runs/w3-from-tree.out`.
- Full file, first check after the obligation landed: 1.69 s, exit 0,
  printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 1.67 s, 1.66 s, 1.65 s. Median
  **1.66 s**, exit 0 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.53 s, 0 UNRESOLVED
  of 1, `probe_red=False`.
- No heap event.

P-l did not fire: the types name the sealed atom `κL`, not a
transparent `sucV`-chain.

## 8. What GO earns, and what the next brief needs

A GO re-states the campaign's bill. The residue is

    kappa-arrow-data :
        (a : S) (oa : IsOrd (fst a))
      → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

That is one untruncated arrow at a named ordinal. It is not
`[LJ-1.414]`'s general implication from an arbitrary truncated
ambient injection to a code. `[LJ-1.414]`'s `HalfA` stays the bill
for a coding route. This measurement says case four does not take
that route.

`[LJ-1.422]` prices `kappa-arrow-data`. The tree delivers the
truncated form from `leastOf` (`src/L/Cardinal.lagda.md:117`,
`:133`). A data payload does not come out of that search
(`dev/literature/truncation-and-selection.md:148-149`).

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. The live producer is
  `dev/pod/queue.toml`. This probe does not consult the archived
  dispatch index.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The bound that chapter named is the square law.
  This probe supplies that law as data at a generic infinite ordinal,
  up to one untruncated arrow.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archive
  paths. This task does not retire a module.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived
  in full 2026-08-18". Declined. This task does not change a DD row.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used for D-10 and for the round-trip comparison: a cardinal
  inequality is a truncated injection, and that is what `κ-injL` is.
- `dev/literature/truncation-and-selection.md:148`, read: "delivers the
  least INDEX untruncated, and any payload it delivers with the". Used
  with `:149` "index is a proposition. **A data payload does not come
  out.**" The failing W3 argument is that payload.
- `dev/literature/devlin-II5.md:72`, read: "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Declined for this
  measurement. Condensation codes a collapse of a hull. This task asks
  whether case four needs a code at all, and it does not.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". Not used. This
  probe is the L-tower band step, not the rud-route architecture.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic
  geology sources and the five questions". Not used. Geology is not
  this measurement.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier:
  fourteen renderings for the owner's ruling". Not used. No glossary
  work in this task.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import `Probe406`, `Probe413` or `Probe414`.
- I did not inhabit `amb-to-coded`. I did not take `coded-descent` or
  `IsCardinalL` in any telescope.
- I did not untruncate `κ-injL`. The obligation is conditional on
  `kappa-arrow-data`.
