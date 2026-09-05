# LJ-1.487 report: the Sigma-one transfer, the failing step of cover

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-487/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-487/Probe487.agda`:

    CoverWitnessesInHull :
        (y : S) → ⟨ y ∈ˢ M ⟩
      → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

The type is taken from `[LJ-1.484]`'s probe that typechecked its
neighbours, `agents/tasks/LJ-1-484/Probe484.agda:123-126`, never from
this brief. Land nothing in `src/`.

W3 first, the type the brief names:

    ord-by-wit : ⟨ some ordinal ∈ˢ M ⟩

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## WHICH PREMISE MOVED

`[LJ-1.484]` is a critic-upheld NO-GO. Heading `## VERDICT` at
`agents/tasks/LJ-1-484/lj-1.484-report.md:114`. Quote at `:116-121`:

> **NO-GO at D-10 step 4, after W3 and the ambient covering both
> closed.** Step 1 is GO. Step 2 is the wrong shape. Step 3 is GO
> and does not pay `cover`: the index is in `lam`, not in `M`.
> Step 4 is unbuilt. That is the literature transfer of the covering
> witnesses into the hull. The obligation term `cover` is not
> written.

I did not inhabit `cover`. I did not take `levelIn` as a hypothesis.
The type I must inhabit is step 4 of that decomposition, copied from
the probe.

`[LJ-1.160]` measured that the hull is not transitive
(`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). That measurement
still stands.

## THE DECOMPOSITION, QUOTED FROM `[LJ-1.484]`

Quote, `agents/tasks/LJ-1-484/lj-1.484-report.md:129-185`:

> ## THE DECOMPOSITION
>
> Every step as a type. Each marked BUILT or UNBUILT. This section
> is what the next brief is written from.
>
> 1. **code-of.** BUILT. W3.
>
>        code-of : (y : S) → ⟨ y ∈ˢ M ⟩
>                → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁
>
>    Term: `Probe484.agda:68-69`, `code-of = H.hull-member`.
>    Supplier: `src/L/Hull.lagda.md:337-339`.
>
> 2. **StageBoundOfCode.** UNBUILT. Wrong shape. The brief's step 2.
>
>        StageBoundOfCode :
>            (c : Code) → Σ[ γ ∈ S ] (IsOrd γ × ⟨ fst (val c) ∈ˢ Lset γ ⟩)
>
>    Site: `Probe484.agda:110-112`. `Code` is `base` or `wit`
>    (`src/L/Hull.lagda.md:72-74`). Neither carries an ordinal.
>
> 3. **ambient-cover and ambient-level.** BUILT. Not `cover`.
>
>        ambient-cover : (y : S) → ⟨ y ∈ˢ M ⟩
>          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
>
>        ambient-level : (y : S) → ⟨ y ∈ˢ M ⟩
>          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
>
>    Terms: `Probe484.agda:80-82` and `:88-98`. ... The index is in `lam`. It is
>    not in `M`.
>
> 4. **CoverWitnessesInHull.** UNBUILT. The failing step.
>
>        CoverWitnessesInHull :
>            (y : S) → ⟨ y ∈ˢ M ⟩
>          → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
>
>    Site: `Probe484.agda:123-126`. This is Devlin's Σ₁ transfer
>    of the covering witnesses into the hull
>    (`dev/literature/devlin-II5.md:107-108`).

Step 4's type from the probe that typechecked, `Probe484.agda:123-126`.

## D-10, BEFORE ANY AGDA

The obstruction is `γ ∈ M`, not `y ∈ Lset γ`. Two routes, weighed
before a term.

1. **By `wit`.** The hull is closed under definable existence
   (`src/L/Hull.lagda.md:120-123`). `[LJ-1.472]` and `[LJ-1.474]`
   put numerals and numeral-codes in the hull by `wit` at a
   formula of type `Formula (⊥* {ℓ}) (suc k)`. The covering index
   of an arbitrary hull member `y` is not a numeral. The formula
   that would name it is "γ is an ordinal and y ∈ Lset γ". `Lset`
   is not a constructor of the hull language. The tree's Φ is
   `LsetGraphAt` at `src/L/Coding/Sequence.lagda.md:349`, type
   `Formula CS.S n`. `wit` takes `Formula (⊥* {ℓ}) (suc k)` at
   `src/L/Hull.lagda.md:74`. Packaging is `absFo`
   (`src/FOL/Manipulation/Parameters.lagda.md:260`), measured by
   `[LJ-1.462]`. Adequacy of the graph is `Lset-only` /
   `Lset-defines` at `src/L/Hierarchy.lagda.md:334-335` and
   `:646-648`, at the class carrier `𝒮ʟ`. The hull's search is at
   the stage `AbsL.𝒮M`. Those semantics do not meet. The level
   formula lets `wit` *name* a covering formula (`coverIndex` at
   `Probe487.agda:139-143`). It does not let `wit` *search* that
   formula at this telescope.

2. **By elementarity.** Devlin transfers
   "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" by Σ₁-elementarity of X in L_α
   (`dev/literature/devlin-II5.md:107-108`). The tree has the
   TYPE `AtM.Elementary` at `src/L/Hull.lagda.md:174-176` and the
   inhabitant `HullElemDown.WithCode.elem` at
   `src/L/BoundedSubset.lagda.md:759-760`, under a canonical-code
   hypothesis. The consumer at a concrete `X` inhabits it at
   `:1543-1545`. The generic `HullStage` telescope of this probe
   does not. `Elementary` is at `Formula SM`. The covering
   statement in the tree is `reverse` at
   `src/L/BoundedSubset.lagda.md:865-869`, type `Formula CS.S 1`.
   Those languages do not meet. The tree does not have
   `M ≺_{Σ₁} L_lam` at the language of the level formula, at this
   telescope.

**I took route 1.** W3 is the cheapest split: one ordinal by `wit`
at a formula, obligation omitted. Route 1 is nearer after W3. It
does not close for a general covering index. Route 2 is farther.
What route 1 lacks is Sat of the packaged covering formula at the
stage, and a filled `Vec Code` at `countFo coverIndex`.

## W8, LITERATURE, BEFORE ANY AGDA

The orthodox argument, `dev/literature/devlin-II5.md:107-108`:
the reverse inclusion M ⊆ ⋃_{γ<β} L_γ transfers the Σ₁ statement
"∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" from L_α to X by Σ₁-elementarity and
along the collapse. Φ is the Σ₀ level formula of II.2.7
(`dev/literature/devlin-II5.md:95-99`). The transfer needs
elementarity this tree does not have at this telescope, at this
language. That is an obstruction of a route, not a literature
refutation of the type. I do not stop as a literature NO-GO
before W3.

## PREDECESSOR TYPES

- `[LJ-1.484]` is NO-GO at D-10 step 4
  (`agents/tasks/LJ-1-484/lj-1.484-report.md:114`). The statement
  `cover` is not named FALSE. This task inhabits step 4 of that
  decomposition, not `cover`.
- `[LJ-1.462]` is NO-GO at D-10 step 3 for `levelIn`
  (`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). The statement
  is not named FALSE. This task does not inhabit `levelIn`. It
  does not take `levelIn` as a hypothesis.
- `[LJ-1.472]` is GO on numerals in the hull
  (`agents/tasks/LJ-1-472/lj-1.472-report.md:151`). A numeral is
  not a general ordinal. C-42 forbids the transfer.
- `[LJ-1.474]` is GO on codes for the level formula's constants
  (`agents/tasks/LJ-1-474/lj-1.474-report.md:70`).
- `[LJ-1.160]` measured that the hull is not transitive
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`).

## VERDICT

**NO-GO at CoverWitnessesInHull, after W3 closed.** W3 is GO:
`wit` names an ordinal at `isOrdFo`. The covering formula
packages and feeds to `wit`. The obligation term is not written.
Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

This is an obstruction of two routes, not a refutation of the
type. I did not build a term of the negation. The NO-GO is
stated in
`agents/tasks/LJ-1-487/review-of-CoverWitnessesInHull.md`. That
file is the critic's input. It does not close the task.

## WHAT COVER STILL OWES

Restate of `[LJ-1.484]`'s four steps, this one marked. I do not
claim `cover`.

1. **code-of.** BUILT, by `[LJ-1.484]`. `hull-member` at
   `src/L/Hull.lagda.md:337-339`. Not re-ordered here.

2. **StageBoundOfCode.** UNBUILT. Wrong shape. Still wrong. A
   `Code` does not carry an ordinal
   (`src/L/Hull.lagda.md:72-74`). W3 shows `wit` can *name* an
   ordinal at a formula. That does not make step 2 the right
   shape. Step 2 still does not supply `CoverWitnessesInHull`.
   It does not now matter for this step: the covering index is
   not read off a `Code` constructor.

3. **ambient-cover / ambient-level.** BUILT, by `[LJ-1.484]`.
   The index is in `lam`, not in `M`. Still not `cover`. Not
   re-ordered here.

4. **CoverWitnessesInHull.** UNBUILT. This task. The type is at
   `Probe487.agda:163-166`. The formula is named (`coverIndex` at
   `:139-143`). Packaging and `feed-cover` typecheck (`:145-154`).
   Sat at the hull's `_⊨₀_` is unbuilt. No term of the type.

`cover` stays unbuilt. `levelIn` stays an unpaid sibling.

## W2 (DD4)

The mathematics is written once at a generic carrier. `isOrdFo`
is generic in `K` (`Probe487.agda:52-55`). Instantiation is at
`⊥*` for `wit` (`:79-80`) and at `CS.S` for `coverIndex`
(`:141`). The module is generic in `ℓ`. `lam`, `X` and the
limit hypotheses stay parameters. No ordinal is fixed. No second
copy at a concrete stage. The conflict the clause names did not
arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-487/Probe487.agda`, module
`LJ-1-487.Probe487 {ℓ} (lem)`.

- Telescope `HullStage` (`:61-64`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. Nothing below
  `module Condense` is copied. `M = H.T.Hull`. `levelIn` is not
  a parameter. `cover` is not a parameter.
- `isOrdFo`, generic in `K` (`:52-55`). Same spelling as
  `isOrdAt` at `src/L/BoundedSubset.lagda.md:795-798`, at
  `Formula (⊥* {ℓ})` not `Formula (⊥* {ℓ-suc ℓ})`.
- W3 inhabited: `ord-by-wit` (`:122-128`). `wit` at `φord = isOrdFo zero`.
  `isOrdFo-out` (`:102-117`) reads the ordinal formula back to
  `IsOrd`. The value is not identified with a numeral.
- Diagnostic: `coverIndex` (`:139-143`), `packagedCover`
  (`:145-146`), `feed-cover` (`:153-154`). Not the obligation.
- Obligation as type: `CoverWitnessesInHull` (`:163-166`).
  Unbuilt. No term of that type.

Measured non-blank non-comment lines: 93. Total lines: 167. The
brief estimate was about 160 lines, of which the obligation is
about 45. Nothing is funded against the estimate.

## STEP ONE, W3

**`wit` names an ordinal at the ordinal formula.** `ord-by-wit`
(`Probe487.agda:122-128`) is the brief's type, inhabited. The
obligation is omitted.

This is not `[LJ-1.472]`'s numeral measurement. The formula is
`isOrdFo`, the spelling of `isOrdAt` at
`src/L/BoundedSubset.lagda.md:795-798`, at `Formula (⊥* {ℓ})`.
`Sat` holds at the empty set (`:85-91`). `val-wit` opens the
search. `isOrdFo-out` reads `IsOrd` off the least witness. The
value is not identified with `∅` or with `numeralL 0`. C-42:
a numeral is not a general ordinal, and this run does not fund
against `[LJ-1.472]`.

Three forced rechecks of the W3-only file (`ord-by-wit` only,
obligation omitted), `_build` interface removed before each,
dependencies warm, caliber `-A64m -I0 -M8g`, one Agda process.
Exit 0 every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.49 | 477478912 |
| `runs/w3-2.out` / `w3-2.time` | 2.24 | 477478912 |
| `runs/w3-3.out` / `w3-3.time` | 3.78 | 396771328 |

Median wall **2.49 s**. Median peak RSS **477478912 bytes**. No heap
event. The first green W3-only check `runs/w3-0b.out` was 2.48 s and
477495296 bytes, also exit 0. It is not one of the three forced
rechecks. The brief estimate for W3 was about 12 lines and under
20 seconds. The measured median is under that estimate.

A general covering index cannot be named the same way. The same
way is `wit` at a closed formula with an empty parameter vector.
A covering index of an arbitrary `y` depends on `y` and on `Lset`.
Route 1 for the obligation is not closed by W3. It turns on the
level formula in the hull language, which is the packaging and
Sat gap below.

## STEP TWO, THE OBLIGATION

Omitted as a term. `CoverWitnessesInHull` is a `Type` at
`Probe487.agda:163-166`. Route 1 named the covering formula and
did not discharge Sat. A truncated conclusion was not written
inside the existing truncation. `levelIn` was not added as a
hypothesis. `cover` was not added as a hypothesis.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency
warm, from the repository root. The probe interface was deleted
before every kept run.

- W3, three forced rechecks: see the table above. Median
  **2.49 s**, **477478912 bytes**. Exit 0.
- Full file, three forced rechecks. W3, the covering-formula
  diagnostics, and the D-10 type are in the file. The obligation
  is omitted as a term.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 4.37 | 1105379328 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 4.39 | 1105379328 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 4.56 | 1085456384 |

Median wall **4.39 s**. Median peak RSS **1105379328 bytes**.
Exit 0 every time. Each printed `Checking`. No heap event.
The first green full check `runs/full-0.out` was 4.37 s and
1105362944 bytes, also exit 0. It is not one of the three forced
rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.80 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `CoverWitnessesInHull` is a `Type` inside `HullStage`. That is
  the intended NO-GO reading. The worktree has no `.venv`. The
  meter ran under `/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

## 3. What NO-GO earns, and what is still owed

NO-GO names which route is nearer and what it lacks. Route 1 is
nearer. It lacks Sat of `packagedCover` at the hull's `_⊨₀_`,
and a filled `Vec Code (countFo coverIndex)`. If it names
elementarity as absent, that is the first measurement of what
the condensation front owes beyond definability: the tree has
`Elementary` under canonical codes at a concrete `X`
(`src/L/BoundedSubset.lagda.md:1543-1545`), and it does not have
`M ≺_{Σ₁} L_lam` at `Formula CS.S` at the generic `HullStage`
telescope.

What this task does not settle:

- It does not inhabit `CoverWitnessesInHull`.
- It does not inhabit `cover`.
- It does not inhabit `levelIn`.
- It does not refute `CoverWitnessesInHull`.
- It does not fill `Vec Code (countFo coverIndex)`.
- It does not re-measure `[LJ-1.474]` at `coverIndex`. C-42.
- It does not edit `src/`.

## 4. What the next brief needs

- Do not order `ord-by-wit` again. `wit` names an ordinal at
  `isOrdFo`. A numeral is a different formula.
- Do not order `code-of` or `ambient-cover` again. `[LJ-1.484]`
  built them.
- Do not order a stage bound read off a `Code`. Step 2 is still
  the wrong shape and does not now matter for this step.
- The unpaid object is still `CoverWitnessesInHull`. A brief that
  sends `coverIndex` through `wit` must fund Sat at the stage
  `AbsL.𝒮M`, not at `𝒮ʟ`. `[LJ-1.462]` measured the formula-type
  meeting. This task measured that packaging of the covering
  formula typechecks and that Sat is the remaining gap of route 1.
- A brief that fills `Vec Code (countFo coverIndex)` must
  re-measure `[LJ-1.474]` at this formula. C-42.
- A brief that takes the elementarity route must inhabit
  `M ≺_{Σ₁} L_lam` at `Formula CS.S` (or `coverIndex`) at this
  telescope. `HullElemDown.WithCode.elem` at
  `src/L/BoundedSubset.lagda.md:759-760` is not that fact.
- Do not take `levelIn` as a hypothesis of a `cover` probe.
- What the statement cost: 93 non-blank non-comment lines, W3
  median 2.49 s, full median 4.39 s, peak RSS 1105379328 bytes
  on the kept rechecks. What the shape resisted: Sat of the
  packaged covering formula at the stage. What I had to weaken:
  nothing of the obligation. What I could not close:
  `CoverWitnessesInHull`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4. W4
  did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:107`. Quote:
  `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the`.
  Also read at `:108`. Quote:
  `statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally`.
  Used: `CoverWitnessesInHull` is that reverse-inclusion transfer
  of the covering witnesses into the hull. Φ is the LST analogue.
  The orthodox argument uses Σ₁-elementarity of X in L_α. The tree
  does not have that at this telescope, at this language. Devlin
  does not commute the collapse with the stage operation.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is `wit` at an ordinal formula. It is not
  a truncation question. The conclusion of the obligation is already
  truncated once.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `CoverWitnessesInHull` or `cover`.
- I did not take `levelIn` as a hypothesis.
- I did not postulate. I did not weaken `γ ∈ M`.
- I did not import a probe.
- I did not identify the W3 ordinal with a numeral.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-487/`:

- `lj-1.487-report.md`, this report
- `Probe487.agda`, W3 and the covering-formula diagnostics
- `review-of-CoverWitnessesInHull.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
