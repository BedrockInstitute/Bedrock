# LJ-1.462 report: levelIn again, with the formula the tree turned out to have

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-462/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-462/Probe462.agda`:

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

W3 first, the type the brief names:

    lset-code : (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## WHICH PREMISE MOVED

`[LJ-1.451]` measured the CONSTRUCTOR question. That measurement still
stands. `Code` has constructors `base` and `wit` only
(`src/L/Hull.lagda.md:72-74`). There is no constructor that names `Lset`.

`[LJ-1.458]` measured the FORMULA question at the class carrier. That
measurement is GO. The formula is `LsetGraphAt` at
`src/L/Coding/Sequence.lagda.md:349`. Its adequacy is `Lset-only` at
`src/L/Hierarchy.lagda.md:334-335`, with an extra `IsOrd`.

What moved is the formula question. The constructor question did not
move. `wit` takes a formula (`src/L/Hull.lagda.md:74`). The delivered
formula is not that formula's type.

## D-10, BEFORE ANY AGDA

The four steps, as types. Written here before any term.

1. Collapse membership, delivered.

       C.πX-member :
           (z : S) → ⟨ z ∈ˢ C.πX ⟩
         → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

   Site: `src/V/Collapse.lagda.md:78-79`.

2. The statement about the hull, two conjuncts.

       HullClosedLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

       πCommuteLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

3. Definability of `Lset` in the hull language. This is W3.

       LsetCode :
           (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

4. Absoluteness. Same type as `πCommuteLset`.

## PREDECESSOR TYPES

- `[LJ-1.451]` is NO-GO at D-10 step 3
  (`agents/tasks/LJ-1-451/lj-1.451-report.md:68`). The statement is not
  named FALSE. The W3 type is well-formed and unbuilt
  (`agents/tasks/LJ-1-451/Probe451.agda:82-84`). This task does not
  inhabit a NO-GO as if it were GO.
- `[LJ-1.458]` is GO for `LsetAt = LsetGraphAt`
  (`agents/tasks/LJ-1-458/lj-1.458-report.md:71-77`). That type is
  `Formula S n` at the class carrier. It is not `Formula (⊥* {ℓ}) (suc k)`.
  C-42 forbids the transfer.

## VERDICT

**NO-GO at D-10 step 3, and it is not `[LJ-1.451]`'s absence.** The
formula is delivered. The two formula types do not meet. Packaging is
`absFo`, not a `subst`. `feed` typechecks with an extra `Vec Code`.
The W3 type `lset-code` is well-formed and unbuilt
(`Probe462.agda:109-111`). The obligation term `levelIn` is not
written. Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

This is an obstruction of the hull-language route. It is not a
refutation of `levelIn`. I did not build a term of the negation.

The NO-GO is stated in `agents/tasks/LJ-1-462/review-of-levelIn.md`.
That file is the critic's input. It does not close the task.

## 1. What was built

All in `agents/tasks/LJ-1-462/Probe462.agda`, module
`LJ-1-462.Probe462 {ℓ} (lem)`.

- Telescope `HullStage` (`:78-90`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. The brief names `:898-916`.
  Line `:898` is comment. The module keyword is at `:903`. Line `:916`
  is `module Condense`, and it is not copied. `M = H.T.Hull`.
  `module C = Collapse M`.
- The two formula types, named. `graph = LsetGraph` (`:63-64`).
  `graphAt = LsetGraphAt {n = 2} zero (suc zero)` (`:71-72`).
  `packaged = absFo {ℓz = ℓ} LsetGraph` (`:66-67`).
- `feed` inhabited (`:101-102`): `wit` applied to `packaged` with one
  code for the argument and a `Vec Code (countFo LsetGraph)` for the
  constants. This is not `lset-code`.
- Step 1 inhabited: `step1 = C.πX-member` (`:133-134`).
- Step 2 as types: `HullClosedLset`, `πCommuteLset` (`:136-142`). Unbuilt.
- Step 3 as type: `lset-code` (`:109-111`). Unbuilt. This is W3.
- D-10 correction beside the original: `lset-code-ord` (`:118-121`).
  Adds `IsOrd`. Still unbuilt.
- Obligation as type: `LevelIn` (`:147-149`). Unbuilt. No term named
  `levelIn`.

Measured non-blank non-comment lines: 63. Total lines: 149. The brief
estimate was about 160 lines, of which the obligation is about 40.
Nothing is funded against the estimate.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `lam`, `X` and the limit hypotheses stay parameters.
No ordinal is fixed. No second copy at a concrete stage. The conflict
the clause names (a deadline that forces a fixed form) did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## STEP ONE, W3

**The two formula types do not meet.** `lset-code` (`Probe462.agda:109-111`)
is the brief's type, stated as a `Type`. Unbuilt. The obligation is
omitted.

`LsetGraphAt` is `Formula CS.S n` at `src/L/Coding/Sequence.lagda.md:349`,
with `CS.S` the carrier of `𝒮ʟ` (`src/L/Constructible.lagda.md:410-411`).
That type lives in `Type (ℓ-suc ℓ)`. `wit` takes `Formula (⊥* {ℓ}) (suc k)`
at `src/L/Hull.lagda.md:74`. That type lives in `Type ℓ`. A `subst` cannot
join them. I did not hide the gap in a `subst`.

The packaging is `absFo` at
`src/FOL/Manipulation/Parameters.lagda.md:260`:

    absFo : ∀ {ℓz ℓc} {K : Type ℓc} {n} (φ : Formula K n)
          → Formula (⊥* {ℓz}) (n + countFo φ)

`packaged = absFo {ℓz = ℓ} LsetGraph` is
`Formula (⊥* {ℓ}) (2 + countFo LsetGraph)` (`Probe462.agda:66-67`).
That type meets `wit`'s formula slot at
`k = suc (countFo LsetGraph)`.

`erase` at `src/FOL/Count.lagda.md:598` is not the packaging. `Count` is
parameterised by `K : Type ℓ` (`:222`). At `K = CS.S` that `ℓ` is
`ℓ-suc ℓ`, so `erase` would produce `Formula (⊥* {ℓ-suc ℓ}) n`, not
`Formula (⊥* {ℓ}) n`. `wit` would still refuse it.

`feed` (`Probe462.agda:101-102`) applies `wit` to `packaged`. It needs
a further `Vec Code (countFo LsetGraph)`. Those codes are not
delivered. `constantsFo LsetGraph` is `Vec CS.S`, not `Vec Code`.
The constants are class-carrier numerals: `tagAtL` names
`con (numeralL k)` at `src/L/Coding/Model.lagda.md:586`, and
`LsetGraphAt` reaches `tagAtL` through `StepAt`, `DefAt`, `isCodeAt`
and `keyArityAtL`. I did not normalise `countFo LsetGraph`. I did
not report a number I did not measure.

The hull carries no ordinality. `Lset-only` at
`src/L/Hierarchy.lagda.md:334-335` needs `IsOrd` on the argument
slot. That hypothesis does not arise on `Code`. `lset-code` has no
`IsOrd`. The consumer of `levelIn` does. The corrected type
`lset-code-ord` (`Probe462.agda:118-121`) records that. It is still
unbuilt: `feed` still needs the extra codes, and the equality still
needs `Lset-only`.

Three forced rechecks, `_build` interface removed before each,
dependencies warm, caliber `-A64m -I0 -M8g`, one Agda process. Exit 0
every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 4.74 | 1240236032 |
| `runs/w3-2.out` / `w3-2.time` | 4.71 | 1240268800 |
| `runs/w3-3.out` / `w3-3.time` | 4.70 | 1240268800 |

Median wall **4.71 s**. Median peak RSS **1240268800 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 4.53 s and
1047298048 bytes, also exit 0, also printed `Checking`. It is not
one of the three forced rechecks. The brief estimate for W3 was
about 25 lines and under 15 seconds. The measured median is under
that estimate.

`Code` still has two constructors at `src/L/Hull.lagda.md:72-74`:
`base` and `wit`. I did not add a third.

## STEP TWO, THE OBLIGATION

Omitted. Step 3 failed. The obligation is not inhabited. A truncated
conclusion was not written. `cover` was not added as a hypothesis.

Step 4 was not reached. After `[LJ-1.458]` this is not "the formula
is absent". The formula is present. The types do not meet. The
packaging meets `wit`'s formula slot and then dies on the extra
`Vec Code` and on `IsOrd`.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **4.71 s**,
  **1240268800 bytes**. Exit 0.
- Full file, three forced rechecks. The D-10 types are in the file.
  The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 4.73 | 1240236032 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 4.56 | 1241268224 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 4.51 | 1241300992 |

Median wall **4.56 s**. Median peak RSS **1241268224 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the D-10 types were added, `runs/full-0.out`, was 4.40 s
and 1240285184 bytes, also exit 0. It is not one of the three forced
rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 1.76 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `levelIn` is
  not in scope. That is the intended NO-GO reading.

## 3. What NO-GO earns, and what is still owed

NO-GO names which of the four steps fails. It is still step 3. It is
no longer step 3's absence. The formula `LsetGraphAt` is in the tree.
The types `Formula CS.S n` and `Formula (⊥* {ℓ}) (suc k)` do not meet
(`src/L/Coding/Sequence.lagda.md:349` against
`src/L/Hull.lagda.md:74`). `absFo` is the packaging
(`src/FOL/Manipulation/Parameters.lagda.md:260`). After packaging,
`wit` still needs a `Vec Code` for the class-carrier constants, and
the equality still needs `IsOrd`, which `Code` does not carry.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `lset-code`.
- It does not inhabit `lset-code-ord`.
- It does not inhabit `levelIn`.
- It does not refute `levelIn`.
- It does not produce hull codes for `constantsFo LsetGraph`.
- It does not pay `cover`.
- It does not edit `src/`.
- It does not reach step 4.

C-42: this is not a refutation. The count of the unpaid shape in live
`src/` is 4 binders, 1 applied spend, 3 pass-down spends, 0 producers.
The table is in `review-of-levelIn.md`. I re-counted. I did not copy
`[LJ-1.451]`'s line numbers.

## 4. What the next brief needs

- Do not order `LsetAt : Formula S n` again. It is `LsetGraphAt`.
- Do not send `levelIn` down the hull-language route with
  `LsetGraphAt` as a drop-in argument to `wit`. The types do not
  meet.
- The packaging that does meet `wit`'s formula slot is `absFo {ℓz = ℓ}`.
  After it, the next unpaid objects are: a `Vec Code` for the
  constants of `LsetGraph`, then the equality at `Lset-only`, which
  needs `IsOrd`.
- Do not assume `Lset-only` reads `wit`'s satisfaction. `Lset-only`
  is at the class carrier (`src/L/Hierarchy.lagda.md:73` opens
  `𝒮ʟ`). `wit` searches in `TermAlgebra` over the stage
  (`src/L/Hull.lagda.md:323`, `AbsL.𝒮M` from `:153`). That meeting
  is not measured here.
- `[LJ-1.451]`'s `MissingFormula` at `Formula (⊥* {ℓ}) 2` is still
  unbuilt. `absFo LsetGraph` has arity `2 + countFo LsetGraph`, not
  arity 2.
- `cover` still needs a producer.
- What the statement cost: 63 non-blank non-comment lines, W3 median
  4.71 s, full median 4.56 s, peak RSS 1241300992 bytes on the kept
  rechecks. What the shape resisted: the two formula types, then the
  extra `Vec Code`, then `IsOrd` on `Code`. What I had to weaken:
  nothing of the obligation. `feed` is a diagnostic with an extra
  hypothesis. What I could not close: `lset-code`, `lset-code-ord`,
  `levelIn`.

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
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ is the LST analogue of the class-carrier graph. `[LJ-1.458]`
  found that analogue as `LsetGraphAt`. This task measured that the
  hull-language types still do not meet it.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a meeting of two formula types. It is not
  a truncation question.
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
- I did not inhabit `lset-code`, `lset-code-ord` or `levelIn`.
- I did not add a `Code` constructor.
- I did not postulate. I did not weaken the conclusion.
- I did not pay `cover`.
- I did not hide the type gap in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-462/`:

- `lj-1.462-report.md`, this report
- `Probe462.agda`, W3 and the D-10 types
- `review-of-levelIn.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
