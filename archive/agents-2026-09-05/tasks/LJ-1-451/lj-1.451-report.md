# LJ-1.451 report: the cheaper of the two condensation hypotheses

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-451/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-451/Probe451.agda`:

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

W3 first, the type the brief names:

    lset-code : (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

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

If step 3 has no formula, the task is a NO-GO and the formula is what
the next brief must order.

## PREDECESSOR TYPES

- `[LJ-1.121]` did not refute `levelIn` and did not supply it
  (`agents/tasks/LJ-1-121/lj-1.121-report.md:7-8`: "Neither is
  refutable. Neither is supplied."). The statement is not named FALSE.
  This task does not inhabit that probe's `Supply` parameters.
- `[LJ-1.160]` did not discharge `levelIn`. It routed around the wall
  through unpaid `CrossOut` and `HasLevels`
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:11-12`: "The substrate does
  not discharge `levelIn` or `cover`."). The statement is not named
  FALSE. The delivered type in that probe is
  `agents/tasks/LJ-1-160/ProbeLJ1160A.agda:83-88`, built from those two
  unpaid hypotheses. This task does not inhabit them. The brief forbids
  a postulate.

## VERDICT

**NO-GO at D-10 step 3.** The W3 type is well-formed and unbuilt
(`agents/tasks/LJ-1-451/Probe451.agda:82-84`). `Code` has constructors
`base` and `wit` only (`src/L/Hull.lagda.md:72-74`). There is no
constructor that names `Lset`. The formula `closed` would consume is
not delivered (`src/L/Hull.lagda.md:120-123`). The obligation term
`levelIn` is not written. Witness meter: 1 UNRESOLVED of 1,
`probe_red=False` (`runs/witness.out:1-2`).

This is an obstruction of the hull-language route. It is not a
refutation of `levelIn`. I did not build a term of the negation.

The NO-GO is stated in `agents/tasks/LJ-1-451/review-of-levelIn.md`.
That file is the critic's input. It does not close the task.

## 1. What was built

All in `agents/tasks/LJ-1-451/Probe451.agda`, module
`LJ-1-451.Probe451 {ℓ} (lem)`.

- Telescope `HullStage` (`:43-55`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. The brief names `:898-916`.
  Line `:898` is comment. The module keyword is at `:903`. Line `:916`
  is `module Condense`, and it is not copied. `M = H.T.Hull`.
  `module C = Collapse M`.
- Step 1 inhabited: `step1 = C.πX-member` (`:69-70`).
- Step 2 as types: `HullClosedLset`, `πCommuteLset` (`:73-79`). Unbuilt.
- Step 3 as type: `LsetCode` (`:82-84`). Unbuilt. This is W3.
- Obligation as type: `LevelIn` (`:89-91`). Unbuilt. No term named
  `levelIn`.
- The missing formula as type: `MissingFormula` (`:97-100`). Unbuilt.

Measured non-blank non-comment lines: 51. Total lines: 100. The brief
estimate was about 140 lines, of which the obligation is about 30.
Nothing is funded against the estimate.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `lam`, `X` and the limit hypotheses stay parameters.
No ordinal is fixed. No second copy at a concrete stage. The conflict
the clause names (a deadline that forces a fixed form) did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## STEP ONE, W3

**The type is well-formed. The term is unbuilt.** `LsetCode`
(`Probe451.agda:82-84`) is the brief's `lset-code`, stated as a
`Type`. The obligation is omitted.

Three forced rechecks, interface removed before each, dependencies
warm, caliber `-A64m -I0 -M8g`, one Agda process. Exit 0 every time.
Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.91 | 477036544 |
| `runs/w3-2.out` / `w3-2.time` | 1.95 | 477020160 |
| `runs/w3-3.out` / `w3-3.time` | 2.06 | 477036544 |

Median wall **1.95 s**. Median peak RSS **477036544 bytes**. No heap
event. The brief estimate was under 5 seconds. The measured median is
under that estimate.

The W3 type itself is three lines. The telescope is required to form
`Code`. I did not add a constructor.

`Code` has two constructors at `src/L/Hull.lagda.md:72-74`: `base` and
`wit`. There is no third. I did not add one. `base` names seed
elements of `X` (`module T = TermAlgebra ... {K = ⟪ X ⟫} inStg` at
`src/L/Hull.lagda.md:323`). `Lset y` is not a seed in general. `wit`
needs a `Formula (⊥* {ℓ}) (suc k)`. No such formula for `Lset` is
delivered at `Formula Code` or at `Formula (⊥* {ℓ})`. That is why the
term is unbuilt.

The brief named `src/L/Hull.lagda.md:120-123` as the missing
constructor. That site is `closed`, a lemma. It consumes a
`Formula Code 1`. In live `src/`, `Formula Code` occurs at exactly
three sites: `src/L/Hull.lagda.md:94`, `:120` and `:415`. None names
`Lset`.

## STEP TWO, THE OBLIGATION

Omitted. Step 3 failed. The obligation is not inhabited. A truncated
conclusion was not written. `cover` was not added as a hypothesis.

## THE MISSING FORMULA

The next brief must order one formula. The probe names it:

    MissingFormula =
      Σ[ ψ ∈ Formula (⊥* {ℓ}) 2 ]
        ((c : Code) → fst (val (wit 1 ψ (c ∷ []))) ≡ Lset (fst (val c)))

at `Probe451.agda:97-100`. The other packaging is a `Formula Code 1`
for `closed` at `src/L/Hull.lagda.md:120-123`. `closed` already
abstracts that packaging: `ψ = absFo φ` at
`src/L/Hull.lagda.md:125-126`.

The graph of `Lset` exists at the class carrier: `LsetGraphAt` at
`src/L/Coding/Sequence.lagda.md:349`, and `LsetGraph : Formula S 2` at
`:353`. It is not the hull language. Devlin's Φ is the same object in
LST (`dev/literature/devlin-II5.md:95-96`). Transplanting that graph
is later work. This task does not transplant it.

The in-tree vehicles that move formulas between constant domains are
delivered:

    embed : ∀ {ℓ ℓ'} {K : Type ℓ'} {n} → Formula (⊥* {ℓ}) n → Formula K n

at `src/FOL/Manipulation/Relabelling.lagda.md:117`, and

    absFo : ∀ {ℓz ℓc} {K : Type ℓc} {n} (φ : Formula K n)
          → Formula (⊥* {ℓz}) (n + countFo φ)

at `src/FOL/Manipulation/Parameters.lagda.md:260`. `absFo LsetGraph`
adds `countFo LsetGraph` slots. Those slots are class-carrier
constants, not hull codes. `wit` needs a `Vec Code k` for them. That
is why the transplant is not this task's 20-line W3.

`Hull` exports `Code`, `base` and `closed`. The inner `open T using`
at `src/L/Hull.lagda.md:324` omits `wit`. That is not an access
barrier: `module T` at `:323` is not private, and this probe spends
`wit` through `open H.T using ( Code; val; base; wit )` at
`Probe451.agda:58`. The first packaging is reachable.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.95 s**,
  **477036544 bytes**. Exit 0.
- Full file, three forced rechecks. The full file is the W3 file. The
  obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.97 | 477020160 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.99 | 477036544 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.04 | 477036544 |

Median wall **1.99 s**. Median peak RSS **477036544 bytes**. Exit 0
every time. Each printed `Checking`. No heap event.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.13 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `levelIn` is
  not in scope. That is the intended NO-GO reading.

## 3. What NO-GO earns, and what is still owed

NO-GO names the missing formula. That is the first honest statement
of what this half of the condensation front costs on the hull-language
route. `cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `LsetCode`.
- It does not inhabit `MissingFormula`.
- It does not inhabit `levelIn`.
- It does not refute `levelIn`.
- It does not transplant `LsetGraphAt` into `Formula Code`.
- It does not pay `cover`.
- It does not edit `src/`.

C-42: this is not a refutation. The count of the unpaid shape in live
`src/` is 4 binders, 1 applied spend, 3 pass-down spends, 0 producers.
The table is in `review-of-levelIn.md`.

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

- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a constructor and formula question. It is
  not a truncation question.
- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: that Φ is the missing formula at LST. The tree's analogue at
  the class carrier is `LsetGraphAt`. The hull language does not have
  it. This is why step 3 fails.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not the site.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `LsetCode`, `MissingFormula` or `levelIn`.
- I did not add a `Code` constructor.
- I did not postulate. I did not weaken the conclusion.
- I did not pay `cover`.
