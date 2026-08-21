# LJ-1.466 report: the constants the hull cannot yet name

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-466/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-466/Probe466.agda`:

    lset-codes : Vec Code (countFo LsetGraph)

Land nothing in `src/`.

## PREDECESSOR, READ FIRST

`[LJ-1.462]` is a stated NO-GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-462/lj-1.462-report.md:75`. Quote at `:77-79`:

> **NO-GO at D-10 step 3, and it is not `[LJ-1.451]`'s absence.** The
> formula is delivered. The two formula types do not meet. Packaging is
> `absFo`, not a `subst`. `feed` typechecks with an extra `Vec Code`.

The critic upheld that NO-GO
(`agents/tasks/LJ-1-462/review-of-LJ-1-462-1.md:6`, `verdict: upheld`).

The `feed` line, at `agents/tasks/LJ-1-462/Probe462.agda:101-102`:

    feed : (c : Code) (cs : Vec Code (countFo LsetGraph)) → Code
    feed c cs = wit (suc (countFo LsetGraph)) packaged (c ∷ cs)

Packaging is present: `packaged = absFo {ℓz = ℓ} LsetGraph` at
`Probe462.agda:66-67`. The packaging the hull itself uses is `absFo` at
`src/L/Hull.lagda.md:126`. I did not stop. I did not inhabit `levelIn`
or `lset-code`. Those are the NO-GO types. This task names a new term.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`base : K → Code` at `src/L/Hull.lagda.md:73`. The hull instantiates
`K = ⟪ X ⟫` at `src/L/Hull.lagda.md:323`. So a constant of `LsetGraph`
gets a hull code by `base` only if it is a member of `X`.

`constantsFo` returns `Vec K (countFo φ)` at the formula's own parameter
type (`src/FOL/Manipulation/Parameters.lagda.md:105`). For `LsetGraph`
that `K` is the class carrier `S` of `𝒮ʟ`, not `⟪ X ⟫`.

A general `X` in the consumer telescope
(`src/L/BoundedSubset.lagda.md:903-905`) is any subset of `Lset lam`.
Nothing in that telescope puts a numeral of `L` into `X`.

If `countFo LsetGraph` is zero, the vector is `[]` and the obligation
closes. If it is not zero, each constant must be named, and for each
the condition on `X` must be stated. I do not add that condition as a
hypothesis. I do not postulate.

## VERDICT

**NO-GO.** `how-many` is not zero. It is not a closed integer. Every
visible constant is `numeralL k` for `k ∈ {0,1,...,11}`. None of those
sets lies in a general hull carrier `⟪ X ⟫`. Mapping `base` over
`constantsFo LsetGraph` does not typecheck. I did not inhabit
`lset-codes`. Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

The NO-GO is stated in `agents/tasks/LJ-1-466/review-of-lset-codes.md`.
That file is the critic's input. It does not close the task.

This is an obstruction of the hull-language route at the extra `Vec Code`
that `[LJ-1.462]` named. It is not a refutation of `levelIn`. I did not
build a term of the negation.

## WHAT THE HULL MUST CONTAIN

Every constant of `LsetGraph` that Agda printed, and every constant the
source cone names, is `con (numeralL k)` for a tag `k`. There is no
`ωʟ`. There is no stage. There is no member of a general `X`.

`numeralL : ℕ → S` at `src/L/Axioms/Numerals.lagda.md:175-177`.
`numeralL-fst` at `:179` says `fst (numeralL n) ≡ # n`.
`base` needs a member of `X` (`src/L/Hull.lagda.md:73,323`).

The condition on `X`, one row per value. Occurrences repeat. The
condition does not.

| k | constant | a site that names it | condition on `X` |
|---|---|---|---|
| 0 | `numeralL 0` = `∅ʟ` | `tagAtL` at `src/L/Coding/Model.lagda.md:586` with `k = 0`; `envOneAt` at `src/L/Coding/Powerset.lagda.md:129`; `zeroPay` at `src/L/Coding/Shape.lagda.md:179`; `isTmAt` at `:141`; `memClauseAt` at `src/L/Coding/Model.lagda.md:1788` | `⟨ fst (numeralL 0) ∈ˢ X ⟩`, i.e. `⟨ ∅ ∈ˢ X ⟩` |
| 1 | `numeralL 1` | `isCodeAt` via `keyArityAtL c 1` at `src/L/Coding/Powerset.lagda.md:298`; `isTmAt` at `src/L/Coding/Shape.lagda.md:142`; `eqClauseAt` at `src/L/Coding/Model.lagda.md:1791` | `⟨ fst (numeralL 1) ∈ˢ X ⟩` |
| 2 | `numeralL 2` | `andClauseAt` at `src/L/Coding/Model.lagda.md:1118`; `shapedAt` `binForm 2` at `src/L/Coding/Shape.lagda.md:184`; `andClosedAt` at `src/L/Coding/Model.lagda.md:2182` | `⟨ fst (numeralL 2) ∈ˢ X ⟩` |
| 3 | `numeralL 3` | `orClauseAt` at `src/L/Coding/Model.lagda.md:1121`; `binForm 3` at `src/L/Coding/Shape.lagda.md:184`; `orClosedAt` at `src/L/Coding/Model.lagda.md:2183` | `⟨ fst (numeralL 3) ∈ˢ X ⟩` |
| 4 | `numeralL 4` | `impClauseAt` at `src/L/Coding/Model.lagda.md:1276`; `binForm 4` at `src/L/Coding/Shape.lagda.md:184`; `impClosedAt` at `src/L/Coding/Model.lagda.md:2184` | `⟨ fst (numeralL 4) ∈ˢ X ⟩` |
| 5 | `numeralL 5` | `negClauseAt` at `src/L/Coding/Model.lagda.md:1172`; `unForm 5` at `src/L/Coding/Shape.lagda.md:185`; `negClosedAt` at `src/L/Coding/Model.lagda.md:2185` | `⟨ fst (numeralL 5) ∈ˢ X ⟩` |
| 6 | `numeralL 6` | `topClauseAt` at `src/L/Coding/Model.lagda.md:1279`; `unForm 6` at `src/L/Coding/Shape.lagda.md:185` | `⟨ fst (numeralL 6) ∈ˢ X ⟩` |
| 7 | `numeralL 7` | `botClauseAt` at `src/L/Coding/Model.lagda.md:1282`; `unForm 7` at `src/L/Coding/Shape.lagda.md:185` | `⟨ fst (numeralL 7) ∈ˢ X ⟩` |
| 8 | `numeralL 8` | `existClauseAt` at `src/L/Coding/Model.lagda.md:1615`; `unForm 8` at `src/L/Coding/Shape.lagda.md:186`; `existClosedAt` at `src/L/Coding/Model.lagda.md:2186` | `⟨ fst (numeralL 8) ∈ˢ X ⟩` |
| 9 | `numeralL 9` | `forallClauseAt` at `src/L/Coding/Model.lagda.md:1618`; `unForm 9` at `src/L/Coding/Shape.lagda.md:186`; `forallClosedAt` at `src/L/Coding/Model.lagda.md:2187` | `⟨ fst (numeralL 9) ∈ˢ X ⟩` |
| 10 | `numeralL 10` | `allInClauseAt` at `src/L/Coding/Model.lagda.md:1947`; `binForm 10` at `src/L/Coding/Shape.lagda.md:187`; `allInClosedAt` at `src/L/Coding/Model.lagda.md:2188` | `⟨ fst (numeralL 10) ∈ˢ X ⟩` |
| 11 | `numeralL 11` | `exInClauseAt` at `src/L/Coding/Model.lagda.md:1950`; `binForm 11` at `src/L/Coding/Shape.lagda.md:187`; `exInClosedAt` at `src/L/Coding/Model.lagda.md:2189` | `⟨ fst (numeralL 11) ∈ˢ X ⟩` |

Equivalently, by `numeralL-fst`, `X` must contain `# k` for each
`k = 0,1,...,11`.

`shapedAt` at `src/L/Coding/Shape.lagda.md:183-188` already names all
twelve tags. `hasWitnessAt` uses `shapedAt`
(`src/L/Coding/CodeSet.lagda.md:241-242`). `isCodeAt` uses
`hasWitnessAt` (`src/L/Coding/Powerset.lagda.md:298`). So the twelve
numerals are required even if `satGraphAt` stays opaque.

The consumer telescope does not put any of them in `X`. `∅∈λ` at
`src/L/BoundedSubset.lagda.md:905` puts `∅` in the ordinal, not in `X`.

## 1. What was built

All in `agents/tasks/LJ-1-466/Probe466.agda`, module
`LJ-1-466.Probe466 {ℓ} (lem)`.

- W3: `how-many = countFo LsetGraph` (`:47-48`).
- Packaging copied from `[LJ-1.462]`: `packaged = absFo {ℓz = ℓ} LsetGraph`
  (`:51-52`).
- `consts = constantsFo LsetGraph` (`:55-56`). Type `Vec CS.S (countFo LsetGraph)`.
  This is the vector the brief asked me to write down. It is not `Vec Code`.
- Telescope `HullStage` (`:61-71`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. `M = H.T.Hull`.
  `module C = Collapse M`.
- `feed` rebuilt (`:81-82`), same term as `Probe462.agda:101-102`.
- No term named `lset-codes`. No term named `levelIn`. No term named
  `lset-code`.

Measured non-blank non-comment lines: 39. Total lines: 86. The brief
estimate was about 120 lines, of which the obligation is about 20.
Nothing is funded against the estimate.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `lam`, `X` and the limit hypotheses stay parameters.
No ordinal is fixed. No second copy at a concrete stage. The conflict
the clause names (a deadline that forces a fixed form) did not arise.

The census is also generic: the constants are numerals of `L`, not
values of a fixed stage.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## STEP ONE, W3

**The length is not zero, and it is not a closed natural number.**

Three forced rechecks of the W3-only file (`how-many` only), `_build`
interface removed before each, dependencies warm, caliber
`-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each printed
`Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.95 | 393428992 |
| `runs/w3-2.out` / `w3-2.time` | 1.68 | 393428992 |
| `runs/w3-3.out` / `w3-3.time` | 1.51 | 393428992 |

Median wall **1.68 s**. Median peak RSS **393428992 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 1.34 s and
393445376 bytes, also exit 0, also printed `Checking`. It is not one
of the three forced rechecks.

Force against zero, one run, obligation omitted, then the equality
removed. `runs/w3-force.out` / `w3-force.time`. Exit 42.
`[UnequalTerms]` at `runs/w3-force.out:2`. Head constructor `suc` at
`:3`. Wall **2.73 s**. Peak RSS **679886848 bytes**. File size
1792264 bytes. Printed form still contains `countFo` of
`L.Coding.Graph.satGraphAt` (`runs/w3-force.out`, first `countFo`).
`satGraphAt` is opaque at `src/L/Coding/Graph.lagda.md:203-205`.
**I report no exact integer.** The brief asked for the number. The
number Agda will print is not a closed literal.

What the force did print, counted from `runs/w3-force.out`:

- 35 leading `suc` before the first stuck `countFo`. That block is one
  fully reduced `isCodeAt` (35 constants: 1 from `keyArityAtL c 1`,
  34 from `hasWitnessAt` = 8 `closedAt` tags + 26 `shapedAt` tags).
- 6 remaining `countFo` summands. One of them is opaque `satGraphAt`.
- 105 `FOL.Syntax.Term.con` in those unevaluated arguments. All 105
  are `numeralL k` for `k ∈ {0,1,...,11}`. Histogram of those 105:
  0:27, 1:24, 2:6, 3:6, 4:6, 5:6, 6:3, 7:3, 8:6, 9:6, 10:6, 11:6.

The task is a census of constants, as the brief said it would be if
the length was large.

## STEP TWO, THE OBLIGATION

Omitted. W3 is not zero. The constants are not in a general `X`. The
brief forbids a hypothesis that places a constant in `X` by fiat.
`lset-codes` is not written.

`consts` (`Probe466.agda:55-56`) is the class-carrier vector. `feed`
(`:81-82`) still waits for `Vec Code`. Those two types do not meet.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.68 s**,
  **393428992 bytes**. Exit 0.
- Force against zero: **2.73 s**, **679886848 bytes**. Exit 42.
  `[UnequalTerms]`.
- Full file, three forced rechecks. The telescope, `consts` and `feed`
  are in the file. The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 5.42 | 1223344128 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 5.44 | 1245380608 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 5.98 | 1135149056 |

Median wall **5.44 s**. Median peak RSS **1223344128 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the telescope was added, `runs/full-0.out`, was 5.67 s
and 1172946944 bytes, also exit 0. It is not one of the three forced
rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.83 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `lset-codes` is
  not in scope. That is the intended NO-GO reading.

## 3. What NO-GO earns, and what is still owed

NO-GO names the condition on the hull. The condensation front that
builds a hull over `X` must put the twelve numerals `# 0` through
`# 11` into `X`, or it must code those numerals by `wit`, or it must
replace `LsetGraph` by a formula that does not name them.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `lset-codes`.
- It does not inhabit `lset-code` or `levelIn`.
- It does not refute `levelIn`.
- It does not restrict `X` in the consumer telescope.
- It does not code a numeral by `wit`.
- It does not unfold `satGraphAt`.
- It does not produce a closed integer for `countFo LsetGraph`.
- It does not edit `src/`.
- It does not pay `cover`.

C-42: this is not a refutation. The named type is well-formed. The
inhabitation fails at a general `X`. I did not search the tree for a
false shape.

## 4. What the next brief needs

- Do not order `lset-codes : Vec Code (countFo LsetGraph)` at a
  general `X`. `base` cannot see the constants.
- The constants are `numeralL 0` through `numeralL 11`. The condition
  is `⟨ fst (numeralL k) ∈ˢ X ⟩` for each of those twelve, equivalently
  `⟨ # k ∈ˢ X ⟩`.
- `countFo LsetGraph` is not zero and is not a closed literal.
  `satGraphAt` is opaque. Do not fund a later task against an exact
  length that this run did not print.
- `constantsFo LsetGraph` is `Vec CS.S (countFo LsetGraph)` and is
  inhabited here as `consts` (`Probe466.agda:55-56`).
- `[LJ-1.462]`'s `feed` still typechecks and still needs the `Vec Code`.
- A later brief that restricts `X` to contain the twelve numerals may
  map `base` over a membership witness. A later brief that codes the
  numerals by `wit` from the empty set does a different construction.
  This brief forbade both.
- What the statement cost: 39 non-blank non-comment lines, W3 median
  1.68 s, full median 5.44 s, peak RSS 1245380608 bytes on the kept
  rechecks. What the shape resisted: `base` takes `⟪ X ⟫`, the
  constants are class-carrier numerals, a general `X` does not hold
  them. What I had to weaken: nothing of the obligation. I did not
  add a hypothesis. What I could not close: `lset-codes`, and a closed
  integer for `how-many`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live formula.
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
  Used: Φ is the LST analogue of the class-carrier graph. The tree's
  analogue `LsetGraph` names tag numerals as constants. Devlin's Φ is
  a formula of LST. The hull condition measured here is a fact about
  this tree's coding, not about Φ as LST.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a count of constants. It is not a
  truncation question.
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
- I did not inhabit `lset-codes`, `lset-code` or `levelIn`.
- I did not add a `Code` constructor.
- I did not postulate. I did not add a hypothesis placing a constant
  in `X`.
- I did not unfold `satGraphAt`.
- I did not pay `cover`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-466/`:

- `lj-1.466-report.md`, this report
- `Probe466.agda`, W3, `consts`, the telescope and `feed`
- `review-of-lset-codes.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
