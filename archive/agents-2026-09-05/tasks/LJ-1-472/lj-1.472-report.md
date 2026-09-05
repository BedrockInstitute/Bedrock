# LJ-1.472 report: the condensation hull holds the numerals

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-472/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-472/Probe472.agda`:

    numerals-in-hull :
        (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ H.T.Hull ⟩

where `H` is the hull `src/L/BoundedSubset.lagda.md:903-914` builds.
Land nothing in `src/`.

The standing direction (`dev/pod/direction.md:38`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## PREDECESSOR, READ FIRST

`[LJ-1.466]` is a stated NO-GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-466/lj-1.466-report.md:60`. Quote at `:62-66`:

> **NO-GO.** `how-many` is not zero. It is not a closed integer. Every
> visible constant is `numeralL k` for `k ∈ {0,1,...,11}`. None of those
> sets lies in a general hull carrier `⟪ X ⟫`. Mapping `base` over
> `constantsFo LsetGraph` does not typecheck. I did not inhabit
> `lset-codes`.

The brief named that report a critic-upheld NO-GO. The critic file
does not uphold it. Quote at
`agents/tasks/LJ-1-466/review-of-LJ-1-466-1.md:6`:

> verdict: overturned

The critic leaves the census and the `base` obstruction, and names the
price this task measures. Quote at `:241-243`:

> After this review the widest unmeasured term is the PRICE of the `wit`
> route: twelve codes `c` built by `wit`, each with a proof that its value is
> the numeral, inside the consumer telescope.

The 466 report is a stated NO-GO, so I did not stop. The named type of
this brief is new. It is not `lset-codes`. I did not inhabit that
NO-GO type.

### Condition table, quoted from `[LJ-1.466]`

From `agents/tasks/LJ-1-466/lj-1.466-report.md:76-102`, heading
`## WHAT THE HULL MUST CONTAIN`:

> Every constant of `LsetGraph` that Agda printed, and every constant the
> source cone names, is `con (numeralL k)` for a tag `k`. There is no
> `ωʟ`. There is no stage. There is no member of a general `X`.

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

Read as a condition on `X` for the `base` route, the table stands. The
critic says so at `review-of-LJ-1-466-1.md:220-221`. This task does not
use `base`.

## D-10, BEFORE ANY AGDA

Two routes. I weighed both before a term.

### Route 1, by closure

The hull is closed under definable existence at `src/L/Hull.lagda.md:120-123`
(`closed`) and at `:74` (`wit`). A numeral is definable without parameters.

Does the formula exist in the live tree as a named term? **No.**
`[LJ-1.466]` found the constants and not a formula that defines one.
Search over live `src/` for `numeralFo` returns no hit. Search for
`succFo` in live `src/` returns no hit.

The constructors exist. `FOL.Syntax` has `∀̇∈`, `∃̇∈`, `⊥̇`, `_∈̇_`, `_≐_`,
`_∧̇_` and `_∨̇_` (`src/FOL/Syntax.lagda.md:94-100`). The parameter-free
formula that names the empty set is `∀̇∈ (var zero) ⊥̇`. That is the
archived `numeralFo zero` at
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:372`. The successor
step is there too (`succFo` at `:367-368`, `numeralFo (suc n)` at `:373`).
A probe may write them. Live `src/` does not.

### Route 2, by the carrier

`base` needs a member of `X` (`src/L/Hull.lagda.md:73`, instantiated at
`:323` with `K = ⟪ X ⟫`). `X⊆M` then puts that member in the hull
(`src/L/Hull.lagda.md:354-355`).

What `UK.X` contains. `UnionKit` at
`src/L/BoundedSubset.lagda.md:1149-1150`:

    X : S
    X = Lset α ∪ ⁅ x ⁆s

So `UK.X` holds every member of `Lset α` and the singleton `{x}`.
`Lα∈X` at `:1161-1165` is the left inclusion. The consumer
`BoundedSubsetAt` instantiates `HullStage` at `UK.X`
(`src/L/BoundedSubset.lagda.md:1404-1405`).

The numerals lie in the **stage** `Lset lam`, not in a general `X`.
`num∈λ` at `src/L/Coding/Bound.lagda.md:139-140` says
`⟨ fst (numeralL k) ∈ˢ Lset lam ⟩`. `∅∈λ` at
`src/L/BoundedSubset.lagda.md:905` puts `∅` in the ordinal, not in `X`.
That is the same observation `[LJ-1.466]` recorded at
`lj-1.466-report.md:113-114`.

At the consumer, `α` is not finite (`α∉ω` at `:1387`). `one∈α` at
`:1205-1210` already puts `1` in `α`. The same trichotomy with `#∈ω k`
would put `# k` in `α`, hence in `Lset α` by the `#∈Tλ` pattern at
`src/L/Coding/Bound.lagda.md:55-61`, hence in `UK.X` by `Lα∈X`. **That
is a condition on the consumer, not a fact about HullStage's general
`X`.** The brief forbids a hypothesis that places a numeral in the hull
by fiat. I did not add it.

### Which route I took

**Route 1, by closure**, at HullStage's general `X`. Route 2 does not
close at that telescope. Route 2 is nearer at the consumer `UK.X` only
after a lemma `# k ∈ Lset α` that this brief does not order.

W3 is `k = 0` alone. The empty-set formula exists as constructors. It
typechecked. The other eleven are the archived `numeralFo` plus
uniqueness, written in the probe. That is the price the critic named.

## WHAT THIS DECIDES

A GO reopens `[LJ-1.466]`'s obligation: the extra `Vec Code` can be
filled by `wit` at `numeralFo`, and the hull route to `levelIn` stays
open. A NO-GO would close that hull route to `levelIn`, and the campaign
would stop paying for it after `[LJ-1.451]`, `[LJ-1.462]` and
`[LJ-1.466]`.

This return is a GO. The hull over a general `X` holds every numeral.

## VERDICT

**GO.** `zero-in-hull` typechecks. `numerals-in-hull` typechecks. The
witness meter reads `0 UNRESOLVED of 1`, `probe_red=False`
(`runs/witness.out:1-2`). I did not add a hypothesis on `X`. I did not
postulate. I did not inhabit `levelIn` or `lset-codes`.

The term lives inside `HullStage` at `Probe472.agda`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. A top-level alias
`numerals-in-hull = HullStage.numerals-in-hull` is there because the
meter reads `Target.numerals-in-hull` (`scripts/pod/witness.py:278`) and
a named parameterised module does not lift the name.

## W2 (DD4)

The mathematics is written once at a generic carrier. `succFo` and
`numeralFo` are generic in `K` (`Probe472.agda`, above `HullStage`).
The module is generic in `ℓ`. `lam`, `X` and the limit hypotheses stay
parameters. Instantiation is at `⊥*` for `wit`. No ordinal is fixed. No
second copy at a concrete stage. The conflict the clause names did not
arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-472/Probe472.agda`, module
`LJ-1-472.Probe472 {ℓ} (lem)`.

- Telescope `HullStage`, copied from
  `src/L/BoundedSubset.lagda.md:903-914`.
- W3: `zero-in-hull` at `k = 0`, `wit` at `∀̇∈ (var zero) ⊥̇`.
- `succFo` and `numeralFo`, generic in `K`, copied from
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373`.
- `nL k` uses `Bd.num∈λ` (`src/L/Coding/Bound.lagda.md:139-140`) so the
  numeral is a stage member. No `ω ∈ Lset α` hypothesis.
- `succ-sat`, `succ-sat-bwd`, `numeral-sat`, `numeral-unique`.
- Obligation: `numerals-in-hull`, `wit` at `numeralFo k`, identified by
  `val-wit` and `numeral-unique`.
- Top-level alias for the witness meter.

Measured non-blank non-comment lines: 165. Total lines: 229. The brief
estimate was about 120 lines, of which the obligation is about 20.
Nothing is funded against the estimate.

## STEP ONE, W3

**`k = 0` sits in the hull, by route 1.** `wit` at `∀̇∈ (var zero) ⊥̇`.
`val-wit` opens the search. Extensionality of the empty set identifies
the value with `fst (numeralL 0)`.

Three forced rechecks of the W3-only file (`zero-in-hull` only, obligation
omitted), `_build` interface removed before each, dependencies warm,
caliber `-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each
printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.99 | 475168768 |
| `runs/w3-2.out` / `w3-2.time` | 1.98 | 475152384 |
| `runs/w3-3.out` / `w3-3.time` | 1.99 | 475136000 |

Median wall **1.99 s**. Median peak RSS **475152384 bytes**. No heap
event. The first green W3-only check `runs/w3-0d.out` was 1.99 s and
475152384 bytes, also exit 0. It is not one of the three forced
rechecks.

The other eleven are priced by the same route: `numeralFo` plus
uniqueness, written in the probe. That is what the full file measures.

## STEP TWO, THE OBLIGATION

Inhabited. Route 1. No extra hypothesis on `X`. `numeralFo k` is the
formula. `wit 0 (φk k) []` is the code. `numeral-unique` identifies
`fst (val (ck k))` with `fst (numeralL k)`.

The critic of `[LJ-1.466]` measured that a hollow `wit` at
`var zero ≐ var zero` inhabits `Vec Code` (`review-of-LJ-1-466-1.md:69-75`).
This term is not that. `Sat` holds. The value is the numeral.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.99 s**,
  **475152384 bytes**. Exit 0.
- Full file, three forced rechecks. The obligation and the alias are
  in the file.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.29 | 509919232 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.35 | 509902848 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.32 | 509853696 |

Median wall **2.32 s**. Median peak RSS **509902848 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the alias, `runs/full-alias.out` / `full-alias.time`, was
2.36 s and 509902848 bytes, also exit 0. It is not one of the three
forced rechecks.

- Witness meter, one obligation: 0 UNRESOLVED of 1, 2.04 s,
  `probe_red=False` (`runs/witness.out:1-2`). Exit 0.

## 3. What GO earns, and what is still owed

GO reopens `[LJ-1.466]`'s `lset-codes`. Each constant `numeralL k` now
has a `Code` whose value is that numeral, at a general `X`. Mapping
those codes along `constantsFo LsetGraph` is the next term. I did not
build it. The length is still not a closed integer.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `lset-codes`.
- It does not inhabit `lset-code` or `levelIn`.
- It does not refute `levelIn`.
- It does not restrict `X` in the consumer telescope.
- It does not unfold `satGraphAt`.
- It does not produce a closed integer for `countFo LsetGraph`.
- It does not edit `src/`.
- It does not pay `cover`.
- It does not land `numeralFo` in `src/`. The formula lives in the probe.

C-42: this is not a refutation. I did not search the tree for a false
shape.

## 4. What the next brief needs

- `numerals-in-hull` is delivered at a general `X`, by `wit` at
  `numeralFo`. Site: `agents/tasks/LJ-1-472/Probe472.agda`.
- Do not order a hypothesis `⟨ fst (numeralL k) ∈ˢ X ⟩`. The hull
  already holds the numeral.
- `[LJ-1.466]`'s `lset-codes : Vec Code (countFo LsetGraph)` is the
  natural next term. `constantsFo LsetGraph` is still `Vec CS.S`. Each
  entry is some `numeralL k`. The code for that `k` is `ck k` in this
  probe, or `wit 0 (numeralFo k zero) []` with the uniqueness proof.
- `countFo LsetGraph` is still not a closed literal. Do not fund a
  later task against an exact length.
- `[LJ-1.462]`'s `feed` still typechecks and still needs the `Vec Code`.
- What the statement cost: 165 non-blank non-comment lines, W3 median
  1.99 s, full median 2.32 s, peak RSS 509919232 bytes on the kept
  rechecks. What the shape resisted: nothing of the obligation. The
  formula was not in live `src/`; the probe wrote it. What I had to
  weaken: nothing. What I could not close: `lset-codes`, `levelIn`,
  `cover`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live hull.
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

The formula I wrote is not in those candidates. It is at
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373`.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ is a parameter-free definition of a constructible object.
  The tree's `numeralFo` is the same shape for a numeral. Devlin's Φ
  is a formula of LST. The membership measured here is a fact about
  this tree's hull.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. The search is `leastOf` already in the hull.
  No truncation question is at issue.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. The formula was taken from the archived live
  chapter, not from the rud-route digest.
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
- I did not postulate. I did not add a hypothesis placing a numeral
  in `X`.
- I did not unfold `satGraphAt`.
- I did not pay `cover`.
- I did not write `review-of-numerals-in-hull.md`. The term inhabits.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-472/`:

- `lj-1.472-report.md`, this report
- `Probe472.agda`, W3, `numeralFo`, the telescope and `numerals-in-hull`
- `runs/`, the Agda transcripts named above
