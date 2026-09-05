# LJ-1.247 report: row 4 (the column square) dissolves, and A5 re-derived

tier: pi (deepseek-subagent-mode). Probe task. No master edited. No commit,
no push. Written incrementally (C-22).

Every negative is marked **MEASURED** or **INFERRED**, in those words.

## 0. LEAD

**ROW 4 DISSOLVES. The column square needs no object of its own and no
L-internalization. It is 0 lines against the inferred 99.**

The column square is the successor step of the AMBIENT induction chain
(`pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))`), and that chain is
superseded. The delivered tree supplies the consumer's whole obligation with
`via-col-square` at `src/L/Ordinal/SquareLaw.lagda.md:960-961` (the order
route, direct, no successor step) plus the base at `ω` that `[LJ-1.234]`
closed in 60 lines. **The column square is in NO delivered `src/` file.**
MEASURED by grep, three patterns, zero hits.

**A5 = 348 lines. Every row is measured for the first time.**

| # | object | lines | class |
|---|---:|---:|---|
| — | `StageBound`, shared device | 16 | **MEASURED** |
| 1 | composition of two injections | 160 | **MEASURED**, `[LJ-1.152]` |
| 2 | the `CSB` bijection | 0 | **MEASURED**, `[LJ-1.156]` |
| 3 | the inclusion `j` | 112 | **MEASURED**, `[LJ-1.176]` |
| 4 | the column square `pair` | **0** | **DISSOLVED**, this task |
| 5 | `pairω` | 60 | **MEASURED**, `[LJ-1.234]` |
| | **A5** | **348** | |

**Arithmetic: 16 + 160 + 0 + 112 + 0 + 60 = 348.** The brief's own dissolve
arithmetic is the same number: 547 − 99 − 160 + 60 = 348.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

Copied from the brief and fixed before any probe code was written:

- **ROW 4 DISSOLVES.** Say so with the evidence. Then A5 is 547 − 99 − 160
  + 60 and every row is measured. STOP.
- **ROW 4 BUILDS.** Report its written lines against 99, and the seconds.
- **ROW 4 IS MATERIALLY OVER 99.** Report both figures.
- **THE PRODUCT ACTION NEEDS ITS OWN OBJECT.** Name it and price it.
- **A WALL.** One `agda` run past 20 minutes is a wall.

**VERDICT: ROW 4 DISSOLVES.** No other branch was reached. No `agda` run was
needed, because the dissolve branch is a structural finding and the brief
names no measurement for it.

## 2. THE DISSOLUTION QUESTION, ASKED AND ANSWERED

The question, in the brief's words: does anything demand the column square
as its own object, or does the delivered order route give it the way it gave
the base at `ω`?

**ANSWER: nothing demands it. The delivered order route gives it.**

The consumer's obligation is `sq δ` — the AMBIENT injection
`Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ] ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)`.
MEASURED at three delivered sites:

- `src/L/Ordinal/SquareLaw.lagda.md:685-687` defines `sq` as exactly that.
- `src/L/StageCardinal.lagda.md:17-19` takes it as its `sq` hypothesis.
- `src/L/BoundedSubset.lagda.md:1388-1390` takes it as its `sq` hypothesis.

The consumer never asks for an L-element. It asks for a metatheoretic
injection. `via-col-square : (α : S) → Init α → sq α`
(`SquareLaw.lagda.md:960-961`) delivers that injection directly at every
initial ordinal by the order-theoretic collapse, with NO successor step and
NO composition. `[LJ-1.234]` closed the one non-initial gap, the base at
`ω`, in 60 lines. Nothing is left for the column square to supply.

**The column square was the successor step of a different route.** In the
ambient chain it is `pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))`
(`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:494`), which composes three
injections that already exist. That chain climbs from `ω` to every ordinal
by successor steps. The delivered order route does not climb. It builds
`sq α` at `α` directly. The step is gone, so its object is gone.

## 3. THE EVIDENCE, ALL MEASURED BY GREP OR READING

| claim | evidence | class |
|---|---|---|
| the column square is in no delivered file | `grep α↪κ src/` = 0; `grep sqκ src/` = 0 | **MEASURED** |
| the archived successor step is not delivered | `grep "pair-suc\|module Shift" src/` = 0 | **MEASURED** |
| the order route IS delivered | `via-col-square` at `SquareLaw.lagda.md:960-961` | **MEASURED** |
| the order route is green | `_build/2.8.0/agda/src/L/Ordinal/SquareLaw.agdai` dated 14 Aug 08:47, and `git status` shows no `src/` edit | **MEASURED** |
| the consumer asks for the ambient injection, not an L-element | the three `sq` sites above | **MEASURED** |
| the 99 was a transfer, not a measurement | `lj-1.176-report.md:265-269` says so; `lj-1.152-report.md:224` is the source | **MEASURED** |

**The 99's provenance, checked per C-44.** `lj-1.152-report.md:224`: "Part 4
alone, 99 lines, is what a second composition site costs." That figure was
for a composite of two graphs between plain sets. `[LJ-1.176]` carried it to
the column square and marked it INFERRED. **The inference is now moot: the
site it was carried to does not exist.**

## 4. THE PRODUCT ACTION

**`[LJ-1.176]` named the risk: the product action `(x , y) ↦ (α↪κ x , α↪κ y)`
may need its own object. It does not.** The product action is a component of
the column square's composition, and the whole column square dissolves. The
order route never forms the product action: `via-col-square`'s pairing is
`pair p = fiber α {x = colA p} (col∈α p) .fst`
(`SquareLaw.lagda.md:944-945`), whose only atoms are membership and the
collapse. No product action, no `α↪κ`, no `j`. MEASURED by reading the
definition.

## 5. A5 RE-DERIVED

**A5 = 348 lines, fully measured.** Rows 1, 2, 3 and 5 are not re-priced
(the brief forbids it); row 4 is dissolved here.

| # | object | lines | class |
|---|---:|---:|---|
| — | `StageBound` | 16 | **MEASURED**, `[LJ-1.176]` and `[LJ-1.154]` |
| 1 | composition of two injections | 160 | **MEASURED**, `[LJ-1.152]` |
| 2 | `CSB` | 0 | **MEASURED**, `[LJ-1.156]` |
| 3 | inclusion `j` | 112 | **MEASURED**, `[LJ-1.176]` |
| 4 | column square `pair` | **0** | **DISSOLVED**, this task |
| 5 | `pairω` | 60 | **MEASURED**, `[LJ-1.234]` |
| | **A5** | **348** | |

**Against the brief's arithmetic: 547 − 99 − 160 + 60 = 348.** The two
figures agree.

**I do NOT quote a total for Route A-prime.** The brief forbids it, and six
reports refuse one. A5's own total is 348.

## 6. TOWER STATUS

**The dissolution is tower-neutral. MEASURED, and by the statement.**

The column square's statement is `sq α`, which names `⟪_⟫`, `×`, `→`, `Σ`
and `≡` and nothing else (`SquareLaw.lagda.md:685-687`). No
`hasSeparationL`, no `hasReplacementL`, no `Lset`, no `stage`, no
`boundingOrd`, no `𝒮ʟ`. The object dissolves to zero lines, so it adds zero
tower-specific weight to either tower.

The route that replaces it, `via-col-square`, was measured tower-neutral by
`[LJ-1.234]` section 4 (zero hits for the tower atoms over the whole probe).
So the J tower pays nothing twice here.

**A5's tower status stays OPEN.** `[LJ-1.243]` measured that
`[LJ-1.227]`'s tower table does not cover A5, and I do not settle it. This
task removes one inferred row; it does not re-open the tower question and
it does not close it.

## 7. SECONDS AND LOAD

**No `agda` run was needed, so no seconds figure is reported.** The dissolve
branch is a structural finding: the column square is absent from the
delivered tree and the delivered order route supplies the consumer's
obligation. The decision rests on greps and reads, not on an elaboration.
ONE agda process would have been used under `GHCRTS="-A64m -I0 -M8g"` had a
measurement been required; it was not. The cap was never raised.

## 8. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-176/lj-1.176-report.md`, read WHOLE.** TAKEN: the
  five-object partition and the 547 (section 5); the row-4 inference and its
  own warning at `:265-269`; the row-5 transfer record at `:227-229`; the
  99's source at `:224` of the `[LJ-1.152]` report it cites.
- **`agents/tasks/LJ-1-234/lj-1.234-report.md` and `ProbeLJ1234A.agda`, read
  WHOLE.** TAKEN: the dissolution question and its answer; the 60-line base
  at `ω`; the consumer analysis (section 5); the tower-neutral grep (section
  4). This report is the template, exactly as the brief says.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`, read WHOLE.** TAKEN: the
  99-line second-site figure at `:224`, which is the whole of what row 4's
  99 was. The transfer is now moot.
- **`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:482-497`.** TAKEN: the column
  square as the ambient chain wrote it, `pair (x , y) = j (sqκ .fst
  (α↪κ .fst x , α↪κ .fst y))` at `:494`. It is a probe, not a master.
- **`src/L/Ordinal/SquareLaw.lagda.md:685-687` and `:960-961`, read in the
  source.** TAKEN: the consumer's obligation and the delivered order route.
- **`archive/dev/TASKS-archived.md:82`.** TAKEN: L3.32-T47 "Truncated square
  law at initial ordinals — DELIVERED", which is the order core the current
  tree keeps. One line read, as the brief requires.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:793`
  (and `:652`, `:831`, `:958-959`).** TAKEN, SHAPE ONLY: the retired route
  DID hold a column-square successor step, `pair-suc` at `:793`, fed by
  `Shift` at `:652`, beside its `CoreAtω` base at `:831`. The current tree
  holds NONE of the three. The note at `:958-959` states the boundary in
  words: the order core gives the law at initial ordinals and nothing at
  non-initial ones such as `ω + ω`, whose site reduces to the cardinal by
  the least-of transfer. **WHAT WOULD NOT TRANSFER: the line counts (P-l) and the whole
  successor-step shape, which the current tree replaced.**

## 9. LITERATURE USED (DD18)

- **`dev/literature/rudimentary-functions.md:68`.** TAKEN: the basis line is
  `F2(x, y) = x × y`, the product, delivered outright. The same list gives
  `F9(x, y) = <x, y>`, the ordered pair, at `:75`. **It requires NO column
  square as its own object.** The basis delivers the square's carrier
  `⟪α⟫ × ⟪α⟫` directly, and no basis function is a successor-step
  composition of injections. **MEASURED: zero hits in that file for
  "column", "square", or any successor-step pairing.** The column square is
  a construction of the ambient chain, not a requirement of the literature
  basis.

## 10. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The column square is in no delivered `src/` file.** Three
  greps, zero hits: `α↪κ`, `sqκ`, `pair-suc|module Shift`.
- **MEASURED. The delivered order route exists and is green.**
  `via-col-square` at `SquareLaw.lagda.md:960-961`, with a cached interface
  dated 14 Aug 08:47 and a clean `git status` over `src/`.
- **MEASURED. The consumer asks for the ambient injection, not an
  L-element.** The three `sq` sites in section 2.
- **MEASURED. The product action needs no object of its own.** The order
  route's pairing has no product action (`SquareLaw.lagda.md:944-945`).
- **MEASURED. The 99 was a transfer, not a measurement.** Its source is
  `lj-1.152-report.md:224`, and `[LJ-1.176]` marked it INFERRED.
- **MEASURED. The dissolution is tower-neutral.** The statement `sq α`
  names no tower atom, and the object dissolves to zero lines.
- **INFERRED. A5's tower status is OPEN.** Inherited from `[LJ-1.243]`; I
  did not re-measure it, and I do not settle it either way.
- **NOT MEASURED. Seconds for row 4.** There is no object to elaborate, so
  there is no seconds figure. This is a dissolution, not a zero-second run.

## 11. WORKING TREE

One file written, this report, in `agents/tasks/LJ-1-247/`. No master
edited. No file under `src/` edited. No commit, no push, no
`git checkout .`/stash/reset/clean. No `make check`. No agda process was
run and none is running.

**Checks run after the last edit:** `scripts/lint-prose.py --check` on
this report, exit 0. `scripts/lint-agda.py --check` has no target: this
task wrote no `.agda` file, because the dissolve branch names no
measurement.
