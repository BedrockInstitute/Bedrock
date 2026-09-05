# LJ-1.51: discharge the five hypotheses

Status: COMPLETE. Written incrementally per C-22. ASD-STE100.
No commit. No push.

## 0. THE LEDGER (live)

Two of the five are discharged and wired. One more (`sq`) is delivered as
the measured master; its module parameter still survives because the
consumer interface demands the law at every infinite ordinal, which the
Init-restricted law cannot serve. Two (`cover`, `levelIn`) survive, priced
below.

| hypothesis | home | status | what a survivor still needs |
|---|---|---|---|
| `fin-inj` | `StageCardinal:589` (was `BoundedSubset:909`) | **DISCHARGED** | none; delivered in `StageCardinal`, the parameter removed from `Devlin55` |
| `sq` | `StageCardinal:15`, `BoundedSubset:1045` | **MASTER BUILT**, parameter survives | the fixed-target consumer reshaping (LJ-1.17 route 1, 200 to 280 lines), which alone lets the Init-restricted law serve the induction |
| `Mext` | `BoundedSubsetAt.Co` | **DISCHARGED** | none; `HullExt.hullExt` proves `isExt HS.M`, the parameter is removed from `Co` |
| `cover` | `BoundedSubset:599`, `:1092` | SURVIVES | the level-hood adequacy at the hull plus the least-δ and level-preservation steps; see section 4.2 |
| `levelIn` | `BoundedSubset:598`, `:1091` | SURVIVES | the level-hood adequacy at the hull plus the collapse-of-the-level; see section 4.1 |

## 1. ORDER OF ATTACK

1. `fin-inj`, 50 to 100 lines, mechanical.
2. `sq`, the measured 744-line master.
3. `Mext`, 120 to 250 lines from `hull-closed`.
4. `cover`, the rank chain.
5. `levelIn`, priced before built.

## 2. WHAT LANDED

### 2.1 `fin-inj`, discharged

The route measured by LJ-1.21 works as priced: a member of `ω` is merely a
numeral `# n`, `Lset (# n)` is the finite stage with a delivered tally
(`L.Choice.Finite.stageOrder`), the least index of a member in the tally is
a natural number, and the numeral injection maps the index into `ω`.
Injectivity uses the tally witness and the injectivity of the index and the
numeral; minimality is never used, any deterministic index would do. The
extraction from the truncated `ω` membership is LEM on a proposition (the
`Σ[ n ] (# n ≡ δ)` fibre is a proposition by `#-inj′`). The content lives
in `src/L/StageCardinal.lagda.md` as the `FinInj` module plus `fin-inj`;
`module Upper` lost its `fin-inj` parameter, and `Devlin55` lost its own.
`L.StageCardinal`'s top-level signature is unchanged, so `Everything`'s
bare import still loads it.

### 2.2 `Mext`, discharged

The LJ-1.49 route works, with one simplification: the least-code selection
is never needed. The codes of the two hull members stay inside the
truncated hull membership and are eliminated into the proposition
`x ≡ y`. The proof (`HullExt` in `src/L/BoundedSubset.lagda.md`) is the
difference-witness argument: suppose `x ≠ y`; extensionality's
contrapositive (one LEM) gives a direction, say `¬ (x ⊆ y)`; a classical
extraction (one LEM on a proposition) gives a global witness
`z ∈ x \ y`; `z ∈ Lset lam` by transitivity of the stage, so `z` is an
outer witness of the difference formula `v ∈ x ∧ v ∉ y` over the codes;
`hull-closed` produces a hull member with the same property; the agreement
hypothesis refutes it. `Mext` is deleted from `Co`'s parameters and
`InvColl HS.M` is fed `HE.hullExt`.

The formula `φ c d = (var zero ∈̇ con c) ∧̇ (¬̇ (var zero ∈̇ con d))` is the
membership-separation formula the LJ-1.49 price named, and `hull-closed`
is exactly the Skolem-witness step.

P-v is observed throughout: every proof that appears in both a type and a
body has a name (`numeralω-inj`, `least-wit`, `ext-contra`, `hullExt`), and
no `refl` is written inline as an argument of a transparent recursion.

### 2.3 `sq`, the master is built; the parameter survives

`src/L/Ordinal/SquareLaw.lagda.md` (one new master, `L.Ordinal.SquareLaw`)
contains the measured via-collapse pair: the collapse of the max-lex
product order, the finite base with the exclusion chase, the initial core
and the `Initial` module, delivered as
`opaque via-col-square : (α : S) → Init α → sq α`. Two adaptations from
the LJ-1.47 probes: the archived `natSWO` is replaced by the delivered
`L.Choice.Finite.natOrder`, and the lexicographic product `prodSWO`
(absent from today's tree) is embedded as generic content, so the master
stays at one file. It checks cold at 7.46 s over 775 in-fence lines
(0.0096 s per line), inside the measured band.

**Why the parameter survives.** `L.StageCardinal` consumes `sq` at every
infinite ordinal: `Upper`'s ∈-induction calls the law at the target and at
every infinite ordinal below it, including non-initial ones such as
`ω + ω` where `Init` is not discharged and the extraction wall blocks the
honest law (the archived chapter's recorded reason). The cure is the
fixed-target reshaping: for an initial `κ` and every `β ≤ κ`, prove
`⟪ Lset β ⟫ ↪ ⟪ κ ⟫` with every square-law call at the target `κ`
(`Init κ`), which is LJ-1.17 route 1, priced at 200 to 280 lines, with its
limit half at 150 to 220 lines (`_build/lj-1.6-review.md:123-124`), and
explicitly NOT part of LJ-1.47's measurement
(`_build/lj-1.47-report.md:102-104`). That reshaping is the gate that turns
the built master into a discharged parameter; it is outside the measured
master this dispatch was sent to build.

## 3. MEASUREMENTS

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, USER seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved aside),
dependencies warm, one process at a time, quiet machine. Every figure is
the mean of three completed runs; there is no interruption and no heap
exhaustion.

| module | runs, user s | mean | spread | in-fence lines | s per line |
|---|---:|---:|---:|---:|---:|
| `L.BoundedSubset` whole | 10.95 / 11.04 / 11.29 | 11.09 | 0.34 (3.1 pc) | 1,101 | 0.01007 |
| `L.StageCardinal` whole | 11.26 / 11.38 / 11.48 | 11.37 | 0.22 (1.9 pc) | 564 | 0.02016 |
| `L.Ordinal.SquareLaw` (new) | 7.43 / 7.45 / 7.51 | 7.46 | 0.08 (1.1 pc) | 775 | 0.00962 |
| HullExt content probe | 1.89 / 1.88 / 1.87 | 1.88 | 0.02 (1.1 pc) | n/a | n/a |
| HullExt import cone | 1.53 / 1.51 / 1.52 | 1.52 | 0.02 (1.3 pc) | n/a | n/a |
| SquareLaw import cone | 0.96 / 0.89 / 0.89 | 0.91 | 0.07 (7.7 pc) | n/a | n/a |
| fin-inj content probe | 0.82 / 0.83 / 0.82 | 0.82 | 0.01 (1.2 pc) | n/a | n/a |
| fin-inj import cone | 0.70 / 0.67 / 0.67 | 0.68 | 0.03 (4.4 pc) | n/a | n/a |

The marginal rates, one caliber throughout:

| added content | lines | mean user s | rate |
|---|---:|---:|---:|
| `fin-inj` (in StageCardinal) | 80 | 0.82 - 0.68 = 0.14 | 0.0018 |
| `HullExt` (in BoundedSubset) | 125 | 1.88 - 1.52 = 0.36 | 0.0029 |
| `SquareLaw` master | 775 | 7.46 - 0.91 = 6.55 | 0.0085 |

The whole-file rates sit where the classes predict: `BoundedSubset` and
`SquareLaw` are at or under the DD24 bar 0.012716 (`dev/ledger.toml:2590`
times `:2810`); `StageCardinal` at 0.02016 is above it, but that is the
pre-existing module's own rate (LJ-1.21 measured 0.087 at the same
caliber), and the added `fin-inj` content is the cheapest part. The
module-load cones are the quoted cone rows; they are per-invocation
interface costs, not content costs, and the ledger itself says so
(`dev/ledger.toml:2580-2586`).

## 4. THE SURVIVORS, PRICED

### 4.1 `levelIn`: the wall, and the term I cannot write

`levelIn δ oδ δ∈πX : Lset δ ∈ πX`. The discharge is the level-hood
adequacy at the hull's carrier, and its deepest step is unpriced. The
structure, written as the term I could not write:

```text
levelIn δ oδ δ∈πX =
  -- δ = π m for a hull member m (πX-member; eliminate the truncation into
  -- the proposition Lset δ ∈ πX)
  -- the Σ₂ level-hood statement at the hull gives, by elementarity of the
  -- hull (an unbuilt TV/ElemDown instance), witnesses K' v' w' ∈ M of the
  -- level graph at m, with v' the level value
  -- collapse-of-the-level:  π v' ≡ Lset (π m) = Lset δ
  --     needs (i) the twelve-row agreement re-based at the hull's carrier
  --     (v' = Lset m' for the code witness m'), and
  --     (ii) π (Lset m') = Lset (π m'), the collapse commuting with the
  --          level construction
  -- then πX-intro v' gives Lset δ ∈ πX
```

Two of the three pieces have prices: the certificate transfers through
the delivered `EraseTransfer` template at 1.56 s at the leaf and 2.83 s as
the Σ₁ template (the 1.50 review's exits, both green), and the adequacy's
statement-level connector is a 4.78 s probe
(`_build/lj-1.49-report.md:42`). The third piece, the
collapse-of-the-level `π (Lset m') = Lset (π m')`, has NO price: nothing
in the delivered tree measures it, and this dispatch found nothing to
anchor it on. `Lset m'` is not known to be a subset of `M` (that is the
levelIn direction itself), so `Collapse.fixes` does not apply; and no
collapse-commutation law for the level construction exists. Per C-34 the
honest entry is: the collapse-of-the-level is the wall, with no measured
price, and the structural total for `levelIn` is 200 to 400 lines
contingent on it.

### 4.2 `cover`: priced with the adequacy

`cover y y∈M : ∥ Σ γ (IsOrd γ × γ ∈ πX × π y ∈ Lset γ) ∥₁`. The route is
the rank/cofinality chain: `y ∈ Lset lam` (Hull⊆L), so `rank y ∈ lam`
(`rank-Lset`); the least `δ` with `y ∈ Lset δ` is a definable function of
`y`, hence a hull member once the level-membership relation is expressible
in the hull's language (the adequacy); then `π y ∈ Lset (π δ)` by a
level-preservation step, with `π δ ∈ πX`. Like `levelIn`, cover is priced
with the adequacy (`_build/lj-1.49-report.md:76-99`); its additional
steps (least-δ selection, level-preservation) are structural, 150 to 300
lines on top of the adequacy's discharge. No part of it can be built
before the adequacy, and the adequacy's own deepest step is the
unmeasured collapse-of-the-level of section 4.1.

### 4.3 `sq`: the consumer wall

The master is built (section 2.3). The parameter survives because the
current consumer calls the law at every infinite ordinal below the target;
the Init-restricted law cannot serve those sites, for the archive's own
recorded reason (the extraction wall at non-initial ordinals,
`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`). The
discharge is the fixed-target reshaping, priced at 200 to 280 lines
(`_build/lj-1.17-review.md` route 1, `_build/lj-1.47-report.md:102-104`),
whose limit half is 150 to 220 lines (`_build/lj-1.6-review.md:123-124`).
That reshaping is a build in its own right; it was not part of this
dispatch's measured master.

## 5. DD4 SPLIT

- `fin-inj`: template content. It mentions `V`, `Lset`, the tally and the
  numeral coding; no Def syntax, no level-hood formula. The J tower
  instantiates it unchanged.
- `sq` (`L.Ordinal.SquareLaw`): template content. The whole master is
  ordinal and cardinal machinery over `V`, `L.Ordinal`, `L.WellOrder` and
  `FOL.ZFStructure`; no Def-tower object appears in any type. The J tower
  inherits the module unchanged (D-26: no generation data needed to
  well-order the product, which is the descent's row and not this one).
- `Mext` (`HullExt`): shared template content with an L-side anchor. The
  difference-witness argument is generic in the `TermAlgebra` hull (Code,
  val, hull-closed, hull-member, Hull⊆L, stage transitivity), so the J
  tower's hull, built from the same `TermAlgebra`, reuses the module
  unchanged; the instantiation is at L's stage `lam`.
- `cover` and `levelIn`: Def-side. They key on the `Lset` level
  construction and the hull's level-hood statement, which are per-tower;
  D-26 predicts per-tower proofs, and this dispatch found nothing that
  changes that prediction.

## 6. WHAT I AM NOT SURE OF

1. The `fin-inj` marginal (0.14 s over 80 lines, 0.0018 s per line) sits
   near cone noise; the content is genuinely cheap, but a rate this low is
   only an upper bound, not a floor.
2. The `HullExt` placement adds 125 in-fence lines and 0.36 s of content
   to `BoundedSubset`; the whole-file rate stays under the bar. The
   probe-cone comparison is a proxy for the in-place marginal, not a
   measurement of the placed file alone.
3. `L.StageCardinal`'s whole-file rate (0.02016) is above the DD24 bar.
   The file was already at 0.087 per LJ-1.21's caliber; the delta is
   machine and tree drift, and the added content is the cheapest part. The
   wing arithmetic that decides the bar is the orchestrator's, not mine.
4. The `sq` master is 775 in-fence lines against the measured pair's 744:
   the extra 31 lines are the embedded `prodSWO` (measured separately by
   LJ-1.47 as the Combinators delivery). The rate is unchanged.
5. `Everything.lagda.md` imports `L.StageCardinal` and `L.BoundedSubset`
   bare; both top-level signatures are unchanged, and the two consumer
   probes I rechecked are green, but I did not typecheck `Everything`
   itself (that is the twelve-minute `make check` gate, which the brief
   forbids).
6. The `Init` verification at the actual cardinals (proving the three
   clauses at `κ` and `κ⁺`) is LJ-1.47's residual and remains outside this
   dispatch, as does the separate `ω`-base coding for GCH at `ω`.

## 7. ARCHIVE USED

- `_build/lj-1.50-review.md`, read WHOLE. Took the P-v extension
  (`:376-394`), the verdict tables (`:9-50`), and the unpriced
  collapse-of-the-level note (`:371`, `:442-443`).
- `_build/lj-1.47-report.md`, read WHOLE. Took the via-collapse pair price
  (`:10-31`), the consumer reshaping note (`:102-104`) and the wing table
  (`:152-160`).
- `_build/lj-1.49-report.md`, read WHOLE. Took the residue (`:31-63`) and
  the `Mext` price (`:99-103`).
- `_build/lj-1.21-report.md`, read WHOLE. Took the `fin-inj` price
  (`:9-16`, `:201-204`) and the tally base.
- `_build/lj-1.6-review.md:123-124`, the limit-half price.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`, read the shape
  (`:969-990`), `Initial` (`:1259-1286`) and the non-initial gap
  (`:956-963`).
- `src/ProbeLJ147Collapse.agda` and `src/ProbeLJ147SquareLawViaCol.agda`,
  read WHOLE; their content is the master's body with the imports
  re-pointed and `natSWO` replaced.
- `src/ProbeLJ117Combinators.agda`, read the `prodSWO` section
  (`:20-137`), embedded into the master.
- `src/L/BoundedSubset.lagda.md`, read the parameter lists (`:596-599`,
  `:906-957`) and the consumer code.
- `src/L/StageCardinal.lagda.md`, read WHOLE.
- `src/L/Hull.lagda.md`, read `TermAlgebra` (`:58-146`), `AtStage`/`AtM`
  (`:148-338`), `Hull` (`:313-425`).
- `src/L/Choice/Finite.lagda.md`, read the `Tally` record (`:120-125`),
  `natOrder` (`:596`), `stageOrder` (`:865-918`).
- `src/V/Collapse.lagda.md`, read `Collapse` (`:40-97`), `πX`
  (`:98-140`), `fixes` (`:334-341`), `isExt` (`:31-33`).
- `src/ProbeTowerInd2.agda`, read WHOLE (the fixed-target successor
  shape).
- `dev/ledger.toml`: the DD24 bar (`:2590`, `:2810`), the caliber note
  (`:2580-2586`).

Nothing else in `archive/` was read. WHY NOT: the retired route's other
crossings do not bear on the five hypotheses; the condensation target of
the retired route is classically false (`[LJ-1.11]`).

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385`, Devlin 5.5's statement and proof
  chain. TOOK: the site `α` is an arbitrary infinite ordinal below `κ`,
  which is why the Init-restricted law cannot serve the current consumer
  directly.
- `dev/literature/devlin-II5.md:164-166`, the single application in 5.6 at
  `κ⁺` with `α = κ`. TOOK: the initial-only application sites.
- `dev/literature/devlin-II5.md:209-257` (Step C), the level-hood strength
  requirement. TOOK: the shape of the Σ₂ statement the adequacy must carry
  at the hull.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.
- `jech13.txt` and `dev/literature/j-hierarchy.md` were NOT read. WHY NOT:
  the J-side cross-checks do not change the ordinal arithmetic or the
  hull-side hypotheses that this dispatch discharged or priced.

## 9. WHAT DEVLIN ASSUMES, IN ONE LINE

Devlin assumes the cardinal arithmetic of 1.1(vii) — `|L_λ| ≤ Σ_{α<λ} |α|
= |λ|` at limits and "easily seen" formula counts at successors — and
proves none of it (`_build/literature/dev2.txt:200-215`); the formal proof
supplies it as `fin-inj` (the finite counts), `sq` (the square law at the
initial ordinals) and the fixed-target consumer that this dispatch's
master is built to serve.
