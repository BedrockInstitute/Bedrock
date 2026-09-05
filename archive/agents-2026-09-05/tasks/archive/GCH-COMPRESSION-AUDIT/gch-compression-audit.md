# GCH compression audit

Status: COMPLETE. Written incrementally per C-22. ASD-STE100.
Subject: the nine GCH-side masters, 8,476 in-fence lines, pinned at `f7314af`.
Method: all measurements run on a pristine copy of `f7314af` in `/tmp/gch-audit`
with its own interface directory. No master was edited. No run touched the main
tree's `_build`.

Sibling note: the codex agent `[LJ-1.52]` is live in this repository with write
scope on `src/L/BoundedSubset.lagda.md` and `src/L/Condensation.lagda.md`. At
audit start no `agda` process was running (pgrep exit 1). I re-check for a live
`agda` process before each timed run and record what I found.

## 1. THE PATCH LIST (ranked by lines saved per unit of risk)

All figures are measured on a pristine copy of `f7314af` in
`/tmp/gch-audit` (own interface removed each run, dependencies warm, one
process, `GHCRTS="-A64m -I0 -M8g"`, user seconds). Baseline
`src/L/Condensation.lagda.md`: 59.68 / 60.57 / 61.35, median 60.57, at
4,632 in-fence lines. Every timed run's pre-check found no foreign
`agda` process; two runs that logged a stale pid of my own prior run sit
inside their siblings' spread.

APPLY GATE for every Condensation item: `[LJ-1.52]` has write scope on
this master NOW. Apply only after it lands, re-derive line numbers on
the final master, and re-grep the deleted names first (a2 items are the
ones its reports cite; see risks).

### Item 1 (A1): delete the superseded Row layer and its private kits

- Edit: delete `src/L/Condensation.lagda.md:774-952` (the five `*Decode`
  kits with their header comment) and `:1766-2210` (the block banner,
  `RowTransfer`, `RowDecode`, `BotRow` .. `ExInRow`). Line numbers are
  `f7314af`'s.
- Lines saved: 613 (ledger caliber; file 4,632 to 4,019).
- Seconds: 54.27 / 55.77 / 55.92, median 55.77 against 60.57, DELTA
  MINUS 4.80 s (spread 1.65 s). The deletion is also a speedup.
- Ratio effect: Condensation's own rate RISES 0.01308 to 0.01388 (same
  load cone over fewer lines); the WING aggregate moves 0.01146 to
  0.01174, still under the 0.012716 bar.
- Risk: LOW. The deleted names have zero references in the file, zero in
  the eight sibling masters, zero anywhere in `src/` (only `Everything`
  imports this module at all). The closed Agree table never references
  them. No exported signature that remains changes; the removed names
  were never consumed. Typechecked green; consumer check in section 2.
  Residual risk: `[LJ-1.52]` could choose to instantiate a `*Row`
  module for its re-basing; its brief prescribes the Agree rows and
  `EraseTransfer` instead. The apply gate covers this.

### Item 2 (B): the [LJ-1.39] re-derivation, on top of Item 1

- Edit: insert the `sh2`/`z2..z9` private kit after `module Cnt = ...`
  (the exact kit text of `_build/lj-1.39-report.md` section 5); replace
  every balanced `(suc^k base)` chain, k at least 2, in BODY positions
  only; re-flow continuation lines at 120 columns where the previous
  line's own paren balance is positive, never across a comment or a
  layout keyword (`let`, `where`, `do`, `of`). The transform script is
  reproduced at `/tmp/gch-audit/lj139.py`; it replaced chains on 1,036
  lines.
- Lines saved: 644 further (4,019 to 3,375).
- Seconds: 46.55 / 46.05 first two cold runs against Item 1's 55.77,
  DELTA MINUS about 9.5 s. THE COMPRESSION IS A LARGE SPEEDUP, bigger
  than [LJ-1.39]'s 0.36 s because the Agree blocks re-elaborate these
  literals far more often than the 2,031-line file did.
- Ratio effect: file rate 0.01388 to about 0.0137 (46.3/3,375); wing
  aggregate falls to about 0.01131 (fewer seconds AND fewer lines).
- Risk: LOW-MEDIUM. No type signature changes: the replacement engine
  never touches signature lines (computed mechanically, not
  hand-listed), and the joined normalized type text of the whole file is
  IDENTICAL before and after (verified programmatically). Bodies change
  spelling only: `z_k` and `sh2` normalize to the same `suc` chains.
  The re-derived [LJ-1.39] verdict HOLDS and is now much stronger.
- [LJ-1.39]'s two open cautions carry over: the 120-column budget is a
  house-style choice (160 saves more), and the transform must be re-run
  mechanically on the final master, never hand-applied.

### Item 3 (A2): delete the zero-consumer block-1 shape exemplars. DEFERRED

- Edit (line numbers of the A1+B state; re-derive on the final master):
  delete `existCertAt`/`Σ₁-cert` with comment (233-239), the ClauseDecode
  banner, `ClauseDecode`, `CertTransfer`, `ride-only`, `ride-defines`
  (278-391), `StepAtB` with comment (1501-1518); then drop the orphaned
  `; Σ₁; σ-Δ₀; σ-∃` from the `FOL.LevyHierarchy` import.
- Lines saved: 123 further (3,375 to 3,252). Typechecked green.
- Seconds: 44.81 / 45.96 / 46.33, median 45.96 against Item 2's 46.05:
  SECONDS-NEUTRAL (minus 0.09 s, inside the noise band).
- Ratio effect: file rate rises slightly (same seconds, fewer lines).
- Risk: HIGH TODAY, LOW AFTER [LJ-1.52]. All six names have zero code
  references, but `[LJ-1.48]` calls `existCertAt`/`Σ₁-cert` "the exact
  block-1 certificate shape" for the level-hood matrix, and the
  `[LJ-1.50]` review says "the delivered CertTransfer already takes that
  route" for the Σ₁ transfer `[LJ-1.52]` needs. The live sibling may
  instantiate exactly these. Do not apply until it lands and a re-grep
  of the six names on the final master comes back empty.

### Apply order

1 first (biggest mass, lowest risk), then 2 (mechanical, re-run the
script on the post-1 master), then 3 only after the gate clears. Items 1
and 2 together are the recommendation; item 3 is the orchestrator's
call.

## 2. THE TOTAL

Baseline wing: 97.15 s over 8,476 lines = 0.01146 s/line (sum of
per-file cold medians; table in section 5). Bar: 0.012716.

| configuration | Condensation lines | Condensation s | wing lines | wing s | wing ratio |
|---|---:|---:|---:|---:|---:|
| baseline `f7314af` | 4,632 | 60.57 | 8,476 | 97.15 | 0.01146 |
| + item 1 (A1) | 4,019 | 55.77 | 7,863 | 92.35 | 0.01174 |
| + item 2 (A1+B) | 3,375 | 46.05 | 7,219 | 82.63 | 0.01145 |
| + item 3 (all) | 3,252 | 45.96 | 7,096 | 82.54 | 0.01163 |

The recommended state (items 1 and 2): 1,257 lines deleted (14.8
percent of the wing), 14.52 s saved, and the wing ratio comes back to
0.01145, indistinguishable from baseline and under the bar. The usual
"compression worsens the ratio" penalty is fully paid back by item 2's
speedup.

Verification done on the recommended state: the file typechecks green;
`src/L/BoundedSubset.lagda.md` (the only consumer) typechecks green
against it at 11.88 s user (baseline 11.69, inside noise);
`scripts/check-fences.py --check` clean; `scripts/lint-agda.py --check`
exit 0; the joined normalized type text of the whole file is identical
before and after item 2, so no signature and no theorem statement
changed; item 1 removes only never-referenced names.

## 3. WHAT HAS NO CONSUMER

The import graph is small. Outside the nine masters, only
`src/Everything.lagda.md` imports any of them (grep over `src/`, all
importers listed; probes excluded). Internal consumption:
`BoundedSubset` imports `Condensation` (`DefBodyB`, `Δ₀-DefBodyB`,
`module GraphB` only, `src/L/BoundedSubset.lagda.md:29-31`), `Hull`
(`module AtStage`, `:33`), `Collapse` (`:34`), `StageCardinal` (`:563`),
`Presentation` (`:723`), `FOL.Count` (`:22`). `StageCardinal` imports
`FOL.Count` (`:20`) and `Presentation` (`:24`). `SquareLaw` imports
`Presentation` (`:32`).

### 3.1 Dead inside Condensation, with both directions checked

Transitive reachability over all 155 top-level declarations, computed
from the live roots: the three downstream-consumed names above, the
thirteen closed Agree modules (`BotAgree` .. `EqAgree`, `ExistAgree`,
`ClauseAgree`), and `EraseTransfer` (prescribed to `[LJ-1.52]` by its
brief). 26 declarations are unreachable, 757 non-blank in-fence lines:

- The superseded Row layer: `RowTransfer` (:1772), `RowDecode` (:1786),
  eleven `*Row` modules (:1795-2210). Built by `[LJ-1.37]` (the C-35
  false-theorem dispatch). The closed table that replaced it is the
  Agree layer (`[LJ-1.40]`, `[LJ-1.41]`, `[LJ-1.43]`), and no Agree
  module references `RowTransfer` or any `*Row` module.
- The five `*Decode` kits (:777-955). Their in-file reference counts
  (2, 5, 1, 1, 2) match the Row modules' uses exactly; no live code
  reaches them.
- `ClauseDecode` (:304), `CertTransfer` (:398), `ride-only` (:408),
  `ride-defines` (:413), `existCertAt`/`Σ₁-cert` (:255-259),
  `StepAtB` (:2422). Zero references, BUT `[LJ-1.48]` and the
  `[LJ-1.50]` review cite them as the shape exemplars for the level-hood
  work that `[LJ-1.52]` is building right now. Deferred (see section 1).
- `ride-only`/`ride-defines` are one-line aliases of
  `L.Hierarchy.Lset-only`/`Lset-defines`; deleting them weakens no
  theorem.

The thirteen Agree modules and `ClauseAgree` also have zero consumers
today, and so do `Devlin55`, `LevelHood0`, `erase-Δ₀`, `AtHullInstance`
in `BoundedSubset`. These are NOT dead: they are the closed deliverable
and the in-flight `[LJ-1.52]` material. The audit lists them so the
no-consumer evidence is complete, and touches none of them.

### 3.2 Masters with no consumer

- `src/L/Ordinal/StageArith.lagda.md` (75 lines, 0.68 s): nothing in
  `src/` imports it except `Everything` (grep evidence above). It was
  built and priced deliberately at `[LJ-1.20]` as the `+ω` kit for the
  bound step (`dev/PLAN.md:483`), and the level/cover work now in
  flight is its intended consumer. Removing it saves 75 lines and
  0.68 s and would LOWER the wing aggregate quality (its rate 0.0091 is
  below the wing mean). Not recommended; the orchestrator should decide
  after `[LJ-1.52]` lands.
- `src/L/Ordinal/SquareLaw.lagda.md` (775 lines): consumers-in-waiting;
  the `sq` wiring is `[LJ-1.17]` route 1 and is explicitly deferred by
  the `[LJ-1.52]` brief. Not a deletion candidate.

### 3.3 Small zero-consumer items elsewhere

- `src/L/Hull.lagda.md:515-524`: `OrderAtom` and `OrderAtStage`, about
  10 lines, zero references. They are order-at-stage instantiation
  conveniences that the in-flight cover/least-δ work may consume.
  Rejected for now: yield too small against the conflict risk.

## 4. WHAT I REJECTED AND WHY

- **Everything in `BoundedSubset` (1,101 lines).** Nine inner names have
  zero references (`Σ₁-levelHood` :141, `SemPM` :171, `surj'` :175,
  `reflect` :464, `_⊨ₚ_` :492, `Σ₁-Σ₂` :540, `leg1` :778, `leg2` :821,
  `BoundedSubsetAt` :1078). All are `[LJ-1.52]`'s in-flight material or
  sit inside the closed `Devlin55` block. The sibling has write scope on
  this file NOW. No patch.
- **Deleting `StageArith` (75 lines, 0.68 s).** Zero importers, but it
  is the deliberately built and priced `+ω` kit (`[LJ-1.20]`,
  `dev/PLAN.md:483`) whose intended consumer is the bound step now in
  flight. Its rate 0.0091 is below the wing mean, so deleting it would
  RAISE the aggregate ratio while removing planned capability.
- **`OrderAtom`/`OrderAtStage` in Hull (about 10 lines).** Zero
  references, but they are order-at-stage conveniences the cover work
  may consume, and the yield is under measurement noise.
- **A `sh2`/`z` kit for any other master (D-28).** The index-chain mass
  is Condensation-only: strict index-only lines are 321 there against 2
  in BoundedSubset and 0 in the other seven (re-measured on `f7314af`;
  `[LJ-1.39]`'s two-orders-of-magnitude finding still holds). A kit
  outside Condensation prices at 31 kit lines minimum against near-zero
  sites.
- **Re-flow alone on BoundedSubset (about 20-30 lines).** No kit needed,
  but the sibling edits the file today and the yield is small. Re-offer
  after `[LJ-1.52]` lands if the ledger needs it.
- **Class-4 parameter collapse in Condensation.** The extraction already
  happened: `PropAgree` serves And and Or, `AtomLeaf` serves Mem and Eq,
  `BndLeaf` serves AllIn and ExIn, and `UnaryShape`/`BinaryShape`/
  `EnvSet`/`TmVal`/`SubValB2T`/`SubValSuccB2T` are shared kits with
  multi-site reference counts (10, 12, 19, 6, 4, 8 in-file). I found no
  remaining duplicated shape whose kit would price under its sites per
  D-28.
- **`SquareLaw` general-law trimming (D-30).** The 775-line master
  landed lean at `[LJ-1.51]`: the archived square law's four unused
  general-law sections (`[LJ-1.47]`, 5.45x) did not come along. Its
  exports `via-col-square`/`via-col-truncated` await the deferred
  `[LJ-1.17]` wiring. Nothing to cut.

## 5. WHAT I COULD NOT MEASURE

Per-file baselines measured (cold user seconds, own interface removed,
deps warm, medians): Condensation 60.57, BoundedSubset 11.69, Hull 2.49,
SquareLaw 7.60, StageCardinal 11.33, Count 1.435, Collapse 0.84,
StageArith 0.68, Presentation 0.51. Sum 97.15.

- **Item 3's own seconds delta** is bounded by the noise band (46.33
  first run against the 46.05 item-2 median); I report it as
  seconds-neutral rather than as a signed number.
- **The main-tree numbers.** Every measurement ran in the pinned scratch
  copy so the live `[LJ-1.52]` sibling was never raced for interfaces or
  a quiet machine. The scratch cone differs from the main tree only in
  path; a confirming re-measure on the final master is the apply gate
  anyway (C-32).
- **StageCardinal's 0.02009 s/line**, the worst rate in the wing. It has
  zero index-padding lines, no dead code, and no unconsumed exports (the
  two flagged names are consumed by their top-level wrappers). Its cost
  is real content (well-founded recursion over stages). A cure would be
  a build-side re-spelling (P-v class), out of an audit's scope; I name
  it as the next candidate for a measured probe.
- **Signature diff caliber.** `[LJ-1.39]` diffed interaction-mode module
  contents; I verified instead by (a) mechanical protection of type
  lines, (b) identical joined type text, (c) the consumer green. I did
  not reproduce the interaction-mode diff.

## 6. SIBLING AND MACHINE STATE

The brief requires the check: before every timed run the script logged
`pgrep -x agda`. No foreign `agda` process appeared in any pre-check.
The codex agent `[LJ-1.52]` was dispatched at 23:02 tonight with write
scope on two of the nine subject masters; it had not started an `agda`
process during any of my runs. Two log lines captured a stale pid of my
own just-finished run; both affected runs sit inside their siblings'
spread and the medians are quiet-run medians.

At audit end `dev/PLAN.md` shows as modified in the main working tree.
That edit appeared during this session and is not mine: I wrote only
this report file. Expect the sibling's or the orchestrator's in-flight
work there.

## ARCHIVE USED

- `_build/lj-1.39-report.md`, whole. Took the kit text, the transform
  rules, the protocol (deps warm, own interface aside), and the two
  open cautions.
- `_build/lj-1.42-report.md:29,85-87,156-158`: the dead-scaffolding
  claim. `QuantBody` is already gone from `f7314af`; `ExistAgree` is
  live at `:3919`. The claim is stale and I re-derived from zero.
- `_build/lj-1.40-report.md:1-40`, `_build/lj-1.43-report.md:1-60`: what
  the closed twelve-row table IS (the Agree layer), which decided that
  the `*Row` layer is superseded.
- `_build/lj-1.37-report.md:56-57,153`: the Row layer's birth.
- `_build/lj-1.48-report.md:40-60,195-215` and
  `_build/lj-1.50-review.md:150-165,515-528`: the in-flight claims that
  moved `ClauseDecode`/`CertTransfer`/`existCertAt`/`Σ₁-cert`/`StepAtB`
  from item 1 to the deferred item 3.
- `dev/PLAN.md:483`: StageArith's registered purpose.
- `dev/LESSONS.md:1757-1810` (D-28), `:3255` (D-30), plus the review
  bundle via `scripts/rules.py --for review`.
