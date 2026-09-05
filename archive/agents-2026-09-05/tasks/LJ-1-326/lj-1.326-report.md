# LJ-1.326 report: the miniature that gates BOTH new debts

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## BUILDS

**`InjL κ (𝒫 κ)` BUILDS from delivered code, in 14 lines.** The term is
`Reverse.injκ` at `agents/tasks/LJ-1-326/ProbeLJ1326A.agda:120`.

**The assembly pattern is now MEASURED at THREE delivered sites, not one.** The
four conjuncts of `L.InjChain.Carve`, of `L.InjChain.OrdIncl` and of
`L.Absorption.ShiftGraph` all type as an `InjCode`, with no adapter, no
transport and no re-proof. The tuple is the identity on four delivered names.

**So `[LJ-1.325]`'s two NO-GO branches are both closed.** Debt 2 does not become
unpriced. Debt 1's adapter half does not return to the ruling's 800.

## 1. WHAT RAN, AND THE MACHINE LOAD BESIDE EVERY FIGURE

Load counted before every invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. It read **1** every
time, so one sibling process was live and I took the second slot. C-12 was
never exceeded. `GHCRTS="-A64m -I0 -M8g"` on every run. No heap wall. No run
came near the 30-minute line.

| run | what | exit | real seconds | load before |
|---|---|---:|---:|---:|
| 1 | Parts 1 and 2, first ever check of the file | 0 | **16.08** | 1 |
| 2 | NEGATIVE CONTROL, `sv` and `dm` swapped in the tuple | **42** | 1.75 | 1 |
| 3 | control reverted, re-verified | 0 | 1.70 | 1 |
| 4 | Part 1b added, `L.Absorption` pulled in | 0 | **6.35** | 1 |
| 5 | final re-verification of the file as it stands | 0 | 1.81 | 1 |

**Run 1's 16.08 s is not a cold figure.** Every dependency interface was
already built, so this measures the probe and the interface load only. A cold
build of the closure is not measured here.

**RUN 2 IS THE POINT OF THE TABLE.** A green run on a new file proves nothing
until you have seen the file go red. I swapped two components of one tuple and
Agda refused with exit 42, naming the expected type
`⟨ ... (O.G ∷ D ∷ []) (L.Coding.Model.svAt zero) ⟩` against `O.dm`. **So the
tuple is really elaborated, and the four conjuncts sit in the order `InjCode`
declares.** MEASURED.

## 2. THE TERM, AND ITS THREE PARTS

The probe is `agents/tasks/LJ-1-326/ProbeLJ1326A.agda`, 121 lines, of which 54
are code and 25 of those are the module header and the imports.

### 2.1 Part 2, the debt-2 miniature: `InjL κ (𝒫 κ)`

**14 code lines**, `:101-120`. Hypotheses: `zf : ModelL.isZFModel`, `κ : S`, and
`oκ : IsOrd (fst κ)`. Nothing else. No cardinal hypothesis, no infinity
hypothesis, no square law.

The whole content is the subset witness, at `:105-112`:

```agda
sub : (z : V ℓ) → ⟨ z ∈ fst κ ⟩ → ⟨ z ∈ fst (𝒫 κ) ⟩
sub z z∈κ = subst ⟨_⟩ (sym (℩-spec (hasPower κ) zS)) zS⊆κ
```

`℩-spec (hasPower κ)` is the power-set specification read straight off the model
record (`src/FOL/ZFModel.lagda.md:199` for the field, `:287-288` for `𝒫`,
`:123-124` for `℩-spec`). The subset itself is the ordinal's own transitivity,
`oκ .fst`. Then `InclGraph κ (𝒫 κ) sub` carves the graph and
`(I.sv , I.dm , I.ij , I.ran)` is the `InjCode`.

**This closes `[LJ-1.325]`'s open item 2** (`lj-1.325-report.md:466-468`,
「That `𝒫 κ` accepts the inclusion's subset witness. INFERRED」). It is MEASURED
now.

### 2.2 Part 1, miniature A: the tuple at the ordinal inclusion

**7 code lines**, `:61-70`. `OrdIncl C oC D D∈C` gives `InjCode O.G D C` and
`InjL D C`. I wrote it GENERIC in the ordinal pair rather than at one delivered
pair, so it measures the TYPES and not one site.

**This closes `[LJ-1.325]`'s open item 1** (`lj-1.325-report.md:463-465`).

### 2.3 Part 1b, miniature A at debt 1's own site (P-l)

**8 code lines**, `:81-91`. `ShiftGraph γ oγ γ∉ω numerals`
(`src/L/Absorption.lagda.md:538-605`) gives `InjCode SG.G SG.D SG.C` and
`InjL SG.D SG.C`.

**I ran this because P-l forbids transferring a measured cure by analogy.** The
`InjChain` result does not price the `Absorption` site. So I re-measured at the
`Absorption` site, and it is the ruling's own named miniature:「code `absorbs`
at its smallest site into an `InjCode` witness」
(`agents/tasks/LJ-1-323/lj-1.323-ruling.md:258-260`). **GO, at 8 lines.**

## 3. WHAT I RE-DERIVED MYSELF (C-44)

`[LJ-1.325]` funded this task. I re-read every claim I act on.

| claim | where I checked it | verdict |
|---|---|---|
| `InjCode` is a four-part product | `src/L/Cardinal.lagda.md:223-228` | CONFIRMED |
| `Carve` proves the four, under「THE FOUR CONJUNCTS」 | `src/L/InjChain.lagda.md:513-547` | CONFIRMED, and the heading is at `:513` |
| `Comp` proves the four for the composite | `src/L/InjChain.lagda.md:376-422`, heading at `:376` | CONFIRMED |
| `Carve` proves the four in `Absorption` | `src/L/Absorption.lagda.md:448-498`, heading at `:448` | CONFIRMED |
| all three are opened `public` | `src/L/InjChain.lagda.md:598`, `:607`, `src/L/Absorption.lagda.md:604-605` | CONFIRMED, and my three modules reach them from outside |

**AND ONE FINDING `[LJ-1.325]` DID NOT STATE.** `Comp`
(`src/L/InjChain.lagda.md:314-323`) takes the four conjuncts of BOTH arguments
as PARAMETERS and returns the four conjuncts of the composite. **Its interface
is `InjCode`'s four fields written out twice.** So the coded composition needs
no adapter at all: it already consumes and produces exactly the coded shape.
The chaining device for debt 1 is delivered and coded today. MEASURED, by
reading the parameter list.

## 4. WHAT EACH DEBT'S PRICE BECOMES

### 4.1 Debt 2, the reverse bound `InjL δ (𝒫 κ)`

**About 600 lines, and it is STILL A SURVEY. My measurement does not price it.**
What changed is the BASIS and the risk.

- **The coded face of the reverse bound is MEASURED at 14 lines.** It is no
  longer part of the 600, and it is no longer a hypothesis.
- **`[LJ-1.325]`'s NO-GO branch is closed.** It said a NO-GO would make debt 2
  UNPRICED (`lj-1.325-report.md:188-190`). That branch is dead.
- **The 600 now prices ONE object and nothing else: the order-type predicate in
  the object language**, with its adequacy in both directions. Every other part
  of the leg has a delivered coded device.
- **What my term does NOT give.** `InjL κ (𝒫 κ)` is one cardinal step too low.
  The lift to δ is not an inclusion: an ordinal α with `κ ⊆ α` and `α ∈ δ` is
  not a subset of `κ`, so `InclGraph` does not reach the pair `(δ , 𝒫 κ)`.
  MEASURED, by the type: `InclGraph` demands
  `(z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩`, which at `(δ , 𝒫 κ)` is exactly
  the false statement. **So the 600 is not reduced by this probe.**

### 4.2 Debt 1, the coded final injection

**The adapter half is MEASURED at 8 lines at `absorbs`'s own site.** The
ruling's about 800 (`lj-1.323-ruling.md:254-255`) is refuted AS A PRICE FOR THAT
HALF. `[LJ-1.325]`'s about 25 is an over-estimate for the same half, and its
NO-GO branch (`lj-1.325-report.md:121-122`) is closed.

**THE UNPRICED HALF IS UNTOUCHED, AND IT NOW DOMINATES ENTIRELY.** The brief
told me to stop if I met it. I did not meet it, because I did not attempt it.
Here is where it bites, MEASURED by reading the types:

- `pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫` at `src/L/InjChain.lagda.md:175-176` is a
  bare ambient function. `pairω-inj` at `:178-182` is its injectivity.
  `squareω : sq ω` at `:184-185` is the pair of the two.
- `Comp` at `src/L/InjChain.lagda.md:314-323` demands eight arguments: the four
  conjuncts of each side. **A bare function and an injectivity proof supply
  none of the eight.** So the pairing leg cannot enter `Comp`.
- **The gap is a MISSING FORMULA, not a missing adapter.** Every carve in the
  tree runs through `hasSeparationL b φ` with `φ : Formula S 1`
  (`src/L/InjChain.lagda.md:471-472`, `:480`). `pairω` has no `φ`. That is
  `[LJ-1.325]`'s probe B and this task must not attempt it.

**So debt 1 = about 8 lines MEASURED per carved leg, plus an UNPRICED term per
uncarved leg.** The count of uncarved legs is not measured here, and I do not
guess it.

### 4.3 The honest summary line

**One survey price is re-based, not lowered. One survey price is refuted for its
adapter half and left unpriced for its dominant half.** A probe that measures
ten lines cannot price six hundred, and this report does not pretend otherwise.

## 5. DD4, AND YOUR TERM PULLS `InjChain` BACK IN

**NAME THE AXIS (C-46).** DD4's own axis is AC closure against GCH closure,
fixed in code at `scripts/measure/ledger.py:50`.

**YES. MY TERM PULLS `InjChain` BACK INTO THE GCH CLOSURE, AND THE PRETTY
NUMBER GOES AWAY.**

MEASURED at HEAD with a replication that reuses `ledger.py`'s own
`import_graph`, `closure` and `count`, and adds the import edges a landed term
would create. It runs no Agda. **It reproduces `[LJ-1.325]`'s HEAD row digit for
digit on all four figures, so it is calibrated.**

| scenario | GCH closure | SHARED | share |
|---|---|---|---|
| HEAD today | 48 masters, 8,889 lines | 43 masters, 7,596 lines | 41.1% of 18,490 |
| with debt 2's term (`InjChain`) | **49 masters, 9,391 lines** | 43 masters, 7,596 lines | **40.0% of 18,992** |
| with debt 1's term too (`Absorption`) | **51 masters, 9,953 lines** | **44 masters, 7,632 lines** | **39.1% of 19,518** |

**Read the rows and not the share.** Landing debt 2's term alone adds one master
and 502 lines to the GCH side and adds NOTHING to SHARED, so the share FALLS.
Landing both terms brings back `Absorption`, and `L/Axioms/Infinity` returns to
SHARED with it.

**AND THE THIRD ROW IS THE FINDING.** 51 masters, 44 shared and 39.1 percent are
`[LJ-1.325]`'s PRE-RESTATEMENT figures (`lj-1.325-report.md:296-305`). **So the
2.0-point rise the restatement produced is an artifact that the proof will hand
straight back.** The understatement `dev/ledger.toml:204` names is real and this
measurement bounds it: about 1,028 lines on the GCH side and 36 on SHARED.

**DD4's substance, and it is better than the number.** The three carve sites are
written GENERIC and the coded layer is shared by construction: `Carve` takes the
bound, the subset witness and the separation field as PARAMETERS
(`src/L/InjChain.lagda.md:463-472`), and `Comp` takes the four conjuncts of both
sides as parameters. **My three modules add ZERO new mathematics.** Each is a
tuple over names the tree already exports. That is what「maximize the code the
two proofs share, and write it generic」buys, measured: the adapter cost is 8
lines because the supplier was written generic.

## 6. THE ABORT CRITERION, ANSWERED ROW BY ROW

| the brief's row | outcome |
|---|---|
| **`InjL κ (𝒫 κ)` BUILDS** | **YES.** 14 lines, `ProbeLJ1326A.agda:101-120`. Section 4 re-prices both debts |
| IT DOES NOT BUILD | not taken |
| THE INCLUSION IS NOT AT THE PAIR YOU NEED | not taken for `(κ , 𝒫 κ)`. **It IS taken for `(δ , 𝒫 κ)`**, section 4.1 |
| IT NEEDS THE SQUARE LAW LEG | not taken. No part of my term touches `sq`. Section 4.2 names where the leg bites for debt 1 |
| A WALL | not taken. Longest single invocation 16.08 s |

## 7. WHAT I DID NOT SETTLE

I name these rather than guess.

1. **The 600 for debt 2.** Untouched. It stays a survey of the order-type
   predicate.
2. **How many legs of debt 1's final chain are uncarved.** Not counted. C-42
   says a refutation measures ONE site; the same holds for a GO. The sweep is a
   separate task.
3. **`pairω`'s description.** Not attempted, by the brief's order.
4. **A cold check cost.** Every figure here is warm. A sibling was measuring
   check times and I kept my runs short.
5. **Whether the three tuples would survive as `src/` exports.** A probe is not
   a landing. The exports, their names and their placement are the
   orchestrator's call.

## 8. PROHIBITIONS, ANSWERED

- **Writes:** `agents/tasks/LJ-1-326/` only, two files, this report and
  `ProbeLJ1326A.agda`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda:** five invocations, one at a time, load counted before each,
  `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- The DD4 replication script sits in the session scratchpad, outside the
  repository.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-325/lj-1.325-report.md`, READ WHOLE.** Line read
  `:463-468`, section 9 items 1 and 2:「That `InjCode G D C` accepts
  `(sv , dm , ij , ran)` ... INFERRED, never MEASURED」and「That `𝒫 κ` accepts
  the inclusion's subset witness. INFERRED」. **TOOK: both items, and this
  probe MEASURES both.** Its four-conjunct table at `:44-48` is confirmed at
  every locator.
- **`agents/tasks/LJ-1-323/lj-1.323-ruling.md`, READ `:226-273`.** Line read
  `:258-260`:「the widest unmeasured term is the interning of ONE delivered
  ambient injection, and the decisive miniature is to code `absorbs` at its
  smallest site into an `InjCode` witness」. **TOOK: that miniature, and RAN it
  as Part 1b. GO at 8 lines.** So the ruling's own gate is discharged, and its
  about 800 is refuted for the half it names.
- **`archive/dev/TASKS-archived.md`, line read `:53`** (T18, the GCH scope
  gate, NO-GO). **TOOK, SHAPE ONLY:** the retired route also gated a GCH-side
  price with one small probe before funding it. **WHAT WOULD NOT TRANSFER:** the
  retired route built coded objects over the rud presentation, and every number
  in that file prices that presentation. `dev/PLAN.md:787` records the route as
  retired. So no figure there is a comparable for a `Carve` site, and its
  coded-object technique cannot be lifted: `Carve` runs on `hasSeparationL` and
  a `Formula S 1`, which the rud route did not have in this form.

## 10. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`. IT BEARS.** READ `:66-90`.
  Line read `:75-81`:「A cardinal inequality is a truncated existence of an
  injection」, HoTT Book Definition 10.2.7. **TOOK: `InjL` is `∥ Σ ∥₁`, so my
  term needs no untruncation and the tuple goes straight under `∣_∣₁`.**
  **THE ONE-LINE ANSWER THE BRIEF ASKED FOR: the classical route needs ONE
  thing my assembly does not give, and it is not Cantor.** A set theorist gets
  `κ⁺ ≤ 2^κ` by mapping each α below κ⁺ to a well-order of κ of type α. That
  needs a predicate「W codes a well-order of order type α」in the object
  language, plus a canonical choice of W per α. My assembly gives the coded
  face for free once the subset witness exists; **it gives no order-type
  predicate, and `:68-70` says the selection device is a definable well-order
  plus a universal guard, which the project owns as `orderL` and `Pick`.** So
  the missing part is the predicate and not the selection.
- **`dev/literature/devlin-II5.md`. IT DOES NOT BEAR ON THIS PROBE.** READ
  `:145-166`. **WHY NOT:** Devlin's 5.6 proves the FORWARD bound,
  `𝒫(κ) ⊆ L_{κ⁺}`, and leaves the reverse to the reader. My term is on the
  reverse side and one cardinal step below it. Nothing in 5.6 prices a coded
  tuple.
- **WHY NOT re-fetched:** both digests landed with locators and I take only
  statement-level facts from them.
