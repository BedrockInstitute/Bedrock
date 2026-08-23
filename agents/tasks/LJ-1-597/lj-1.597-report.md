# [LJ-1.597] report: the graph of one step

## HEAD
head_slot: coder
machine: shared
task: LJ-1.597 (attempt 2, after the overturn of attempt 1's NO-GO)
obligation: agents/tasks/LJ-1-597/Probe597.agda::step-graph
verdict: NO-GO, stated the [LJ-1.584] way: green probe, no hole, no
postulate, the obligation's name not in the probe, and the stop file
`agents/tasks/LJ-1-597/review-of-step-graph.md` ON DISK.

The report was a skeleton before any proof Agda and was filled as each
answer landed (C-22). Nothing landed in `src/`. Nothing is postulated. No
row of the probe puts `step`, `branch` or `stage-card-upper` into a
conversion problem; `[LJ-1.584]` measured that one such row does not
terminate (`agents/tasks/LJ-1-584/runs/w3b-1.out`). The program set
`GHCRTS="-A64m -I0 -M2g"` on this pane (caliber recorded in every run
file). I did not set it. One Agda process at a time. No commit, no push.

## W3: `step`, RE-ASCRIBED ALONE

`runs/W3.agda` was written first and typechecked alone for THIS attempt:
`runs/w3-2.out`, GREEN, exit 0, 1.49 s. The brief's estimate was about 12
lines under 90 s; the slice is 40 lines including its header and import
block, and the time was inside the estimate.

What W3 says, and what the D-10 read of the chapter found:

- **IT TAKES** a stage `α : S`, the induction hypothesis
  `IH : (δ : S) → ⟨ δ ∈ˢ α ⟩ → P δ`, and then `P α`'s own fields: `oα :
  IsOrd α`, `α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩`, `infα : ⟨ α ∈ˢ ω ⟩ → ⊥`
  (`src/L/StageCardinal.lagda.md:561`, `:530-532`).
- **IT RETURNS** `P α`: a function `⟪ Lset α ⟫ → ⟪ α ⟫` with its
  injectivity (`:530-532`).
- **IT CALLS** `limit-step` and `branch`, in ONE equation
  (`:562`): `step α IH oα α∈suc infα = limit-step α α∈suc oα infα
  (branch α oα α∈suc infα IH)`. The full call table is the next section.

In the probe: `step` (`Probe597.agda:118`), imported from the W3 slice
and not restated; `step-fn`, the function part of the step's output at
one stage, named once (`Probe597.agda:126-130`). `step` sits in types
and in one projection and nowhere else.

## WHAT step CALLS

Every call in the transitive closure of the step's one equation, each at
`file:line` in `src/L/StageCardinal.lagda.md`, each marked. INTERNAL
means a predecessor measured the ingredient expressible in the object
language; the measurements are named.

| call | site | what it is | formula? |
|---|---|---|---|
| `limit-step` | `:396-403` | assembles `LimitStep.h` with `D := DefOf.defSet`, `inv := 𝒟ₒ-inv` | wrapper |
| `branch` | `:534-559` | the `ih` the step supplies; the recursion's own values one stage down | **NO, ingredient (iv)** |
| `LimitStep.h` | `:350-351` | `leastOf` over the ordinal order of `class-pred`'s class | INTERNAL, ingredient (ii) |
| `OrdSWO.ordSWO` | `:258-264` | the ordinal strict order on `⟪ α ⟫`; `_≺_` is `∈ᵗ` (`:230-231`) | INTERNAL |
| `class-pred` | `:319-323` | the selection predicate; five ingredients, table below | mixed, see below |
| `DefOf.defSet` | `:400` | `D`; it is `𝒟ₒ` | INTERNAL, ingredient (i): `[LJ-1.584]` (`:400-401`) |
| `𝒟ₒ-inv` | `:401` | `inv`; the inverse witness | INTERNAL |
| `Lset-out`, `member` | `:326-333` | nonemptiness of the class | INTERNAL |
| `Bound.pair` | `:68-69` via `:283` | the packing in the value equation; `refl`-equal to `fst (sq α α∈suc infα)` (`pair-is-sq`, `Probe597.agda:180-184`) | **NO, ingredient (iii)**: `sq` is the arbitrary ambient parameter (`:17-19`), `[LJ-1.533]`'s wall (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`) |
| `cnt` | `:288-289` | `fst (Bound.formula-bound (ih m))`; `refl`-measured by `[LJ-1.594]` (`Probe594.agda:252-263`) | **NO, ingredient (iv)** |
| `Bound.formula-bound` | `:196-206` | the counting bound: `count-bound` (`:128-130`) packs the formula's code through `pair` and through `g = ih m` | mixed: its packing calls (iii) and its input is (iv); the code/numeral machinery itself is internal |
| `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1` | `:285-286` | the meta syntax the existential of `class-pred` ranges over | **UNMEASURED at this carrier**, ingredient (v): the coded-copy machine exists (`src/L/Coding/CodeSet.lagda.md:300-301`, `:440-443`), no task has instantiated it here |
| `ord-tri`, `mem-ord`, `suc-ord`, `∈-irrefl` | `:537`, `:542`, `:543-544`, `:547` | the branch's ordinal dispatch | INTERNAL (ordinal machinery) |
| `comp-inj` | `:501-503` | composition of injections | INTERNAL |
| `Emb.emb` | `:507-515` | the inclusion `δ ⊆ α` at presentation grain, a membership fiber | INTERNAL |
| `WOEmb.ω-inj` | `:519-528` | `ω`'s inclusion, by trichotomy and `Emb.emb` | INTERNAL |
| `fin-inj` | `:488`, called `:551` | the ω-base: `finite-stage-inj :485` through `StageOrder.tally`, value `leastOf natOrder` (`:440-453`) | **UNMEASURED: no task has measured whether the `Tally` has a formula** |
| `IH` | `:556` (infinite case), `:549-550` (ω case) | the induction hypothesis | **NO: the target one stage down** (`[LJ-1.594]`, ingredient (iv)) |

The five ingredients of `class-pred`'s value equation, `[LJ-1.594]`'s
upheld table (`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:33-47`,
measured by `class-pred-is`, `Probe594.agda:283-300`): (i) `D` INTERNAL,
(ii) leastness INTERNAL, (iii) the pairing NO FORMULA, (iv) the count
through the branch NO FORMULA, (v) the meta syntax UNMEASURED at this
carrier. The value equation itself, the only occurrence of the value `y`:

    fst (sq α α∈suc infα) (m , cnt m φ) ≡ y

In the probe: `branch-type`, TYPE ONLY (`Probe597.agda:137-141`);
`fin-inj-type`, TYPE ONLY (`:150-151`); `pair-is-sq`, `refl`
(`:180-184`); `cnt-type` and `class-pred-type`, TYPE ONLY (`:200-207`,
`:222-229`). Why the last two are type-only is in THE FLOOR below.

`[LJ-1.584]`'s theorem that every value of the injection is a value of
the pairing (`agents/tasks/LJ-1-584/Probe584.agda:186-206`, GREEN)
applies at the step with the step's own supply `branch` (`:562`), so at
the STEP, not only at the whole injection, every value of the graph's
subject is an `sq`-packed value: the value equation's only `y`-occurrence
is the `sq`-application side. Attempt 1 of this task carried that
application as a green row under `-M4g` (`runs/final-4.out`); this
attempt cites it and does not re-apply it (THE FLOOR below).

## THE RECURSION RE-ASSCRIPTION

The brief ordered the chapter's TYPE read against its own SENTENCE, and
the critic required the comparison recorded. **They agree.**

- The record `Recursion` (`src/L/Recursion.lagda.md:103-108`): `dom : S`,
  `graph : Formula S 2`, `funct : ... isContr ...`.
- The record `Definition` (`src/L/Recursion.lagda.md:272-279`): `dom`,
  `fn : S → S`, `graph : Formula S 2`, `defines`, `only`.
- The sentence (`src/L/Recursion.lagda.md:259-261`): internalizable WHEN
  the graph is expressible, nothing about shape, depth, descent or clause
  complexity in the condition.

Both the type and the sentence are the graph of the VALUE function
`S → S`. **NEITHER is the graph of the step functional
`(α, IH) ↦ P α`**: `IH` is a meta-language function and the output is an
injection between presentation types; neither is an element of `S`. The
chapter separates exactly this case in its prose on encoded indices
(`src/L/Recursion.lagda.md:207-231`). So the obligation the brief names
is the `Definition`-shaped graph of the step's FUNCTION PART at one
`(α, IH)`. That is what `Graph` states, and the brief's own phrasing
("a `Formula` expressing the graph of `stage-card-upper`'s `step`")
reads the same way. The chapter supplies the CONDITION and not the
formula: its own closing prose says writing the graph "is the work"
(`src/L/Recursion.lagda.md:324-325`).

## THE GRAPH

**THE TYPE IS WRITTEN AND NOT INHABITED.** `Graph`
(`Probe597.agda:269-285`): a `Formula S 2` ψ, read at `(y ∷ x ∷ [])`,
with BOTH readings at `fn := step-fn α oα α∈suc infα IH` on the members
of `dom := LsetS α oα`:

- **the `defines` direction**: for every member `x` of the stage and
  every `y` equal to the step's value at `x`'s index, the formula holds;
- **the `only` direction**: whatever the formula holds of, at a member
  `x`, is the step's value at `x`'s index.

Arity 2, value variable first, index variable second: the internal
chapter's own order (`src/L/Recursion.lagda.md:276-278`). The arity-3
neighbour `[LJ-1.568]`'s `Def` differs by a spectator variable no
direction uses; no row converts the two arities because the syntax has
no substitution and no weakening (`src/FOL/Syntax.lagda.md:157`), so no
equivalence is claimed and the stop does not rest on one.

**THE ATOMS THAT BLOCK IT**, at the grain the brief asked for. The value
equation of the step's graph is
`fst (sq α α∈suc infα) (m , cnt m φ) ≡ y` (`class-pred`,
`src/L/StageCardinal.lagda.md:319-323`, written out by `[LJ-1.594]`'s
green `refl`). TWO calls in that one equation have no formula:

1. **THE PAIRING (iii).** `B.pair` is `fst (sq α α∈suc infα)` applied,
   `refl` at this site (`pair-is-sq`, `Probe597.agda:180-184`). `sq` is
   the module parameter carrying injectivity and nothing else
   (`src/L/StageCardinal.lagda.md:17-19`). `[LJ-1.533]`'s wall, measured
   three times (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`), with
   the type-level reason: every L-element generator takes a `Formula`
   (`src/L/Axioms/Full.lagda.md:144`, `:277-280`). `[LJ-1.584]` named
   this atom for the whole injection
   (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:33-45`).
2. **THE COUNT (iv).** `cnt m φ` is `fst (Bound.formula-bound (ih m)) φ`
   (`src/L/StageCardinal.lagda.md:288-289`), and at the step's own site
   `ih` is `branch` (`:562`): at every infinite member stage the
   induction hypothesis itself (`:556`), the target one stage down; at
   `ω` the IH at `ω` (`:549-550`); at every finite member stage `fin-inj`
   (`:551`) through the `Tally` (`:488`, `:485`, `:440-453`), whose
   describability NO TASK HAS MEASURED.

**WHAT THIS ADDS TO `[LJ-1.584]` AND `[LJ-1.594]`.** The brief split the
scope: the graph of ONE STEP with `IH` a PARAMETER of the obligation's
type, so the formula may vary with `IH`. It does not help: a
`Formula S 2` is finite syntax with constants in `S`, and the value
equation carries `cnt m φ` at the unboundedly many member stages below
`α`, so the recursion enters through the count. **A FORMULA FOR THE
PAIRING ALONE DOES NOT DISCHARGE THE STEP'S GRAPH**, and the finite base
under the count is unmeasured. Four tasks said the injection has no
formula; this return names the two calls inside the one step that carry
no formula, and the unmeasured `Tally` under the second of them.

**THE STOP.** `agents/tasks/LJ-1-597/review-of-step-graph.md`, on disk,
states the NO-GO, the re-ascription, the not-false rows and what would
reopen it: `[LJ-1.594]`'s chapter route (ingredient (v) first, stage
question `[LJ-1.86]` answered in the brief,
`archive/dev/LJ-dispatch-index.md:160`); a measurement of the `Tally`
base; or `[LJ-1.584]`'s truncated `InjL` reopener, which never describes
the computed injection. The stop file also records the C-42 position:
the refuted shape is the one both predecessors already swept
(`[LJ-1.584]` at
`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:98-104`,
`[LJ-1.594]` at
`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:110-117`), and
this task adds a site to that count, not a new shape.

## THE FLOOR

Measured, not estimated, and the measurement restructured the probe.

- **The floor of the obligation's frame**: `runs/Floor.agda`
  (sections 0-2 of the probe: W3, the call rows, the `Graph` type),
  GREEN `runs/floor-1.out`, `runs/floor-2.out` at 3.54 s (warm
  interfaces, `-M2g`).
- **The D-10 truth rows**: `runs/D10.agda` (`vl→def`,
  `refuting-def-refutes-V=L`, sections 0+3), GREEN `runs/d10-1.out`,
  `runs/d10-2.out` at 3.69 s.
- **The probe**: GREEN, three runs: `runs/final-13.out`,
  `runs/final-14.out` at 3.62 s, `runs/final-15.out` at 3.82 s.
- **W3**: `runs/w3-2.out`, GREEN, 1.49 s.

**THE RESTRUCTURING, AND WHY THE PROBE IS SLICED.** The full file in ONE
process died repeatedly at the OPERATING SYSTEM's hands: `runs/final-5.out`
(importing `[LJ-1.594]`'s whole file), `runs/final-7.out`, and
`runs/final-9.out` to `final-12.out` (SIGKILL, exit 137, no RTS
`Heap exhausted` message, so NOT an RTS `-M2g` wall in the program's
sense, `scripts/pod/facts.py:70`): the machine is shared, load was above
30, and system swap was near full (`vm.swapusage` free below 1.6 GB
during the kills; my process itself consumed several hundred MB of swap
per attempt). `runs/final-6.out` and `final-8.out` between the kills were
clean Agda scope errors (exit 42), which is how the missing `_↪_` scope
and the `fin-inj` site were fixed. Per the heap-wall clause I
restructured in this dispatch and tested each shape under the same cap:

1. `[LJ-1.594]`'s two `refl` rows re-proved inline instead of importing
   its file (whose import drained the machine first,
   `runs/final-5.out`): still killed.
2. `[LJ-1.584]`'s theorem-application row and with it the `P584` import
   dropped, cited instead: still killed.
3. The file SPLIT: sections 0-2 (`Floor`), sections 0+3 (`D10`): BOTH
   GREEN separately, and the probe (0-2 plus a pointer to `D10`) GREEN.

So the probe's final shape is the measured one: every row typechecks
under the same cap in its own process, the obligation's name is absent,
and nothing is postulated. A slice is not a weaker probe; it is the
shape that survived the machine. The cold elaboration cost of the
combined file is not separately priced: every attempt to price it was
the kill.

## WHAT THIS MEASUREMENT COST

- My pane's caliber: `-A64m -I0 -M2g` (wide). Attempt 1's comparable
  runs were at `-M4g` (`runs/accept-1.out`), so ITS seconds and mine are
  not comparable, and I do not compare them.
- Green runs under this caliber: W3 1.49 s; probe 3.62 s, 3.82 s (warm);
  `Floor` 3.54 s; `D10` 3.69 s. Four OS kills before the split, each
  at 4-96 s of wall time.
- The probe is 320 lines, of which the obligation's type is 17
  (`Probe597.agda:269-285`). The brief estimated about 190 lines with
  about 50 for the obligation; the probe carries the call table's
  type-only rows as well, and the obligation's type is smaller than
  estimated.

## WHAT THE NEXT BRIEF NEEDS

1. **The split this task measured stands even if `[LJ-1.596]`'s machine
   does not fit**: the two atoms are in the CONDITION every route
   wanted, per the brief's own reading of `[LJ-1.568]`
   (`agents/tasks/LJ-1-568/Probe568.agda:377`, coding is describing).
2. **The cheapest next measurement is the `Tally` base**: whether
   `fin-inj`'s value (`leastOf natOrder` over the tally,
   `src/L/StageCardinal.lagda.md:440-453`) has a formula. No task has
   measured it, and ingredient (iv) cannot be priced whole while its
   ω-base is unmeasured. It is smaller than this task was.
3. **The chapter route needs the stage question answered in the brief**:
   `AllCodes` at this carrier exists but the proof cannot choose the
   stage (`archive/dev/LJ-dispatch-index.md:160`, `[LJ-1.86]`), and the
   live chapter is `src/L/Coding/CodeSet.lagda.md`, not the retired
   `L.Rud.CodeSet` (`dev/ARCHIVE.md:267`, read and verified this
   dispatch).
4. **Do not re-dispatch "the formula for the step" at this price.** The
   pairing-only hope is dead at the step: the count is in the same
   equation.

## W2 AND W4

**W2.** The mathematics is written once at a generic carrier and
instantiated: the probe is stated at the generic telescope
`{ℓ} lem α₀ oα₀ sq`, the chapter's own, and `Graph` is stated at the
generic `(α, oα, α∈suc, infα, IH)`; both trophies' consumers instantiate
the same statement. Nothing landed in `src/`, so no fixed-form chapter
was written and no deadline conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is exactly the sliced probe that
survived the machine; I did not have to pay for a worse shape and then
compare.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:160`: "| LJ-1.86 | Is there a stage
  containing AllCodes A | EXISTS; proof cannot choose it | AllCodes-stage
  is green. But lam is a module parameter at every frame, so the
  obligation moves to the frame |". This is the recorded stage-choice
  failure the stop file's reopen route names.
- **`archive/dev/JOURNAL-archived.md` READ AND DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired
  route". The retired route's journal does not measure `step` or its
  calls.
- **`archive/dev/JOURNAL.md` READ AND DECLINED.**
  `archive/dev/JOURNAL.md:1`: "# ARCHIVED 2026-08-20". A retired journal;
  the live record of this instance is the runs directory and the critic's
  review.
- **`dev/ARCHIVE.md` READ AND USED.**
  `dev/ARCHIVE.md:267`: "| `L.Rud.CodeSet` | `src/L/Rud/CodeSet.lagda.md` |
  The formula codes over a carrier as one sealed family: membership
  definitional, decode untruncated, every code unconditionally a closure
  member." Read to keep the stop file's reopen route on the LIVE chapter
  (`src/L/Coding/CodeSet.lagda.md`) and not the retired one. No module is
  retired by this return and the registry is unchanged.
- **`archive/dev/ORCHESTRATION.md` READ AND DECLINED.**
  `archive/dev/ORCHESTRATION.md:1`: "# ORCHESTRATION: the orchestrator's
  operating rules". The archived process document; it does not measure
  `L.StageCardinal`.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:83-84`: "So a proof that
  only needs cardinal arithmetic never needs an injection as data, and
  the untruncation question does not arise in the classical texts." This
  is the law behind the truncated `InjL` reopener the stop file names.
  Also read: `:146-148`, the `leastOf` payload law, on why the square law
  arrives truncated only.
- **`dev/literature/devlin-II5.md` READ AND DECLINED.**
  `dev/literature/devlin-II5.md:1`: "# Devlin II.5: the Condensation
  Lemma and the GCH in L". Condensation is not this site; this task
  measured one step's value equation.
- **`dev/literature/digest.md` READ AND DECLINED.**
  `dev/literature/digest.md:1`: "# Digest: the orthodox form of the rud
  route, pinned from the collected literature". The rud-route digest
  does not measure `L.StageCardinal`'s `step`.
- **`dev/literature/terms-2026-08.md` READ AND DECLINED.**
  `dev/literature/terms-2026-08.md:1`: "# The terminology dossier:
  fourteen renderings for the owner's ruling". A terminology dossier;
  no term of this return waits on it.
- **`dev/literature/glossary-review-2026-08.md` READ AND DECLINED.**
  `dev/literature/glossary-review-2026-08.md:1`: "# Glossary review: the
  119 pre-protocol entries". A glossary review; this return adds no
  glossary entry (the Boundary's two-dispatch rule).
