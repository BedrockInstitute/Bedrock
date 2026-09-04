# review-of-carve-rebounded: the re-bound at `step 2 gamma` is false at general gamma

**NO-GO.** `carve-rebounded`, the corrected target named by
`agents/tasks/LJ-1-706/lj-1.706-report.md:15` and funded by this brief,
is not inhabited and cannot be: the certificate it needs contains a
piece that is refuted at general gamma. The refutation is a term:
`refuted-pin` (`agents/tasks/LJ-1-712/Probe712.agda:217-220`), green,
no postulates, exit 0. The probe is green as a whole: median 1.68 s
over three forced rechecks (`runs/recheck-1.out`, `runs/recheck-2.out`,
`runs/recheck-3.out`). The witness meter reads `missing`, `1 UNRESOLVED
of 1`, `probe_red=False` (`runs/meter-1.out`).

**THIS IS NOT A REFUTATION OF `Below`.** `Below` itself is untouched:
no term of its negation was built, and the door machinery survived
everything this task did to it. The stop is at the CERTIFICATE, one
level below the statement, and it kills the re-bounding route, not the
target.

## What the corrected target actually asks, and what it forgot

`[LJ-1.706]`'s D-10 section priced the constants of the relativized
pair-graph as TWO: the ordinal `gamma` and the stage `Lset gamma`. It
concluded "the constants themselves fit" under `Lset (step 2 gamma)`.
The two constants it counted do fit, and this probe proves both fits as
terms (`Probe712.agda:134-148`, `gamma-fit`, `stage-fit`).

The inventory was incomplete. The readers under `DefBody` pin NUMERAL
constants into the spine, each occurrence of the form
`con (numeralL k)`:

| reader | pin k | site |
|---|---|---|
| `tagAtL` | any k its caller passes | `src/L/Coding/Model.lagda.md:585-586` |
| `keyArityAtL c 1` | 1 | `src/L/Coding/CodeSet.lagda.md:135` |
| `envOneAt` | 0 | `src/L/Coding/Powerset.lagda.md:128-129` |
| `closedAt`, eight clauses | 2,3,4,5,8,9,10,11 | `src/L/Coding/Model.lagda.md:2172-2189` |
| `shapes` / `isTmAt` / `zeroPay` | 0,1 and pins 0..11 | `src/L/Coding/Shape.lagda.md:140-145`, `:160-189` |

These are NOT hypothetical: `DefBody` (`src/L/Coding/Powerset.lagda.md:411-414`)
is inside `DefAt`, `DefAt` is inside `StepBody`
(`src/L/Coding/Sequence.lagda.md:141-146`), `StepBody` is inside
`StepAt` (`:149-150`), and the `StepAt`-instantiated `GraphAt` is inside
`PairGraphAt` (`:329`, instantiated at `:349`), which is the body of
`recordedFo` (`agents/tasks/LJ-1-698/Probe698.agda:73-74`). Every
constructor of that spine is inside `phi_r` after `relativize`
(`src/FOL/Manipulation/Relativize.lagda.md:56-57`, which only turns
unbounded quantifiers into bounded ones and leaves the rest).

So the certificate at ANY tau carries, for each pin k, the piece
`BoundedTm (Below' tau) (con (numeralL k))`, which computes to
`⟨ fst (numeralL k) ∈ Lset tau ⟩`
(`src/FOL/Manipulation/Bounding.lagda.md:63-64`), and
`fst (numeralL k)` is `# k` by
`src/L/Axioms/Numerals.lagda.md:179-181`.

## The refutation, and why it is a theorem and not a gap

At `tau := step 2 gamma` the pin-11 piece is
`⟨ # 11 ∈ Lset (step 2 gamma) ⟩` for every ordinal gamma. It fails at
`gamma := ∅`, where `step 2 ∅` is `sucV (sucV ∅)`, whose members are
only `∅` and `{∅}`. The term:

1. `ord∈Lset→∈`
   (`src/L/Ordinal/Stages.lagda.md:266-268`) turns stage membership of
   an ORDINAL into ordinal membership: `⟨ # 11 ∈ Lset (step 2 ∅) ⟩`
   gives `⟨ # 11 ∈ sucV (sucV ∅) ⟩`. (`# 11` is an ordinal:
   `ord#`, `Probe712.agda:169-171`, from `# suc n ≡ sucV (# n)`,
   vendored `Constructions.agda:163-165`.)
2. `∈sucV-elim`
   (`src/V/Model.lagda.md:218-222`), twice: a member of
   `sucV A` is in `A` or EQUALS `A`. Four cases, all closed:
   - `# 11 ∈ ∅`: absurd by `∅-empty`.
   - `# 11 ≡ ∅`: then `# 1 ∈ ∅` along the numeral chain
     (`#1∈#11`, `Probe712.agda:180-182`), absurd.
   - `# 2 ∈ ∅` (after `# 11 ≡ sucV ∅` and `#2∈#11`): absurd.
   - `# 2 ≡ ∅`: then `# 1 ∈ ∅` by `self∈sucV`, absurd.
   (`no-11`, `Probe712.agda:186-210`.)
3. `refuted-pin` (`:216-222`) lifts the one-instance kill to the
   general row the certificate needs.

The classical shape of the fact: `# 11` has von Neumann nesting depth
11, the members of `sucV (sucV ∅)` have depth at most 2, and
`ord∈Lset→∈` is exactly the row that makes the depth argument exact
inside the tree. No new machinery was built; every link is cited from
`src/`.

## D-10: the corrected target, beside the original

The original corrected target ("re-bound at `step 2 gamma`, the door
lands exactly at `Below`'s stage") is REFUTED at general gamma. Three
shapes stand beside it:

- **R1, the conditional rescue.** The route works verbatim for any
  gamma whose `step 2 gamma` already sits above the pinned numerals'
  stages: there the certificate assembles and the door lands exactly.
  What it owes: the numeral floor `kappa` = the stage of the highest
  pinned numeral (a measurement the tree does not have yet; nothing in
  the tree bounds `fst (numeralL k)` under any stage), and then a
  SEPARATE mechanism for every `gamma < kappa`. Below quantifies over
  all ordinals, so infinitely many small gamma remain; this shape pays
  the route only above the floor.
- **R2, numeral-free readers.** The pins exist because the readers
  name arities with metalevel numerals. The tree already knows the
  cure for exactly this: `CodeSet`'s own prose
  (`src/L/Coding/CodeSet.lagda.md`, "Is a key at some arity") says the
  arity "has to become a bound set", and `ωʟ` plus `ω-specL`
  (`src/L/Axioms/Infinity.lagda.md:69`, `:87-88`) is that set. A
  reader stack rebuilt on the `arityNumAtL` shape instead of
  `tagAtL`'s pinned numeral would carry NO constant beyond
  `LsetS gamma ogamma` and the ordinal, both of which fit
  (`Probe712.agda:134-148`), and the original corrected target would
  then be TRUE. Price: a rewrite of the reader spine, and the adequacy
  equations of every reader touched. This is the shape this review
  recommends pricing first.
- **R3, the flat re-bound.** Keep `phi_r`, re-bound at the flat merge
  of `step 2 gamma` with the numerals' stages. The door lands at
  `Lset (sucV tau*)`, and `Below` then owes a comparison row between
  `sucV tau*` and `step 3 gamma` that is false at small gamma for the
  same reason as the original row: this is `[LJ-1.711]`'s row at a new
  site, not a new route.

## C-42: the sweep

The refuted shape is "a door-route certificate whose constants were
inventoried by hand and found to fit". Sites:

- `agents/tasks/LJ-1-706/review-of-below-from-carved.md`,
  section "The constants themselves fit": the site this task names and
  corrects. Count: this is the one live site; the corrected shapes
  priced there inherited the same inventory error.
- `[LJ-1.704]`'s identification: UNAFFECTED. `bound-of`
  (`Probe698.agda:97-101`) lets `mkBoundedFo` choose its stage, and
  that choice absorbs the numerals' stages with everything else. The
  identification, if it lands, is still true at `sigma_mk`; what dies
  is only its usefulness for `Below` at small gamma.
- `[LJ-1.711]`: not opened by this task. Its brief should be read
  against R3 above before it is dispatched.
- Premise 5's worry was the BINDER count (`[LJ-1.714]`). This task's
  measurement redirects that worry: the binder COUNT never gates the
  certificate, because `relativize` reuses the SAME constant at every
  binder (`src/FOL/Manipulation/Relativize.lagda.md:56-57`) and that
  constant's fit is `stage-fit`, independent of how many binders carry
  it. `[LJ-1.714]`'s count still matters for `[LJ-1.706]`'s overshoot
  argument about `mkBoundedFo`'s own stage, but it cannot rescue or
  kill the re-bounding; the CONSTANTS do, and they kill it.

## What is delivered

`Probe712.agda`, green, no postulates, no holes: Section 1 the frame
and `phi_r`; Section 2 `AtCert` / `rebound-lands`, the door at an
ARBITRARY presented certificate (the brief's W3 question answered by a
term: the door is NOT tied to `mkBoundedFo`'s stage); Section 3
`gamma-fit` / `stage-fit` / `Lset∈suc`, the two constants the review
counted, now inhabited; Section 4 `ord#` / `climb` / `no-11` /
`pin-11` / `refuted-pin`, the formal kill. The obligation name
`carve-rebounded` is absent on purpose; no postulate stands in for it.

**WHAT THE NEXT BRIEF NEEDS.** Decide between R1 and R2 before
`[LJ-1.704]` closes. R2 is the only shape that can make the original
corrected target true as stated; R1 buys the route above a floor whose
measurement (numeral stage bound) does not exist in the tree yet and
would itself be a task. Do not re-dispatch `AtCert`, `rebound-lands`,
`gamma-fit`, `stage-fit`, `Lset∈suc`, `no-11`, or `refuted-pin`: they
are this probe's, green, and importable. The door being general
(section 2) is a fact the campaign can use anywhere a certificate can
be presented, independent of where this stop lands.
