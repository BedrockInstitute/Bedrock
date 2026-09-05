# NO-GO: `rec-graph-at-infinite`

The obligation `agents/tasks/LJ-1-603/Probe603.agda::rec-graph-at-infinite` is NOT in
the probe. This file states why, names the atom, and gives the merge the measurement
earns. **THE LIMIT CASE OF INGREDIENT (iv)'S RECURSION REACHES `sq`, AND IT REACHES IT
TWICE IN ONE VALUE EQUATION.**

**THE PROBE IS GREEN, EXIT 0** (`agents/tasks/LJ-1-603/runs/final-8.out` cold at
111.89 s, `runs/final-9.out` warm at 1.44 s, cap 300 s, caliber `-A64m -I0 -M2g`,
peak 898 MB under the pane's 2 GB). Nothing is postulated, there is no hole, `--safe`
is on, and nothing landed in `src/`. No weaker term is offered under the obligation's
name: that is `[LJ-1.597]`'s discipline
(`agents/tasks/LJ-1-597/Probe597.agda:5-8`).

## THE OBLIGATION AND ITS TYPE

The statement is `W3.RecGraphInf` (`agents/tasks/LJ-1-603/runs/W3.agda:174-180`), in
the campaign's fixed `Graph` shape (`agents/tasks/LJ-1-597/Probe597.agda:269-285`,
also `[LJ-1.601]`'s): a `Formula S 2`, value variable first and index variable second,
with `defines` and `only` (`src/L/Recursion.lagda.md:272-279`), at the function part
of the route's delivered recursion AT an infinite member stage, read on the members
of `Lset δ`. The index `W3.InfStage` is the limit case's own index: the stage with its
ordinal data and the witness `ω ∈ δ` that selects the branch's limit case
(`src/L/StageCardinal.lagda.md:545`, `:555-556`). The subject `W3.val` is the step's
function part AT the member stage, one unfolding of the assembly's `∈-induction`
(`src/L/StageCardinal.lagda.md:566`), with the branch below the member stage abstract.

The obligation is a term of that type at every index and branch. None is delivered.

## THE MEASUREMENT

Seven `refl` rows at the MEMBER stage (`Probe603.agda`, section 1), `[LJ-1.594]`'s
discipline one stage down. The chain:

1. The step at the member stage is `LimitStep.h` with the site's `D` and `inv`
   (`step-at-member`; `[LJ-1.594]`'s `D-at-the-site` at `Probe594.agda:227-234`).
2. The value is the ordinal-least witness of `class-pred`
   (`value-is-leastOf`; `src/L/StageCardinal.lagda.md:349-351`).
3. **`class-pred` written out, and the value y occurs ONLY on the `sq`-application
   side** (`class-pred-at-member`): the witness is `m`, `φ` with
   `D (⟪ δ ⟫↪ m) φ ≡ ⟪ Lset δ ⟫↪ x` and
   `fst (sq δ δ∈suc infδ) (m , cnt m φ) ≡ y`.
4. The packing is `sq` applied and nothing else (`pair-is-sq-at-member`;
   `src/L/StageCardinal.lagda.md:283`, `:68-69`).
5. The count inside it is ingredient (iv) itself, `fst (Bound.formula-bound (ih m))`
   (`cnt-is-the-IH-at-member`; `src/L/StageCardinal.lagda.md:288-289`).
6. and 7. **The count's own packing is the same parameter again**
   (`formula-bound-is-count`, `count-bound-is-sq-packs`;
   `src/L/StageCardinal.lagda.md:124-128`): every `pair` in `count-bound` is
   `sq δ δ∈suc infδ` applied by row 4.

So the ONLY occurrences of the value in the value equation at an infinite member
stage are `sq`-applications, and there are two layers of them: the outer pack of the
pair, and the count's inner packs of the formula's code.

## WHAT CHANGES AT THE LIMIT

At the FINITE base, the value at a member is `numeralω (least x x∈)`
(`src/L/StageCardinal.lagda.md:459`): a numeral, the least tally index, with no `sq`
anywhere in the value equation, and `[LJ-1.601]` measured the table formula GO. At an
INFINITE member stage, the value is the ordinal-least `y` with `class-pred x y`
(`src/L/StageCardinal.lagda.md:349-351`), and `class-pred`'s second conjunct compares
`y` with `B.pair m (cnt m φ)` (`:319-323`) where `B = Bound δ oδ infδ
(sq δ δ∈suc infδ)` (`:283`), while `cnt` itself packs the formula's code through the
same `pair` (`:124-128`). **What changes is the PACKING and not the index: the
selection moves from a natural-number least over a finite tally to an ordinal least
over a class whose every witness is packed through the bare pairing parameter at the
member stage, twice.** The limit case is therefore NOT a transcription of the finite
table, and this task did not finish early.

## DOES (iv) REACH sq

YES. At an infinite member stage the value equation's only occurrences of the value
are `fst (sq δ δ∈suc infδ)` applied, at `src/L/StageCardinal.lagda.md:322` (the outer
pack, measured by `class-pred-at-member`) and at `:124-128` through `:283` (the
count's inner packs, measured by `count-bound-is-sq-packs` with `pair-is-sq-at-member`).
This is the FOURTH arrival at the bare parameter, now from the member stages: after
`[LJ-1.572]`, `[LJ-1.594]` (`agents/tasks/LJ-1-594/Probe594.agda:238-243`) and
`[LJ-1.597]` (`agents/tasks/LJ-1-597/review-of-step-graph.md:104-112`).

## THE ATOM, AND THE MERGE THIS MEASUREMENT EARNS

`sq` is the module parameter at `src/L/StageCardinal.lagda.md:17-20`: injectivity and
nothing else, no formula, no Levy grade, no stage. NOTHING CODES AN ARBITRARY AMBIENT
INJECTION, measured three times
(`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`), and the type-level reason is that
every L-element generator takes a `Formula`
(`src/L/Axioms/Full.lagda.md:144`, `:277-280`).

**AND THE ARRIVAL IS INSIDE INGREDIENT (iv), NOT BESIDE IT.** The count IS ingredient
(iv) (`cnt-is-the-IH-at-member`, and `[LJ-1.594]`'s `cnt-is-the-IH` at
`Probe594.agda:252-263`), and the count's own packing reaches `sq` at the member
stage. So (iv) cannot be completed by any table at its base: at every infinite member
stage, (iv)'s value equation already IS an application of (iii)'s parameter. **The
completion of (iv) and the discharge of (iii) are ONE problem: a definable pairing at
the ordinal stages.** With `sq` bare, no `Formula S 2` can express the graph the
statement names, because the graph itself varies with the arbitrary parameter while
the formula's means to name the packed values are the first-order structure of `δ`
alone.

`[LJ-1.601]`'s GO STANDS, at the finite member stages only, and the two halves do NOT
join: `the-finite-base-has-a-formula` (`Probe603.agda`, section 2) is the finite half
imported at its own type, and this file's finding is the reason the join has no
content. The composition with `Emb.emb` into the ambient `α`
(`src/L/StageCardinal.lagda.md:555-556`) is not measured here, the same boundary
`[LJ-1.601]` drew at `:548`.

## THE TIE TO INGREDIENT (iv), AND ITS STRENGTH

The branch's limit case composes the induction hypothesis at the member stage with
the ordinal embedding (`src/L/StageCardinal.lagda.md:555-556`), and the assembly
`stage-card-upper = ∈-induction step` (`:566`) makes that hypothesis the step's own
output at the member stage, which is section 1's subject. `P-is-the-injection`
(`Probe603.agda`, section 3) is `refl`, `[LJ-1.594]`'s own row (`Probe594.agda:337-341`):
the induction hypothesis and the thing being built are ONE type. The branch's own
equation at the limit case is a READING with its sites named, not a proved row:
`ord-tri` is well-founded induction under LEM (`src/L/Ordinal/Linear.lagda.md:136-137`),
so no `refl` can select the limit case at an abstract stage, and `[LJ-1.584]` measured
that `branch` in a conversion problem does not terminate
(`agents/tasks/LJ-1-584/runs/w3b-1.out`).

## WHAT IS NOT CLAIMED

**THE TARGET IS NOT FALSE AND THIS FILE DOES NOT REFUTE IT.** `V = L` gives a
definable pairing at the stages, and through it a formula for a stage injection:
`[LJ-1.594]`'s `vl→target` chain (`agents/tasks/LJ-1-594/Probe594.agda:135-152`)
carries that, and this task re-runs none of it. What is measured here is narrower:
WITH `sq` A BARE PARAMETER, the delivered recursion's graph at an infinite member
stage is not expressible, because its value equation's every occurrence of the value
is an application of that parameter.

**NO EQUIVALENCE BETWEEN THE ARITY-2 SHAPE AND `[LJ-1.568]`'s ARITY-3 `Def` IS
CLAIMED.** `[LJ-1.597]`'s caveat, carried unchanged.

**THE STATEMENT'S OWN INDEX IS PART OF THE DELIVERABLE.** `W3.InfStage`
(`agents/tasks/LJ-1-603/runs/W3.agda:113-131`) is the first statement in this campaign
to carry `ω ∈ δ` as data, and its spelling is a measurement of this dispatch: the
record spelling of the same five components WALLS the pane's 2 GB cap
(`runs/w3-1.out`, `runs/bisect-a.out` to `bisect-c.out`), the Sigma spelling is GREEN
at 1.42 s (`runs/w3-2.out`, cure measured at `runs/bisect-d.out`, 1.32 s).

## THE C-42 SWEEP

C-42 orders the count before the cure. The shape this stop names is the one both
predecessors already swept: a bare ambient injection handed to a chapter as a module
parameter, and a selection predicate quantifying over `Formula` at an ambient carrier
(`[LJ-1.584]`: seven parameter lines, three objects, three chapters; `[LJ-1.594]`: 80
lines in 16 files, two of them the cure). **This task adds the MEMBER-STAGE site to
the first count and no new shape and no new file.** The cure files are unchanged:
`src/L/Coding/CodeSet.lagda.md` and `src/L/Coding/Powerset.lagda.md`.

## WHAT WOULD REOPEN IT

Not this obligation, and not at this price.

1. **RE-PARAMETERISE `L.StageCardinal` WITH A DEFINABLE PAIRING** at the ordinal
   stages. That is `[LJ-1.584]`'s route 2 (`agents/tasks/LJ-1-584/lj-1.584-report.md:195-197`)
   and it is now the ONE route that serves BOTH (iii) and (iv): this file measures
   that they are one problem. With a definable `sq`, rows 1.3 and 1.7 become
   formula-expressible, and the residue is `[LJ-1.594]`'s ingredients (i), (ii) and
   (v), each of which has its machine (`review-of-pairing-suffices.md:138` and the
   order under it: (v) first, the coded copy at the carrier, which must name the
   STAGE that holds `AllCodes`, because `[LJ-1.86]` measured the proof cannot choose
   it, `archive/dev/LJ-dispatch-index.md:160`).
2. **THE TRUNCATED REOPENER `[LJ-1.584]` NAMED** is untouched by this file: a route
   that needs only cardinal arithmetic never needs the computed injection as data
   (`dev/literature/truncation-and-selection.md:83-84`).
