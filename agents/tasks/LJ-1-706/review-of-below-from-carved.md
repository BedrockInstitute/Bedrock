# review-of-below-from-carved: the obligation is not delivered, and the placement row is the reason

**NO-GO.** `below-from-carved` is the section 2 type of
`agents/tasks/LJ-1-706/Probe706.agda` without the `Bound-in-tower`
hypothesis, and it is not inhabited. No postulate stands in for it. The
probe is green: exit 0, median 2.38 s over three forced rechecks
(`runs/recheck-1.out`, `runs/recheck-2.out`, `runs/recheck-3.out`). The
witness meter reads `1 UNRESOLVED of 1, probe_red=False`
(`runs/meter-obligation.out`, `[NotInScope]` at the generated witness).

**THIS IS NOT A REFUTATION OF `Below`.** `Below` is `[LJ-1.697]`'s type
(`agents/tasks/LJ-1-697/Probe697.agda:72-74`) and it is the classical
fact `[LJ-1.536]` already reduced to (`review-of-StageHigh.md:83-88`).
No term of its negation was built. The stop is at the DOOR'S STAGE, one
level below the statement.

## What the identification gives, and where it stops

`[LJ-1.704]`'s identification, taken here as a hypothesis
(`Probe706.agda:59-61`), says the carved set IS the table's first
projection. With it, membership of the carved set IS membership of the
table. The probe proves the two rows that make that precise:

- `door-lands` (`Probe706.agda:94-99`): the delivered door
  (`agents/tasks/LJ-1-698/Probe698.agda:128-129`) puts the carved set in
  `Lset (sucV σ)`, where `σ` is `mkBoundedFo`'s stage
  (`agents/tasks/LJ-1-698/Probe698.agda:97-101`). Green.
- `below-from-place` (`Probe706.agda:78-83`): `Bound-in-tower` plus the
  identification give `Below`. `Lset-in`
  (`src/L/Constructible.lagda.md:329-330`) reads the carved set's
  `𝒟ₒ`-membership at the tower's stage; `subst` moves it to the table
  along the identification. Green.

So the distance from the identification to `Below` is EXACTLY ONE ROW:
`Bound-in-tower` (`Probe706.agda:65-67`), the placement of
`mkBoundedFo`'s bounding stage under the tower over `δ`.

## Why the tree does not have that row

`σ` is the first projection of `bound-of`, and `bound-of` is
`mkBoundedFo` applied to the relativized pair-graph. Nothing in the tree
places `mkBoundedFo`'s output under any ceiling:

- `mkBoundedFo` merges stages with `bound2`
  (`src/L/Axioms/Separation.lagda.md:449-462`), and `bound2` is the
  union of the successor family (`src/L/Ordinal.lagda.md:185-192`,
  engine at `:166-180`). It sits AT LEAST ONE SUCCESSOR ABOVE each
  input.
- The reflection machinery consumes `bound2` the same way and only ever
  goes UP: `Box σ P` is a `τ` with `σ ∈ τ`
  (`src/L/ReflectFo.lagda.md:202-204`). No lemma in the tree puts a
  merged bound UNDER a fixed ordinal.
- `Lset-in` needs `δ ∈ α`. That membership is the row itself.

## D-10: the row is not only missing, it is false in the direction the door needs

Price the truth of the row before pricing its proof. The evidence chain,
every link in the tree:

1. The outer merge's constant is the ordinal itself, and its stage is
   `sucV γ` EXACTLY. Every `α` with `γ ∈ Lset α` has `γ ∈ α`
   (`src/L/Ordinal/Stages.lagda.md:265-268`), so `α ≥ sucV γ`; and
   `γ ∈ Lset (sucV γ)` (`src/L/Ordinal/Stages.lagda.md:434`). `stage`
   is the least such `α` (`src/L/Stage.lagda.md:191-193`).
2. `bound2` contains the successor of each input
   (`src/L/Ordinal.lagda.md:185-192`), so `σ ≥ step 2 γ` at least.
3. `relativize` binds EVERY unbounded quantifier at the constant
   (`src/FOL/Manipulation/Relativize.lagda.md:56-57`), and each such
   binder is a `bound2` merge node carrying `stage` of that constant
   (`src/L/Axioms/Separation.lagda.md:461`, `:431-433`).
4. The base formula carries at least three NESTED unbounded
   quantifiers: `PairGraphAt`'s `∃̇` (`src/L/Coding/Sequence.lagda.md:328-329`),
   `GraphAt`'s `∃̇` (`:291-292`), `ApproxAt`'s `∀̇` over `domAt`'s `∀̇`
   (`:286-289`, `src/L/Coding/Model.lagda.md:278-280`). Each becomes a
   binder at `A = LsetS γ oγ`, and each merge climbs one successor over
   the one below it.

So the placement row `σ ∈ step 3 γ`, that is `σ ≤ step 2 γ`, forces the
whole nested chain to fit at or below `sucV γ`, which forces
`stage (LsetS γ oγ)` to sit at least three successors below its own
ceiling `sucV γ` (step 2 of `stage A ≤ sucV γ`:
`Lset γ ∈ Lset (sucV γ)` by `𝒟ₒ-intro` at `⊤̇` and `Lset-suc`
(`src/L/Axioms/Basic.lagda.md:196-197`), then `stage-earliest`).
Classically `L_γ` first appears at `L_{γ+1}`, so `stage A = sucV γ` and
the row is FALSE at general `γ`. The tree has not paid that lower bound
("`L_γ` does not appear by stage `γ`"). That is the honest open row
beside this stop: pay it, and this stop becomes a refutation of the
`mkBoundedFo` door at `Below`'s stage.

## The corrected target, beside the original

The constants themselves fit. `γ ∈ Lset (sucV γ)` and
`Lset γ ∈ Lset (sucV γ)`, and `Lset-mono` carries both into
`Lset (step 2 γ)`. So the door CAN be fired one ceiling lower:

- Re-bound the carve at `τ := step 2 γ`: assemble
  `BoundedFo (Below′ (step 2 γ)) φᵣ` by hand. `BoundedFo` computes on
  constructors (`src/FOL/Manipulation/Bounding.lagda.md:63-79`), and
  `φᵣ`'s spine is a fixed formula. The door at `Lset τ` then lands the
  `τ`-carve in `Lset (sucV τ) = Lset (step 3 γ)`: EXACTLY `Below`'s
  stage, with no comparison left to pay.
- What that costs: the identification must then be stated at the
  `τ`-carve, which changes `[LJ-1.704]`'s frame, OR a carve-agreement
  `carve (liftFo φᵣ hσ) ≡ carve (liftFo φᵣ hτ)` must be paid. That is
  the separation-uniqueness shape `[LJ-1.704]`'s own W3 already names.
  The lift uses the bound's fiber data
  (`src/L/Axioms/Separation.lagda.md:131-135`), so the two carves are
  not the same term by conversion.

This is the mathematician's call, not this slot's: it re-aims a live
task's obligation.

## What is delivered

`Below`, `Identified`, `Bound-in-tower` (types, `Probe706.agda:53-67`),
`below-from-place` (`:78-83`), `door-lands` (`:94-99`). All green. Do
not re-dispatch any of them. Do not rebuild `door-next`, `bound-of`,
`Carved`, or `step`: they are imported from the probes that typechecked
them.

**WHAT THE NEXT BRIEF NEEDS.** The campaign learned the distance before
`[LJ-1.704]` landed, which is what this task was funded for: the
identification is not the gap, the bounding stage is, and
`mkBoundedFo`'s stage overshoots `Below`'s ceiling by the relativized
binder depth unless the carve is re-bounded at `step 2 γ`. Decide
between the two corrected shapes above before `[LJ-1.704]` closes, or
its identification lands on a carve that cannot feed `Below`.
