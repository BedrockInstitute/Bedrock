# review-of-stage-read: the backward half dies at the DefAt membrane

**VERDICT: STOP, STATED.** `stage-read` is not inhabited. The statement
is not refuted here: this dispatch priced the nearest counterexample
and it dies (section 3 below). What the dispatch measured is where the
un-guarding spine sticks, and it is not the syntax bridge.

## THE OBLIGATION

    stage-read :
        (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
        (u z W : S) → ⟨ fst u ∈ γ ⟩ → ⟨ fst z ∈ Lset γ ⟩
      → ⟨ (z ∷ u ∷ W ∷ []) ⊨ relativize (LsetS γ oγ)
                            (LsetGraphAt zero (suc zero)) ⟩
      → fst z ≡ Lset (fst u)

Transcribed verbatim from `agents/tasks/LJ-1-725/Probe725.agda:251-258`
and exported as a TYPE at the top level of
`agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda`. No inhabitant stands
under it, no postulate supports it, the probe carries `--safe` and no
hole. The names `carved-is-hier` and `table-sat` are absent, per the
brief.

## WHAT IS REAL, AND TYPECHECKS

`agents/tasks/LJ-1-725-SPLIT/runs/p-7.out`, EXIT=0, 1.87 s,
374,587,392 bytes peak, one Agda process, caliber `-A64m -I0 -M2g`
printed in the run. 17 percent of the wide cap, no heap wall.

1. `Lset-trans-set` (Probe725Split.agda, section 1). Members of
   members of `Lset γ` lie in `Lset γ`. This is half 1 of the
   corrected target in `agents/tasks/LJ-1-725/review-of-carved-is-hier.md`.
   One `PT.rec` over the landed `Lset-out`
   (src/L/Constructible.lagda.md:346), closed by the landed operator
   refinement `𝒟ₒ∋⊆` (src/L/Constructible.lagda.md:323) and
   `Lset-mono` (src/L/Constructible.lagda.md:365). The two-step
   iterate `Lset-trans-set²` is the form the spine's recorded-pair
   sites consume, because a pair's components sit two membership
   steps below a member of the bound and Kuratowski pairs are not
   transitive, so the fact must be iterated, never assumed.
2. `ord-in-Lset` (section 2). A member of an ordinal lies in the
   ordinal's own stage. `[LJ-1.724]`'s cure
   (agents/tasks/LJ-1-724/Probe724.agda:67-71), re-measured at this
   site from the landed `Lset-cumul` and `ord∈Lset-suc`
   (src/L/Ordinal/Stages.lagda.md:164,434). That probe is not in this
   worktree, so nothing is imported from it. This is the fact that
   puts every member of `fst u` inside the relativization's bound.

## WHY THE SPINE DOES NOT CLOSE

`relativize-correct` (src/FOL/Manipulation/Relativize.lagda.md:142)
turns the residual conjunct into the `A`-bounded satisfaction of the
graph at `A = Lset γ`; the equation then wants the argument of
`Lset-only` (src/L/Hierarchy.lagda.md:334) rebuilt under that bound.
The rebuild splits into two inclusions of sets.

**The forward inclusion closes on the delivered facts.** For
`x ∈ fst z` with `⟨ fst z ∈ Lset γ ⟩`: `x` is in the bound by
`Lset-trans-set`; the bounded `StepAt` conjunct instantiates at `x`;
its three existential witnesses arrive in the bound from the guards;
`approx-val`'s chain re-runs with every extraction site in the bound
by `Lset-trans-set` (iterated) and `ord-in-Lset`; `Lset-in` lands `x`
in `Lset (fst u)`. Not inhabited here; the read of the bounded `DefAt`
that replaces `Sequence.readBody`'s equation
(src/L/Coding/Sequence.lagda.md:180) is real work and is priced in
the report, not attempted.

**The backward inclusion does not close, and this is the stop.** For
`x ∈ Lset (fst u)` one must feed the bounded `StepAt` at `x`: produce
the bounded satisfaction of `∃̇∃̇∃̇ (StepBody b f)` at `x` with witnesses
inside the bound. The natural witnesses exist (`ord-in-Lset` puts the
argument pair in the bound, `Lset-mono` and `Lset-suc`
(src/L/Axioms/Basic.lagda.md:196) put `Lset δ` and `𝒟ₒ (Lset δ)` in
the bound, and `domAt`'s backward half, instantiated at bound members,
plus the pinned recorded value, supplies the recorded pair). What
dies is the payload's `DefAt zero (suc zero)`
(src/L/Coding/Powerset.lagda.md:442): under the bound, its two
existentials demand a formula CODE and the satisfaction recursion's
VALUE, both inside `Lset γ`, for every bound member of the definable
powerset. The tree carries no stage bound for the coding
constructions: `CodeSet`'s `smallAny`
(src/L/Coding/CodeSet.lagda.md:304) returns an unspecified stage
containing the keys, and no landed lemma bounds `keyS`, `Sat` or the
environment sets by their carrier's stage. `[LJ-1.724]` measured this
same membrane class failing outright below a fixed finite stage
(agents/tasks/LJ-1-724/lj-1.724-report.md, verdict item 4). `DefAt-stage`
(src/L/Coding/Powerset.lagda.md:720) turns the UNBOUNDED description
into an equation at a stage carrier, but the bounded reading still
quantifies its witnesses inside the bound, so it does not dissolve the
membrane.

So the precise answer to the brief's NO-GO question, "which unbounded
∀ of the graph still fails to un-guard": the failing site is the
second conjunct of the relativized `Step (suc w) (suc b) zero`, the
`extAt`'s reverse implication at arguments inside `Lset (fst u)`. Its
guard un-guards fine (the delivered facts discharge it); its PAYLOAD
re-imposes the bound through `DefAt`'s existential witnesses. The wall
is an ∃-supply problem under the bound, not a ∀-guard problem.

## THE COUNTEREXAMPLE THIS DISPATCH PRICED, AND WHY IT DIES

Before stopping, the target's truth was checked per D-10. The nearest
candidate: a small stage, an empty table, and degenerate slots. At
`γ = 2`, `u = 1`, `z = ∅`, `W = ∅`, the empty table satisfies every
guarded clause EXCEPT `domAt`'s backward half: the domain slot of
`ApproxAt zero (suc b)` is `fst u`, the bound `Lset 2` cannot hold the
recorded pair the argument `0` requires (rank arithmetic, the 724
report's item 3), so the hypothesis is unsatisfiable there and the
implication is vacuous. No counterexample survived pricing. The
statement's model-side truth is intact as far as this dispatch can
measure; what is missing is its internalization, and the missing
lemma is measured above.

## THE CORRECTED TARGET

Fund, as its own obligation before any spine assembly:

    the coding constructions sit below the carrier's stage:  for a
    carrier A whose underlying set lies in Lset γ, the key, the
    recursion value and the environment sets of a formula over A lie
    in Lset γ (or in a stated finite successor of it, with the
    successor arithmetic against γ landed alongside).

Model-side this is plausible (keys are hereditarily finite over the
carrier; satisfaction values and environments sit at small finite rank
above it, and the Bridge chapter's
`Sat-spec`/`defSet-Sat` machinery is the content), but nothing bounds
them today. After that lemma lands, the backward half is one assembly
(the witnesses above, filled through the membrane), and the forward
half's bounded `DefAt` read dissolves by the same bound. Both prices
should be set after the bound is measured, not before.

## WHAT I DID NOT DO

I did not inhabit `stage-read`. I did not inhabit `carved-is-hier` or
`table-sat`; both names are absent from the probe. I did not land
anything in `src/`. I postulated nothing. The probe carries `--safe`
and no hole. No failing run was repeated unchanged: p-1 through p-6
each fixed one distinct defect (a missing `𝒟ₒ` in the import list, the
wrong closing lemma for the step, a missing `Lset-mono` import, an
implicit stage argument the unifier cannot inject, and the field
name's mixfix form); p-7 was the first green run and p-8 is the
verdict run on the delivered bytes after a comment-only pass.
