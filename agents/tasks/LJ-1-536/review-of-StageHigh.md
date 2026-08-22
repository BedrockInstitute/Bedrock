# review-of-StageHigh: the obligation is not delivered, and the door is the reason

**NO-GO.** `StageHigh` is stated at `agents/tasks/LJ-1-536/Probe536.agda:350-352`
and it is not inhabited. No postulate stands in for it. The probe is green:
exit 0, `agents/tasks/LJ-1-536/runs/full-t2.out`, median 12.45 s and 669 MB over
three cold runs (`runs/full-t1.time`, `runs/full-t2.time`, `runs/full-t3.time`).

**THIS IS NOT A FAILURE AT THE STATEMENT. IT IS A NO-GO AT THE DOOR, WHICH THE
BRIEF NAMED AS THE OUTCOME THAT EARNS A RULING.**

## What the door wants that the tree does not have

`𝒟ₒ-intro` is the one route into a stage (`src/L/Constructible.lagda.md:301-304`,
re-ascribed and machine-checked at `Probe536.agda:76-80`). It wants a
`Formula ⟪ A ⟫ 1` whose `defSet` is the target set. `defSet` reads that formula
under the INNER satisfaction of the world `(A , ∈)`
(`src/L/Definability.lagda.md:111-112`, `:146-147`), so **every quantifier in it
ranges over the members of the stage and over nothing else.**

The tree delivers exactly one bridge from an external formula to that inner
reading: `L.Axioms.Separation.AtStage`
(`src/L/Axioms/Separation.lagda.md:119-135`, `:199-231`), re-ascribed at
`agents/tasks/LJ-1-536/runs/W3.agda:111-141`. Its hypotheses are two:

1. the formula is `Δ₀` (`src/L/Axioms/Separation.lagda.md:199-206`), and
2. every constant in it is a member of the stage (`BoundedFo Below`,
   `src/FOL/Manipulation/Bounding.lagda.md:63-79`).

**So the tree can carve a stage with parameters from that stage and bounded
quantifiers, and it can do nothing else.** A formula with an unbounded
existential, read inside the stage, is admissible to `𝒟ₒ-intro` itself and has
no route from `src/` at all.

## Why [LJ-1.520]'s graded formula does not open it

The brief ordered this question first and named a mismatch as a stop.

`levelFo-Σ₁` delivers a `Formula S n` with a `Σ₁` witness
(`agents/tasks/LJ-1-520/Probe520.agda:171-172`), re-ascribed at
`Probe536.agda:112-113`. It misses the door in one way that matters.

**THE CONSTANT DOMAIN AND THE ARITY ARE NOT THE MISS.** `[LJ-1.520]` proved the
formula carries no constant, by `refl`
(`agents/tasks/LJ-1-520/runs/CountCheck.agda:18-19`), so `erase` and then
`embed` (`src/FOL/Manipulation/Relabelling.lagda.md:117`) move it to any
constant domain, and two binders fix the arity.

**THE MISS IS THE GRADE, AND IT IS A REFUTATION AND NOT A GAP REPORT.**
`Probe536.agda:115-116`:

    no-Δ₀-levelFo : {n : ℕ} (w b : Fin n) → Δ₀ (fst (levelFo-Σ₁ w b)) → Empty.⊥
    no-Δ₀-levelFo w b ()

`Δ₀` has no constructor indexed by an unbounded existential
(`src/FOL/LevyHierarchy.lagda.md:47-57`) and `levelFo` is thirteen of them
(`agents/tasks/LJ-1-520/Probe520.agda:167-169`). Agda closes it by absurd
pattern. **The graded formula cannot pass the only bridge the tree delivers, and
no work on that formula will change this**, because the grade is what
`[LJ-1.520]` was asked to produce.

## And the primary source says the same thing

`dev/literature/devlin-II5.md:221-222` states the requirement:

> live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
> γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not

and `:217` states the other reading:

> Strength: the existential over z is UNBOUNDED at the ambient level.

**The literature digest already separated the two readings that this task
measured.** `[LJ-1.520]` delivered the AMBIENT Σ₁ form. The door wants the
witness INSIDE the carrier. The tree has no term that moves one to the other,
and such a term is downward absoluteness for `Σ₁`, which is false in general.

## What is delivered instead

`reduction : HierBelowAll → StageHigh` (`Probe536.agda:357-358`) and its
pointwise form `reduction-at` (`:362-364`). Both are green. They are total in
γ, they use no limit hypothesis, no α, and they never read `ω ∈ γ`.

The residue is one statement: `HierBelow γ`, the internal hierarchy at γ is a
member of `Lset (step 3 γ)` (`Probe536.agda:186-187`). At a successor γ that
statement IS the obligation at the predecessor. At a limit it is not, and
`HierBelowLimit` (`:408-409`) states the open case.

**THE LIMIT DID NOT LEAVE.** `[LJ-1.519]` split Devlin 2.6(ii) so that Part B
names no limit in its type, and that is correct: the reduction above is total in
γ. But the induction that pays `HierBelow` has one case the adjunction cannot
reach, and that case is a limit ordinal. The split moved the limit out of the
statement and into the induction.
