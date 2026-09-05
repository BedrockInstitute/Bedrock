# review-of-level-formula: `[LJ-1.656]` does not deliver `LevelFormula`, and this is where it stops

**THE OBLIGATION IS NOT INHABITED.** `level-formula` is absent from
`Probe656.agda`, the witness meter reads it `missing`
(`runs/meter-obligation.out`, `1 UNRESOLVED of 1`, `probe_red=False`),
and this file is the stop. Both probes are green and every other name in
them typechecks (`runs/meter-names.out`, `0 UNRESOLVED of 17`).

## 1. WHAT IS SETTLED, AND IT IS NOT NOTHING

`LevelFormula` has THREE components, and the brief is right that all
three or nothing. Two of the three are settled here.

**COMPONENT 1, THE FORMULA: DELIVERED.** `Frame.lv : Formula Code 2`.
It is `[LJ-1.651]`'s chain at the obligation's own slot order, plus a
second conjunct section 3 below shows the obligation FORCES.

**THE SET HALF OF COMPONENT 3: DELIVERED, AND CHEAPER THAN PRICED.**
`Frame.lset-in-stage` says the stage holds the level of every one of its
own ordinals, in two lines. **It does not spend `succλ`.** The level of
`δ` is at the stage indexed by `δ` ITSELF, because a carrier is one of its
own definable subsets (`defSet⊤≡A`, `src/L/Definability.lagda.md:178`,
reached through `𝒟ₒ-intro`, `src/L/Constructible.lagda.md:301`).

**COMPONENTS 2 AND 3 REDUCE TO TWO ROWS AT THE CLASS CARRIER, AND THE
STAGE APPEARS IN NEITHER.** `FrameB.level-formula-from-class` is that
reduction and it typechecks:

    level-formula-from-class : MatrixDecode → ClassWitness → LevelFormula

## 2. WHY THE STAGE AND THE ALPHABET COST NOTHING, MEASURED

The passage between the stage's inner world and the class carrier is an
EQUALITY of truth values (`FrameB.matrix-bridge`, `FrameB.ord-bridge`),
so it is spent in BOTH directions and neither costs a hypothesis. Three
delivered facts make it free:

1. **The matrix is Δ₀** (`Δ₀-matrix₀`, from `LH0.Δ₀-matrix` and
   `erase-Δ₀`), so `abs₀` (`src/FOL/Absoluteness.lagda.md:122-124`) reads
   one truth value at the stage, at the ambient and at the class.
2. **The witnesses the Σ₁ closure produces at the stage ARE stage
   members**, so the closure never leaves the stage and the `σ₁-up`
   asymmetry never bites.
3. **The stage lies in `L`** (`FrameB.stage⊆L`), so a stage member
   recasts as a class member with no content.

**AND THE ALPHABET IS FREE TOO.** `Alphabet.toAmb` says the reading of an
embedded parameter-free formula does not depend on the alphabet, and
`FrameB.code≡id` is that at the stage's own structure, between the hull's
`Code` reading and the stage's own. This is why the probe erases at the
MATRIX rather than at the end: `[LJ-1.651]` carried the class alphabet to
the last line and slid it with one `mapFo`
(`agents/tasks/LJ-1-651/Probe651.agda:128-129`), and that spelling cannot
be read at the other two alphabets without a `mapFo`/`renameFo`
commutation law the tree does not deliver.

## 3. AND ONE THING THE OBLIGATION DEMANDS THAT NO PREDECESSOR SUPPLIED

**THE SOUNDNESS HALF CARRIES NO ORDINALITY HYPOTHESIS**
(`agents/tasks/LJ-1-650/Probe650.agda:325`): it quantifies over EVERY
pair of stage members. The tree's only delivered landing demands one:
`ride-only` takes `IsOrd (fst (lookup b γ))`
(`src/L/Condensation.lagda.md:422-425`). **So on the route the tree
delivers, the formula has to SAY it**, and `lv` is two conjuncts.
`[LJ-1.651]`'s `lset-formula` is the first conjunct alone, so it does not
reach this obligation on that route. **Whether some other route proves
soundness without the conjunct is not measured here.**

## 4. THE ROW THAT STOPS IT, AND IT IS FOUR HUNDRED DISPATCHES OLD

**THE SOUNDNESS ROW IS `GraphAgree`, AND IT IS NOT DELIVERED ANYWHERE.**
It is `[LJ-1.52]`'s hypothesis
(`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:48-54`), restated at
today's slot roles by `[LJ-1.570]`, which named it in its own words:
"THE ONE SYNTACTIC ROW THAT IS NOT DELIVERED"
(`agents/tasks/LJ-1-570/Probe570.agda:285-293`). This probe does not name
it, because naming the graph in a type is expensive (section 6); it
states the row one link lower, as `FrameB.MatrixDecode`, and
`[LJ-1.570]`'s own `matrix-decode`
(`agents/tasks/LJ-1-570/Probe570.agda:300-322`) is exactly the delivered
proof of `GraphAgree → MatrixDecode`.

**`[LJ-1.52]` LEFT THREE ROWS, NOT ONE.** `StepAgree` and `ApproxAgree`
are the other two (`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:53-70`).
**Grep over `src/` finds none of the three.** The only `*Agree` modules in
the tree are the twelve-row table's
(`src/L/Condensation/{Lower,Upper,Twelve}Agree.lagda.md`), which are about
the satisfaction predicate inside the leaf and not about the graph.

**AND `LevelHood0` HAS NO CONSUMER IN `src/`.** Grep: the only occurrence
outside its own definition is `src/L/BoundedSubset.lagda.md:840`. The
tree delivers the level-hood matrix as SYNTAX with a Δ₀ certificate and
nothing semantic.

## 5. THE MECHANISM, MACHINE-CHECKED

**`GraphAgree` CANNOT BE A FREE ROW, AND THE REASON IS ONE CONJUNCT.**
The two extension frames differ in exactly one place:

    extAt  y   φ = ∀̇ (z ∈ y ⇒ φ) ∧̇ ∀̇   (φ ⇒ z ∈ y)   src/L/Coding/Model.lagda.md:662-664
    extAtB y K φ = ∀̇∈ y φ        ∧̇ ∀̇∈K (φ ⇒ z ∈ y)   src/L/Condensation.lagda.md:103-105

The FIRST conjuncts say the same thing. The SECOND does not: the machine
frame pins the value against EVERY satisfier of `φ`, the bounded frame
only against the satisfiers that lie in `K`. Two green terms are that
sentence:

- **`extAtB-junk`**: an empty value slot and a bound that catches no
  satisfier satisfy the bounded frame, whatever `φ` is.
- **`extAt-pins`**: the machine frame pins the value against every
  satisfier there is, in or out of any bound. (It is the delivered
  `extAt-in`, `src/L/Coding/Model.lagda.md:671-673`, named here so the
  contrast is one file's two lines.)

`graphBndAt` reaches its value slot through `extAtB` and nothing else
(`src/L/Condensation.lagda.md:2418`, `:2493`); `LsetGraphAt` reaches its
value slot through `extAt` (`src/L/Coding/Sequence.lagda.md:119`). **And
the tree states the price in its own words**: `extAtB→extAt`
(`src/L/Condensation.lagda.md:2514-2521`) takes a third argument,
`(z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩`, "every
satisfier lies in K", **and nothing in `levelHoodB` says it.**

## 6. WHAT I DID NOT PROVE, STATED PLAINLY

**I DID NOT PROVE `GraphAgree` FALSE, AND THIS FILE CLAIMS NO SUCH
THING.** Section 5 measures the MECHANISM by which the bounded frame
under-determines its value. That is not a refutation of the row.

**THE CHEAPEST EXPERIMENT THAT WOULD SETTLE IT**, so the next brief can
price it rather than guess: exhibit a concrete `K` in `L` at which every
conjunct of `graphBndAt` holds with a value that is NOT `Lset γ`. The
conjuncts to discharge are `domB` (`src/L/Condensation.lagda.md:1749-1756`),
the two bounded universals of `approxBndAt` (`:2471-2477`), and the outer
`extAtB` of `stepBndAt` (`:2418`), whose body bottoms out in `bodyB`
(`:2404-2408`) whose FIRST conjunct is a membership in the carrier slot.
**That last fact is what makes the experiment plausible without touching
the code machinery at all.** This task did not attempt it and does not
bound its price.

## 7. WHAT THE NEXT BRIEF SHOULD ASK FOR

The obligation is now two rows, `FrameB.MatrixDecode` and
`FrameB.ClassWitness`, both stated in `runs/Probe656B.agda`, both at the CLASS
carrier, and neither mentioning the stage, the hull, the code alphabet or
`succλ`. Either is a task; neither is this one. Before pricing a cure for
the first, C-42 asks for a count: `[LJ-1.52]` left three rows unbuilt and
this task measured only the one it needed.
