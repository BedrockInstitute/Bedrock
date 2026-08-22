# Review of `succ-into-subsets`

**THE OBLIGATION IS NOT INHABITED. THIS FILE IS THE OBSTRUCTION.** The brief
ordered a stop that names which input cannot be supplied, and this is that stop.

`agents/tasks/LJ-1-549/Probe549.agda` is GREEN, exit 0, three cold runs
(`runs/final-1.out` to `runs/final-3.out`). It carries no hole and no postulate.
That is deliberate: a hole makes every reduction a claim, and green makes each
one a measurement. Nothing lands in `src/`.

## THE STATEMENT

    succ-into-subsets :
        (κ δ : SL.S) → SuccCardL δ κ
      → ∥ Σ[ b ∈ SL.S ] Σ[ F ∈ SL.S ]
           ( InjCode F δ b
           × ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

It is `agents/tasks/LJ-1-546/Probe546.agda:152-157`. This task took the type
from that file by IMPORTING it, so it cannot have drifted:
`statement-is-pointwise` and `pointwise-is-statement`
(`Probe549.agda:169-175`) are the identity function in both directions between
`P546.SuccIntoSubsets` and this task's pointwise `SubsetsAt` under `SuccCardL`.

## FINDING 1. THE FREEDOM IN `b` IS WORTH NOTHING, AND THE BRIEF SAYS IT IS
## THE WHOLE POINT

The brief says: "It does not ask for `𝒫 κ` itself. It asks for SOME L-set `b`
whose members are all subsets of κ... **The freedom in `b` is the whole point of
the reduction**, and it is yours to use."

**IT CANNOT BE USED, BECAUSE THE LARGEST ADMISSIBLE `b` IS ALREADY FREE.**

`hasPowerL` (`src/L/Axioms/Power.lagda.md:187`) is an UNCONDITIONAL term of the
tree: it separates the bounding stage by `subFo κ` (`:98-99`, `:187-190`). So

    powL : S → S
    powL κ = ℩ (hasPowerL κ)

is a term with no `zf : isZFModel` in its type (`Probe549.agda:121-122`), and
`℩-spec` reads its membership as `y ⊆ˢ κ` on the nose (`powL-sub`,
`Probe549.agda:124-125`). The second conjunct of the obligation is therefore
DISCHARGED OUTRIGHT at `b := powL κ`, with no hypothesis at all.

Both implications are typechecked:

- `power→subsets` (`Probe549.agda:179-181`): a code at `(δ , powL κ)` gives the
  obligation's conclusion.
- `subsets→power` (`Probe549.agda:186-190`): the obligation's conclusion gives a
  code at `(δ , powL κ)`, by `[LJ-1.546]`'s own `code-target-mono`, IMPORTED and
  not rebuilt.

**SO `SuccIntoSubsets` AND B10 ARE THE SAME PROBLEM.** `powL-is-𝒫`
(`Probe549.agda:133-136`) proves `powL κ ≡ 𝒫 κ` at ANY model record, because
both are `℩` of a proof of the same `isContr` and `isContr` is a proposition;
`power→B10` and `B10→power` (`:193-199`) carry the equivalence to
`InjL δ (𝒫 κ)` itself.

**WHAT `[LJ-1.546]`'s REDUCTION BOUGHT IS REAL AND IT IS ONE THING: the `zf`
record leaves the statement.** It bought no mathematics. This is a D-10 finding
about the brief's premise and it is stated with terms rather than argued.

## FINDING 2. WHICH INPUT I CANNOT SUPPLY

The brief asks: does `approx-carve`'s method reach this table, and if not, name
the input.

**THE METHOD REACHES IT. TWO OF ITS INPUTS DO NOT EXIST.**

`approx-carve`'s method (`agents/tasks/LJ-1-537/Probe537.agda:119-212`) is four
inputs: a `smallDom` bound over the members of the domain, a `Formula S 1`,
`hasSeparationL`, and the two membership readings. `module Table`
(`Probe549.agda:268-438`) runs that method at THIS table and builds everything
it can. What it cannot build is the module's own two parameters:

1. **`s`, THE AMBIENT ASSIGNMENT** (`Probe549.agda:269-271`): a map from the
   members of δ to L-sets, injective, every value a subset of κ.
2. **`Link`, ITS OBJECT-LANGUAGE DESCRIPTION** (`Probe549.agda:272-277`): a
   `Formula S 3` whose satisfaction at `(y ∷ x ∷ z ∷ [])` says `y` is the value
   of `s` at `x`, with both readings.

**THE BOUND IS NOT THE MISSING INPUT.** `smallDom` (`src/L/Recursion.lagda.md:133`)
confines the whole table at once, because the pairs are indexed by `⟪ fst δ ⟫`,
which is small. `bnd` (`Probe549.agda:289-290`) is built. It needs `s` and
nothing else.

**AND `s` IS NOT A CODING QUESTION.** Section 6 (`Probe549.agda:551-600`) reads
the three hypotheses on `s` back in both directions:

    assignment→ambient : ... → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
    ambient→assignment : ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫ → Σ[ s ∈ ... ] ...

**SO INPUT 1 IS THE AMBIENT STATEMENT `κ⁺ ≤ 2^κ`, EXACTLY.** No chapter of
`src/` delivers it. `[LJ-1.535]` closed the counting-site route
(`agents/tasks/LJ-1-535/lj-1.535-report.md:1`) and the bounded-subset theorem
(`src/L/BoundedSubset.lagda.md:1621`) is the OTHER leg: it concludes
`x ∈ˢ Lset κ` from `x ⊆ Lset α`, which is `2^κ ≤ κ⁺`.

**AND INPUT 2 IS `[LJ-1.533]`'s WALL AT ITS THIRD SITE.** "Nothing in `src/` and
no term in any probe turns an arbitrary ambient function into an `InjCode`"
(`agents/tasks/LJ-1-533/lj-1.533-report.md`, `## WHAT CODES AN AMBIENT
INJECTION`). Both L-set generators take a `Formula`
(`src/L/Axioms/Full.lagda.md:144-146`, `:277-280`) and `_↪_` carries none
(`src/L/Cardinal.lagda.md:47-48`).

## FINDING 3. EVERY DELIVERED CODE PRODUCER IS REFUTED AT THIS PAIR

This is stronger than "no producer was found". There are three producer shapes
in `src/` and two of them are refuted here by a term.

**THE SHIFT.** `shift-coded` (`src/L/CodedShift.lagda.md:37-40`,
`src/L/Absorption.lagda.md:611-626`) delivers at the pair `(sucʟ γ , γ)`, and
`[LJ-1.546]`'s `code-source-determined` (`Probe546.agda:127-133`) says a table
has ONE source. So it reaches this obligation only if δ is an ordinal
successor. **IT IS NOT**: `no-ordinal-successor` (`Probe549.agda:482-497`).
If `δ ≡ sucʟ γ` for an infinite ordinal γ holding every numeral, `shift-coded`
codes δ into γ, and `γ ∈ δ`, which `IsCardinalL δ` forbids. The producer
refutes itself at this source.

**THE INCLUSION.** `L.InjChain.Carve` (`src/L/InjChain.lagda.md:468`, conjuncts
at `:518`, `:525`, `:532`, `:544`), opened by `InclGraph` (`:575-598`) and
`OrdIncl` (`:604-607`), delivers a code at `(D , C)` for any `D` whose members are
members of `C`, and it needs NO ambient function. **IT IS REFUTED**:
`inclusion-fails` (`Probe549.agda:635-648`). δ is not a subset of the power set
of κ, and the witness is `sucʟ κ`, which is a member of δ
(`succ-kappa-in`, `Probe549.agda:514-536`) and is not a subset of κ.

**COMPOSITION.** `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314`, conjuncts at
`:380`, `:391`, `:402`, `:420`) produces nothing on its own: it takes two codes.
No delivered code has δ as its source, by the same
`code-source-determined`.

**THE COUNT BY NAME MISSED TWO OF THE THREE.** `[LJ-1.546]`'s sweep grepped for
`InjCode` and found two sites. `L.InjChain` delivers the four conjuncts without
ever writing the type's name, so a name sweep does not see it. I record the
correction here so the next sweep does not repeat it.

## THE CHEAPEST `b` THE BRIEF NAMED, PRICED

`sucʟ κ` passes the second conjunct: every member of κ⁺¹ is a subset of κ,
`succ-kappa-subsets` (`Probe549.agda:503-510`). So it is a real candidate and
not a category error. It is refuted as a target by the cardinal clause:
`succ-kappa-excluded` (`Probe549.agda:541-548`).

A STAGE fails the second conjunct: a member of `Lset β` is an arbitrary L-set.
A BOUNDED COLLECTION is `powL κ` restricted, and finding 1 says a restriction
can only cost more.

## THE LEASTNESS CLAUSE

**NOT USED, ANYWHERE IN THIS FILE.** No term of `Probe549.agda` takes
`SuccCardL`, and `Residue` (`Probe549.agda:668-677`), the type the whole
reduction consumes, does not mention it.

**THAT IS NOT GOOD NEWS AND I WILL NOT REPORT IT AS SUCH.** The clause is not
removed from the problem: it is pushed entirely into input 1. It is what makes
input 1 TRUE, because every member of δ must inject into κ, and that is exactly
what "no cardinal strictly between κ and δ" says.

## WHAT WOULD REOPEN THIS

`Residue δ κ` (`Probe549.agda:668-677`), and nothing weaker was found. It is one
Σ: the assignment, its two laws, the formula, and the formula's two readings.
`residue-suffices` (`Probe549.agda:679-681`) spends it for the obligation and
`residue-pays-B10` (`:685-689`) spends it for B10 outright.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the residue. `src/` is
untouched. `transfer-suffices` was not rebuilt. B5 and B9 were not touched.
I did not commit and did not push.
