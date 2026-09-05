# NO-GO: `b9-inf` - the internalization machine does not apply to `stage-card-upper`

## THE STOP

**THE OBLIGATION IS NOT INHABITED.** No term of
`agents/tasks/LJ-1-596/Probe596.agda` is named `b9-inf`. `B9Inf` is stated in
the probe, copied letter for letter from
`agents/tasks/LJ-1-593/Probe593.agda:511-514`, and no term of that type is
offered.

**THE PROBE IS GREEN, EXIT 0, AND CARRIES NO HOLE AND NO POSTULATE**
(`agents/tasks/LJ-1-596/runs/final-1.out`, `final-2.out`, `final-3.out`, all
cold for this file). Green and not holed is deliberate: every reduction in the
file is a measurement and not a claim.

**THIS IS THE FOURTH MEASURED FAILURE ON THIS OBJECT, AND THE FIRST THAT
MEASURES THE MACHINE AND NOT THE OBJECT.** The brief says a NO-GO here is a
ruling for the owner. The ruling this file supports is narrow and it is not
"the object is false":

- The object is not false. `[LJ-1.594]` measured that `V = L` gives the target
  outright (`agents/tasks/LJ-1.594/Probe594.agda:135-140`), and the
  construction the classical sources give is a recursion whose table the
  machine would internalize if its graph existed.
- What is false is the hope that `src/L/Recursion.lagda.md` applies to
  `stage-card-upper` AS THE TREE HAS IT. The chapter is not misstated and not
  broken. Its condition simply asks, at this site, for an input the tree does
  not have, and producing that input is a chapter of `src/`, not a term of a
  probe.

## THE MEASUREMENT, IN FIVE ROWS

**1. THE CHAPTER'S ACTUAL CONDITION, RE-ASCRIPTED.** The prose sentence is at
`src/L/Recursion.lagda.md:259-262`: "A recursive definition is internalizable
when its graph is expressible, and nothing about the recursion's shape, its
depth, its order of descent, or the complexity of its clauses appears in the
condition." The type demands a formula AND the two adequacy implications
`defines` (`src/L/Recursion.lagda.md:277`) and `only` (`:278-279`), and a
TOTAL function `fn : S → S` (`:275`). The sentence is true of the type only
if "expressible" is read as "adequate in both directions", which is the
mathematics itself. The SECOND half of the sentence is true as stated: no
field of either record (`:103-108`, `:272-279`) mentions shape, depth, descent
order or clause complexity. The probe states the condition as one type and
hands it to the actual record (`Condition`, `condition-is-the-record`,
`Probe596.agda` section 1).

**2. `step`'s VALUE IS FUNCTION-VALUED AND THE MACHINE CONSUMES SETS.** The
machine's `fn : S → S` (`src/L/Recursion.lagda.md:275`) returns an L-set;
`P` (`src/L/StageCardinal.lagda.md:530-532`) returns an injection between
fibers. The `refl` row is `P-is-function-valued`
(`agents/tasks/LJ-1-596/runs/W3.agda`, inside `module Tower`). To feed the
machine at all, the recursion must first be re-targeted at codes, and that
re-targeting is what B9 was going to build.

**3. THE GRAPH DOES NOT STATE.** W3 wrote it first and typechecked it alone
(`agents/tasks/LJ-1-596/runs/W3.agda`, green, `runs/w3-11.out`). The slot
fills from ABSTRACT adequacy (`module Elem.Given`: hand it `ψ` plus
`Adequate ψ`, and the actual `Recursion` and `Definition` records of
`src/L/Recursion.lagda.md` instantiate and the machine runs). No term `ψ`
exists in this tree. The two ingredients of the graph's class predicate that
the object language cannot name are both stated as types at their own sites
(`module Ingredients`, citing `src/L/StageCardinal.lagda.md:281-282` for the
meta syntax the existential ranges over and `:288-289` with `:283` for the
count through `ih`, which is the recursion's own value at a member).

**4. THE TREE'S TWO INTERNALIZED RECURSIONS ARE THE PRECEDENT AND THE PRICE.**
`src/L/Coding/Graph.lagda.md:238` (`satGraph`, adequate by `L.Coding.Uniform`'s
`exists` and `unique`) internalized the satisfaction recursion, and
`src/L/Coding/Sequence.lagda.md:353` (`LsetGraph`, adequate by
`src/L/Hierarchy.lagda.md`'s `Lset-defines` and `Lset-only`) internalized the
tower. Both steps read their argument through the satisfaction machinery
alone. `stage-card-upper`'s step does not: `class-pred`
(`src/L/StageCardinal.lagda.md:319-324`) re-reads the system being built
through `cnt`, which counts formula CONSTANTS through the branch injection.
That is why the missing graph is a chapter and not a formula: it is the
level-recursion formula with the bound witness, which `[LJ-1.594]` had already
priced as "the one `Formula` that ties them together, with its `defines` and
its `only`... That is a chapter of `src/`"
(`agents/tasks/LJ-1-594/Probe594.agda:434-439`).

**5. AND THE DATA DOES NOT REACH THE MACHINE EITHER.** `stage-card-upper`
needs the square-law family as MODULE DATA (`src/L/StageCardinal.lagda.md:17-20`),
and the tree reaches `SqFam` only through `SqCollect`, marked "Not inhabited"
(`src/L/StageBound.lagda.md:42`). `[LJ-1.592]` measured that the
propositional-motive induction dissolves this collection
(`agents/tasks/LJ-1-592/Probe592.agda:275-279`) and that what remains is the
code, which is rows 3 and 4 here. `B9Inf`'s three hypotheses supply the
truncated square only.

## WHAT WOULD REOPEN THIS

**ONE CHAPTER OF `src/`, NOW NAMED BY A TERM AND NOT BY A PARAGRAPH.** The
probe's conditional says exactly what it must deliver:
`b9inf-given-graph` (`agents/tasks/LJ-1-596/Probe596.agda`, section 3.4). At
the bill's own pair, given

1. an ambient injection `g : ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫`, and
2. `Machine.Input`: a total function that pair-codes `g` on the domain, and a
   `Formula S 2` adequate to it in both directions,

the machine's table IS an `InjCode`, all four conjuncts, and `InjL Lδ δ`
follows. The function half of input 2 is constructible from LEM alone (W3's
`Elem.fn`); **the formula half is the chapter.** Whoever writes it gets B9Inf
from this file's own term, and with it, by `[LJ-1.593]`'s corollary
(`square-from-b9inf`, `agents/tasks/LJ-1-593/Probe593.agda:521-530`), the
coded square law.

The classical shape of that chapter is on record: the level-recursion formula
`E(f, α)` with the bound set `K(u)`, "the finite sequences over formulas,
variables and members of u" (`dev/literature/devlin-II5.md:337-347`, item 7),
whose witness is the level sequence. `[LJ-1.86]`'s warning stands for its
frame: the stage containing `AllCodes A` exists and the proof cannot choose
it, because `lam` is a module parameter at every frame
(`archive/dev/LJ-dispatch-index.md:160`).

## WHAT I DID NOT DO

**I DID NOT FUND OR ATTEMPT THE SQUARE LAW** (`[LJ-1.593]` forbids it:
`agents/tasks/LJ-1-593/review-of-square-coded.md:73`). **I DID NOT ATTEMPT
"ANY CODED INJECTION"** (`[LJ-1.592]` measured the count is three:
`agents/tasks/LJ-1-592/review-of-stage-counted.md`). **I DID NOT INHABIT
`B9Inf`, AND THE CONDITIONAL IS NOT A DISCHARGE**: its two inputs are
hypotheses, and neither exists in the tree today. I did not edit `src/`, did
not postulate, did not set `GHCRTS`, did not commit and did not push.
