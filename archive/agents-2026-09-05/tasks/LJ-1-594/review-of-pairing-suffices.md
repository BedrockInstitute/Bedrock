# NO-GO: `pairing-suffices`

The obligation `agents/tasks/LJ-1-594/Probe594.agda::pairing-suffices` is NOT in
the probe. This file states why, names the terms that block it, and gives the
price of route 2 in the machines the tree already holds.

**THE PROBE IS GREEN, EXIT 0, FIVE RUNS** (`agents/tasks/LJ-1-594/runs/final-1.out`
to `final-5.out`), of which `final-3`, `final-4` and `final-5` postdate the last
edit to `Probe594.agda`. Nothing is postulated, there is no hole, `--safe` is on,
and nothing landed in `src/`.

## THE ANSWER IS NOT THE ONE THE BRIEF ANTICIPATED

The brief says: "**If your hypothesis is as strong as the conclusion, it is not a
reduction and you must say so plainly.**"

**THE HYPOTHESIS IS NOT AS STRONG AS THE CONCLUSION. IT IS TOO WEAK.**
`DefPairing` (`agents/tasks/LJ-1-594/Probe594.agda:199-210`) describes ONE binary
function on the members of ONE ordinal. The conclusion is an injection of a whole
stage. The hypothesis is strictly weaker, and it is still not sufficient. That is
a different failure from the one the brief priced for.

## THE BRIEF'S CENTRAL PREMISE IS FALSE AS MEASURED

The brief quotes `[LJ-1.584]` and builds the task on it:

> "`class-pred`'s other two ingredients are already internal ... **THE PAIRING IS**
> [the only non-internal part]."

and concludes "**SO TWO OF THE THREE INGREDIENTS ARE ALREADY INTERNAL** ... the
module is one substitution away from carrying a formula".

**`class-pred` HAS FIVE INGREDIENTS, NOT THREE, AND THIS IS A THEOREM AND NOT A
READING.** `class-pred-is` (`Probe594.agda:283-300`) writes
`src/L/StageCardinal.lagda.md:319-324` out by `refl`, with the pairing already
replaced by `sq` applied. Read its right hand side:

| | ingredient | status |
|---|---|---|
| (i) | `D`, the definable power set | INTERNAL. `D-at-the-site`, `Probe594.agda:227-234`: at the real site `limit-step` supplies `DefOf.defSet (Lset ·)` and `𝒟ₒ-inv` (`src/L/StageCardinal.lagda.md:400-401`) |
| (ii) | the least-element selection | INTERNAL. `h-is-leastOf`, `Probe594.agda:305-317`: `leastOf` over `OrdSWO.ordSWO` (`src/L/StageCardinal.lagda.md:349-351`, `:258-264`) |
| (iii) | the pairing `fst (sq α α∈suc infα)` | THE HYPOTHESIS. `pair-is-sq`, `Probe594.agda:238-243`, which is `[LJ-1.584]`'s W3 imported (`agents/tasks/LJ-1-584/runs/W3a.agda:41-46`) |
| (iv) | **`ih m`, the injection at the stage BELOW** | **NOT INTERNAL AND NOT THE PAIRING** |
| (v) | **`Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`, the META syntax the existential ranges over** | **NOT THE PAIRING** |

**(iv) AND (v) ARE THE TWO THE PREDECESSOR DID NOT COUNT.** Neither is reached by
substituting the module parameter, and that is the whole content of this NO-GO.

## (iv) IS THE TARGET ITSELF, ONE STAGE DOWN

`cnt-is-the-IH` (`Probe594.agda:252-263`) is `refl`: the counting term
`cnt` (`src/L/StageCardinal.lagda.md:288-289`) is
`fst (Bound.formula-bound (ih m))`, computed from `LimitStep`'s fifth argument
`ih` and from nothing else the pairing controls.

At the real site that argument is `branch` (`src/L/StageCardinal.lagda.md:562`),
whose own argument is the induction hypothesis of `stage-card-upper`'s
`∈-induction` (`:564-566`). `branch-at-the-site` (`Probe594.agda:327-332`)
re-ascribes it, TYPE ONLY, and `P-is-the-injection` (`Probe594.agda:337-341`) is
`refl`: `Upper.P δ` IS `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫`
(`src/L/StageCardinal.lagda.md:530-532`).

**SO "THE INDUCTION HYPOTHESIS" AND "THE THING BEING BUILT" ARE ONE TYPE.** A
formula for the injection at α therefore presupposes formulas for the injections
below α. A pairing does not supply them.

**TYPE ONLY, ON PURPOSE.** `[LJ-1.584]` measured that putting `step` into a
conversion problem does not terminate (`agents/tasks/LJ-1-584/runs/w3b-1.out`,
180 s, not a heap event). No row of this probe puts `step`, `branch` or
`stage-card-upper` into one.

## (v) IS META SYNTAX OVER AN AMBIENT CARRIER

The existential of `class-pred` ranges over `Formula ⟪ Lset δ ⟫ 1`: Agda's
formula type at a carrier that is the members of an ambient set. A formula of the
object language cannot quantify over it without a coded copy inside L. The
pairing hypothesis says nothing about it.

## THE PRICE, AND IT IS THE HALF WORTH DISPATCHING

**EVERY ONE OF THE FIVE INGREDIENTS HAS A MACHINE IN `src/` TODAY.** (i) and (ii)
are in the table above. (iii) is the hypothesis. The two the predecessor missed
are the two this file expected to be missing, and NEITHER IS:

1. **(iv) COSTS A FORMULA AND NOT A NEW INDUCTION PRINCIPLE.**
   `src/L/Recursion.lagda.md` is titled "Recursive definitions are
   internalizable" (`:1`) and its condition is the graph alone: "A recursive
   definition is internalizable when its graph is expressible, and nothing about
   the recursion's shape, its depth, its order of descent, or the complexity of
   its clauses appears in the condition" (`src/L/Recursion.lagda.md:259-261`).
   `recursion-from-a-definition` and `table-of` (`Probe594.agda:362-370`)
   re-ascribe `asRecursion` and `Of.table`. And the tower the recursion descends
   is ALREADY an object of L: `hierL` (`src/L/Hierarchy.lagda.md:621-622`),
   re-ascribed at `Probe594.agda:376-382`.

2. **(v) IS ALREADY CODED.** `L.Coding.CodeSet` gives every meta formula over an
   ambient carrier `⟪ fst A ⟫` a code that is an L-set
   (`src/L/Coding/CodeSet.lagda.md:300-301`) and collects them at every arity
   into one L-set (`src/L/Coding/CodeSet.lagda.md:440-443`).
   `coded-syntax`, `all-codes` and `coded-syntax-collected`
   (`Probe594.agda:392-401`) re-ascribe them. At `A := LsetS δ oδ` the carrier is
   exactly `⟪ Lset δ ⟫`, which is (v)'s.

**SO WHAT IS MISSING IS ONE `Formula`, WITH ITS `defines` AND ITS `only`**: the
object-language rendering of `class-pred`, tying (i) to (v) together. **That is a
chapter of `src/`, and it is not the substitution of a module parameter.** The
brief's estimate of about 160 probe lines is the right size for THIS
measurement; it is not the size of that chapter, and nothing here funds one.

## THE C-42 SWEEP: HOW FAR THE SHAPE EXTENDS

C-42 orders the count before the cure. The refutation above names ONE site. The
shape it names is **a selection predicate that quantifies over `Formula` at an
AMBIENT carrier**, written `Formula ⟪ ... ⟫`. Grepped at today's tree with
`grep -rn "Formula ⟪" src/`:

**80 LINES IN 16 FILES.** By file: `src/L/Coding/Powerset.lagda.md` 15,
`src/L/Coding/CodeSet.lagda.md` 12, `src/L/StageCardinal.lagda.md` 11,
`src/L/Definability.lagda.md` 7, `src/L/Coding/Uniform.lagda.md` 7,
`src/L/Choice/Name.lagda.md` 5, `src/L/Coding/Key.lagda.md` 4,
`src/L/Axioms/Separation.lagda.md` 4, `src/L/Axioms/Basic.lagda.md` 4,
`src/L/Choice/Internal.lagda.md` 3, `src/L/Constructible.lagda.md` 2,
`src/L/Coding/Bridge.lagda.md` 2, and one each in
`src/L/Ordinal/Stages.lagda.md`, `src/L/Coding/EnvSupply.lagda.md`,
`src/L/Choice/Faithful.lagda.md`, `src/L/Choice/Adequate.lagda.md`.

**THE COUNT'S MEANING IS NOT "16 BLOCKED SITES", AND SAYING SO WOULD BE THE
ERROR C-42 EXISTS TO STOP.** Two of the sixteen, `Coding/CodeSet` and
`Coding/Powerset`, are the CURE for the shape and not an instance of it: they are
where the coded copy is built. The sweep's real finding is that the shape is
common and that the tree already answered it twice.

## WHAT WOULD REOPEN IT

**Not this brief's obligation, and not at this brief's price.** Two routes, and
the second is not this task's.

1. **WRITE THE `Formula` FOR `class-pred`, AS A CHAPTER.** Its five ingredients
   are the table above and every one has its machine. The order the pieces go in
   is (v) first, because the existential's range has to exist before the rest of
   the clause can be written: `keyS` at `A := LsetS δ oδ`. Then (i) and (ii),
   which are already internal. Then (iv) through `L.Recursion`'s `Definition`,
   whose `dom` is `hierL`. **The pairing, (iii), goes in LAST and is the smallest
   of the five.** A brief that asks for the whole formula in one dispatch is
   asking for a chapter; the first dispatch worth ordering is (v) at this
   carrier, because it is the one nobody has instantiated here.

   **AND THAT FIRST DISPATCH HAS A HISTORY THE ARCHIVE ALREADY RECORDS.**
   `archive/dev/LJ-dispatch-index.md:160`: "`| LJ-1.86 | Is there a stage
   containing AllCodes A | EXISTS; proof cannot choose it | AllCodes-stage is
   green. But lam is a module parameter at every frame, so the obligation moves
   to the frame |`". So `AllCodes` at a carrier is not new ground, and the
   known failure is not the code set: it is choosing the stage that holds it.
   A brief that orders (v) must say which stage, and `[LJ-1.86]`'s answer is
   that the frame decides.

   **AND IT MUST NAME THE LIVE CHAPTER, NOT THE RETIRED ONE.** `dev/ARCHIVE.md:267`
   retires `L.Rud.CodeSet` (`src/L/Rud/CodeSet.lagda.md`), a DIFFERENT chapter
   from the live `src/L/Coding/CodeSet.lagda.md` this file re-ascribes. The two
   names differ by one component.

2. **`[LJ-1.592]`'s ROUTE 1 IS UNTOUCHED BY THIS FILE.** It aims at `Reopener`
   directly and never names `stage-card-upper`, so none of (i) to (v) binds it.
   This NO-GO leaves it carrying the object alone, exactly as the brief said a
   route-2 NO-GO would.

## WHAT IS NOT CLAIMED

**THE TARGET IS NOT FALSE AND THIS FILE DOES NOT REFUTE IT.** `V = L` gives it
outright: `vl→target` (`Probe594.agda:135-140`), through `[LJ-1.584]`'s
`vl→obligation` (`agents/tasks/LJ-1-584/Probe584.agda:108-118`) and
`def-h→target` (`Probe594.agda:124-129`). So a refutation of the target is a
refutation of `V = L` (`refuting-target-refutes-V=L`, `Probe594.agda:146-152`).

**AND THE SECOND HALF OF ROUTE 2 IS FREE AND ALREADY BUILT.** `def-h→target` is
`[LJ-1.568]`'s `restrict→B9` at its own THEOREM `def-restricted`
(`agents/tasks/LJ-1-568/Probe568.agda:285`, `:252`), so it spends no hypothesis:
whoever writes the formula gets `InjL (Lset α) α` for nothing. **The block is
entirely in producing the formula, and nowhere after it.**

**NO ROW OF THIS FILE CLAIMS A SECOND LEDGER ROW.** `[LJ-1.585]` measured that
this object buys at most one (`agents/tasks/LJ-1-585/Probe585.agda:163`).
