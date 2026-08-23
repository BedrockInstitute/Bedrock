# NO-GO: `stage-counted`

The obligation `agents/tasks/LJ-1-592/Probe592.agda::stage-counted` is NOT in
the probe. This file says why, names the term that blocks it, and names what
would reopen it.

**THE PROBE IS GREEN, EXIT 0, FOUR CLEAN RUNS**
(`agents/tasks/LJ-1-592/runs/final-1.out` to `final-4.out`, each after the
interface file was deleted). Nothing is postulated, there is no hole, `--safe`
is on (`agents/tasks/LJ-1-592/Probe592.agda:1`), and nothing landed in `src/`.

## THE OBLIGATION'S TYPE IS WRITTEN AND IT IS NOT INHABITED

`Target` (`agents/tasks/LJ-1-592/runs/W3.agda:55-56`) is `[LJ-1.584]`'s
`Reopener` (`agents/tasks/LJ-1-584/Probe584.agda:250-251`), taken as the type
that predecessor delivered. It is `InjL (LsetS α oα) (ordS α oα)` at an
ordinal `α` and no other hypothesis.

## ROUTE 1'S PERMISSION IS REAL, AND THE PROBE MEASURES IT

W3 is inhabited. `isPropTarget` (`runs/W3.agda:64-65`) is `squash₁` and nothing
else, because `InjL a b` is `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
(`src/L/GCH.lagda.md:37-38`) and the truncation is OUTSIDE the Σ. So
`untrunc-free` (`runs/W3.agda:70-72`) holds at EVERY hypothesis type and at
every universe level. **The recursion is legal and it is free.**

**AND IT DOES NOT REST ON `isPropInjCode`.** The brief gives
`agents/tasks/LJ-1-576/Probe576.agda:77-84` as the measured basis. That term is
true and it is about a different type: it says the Σ's BODY is a proposition.
The permission needs only the truncation. The probe records this at
`Probe592.agda:91-96`.

## AND ROUTE 1 WINS SOMETHING REAL WITH IT

**THE OLD MOTIVE NEEDS A COLLECTION THAT THE TREE MARKS "NOT INHABITED".**
`stage-card-upper` (`src/L/StageCardinal.lagda.md:564-565`) concludes at
`⟪ Lset α ⟫ ↪ ⟪ α ⟫`, which is not a proposition, so its `∈-induction` takes the
square law as DATA at every sub-stage. That is `SqFam`
(`src/L/StageBound.lagda.md:36-40`), and the tree reaches `SqFam` only through
`SqCollect`, which `src/L/StageBound.lagda.md:42` marks "Not inhabited".

**THE TARGET IS A PROPOSITION, SO THAT COLLECTION IS NOT NEEDED.**
`coded-step→restricted` (`Probe592.agda:275-279`) is the same induction over
the propositional motive. It spends `sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-328`) POINTWISE through `sq-trunc-spends`
(`Probe592.agda:245-249`). **It is green, and it uses no `SqFam`, no
`SqCollect` and no `sq` module parameter.** The top-level module of the probe
takes `lem`, `α₀` and `oα₀` only (`Probe592.agda:38-39`), unlike every
predecessor at this site (`agents/tasks/LJ-1-561/Probe561.agda:44-49`,
`agents/tasks/LJ-1-568/Probe568.agda:45`,
`agents/tasks/LJ-1-584/Probe584.agda:38-43`), so the claim is a fact of the
module structure and not an assertion.

**WHAT REMAINS IS ONE TERM, AND THE PROBE NAMES IT.** `CodedStep`
(`Probe592.agda:263-268`): at a stage `δ`, with the square law at `δ` as data
and the CODED conclusion already held at every member of `δ`, produce the coded
conclusion at `δ`.

## THE BLOCK: `CodedStep` IS A CODE, AND THE TRUNCATION NEVER TOUCHED IT

**THIS IS THE FINDING, AND IT CLOSES ROUTE 1.**

1. The target reads back as an ambient injection. `target→ambient∥`
   (`Probe592.agda:107-110`) is `readL` (`src/L/CantorBernstein.lagda.md:33-38`)
   under `PT.map`.
2. The square-law family builds the ambient injection. `sqfam→ambient`
   (`Probe592.agda:332-335`) is `stage-card-upper` itself.
3. The arrow between them in the missing direction is `W`. `ambient→target`
   (`Probe592.agda:343-344`) is `[LJ-1.561]`'s `w→code` (`Probe561.agda:287`), and
   `W` (`Probe561.agda:160-163`) is "the graph of every ambient injection
   between L-elements is in L".
4. And `W` pays `CodedStep` outright: `w→coded-step` (`Probe592.agda:368-370`).

So the two routes meet at `W` (`trunc-route-meets-W`, `Probe592.agda:358-363`).
**What the propositional motive removed is the COLLECTION. It did not remove the
CODE.** `W` is `[LJ-1.554]`'s missing input and `[LJ-1.533]`'s wall
(`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`).

## AND "ANY CODED INJECTION" IS NOT A FREE CHOICE. THE COUNT IS THREE

C-42 orders the count before the cure (`dev/LESSONS.md:3752`). Here the shape
is the brief's own permission, "build ANY coded injection", so the number that
settles it is how many ways the tree can build one. **THE TREE BUILDS A CODED
INJECTION IN THREE WAYS AND NO MORE.**

| way | site | what it needs |
|---|---|---|
| separation at `inclFo D` | `src/L/InjChain.lagda.md:480` | `D ⊆ C`; the range conjunct at `:544-547` is where the subset witness is spent |
| separation at `shiftFo D γ ω z` | `src/L/Absorption.lagda.md:413` | the pair `(sucʟ γ , γ)` |
| composition of two codes held | `src/L/InjChain.lagda.md:314-446` | both legs |

Six files of `src/` name `InjCode`. Two are the definition and its truncation
(`src/L/Cardinal.lagda.md:223-228`, `src/L/GCH.lagda.md:37-38`), one is a
comment (`src/FOL/Bernstein.lagda.md:106`), one is a CONSUMER
(`src/L/CantorBernstein.lagda.md:33-38`), and the last two are ONE term by the
elaborator (`agents/tasks/LJ-1-587/Probe587.agda:223-230`). Every other
`hasSeparationL` application in `src/` carves something that is not an
injection graph (`src/L/Axioms/Power.lagda.md:190`,
`src/L/Choice/Before.lagda.md:232`, `src/L/Choice/Table.lagda.md:785`,
`src/L/Choice/Limit.lagda.md:608`, `src/L/Coding/CodeSet.lagda.md:310`,
`src/L/Coding/EnvSet.lagda.md:190`), and `src/L/Coding/Key.lagda.md:258` is a
third `Carve` that names no `InjCode`.

**SO A NEW CODED INJECTION IS A NEW `Formula S 1` PLUS A BOUND, SEPARATED.**
That is `[LJ-1.568]`'s `Def` (`agents/tasks/LJ-1-568/Probe568.agda:189`), and
`[LJ-1.584]` refuted it at the only injection this pair has. **The truncation
supplies no formula.** `archive/dev/JOURNAL.md:940` records what the square law
supplies instead: `src/L/StageCardinal.lagda.md:15-19` demands an injective
`⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` "and nothing more".

## THE TWO `[LJ-1.587]` PRODUCERS, TRIED, AS THE BRIEF ORDERS

Both are applied at this pair and both typecheck, so what is measured is the
input each still wants.

- `injL-from-subset` (`agents/tasks/LJ-1-587/Probe587.agda:255-257`) gives
  `subset-route` (`Probe592.agda:160-163`). Its hypothesis is `Lset α ⊆ α`.
  **NOT AVAILABLE.**
- **AND THE SAME PRODUCER PAYS THE CONVERSE OUTRIGHT.** `ord-into-stage`
  (`Probe592.agda:173-174`) is green with no hypothesis: in L, every ordinal
  injects into its own stage. The tree's inclusion runs the other way
  (`src/L/StageCardinal.lagda.md:193-195`).
- `injL-compose` (`Probe587.agda:259-261`) gives `compose-route`
  (`Probe592.agda:195-198`). It wants a middle `b` and BOTH legs. The left leg
  is the target's own shape at `b`, so the producer moves the problem. **NO
  MIDDLE IS OFFERED.** The one middle the tree hands over free is the wrong way
  round (`converse-composes`, `Probe592.agda:204-208`).

**NEITHER SUFFICES.**

## IT IS NOT REFUTED, AND THE TYPE AS WRITTEN IS STILL TOO WIDE

**THIS FILE DOES NOT CLAIM THE STATEMENT IS FALSE.** `w→restricted`
(`Probe592.agda:351-352`) is `[LJ-1.561]`'s `w→B9` (`Probe561.agda:376-381`), so a
refutation of the restricted row would refute `W`.

**BUT THE TYPE AS WRITTEN QUANTIFIES OVER EVERY ORDINAL, AND THE EXCESS HAS
NOTHING TO DO WITH CODING.** `Reopener` takes `IsOrd α` and nothing else, so
`target→ambient∥` holds at finite ordinals too, where the tree proves no
ambient injection: `stage-card-upper` carries `α ∈ˢ sucV α₀` and `α ∉ ω`
(`src/L/StageCardinal.lagda.md:564-565`), and
`archive/dev/LJ-dispatch-index.md:81` records the coverage as "every infinite
alpha". `[LJ-1.585]`'s `side-conditions-are-false`
(`agents/tasks/LJ-1-585/Probe585.agda:219-227`) refutes the SUPPLY of those two
conditions at δ := 0. The classical statement is also restricted: Devlin
1.1(vii) is `|L_α| = |α|` for infinite α (`dev/literature/devlin-II5.md:155-156`).

**I DID NOT PROVE THE FINITE CASE FALSE.** `[LJ-1.533]`'s review says in its
own words that it "did not prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named
finite δ" (`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55`), and
this file does not prove it either.

## WHAT WOULD REOPEN IT

**Not this route.** Three, and the first is the cheapest.

1. **CORRECT THE TARGET'S QUANTIFIER FIRST.** A next brief that keeps
   `Reopener`'s bare `IsOrd α` asks for a statement that is stronger than
   `L.StageCardinal` proves at ordinals below ω, for a reason that has nothing
   to do with `InjL`. `Restricted` (`Probe592.agda:129-132`) is the corrected
   target and `coded-step→restricted` already concludes at it.
2. **AIM AT `CodedStep`, WHICH IS SMALLER THAN `Reopener`.** It is one stage,
   with the square law as data and the CODED induction hypothesis in hand. It
   is not the whole tower. Priced against nothing measured; named as a route,
   not funded.
3. **GIVE THE PAIRING A FORMULA.** This is `[LJ-1.584]`'s route 2 in its own
   words (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:131-139`),
   and `[LJ-1.594]` carries it. Section 4 of the probe is why it is the only
   remaining shape: a new coded injection IS a new formula.

**AND ONE NAMED ROUTE IS NOW UNNECESSARY AT THIS TARGET.** `[LJ-1.584]`'s route
3 (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:141-148`) asks for
a weakly constant endomap on `sq δ`, because Kraus, Escardo, Coquand and
Altenkirch Theorem 16 makes such an endomap lift `∥ sq δ ∥₁` to `sq δ`
(`dev/literature/truncation-and-selection.md:158-160`). **THAT LIFT BUYS
NOTHING HERE.** The same literature file gives the first question to ask: "Is
the goal a proposition? Then `PT.rec` applies and there is nothing to discuss"
(`dev/literature/truncation-and-selection.md:288-289`). W3 says the goal IS a
proposition, and `sq-trunc-spends` (`Probe592.agda:245-249`) is the whole lift
in one line. **The endomap remains a route to a CANONICAL `stage-card-upper`,
which is a different object; it is not a route to this target.**

**WHAT IS DEAD.** Untruncating to reach this target. The probe shows the
untruncation is free (W3), that it removes `SqCollect`
(`coded-step→restricted`), and that the residue is still `W`
(`w→coded-step`). **A next brief that offers a truncated hypothesis at this
pair buys nothing that is not already in `Probe592.agda`.**
