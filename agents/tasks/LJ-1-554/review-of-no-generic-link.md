# Review of `no-generic-link`

**THE OBLIGATION IS NOT INHABITED, AND NEITHER IS THE GENERIC `Link`.** The brief
said one of the two is true and that the task is to find out which. **The measured
answer is that neither is reachable in this tree, and the reason is a type
argument and not a failed search.** This file is the obstruction, for the branch
`stop-stated`.

`agents/tasks/LJ-1-554/Probe554.agda` is GREEN, exit 0, three runs
(`runs/final-1.out` to `runs/final-3.out`). It carries no hole and no postulate.
That is deliberate: a hole makes every reduction a claim, and green makes each
one a measurement. Nothing lands in `src/`.

## THE STATEMENT

    no-generic-link :
      ( (δ κ : S) (s : ⟪ fst δ ⟫ → S)
        → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
        → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
        → Σ[ Link ∈ Formula S 3 ] <the two readings> )
      → Empty.⊥

It is `Probe554.agda:95-96`, written as `NoGenericLinkᵀ` over `GenericLink`
(`:88-93`).

**THE TYPE IS `[LJ-1.549]`'s RESIDUE AND NOT A PARAPHRASE OF IT.**
`generic→residue` (`Probe554.agda:99-105`) delivers `P549.Residue δ κ`
(`agents/tasks/LJ-1-549/Probe549.agda:668`) from the hypothesis, and
`residue→generic` (`Probe554.agda:107-113`) is the identity in the other
direction. So the brief's `<the two readings of [LJ-1.549]'s Residue>` is the
type this file measures, and it cannot have drifted.

## FINDING 1. D-10. THE COUNTING DOES NOT FIRE, AND THE TREE SAYS SO ITSELF

The brief offered the argument: "If the formulas are a set and the assignments
are a function space into a proper carrier, say so: that is the whole argument
and the rest is writing it down."

**THE FORMULAS ARE NOT A SET.** `Formula K n` takes its constants from `K`
(`src/FOL/Syntax.lagda.md:43`, `con : K → Term K n`), and the `K` here is `S`,
the L-carrier itself. The book states the consequence in its own prose,
`src/FOL/Syntax.lagda.md:138`:

> a syntax whose constants are all sets is too big to be
> counted or coded

**MEASUREMENT 1, MACHINE-CHECKED.** `nameOf` (`Probe554.agda:144-145`) maps
every L-set to a formula of `Formula S 3`, and `nameOf-inj` (`:147-148`) proves
that map injective. So `Formula S 3` is at least as wide as `S`. There is no
room for a counting argument between the two sides.

**MEASUREMENT 2, MACHINE-CHECKED, AND IT IS THE SHAPE OF THE WHOLE ANSWER.**
The graph of the assignment is ALREADY an ambient set, with no hypothesis at all.
`grV` (`Probe554.agda:160-161`) is `sett ⟪ fst δ ⟫ (λ k → pr (⟪ fst δ ⟫↪ k)
(fst (s k)))`. Membership in it is definitional, so both readings are the
identity function: `grV-in` (`:163-165`) and `grV-out` (`:167-170`).

**SO NOTHING IS MISSING AMBIENTLY.** What is missing is `isL` of that one set.
`isL` is not a size condition (`src/L/Constructible.lagda.md:376-377`).

## FINDING 2. `Link` AND THE CODED GRAPH ARE THE SAME REQUEST

`IsGraphOf δ s G` (`Probe554.agda:190-195`) says that the L-element `G` has the
ordered pairs of the assignment as members. It names no formula.

**FORWARD.** `link→graph` (`Probe554.agda:198-211`) takes the `Link` and returns
such a `G`. It rebuilds nothing: it runs `[LJ-1.549]`'s `module Table`
(`agents/tasks/LJ-1-549/Probe549.agda:268-438`), whose separation is what carves
`G` out of the bound.

**CONVERSE.** `graph→link` (`Probe554.agda:232-265`) takes such a `G` and returns
a `Link`. The formula is `LinkFo` (`:228-230`), one line:

    LinkFo G = ∃̇ ( prAtL zero (suc (suc zero)) (suc zero) ∧̇ (var zero ∈̇ con G) )

**THE CONVERSE IS CHEAPER THAN THE FORWARD DIRECTION.** It takes no `κ`, no
`⊆ˢ`, and no injectivity. So the two requests are the same request, and the
`Link` half of `[LJ-1.549]`'s residue adds nothing to the coded graph.

## FINDING 3. THE ONE PROPERTY OF `s` THAT BUYS A `Link`

`constructible-graph→link` (`Probe554.agda:307-309`) has this type:

    (δ : S) (s : ⟪ fst δ ⟫ → S) → ⟨ isL (grV δ s) ⟩ → LinkAt δ s

**ONE PROPOSITION, AND IT IS ABOUT ONE NAMED SET.** Not a bound: finding 1 builds
the ambient set with no hypothesis, and `[LJ-1.549]`'s `bnd`
(`agents/tasks/LJ-1-549/Probe549.agda:289-290`) already has the L-side bound from
`s` alone. Not a Levy grade: nothing in this reduction is graded. Not a count:
finding 1 measures that the count does not fire.

## FINDING 4. WHY NEITHER DIRECTION IS REACHABLE

Section 4 of the probe writes three statements and two arrows between them
(`Probe554.agda:312-364`):

    GenericConstructible  ⟹  GenericLink  ⟺  GenericGraph

`no-link→no-constructible` (`Probe554.agda:363-364`) is the consequence in one
line: **an inhabitant of `NoGenericLinkᵀ` refutes `GenericConstructible`.**

**TO REFUTE `GenericConstructible` YOU MUST EXHIBIT ONE AMBIENT SET THAT IS
PROVABLY NOT CONSTRUCTIBLE. THE TREE HAS NONE.**

    grep -rn "isL" --include="*.agda" --include="*.lagda.md" src/ agents/tasks/

with `isL` as the antecedent of a `⊥`: **0 hits.** No term of `src/`, and no term
of any live probe, refutes `isL` of anything.

**AND THE TREE HAS ALREADY RECORDED THAT THIS DIRECTION IS INDEPENDENT RATHER
THAN FALSE.** `dev/memos/2026-08-16-pause.md:515-518`:

> **AND THE MISSING DIRECTION IS INDEPENDENT, not false.** `[LJ-1.300]`
> corrected `[LJ-1.299]`'s label: `AmbientToCode` is TRUE whenever the ambient
> universe satisfies V=L, and FALSE under a Levy collapse. **So no proof and no
> countermodel can settle it inside this development.**

**THAT RECORD IS A MEASUREMENT AT ANOTHER SITE, AND A MEASURED CURE DOES NOT
TRANSFER BY ANALOGY.** Findings 2 and 3 are the re-measurement HERE. They turn
the arity-3 `Link` of `Residue` into exactly that crossing, in both directions,
with no hypothesis left over. That is why the record applies, and I did not take
it on trust.

**SO THE BRIEF'S ESCAPE CLAUSE FIRES.** The brief said: "IF THE REFUTATION NEEDS
A CARDINALITY FACT THE TREE DOES NOT HAVE, SAY SO AND STOP." The refutation needs
a fact of that family and the tree does not have it. I did not import one and I
did not postulate one.

**I CHECKED BEFORE I BELIEVED IT, AS THE BRIEF ORDERED.** `[LJ-1.526]` overturned
an archived cardinal claim by measurement, so I re-measured rather than read.
`[LJ-1.526]` itself states the same gap at its own site,
`agents/tasks/LJ-1-526/Probe526.agda:110-116`: the converse of the cardinal
readback is "STATED AND NOT inhabited", and its comment gives the same reason,
"the definability direction of the readback".

## THE ARROW I DID NOT BUILD, STATED AS A LIMIT AND NOT AS A RESULT

`GenericGraph → GenericConstructible` is NOT built and I do not claim it.
`IsGraphOf δ s G` constrains only the PAIR members of `G`, so a witness may carry
other members and need not be `grV δ s` on the nose. The three statements form a
triangle and not a cycle. The comment says so at `Probe554.agda:325-329`.

**WHAT THIS COSTS THE FINDING: NOTHING.** The obligation is `GenericLink → ⊥`,
the middle equivalence is built in both directions, and the left arrow is all
that finding 4 spends.

## THE SWEEP (C-42)

The shape is "a residue that asks an L-element to describe an object the tree has
only as an ambient function". **THE COUNT OF RECORDED STOPS IS SIX, AND THIS TASK
IS THE SIXTH.** The rows are named at `Probe554.agda:404-417`. One neighbour,
`[LJ-1.535]`, looks like the shape and is not, and the comment says why.

**WHAT THE SWEEP DOES NOT MEASURE.** I counted recorded stops. I did not count
the rows of the campaign that will meet this wall and have not been dispatched,
because that count is not in the tree.
