# [LJ-1.607] stop: the untruncation at the band is the square law under another type, and the one route that could detach it needs a bridge the generators cannot build

## THE STOP

**NO-GO on `band-untruncation`.** The brief's obligation is the
untruncation of the data payload `[LJ-1.605]` names, at today's tree:

```
Untruncation =
    ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
      → (⟨ δ ∈ˢ ω ⟩ → ⊥) → Payload δ)
  → SqParam α₀
```

(`agents/tasks/LJ-1-607/runs/W3.agda:62-64`, where `Payload δ` is the
band's truncated fiber written out, `runs/W3.agda:46-50`, and the row
`runs/W3.agda:69-73` proves by `refl` that this IS
`[LJ-1.605]`'s `missing-direction-type`,
`agents/tasks/LJ-1-605/Probe605.agda:177-181`.) No term of the probe
has the name `band-untruncation`, and no term of the probe inhabits
that type. On a NO-GO the brief's type is not inhabited.

The brief's second disjunct, "or the term that refutes it here", is
what the probe delivers instead, at
`agents/tasks/LJ-1-607/Probe607.agda:228-229`: an untruncation,
composed with the band supply the tree already holds, IS `SqParam α₀`.
That is the untruncated square law at every infinite ordinal of the
band, by `[LJ-1.604]`'s product identity
(`agents/tasks/LJ-1-604/Probe604.agda:160-164`). Building the
untruncation here would not be cheaper than the square law. It would
BE the square law, and `[LJ-1.593]`'s review forbids funding it:
"A fourth dispatch on this object buys nothing that is not in this
file" (`agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`).

## THE EVIDENCE, ALL AT `file:line`

**1. THE BRIEF'S PREMISE ABOUT THE LOST CURE IS FALSE, AND THE CURE
IS GREEN AT THIS TREE.** `pick-canonical` lives at
`agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116`, in the probes'
tracked home, on the library's include path (`bedrock.agda-lib`,
`include: src agents/tasks`). It was rescued from an untracked life in
`src/` by `[LJ-1.227]`
(`archive/dev/JOURNAL.md:878-881`). Re-checked COLD at this dispatch,
verbatim copies at a restored include root: GREEN, exit 0, 1.83 s,
327 MB peak, cap 600 s (`agents/tasks/LJ-1-607/runs/p136-cold-1.out`).
Both halves elaborate today: the canonicity term, and `discharge`
(`agents/tasks/LJ-1-136/ProbeLJ1136B.agda:146-148`), which turns the
truncated existence of a constructible injective graph into an honest
injection.

**2. AND IT DOES NOT REACH THIS PAYLOAD, BY ITS OWN TYPE.**
`discharge` consumes `Ne = ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁`
(`agents/tasks/LJ-1-136/ProbeLJ1136B.agda:98-99`): the truncated
existence of a CONSTRUCTIBLE graph at a bounded stage. The band's
supply holds `∥ sq δ ∥₁`: the truncated existence of an AMBIENT
function package (`agents/tasks/LJ-1-607/runs/W3.agda:46-50`), which
carries no `Formula`, no L-set and no satisfaction
(`agents/tasks/LJ-1-594/runs/W3.agda:42-43`).

**3. THE PROPERTY COMPARISON THE BRIEF ASKED FOR, ANSWERED: NO.**
What lets `leastOf` untruncate on the coded side is that the code
family is an hProp: `InjCode` is four Ω-valued conjuncts
(`agents/tasks/LJ-1-576/Probe576.agda:77-84`). The band's payload has
no comparable property. It is a Σ whose first component is a function
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`), and the direct
elimination was REFUSED by the elaborator at this dispatch
(`agents/tasks/LJ-1-607/runs/direct-refused-1.out`, exit 42): the
trivial candidate for the demanded `isProp (sq δ)` does not check, and
no other candidate is in the tree. The tree's one elimination of a
truncation into data is `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-161`), whose goal is a proposition
by `isPropLeastOf` (`src/L/WellOrder/Base.lagda.md:136-139`); the
survey of all 66 `src/` files that use `PT.rec` found no other.

**4. THE ONE ROUTE THAT COULD DETACH THE UNTRUNCATION REDUCES TO A
BRIDGE THE TREE CANNOT BUILD.** The assembly row
(`agents/tasks/LJ-1-607/Probe607.agda:240-254`) proves, generically:
engine plus decoding plus BRIDGE gives the site's untruncation. The
engine is green today (evidence 1). The decoding is green today
(`discharge`, evidence 1). The bridge, from the ambient truncated
pairing to a coded truncated existence, has no term, and the reason is
`[LJ-1.533]`'s generator argument at today's lines: the only two
producers of an L-element set are `hasSeparationL`
(`src/L/Axioms/Full.lagda.md:144-146`) and `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:277-280`), both `Formula`-typed
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:107-111`), and
an ambient pairing carries no `Formula`. `[LJ-1.533]` measured the
wall for ambient injections; the bridge wants ambient pairings; the
generators are the same two. This last step is an inference and is
marked as one in the report.

**5. THE CIRCLE, CONFIRMED AS A TERM.** `[LJ-1.605]` measured that
the uniform pairing IS the square law at the band; this task's
`the-circle` row proves the same for the untruncation: composed with
`sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325-328`), the
supply the tree already holds, it is `SqParam α₀`. So the untruncation
is not a way around the square law. It is the square law under another
type, and the route change the mathematician takes to the owner is:
both exits of this point are measured shut, the square law by
`[LJ-1.593]`'s funding rule and the bridge by `[LJ-1.533]`'s generator
count.

## WHAT THE BRIEF WILL NOT HAVE FROM THIS TASK

- No term named `band-untruncation` is written: on a NO-GO the brief's
  type is not inhabited.
- Nothing is postulated, and nothing landed in `src/`.
- The probe is GREEN (`agents/tasks/LJ-1-607/runs/final-2.out`,
  `final-3.out`, exit 0), carries no hole and no postulate, so every
  row in it is a measurement and not a claim.
- The square law, B9 and the uniform pairing were not attempted: this
  task is the root and nothing above it.

## WHAT IS NOT CLAIMED

- The target is not false: classically, split support for an inhabited
  type follows from a canonical selection, and inside L one exists.
  The NO-GO is a funding and dispatch-count statement about the tree,
  not a truth statement about set theory.
- `isProp (sq δ)` is not REFUTED here. The direct route is measured
  REFUSED, and no proof of the property is in the tree; that is the
  honest extent of the measurement.
- The bridge wall at PAIRINGS is an inference from `[LJ-1.533]`'s
  measured wall at INJECTIONS, over the same two generators, and the
  report marks it as an inference. A measured wall does not transfer
  by analogy; what transfers here is the generator count, which is a
  type-level fact read at today's lines, and the reduction row that
  makes the bridge the only missing piece.
