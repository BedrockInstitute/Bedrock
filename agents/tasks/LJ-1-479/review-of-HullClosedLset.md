# LJ-1.479 review of `HullClosedLset`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The predecessor type, copied from
`agents/tasks/LJ-1-462/Probe462.agda:136-138`:

```agda
HullClosedLset :
    (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩
```

The probe restates that type as `HullOnV.HullStage.HullClosedLset` at
`agents/tasks/LJ-1-479/Probe479.agda:109-111`. Telescope:
`Probe479.agda:84-96`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below
`module Condense` is copied. There is no term named
`HullClosedLset` at the module root. The witness meter reports
`1 UNRESOLVED of 1` (`agents/tasks/LJ-1-479/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at uniqueness. `wit`'s value is not identified with `Lset y`.
This is not a refutation of the type. I did not build a term of the
negation.

W3 spent `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` as `pins`
(`Probe479.agda:50-54`). That uniqueness carries `IsOrd` on the
argument slot. The uniqueness without `IsOrd` is `pins-no-ord` at
`Probe479.agda:60-64`. Unbuilt. Same type as `LsetAt-out-brief` at
`agents/tasks/LJ-1-458/Probe458.agda:69-73`.

`IsOrd` has no source at a hull member. `hull-ord` at
`Probe479.agda:103-104` is unbuilt. The brief forbids an ordinality
hypothesis on `y`. I did not add one. I did not postulate.

## D-10, IN ONE LINE

`inHull (feed c)` is membership of `val (feed c)`
(`src/L/Hull.lagda.md:117-118`, `feed` at
`agents/tasks/LJ-1-474/Probe474.agda:130-131`). The join needs
`fst (val (feed c)) ≡ Lset y`. `Lset-only` gives that equation only
with `IsOrd`. The hull carries `⟨ y ∈ˢ M ⟩` and nothing else.

## WHAT THIS IS NOT

This is not a proof that `HullClosedLset` is false. C-42 does not
fire: there is no refutation to sweep. I did not inhabit `levelIn`.
I did not touch step 4. `[LJ-1.477]` remains the critic-upheld
NO-GO on the computation-law route
(`agents/tasks/LJ-1-477/lj-1.477-report.md:97`).
