# LJ-1.466 review of `lset-codes`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The named term, from the brief:

```agda
lset-codes : Vec Code (countFo LsetGraph)
```

Telescope: `agents/tasks/LJ-1-466/Probe466.agda:61-64`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below `module Condense`
is copied. There is no term named `lset-codes`. The witness meter reports
`1 UNRESOLVED of 1` (`agents/tasks/LJ-1-466/runs/witness.out:1-2`).

## THE VERDICT

NO-GO. The vector does not inhabit at a general `X`. Every constant of
`LsetGraph` is a class-carrier numeral `numeralL k` for some
`k ∈ {0,1,...,11}`. `base` takes a member of `X`
(`src/L/Hull.lagda.md:73`, instantiated at `:323` with `K = ⟪ X ⟫`).
A general `X` in the consumer telescope does not contain those numerals.

This is a condition on the hull. It is not a hypothesis I added. I did
not postulate. I did not inhabit `lset-codes`.

This is an obstruction of the hull-language route at the extra `Vec Code`
that `[LJ-1.462]` named. It is not a refutation of `levelIn`.

## W3, THE LENGTH

`how-many = countFo LsetGraph` (`Probe466.agda:47-48`). Forced against
zero in `runs/w3-force.out`. Agda rejects the equality with
`[UnequalTerms]` (`runs/w3-force.out:2`). The head constructor of the
left side is `suc` (`runs/w3-force.out:3`). **The length is not zero.**
The printed form is 1792264 bytes. It is not a closed literal. It still
contains `countFo` of `satGraphAt`, which is opaque
(`src/L/Coding/Graph.lagda.md:203-205`). I report no exact integer.

## WHAT THE HULL MUST CONTAIN

See the same heading in `lj-1.466-report.md`. Short form: `X` must
contain `fst (numeralL k)` for each `k = 0,1,...,11`. Equivalently,
`⟨ # k ∈ˢ X ⟩` by `numeralL-fst` at
`src/L/Axioms/Numerals.lagda.md:179`.

## THIS IS NOT A REFUTATION OF THE TYPE

`Vec Code (countFo LsetGraph)` is well-formed. The inhabitation fails
at a general `X` because `base` cannot see the numerals. A later brief
may restrict `X`, or it may code the numerals by `wit`. This task does
neither. The original target is not recorded as false.
