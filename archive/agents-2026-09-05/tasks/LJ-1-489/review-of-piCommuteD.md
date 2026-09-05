# LJ-1.489 review of `piCommuteD`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The type the brief named, restated at
`agents/tasks/LJ-1-489/Probe489.agda:139-141`:

```agda
PiCommuteD :
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)
```

Telescope: `Probe489.agda:53-64`, copied from
`src/L/BoundedSubset.lagda.md:903-916`. Nothing below
`module Condense` is copied. There is no term named
`piCommuteD`. The witness meter reports `1 UNRESOLVED of 1`
(`agents/tasks/LJ-1-489/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at D-10 and at the join of `π-compute` with sealed `𝒟ₒ`.
The two sides cannot agree without elementarity. This is not a
refutation of the type. I did not build a term of the negation.
The obligation term `piCommuteD` is not written.

W3 spent `π-compute` at `𝒟ₒ y` without unfolding the seal on `π`
(`Probe489.agda:81-82`, site `src/V/Collapse.lagda.md:58-59`).
The easier inclusion `OneWay` is stated at `Probe489.agda:88-90`
and is unbuilt. A `subst` along `left-compute` that claimed
membership in `𝒟ₒ (C.π y)` failed with `[UnequalTerms]`
(`runs/one-way-subst.out:2` and `:11-13`). The inhabitant was
then removed. The green file keeps the type and does not keep
the `subst`.

The remaining constructor gap is `JoinAtD` at
`Probe489.agda:119-121`. The remaining elementarity gap is
`FormulaTransport` at `Probe489.agda:128-134`. Both unbuilt.

I did not add an elementarity hypothesis. I did not take
`HullClosedLset` or `CoverWitnessesInHull` as a module
hypothesis. I did not open either seal.

## D-10, IN ONE LINE

`step` at `𝒟ₒ y` builds a `sett` of `π`-images of hull-filtered
members (`src/V/Collapse.lagda.md:47-48`). `𝒟ₒ` at `C.π y` is
every definable subset of `C.π y`
(`src/L/Constructible.lagda.md:211-213` and `:301-308`). A
defining formula over `y` becomes a defining formula over
`C.π y` only if satisfaction transfers along `π`. That is
elementarity, not a computation. The hull is not transitive
(`agents/tasks/LJ-1-160/lj-1.160-report.md:249`).

## WHAT THIS IS NOT

This is not a proof that `piCommuteD` is false. C-42 does not
fire: there is no refutation to sweep. `[LJ-1.160]` already
measured that Devlin's chain does not commute the collapse with
the stage operation (`agents/tasks/LJ-1-160/lj-1.160-report.md:261`).
This task measured that the same obstruction sits one layer
down, at `𝒟ₒ`, and that the cheaper inclusion does not close
by the exported computation law.
