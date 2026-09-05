# LJ-1.477 review of `piCommuteLset`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The predecessor type, copied from
`agents/tasks/LJ-1-462/Probe462.agda:140-142`:

```agda
πCommuteLset :
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)
```

The probe restates that type as `PiCommuteLset` at
`agents/tasks/LJ-1-477/Probe477.agda:100-102`. Telescope:
`Probe477.agda:45-57`, copied from
`src/L/BoundedSubset.lagda.md:903-916`. Nothing below
`module Condense` is copied. There is no term named
`piCommuteLset`. The witness meter reports `1 UNRESOLVED of 1`
(`agents/tasks/LJ-1-477/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at the join of the two computation laws. This is not a
refutation of the type. The two laws spend. Their right-hand sides
do not meet.

W3 spent `π-compute` at `Lset y` without unfolding the seal on `π`
(`Probe477.agda:68-69`, site `src/V/Collapse.lagda.md:58-59`).
`Lset-compute` spent at `C.π y` without unfolding the seal on `Lset`
(`Probe477.agda:81-82`, site `src/L/Constructible.lagda.md:227-228`).
The remaining type is `JoinSteps` at `Probe477.agda:90-93`:

```agda
JoinSteps =
  (y : S) → C.step (Lset y) (λ z _ → C.π z)
          ≡ LsetStep (C.π y) (λ β _ → Lset β)
```

A `refl` inhabitant of that type failed with `[UnequalTerms]`
(`runs/join-refl.out:2`, `:30-31`). The inhabitant was then
removed. The green file keeps the type and does not keep the
`refl`.

I did not add an absoluteness hypothesis. I did not take
`HullClosedLset` as a module hypothesis. I did not build a term of
the negation.

## D-10, IN ONE LINE

`step` at `Lset y` builds a `sett` of `π`-images of hull-filtered
members (`src/V/Collapse.lagda.md:47-48`). `LsetStep` at `C.π y`
builds a `⋃` of `𝒟ₒ` of `Lset` at members of `C.π y`
(`src/L/Constructible.lagda.md:215-216`). The collapse's `step`
does not send the members of `Lset y` to the members of
`Lset (C.π y)` by those two laws alone.

## WHAT THIS IS NOT

This is not a proof that `piCommuteLset` is false. C-42 does not
fire: there is no refutation to sweep. `[LJ-1.160]` already measured
that Devlin's chain does not commute the collapse with the stage
operation (`agents/tasks/LJ-1-160/lj-1.160-report.md:261`). This
task measured that the two computation laws at this site do not
join.
