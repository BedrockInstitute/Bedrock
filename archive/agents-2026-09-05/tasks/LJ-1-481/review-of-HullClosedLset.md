# LJ-1.481 review of `HullClosedLset`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The predecessor type, copied from
`agents/tasks/LJ-1-462/Probe462.agda:136-138`:

```agda
HullClosedLset :
    (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩
```

The probe restates that type as `ClosedLset` at
`agents/tasks/LJ-1-481/Probe481.agda:111-113`. Telescope:
`Probe481.agda:88-98`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below
`module Condense` is copied. There is no term named
`HullClosedLset`. The witness meter reports `1 UNRESOLVED of 1`
(`agents/tasks/LJ-1-481/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at uniqueness of the witness. `Lset-only` pins the value as
`Lset` of the argument only with `IsOrd` on that argument
(`src/L/Hierarchy.lagda.md:334-335`). A hull member `y` has no
source for `IsOrd`. The brief forbids adding that hypothesis.
`wit`'s value need not be `Lset y`. I did not inhabit
`HullClosedLset`.

This is an obstruction of the `feed` then `inHull` route. It is not
a refutation of the type. I did not build a term of the negation.

W3 inhabited `pins` from `Lset-only` (`Probe481.agda:53-57`) and
`pins-at-most-one` from `pins` (`:62-70`). Three forced rechecks,
exit 0, caliber `-A64m -I0 -M8g`. Median wall **1.67 s**. Median
peak RSS **378388480 bytes**. `runs/w3-{1,2,3}.out`.

## D-10, IN ONE LINE

`Lset-only` gives uniqueness. `IsOrd` has no source at
`⟨ y ∈ˢ M ⟩`. `hull-member` at `src/L/Hull.lagda.md:337-339`
returns a `Code`. `Hull⊆L` at `:330-334` places the member in
`Lset α`. `Code` has `base` and `wit` only (`:72-74`).

## WHAT THIS IS NOT

This is not a proof that `HullClosedLset` is false. C-42 does not
fire: there is no refutation to sweep. `[LJ-1.474]`'s `lset-codes`
stands. Those codes do not pin `wit`'s value as `Lset y`.
`[LJ-1.477]`'s critic-upheld NO-GO on step 4 stands
(`agents/tasks/LJ-1-477/review-of-LJ-1-477-1.md:6`).
