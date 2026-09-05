# LJ-1.492 review of `CoverWitnessesInHull`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

The type taken from the predecessor probe that typechecked, never
from this brief. Quote, `agents/tasks/LJ-1-484/Probe484.agda:123-126`:

```agda
CoverWitnessesInHull : Type (ℓ-suc ℓ)
CoverWitnessesInHull =
  (y : S) → ⟨ y ∈ˢ M ⟩
  → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
```

The probe restates that type at
`agents/tasks/LJ-1-492/Probe492.agda:216-219`. Telescope:
`Probe492.agda:97-100`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below
`module Condense` is copied. There is no term of that type. The
witness meter reports `1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-492/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at the conversion from `ambient-level` to STAGE satisfaction
of `coverFo`. W3 is GO. `closed` is opened. The obligation term is
not written.

W3, inhabited:

```agda
coverFo : (yc : Code) → Formula Code 1
```

at `Probe492.agda:124-125`. Three forced rechecks, exit 0, caliber
`-A64m -I0 -M8g`. Median wall **2.14 s**. Median peak RSS
**472317952 bytes**. `runs/w3-{1,2,3}.out`.

`closed` is applied at this formula as `closed-at-cover`
(`Probe492.agda:191-195`), which is `closed (coverFo yc)` from
`src/L/Hull.lagda.md:120-122`. `wit` is not the covering witness.

The failing type is well-formed and unbuilt at
`Probe492.agda:216-219`. This is an obstruction of the conversion
`StageSatOfCover` (`Probe492.agda:205-209`). It is not a
refutation of `CoverWitnessesInHull`. I did not build a term of
the negation. I did not prove the type false. I did not inhabit
`cover`. I did not take `levelIn` as a hypothesis. I did not
postulate.

## WHICH ROUTE IS NEARER, AND WHAT IT LACKS

**Route by `closed` is the named route, and it is opened.** The
formula at arity one typechecks (`coverFo` at
`Probe492.agda:124-125`). `isOrdFo` at `⊨c` goes both ways
(`isOrdFo-in` at `:181-186`, `isOrdFo-out` at `:162-179`).
`ambient-level` is rebuilt (`:141-151`). An ambient covering
ordinal packs as a stage member (`pack-index` at `:157-158`).
`closed` takes that STAGE satisfaction to a hull witness
(`closed-at-cover` at `:191-195`). What it lacks:

1. `StageSatOfCover` (`Probe492.agda:205-209`): the conversion
   from `ambient-level`'s meta-level covering to
   `∥ Σ[ a ∈ ASt.SL ] ⟨ (a ∷ []) ⊨c coverFo yc ⟩ ∥₁`. Adequacy of
   `LsetGraphAt` is `Lset-defines` / `Lset-only` at
   `src/L/Hierarchy.lagda.md:646-648` and `:334-335`, at the class
   carrier `𝒮ʟ`. `⊨c` is at the stage `AbsL.𝒮M`
   (`src/L/Hull.lagda.md:153`, `:323`). The graph is an unbounded
   `∃̇` (`src/L/Coding/Sequence.lagda.md:292`). Δ₀ transfer at
   `src/L/Absoluteness.lagda.md:122-123` does not move it.

**The hull's own closure does not reach its own consumer.**
`closed` transfers STAGE satisfaction of `Formula Code 1` into the
hull. It does not transfer a meta-level covering into STAGE
satisfaction of the level graph.

## WHICH PREMISE MOVED

`[LJ-1.487]` (`agents/tasks/LJ-1-487/lj-1.487-report.md:170`) is
NO-GO at `CoverWitnessesInHull` via `wit`. The statement is not
named FALSE. This task opened `closed` and did not use `wit` as
the covering witness.

`[LJ-1.484]` (`agents/tasks/LJ-1-484/lj-1.484-report.md:114`) is
NO-GO at D-10 step 4. It built `ambient-level` at
`Probe484.agda:88-90`. This task rebuilt that term.

`[LJ-1.462]` (`agents/tasks/LJ-1-462/lj-1.462-report.md:77`) is
NO-GO at D-10 step 3 for `levelIn`. The statement is not named
FALSE. This task does not inhabit `levelIn`.

`[LJ-1.160]` (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`)
measured that the hull is not transitive. That measurement still
stands.

## WHAT I DID NOT DO

- I did not inhabit `CoverWitnessesInHull`.
- I did not inhabit `cover`.
- I did not take `levelIn` as a hypothesis.
- I did not postulate. I did not weaken `γ ∈ M`.
- I did not import a probe.
- I did not write in `src/`.
- I did not use `wit` to name a covering index.
