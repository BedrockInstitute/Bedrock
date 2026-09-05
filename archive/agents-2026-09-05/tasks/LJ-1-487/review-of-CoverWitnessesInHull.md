# LJ-1.487 review of `CoverWitnessesInHull`: the stated NO-GO

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
`agents/tasks/LJ-1-487/Probe487.agda:163-166`. Telescope:
`Probe487.agda:61-64`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Nothing below
`module Condense` is copied. There is no term of that type. The
witness meter reports `1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-487/runs/witness.out:1-2`).

## THE VERDICT

NO-GO at the covering index in `M`. W3 is GO. The covering formula
packages and feeds to `wit`. The obligation term is not written.

W3, inhabited:

```agda
ord-by-wit : ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ) ∥₁
```

at `Probe487.agda:122-128`. `wit` at `isOrdFo`, not at a numeral
formula. Three forced rechecks, exit 0, caliber `-A64m -I0 -M8g`.
Median wall **2.49 s**. Median peak RSS **477478912 bytes**.
`runs/w3-{1,2,3}.out`.

The failing type is well-formed and unbuilt at
`Probe487.agda:163-166`. This is an obstruction of two routes. It
is not a refutation of `CoverWitnessesInHull`. I did not build a
term of the negation. I did not prove the type false. I did not
inhabit `cover`. I did not take `levelIn` as a hypothesis.

## WHICH ROUTE IS NEARER, AND WHAT IT LACKS

**Route 1, by `wit`, is nearer.** W3 shows `wit` can name an
ordinal at a formula (`Probe487.agda:122`). The covering formula
at the class carrier typechecks (`coverIndex` at
`Probe487.agda:139-143`). Packaging typechecks (`packagedCover`
at `:145-146`). `feed-cover` typechecks (`:153-154`). What it
lacks:

1. Sat of `packagedCover` at the hull's `_⊨₀_`. Adequacy of
   `LsetGraphAt` is `Lset-only` / `Lset-defines` at
   `src/L/Hierarchy.lagda.md:334-335` and `:646-648`, at the
   class carrier `𝒮ʟ`. The hull's search is at the stage
   `AbsL.𝒮M` (`src/L/Hull.lagda.md:153`, `:323`). Those
   semantics do not meet.
2. A filled `Vec Code (countFo coverIndex)`. `[LJ-1.474]` filled
   that Vec for `LsetGraph`
   (`agents/tasks/LJ-1-474/lj-1.474-report.md:70`). C-42 forbids
   the transfer to `coverIndex`. This probe does not import that
   probe.

**Route 2, by elementarity, is farther.** Devlin transfers
"∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" by Σ₁-elementarity
(`dev/literature/devlin-II5.md:107-108`). The tree has the TYPE
`AtM.Elementary` at `src/L/Hull.lagda.md:174-176` and the
inhabitant `HullElemDown.WithCode.elem` at
`src/L/BoundedSubset.lagda.md:759-760`, under a canonical-code
hypothesis. The consumer at a concrete `X` inhabits it at
`:1543-1545`. The generic `HullStage` telescope does not.
`Elementary` is at `Formula SM`. `coverIndex` is `Formula CS.S 2`.
The tree does not have `M ≺_{Σ₁} L_lam` at the language of the
level formula, at this telescope.

## WHICH PREMISE MOVED

`[LJ-1.484]` (`agents/tasks/LJ-1-484/lj-1.484-report.md:114`) is
NO-GO at D-10 step 4. The statement `cover` is not named FALSE.
This task inhabits step 4 of that decomposition, not `cover`.

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
