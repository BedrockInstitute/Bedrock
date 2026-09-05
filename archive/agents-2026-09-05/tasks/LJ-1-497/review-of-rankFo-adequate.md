# NO-GO: `rankFo-adequate` is FALSE

## HEAD
task: LJ-1.497
head_slot: coder
obligation: agents/tasks/LJ-1-497/Probe497.agda::rankFo-adequate
verdict: NO-GO
kind: refuted

## THE STATEMENT

The brief asks for one term:

    rankFo-adequate :
        (Q a z : S)
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → (the reading that z is the pair of a member of `a` and its `swo-rank`)

**The telescope as written cannot be STATED**, because `swo-rank` needs an
`SWO` and the only delivered route to one at `a` is `OrdSWO.w (fst a) oa`
(`agents/tasks/LJ-1-490/Probe490.agda:212`), which needs `oa : IsOrd (fst a)`.
I stated it with `oa`, the predecessor's own delivered hypothesis, as
`RankFoAdequate` (`agents/tasks/LJ-1-497/Probe497.agda:275-280`).

## THE VERDICT

**With that one repair, the statement is FALSE, and the refutation
typechecks:**

    no-adequacy :
        (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
      → RankFoAdequate → Empty.⊥

`agents/tasks/LJ-1-497/Probe497.agda:435-451`. Exit 0 on the whole file,
caliber `-A64m -I0 -M8g`, one Agda process, interface deleted before each of
four rechecks (`agents/tasks/LJ-1-497/runs/full-1.out` to `full-4.out`).

Its only hypothesis is that some ordinal of `L` has a member.

## THE SLOT THAT DIVERGES

**The third existential of `rankFo`, the `r` slot**
(`agents/tasks/LJ-1-497/Probe497.agda:258`). It is read as the second
component of the coded pair by `prAtL (s3 zero) (suc zero) zero`
(`:259`) and pinned by `supAt zero (suc zero)` (`:263`). **It is the same
slot `range-clause` reads** (`agents/tasks/LJ-1-490/Probe490.agda:280`).

- **The formula pins that slot EMPTY at a `Q`-minimal member.** `extAt` is a
  biconditional (`src/L/Coding/Model.lagda.md:662-664`), so `supAt f r` fixes
  `r` to the union of the successors of `f`'s values, and a `Q`-minimal `m`
  gives a pair-free `f`. Term: `Fml.sup-no-member`
  (`agents/tasks/LJ-1-497/Probe497.agda:329-334`) with `Fml.fn-no-pairs`
  (`:299-312`).
- **`swo-rank` puts `∅` INSIDE that slot at EVERY member.** Term:
  `rank-at-has-∅` (`agents/tasks/LJ-1-497/Probe497.agda:213-216`).

The two cannot agree. Term: `divergence`
(`agents/tasks/LJ-1-497/Probe497.agda:351-362`), which holds for ANY `Q`.

## WHAT IS AT FAULT, AND WHAT IS NOT

**`[LJ-1.475]`'s formula is NOT at fault and is NOT retired by this.** It
computes the standard rank, which is `∅` at a minimal member.

**`swo-rank` is at fault.** `boundingOrd` is taken over the WHOLE carrier
(`agents/tasks/LJ-1-490/Probe490.agda:145`) and every non-predecessor is
padded with `∅` (`:134-135`), so `sucV ∅ = {∅}` enters the union at every
point. `swo-rank` therefore never takes the value `∅`, and no rank function
has that property.

**The padding is a universe artefact, not a mathematical choice.** Indexing
`boundingOrd` over the predecessors instead does not typecheck:
`Type (ℓ-suc ℓ) != Type ℓ` (`agents/tasks/LJ-1-497/runs/cure-level.out`,
exit 42), because `boundingOrd` wants a small index
(`src/L/Ordinal.lagda.md:154`) and `OrdSWO`'s order is `_∈ᵗ_`-valued
(`agents/tasks/LJ-1-490/Probe490.agda:167`).

## THE ONE THING I DID NOT CLOSE

`no-adequacy` realizes the `Q`-minimal hypothesis with `Q := ∅`. The
`Q`-independent form needs a minimal member of `a` under an arbitrary `Q`,
which needs `Q` read as a well-order, which is precisely the reading the
formula does not perform. That reading is the second missing hypothesis, and
it is named in the report.

## WHAT I DID NOT DO

I did not postulate. I did not weaken the rank to a bound. I did not add a
hypothesis to close a conjunct beyond `oa`, which is the predecessor's. I did
not claim `InjCode`, a limit, or `Residue`. I did not attempt `range-clause`.
I did not build the cure. Nothing landed in `src/`. Nothing was committed and
nothing was pushed.

The full measurement is `agents/tasks/LJ-1-497/lj-1.497-report.md`.
