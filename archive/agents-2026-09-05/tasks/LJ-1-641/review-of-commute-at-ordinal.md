# review-of-commute-at-ordinal: the stated NO-GO

slot: `coder`. Task `[LJ-1.641]`. This file states the stop. It is the
critic's input and it does not close the task.

## THE STOP

**NO-GO on `commute-at-ordinal`. The obligation is not inhabited.** No
name `commute-at-ordinal` is declared in
`agents/tasks/LJ-1-641/Probe641.agda`. The meter agrees:
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`,
`probe_red=False` (`agents/tasks/LJ-1-641/runs/witness.out:1-2`).

**The probe is green and carries no hole** (`runs/recheck-3.out`,
`EXIT=0`, 3.76 s). It carries `--safe`. Nothing is postulated. Nothing
lands in `src/`.

## WHY, IN THREE SENTENCES

The obligation reduces, as a machine-checked term, to exactly three
gaps: `IndexInHull`, `DefFwd` and `DefBwd`
(`Probe641.agda:278`, `commute-from-gaps`). Every one of the three asks
the hull to contain a member picked out by a condition that names
`Lset` or `𝒟ₒ`, and the hull is closed under DEFINABLE witnesses only
(`src/L/Hull.lagda.md:415`, `hull-closed`). So all three need `Lset`
named in the hull's language, which is `lset-code`, step 3 of
`[LJ-1.462]`'s four; `grep -rn "lset-code" src/` returns nothing, and
`[LJ-1.474]` states in terms that it did not build it
(`agents/tasks/LJ-1-474/lj-1.474-report.md:74-75`).

## THE FINDING THAT MATTERS TO THE NEXT BRIEF

**PREMISE 4 OF THE BRIEF IS NOT SUPPORTED, AND THIS IS MEASURED.**

The brief says the hypothesis `IsOrd (HS.C.π δ)` "excludes exactly"
`[LJ-1.477]`'s obstruction, and calls that the whole reason this is a
dispatch and not a repeat.

The reduction never reads that hypothesis. `fwd-from-gaps`
(`Probe641.agda:224`) and `bwd-from-gap` (`:253`) bind `oπδ` and pass
it on unexamined. No row of either term eliminates it. The proof of
that claim is `commute-no-ord-from-gaps` (`Probe641.agda:320`): the
SAME three gaps, with the ordinality dropped from all of them, give the
MORE GENERAL commute that `[LJ-1.477]` attacked. It typechecks.

So the hypothesis buys nothing between the obligation and the three
gaps. If it excludes anything, it must do so inside `IndexInHull`,
which is the only gap whose statement it can reach.

**AND W3 SAYS THE SAME THING FROM THE OTHER SIDE.** `refl` at the join
of the two computation laws fails with `[UnequalTerms]` with BOTH
hypotheses in scope (`runs/join-refl.out:4`), the same error class
`[LJ-1.477]` measured WITHOUT them. That is not new evidence about the
ordinal. `refl` is decided by conversion, and conversion does not read
a hypothesis. **Adding a hypothesis to a type cannot change whether its
two sides are definitionally equal.**

## WHAT THIS IS NOT

This is not a refutation. I did not build a term of the negation. The
statement is very probably TRUE: the hull is a definable hull with
least witnesses (`src/L/Hull.lagda.md:403`, `leastWit`), which is what
makes it elementary, and condensation is true of an elementary hull.
The stop is that the PROOF needs step 3, and step 3 is unbuilt and
independent.

## WHAT THE TASK DELIVERED INSTEAD

`Probe641.agda`, green, with the obligation reduced to a named residue:

    Residue = IndexInHull × DefFwd × DefBwd          (:421)
    residue-suffices : Residue → Commute             (:424)

Everything around the three gaps is discharged. No fourth thing is
owed.
