# review-of-bridge-without-B5: NO-GO

## HEAD
head_slot: coder
task: LJ-1.550
obligation: agents/tasks/LJ-1-550/Probe550.agda::bridge-without-B5
verdict: NO-GO

**THE OBLIGATION IS NOT DELIVERED AND IT IS NOT DEFERRED. IT IS REFUSED ON
MEASUREMENT.** `scripts/pod/witness.py` reports
`missing exit=42 agents/tasks/LJ-1-550/Probe550.agda::bridge-without-B5`,
1 UNRESOLVED of 1, `probe_red=False`
(`agents/tasks/LJ-1-550/runs/witness-1.out`). The probe is green
(`agents/tasks/LJ-1-550/runs/final-2.out`, exit 0). Nothing is postulated and
there is no hole.

## THE ONE SENTENCE

**The bridge cannot be inhabited from the nine other inputs, because its
ANTECEDENT asks for an ambient cardinality fact at δ that the nine do not give,
and `site-forced` proves that no other choice of the antecedent's κ avoids
it.**

## THE BRIEF'S PREMISE IS RIGHT AND ITS CONCLUSION DOES NOT FOLLOW

**RIGHT:** `GCHStatement` names no ambient type (`src/L/GCH.lagda.md:59-70`),
and the chapter says so at `src/L/GCH.lagda.md:57`. The target crosses no
ambient boundary.

**DOES NOT FOLLOW:** the bridge is
`BoundedSubsetTheorem → GCHStatement zf`
(`agents/tasks/LJ-1-523/Probe523.agda:174-175`). Its ANTECEDENT is ambient. The
third slot of `Devlin55.BoundedSubsetAt` is `cardκ : IsCardinal κ`
(`src/L/BoundedSubset.lagda.md:1386`), and `IsCardinal` refutes an AMBIENT
injection (`src/L/BoundedSubset.lagda.md:1046-1047`). An inhabitant of the
bridge must apply the antecedent, so it must fill that slot.

## THE THREE FACTS THAT SETTLE IT, EACH A GREEN TERM

1. **`UseSite.member-in-stage`** (`agents/tasks/LJ-1-550/Probe550.agda:257-284`).
   The antecedent applied at the only assignment that serves the statement.
   Its type names THREE things the nine cannot fill: `IsCardinal (fst δ)`,
   `SqLaw (fst κ)` and `CoHyps`.
2. **`site-forced`** (`agents/tasks/LJ-1-550/Probe550.agda:385-389`), on
   `ambient→internal` (`:375-377`). Any ambient cardinal μ above κ is an
   L-cardinal by readback (`src/L/CantorBernstein.lagda.md:33-38`), so
   `SuccCardL`'s leastness clause (`src/L/GCH.lagda.md:51-53`) gives δ ≤ μ.
   Landing the conclusion inside `Lset (fst δ)` needs μ ≤ δ. **So μ ≡ δ and the
   ambient hypothesis cannot be moved off the successor.**
3. **`b5-from-cardδ`** (`agents/tasks/LJ-1-550/Probe550.agda:394-396`) with the
   negative run (`agents/tasks/LJ-1-550/runs/neg-1.out`, exit 42,
   `[UnequalTerms]`). **B5 is weaker than the slot.** The slot is a Π over every
   member of δ; B5 gives one member. So B5 would not have closed the bridge even
   if it were paid.

## WHAT THE MATHEMATICIAN NEEDS FROM THIS

**THE BILL IS SIXTEEN ROWS, NOT TEN.** `bridge-with-residues`
(`agents/tasks/LJ-1-550/Probe550.agda:335-363`) is the whole implication, green,
from the seven inputs the brief names plus six residues. Three of the six are in
no predecessor table: `StageIsL` (`:317-318`), `InclusionCoded` (`:324-326`) and
`InjLTrans` (`:332-333`). Two more, B11 and B12, were placed OFF the bill by
`agents/tasks/LJ-1-523/lj-1.523-report.md:239-242`, and that placement is wrong:
a Π argument of the antecedent is owed by the inhabitant, not received by it.

**TWO ROUTES, NEITHER PRICED HERE.** Route A restates
`src/L/BoundedSubset.lagda.md:1386` with `CardSpentAt κ α` in place of
`IsCardinal κ`, which `[LJ-1.523]`'s own measurement of `:1597` and `:1601`
licenses; then B5 fills the slot exactly and R1 leaves. Route B is the brief's
own reading: the bridge is the wrong bridge, and the statement should be
approached without `Devlin55.BoundedSubsetAt`.

The full evidence is `agents/tasks/LJ-1-550/lj-1.550-report.md`.
