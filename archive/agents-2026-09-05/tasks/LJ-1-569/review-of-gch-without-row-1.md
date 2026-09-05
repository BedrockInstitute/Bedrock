# review-of-gch-without-row-1: NO-GO

## HEAD
head_slot: coder
task: LJ-1.569
obligation: agents/tasks/LJ-1-569/Probe569.agda::gch-without-row-1
verdict: NO-GO

**THE OBLIGATION IS NOT DELIVERED AND IT IS NOT DEFERRED. IT IS REFUSED ON
MEASUREMENT.** `scripts/pod/witness.py` reports
`missing exit=42 agents/tasks/LJ-1-569/Probe569.agda::gch-without-row-1`,
`1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-569/runs/witness-1.out:1-2`). The probe is green
(`agents/tasks/LJ-1-569/runs/final-5.out`, `EXIT=0`, 3.23 s). Nothing is
postulated, nothing lands in `src/`, and there is no hole.

## THE ONE SENTENCE

**`gch-from-five` consumes row 1 at exactly one place, and what that place
demands is an AMBIENT cardinality fact at δ that the other four rows do not
give and that `src/` has no producer for; the demand survives every weakening
of the slot, because what the slot SPENDS is ambient too.**

## THE BRIEF'S TWO PREMISES ARE RIGHT AND ITS CONCLUSION DOES NOT FOLLOW

**RIGHT, ONE.** `GCHStatement` names no ambient type
(`src/L/GCH.lagda.md:59-69`) and the chapter says so at
`src/L/GCH.lagda.md:57-58`. The target crosses no ambient boundary.

**RIGHT, TWO.** `[LJ-1.558]` did drop the ambient fact one level up
(`agents/tasks/LJ-1-558/Probe558.agda:118-128`), and `[LJ-1.564]` paying
`PowerIntoSucc` did expose it again as row 1
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`).

**DOES NOT FOLLOW.** `[LJ-1.558]`'s move was to take the hard leg
`InjL (𝒫 κ) δ` WHOLE, as a hypothesis (`Probe558.agda:93-96`). It did not
re-route around the ambient fact; it stopped short of the step that spends it.
`[LJ-1.564]` then built that step out of `Devlin55.BoundedSubsetAt`, whose
third telescope slot is `cardκ : IsCardinal κ`
(`src/L/BoundedSubset.lagda.md:1386`), and `IsCardinal` refutes an AMBIENT
injection (`src/L/BoundedSubset.lagda.md:1046-1047`). **An inhabitant of that
step must fill that slot.** AGENTS.md:45 is the governing clause: a measured
cure does not transfer by analogy, and this task re-measured it at its own
site.

## THE FOUR FACTS THAT SETTLE IT

1. **W3, AND THE ELABORATOR SPEAKS.** Three slices, all RED by design.
   `runs/W3.agda.txt:48-55` binds row 1 and drops it from the argument list;
   `runs/W3b.agda.txt:49-60` drops it at the spend site;
   `runs/W3c.agda.txt:58` fills the slot with a term of a known wrong type,
   and `runs/w3-3.out:10-11` prints what the slot demands:

       when checking that the expression r3 has type
       L.BoundedSubset.IsCardinal lem (fst δ)

   **ROW 1 IS CONSUMED. The answer is not bookkeeping.**

2. **ONE USE SITE, AND IT IS `Probe564.agda:360`.**
   `landing-at` (`agents/tasks/LJ-1-569/Probe569.agda:95-108`) is that step
   with the whole bill paid except row 1: rows 2 and 3 are to the left of the
   arrow that asks for `IsCardinal (fst δ)`, and nothing else is.
   `row-1-is-the-only-gap` (`:113-119`) carries it to `GCHStatement` with the
   other four rows passed to `[LJ-1.564]` verbatim and in order.

3. **WEAKENING THE SLOT DOES NOT REMOVE THE AMBIENT DEMAND, AND THIS IS NEW.**
   `[LJ-1.550]`'s review named a Route A: restate
   `src/L/BoundedSubset.lagda.md:1386` with the spent form in place of
   `IsCardinal κ`, "then B5 fills the slot exactly and R1 leaves"
   (`agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:66-69`).
   `row-1-spend-is-B5` (`Probe569.agda:145-146`) is `refl`: the spent form IS
   `[LJ-1.523]`'s B5. **And B5's own type names `⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫`**
   (`Probe569.agda:141-142`). So Route A trades an ambient Π for an ambient
   instance. **It weakens the demand. It does not remove it, and it does not
   deliver this brief's obligation.**

4. **THE DIRECTION IS THE CONVERSE OF READBACK, AND `src/` HAS NO PRODUCER.**
   The consuming step holds `IsCardinalL δ` from `SuccCardL`'s second conjunct
   (`src/L/GCH.lagda.md:49`) and wants `IsCardinal (fst δ)`. Readback runs
   the other way: `ambient→internal` (`Probe569.agda:169-171`) is green on
   `readL` (`src/L/CantorBernstein.lagda.md:33-38`). The converse is stated
   TYPE ONLY as `InternalToAmbient` (`Probe569.agda:175-176`), it is neither
   proved nor refuted here, and it would need a code for an arbitrary ambient
   injection. **The only `InjCode` producers in `src/` are
   `src/L/Absorption.lagda.md:614` and `src/L/CodedShift.lagda.md:40`, and both
   deliver the single shape `InjCode F (sucʟ γ) γ`.**

## WHAT THE OWNER MUST HEAR

The brief states it: **a NO-GO says `L ⊨ GCH` as routed here needs δ to be a
real cardinal.** It does. `row-1-from-the-converse` (`Probe569.agda:187-188`)
names the demand as one principle: **an L-cardinal is a cardinal.** That is a
statement about the ambient V and not about L, and the route asks for it at
every successor pair the trophy quantifies over.

**THE SOURCE IS THE PORT AND IT IS NAMED.** `Devlin55.BoundedSubsetAt` is
Devlin II 5.5, and 5.5 opens `Assume V = L`
(`dev/literature/devlin-II5.md:147`). Under that assumption "κ is a cardinal"
is ambient and internal at once, so the printed hypothesis does not choose.
**Bedrock does not assume V = L.** The port kept the ambient reading, and row 1
is the residue of an assumption the trophy does not make.

## THE ONE THING THIS TASK DID NOT TRY, AND WHY

**Moving the site.** `[LJ-1.550]`'s `site-forced`
(`agents/tasks/LJ-1-550/Probe550.agda:385-389`) already proves that no other
ambient cardinal μ above κ serves: leastness gives δ ⊆ μ, the conclusion needs
μ ⊆ δ, so μ ≡ δ. `[LJ-1.94]` supplied `cardκ` at ITS site from the ambient
Hartogs cardinal (`archive/dev/LJ-dispatch-index.md:170`), and that route is
closed here for exactly the reason `site-forced` gives: `SuccCardL` fixes δ and
Hartogs does not produce it.

The full evidence is `agents/tasks/LJ-1-569/lj-1.569-report.md`.
