# NO-GO: `bounded-subset-internal`

The obligation `agents/tasks/LJ-1-577/Probe577.agda::bounded-subset-internal` is
NOT in the probe. This file states why, and it names the step, which is what
the brief asked for in the second case.

## THE OBLIGATION'S TYPE IS WRITTEN AND IT IS NOT INHABITED

`BoundedSubsetInternal` (`agents/tasks/LJ-1-577/Probe577.agda:260`) is
`Devlin55.BoundedSubsetAt`'s telescope with the head re-ascribed exactly as W3
measured, and with the conclusion untouched. Nothing is weakened: the
conclusion is still `⟨ x ∈ˢ Lset (fst κᴸ) ⟩`
(`agents/tasks/LJ-1-577/Probe577.agda:130`).

The module FORMS with the internal reading. W3 settled that in 3.01 seconds
(`agents/tasks/LJ-1-577/runs/w3-1.out`). So the answer is not "the type does
not exist". The answer is that ONE step of the proof cannot be taken.

## THE STEP

`β∈κ`, at `src/L/BoundedSubset.lagda.md:1594`. It is the only step of the
module that reads the cardinality hypothesis, and it reads it twice, at
`src/L/BoundedSubset.lagda.md:1597` and `:1601`, both times as `cardκ α α∈κ`.

Both spends hand it an AMBIENT injection `⟪ κ ⟫ ↪ ⟪ α ⟫`. The probe
reproduces both, as terms, at `agents/tasks/LJ-1-577/Probe577.agda:186`
(`leg-β≡κ`) and `:192` (`leg-κ∈β`).

The injection both legs refute is `β↪α`, `src/L/BoundedSubset.lagda.md:1578`.
Its two legs are the stage-cardinality lower bound at β (`:1581`) and `πX↪α`
(`:1574`), and `πX↪α` is `CSel.h ∘ IC.inv`: a code selection
(`src/L/BoundedSubset.lagda.md:1518`) after an inverse collapse (`:1517`).
The composite carries no `InjCode`.

## WHAT THE INTERNAL READING DELIVERS, AND WHAT THE STEP WANTS

At the one pair the step spends at:

- the internal reading delivers `SpendInternal κᴸ αᴸ`, the refutation of a
  CODED injection (`agents/tasks/LJ-1-577/Probe577.agda:340`);
- the step wants `Spend (fst κᴸ) α`, the refutation of an AMBIENT injection
  (`agents/tasks/LJ-1-577/Probe577.agda:336`).

The tree has one of the two directions between them and it is the wrong one.
`ambient-spend→internal-spend` (`agents/tasks/LJ-1-577/Probe577.agda:356`)
runs AMBIENT to INTERNAL through `readL` (`src/L/CantorBernstein.lagda.md:33`).
The converse is `GapAtPair` (`agents/tasks/LJ-1-577/Probe577.agda:363`) and
`gap-is-a-code` (`:368`) shows it is exactly a CODE for the one injection.

`src/` has no producer of such a code. The only two `InjCode` producers are
`src/L/Absorption.lagda.md:614` and `src/L/CodedShift.lagda.md:40`, and both
deliver the single shape `InjCode F (sucʟ γ) γ`. This is re-measured at this
task and not carried over from `[LJ-1.569]`.

## THE PRICE OF THE RESIDUE, AND WHY THIS IS A NO-GO AND NOT A GO

`internal-plus-one-code` (`agents/tasks/LJ-1-577/Probe577.agda:279`) is GREEN
and it inhabits the obligation's type from `OrdInjCoded`
(`agents/tasks/LJ-1-577/Probe577.agda:239`), the residue. That is a term with
a hypothesis to the left of the arrow that the obligation does not have, so it
is not the obligation and it is not offered as one.

The residue is not cheaper than the demand the campaign already had:

- `residue-gives-569` (`agents/tasks/LJ-1-577/Probe577.agda:309`) gives
  `[LJ-1.569]`'s `InternalToAmbient` back at every ordinal L-element, and
  `[LJ-1.569]` needed it only at the successor pair
  (`agents/tasks/LJ-1-569/Probe569.agda:187`);
- `internal-from-569` (`agents/tasks/LJ-1-577/Probe577.agda:317`) closes the
  internal statement from `InternalToAmbient` with no coding at all.

So re-ascribing the printed hypothesis does not remove the ambient demand and
does not lower it. **What it does is change the demand's KIND**, and that is
the finding this task returns: the demand stops being a statement about
cardinals and becomes a statement about ONE injection.

## WHAT WOULD REOPEN IT

A code for `β↪α`. Not a code for every ambient injection: `β↪α` is the
composite of a stage-cardinality bound and a code selection over the hull's
term algebra, and both legs are built from L-data. A construction task, and
the probe's `gap-is-a-code` states its exact interface.
