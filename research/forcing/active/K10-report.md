# K10 partial checkpoint: preservation interface obstruction

Historical report for the immutable `k10-partial-2026-09-13` checkpoint.
The current local-condition repair and its verification scope are recorded
in `REPAIR-report.md`; the old missing-supplier inventory below is historical.

Status: **K10 is not complete.** The completed modules below do not constitute
the final Cohen non-CH theorem. No production Agda module has been changed.

## Closed results

- `K10/CardinalContradiction.agda`: a structure-polymorphic internal cardinal
  contradiction using the existing injectability version of CH. Its inputs
  explicitly include an omega witness, its powerset, its successor cardinal,
  a larger cardinal and the internal injection into the powerset. It proves
  `noCH`, actual `¬CHsent` satisfaction and `noGCHω`. It does not supply its
  cardinal-preservation inputs.
- `K10/NegatedSentences.agda`: agreement and satisfaction for the negation of
  the existing shared `GCHωsent`. This is the omega instance, not a newly
  established full global GCH sentence.
- `K10/CheckedOmega.agda`: the actual K9/K5 extension interprets `check(w)` as
  omega when the ground interprets `w` as omega and the filter is positive.
  Inductiveness and successor transfer use actual bounded-formula transfer;
  leastness uses inherited external membership accessibility and the proved
  ground omega-predecessor theorem. No checked-omega premise is added.
- `K10/BooleanPairs.agda` and `K10/BooleanGraph.agda`: actual translated pair
  and graph names, name validity, entry/support specifications, top weights,
  atomic membership values and indexed functional/injective equality laws.
  Distinctness consumes K9's actual Boolean top-valued distinctness. These
  are atomic structural results, not the Boolean value of `IsInjectionφ`
  and not Boolean non-CH. They have no supplied generic filter.
- `K10/PreservationBoundary.agda`: a conditional formal obstruction to the
  unrestricted possible-value antichain schema. If possible values at one
  coordinate exhaust an uncountable ground set, that schema and CCC imply
  a contradiction. It does not construct a complete concrete countermodel
  or a full-possible-values witness for the actual Cohen evaluator.
- `K10/Smoke.agda`: aggregate import of these partial results only.

## Why the planned K7 assembly stops

The source types, not the explanatory comments, expose the issue:

1. `K7/PossibleValues.agda:174-175` defines `valueFo f` as existence of a
   Kuratowski pair belonging to `f`. Its exact semantic reading is at
   lines 238-241. There is no assertion that `f` is a function.
2. `valuesOf-spec`, at lines 455-460, collects values forced by **any**
   condition. It has no common base condition and no function premise.
3. `K7/NoCollapse.agda:483-487` requires `ValueAntichain` for every name `f`
   and coordinate. CCC would therefore make the possible values of every
   relation countable. A constant-input relation with all elements of an
   uncountable target as outputs shows why this cannot be the intended
   function-preservation interface.

The theorem consuming that schema can typecheck because the schema is a
premise. Typechecking does not make it an available supplier. The inherited
tree has no inhabitants of `FamilySet`, `ValueAntichain`, `InverseSpread`,
or `ProvedRangeHolds`; their occurrences are declarations and consumers.
K8 supplies Cohen CCC, not these missing preservation obligations.

Merely adding "the extension regards f as a function" does not repair the
global possible-value set. Generic truth gives a condition in the generic
filter forcing functionality, not functionality below every condition.
The general repair must thread a base condition through possible values,
restrict witnesses to refinements of that condition, and carry the forced
functionality premise through the antichain, covering and preservation
consumers. A top-forced-function interface is a separately restricted option.

This is a prerequisite interface repair, not a final contradiction lemma.
The existing K7 snapshot has deliberately not been altered or re-labelled
as a completed actual cardinal-preservation theorem.

## Remaining acceptance work

- Correct and fill the K7 preservation interface, including its ground
  cardinal bounds, and prove/check the ground-injection transfer.
- Instantiate preservation and omega-one identification at the actual K9
  extension, then apply the closed cardinal-contradiction kernel.
- Complete the Boolean formula-level graph injection, checked-cardinal
  preservation and non-CH top-value proof. Generic truth cannot supply
  a Boolean top-value conclusion by reversal.
- Finish the requested public theorem/correspondence and shared GCH scope.
- Production integration remains separate from these isolated probes.

The inherited K3 `Families`, `Accessibility`, and `MemberImage` assumptions
remain explicit. Ordinary Foundation is not external accessibility, and
these realization capabilities have not been specialized to L here. No
CH, GCH, continuum arithmetic, host choice or generic-existence assumption
is introduced to close the missing K10 conclusions.

## Verification

The coordinator ran the serial gate on 2026-09-13: all seven modules,
including `K10/Smoke.agda`, exited 0. No Agda error or open meta remains
in these files. The stop is an interface obstruction, not a compiler error
in the delivered partial proofs.

Run `sh verify-k10-partial.sh` with Agda 2.8.0 and cubical 0.9. It uses
`GHCRTS='-A64m -I0 -M8g'`, counts active compiler processes before each file,
and retains per-module exit codes in `K10/logs`. Passing it certifies only
these partial modules. It is explicitly not the K10 acceptance gate.

All 211 inherited `.agda` files were compared byte-for-byte with the K9
checkpoint and remain unchanged. The source baseline is
`/Users/alsg/Agentic/bedrock-proofs-archive/k9-complete-2026-09-13`.
