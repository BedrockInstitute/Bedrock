# K7 local-condition repair and K10 prerequisites

Historical repair report. The subsequent continuation in this checkpoint is
documented in `PROGRESS-report.md`; the original repair archive is unchanged.

The erroneous unrestricted preservation interface has been repaired.
**This is not completion of K10 or of an ordinary-ZFC Cohen preservation instance.**
The K9 and earlier K10 archives are unchanged; this is a new mutable proof
checkpoint based on `k10-partial-2026-09-13`.

## Interface repair

`K7/PossibleValues.agda` now constructs `valuesOf sep p f ξ` by ground
Separation using a fixed formula. Its specification is exactly

```
a ∈ valuesOf sep p f ξ
  iff a ∈ κ and there exists r with r ≤ p and r forces valueFo f (check ξ, check a).
```

The refinement constraint is present in the defining formula, not just in
a subsequent lemma. The coded order is represented by a two-variable ground
formula and its reading theorem. `ValuesAtNames` constructs this formula
from the actual coded order. No arbitrary-host-predicate Separation is used.

`K7/NoCollapse.agda` threads the same `p` through the possible-value family,
its antichain/countability bound and the covering proof. `ValueAntichain`
and `ValueMaximalAntichain` require `p` to force the actual
`CardinalBridge.IsFunctionφ` at `f`. To cover values true in the extension,
the proof obtains a truth witness `q ∈ G`, refines `p` and `q` inside `G`,
and uses forcing monotonicity. `no-functional-spread` obtains the initial
`p ∈ G` from the actual function formula, its semantic bridge and truth.

`InverseSpread` now demands an actual surjection, not a relation that merely
covers the target. `PreserveAtTracks` applies the repaired producers and
consumers with the same coded order and fixes their carrier to the condition
carrier. Its previous independent `c` parameter is removed.

The old schema remains only as `RejectedValueAntichain` in the explicitly
historical obstruction module `K10/PreservationBoundary.agda`. It is not a
supplier to the repaired preservation theorem.

## Additional closed proofs

| Module | Result and exact scope |
| --- | --- |
| `K7/ValueAntichains.agda` | Actual ground `ChoiceSet` selects a graph through a definable relation. Separation constructs its range, and the relation's determinacy/incompatibility laws prove that range is an antichain receiving an internal injection from the value set. Forcing-specific relation laws remain to be supplied. |
| `K7/ValueFamilies.agda` | The inherited `MemberImage` capability constructs the family and an inverse-relation table. Actual ground `ChoiceSet` selects a graph giving an internal injection of the family into its index set. |
| `K7/InverseSurjection.agda` | An internal injection `A → B` and an element `u ∈ A` produce an internal surjection `B → A`. The graph is built by actual Collection/Separation, with inverse values on `f[A]` and default `u` outside. No identification of structure equality with host paths is required. |
| `K7/CountableCover.agda` | Proves the exact covering obstruction for a ground cardinal whose every smaller ordinal injects into omega. It counts the entire union of the family, so family members need not be subsets of the target. This supplies the omega-one range from its existing countable-members hypothesis, not the omega-two range. |
| `K10/CheckedInjection.agda` | The actual K9/K5 positive copy preserves internal injectability. It proves transfer of the real graph predicates and does not incorrectly classify `IsInjectionφ` as bounded. |

`PreserveAtTracks.WithImages.family-set`,
`WithInverse.inverse-spread` and
`AtCountableBound.countable-cover` instantiate three repaired obligations
using these proofs. These are actual typed applications, not fresh
assumptions with the desired conclusions. `K10/RepairSmoke.agda` imports
the repaired chain and new prerequisites.

The family construction explicitly retains the inherited `MemberImage`
realization capability for host maps over represented sets. This is not a
derivation of that capability from ordinary first-order Collection. The
inverse-surjection construction, in contrast, works with structure equality
and the ordinary profile, so it applies to extension names.

## Regression checks

`outside-local-values` in `PreserveAtTracks` proves that no value can enter
the local set when all refinements of its base condition exclude it.
`countable-at-forced-function` explicitly checks the new function premise.

`Controls/Negative/MissingFunction.agda` is an intentionally failing fixture:
it removes that premise from the real countability consumer. Agda rejects
the application with `S !=< fst (forces p ...IsFunctionφ (f ∷ []))` while
checking `PB.countable-from-ccc₂`. This file is not a completed proof and
is excluded from the positive-module gate.

Run `sh verify-local-repair.sh`. It checks every positive module in K7,
K8, K9 and K10 serially, then requires the negative control to fail with
the expected error. Every compiler invocation uses
`GHCRTS='-A64m -I0 -M8g'`; the script checks process slots before starting.
Individual logs are retained in `repair-logs/`.

Final regression on 2026-09-13: `sh verify-local-repair.sh` exited 0.
All 111 positive K7–K10 modules exited 0; the missing-function control
was rejected with the expected exit 42 and the expected function-type error.

Against the immutable K10 partial checkpoint, 213 existing Agda modules
are byte-for-byte unchanged. Four existing K7 modules change, and the
historical boundary module changes only its label/comment for the rejected
schema. There are six new positive modules and one negative fixture.
No production source, existing landmark, commit or push is part of this work.

## Remaining K10 work

1. Instantiate the definable local deciding relation and prove its
   determinacy/incompatibility from actual forcing semantics, then apply
   `ValueAntichains` to fill the remaining antichain supplier.
2. Prove the necessary ground omega-two covering bound. The countable-member
   theorem above must not be applied to omega-two or replaced by an assumed
   cardinal-arithmetic conclusion.
3. Assemble the actual preservation/identification instances and feed the
   existing K9 internal injection and K10 cardinal contradiction.
4. Finish the Boolean formula-level graph injection, checked-cardinal
   interpretation/preservation and non-CH top-value theorem, and the public
   correspondence/shared-GCH endpoints. Atomic graph laws and truth in a
   supplied generic extension do not prove these top values.

K6 semantic/definability capabilities and the K3 realization assumptions
remain explicit where their actual instances have not been filled. There
is no new CH/GCH, continuum-arithmetic, host-choice, generic-existence or
truth-to-top reflection assumption.
