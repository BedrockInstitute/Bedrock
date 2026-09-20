# K10 continuation: checked prerequisites and generic assembly

This checkpoint advances K10 but does not complete its general Cohen theorem.
It extends the immutable `k7-local-repair-2026-09-13` checkpoint without
changing any inherited Agda proof or the intentional negative fixture.

## New proofs

- `K7/FunctionalValues.agda` proves that the positive Kuratowski-pair
  predicate used by possible values implies the biconditional pair predicate
  used by `CardinalBridge.isFunction`. The converse uses Pairing. It proves
  value uniqueness and the actual surjection-to-value implication.
- `K7/FunctionalValuesAtNames.agda` checks the exact equality with
  `PossibleValues.Names.valueFo` by reflexivity and exports the actual
  `PreserveAtTracks.Probe.onto` supplier. Its forced consequence theorem is
  deliberately restricted to a condition in the supplied generic filter.
- `K7/ForcingReflection.agda` uses K5's actual sealed forcing relation and
  impossibility of forcing bottom. `K10/CheckedForcing.agda` supplies its
  reflection input from actual K9 translated checks. Every Cohen condition
  forcing equality of two translated checks therefore implies ground equality.
- `K7/UncountableCover.agda` proves the union and covering arguments for a
  larger bound. Its general-structure version explicitly requires a square
  injection, rather than pretending to prove cardinal multiplication.
- `K7/ConstructibleCover.agda` discharges that square premise at the actual
  structure `𝒮ʟ`, by applying the existing `square-law-L`. It converts the
  real `InjL` graph to `CardinalBridge.injectable` through a definable
  relation and ordinary Choice, and proves inclusion of the ordinary product
  in `prodL`. Its covering theorem retains explicit Foundation/Choice,
  cardinal/ordinal data and the bound on smaller ordinals. It has no
  `MemberImage` or assumed square injection. This is an L-specific supplier,
  not an arbitrary-ground omega-two preservation theorem.
- `K10/BooleanPairFormula.agda` proves top values for the exact abstracted
  `CardinalBridge.IsSingletonφ` and `IsPairφ` at the constructed translated
  names. It takes the K4 evaluator's atomic, finite-connective and bounded
  universal laws, not either desired top value. A concrete compiler instance
  still needs the atomic-graph and quantifier supplies; this module does not
  claim an ordered-pair formula or full graph-injection theorem.
- `K10/GenericContradiction.agda` assembles the actual K9 internal injection,
  `CheckedOmega` and `CheckedInjection`. From two explicitly preserved
  cardinals and the ground countability of ordinals below the first, it proves
  the first remains the successor of checked omega, then proves shared
  non-CH and negated GCH omega-instance satisfaction in the actual K9
  extension. Extension Separation, Collection, Pairing, PowerSet and
  Foundation remain explicit. The two cardinal-preservation conclusions are
  boundary parameters here, not claimed as proved suppliers.

`K10/ProgressSmoke.agda` imports the new chain and the prior repair aggregate.

## What remains

1. Prove the all-condition forcing consequence from forced functionality
   and two forced values to forced checked equality. The new hProp semantic
   consequence and checked-equality reflection are its endpoints, not this
   missing bridge. A truth lemma for one supplied generic cannot establish
   the claim for conditions outside that generic.
2. Instantiate the local deciding relation with that consequence and apply
   `ValueAntichains` to produce the remaining actual antichain supplier.
3. Prove the square/cover bound for the stated general ground, then assemble
   the repaired preservation theorem at omega-one and omega-two. The
   L-specialized result does not establish the general theorem, nor does it
   discharge K3's separate realization assumptions at L.
4. Complete the concrete formula evaluator supplies, ordered-pair and graph
   formula laws, Boolean cardinal preservation and non-CH top values, and
   connect the two required theorem presentations. No generic-existence or
   truth-to-top reflection principle has been assumed.

The inherited `Families`, `Accessibility` and `MemberImage` capabilities
remain visible in the name-based modules. Ordinary Foundation is not host
accessibility, and the L square proof is not a realization of MemberImage.

## Verification and reproducibility

Final regression on 2026-09-13: `sh verify-k10-progress.sh` exited 0.
All 120 positive modules exited 0. The missing-function control failed
with the required exit 42 and matching type error. The nine new positive
modules also passed their individual checks. Scoped prose/glossary checks
on the two updated progress/roadmap documents and `git diff --check` passed.

Persistent checkpoint:
`/Users/alsg/Agentic/bedrock-proofs-archive/k10-progress-2026-09-13`.

Run `sh verify-k10-progress.sh`. The gate checks all 120 positive K7–K10
modules serially, then requires the inherited missing-function negative
control to fail with exit 42 and its expected function-type error.
Per-module logs are in `progress-logs/`. Each Agda invocation uses
`GHCRTS='-A64m -I0 -M8g'`; the script refuses to start when two compilers
are already active.

`reference-production/src` is an unchanged copy of the forcing worktree's
production sources. The library includes this copy so that the concrete
L theorem can rebuild its specific dependencies without writing original
production caches. This is not a full Everything/Milestones typecheck.
The snapshot needs Agda 2.8.0 and cubical 0.9. Cache directories may be
removed or omitted from the archive; sources and library files suffice.

No original production source or landmark was changed. No commit or push
was performed. Earlier archives remain unchanged.
