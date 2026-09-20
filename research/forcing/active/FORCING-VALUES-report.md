# K10 all-condition forced-value checkpoint

K10 remains incomplete. This checkpoint closes the arbitrary-condition
functional-value consequence and constructs its local possible-value antichain.

## Checked construction

`K7/ForcedFunctionValues.agda` derives equality of two forced values from
forced functionhood. It uses sequential dense existential witnesses,
monotonicity and regularity, not membership of the condition in a generic.
`ForcedFunctionValuesAtClauses.agda` supplies the actual K5 forcing clauses.
`ValuesAtTruth.agda` connects the result to actual K6 `forces`, including the
exact translated checks in its `AtCheck` interface.

`PossibleValues.agda` now uses the canonical `CardinalBridge.PairφK` graph
formula. The former positive-pair formula remains available. The proof of
their satisfaction equivalence uses Extensionality and Pairing; it is not
an assertion that arbitrary forcing predicates assign identical possible
value sets to both formulas. `ValueAbstraction.agda` checks the exact source
formula and constant-vector identities.

`LocalValueAntichain.agda` defines the ground deciding relation by an actual
formula, proves totality, determinacy and incompatibility, and applies the
existing ground Choice antichain construction. `AntichainsAtTruth.agda`
supplies function-value uniqueness from actual K6, order laws from the
forcing bridge and directedness from the supplied filter.

`PreserveAtTracks.WithAntichains` supplies the exact `ValueAntichain`
interface. Its countable-member cardinal assembly applies the actual
family-set, inverse-surjection and countable-cover producers.
`K10/CheckedForcing.agda` exports reflection for the precise translated
checked-name atom required by the new interfaces.

## Remaining boundaries

The K6 adapter still takes the existing generic filter, meeting, evaluator,
translation-surjectivity and formula-supply capabilities. Only the theorem's
condition is arbitrary; no new generic-free engine is claimed. Definability
of forcing and checks, separation construction, ground profile/Choice and
checked-equality reflection remain explicit at the general antichain boundary.
The Cohen reflection supplier is checked separately.

General-ground omega-two square/cover, the complete actual two-cardinal
preservation specialization, concrete compiler supplies and final Boolean
non-CH endpoints remain open. `MemberImage` and accessibility realization
are not supplied by ordinary ZFC or by the isolated L square theorem.

## Reproduction and scope

On 2026-09-13 the serial gate exited 0: all 127 positive modules passed;
both negative controls were rejected with the expected exit 42 and exact
type-error signatures. Scoped prose and glossary checks on the new literature
record and updated roadmap, and `git diff --check`, also exited 0.

Run `sh verify-k10-forcing.sh`. It serially checks every positive K7 through
K10 module with `GHCRTS='-A64m -I0 -M8g'`, then requires both missing-function
controls to fail with exit 42 and their expected type-error signatures.
The controls are intentionally excluded from the positive module loop.

Compared with the previous checkpoint there are seven new positive modules,
five modified positive modules and one new negative control. The unchanged
production snapshot remains isolated under `reference-production`; build
caches are excluded from the durable archive. No production proof, landmark,
commit or push is changed by this checkpoint.
