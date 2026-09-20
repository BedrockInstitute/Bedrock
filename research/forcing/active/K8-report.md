# K8: internal Cohen conditions and ccc

Status: **complete at the isolated K8 proof-probe gate**.

Work continues in `/Users/alsg/Agentic/bedrock-forcing-cohen-k0`, branch
`research/forcing-cohen-k0`. The working proof snapshot is
`/private/tmp/bedrock-k8-probes.3vlTiP`.

The final durable checkpoint is
`/Users/alsg/Agentic/bedrock-proofs-archive/k8-complete-2026-09-13`.
The older incomplete checkpoint at `bedrock-proofs-archive/k8` is retained
unchanged. The new checkpoint includes the full inherited probe source
dependencies, K8 sources, assumption ledger, checksums and verification logs.
Its Agda library uses this forcing worktree's `src` and Cubical 0.9; it is not
a standalone copy of the production repository.

## Delivered mathematics

The generic finite-partial-function layer constructs the ground carrier and
reverse-inclusion order, domains/ranges, restriction, compatible union and
fresh-coordinate extension. The Cohen instance uses the actual sets
`κ × w` and `two = {empty, {empty}}`. The coded D and E families have
density proofs, with the correct some-value and unequal-value requirements.

The old internal pairing gap is closed: `DiagonalOrder` constructs
`w × w ↪ w`, and `CountableZFC` discharges the countable-union theorem's
pairing input. All countability statements use actual ground-coded injections.

`FullDeltaSystem.AtOmega.finite-delta` proves the uncountable delta-system
lemma from the declared ground assumptions. It uses finite-size layers,
deletion and bound descent, and a second branch that constructs countable
connected components using an internal omega-recursion graph. Internal Choice
selects an uncountable disjoint representative subfamily; the raw choice set is
clipped to the original family. No host recursion or well-order is used.

`DomainFamilies` proves the necessary finite-fiber passage from conditions
to domains. `CohenCCC.AtOmega.ccc` applies the actual delta-system theorem
and uses finite root assignments to contradict an uncountable antichain.
It never identifies distinct functions merely because their domains agree.

`CanonicalCertificate` constructs the structural completion certificate.
`CertifiedCCCTransfer` proves CCC transfer to the actual
`Certificate.Nonzero` carrier, including the equality with the inhabited
regular-open presentation and its coded order. The result is attached as an
actual `Certificate.Property.PropertyTransfer`, whose internal-Choice
hypotheses are explicitly inhabited.

The concise public composition is `K8/Theorem.agda`:
`OverZFC.cohen-ccc`, `completion-ccc`, `certificate`,
`property-transfer`, `coordinate-dense` and `distinct-dense`.
There is no assumed delta-system theorem, Cohen CCC, completion CCC or pairing
injection in those final endpoints.

## Assumptions and checks

The full endpoints use ordinary Extensionality, Pairing, Union, PowerSet,
Separation, Collection and FoundationInduction; explicit path realization of
model equality; `LEM ℓ`; ordinary internal `ChoiceSet`; and an actual set
`w` satisfying `CardinalBridge.isOmega w`. The index set `κ` is arbitrary.
There is no CH/GCH or cardinal-arithmetic hypothesis, host Choice, generic
filter, fullness, resizing or additional universe assumption.
See `K8/ASSUMPTIONS.md` for weaker intermediate interfaces.

Final aggregate and serial verification: **all 62 K8 modules returned exit 0**,
including `Theorem` and `Smoke`. The serial runner returned exit 0 and ended
with `K8 ALL MODULES VERIFIED`.

The runner uses `GHCRTS="-A64m -I0 -M8g"`, checks available Agda slots and
records a log and exit code for every module. Independent mathematical
review checked the actual definitions, formula indices, component selection,
internal recursion and counting arguments. The previous two negative
controls' exit-42 evidence is retained. Interrupted elaboration checks are not
counted as successes.

All 130 inherited K0-K7 Agda files remain byte-identical. No production
`src` file, milestone, glossary, reading route or old checkpoint was changed.
Existing dirty edits were preserved; only this K8 report and an added roadmap
completion paragraph were updated. No commit or push was made. These are isolated proof
probes, so no claim is made that production `make check` or milestone-lint
was run. Completing K8 does not advance K9-K15 or establish the later Cohen
model/CH-independence theorem.
