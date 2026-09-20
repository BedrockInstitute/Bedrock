# K9: the internal Cohen family

K9 is complete at its isolated proof-probe gate, relative to the explicit inherited K3 realization and K6 powerset capabilities below. All 19 formal K9 modules, including the public theorem and aggregate import, pass the safe Agda gate. This is not production integration or completion of K10.

## Checkpoint and results

The checkpoint is `/Users/alsg/Agentic/bedrock-proofs-archive/k9-complete-2026-09-13`. Its `K9-report.md` contains the full construction, assumption and validation record; `K9/logs` contains the serial gate logs. Its library configuration uses the forcing worktree's `src` at commit `cbd1510efd048c77a7c3e7af972166f44f7b9338` on `research/forcing-cohen-k0`. The inherited 192 K0 through K8 Agda files are unchanged from the K8 completion checkpoint.

The real at index alpha is an actual ground-coded name whose entries are checked naturals weighted by conditions assigning bit one at that coordinate. The shared singleton, pair, ordered-pair and indexed-collection constructors produce one ground-coded graph of the real family. Both the real names and graph have proved ground-set support bounds.

| Requirement | Checked endpoint |
|---|---|
| Total generic bits and distinct coordinates, using the existing D/E density | `GenericBits.AtGeneric.bit-total`, `distinct-bits` |
| Actual K5-extension real membership, subsets of checked omega and unequal real values | `RealValues.AtGeneric.real-membership-spec`, `real-subset-check`, `real-values-distinct` |
| Exact internal graph and domain | `GraphNames.graph`, `GraphInjection.Injection.graph-value`, `graph-domain` |
| Full internal injection and its object-language satisfaction | `Theorem.AtGeneric.injection-at-power`, `injection-satisfaction`, `internal-injection` |
| Internal cardinal comparison with the actual powerset target | `Theorem.AtGeneric.internal-cardinal-comparison` |
| Checked-name comparison through the actual translation | `BooleanNameGround.translated-check-comparison`, `translated-check-equality` |
| Every condition forces unequal real names, and their inequality has Boolean top value | `BooleanReals.DenseDistinct.forces-distinct`, `distinct-top` |

The injection uses `CardinalBridge.isInjection` at the actual `K5.Structures` extension, including relation, functionality, totality, range and injectivity clauses. It is not an Agda function presented as an internal set. The powerset existential remains truncated and contains the fixed graph as its actual injection witness.

The Boolean real is the translation of the same poset real name. Bit-one assignments force membership; bit-zero assignments force nonmembership through the existing Cohen compatibility theorem and checked-name reflection. The proof then consumes the actual K8 E-set specification and density, followed by the Boolean forcing regularity bridge. It does not repeat Cohen density or infer Boolean top from truth at a supplied generic.

## Exact inherited assumptions

Ground `NameKernel.Families`, ground `PowerSet`, equality representation, `NameKernel.Accessibility` and `NameKernel.MemberImage` remain explicit. External accessibility is not inferred from ordinary Foundation. The member-image capability is the inherited host-family realization interface, not a first-order ZFC consequence established here; its L realization remains separate. K4 value-set realization spends this same capability.

The dense-set consumers additionally take ground `FoundationInduction`, an actual ground omega witness and `LEM ℓ`. The poset theorem takes a supplied model-generic filter for the actual decoded Cohen notion. No generic-existence claim is made.

The final powerset existential separately takes `OrdinaryProfile.PowerSet` of the actual K5 extension. This is the output interface of K6's conditional `hasPower`, not the ground powerset axiom. K9 does not claim to have newly assembled the full Cohen specialization of K6's truth and definability prerequisites. The graph, real-subset and real-distinctness proofs do not assume the injection conclusion or powerset existence.

There is no added host Choice, resizing, global witness selector, generic-existence reflection, CH/GCH or cardinal-arithmetic hypothesis. There is no continuum upper-bound calculation. K10's cardinal-preservation application and not-CH contradiction remain next; the actual ordinary model and L-specific realization remain later obligations.

## Validation

Both `GHCRTS='-A64m -I0 -M8g' agda K9/Theorem.agda` and the same command at `K9/Smoke.agda` exited 0. `sh verify-k9.sh` exited 0 with all 19 modules passing serially. The script checks for available compiler slots and retains the 8 GB per-process heap cap. The 2,493 new Agda lines are a measured cost, not a reduction target.

Independent read-only audits passed the ground and generic interfaces, cross-carrier entry transport, the complete internal injection, the public theorem's powerset boundary and the final Boolean forcing argument. Source scans found no postulate, termination bypass, unsafe trust, hole or unsolved-meta allowance. Every formal K9 module retains `--cubical --safe --guardedness`.

During development, dependent `with` abstractions reached the fixed heap cap. Explicitly typed local sum eliminators resolved those checks without changing statements or hypotheses. Typed witness helpers resolved an expensive translated-entry elaboration. Diagnostic copies were retained outside the formal checkpoint directory, not counted as interfaces.

The scoped prose and glossary gates use Python 3.11. No production source module, existing ZFC/GCH landmark, commit or push was changed by this task. Production `make check` and source integration were not run for this isolated proof checkpoint.
