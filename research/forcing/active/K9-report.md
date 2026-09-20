# K9: the internal Cohen family

Status: complete at the isolated K9 proof-probe gate, over the explicit inherited K3 realization and K6 powerset capabilities below. All 19 formal K9 modules, the public theorem and the aggregate import pass the safe Agda gate.

The isolated proof workspace extends the immutable K8 checkpoint. Its inherited K0 through K8 Agda sources are not edited. The production source tree, existing ZFC/GCH landmarks and their hypotheses are outside this change.

The source dependency is the `research/forcing-cohen-k0` worktree at commit `cbd1510efd048c77a7c3e7af972166f44f7b9338`. The proof checkpoint is `/Users/alsg/Agentic/bedrock-proofs-archive/k9-complete-2026-09-13`; it retains the Agda library configuration pointing to that worktree's `src`. Reproduce the scoped gate with `sh verify-k9.sh` from the checkpoint directory, using Agda 2.8.0 and cubical 0.9.

## Construction and semantic targets

`NameGround` instantiates the existing material-name implementation over K8's actual Cohen condition carrier and decoded forcing notion. `RealNames` constructs the ground code of each real by separating conditions assigning bit one, forming the weighted checked-natural entries, and taking their indexed union. It proves name validity and a ground-set bound on the children.

`PairNames` supplies shared singleton, unordered-pair and Kuratowski ordered-pair name constructors. Its ordered-pair theorem uses `CardinalBridge.isKPair` at the actual K5 extension structure. `IndexedNames` supplies a shared indexed collection constructor, its exact ground entry specification, validity, support bound and valuation law. `IndexedControl` identifies the checked identity family with the inherited standard check name by ground extensionality.

`GenericBits` uses the existing coded D sets for totality and E sets for separation of coordinates. Functionality follows from directedness and the actual finite-map extension laws. These are host relations used to prove the interpretation of a ground-coded name, not a replacement for that name or the internal graph.

The graph is a single indexed collection of ordered pairs of checked indices and real names. Its proved injection predicate is the full `CardinalBridge.isInjection` at the actual K5 extension, not a host function type. The powerset target is an actual witness for the extension's powerset of checked omega.

`GraphNames` owns the ground construction and support; `GraphInjection` owns the valuation and injection argument. These were separated after the combined module reached the prescribed 8192 MB heap limit (Agda exit 251). The cap remains unchanged. The Boolean realization is likewise separated into support, atomic semantics, translation and check reflection, with the final name comparison and real argument as consumers.

Binary declaration checks subsequently isolated the Boolean comparison's resource problem to a `with` abstraction over the actual reflected equality theorem. The imported instances, complete parameter suppliers and comparison endpoints all checked separately. Replacing that abstraction by an explicitly typed local sum eliminator made the full comparison and reflection module pass, without changing its statement or assumptions.

The same change resolved the graph proof's resource failure; its final scoped check took 7.7 seconds. Explicit local witness types also resolved an expensive elaboration step in the translated-real entry decoder. No heap increase or weakened safety setting was used. Diagnostic copies were moved out of the formal K9 directory and retained separately, rather than counted as completed interfaces.

The Boolean route translates these same real names through `TranslateForward`. It derives local atomic membership and nonmembership from assignments, reuses E-density and the forcing bridge, and proves top-valued inequality. Truth at an externally supplied generic alone is not used to infer Boolean top. The comparison of translated poset checks and canonical Boolean checks is a proved top-valued equality, not definitional identification.

## Public endpoints

| Result | Checked endpoint |
|---|---|
| Ground-coded graph and its ground support | `GraphNames.graph`, `graph-support` |
| Exact graph membership and domain in the actual extension | `GraphInjection.Injection.graph-value`, `graph-domain` |
| Real-valued subsets of checked omega and distinctness | `RealValues.AtGeneric.real-subset-check`, `real-values-distinct` |
| Full internal injection at every genuine powerset witness | `Theorem.AtGeneric.injection-at-power` |
| Object-language injection satisfaction | `Theorem.AtGeneric.injection-satisfaction` |
| Truncated powerset witness carrying the fixed graph injection | `Theorem.AtGeneric.internal-injection` |
| Internal cardinal comparison | `Theorem.AtGeneric.internal-cardinal-comparison` |
| Translated and canonical checked names agree at top | `BooleanNameGround.translated-check-comparison` |
| Every condition forces unequal real names, and their inequality has Boolean top value | `BooleanReals.DenseDistinct.forces-distinct`, `distinct-top` |

## Assumption ledger

- Ground structure at universe level `ℓ`, with the existing `NameKernel.Families`, ground `PowerSet`, and the literal equality representation carried by that family profile.
- The inherited `NameKernel.Accessibility` is external well-foundedness of represented membership. It is not silently replaced by first-order Foundation or inferred from it.
- The inherited `NameKernel.MemberImage` supplies images of host families indexed by represented members. It is an explicit K3 realization capability, not a consequence established here from first-order ZFC, and its L specialization remains a separate obligation. K4's attained value-set realization spends this same capability.
- Ground `FoundationInduction`, an actual ground omega witness and `LEM ℓ` are used where the K8 dense-set arguments or classical distinctions require them.
- The valuation theorem takes a supplied model-generic filter for the actual decoded Cohen notion. No generic-existence theorem is asserted.
- The final powerset existential consumes `OrdinaryProfile.PowerSet` at the actual K5 extension, separately from ground `PowerSet`. This is the output interface of K6's conditional `hasPower`. Its full Cohen/TruthSeam realization is not claimed as newly assembled by K9. Functionality, support, real-subset and distinctness proofs do not assume the injection conclusion or a powerset witness.
- No host choice, global witness selector, resizing, generic-existence reflection, CH/GCH, cardinal-arithmetic assumption or continuum upper bound is introduced. Truncated existential witnesses are eliminated only into propositions in the final result.

K9 is relative to these explicit inherited realization and K6 capabilities. It is not an ordinary-ZFC-only model constructor, an L specialization, K10's not-CH contradiction, or production integration.

## Validation

`GHCRTS='-A64m -I0 -M8g' agda K9/Theorem.agda` and the same command at `K9/Smoke.agda` both exited 0. `sh verify-k9.sh` exited 0 with `K9 ALL MODULES VERIFIED`: all 19 formal modules passed serially. The script checks the process count before each compiler invocation and retains per-module logs under `K9/logs`. The aggregate imports the K8 aggregate and every formal K9 module. The new Agda sources total 2,493 lines, measured as a cost rather than an optimization target.

Every formal K9 source retains `--cubical --safe --guardedness`. The final source scan found no postulate, termination bypass, `trustMe`, hole, unsolved-meta allowance or diagnostic verbosity option. Production `make check`, source integration, commits and pushes were not performed.

The scoped prose and glossary gates both exited 0 with Python 3.11. The research record does not change the trilingual source chapter framework.

The independent read-only audit of `NameGround`, `RealNames`, `PairNames`, `IndexedNames`, `IndexedControl`, `GenericBits` and `RealValues` passed. It checked actual forcing/extension identity, ground versus valued equality, proposition-only truncation elimination, use of the inherited D/E proofs, and absence of hidden Choice or stronger LEM. Two nonblocking observations were recorded: a broad public module alias in `PairNames`, and the local witness-tail abbreviations in `GenericBits`. The latter describe the existing E specification; they do not reprove its density.

An exact directory comparison, excluding only new K9 files and the build cache, verified all 192 inherited Agda modules unchanged against the K8 completion archive.

The independent second audit verified that Boolean support uses the actual Boolean carrier, while poset support uses the actual Cohen carrier. Entry-code transport is derived from Kuratowski-pair uniqueness; it does not transport a condition-membership witness into Boolean-carrier membership. The atomic value-set supplier comes from the explicit inherited `MemberImage` capability.

The public theorem received a separate read-only audit. It found no assumed injection or real-distinctness conclusion. The ground and extension powerset premises are distinct, the powerset witness remains propositionally truncated, and the satisfaction theorem uses the actual `CardinalBridge.IsInjection-bridge` at the actual K5 extension structure.
