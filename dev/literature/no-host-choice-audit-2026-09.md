# Audit: no choice axiom in the Agda metatheory

Date: 2026-09-08. Baseline: `0900bc6b`. Scope: the F0-F8 architecture, K0-K15 trophy-3 roadmap, T4 ground definability, current choice interfaces and checked K0 sources. This is a design/source/literature audit, not a completed formal verification of the planned theorems. No source code was changed or new Agda compilation run for this audit.

## Verdict and binding policy

The selected model-relative route to T3 has no identified mathematical step that inherently requires a host choice axiom. It is not yet proved to meet the exact LEM budget. Several previously permissive or underspecified interfaces must be tightened as below. The universal forcing and T4 results remain required; they must not be silently specialized to L merely to obtain witnesses. F7/F8 are scope boundaries, not enough evidence to certify every future frontier theorem today.

The owner forbids assuming choice in the Agda metatheory in any form: full `SetChoice`, countable choice, dependent choice, host Zorn, a general Boolean prime ideal/ultrafilter principle, a global choice operator, or an equivalent selector hidden inside a capability record. Host LEM remains permitted at explicitly justified levels. Internal AC in a specified set-theoretic model is a separate object-language theorem/hypothesis. For L it must be discharged by the existing LEM-only proof. The final T3 constructor must discharge all local witness premises itself. A failed probe must lead to an honest stop report or revised construction, not an extra host-choice assumption.

This does not ban functions constructively assembled from supplied data, induction/recursion with proved unique outputs, or unique-witness elimination justified in Cubical type theory. A theorem about a given ultrafilter or a given well-order is allowed; a theorem manufacturing one for every arbitrary host object cannot be silently assumed. Distinguish a local structure argument from an axiom asserting a choice of such structures universally.

The subsequent [bounded extraction probes](k0-bounded-extraction-probes-2026-09.md) now verify generic stage-bounded L selection and choice-free unique-value extraction. They retire those local risks but do not prove internal ultrafilter existence or internal name/formula closure.

## Evidence already available

- `src/Landmarks.lagda.md:84` and `src/L/Model.lagda.md:49,107` give L ZFC under `LEM (ℓ-suc ℓ)`; internal AC is proved through `L.Choice.Transversal.hasChoiceL`, not a supplied host `SetChoice`.
- The repository also has the separate theorem `V⊨ZFC : SetChoice (ℓ-suc ℓ) → ...` (`src/Landmarks.lagda.md:61`, `src/V/Model.lagda.md:587`). That conditional theorem is not an axiom automatically activated by importing the file. Its choice-dependent branch cannot supply T3's ground under this policy. Use existing L ZFC and, where sufficient, the LEM-only V ZF theorem. Preserve the existing source landmarks unchanged.
- `L.WellOrder.Base.leastOf` (`src/L/WellOrder/Base.lagda.md:169`) derives a unique least witness from a supplied strict well-order, suitable LEM and truncated inhabitation. Its elimination target is proposition-valued by `isPropLeastOf`; it does not derive arbitrary host choice.
- The [ordinary quotient probes](k0-ordinary-model-probes-2026-09.md) already check quotient descent/effectiveness and a truncated-fullness existential step without Choice or LEM. They do not prove all-formula truth or construct the desired internal ultrafilter.
- The [bounded extraction audit](k0-ultrafilter-extraction-audit-2026-09.md) finds stage-local orders for the L instance. The subsequent generic extraction probe checks the claimed universe level; the actual internal ultrafilter predicate, existence and decoding remain open.

A source search for `Choice` is only a locator, not a proof-dependency audit. A harmless explicit finite `chooseName` is not an axiom; conversely a record named `Witnesses` can hide choice. Acceptance must inspect full elaborated theorem types, imports actually used in proofs, and the construction of every selector.

## Stage-by-stage assessment

| Stage | Possible host-choice leak | Required treatment | Evidence/status |
|---|---|---|---|
| K1 ordinary theory/model adapters | Convert internal existential axioms to host functions, or use choice-dependent V ZFC | Preserve propositional satisfaction; use unique set constructions/equality adapters and L ZFC | Restriction/quotient equality adapters checked; full ordinary ZFC bridge open |
| K2 completion and B+ | Select a representative of each separative class; external Zorn for completion | Build regular opens/quotients internally by set operations; use canonical maps and proved unique comparison | Mathematical no-choice completion route; general code implementation open |
| K3 names and inverse translation | Treat arbitrary host branch/weight functions as M sets; choose a P-condition below each Boolean value | Material internal graph certificates; translate through all refining conditions with set bounds; round trips semantic, not chosen representatives | L name recognition/support/entry decoding checked; general-ground and semantic image closure open |
| K4 values and compiler | Choose a name for each attained value or each parameter tuple externally | Fixed-formula internal relation; Separation supplies attained values, Collection supplies later witness bounds without a representative function | Powerset finite Step, admission and predecessor locality checked; pair-key recursion, full Boolean/RO instance, atomic adequacy and Collection open |
| K4/K12a mixing and fullness | Uniform maximum principle for arbitrary host predicates/Boolean algebras; global raw-name selector | Explicit internally coded mixing families; formula-indexed truncated fullness derived from ground ZFC | Local truncated existential transfer checked; actual internal fullness open |
| K5 bridges and generic truth | Select name representatives or generic conditions simultaneously | Define translations/valuation by recursion and quotient descent; eliminate existential witnesses into propositions or use proved unique constructions | General internal name and truth proofs open |
| K6 ZFC/ordinal transfer | Choose witnesses for Replacement or a well-order of quotient values at host level | Internal Collection/Choice on bounded coded sets; prove axiom satisfaction propositionally; derive value-set well-order internally | Proof design only; no extension axiom used to justify its own ground construction |
| K7/K8 ccc, cardinal preservation, delta systems | External antichain choice/thinning/enumeration and host cardinal arithmetic | Prove the combinatorics in the specified ZFC model, with coded families/graphs and ordinary semantic interpretation | Ground-choice use permitted; proofs pending |
| K11 generic existence | Iterate merely existing choices by host DC, or choose countably many enumerations | Concrete supplied enumeration of conditions and relevant dense sets; take least suitable natural index using LEM and recurse | Strengthened constructor contract; general supplied-generic theorem unchanged |
| K12b ordinary ultrafilter existence | Host ultrafilter lemma/Zorn, even weaker than full AC | Prove the theorem internally for a coded nontrivial Boolean algebra using internal ZFC; completeness not needed for this existence theorem | Main missing internal set-theoretic proof |
| K12b actual L witness | Remove truncation into arbitrary data; assume a global well-order of all L | Bound U in the internal power set PB, use an existing stage order and unique least candidate, then decode operations | Generic bounded extraction checked; internal ultrafilter existence and decoding still open |
| K13 ordinary quotient | Choose one representative of each equivalence class; require a witness function for all existential statements | Set quotient, hProp descent, effectiveness and truncated witnesses; formula induction | Atomic/existential part checked; general syntax/universes open |
| K14/K15 concrete models | Pass G/U/Choice to the final constructor; invoke unproved syntactic completeness | Construct U locally from L, use Boolean top values and quotient truth; adapt existing L to same ZFC/CH semantics | No new host-choice premise allowed; actual model still unimplemented |
| T4 G1-G4 | Alternating covers and uniform ground parameters chosen externally; treat all ambient sets as satisfying AC | Internal/parameter-coded bounded construction in a named ZFC ambient model; propositional existence and unique definability | Needs explicit localization of simultaneous-cover sequence and coding |
| F7/F8 | Select infinitely many iterands, embeddings, supports or class witnesses | Supplied coherent diagrams/policies or internally defined recursion; object-level class hypotheses explicitly scoped | Not a blanket proof of feasibility for every future application |

## Internal families are a separate correctness boundary

The existing `TruthAlgebra` operations admit host-indexed joins (`src/Base/Truth.lagda.md:65`). A Boolean algebra complete only for M-coded families cannot automatically instantiate unrestricted host completeness. Use the restricted/internal forcing evaluator and prove agreement only on families admitted by both sides. The final ordinary quotient can use the existing hProp-valued evaluator. An h-set code-indexed W carrier does not prove that arbitrary host branch/weight graphs belong to M; adding host Choice would not repair that internal-set mismatch either.

## Exact fullness boundary

The useful contract is schematic:

```text
for each fixed object-language formula φ and tuple a of M-name codes,
  ∥ Σ τ : MName, value(φ(τ,a)) = value(∃x φ(x,a)) ∥
```

It is proved by the internally coded ground-ZFC argument. It is not a selector returning a raw τ uniformly in every host predicate `P : MName → B`. Even truncated fullness for arbitrary host predicates is an unjustified strengthening: those predicates need not be definable or coded in M, so internal Separation/Collection/Choice cannot see them. The generic quotient lemma may consume a given fullness certificate; the T3 instance must derive it for the shared syntax.

The set-theoretic maximum principle uniformly over forcing notions is equivalent to AC. Its transfer to the Agda host is therefore not justified by LEM; interpreting its proof inside M is a different claim. [Arnold W. Miller, The maximum principle in forcing and the axiom of choice](https://arxiv.org/abs/1105.5324). Bell Problems 1.29-1.30 and Theorem 4.1 refine the witness/quotient distinction in the [retained textbook](bell-2005-boolean-valued-models.pdf).

Boolean uniqueness is not raw path uniqueness. To return data, prove uniqueness of the actual target, use a specific well-order to choose its unique least representative, or return an appropriate quotient. Do not eliminate a Boolean-unique existential into an arbitrary raw name.

## Internal ultrafilter and actual extraction

Internal AC is allowed to prove, for a particular coded B in M, that the internally coded proper filters admit an ultrafilter. Work over internal sets of subsets/filters. The completion of B is irrelevant to this existence theorem. Do not use host Zorn on the external type of all B predicates; that would include subsets not in M.

For T3, use PB = the L-internal power set of B. `Bound (fst PB) (snd PB)` supplies a stage ordinal and an order on ambient members of that stage. Lift a stage candidate back to the restricted L carrier using `Lset→isL`; require membership in PB and the internal ultrafilter predicate. The existing `leastOf` then gives actual data from the truncated existence premise, provided the predicate stays in the permitted universe. This uses a proved canonical selection on this bounded domain. It is neither a global L-order assumption nor host choice for arbitrary families.

Decode the chosen U pointwise via internal membership. Because B and its operations are internally coded, prove the filter and complement-decision clauses for every interpreted Boolean element. This requires carrier/operation correctness, not completeness for external families. A genericity certificate is not needed. A full Boolean model quotiented by an ordinary ultrafilter satisfies the standard truth theorem; the existential proof uses fullness rather than preservation of arbitrary joins. [Hamkins, Boolean-valued model theory](https://jdh.hamkins.org/a-gentle-introduction-to-boolean-valued-model-theory/).

## Truncation, function construction and size discipline

Allowed constructions include: projecting supplied dependent pairs into a function; eliminating a truncated existence into a proposition; extracting a proved unique witness; recursing with a supplied deterministic next-step function; and using an existing well-order with a proved least-witness theorem. None asserts arbitrary choice from merely inhabited fibers.

Forbidden shortcuts include: `∀ x, ∥ Σ y, R x y ∥` to a simultaneous host function without further proof; a section of every quotient; selecting one item from every external antichain; host Zorn/BPI/DC under another name; and converting internal Choice directly to a host picker.

Resizing and choice are independent audit axes. Higher universes, propositional resizing, and the h-set condition do not supply a selector, nor do they turn an arbitrary external indexed family into an M-set. The current LEM budget may discharge particular resizing steps through existing proved theorems; no additional resizing axiom is silently licensed by the no-choice policy.

## Ground definability and longer-term scope

The phrase 'ambient choice' in a textbook proof must be assigned to a named set-theoretic ambient model, not to Agda. In the main forcing application the extension's internally proved ZFC is available; HIT-V under LEM alone supplies ZF, not the optional `SetChoice`-based V ZFC theorem. For rank-local uniqueness, candidates, power-set comparisons, well-orders and alternating-cover relations must be encoded in the actual model where Choice/Replacement is invoked. A mere host pair of arbitrary class predicates does not provide that internal relation automatically.

One subtle T4 gap needs special emphasis: alternating-cover requests can belong to the ambient model without belonging to either ground. It is therefore incorrect simply to say that each ground's internal AC chooses covers for the entire external request family, or that the resulting sequence belongs to either ground. A candidate repair is to first fix an ordinal bound and internally coded bounded cover supplies in both grounds, obtain fixed well-orders with order-isomorphism-to-ordinal certificates, and use least admissible covers. Decode these as actual well-orders, then use deterministic recursion or a coded recursion in the ambient model. Bounding all requests/covers, the local theory and internal definability must be proved. The finitely many initial well-order existences may be eliminated into the final proposition; no family-wide host choice follows. This is a proposed repair, not a completed simultaneous-cover proof.

Keep the output ground family as a definable predicate with its proved uniqueness/coverage. No global host function choosing a preferred code, generic or poset for every ground is required. A full transfinite alternating-cover sequence requires a construction, not a recursive invocation of truncated existential cover witnesses. Use bounded internally coded relations/choices or proved canonical selection with the exact local theory. If the current weak fragment cannot fund the construction, report and prove the necessary local lemma rather than assume host DC.

For iterations, the iterator consumes actual iterand/embedding/support data or a proved internally definable rule. It does not infer a coherent infinite diagram from pointwise merely existing stages. Class forcing may need object-level class comprehension/recursion or global-choice hypotheses in a specified class model; these are never automatically upgraded to a host class-choice operator. The strict host policy persists for all future work, while each named frontier theorem gets its own feasibility audit.

The [partial-table and image probes](k0-partial-atomic-tables-2026-09.md) now verify that a compatible table union returns its unique value by elimination into a proved proposition, without selecting a contributing table. The actual L image formula handles a supplied internal table. The pending bounded recursion construction must form the internal candidate family before WFI, then prove union totality; no record may substitute host-wide graph closure or a total step on arbitrary predecessor functions for this proof.

The [internal candidate-table probes](k0-internal-candidate-tables-2026-09.md) now form actual L products, bounded formula-selected candidate families and their internal unions. A concrete functionality formula and actual-code readout show how merely inhabited functional fibers return unique values with no LEM or Choice in that adapter. The family constructions use the existing LEM-only ground. No recursive union is yet proved good or total; the complete Good/Step bridge remains essential.

The [Good-formula and extension probes](k0-good-table-extension-2026-09.md) now derive finite-step consistency from step uniqueness, prove internal extension preservation by locality and compose this with the actual Good formula/candidate family. Conditional WFI totality eliminates a truncated output only into domain membership. The subsequent recursion composition proves the internal union good; the actual admitted Boolean step remains open. No host-choice or implicit host-wide step-totality assumption fills that gap.

The [bounded internal recursion probes](k0-bounded-table-recursion-2026-09.md) now prove compatibility and internal Good(T) from the nonrecursive step laws, then construct total values by WFI and unique readout. Solve requires no compatibility or Good(T) argument. The constant-step instance supplies all step laws concretely. Actual Boolean admission and atomic adequacy remain major unproved obligations; no general host function is asserted to have an internal graph.

The [real-name-pair and weighted-image probes](k0-name-pair-weighted-images-2026-09.md) now derive actual closed name-pair domains and WF from existing L names, and uniquely decode coordinates by a proved propositional fiber. Their first weighted image is bounded Separation over coded entries and a coded operation, without a host image selector. Full Boolean Step admission and uniform syntax remain open.

The [indexed-image and supremum-syntax probes](k0-indexed-images-suprema-2026-09.md) now eliminate merely existing predecessor values only into graph propositions to derive the image-locality premise. Their shared two-orientation syntax and B-relative supremum reading require no host selector. Actual internal image realization for the uniform template and the Boolean completeness instance are still required; the formula for a supremum does not construct one.

The [uniform internal-image probes](k0-uniform-internal-images-2026-09.md) discharge shared actual image realization using L Separation under the existing LEM hypothesis. The generic formula substitution lemma needs no classical assumption. Both image localities reuse proposition-valued graph transfer; no witness family is selected. Actual Boolean completeness and the later Step and model-construction obligations remain open.

The [actual powerset weighted-join probes](k0-powerset-weighted-joins-2026-09.md) construct relative suprema as unions of actual internal bounded families and meet as Separation. The composed formula returns actual weighted values for P(X) under the existing LEM, with no host-family completeness or witness selector. This discharges the concrete meet/relative-join instance check, not the general Boolean/RO instance or full Step obligations.

The [outer-image and powerset-expression probes](k0-outer-weighted-expression-2026-09.md) construct implication and infima by internal Separation, including empty-family top, and construct both outer images through a finite inner-supremum relation. Canonical inner values are inserted into those sets without a selected witness family. Branch locality transports propositions along image equalities. Complete Step uniqueness/admissibility, general algebra/RO construction and the later extraction obligations remain open.

The [finite powerset Step probes](k0-powerset-step-formula-2026-09.md) discharge the powerset raw-coordinate Step formula, uniqueness, explicit admission and full predecessor locality. Extremum uniqueness reuses the existing unique-result core on actual bounded image members; no witness family is selected. Pair-key recursion integration, general Boolean/RO realization and the later extraction obligations remain open.

## Required next verification

The [internal-name probes](k0-internal-names-probes-2026-09.md) now verify L supports, data-valued entry decoding and full first-order name recognition. Its converse uses a supplied deterministic definable step with a proved internal omega-iteration theorem, not host DC. Images of supplied coded tables are now checked; weighted recursive images, atomic graph adequacy and general-ground adapters remain open.

The [material-name/value-set probes](k0-material-names-value-sets-2026-09.md) now verify unary material accessibility and the host name carrier without Choice, plus ground attained-value Separation conditional on fixed-graph adequacy. The latter needs no Collection just to form values; Collection remains required for witness sets where later proofs use them. The subsequent L name-recognition proof discharges the instance's recognition obligation; atomic-graph adequacy and its generic adapters remain major open obligations.

1. Generic bounded L-candidate extraction is now checked at the claimed LEM level in the linked probe ledger. Instantiate it with the actual internal ultrafilter predicate once its existence and decoding have been proved.
2. Extend the checked L name interfaces through general-ground adapters and prove internal atomic value graphs, then instantiate the checked attained-value Separation. Derive Collection where witness sets are needed and prove formula-indexed truncated fullness without external graph closure or a global selector.
3. Implement internal ordinary-ultrafilter existence and its decoding, separately from quotient truth.
4. Generalize the checked quotient lemma to shared formulas/universes without selecting representatives.
5. Give K11 a concrete enumeration/least-index constructor; separate mere existence corollaries from data-returning constructors.
6. Localize T4's simultaneous-cover and coding arguments to named internally coded sets/theories.
7. Before accepting any milestone, audit the complete theorem dependency and all witness-bearing records; `--safe` alone does not exclude a choice axiom passed as an explicit parameter.

Conclusion: no new host-choice axiom is authorized, and none has been shown necessary for the selected T3 strategy. The current route needs the above contract repairs and still lacks major proofs. It is defensible to continue under the strict restriction; it is not defensible to report the entire route or its exact LEM budget already verified.
