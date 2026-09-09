# K0 exit checklist and implementation boundary

Date: 2026-09-09. Baseline: `72d01001`. Status: K0 remains open. This checklist consolidates the acceptance requirements in [roadmap section 3](cohen-implementation-roadmap-2026-09.md#3-k0-resolve-representation-risks-with-real-probes) and the subsequent T3 assumption audit. It does not replace failed or missing evidence with a weaker completion criterion.

## Exit rule

K0 ends with a representation decision supported by real safe probes. Passing another isolated example is progress only if it discharges a named item below. Each item must cite checked evidence, state the selected contract and identify the later implementation consumer. An unresolved representation obstruction blocks exit even when it has been documented correctly. Later theorems may remain unimplemented when their prerequisite representation decisions and probe contracts are settled.

The earlier approximate 70 percent estimate was a judgment about progress, not a measured completion or remaining-time metric. This checklist is the operative measure. Do not increase the percentage merely by adding probe files, or continually import later implementation obligations into K0.

## Six fixed acceptance items

| ID | Minimum K0 exit evidence | Current evidence and exact remaining gap | Later owner |
|---|---|---|---|
| E1: ground realization | Concrete equality coherence and an interpreted axiom in an actual target-style model; explicit transitive decoding, external well-foundedness, Infinity and universe contracts | Actual L operations and decoding exist; the singleton example is insufficient. Still connect the general transitive realization contract to a real adapter and record its precise levels and prerequisites | K1 implements the complete axiom/profile and CH/GCH bridges |
| E2: material names | A selected h-set name representation, actual internal support/code closure and safe pair recursion, with a universe and external-WF ledger | Actual L material names, recognition, closed supports, pair dependency and recursion tables are checked. Consolidate the representation choice and distinguish generic requirements from the L backend | K3 implements check/generic names, valuation and translations |
| E3: atomic example | Nontrivial equality and membership values and a representative congruence/substitution check on the chosen representation, using the safe recursion path | Passed at the representative boundary: the [material atomic example](k0-material-atomic-example-2026-09.md) checks actual membership, arbitrary singleton weights, empty equality, and one same-domain zero-weight substitution example with an internally constructed domain | K4 proves the general Boolean atomic laws and substitution calculus |
| E4: quantified value family | A real internally collected attained-value family, its adequacy and an admitted join; fixed-formula correctness without internal global truth; a noncircular ground-side proof order | The [attained-value instance](k0-atomic-value-set-2026-09.md) now checks actual valid-name values, exact internal membership and an admitted join. The construction order below specifies the boundary for later formula induction; the [E3 representative interpretation](k0-material-atomic-example-2026-09.md) is now also checked | K4 implements all-formula compilation; K6/K12 implement witness/rank bounds, Collection and fullness |
| E5: completion contract | A ground-coded small completion example with membership/map correctness, and distinct conditions identified by a dense noninjective completion map | Finite nonseparative and material-code probes exist separately. Check their composition with real finite ground closure and record the K2 input/output certificates | K2 proves general regular-open completion, completeness, uniqueness and map/property transport |
| E6: decision and assumption audit | One decision record selecting ground decoding, name levels, admitted families and quantifier proof order; separate host/internal assumptions and T3 extraction obligations | Existing ledgers, the no-host-choice audit and the checked ordinary-model boundary probes supply evidence. Close E1-E5 and consolidate the decision. Audit the ordinary-model profile, set quotient, internal fullness, internal ultrafilter construction/interpretation and universe/extraction contracts as specified below | K12-K14 construct internal witnesses/ultrafilter, quotient truth and the actual ordinary model |

The name-carrier choice has substantial positive evidence, while E1 and E5 still contain explicit probe gaps. E6 is an integration gate, not permission to declare success after merely listing blockers. A later theorem being unproved is acceptable only when it does not conceal an unresolved representation or assumption issue required by these exit items.

The E6 audit must cite the [ordinary-model probes](k0-ordinary-model-probes-2026-09.md) for real set quotient, atomic/equality descent, truncated-fullness existential transfer and ordinary-structure packaging. For internal fullness and ultrafilter witnesses, specify inputs, outputs, universe/h-levels, permitted truncation-elimination targets and the mechanism for extracting host data from an L-internal witness. An unexplained host selector, BPI/Zorn/Choice assumption or elimination of mere existence into arbitrary data leaves E6 open. Merely assigning the construction to K12 does not settle that contract. The constructions and all-formula truth themselves remain in K12-K14.

## Bounded remaining work order

1. Completed in this batch: E4's actual attained-value set and join instance from the checked fixed graph and valid-name recognition. The [checked instance](k0-atomic-value-set-2026-09.md) reuses `FixedValueSet` and its adequacy/upper-bound transfer. It does not select one name per attained Boolean value.
2. Completed in the next batch: E3's [material atomic example](k0-material-atomic-example-2026-09.md). `ActualZero X` internally supplies the shared domain and proves raw distinction, equality at top and unchanged membership in one fixed context. The arbitrary-weight singleton calculation also checks. Stop this branch here; general substitution and the full atomic theorem library belong to K4.
3. Close E1 and E5 with the smallest real adapter/composition tests that discharge their contracts. Reuse existing decoding, finite constructors and nonseparative probes. Do not implement general regular-open completion merely to finish a finite adapter test.
4. Consolidate E2 and E6, audit the complete probe dependency assumptions and issue the representation decision. Report each acceptance item explicitly as passed or still open. Only then declare K0 complete.

These are acceptance batches, not promised one-turn tasks. A discovered counterexample may require revising the representation; it must not silently add an unrelated milestone to K0. Corrections needed to meet an existing item stay within that item and are recorded with the evidence.

## Quantifier construction order to preserve

The intended ground-side chain is:

```text
actual material-name recognition
  → fixed atomic graph with exact reading
  → Separation inside the Boolean carrier of the values actually attained
  → upper-bound equivalence with the semantic family
  → admitted internal supremum
  → later formula induction and its fixed-formula compiler
  → later Collection/rank bounds when a set of witnesses is required
  → later fullness and extension axiom transfer
```

Collecting attained values does not select a witness for each value. The values form a subset of B even when the names range over the entire external carrier of valid material names. Adequacy must prove that every semantic value occurs and that every collected value comes from a valid name. A bounded join alone does not produce a maximum-principle witness. The concrete atomic test does not establish all-formula compiler correctness or internal global satisfaction.

## Explicitly outside K0 implementation

General `RO^M(P)`, all Boolean algebra laws for that construction, forcing theorem and generic truth, full atomic/formula substitution, all extension axioms, cardinal preservation, Cohen combinatorics, the internal ultrafilter construction, complete quotient truth and the ordinary non-CH model remain with their existing K1-K14 owners. K0 audits their representation and assumption prerequisites, especially the absence of host choice; it does not prove those theorems in advance. K15 assembles semantic CH independence, and ground definability remains T4.

The completed L ZFC/GCH landmarks and their single LEM hypothesis remain unchanged. K0 source work stays in temporary probes, with checked snapshots under `dev/literature`. This checklist changes neither the dual forcing interfaces and certified conversion direction nor the requirement to establish reusable results before T3.
