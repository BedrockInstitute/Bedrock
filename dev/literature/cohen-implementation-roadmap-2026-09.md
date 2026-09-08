# First forcing milestone: a Cohen extension violating GCH

Design date: 2026-09-08. Status: implementation roadmap, with no new checked forcing code. This refines the [long-term architecture](forcing-geology-design-2026-09.md), which remains authoritative for component boundaries. Cohen is now the first headline application; ground-model definability is the second. This ordering does not weaken either public interface, the required semantic bridges, or the future extension calculus. The owner requested this planning deliverable in `dev/literature`; source implementation and teaching integration require subsequent scoped briefs.

The [Bell 2005 reassessment](bell-2005-route-reassessment-2026-09.md) supplies textbook theorem locators and refines the contracts below. The [full text](bell-2005-boolean-valued-models.fulltext.md) is a search artifact; exact mathematical expressions can be checked in the [local PDF](bell-2005-boolean-valued-models.pdf).

## 1. The result and its completion contract

Given a transitive ground M satisfying first-order ZFC, let κ = (ω₂)^M and P = Fn(κ × ω, 2, finite)^M, ordered by reverse inclusion. For a supplied M-generic filter G, construct the actual extension and prove:

    M[G] satisfies ZFC + not CH, hence ZFC + not GCH.

All sets, finite-function collections and ground cardinals in the hypothesis are computed in M. The semantic CH predicate and its object-language sentence must agree; likewise for the ω-instance of GCH. The conclusion must identify the extension's ω₁ with the embedded ground ω₁, not merely preserve an ordinal comparison. The function witnessing many reals must be an internal set-coded injection in M[G].

Deliver three connected outputs: the poset theorem, the corresponding Boolean-name/value theorem for the internally computed completion, and the theorem identifying their generic specializations. Include a separate generic-existence corollary for an externally countable transitive set ground, with an explicit enumeration or the exact hypotheses producing one. Do not assert that such a ground exists. The generic-existence constructor is a library facility, not a restriction on the supplied-generic theorem.

For proper-class ground instances, the ambient realization must explicitly support the ground predicate, recursion, names and extension interpretation being used. Do not manufacture an L-generic in the existing ambient universe from L⊨ZFC. An L specialization is conditional on the requisite realization and generic, and cannot be used to discharge the main theorem vacuously.

The milestone requires neither exact continuum ω₂, nice-name counting nor ground GCH. It does not include a syntactic relative-consistency theorem, which has a distinct soundness/proof-translation interface. Preserve the existing L⊨ZFC and L⊨GCH unchanged.

## 2. Implementation sequence and dependency graph

K labels are implementation work packages, not final Agda module names. F labels refer to the master architecture. A package can be split into coherent source briefs; its exit condition remains mandatory.

| Package | Architecture phase | Requires | Concrete output |
|---|---|---|---|
| K0: representation probes | F0 | Existing audits | Safe witnesses for model, names, sizes and the compiler boundary |
| K1: theory and model adapters | F1 | Accepted K0 contracts | Common ZFC/CH/GCH interpretation and transitive-ground interfaces |
| K2: structural forcing and automatic completion | F1/F2 | Relevant K1 set/model primitives | Preorders, lawful Booleans, model-internal completion and B⁺ certificates |
| K3: names and structural evaluation | F2 | K1, relevant K2 | Names, codes, valuation, translations, check and generic names |
| K4: Boolean semantics and internal compiler | F3 | K1-K3 | Sized formula values, equality laws, definability and separate witness capabilities |
| K5: poset clauses and semantic bridge | F4 | K2-K4 | Recursive clauses, formula agreement, generic truth and extension correspondence |
| K6: extension theory | F5 | K3-K5 | ZF, separate AC and ordinal transfer, trivial forcing and both public APIs |
| K7: chain conditions and preservation | Early F5 preservation slice | K1-K5; K6 for extension cardinal interpretation | Distinct CCC predicates and ground-ZFC cardinal preservation |
| K8: Cohen conditions and ccc | C1 | K1 and K2 structural posets | Internal finite maps, coordinate density, delta-system ccc |
| K9: internal family of reals | C2 | K3-K6, K8 | Set-coded family, Boolean correspondence and distinctness |
| K10: final Cohen theorem | C3 | K6-K9 | Both theorem presentations and their generic specialization |
| K11: generic-existence constructor and release | F5/C3 integration | K2; K10 for final application | Countable-ground corollary, assumption audit and integration gates |

K8 starts as soon as its set mathematics is ready; it need not wait for semantics. The generic-enumeration part of K11 can also start early. K7's possible-value arguments and K6's axiom proofs can progress separately after K5. K10 cannot bypass K6 or K5 because a host Boolean countermodel is already available.

```mermaid
flowchart TD
  K0["K0: probes"] --> K1["K1: theory and models"]
  K1 --> K2["K2: completion adapter"]
  K2 --> K3["K3: names and evaluation"]
  K3 --> K4["K4: Boolean semantics"]
  K4 --> K5["K5: poset and semantic bridge"]
  K5 --> K6["K6: extension ZFC"]
  K5 --> K7["K7: preservation"]
  K6 --> K7
  K2 --> K8["K8: Cohen combinatorics"]
  K6 --> K9["K9: internal reals"]
  K8 --> K9
  K7 --> K10["K10: Cohen theorem"]
  K9 --> K10
  K10 --> K11["K11: release and existence corollary"]
```

The likely critical path is K0-K6, followed by joining preservation and the Cohen family. This is a dependency estimate, not a timing prediction. Ground-definability uniqueness and rank-local coding can develop independently after their own foundations exist; they are not prerequisites of Cohen.

## 3. K0: resolve representation risks with real probes

Produce a short representation decision record accompanied by small `--safe` Agda probes in a task-specific temporary directory. Use actual existing interfaces where possible, not renamed empty records.

| Probe | Required evidence | Failure response |
|---|---|---|
| Ground/profile adapter | A concrete structure with equality coherence and an interpreted axiom; inspect Foundation and Infinity separation | Split strong host model assumptions from first-order axioms |
| Raw-name carrier | A well-founded recursive name operation and its universe/h-level obligations | Choose a justified material or set-level presentation; do not assume universe-indexed W-types are h-sets |
| Atomic semantics | Nontrivial Boolean-valued membership/equality and congruence on a small name example using safe pair-of-names recursion (Bell equations 1.15-1.16) | Revise recursion or quotient design before formula semantics |
| Quantified semantics | A genuine existential with an admitted join family or rank bound, plus a fixed-formula compiler correctness obligation that does not assume internal global truth | Separate the restricted evaluator from unrestricted host completeness |
| Internal completion | A small ground-coded example with completion membership and map correctness | Repair ground-code closure; an external RO(P) alone is insufficient |
| Nonseparative presentation | Two distinct conditions identified by separative semantics, with the dense-map specification | Use semantic equality, not raw-condition injectivity |

Record universe levels, LEM, resizing, truncation elimination, host choice, internal choice and genericity separately. If a required assumption is not available, report the exact obstruction; do not add it to existing landmarks. Record the safe recursion strategy and the proposed proof order for quantifier bounds. K0 is complete only when the risks have concrete evidence or an explicit unresolved blocking obligation. Failed probes are measured results, not completed interfaces.

## 4. K1-K3: reusable foundations and the automatic adapter

K1 defines common first-order ZFC schemas and general-model CH/GCH formulas, with semantic bridges for functions, injections, ω, powersets and cardinals. Reuse existing syntax, manipulation and evaluation laws. The strong current model record is adapted through proved equality and axiom lemmas. It is not the default contract for arbitrary first-order models. Internal cardinal code lemmas must not import L-specific condensation. Add explicit equivalences for Bell's Collection-form Replacement and induction-form Regularity (pp. 17-18); do not confuse the latter with host accessibility.

K2 separates structural preorder/Boolean mathematics from forcing semantics. State the stronger-condition convention, compatibility, dense and predense subsets, filters, and model-relative genericity. Preserve nonseparative presentations; separativity and a largest condition are supported adapters or additional data. Define completeness relative to the model's coded subsets. A ground-complete algebra is not automatically complete for external families.

The completion adapter has the following schematic mathematical contract, not a promised existing Agda signature:

    input:  M, a code for P and its order, proof of the forcing laws
    output: a code for B = RO^M(P), Boolean and internal-completeness laws,
            i : P -> B+, compatibility/refinement laws and density,
            agreement between host presentation and ground codes

Computing a Boolean completion in ZF does not require a global Choice hypothesis. Audit that construction independently from later ZFC theorem packages. Power Set and the other actual set-existence hypotheses still belong in its contract. B⁺ is the reverse structural adapter, with the completion comparison appropriate to B. Include identities, coherent map composition for the supported maps, and explicit noninjectivity of i for nonseparative P. Arbitrary monotone maps do not receive completion lifts automatically. Include comparison of two certified completions via joins of the images of conditions below each Boolean element (Bell Lemma 2.3). A specialized backend can then reuse semantic proofs without a second forcing engine. A complete-subalgebra inclusion only receives the justified atomic/bounded-formula agreement (Theorem 1.20 and Corollary 1.21), not arbitrary-formula elementarity.

K3 adds well-founded names, subname/support bounds, valuation, check names and a name for the generic filter. Translate conditions in P-names through i. For reverse translation investigate replacing a Boolean weight by all refining P-conditions, avoiding a choice of a single representative. Prove set-code closure and bounds for the whole translated support. Denotational round trips wait for K4/K5; raw names need not coincide.

Use recursion once where both representations genuinely share it. Boolean equality must survive any quotient of names. A quotient by ordinary extensional membership is not justified merely because the existing cumulative hierarchy uses one.

### Automatic conversion versus automation tooling

The first delivery is an ordinary proved construction callable without tactics. Its outputs are symbolic sets, predicates, maps and certificates; it does not enumerate an arbitrary infinite powerset. Reusing a certificate should not repeatedly rebuild independent completions in each application.

The semantic adapter is layered onto the structural output after K4/K5. It supplies translated names and formulas, generic transport, and satisfaction agreement. An elaborator or tactic may later select this adapter automatically, but must generate terms checked by the same safe kernel. Such tooling is not a prerequisite for the first trophy. Mathematical automatic conversion is required; an elaborate interactive compiler product is not.

Keep semantic certificates and property certificates distinct:

| Requested operation | What authorizes it |
|---|---|
| Produce RO^M(P) and i | Structural completion theorem and internal set existence |
| Translate a name/formula/generic | Its particular translation/correctness theorem |
| Transfer CCC₂ from P to RO^M(P) | Explicit theorem under ground ZFC or another proved sufficient profile |
| Transfer closure or a size estimate | A property-specific theorem, not semantic equivalence |
| Select a maximum-principle witness | The separately supplied witness/choice capability |

A ZF completion request with only CCC₂(P) must not manufacture CCC₂(B). Distinguish CCC₁, CCC₂ and CCC₃ in the public predicates. Likewise DC assumptions are attached to the theorem using them, not treated as the entry fee for completion. [Karagila-Schweber, sections 4-7](https://link.springer.com/article/10.1007/s40879-022-00564-2).

## 5. K4-K6: one semantic proof home and an actual extension

K4 first proves Boolean atomic equality, membership and substitution. Resolve set-coded quantifier-value existence and bound independence before defining unbounded formula values. Build the host syntactic compiler producing internal Boolean forcing formulas and prove correctness by formula induction. For each fixed input formula its output is interpreted inside the ground. Do not claim an internal global truth-value function on all formulas of that ground's own universe (Bell p. 24). Agreement with the host evaluator is conditional on both admitting the relevant families. The model's Separation/Collection/Replacement supplies internal value sets or bounds; extension Replacement cannot be used here.

Explicit-family mixing, unique-existence witnesses and general fullness/maximum principle are separately scoped results with exact selection assumptions (Bell Lemma 1.25 and Problems 1.29-1.30). The unique-existence result needs no AC in the set-theoretic argument, but its uniqueness is Boolean equality rather than raw-name equality. The maximum principle uniformly over all complete Boolean algebras is equivalent to AC; do not export it from Boolean completeness alone. They are not prerequisites for defining a supremum whose existence their proof uses. The available ZFC profile can discharge internal selection needs in the Cohen path, without adding host set choice to the generic kernel.

K5 transports the canonical compiler and semantics to P and proves the ordinary poset clauses, their characterization, monotonicity and density. The public equivalence is:

    p forces_P φ(τ) iff i(p) <= BooleanValue_B(φ(translate(τ))).

For corresponding model-relative generics, prove valuation agreement and generic truth, without requiring a maximum-principle witness. Prove extension isomorphism fixing the ground, including membership and satisfaction. A full-model arbitrary-ultrafilter quotient theorem may separately use the maximum principle (Bell Theorem 4.1); it must not silently strengthen this generic-truth contract or claim well-foundedness for arbitrary ultrafilters. Generic correspondence must meet all coded dense subsets, not just the maximal antichains available under an unstated Choice principle. Expose direct poset lemmas so application proofs do not unfold RO membership.

K6 transfers the axioms with one substantive proof per genuinely different profile. Give separate obligations for Extensionality/Foundation, elementary set constructions, Separation, Power Set, Replacement and AC. For Power Set normalize candidates to Boolean-valued functions on the given name's domain in M (Bell Lemma 1.38); for Collection/Replacement uniformly bound witness ranks across that domain using ground Collection and forcing definability (Lemma 1.36). Neither proof may collect a proper class of names by host fiat. Prove no new ordinals and the identification of ground naturals. Prove AC separately from ZF and keep the base APIs usable with a weaker ground profile where their theorems permit it. Label every result by its ground assumptions: a proof of extension ZF that uses ground ZFC has not proved ZF-ground transfer.

Exit examples before the headline theorem: trivial forcing fixes the ground; a nonseparative P has the expected semantic translation; check names preserve membership; the generic-name valuation returns the given generic; a nontrivial existential exercises the compiler and generic truth. An arbitrary-ultrafilter quotient is not accepted in place of M[G].

## 6. K7-K8: preservation and concrete Cohen conditions

K7 belongs to general preservation. Define the three countable chain conditions separately and prove their equivalence under internal ZFC. Prove the ZFC completion transfer used by the Cohen Boolean theorem; it is a property certificate attached to the adapter. This theorem must consume M's choice, not an unmentioned choice function on external families.

The substantive preservation argument can use Boolean disjoint values for alternative ordinal outputs, then export the poset result. Bound possible values coordinate by coordinate in the ground, prove the requisite internal cardinal bounds, and exclude collapsing surjections and forbidden short cofinal maps. The first public consumer needs preservation and identification of ω₁ and ω₂. State the reusable theorem parametrically over ground cardinals in its proved range; do not hide a Cohen-specific preservation proof. General cofinality statements must specify the exact range established, rather than promise every future variant.

K8 is a separate combinatorial branch. Build a reusable internal finite-partial-function interface: graph recognition, domain, restriction, compatible union, cardinality of a finite domain, and fresh-coordinate extension. Specialize it to κ × ω -> 2. Prove this collection and its order are sets in M and that the host finite-map operations agree with the codes. Finite-map mathematics belongs in a generic set component; the application owns the specialization.

Prove the uncountable delta-system lemma for finite sets in the ground ZFC profile, then thin conditions to equal assignments on the finite root. Handle the passage from conditions to their domains: distinct conditions can have the same domain, so justify the finite fibers or use an indexed-family version of the lemma. Two remaining conditions have a common finite-function extension. This proves CCC₂(P). Obtain the Boolean CCC result through the certified ZFC transfer, not by repeating the topological proof.

Also prove the ground-coded dense sets:

    D_(α,n) = {p : (α,n) is in dom(p)}
    E_(α,β) = {p : some n has p(α,n) and p(β,n) defined and unequal}

D requires assignment of a value, not a predetermined bit below every condition. For E use a fresh n outside both relevant finite domains. No exact continuum calculation enters either proof. Bell Theorem 2.12, pp. 65-66, is the reference for the subsequent lower-bound argument; its extra cardinal-arithmetic assumption belongs to the upper-bound half and must not enter this target.

## 7. K9-K10: names for the family and the final contradiction

Define a name for each real as the set of naturals whose coordinate receives bit 1. Define a single name for the graph α -> rα, using shared name constructors for pairs and indexed collections. Prove its support is a ground set. After valuation, the graph is a function on the embedded κ with values in the extension's powerset of ω. If bit sequences are used as the initial presentation, prove their correspondence with subsets of ω.

Use D for totality of the generic union and E for distinctness. Prove the combinatorial density statements once in the poset interface. The bridge yields the Boolean assertion that distinct checked coordinates name unequal reals. This is not a second independent Cohen-real construction. The output is an internal injection, not just an Agda function between external carriers.

K10 combines that injection with K7's identification of extension ω₁ and preservation of κ = ground ω₂. Assuming the extension's CH would give an injection κ -> ω₁ through the internal CH bijection, contradicting the internal cardinal comparison. Derive not GCH through the shared ω-instance theorem. Export both the semantic result and its object-language satisfaction statement.

The Boolean theorem uses checked ground cardinal parameters, whose interpretation is proved. Do not replace ground ω₂ by the ambient host ω₂. The final poset theorem should mention M, P and G and the needed model hypotheses, not expose every field of the completion construction to its user. A separate correspondence theorem documents the Boolean path.

## 8. K11 and acceptance of the first trophy

For an externally countable transitive set ground, enumerate the coded dense subsets to be met and recursively choose descending conditions meeting them. Prefer a supplied enumeration of conditions to choose the least suitable next index, with the required host logic made explicit. Generate the filter with the correct stronger-condition convention and prove genericity. This construction proves existence conditional on the starting model; it does not produce that model from ZFC or provide a generic for the ambient proper-class L.

The first trophy is accepted only after all of the following are checked:

- K0 representation and assumption decisions are resolved, with source-level witnesses.
- K2 automatic completion is general, model-internal and exercised on a nonseparative example; semantic certificates from K5 are reusable.
- Poset clauses, Boolean semantics, internal compiler correctness and generic-extension correspondence are all present.
- ZFC preservation and the required cardinal preservation are generic library theorems, with internal Choice usage visible.
- Cohen's dense-set and finite-map proofs are not mechanically duplicated in the Boolean layer.
- The real family and cardinal contradiction live inside the extension and match the object-language CH/GCH formulas.
- The supplied-generic result and countable-ground existence corollary have distinct honest hypotheses.
- No test or theorem silently grants a choiceless CCC transfer, an external-family join, an arbitrary witness selector or an L-generic.
- The actual named source files typecheck with `--safe`; integration runs the repository's required gates and preserves both existing landmarks.

Use meaningful boundary checks, not tests that merely repeat definitions. Inspect the public types to ensure absence of unwanted host-choice assumptions and to distinguish property certificates from semantic certificates. A full formal countermodel to choiceless CCC transfer is a later application, not a prerequisite; the initial API must already refuse to infer that transfer without a theorem.

Each source brief must name allowed files, prerequisite exports, theorem statements, proof ownership, assumption ledger, acceptance examples and checks. Source/module names are chosen against the live teaching architecture, not fixed here while another conversation is reorganizing it. Before running Agda, count existing processes and use the repository memory guard. K0 can use temporary probes; this document revision itself writes no source code.

## 9. What follows, and evidence

After K10/K11, ground definability consumes the extension, definability, cardinal and coding infrastructure. It adds small-forcing approximation/cover, model uniqueness, rank-local candidate recognition and the uniform ground formula. It does not depend on the not-CH conclusion. Products, iterations, quotients, intermediate models, symmetry and class forcing retain their phases and capability boundaries in the master plan; success here does not mark those phases complete.

Flypitch's weighted-name semantics, Boolean ZFC arguments and Cohen cardinal comparisons are proof-design references for K3/K4/K6/K7/K9. They are not a substitute for K2's ground-internal adapter, K5's actual generic-extension correspondence or K11. Avoid copying its collapse branch for a positive result already supplied by L. Consult the [pinned source audit](flypitch4-source-audit-2026-09.md), the [Cohen comparison](cohen-flypitch4-design-2026-09.md), and the [infrastructure/source ledger](cohen-infrastructure-overlap-2026-09.md). The port was source-audited, not rebuilt in this task.

This schedule is a design inference from those audits and the master architecture. No implementation completion, performance estimate or mathematically optimal representation is asserted. The next actionable brief is K0. Its outcome selects representations within the architecture; it does not reopen the requirement for two usable interfaces and certified translations.

## 10. Validation records

### Initial planning revision

The changed scope is this new roadmap, the master architecture, and the two Cohen evidence notes. Scoped `lint-prose.py --check` and `check-glossary.py --check` both exited 0 on those four files. A local check of 24 relative links, fence balance and absence of em dashes exited 0. The dependency review separates early combinatorial work from completed application acceptance, places required preservation before K10, and keeps the structural adapter independent of downstream semantics.

No Agda probe or source implementation was run in this planning revision. The future K0 probes and implementation gates above are requirements, not reported results. The source chapter-framework gate and whole-tree build were not run for these English research notes.

### Bell textbook follow-up

The follow-up refines K0-K6 contracts using the textbook without changing K0-K11 dependencies or the first trophy. The extraction and combined document checks are recorded in the Bell reassessment. No source implementation was added.
