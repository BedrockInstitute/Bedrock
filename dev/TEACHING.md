# Teaching architecture

Preserve the completed safe ZFC and GCH proofs. Optimize coherent learning units,
explicit prerequisites and reusable mathematical interfaces. Modest code/build
cost increases are acceptable when they buy a specific improvement in those
properties; chapter count and source line count are not objectives.

## Reading contract

- Milestones is an explicitly labelled preview of the final theorem statements.
- All other chapters introduce their direct prerequisites before using them.
- Each chapter names its mathematical question, required concepts and endpoint.
- The reading catalog offers one valid linear extension of the prerequisite
  graph, not a mandatory schedule. Its parallel-route guide identifies shared
  foundations, independent topics and the prerequisites of their join chapters.
  Readers may interleave available topics. Namespace and learning-stage views
  use the same actual modules.
- A reusable theorem lives outside the particular application that first needed
  it. An application should import its prerequisites, not the earlier application.
- Split a chapter when it changes its mathematical question or abstraction level;
  merge material when its explanation and proof form one learning unit. Preserve
  meaningful opacity boundaries even when changing files.

## Accepted architecture

1. **Constants in syntax.** Separate mapping from semantic relabelling. Place
   occurrence enumeration and zero-occurrence erasure together; parameter
   abstraction then consumes that representation. Retire the separate Count
   chapter and migrate real imports without compatibility re-exports.
2. **Internal coding vocabulary.** Separate the Model dictionary, the reusable
   Expressions toolkit and Closure predicates. The broad dictionary import must
   no longer entail learning the entire language for recursion clauses.
3. **Ordinal collapse.** Move the generic Mostowski theorem out of Hartogs's
   cardinal construction. Hartogs and GCH order types become two explicit users.
4. **Satisfaction recursion.** Put shared bounded quantification over coded
   pairs in Quantification; colocate tower construction with its specification
   and readers; isolate the closed code domain in CodeDomain; let SatisfactionClauses start
   with the actual satisfaction relation. Preserve the existing transparent
   proofs, rather than introducing an unnecessary new abstraction framework.
   Generic pair projections belong to Quantification; CodeDomain does not
   re-export its prerequisites as a compatibility entry point.
5. **The whole reading catalog.** Replace the oversized constructibility part and
   obsolete trailing tools section with coherent stages. Fix the 36 measured
   prerequisite inversions, update all chapter descriptions and distinguish the
   completed mathematical results from future research aims.

## Boundaries retained after review

- **Choice.FiniteStageOrders** keeps finite enumeration, comparison and the finite-stage
  order together: these are successive ingredients of one canonical-order
  construction. The generic natural-number well-order is an example in
  WellOrder.Base, shared by Finite and SquareLaw. This removes the accidental
  dependency from ordinal square-law tools to the Choice construction without
  adding a tiny standalone chapter.
- **Coding.HierarchySequence** keeps sequence coding with its approximation interface.
  These form one short lesson from a sequence predicate to
  the table shape used by the hierarchy and choice constructions.
- **Constructible** retains transitivity facts beside the layer constructors.
  In particular, preservation by the definable-powerset operator is genuinely
  constructibility-specific. Moving the whole prefix to a general set chapter
  would misclassify it; extracting only the short predicates would fragment
  the introduction to layers.
- **V.Smallness** retains separation and formula-smallness induction as one
  account of which predicates produce sets. Its consumers need different
  endpoints, but the underlying explanation is shared and the chapter is small.
- **NumeralBound, Descent and Injection** remain narrow, named mathematical interfaces,
  rather than being absorbed into whichever application first imports them.

These choices favor coherent lessons over maximizing either splits or merges.

## Acceptance

- Each moved definition has exactly one substantive home and all real consumers
  import it there; no accidental cycles or compatibility shells.
- The catalog contains every master exactly once, with no prerequisite inversion
  except the explicitly marked Milestones preview. The reading-order gate checks
  fenced imports and runs with `make check`; its tests cover the preview, backward
  prerequisites, exact coverage and prose that resembles imports.
- English, Chinese and Japanese introductions, catalog descriptions, symbols and rendered
  navigation agree with the final module paths and order.
- `make check` passes; the site build and its internal links are checked after
  moves because Agda alone does not validate reader navigation.
- Compare fresh project-interface Milestones time and peak RSS with the last
  verified 201.38 s / 1,865,891,840-byte observation. Keep Cubical interfaces and
  the same memory guard; record costs honestly without treating one run as an
  average. README retains only the compact current figures requested by the user.

## Dependency map and prose review

The graph review found one accidental subject dependency: SquareLaw used
Choice.FiniteStageOrders only for the natural-number well-order. That example now lives
in WellOrder.Base; the original consumers import it directly. The graph has
117 nodes, 1,572 direct imports and 211 edges in its full transitive reduction.
Its longest path contains 33 modules. Genuine convergence in the hull and GCH
assembly remains visible.

The map now offers compact, teaching-stage and namespace layouts over the same
graph. The compact view is 1,164 pixels wide, compared with the previous
3,578-pixel drawing. The stage view is 1,022 pixels wide and intentionally longer
vertically to separate lessons. Every view preserves all nodes and downward
edge direction. Reading stages are derived from the bilingual catalog, and
imports are parsed only inside Agda fences. The page explains transitive
reduction, the omitted hub edges and Milestones' position as a dependency endpoint.

Introductions, closing summaries and order references were reviewed across all
118 masters. Obsolete part numbers, retired-design narratives and false endpoint
or consumer claims were replaced with the current modules and constructions.
The prose audits preserve fenced code; the only additional proof-code change is
the relocation and relation-level generalization of the natural-number order.

## Verification (2026-09-07)

The final tree has 118 masters and 117 reading chapters in ten stages, including
the opening preview. Both catalog languages cover all chapters. All 118 masters
retain `--safe`; the two Milestones endpoint statements and their code are unchanged.
The Milestones dependency closure reaches every master with no aggregator exception.

`make check` passed with 42 tests. All masters, including every new chapter,
also passed explicit Agda/prose lint. The site built successfully into fresh
`_build/teaching-html` and `_build/teaching-site` directories. Its 234 bilingual
chapter pages have the exact catalog previous/next order; the link checker found
zero broken links among 743,855 relative links. Type-hint extraction now respects
`HTML_DIR`, so renamed chapters and their hints use the same generated module set.

The source contains 26,458 nonblank Agda lines, 150 more than before (+0.57%).
This pays for explicit module boundaries and direct consumer imports; it does not
change the syntax constructors, mathematical statements or classical assumptions.

Fresh project-interface typechecking of Milestones passed in 206.23 s with
peak RSS 1,675,280,384 bytes (1.56 GiB), retaining installed Cubical
interfaces and using `GHCRTS="-A64m -I0 -M8g"`. All source hashes remained
identical before and after the measurement. Relative to the pre-reorganization observation,
this is 4.85 s slower (+2.41%) and 10.22% lower peak RSS. These are individual
observations, not averages. The small time and source-size costs are accepted for
the clearer module boundaries and prerequisite order.

Layout validation covers all 117 nodes, non-overlap and downward edges in all
three views. The generated JavaScript also passed 12 layout/edge/reference
combinations and pin/detail callbacks using a DOM test double. Source-derived
SVG previews were visually reviewed. Browser control was unavailable, so these
checks do not claim a real-browser interaction test.

## Parallel reading and definition-level evidence

The definition audit measures first-use separation along the catalog's example
route. That number depends on the chosen topological ordering. It is not a graph
distance, a lower bound on learning time, or evidence that the reader must retain
a definition while studying unrelated branches. Across independent routes, use
prerequisite readiness and explicit join conditions instead of chapter distance.
Within a chosen route, local examples and first substantive applications remain
useful editorial checks; proof helpers and endpoint theorems need separate review.

The next catalog revision places complete optional topics near their applications
in the example route, while keeping their generic mathematical homes intact.
Presentation, strict well-orders, coded injections and the two collapse/bijection
tools can be entered once their prerequisites are ready, without completing every
chapter listed before them. The bounded-quantification and recursion lessons
remain a coherent preparation for the environment tower. None of these changes
introduces a new dependency or changes a proof.

The syntax composition laws remain in ConstantMapping. Moving them into a semantic or
constructibility application would make the interface conceptually heavier for
its other consumers. Their explanation now names the concrete two-step constant
map that the later bridge composes. Transversal no longer falsely claims to be
the well-order search's sole or first consumer.

The parallel-route guide documents four forks and joins: formula manipulation
and the ambient model; external canonical orders and internal satisfaction;
Choice completion and cardinal tools; descriptions and Skolem hulls. Import-closure
checks confirm their stated independence and joins. In particular Hull needs
Choice.StageOrders, and the final GCH theorem needs L.Model; neither dependency is
hidden by calling these routes parallel. The map labels catalog positions as
example-route positions in all three UI languages.

## Reader-facing route explorer

The reading catalog remains a complete example ordering. A `bedrock-routes` HTML comment
in its source carries versioned route metadata: stable route IDs, bilingual
titles/descriptions and chapter membership. Shared chapters may belong to more
than one route. Dependencies are not duplicated in the annotation: the build
extracts them from fenced imports and validates coverage and identifiers.

The landing page offers topic cards, side-by-side routes and a readiness view.
Chapter pages show their own prerequisites and local completion control. A
completed chapter is a reader's self-report, not a tested mastery score. Progress
lives only in the current browser and can be cleared. The original catalog and
dependency map remain available without the explorer; previous/next links are
explicitly labelled as steps on the example route. Parallel routes do not erase
shared prerequisites or require the reader to finish an entire unrelated route.

`reading_routes.py` owns metadata validation and the derived reading data.
`render-site.py` removes annotations from visible prose and emits a language-local
data file. The static explorer assets consume that file without a server or
account. `make lint` validates route annotations; the unit gate covers malformed
metadata and the source-derived prerequisite rules.

### Route explorer verification (2026-09-07)

`make check` passed with 50 tests, including 8 route metadata tests. Source
comparison confirms that all Agda fences outside the reading catalog are unchanged;
the catalog only changes reading metadata. The proof tree remains at 26,458 nonblank
Agda lines and 117 reading chapters. Seven optional topics moved within the
example route; this does not change their actual dependency graph.

The bilingual site renders all 117 chapter explorers and the landing explorer.
Link checking found zero broken links among 744,892 relative links. Actual
headless Chrome verification passed topic/compare/readiness views, one-to-three
route selection, dependency-based readiness, completion and view persistence,
reset cancellation/confirmation, chapter return and browser Back, preview
exclusion, keyboard focus, dark theme and the no-JavaScript catalog. At 390 pixels
the document does not overflow horizontally. Screenshot review caught and fixed
a sticky column heading that obscured a chapter link; columns now use normal
flow. The phone header gives search its own row, and wide catalog tables scroll
inside their own bounds. Review screenshots and the browser test remain in
ignored build output, not in the source or committed documents.


## Trilingual chapter framework (2026-09-07)

The framework covers all 118 masters, including the reading guide: 698 matched
English, Chinese and Japanese titles, each with an opening paragraph about its
own mathematical question and result. Long undivided coding and GCH chapters now
have sections at existing proof boundaries. Later scaffold paragraphs remain for
another phase; the language weaver preserves their English fallback.

The terminology review first reconsidered all 145 existing entries. The central
vocabulary now has 159 entries, with literature evidence and explicitly labelled
composed terms in `literature/terminology-2026-09.md`. Semantic adequacy, local
adequate stages, and the two meanings of reflection remain distinct. The glossary
gate checks explicit translation groups without mistaking fallback prose for a
missing translation.

Fifty-seven module names now state their subjects more clearly. For example,
`Coding.PairFormulas` introduces pair formulas, `Coding.EnvironmentAgreement`
proves agreement of the two environment-set presentations, and
`Coding.NumeralBound` bounds numerals at successor-closed ordinal stages.
`GCH.StageCountingTools` supplies the tools used by `GCH.StageInjection`;
`Choice.NameComparisonAdequacy` and `Choice.StageOrderAdequacy` name the particular
representations they validate. All imports and route metadata use the new names.

The catalog, sidebar, previous/next links and route cards use the actual localized
chapter titles. All three languages are built by default. Agda code must remain
outside language groups, so choosing Japanese cannot hide a proof block.
The framework gate checks every heading and opening; the link checker verifies
cross-page fragments as well as destination files.

Module-name normalization confirms that the nonblank proof lines are unchanged
(26,458), and the dependency graph is isomorphic to the preceding tree: 117 nodes
and 1,572 direct imports. Section changes only split prose and existing fences;
no mathematical definition or proof was moved between chapters in this phase.


The final `make check` passes with 69 unit tests. The three-language site builds
354 master pages; every rendered H1 matches its language's source heading and
all three editions display identical highlighted proof code. Link validation
checks 1,119,318 relative links across 845 generated pages, including cross-page
fragments, with no broken targets. Browser checks cover the route controls,
progress persistence, keyboard use, language switching and the 390-pixel mobile
layout. Long module names wrap in prose navigation and use complete two-line
labels in the dependency map. Build artifacts and review screenshots stay under
ignored `_build` directories.

Chrome also verifies all 117 dependency-map labels in each of the three layouts:
complete names, at most two lines, no overflow or overlap with chapter numbers.
The map remeasures labels after its fonts load. The verified output is copied to
`_build/html` and `_build/site`, so `make serve` opens the current edition.


## Reading interface refinement

The landing page presents reading routes, the dependency map and the chapter
catalog as three tabs. Each has a shareable fragment URL; switching tabs retains
route selections and graph controls. The old dependency-map URL redirects to its
tab. Without JavaScript, the chapter catalog remains accessible. Keyboard users
can switch tabs with arrow keys, Home and End.

Chapter introductions precede the collapsed route/prerequisite panel. Chinese
and Japanese editions keep untranslated English narrative in labelled, initially
closed disclosures; shared mathematical notation and proof code remain visible.
This changes presentation, not the scope of translation. The renderer tests cover
English paragraphs containing CJK quotations as well as symbolic blocks.

The glossary distinguishes the constructible hierarchy, an individual stage
L_α, and its ordinal index α. The Stage chapter now names and explains the last
of these explicitly. Literature evidence and the limits of the proposed CJK
renderings are recorded in `literature/stage-level-hierarchy.md`.

Validation: `make check` passes with 79 unit tests. All 354 master pages retain
matching localized titles and identical proof code across languages; the site
link checker reports no broken targets. Chrome checks cover tab history and
language switching, retained route/map state, progress after reload, English
disclosures, node selection, all 117 labels in each layout, and mobile/dark views.


## Interface refinement before detailed exposition

The definition-level review identified misplaced injection interfaces, broad
re-exports and downstream dependence on hull implementation details. The accepted
work is a sequence of focused changes, with trilingual headings and introductions
and the reading catalog updated at every new boundary:

1. Move general internal-injection vocabulary and composition laws out of the
   GCH statement/assembly modules; give definable injections a general L home.
2. Keep the earliest-disagreement construction together but expose its actual
   three-result endpoint. Put chapter recaps after their substantive results.
3. Separate reusable code-alphabet and table-specification interfaces from the
   proofs that realize them. Remove SatisfactionFrame's unrelated re-exports.
4. Separate recursion's graph representation when this removes real dependencies
   from consumers of its replacement/image interface.
5. Replace hull consumers' access to nested formula environments and collapse
   implementations with explicit mathematical reading/transfer interfaces.

Do not split Coding.Model into four chapters merely because consumers use
different dictionary entries. Retain the existing reflection and axiom stages,
whose boundaries express distinct mathematical obligations and assumptions.
Preserve opacity around large formulas; exposing their reductions is not an
acceptable price for a cosmetically smaller interface.

Acceptance requires actual consumers to use the new interfaces, no compatibility
forwarding modules, a valid parallel reading catalog, matched trilingual chapter
and subsection openings, safe whole-tree typechecking and a checked site build.
A numerical import reduction alone is not evidence of improved cohesion.

The general injection interfaces now live in `L.Cardinal`,
`L.DefinableInjection` and `L.InjectionComposition`. Six chapters no longer
import GCH.Assembly just for inclusion or composition; its four remaining
consumers use its GCH obligations or final assembly theorem.

`L.Recursion.Graph` owns the ordered-pair representation of recursive values.
`CodeAlphabet` supplies syntax constants, while `CodeDomain` and
`SatisfactionClauses` describe formulas without assuming excluded middle.
`CodeDomainAdequacy` and `SatisfactionClauseSemantics` own their semantic proofs.
The former SatisfactionFrame is replaced by `L.Coding.SatisfactionGraphSet`,
whose result is the internal graph of uniform satisfaction. Consumers import
other coding tools directly from their owners.

The catalog retains ten parallel routes. Its 120 chapters introduce the code
alphabet immediately before semantic use, and postpone code-domain soundness
and completeness until the GCH description branch. The latter proof is not an
ancestor of UniformSatisfaction. All new chapter boundaries carry matched
English, Chinese and Japanese headings and opening paragraphs. Existing code
explanations remain outside the scope of this writing phase.

The hull interface separates mathematical readings from counting: the telescope
provides least-witness decoding and uniqueness, while HullCounting places the
recovered parameters in its finite-sequence and product bounds. Collapse
membership and inverse transfer belong to SkolemHull's Carry interface.
Consumers no longer reconstruct collapse implementation fields or the nested
satisfaction-table environment. Large describing formulas remain opaque.

Validation on 2026-09-08: `make check` passes, including 79 tests and the
120-page, 707-title trilingual framework. A fresh project typecheck with Cubical
cache retained takes 212.06 seconds and reaches 1.62 GiB peak RSS; the tree has
26,587 nonblank Agda code lines. The 120-chapter DAG has 1,487 direct edges,
224 transitive-reduction edges and a longest chain of 30 modules. These costs
are acceptable for the explicit ownership and semantic interfaces established
here; reducing import count is not the acceptance criterion.

`make site` completes with library type hints enabled. All 366 localized master
pages have matching titles and identical rendered Agda code, and the site link
checker finds no broken targets. Chrome verifies the reading-guide sidebar in
three languages, mobile tab navigation and all 120 node labels in each of the
three dependency-map layouts. Obsolete generated pages for the two renamed
modules were removed before the final build. Generated logs and screenshots
remain under ignored `_build/cohesion-refactor`.
