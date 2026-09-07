# Teaching architecture

Preserve the completed safe ZFC and GCH proofs. Optimize coherent learning units,
explicit prerequisites and reusable mathematical interfaces. Modest code/build
cost increases are acceptable when they buy a specific improvement in those
properties; chapter count and source line count are not objectives.

## Reading contract

- Landmarks is an explicitly labelled preview of the final theorem statements.
- All other chapters introduce their direct prerequisites before using them.
- Each chapter names its mathematical question, required concepts and endpoint.
- The reading catalog groups chapters by a proof's learning stages. The namespace
  tree continues to group by subject; both views use the same actual modules.
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
   and readers; isolate the closed code domain in CodeDomain; let Clauses start
   with the actual satisfaction relation. Preserve the existing transparent
   proofs, rather than introducing an unnecessary new abstraction framework.
   Generic pair projections belong to Quantification; CodeDomain does not
   re-export its prerequisites as a compatibility entry point.
5. **The whole reading catalog.** Replace the oversized constructibility part and
   obsolete trailing tools section with coherent stages. Fix the 36 measured
   prerequisite inversions, update all chapter descriptions and distinguish the
   completed mathematical results from future research aims.

## Boundaries retained after review

- **Choice.Finite** keeps finite enumeration, comparison and the finite-stage
  order together: these are successive ingredients of one canonical-order
  construction. The generic natural-number well-order is an example in
  WellOrder.Base, shared by Finite and SquareLaw. This removes the accidental
  dependency from ordinal square-law tools to the Choice construction without
  adding a tiny standalone chapter.
- **Coding.Sequence** keeps sequence coding with its approximation interface.
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
- **Bound, Descent and Injection** remain narrow, named mathematical interfaces,
  rather than being absorbed into whichever application first imports them.

These choices favor coherent lessons over maximizing either splits or merges.

## Acceptance

- Each moved definition has exactly one substantive home and all real consumers
  import it there; no accidental cycles or compatibility shells.
- The catalog contains every master exactly once, with no prerequisite inversion
  except the explicitly marked Landmarks preview. The reading-order gate checks
  fenced imports and runs with `make check`; its tests cover the preview, backward
  prerequisites, exact coverage and prose that resembles imports.
- English and Chinese introductions, catalog descriptions, symbols and rendered
  navigation agree with the final module paths and order.
- `make check` passes; the site build and its internal links are checked after
  moves because Agda alone does not validate reader navigation.
- Compare fresh project-interface Landmarks time and peak RSS with the last
  verified 201.38 s / 1,865,891,840-byte observation. Keep Cubical interfaces and
  the same memory guard; record costs honestly without treating one run as an
  average. README retains only the compact current figures requested by the user.

## Dependency map and prose review

The graph review found one accidental subject dependency: SquareLaw used
Choice.Finite only for the natural-number well-order. That example now lives
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
reduction, the omitted hub edges and Landmarks' position as a dependency endpoint.

Introductions, closing summaries and order references were reviewed across all
118 masters. Obsolete part numbers, retired-design narratives and false endpoint
or consumer claims were replaced with the current modules and constructions.
The prose audits preserve fenced code; the only additional proof-code change is
the relocation and relation-level generalization of the natural-number order.

## Verification (2026-09-07)

The final tree has 118 masters and 117 reading chapters in ten stages, including
the opening preview. Both catalog languages cover all chapters. All 118 masters
retain `--safe`; the two Landmarks endpoint statements and their code are unchanged.
The Landmarks dependency closure reaches every master except Everything.

`make check` passed with 42 tests. All masters, including every new chapter,
also passed explicit Agda/prose lint. The site built successfully into fresh
`_build/teaching-html` and `_build/teaching-site` directories. Its 234 bilingual
chapter pages have the exact catalog previous/next order; the link checker found
zero broken links among 743,855 relative links. Type-hint extraction now respects
`HTML_DIR`, so renamed chapters and their hints use the same generated module set.

The source contains 26,458 nonblank Agda lines, 150 more than before (+0.57%).
This pays for explicit module boundaries and direct consumer imports; it does not
change the syntax constructors, mathematical statements or classical assumptions.

Fresh project-interface typechecking of Landmarks passed in 206.23 s with
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
