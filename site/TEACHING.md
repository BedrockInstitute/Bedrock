# Teaching architecture

Preserve the completed safe ZFC and GCH proofs. Optimize coherent learning units,
explicit prerequisites and reusable mathematical interfaces. Modest code/build
cost increases are acceptable when they buy a specific improvement in those
properties; chapter count and source line count are not objectives.

## Reading contract

- Origin is an explicitly labelled preview of the final theorem statements.
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

## Mathematical ownership

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

## Change acceptance

- Each definition has one substantive home and real consumers import it there.
  Do not introduce cycles or compatibility-only modules.
- The catalog covers every master exactly once. The Origin preview is the
  explicit prerequisite-order exception, not an exception for ordinary chapters.
- All editions agree on module paths, mathematical assumptions, titles and
  navigation. Keep proof code outside translation groups.
- Run `make check`, the Origin closure gate and site/link checks after structural
  changes. Measure build time and memory under comparable cache conditions;
  these are costs to report, not proof-compression targets.

## Parallel reading

A catalog order is one topological ordering, not a mandatory reading schedule.
Measure readiness using actual imports and explicit join conditions. Chapter
distance is not a graph distance or an estimate of learning time. Within a route,
review first substantive applications separately from helper lemmas and endpoints.

The configured catalog supplies stable route IDs, localized titles, descriptions,
membership and human-review status. Dependencies come from source imports, not a
second handwritten graph. Shared chapters can belong to several routes. Readers
may pursue a topic when its prerequisites are ready without finishing unrelated
branches. A completion mark is a reader's local self-report, not a mastery score.

## Exposition

Preserve the chapter and subsection structure unless a change in mathematical
question or abstraction level justifies a new boundary. Explain purpose,
dependent types and proof steps through a connected argument; do not narrate
imports or file order. Formal code follows its explanation.

Maintain parallel English, Chinese and Japanese titles and exposition. Use
[the language style](STYLE-i18n.md), [Agda conventions](STYLE-agda.md), and
[the glossary](GLOSSARY.md). Translate terminology from the central decisions,
not independent local guesses. Untranslated English fallback is a presentation
mechanism, not evidence that a chapter's literary pass is complete.

Use the literary-exposition report to recompute current progress rather than
copying dated module counts. Record temporary pass results under `_build/` or
in the task handoff, not as a growing historical ledger in this specification.
