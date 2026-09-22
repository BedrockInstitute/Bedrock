# Choice refinement, 2026-09-22

This pass applies the first three chapters' reviewed preferences to `Base.Choice`.
It preserves the chapter/subsection outline and all mathematical assumptions and
conclusions. The initial prose pass preserved the 90 Agda code lines exactly.
The subsequent owner-approved refinement replaces the two local path/proof maps
with the library-backed equivalence `quotientPath≃P`, and uses `cong` explicitly.

## Preferences recovered from Git

The entries below distinguish evidence in committed changes from the editorial
application made in this pass. The large figure commits consolidate many smaller
owner reviews; their final conventions are recorded in STYLE-i18n and the recipes.

| Commit | Evidence in the first three chapters | Application to Choice |
| --- | --- | --- |
| `46fa5b5c` | Foundational vocabulary is centralized; prose explains the mathematical role of the following code. | Introduce the three existence statements before `SetChoice`; link actual names and remove the import inventory. |
| `054ca97b` | Parallel EN/ZH/JA explanations, Japanese plain style, and named mathematical statements replace informal proof commentary. | Rewrite all three routes together; label the definition, descent lemma and theorem; close outer proofs with `∎`. |
| `ba882397` | The classical classifier separates its motivating question, maps, laws and final use of LEM. Explanation is placed where its object first becomes useful. | Separate quotient construction, representatives, the two implications and truncation elimination. Explain the sole use of choice where `merePicker` is applied. |
| `23c0a41f` | Boolean labels are distinguished from propositions; the two directions and proof boundaries are explicit. | Distinguish a boolean, its quotient class, the path certifying a representative, and the proposition being decided. |
| `f15b9c5b` | Shared diagrams, outside captions, optional constructions, margin notes, code/math notation, and narrow fibre terminology become checked conventions. | Use three diagrams with shared styles; put relation-law checks in a default-open optional block; reserve fibre for `Pick x`, the fibre of the quotient map. |
| `7b5b8de6` | Fibre prose is shortened once the diagram carries the geometry; only animated objects pulse, and navigation is shared. | Captions state the takeaway instead of narrating every mark. These proof diagrams are static; they require no pulse or new navigation code. |

## Mathematical corrections

- General family values are called `B x`, not fibres. `Pick x` is literally the
  dependent pair defining the fibre of `[_] : Bool → Glued`.
- Choice retains its truncated conclusion. The original statements that an
  actual function is supplied, or that no truncation ever yields an element,
  were too strong. Explain the `rec₁` proposition-valued goal locally instead.
- The definition requires `isSet X`, not `isSet (B x)`. The margin note and reader
  term explicitly preserve this distinction. Do not identify the exact local
  signature with a textbook formulation that additionally restricts the values.
- The quotient is formed without deciding P. The two conditional pictures do
  not invoke excluded middle. Both directions use `quotientPath≃P`, obtained from
  `isEquivRel→effectiveIso` and `isoToEquiv`. This requires the checked equivalence
  laws; the library supplies both round-trip laws. The first figure follows the
  equivalence definition, and both figures abbreviate that equivalence as e.
- Reflexivity uses `tt*`, not the wildcard `_`. Transitivity's diagonal cases
  return `tt*`; only off-diagonal cases reuse a premise.
- The first certificate in `agree→P` must be reversed. The path-chain diagram
  shows that reversal explicitly. The other direction maps the path with the
  ordinary function taking the first component of `g`.
- The recap names `V.Model` and distinguishes its ambient choice assumption from
  the later internal choice theorem for L, which assumes only LEM.

Checked primary definitions: installed Cubical 0.9 SetQuotients Base/Properties
(`eq/`, `squash/`, `[]surjective`, `effective`, `isEquivRel→effectiveIso`), Nullary Properties (`mapDec`,
`isPropDec`), HLevels (`isOfHLevelLift`), PropositionalTruncation Properties (`rec`,
`map`); actual consumers `V.Model.V⊨ZFC` and `L.Model.L⊨ZFC`.

Existing translations for set-level choice and set quotient are promoted to
reader terms, with evidence and exact scope centralized in `glossary.toml`.
The [HoTT Book](https://homotopytypetheory.org/book/), section 3.8, motivates the
truncated formulation; the source of truth for this chapter's precise hypothesis
remains the local Agda signature.

## Reused recipes

| Recipe | Use in Choice |
| --- | --- |
| `prose.parallel`, `prose.term`, `code.reference` | All routes; formal introductions of set quotient and set-level choice |
| `prose.statement`, `prose.proof` | `SetChoice`, `lowerSetChoice`, `choice→lem` |
| `code.display-note` | `lower (f (lift x)) : B x` with an attached evaluation explanation |
| `prose.margin-note` | The h-set restriction concerns the index type |
| `prose.optional` | Default-open verification of the quotient relation |
| `prose.comparison-table` | Three existence statements, lifted data, decision cases |
| `figure.frame`, `figure.compare`, `figure.space`, `figure.paths` | `fig-choice-gluing`: conditional quotient geometries |
| `figure.compact-map`, `figure.path-map`, `figure.paths` | `fig-choice-agreement`: compose certificates versus map a path |
| `figure.factorization-math` | `fig-choice-truncation`: reuse the Prelude's truncation factorization |

No chapter-local CSS, JavaScript, scroll containers or decorative nesting is added.

## Initial prose-pass validation

- `make -o _build/bin/bedrock-agda check AGDA_DIR=/Users/alsg/.agda`: exit 0;
  complete Milestones typecheck, source gates, 222 Python tests and Agda lint tests.
  The existing pinned compiler was used without rebuilding it.
- Compared the initial refined concatenated Agda fences against `HEAD`: all 90 lines are
  identical. That version also typechecked through the Agda HTML backend.
- Scoped literary-exposition, prose, glossary, chapter-framework and all-chapter
  diagram checks: exit 0. All 23 fences have at most five nonempty code lines.
- Rendered EN/ZH/JA with KaTeX. At 390px, all three figures and all three tables
  fit their containers, the page has no horizontal overflow, and there are no
  KaTeX errors. Inspected the path labels and quotient geometry visually.
- The optional block starts open, closes by click and reopens with Enter.
  Temporary viewport overrides are reset after previewing.

- All three desktop routes at 1260px also fit without figure overflow or KaTeX
  errors. The final chapter trace was regenerated: 180 application nodes and
  122 binding/name nodes, preserving the code hover and AST interactions.

## Adopted equivalence interface

The owner accepted the evaluated replacement of `glue` and `unglue` by
`quotientPath≃P`. Its definition uses the library's `isEquivRel→effectiveIso`
and `isoToEquiv`; `agree→P` uses `equivFun`, and `P→agree` uses `invEq` followed
by `cong`. The assumptions and conclusions of `SetChoice`, `lowerSetChoice`
and `choice→lem` remain unchanged.

The EN/ZH/JA exposition now introduces the path characterization as one type
equivalence. The first figure follows that definition, displays the equivalence,
and labels its path e⁻¹(p). The agreement figure uses the same notation and its
caption explains which direction of e each argument uses. Existing path colors,
white endpoints, function-arrow roles and caption placement are retained.

The revised chapter typechecks through the HTML backend. Its refreshed trace
contains 177 application nodes and 119 binding/name nodes. Prose, terminology,
chapter framework, literary exposition and diagram gates pass. All 24 code
fences have at most five nonempty lines. Browser inspection confirms no KaTeX
errors or figure/page overflow in the three 390px routes and the 1260px Chinese
route; the temporary viewport override was reset.

After adopting the equivalence, the complete `make check` gate passed again
(exit 0), including the Milestones closure, all source gates, 222 Python tests
and Agda lint tests. No theorem gained a hypothesis or changed its conclusion.
