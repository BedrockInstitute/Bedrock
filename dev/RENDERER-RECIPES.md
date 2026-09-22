# Renderer style recipes

This is the maintained recipe index for textbook authors and the renderer. The initial
inventory follows `Base.Prelude`, `Base.Impredicativity`, then `Base.Classical` in reading
order. "First use" means the first occurrence in those three chapters, not the date a
style was introduced. Refer to a recipe by its stable ID when requesting a new passage
or figure. Reuse the existing classes; do not copy their CSS into chapter markup.

## Prose and code

| Recipe ID | Use and canonical source form | First use | Implementation / checks |
| --- | --- | --- | --- |
| `prose.parallel` | Three language blocks, followed by shared Agda fences; matching chapter/subsection structure | [Prelude](../src/Base/Prelude.lagda.md), opening and "Traceable vocabulary" | `i18n_markers.py`, chapter-framework and literary-exposition gates |
| `prose.term` | First introduction `[term]{.term-intro #id}`; explicit later reference `[term]{.term-ref #id}` | [Prelude](../src/Base/Prelude.lagda.md), `object-theory` in the opening | `glossary.toml`, glossary renderer and gate; never duplicate term metadata locally |
| `code.reference` | Inline `` `name`{.Agda} `` links to a checked Agda name | [Prelude](../src/Base/Prelude.lagda.md), `Type ℓ` under "Universe levels" | `render-site.py` resolves references; formal code remains in Agda fences |
| `code.display` | One centered `<div>` containing one `<code>` for reader-facing notation; see the template below | [Prelude](../src/Base/Prelude.lagda.md), `Type ℓ : Type (ℓ-suc ℓ)` | `bedrock.css`, `bedrock.js`, one-line rule in `lint-prose.py` |
| `code.display-note` | `code.display` with localized `data-note="..."` explaining the notation | [Prelude](../src/Base/Prelude.lagda.md), the same universe-level expression | Desktop margin note; narrow-screen tap/focus note; keep the annotation in its language block |
| `prose.margin-note` | `span.prose-annotation-target` followed by `aside.prose-annotation-note` | [Prelude](../src/Base/Prelude.lagda.md), why types cannot generally be moved downward after `Lift` | `bedrock.css` and `bedrock.js`; use for a brief attached qualification |
| `prose.disclosure` | `details.prose-disclosure` with a localized `summary` | [Prelude](../src/Base/Prelude.lagda.md), compiler-option explanation | Ancillary interface detail only; localized prefix checked by `lint-prose.py` |
| `prose.optional` | Default-open, collapsible `details.optional-reading` with a localized `summary.optional-reading-title`; see template below | [Impredicativity](../src/Base/Impredicativity.lagda.md), `coded-truth-construction-title` | Small inset, muted background, left rule; title and outer-proof QED checked by `lint-prose.py`; structural wrapper recognized by literary gate |
| `prose.statement` | `**Definition** (`name`{.Agda}) Text`; also Construction, Fact, Lemma, Theorem, Corollary with localized labels | [Impredicativity](../src/Base/Impredicativity.lagda.md), `hasSize` | `lint-prose.py`; the label and declaration form one sentence, without a period after the label |
| `prose.proof` | `**Proof** Text`, alternating explanation and code, with standalone `∎` after the complete outer proof | [Impredicativity](../src/Base/Impredicativity.lagda.md), `ΩResizing→Resizing`; further examples in [Classical](../src/Base/Classical.lagda.md), `isPropLEM` and `lowerLEM` | `lint-prose.py`; helpers within an optional block do not each need a QED |

### Centered code display

```html
<div class="single-line-code"><code>expression</code></div>
```

### Default-open optional construction

```html
<details open class="optional-reading" aria-labelledby="unique-title-id">
<!--en-->
<summary class="optional-reading-title" id="unique-title-id">Optional: construction of …</summary>

To construct the representative used above, …
<!--zh-->
<summary class="optional-reading-title" id="unique-title-id">选读：……的构造</summary>

为构造上面使用的代表，……
<!--ja-->
<summary class="optional-reading-title" id="unique-title-id">発展：……の構成</summary>

上で用いた代表を構成するために、……
<!--/-->

<!-- Shared code and figures, interleaved with further language groups. -->
</details>
```

The title ID is unique in the rendered page; its three source occurrences are language
alternatives. The `open` attribute is required: readers see the construction initially
and can collapse or expand it by activating its summary. Use the native disclosure
control, without a separate play/toggle button or persisted collapsed state. Keep normal text size and
line spacing. On small screens reduce the inset rather than compressing the content.
If this block completes an enclosing proof, put that proof's `∎` after `</details>`.

## Figures

All figure recipes compose `book-diagram`, a stable `fig-*` ID, `aria-describedby`,
and a direct trilingual `figcaption`. Place the explanation and hypotheses before
the figure and use the caption for its takeaway. Figures have no outer decorative
frame by default and no internal scrolling. Use `figure.frame` when the components
need an explicit overall boundary; the caption always stays outside that boundary.
The first common shell is `fig-pi-sigma` in Prelude.

| Recipe ID | Reusable structure | First use | Reuse guidance |
| --- | --- | --- | --- |
| `figure.frame` | One direct `div.diagram-framed` for the diagram content, followed by a sibling `figcaption` outside the frame | [Prelude](../src/Base/Prelude.lagda.md), `fig-proposition-and-proof` | Groups formulas, spaces and labels; never frame the overall description; the diagram gate enforces this structure |
| `figure.compare` | `type-comparison-panels` with `diagram-panel` | [Prelude](../src/Base/Prelude.lagda.md), `fig-pi-sigma` | Parallel alternatives; align corresponding rows and center their contents |
| `figure.space` | HTML `diagram-space` or SVG `diagram-space-shape` | [Prelude](../src/Base/Prelude.lagda.md), `fig-type-transport` | A box denotes a mathematical type space; place elements inside and the type label above them |
| `figure.paths` | `path-stage`, SVG `viewBox`, positioned `path-label` | [Prelude](../src/Base/Prelude.lagda.md), `fig-path-operations` | Ordinary paths: blue, no arrowheads, white endpoints with blue outlines; `refl` is a point |
| `figure.path-map` | `diagram-panel.path-single` with one path stage | [Prelude](../src/Base/Prelude.lagda.md), `fig-path-cong` | One function's action on paths; use `diagram-map-line` / `diagram-map-tip` for function arrows |
| `figure.transport` | `transport-scene`: two type spaces above two base elements, joined by a path below | [Prelude](../src/Base/Prelude.lagda.md), `fig-type-transport`; reused by `fig-path-transport` | Keep transport and subst visually parallel; dashed guides express correspondence, not functions |
| `figure.factorization` | Three SVG type-space boxes, functions between them, and related terms inside the target box | [Prelude](../src/Base/Prelude.lagda.md), `fig-subst-factorization` | Reuse the composition, role classes and alignment; choose geometry for the actual formulas |
| `figure.pointwise` | `funext-scene`: sampled paths and a result space | [Prelude](../src/Base/Prelude.lagda.md), `fig-path-funext` | A family of pointwise paths gives a path of functions |
| `figure.implications` | `hlevel-panels`, internal assumptions, examples and definitions, with `hlevel-link` connectors | [Prelude](../src/Base/Prelude.lagda.md), `fig-hlevel-distinction` | Align corresponding panel regions; logical implications use implication symbols |
| `figure.universe-copy` | `level-scene`, two type spaces and a separate properties row | [Prelude](../src/Base/Prelude.lagda.md), `fig-universe-homotopy` | Distinguish movement of universe level from preservation of properties |
| `figure.factorization-math` | A single panel containing a KaTeX commutative diagram | [Prelude](../src/Base/Prelude.lagda.md), `fig-truncation-rec` | Compact equations/functions; never override descendant KaTeX SVG dimensions |
| `figure.resizing` | `resizing-comparison` / `resizing-case`: title, note, assumption, centered scene, conclusion | [Impredicativity](../src/Base/Impredicativity.lagda.md), `fig-resizing-comparison` | Scene rows share a vertical center; conclusion formulas align; narrow layouts stack panels |
| `figure.path-space` | `coded-truth-proof-scene`: two proof spaces and the ambient type, with `diagram-path-space` lens | [Impredicativity](../src/Base/Impredicativity.lagda.md), `fig-coded-truth` | Align proof points; put endpoint labels next to endpoints; the shaded family is schematic, not a literal subspace of Ω |
| `figure.roundtrips` | `type-comparison-panels classical-roundtrips`, parallel path stages | [Classical](../src/Base/Classical.lagda.md), `fig-classical-roundtrips` | Two inverse laws displayed in matching geometry, with paths for equality |
| `figure.compact-map` | `diagram-compact-stage` inside the standard frame or comparison columns | [Prelude](../src/Base/Prelude.lagda.md), `fig-truncation-witnesses` | Vertically aligned source/target spaces, bounded width, shared label size; reused in `fig-fiber-contraction` and `fig-lower-lem` |
| `figure.indexed-slots` | `diagram-indexed`, a three-column `vector-slots` strip, and aligned index/result points | [Prelude](../src/Base/Prelude.lagda.md), `fig-fin-vector-lookup` | The strip represents entries of one vector, not a type space; arrows denote `lookup` with that vector fixed; numerical index labels must be explained in prose |
| `interaction.path-space` | `coded-truth-trigger`, moving region/path copies and target point classes | [Impredicativity](../src/Base/Impredicativity.lagda.md), `fig-coded-truth` | Click/Enter/Space unfolds a path family while whole paths shrink to points; gentle fill pulse, no play button; reduced-motion users retain the static explanation |

Appearance is centralized in `site/static/bedrock.css`; animation is in
`site/static/bedrock.js`. Shared SVG roles and allowed geometry are enforced by
`scripts/site/diagram_style.py`, called by the renderer and `check-diagrams.py`.
For a comparison grouped by a single outer frame, see Prelude's
`fig-proposition-and-proof`: it composes `figure.compare`, `figure.space` and
`figure.paths`, enclosed by `figure.frame`. Each column places the packaged proposition above its underlying
type space and the certificate's type below it. Empty and inhabited examples share
the same geometry, so absence of proof remains visible. The caption distinguishes
the certificate function from its path-valued application; do not explain this
distinction by whether a label is inside or outside a box.
The path-space animation currently targets `#fig-coded-truth`: adapting it to a second
figure requires generalizing the initializer; copying the ID is not a reusable API.

## Maintenance

1. Before adding a style, choose an existing recipe ID and cite its first-use figure or
   passage. Geometry and mathematical labels remain specific to each construction.
2. Add a recipe here only when the existing set cannot express the intended reading
   structure. Record its stable ID, source form, exact first-use locator, implementation
   and checks. Update this table whenever an example moves or a class is renamed.
3. Keep colors, borders, padding, gaps and responsive behavior in shared CSS. Inline
   figure styles may specify only `left`, `top` and `aspect-ratio`. Do not nest decorative
   panels or use arrowheads for mere association. Higher paths may use filled regions.
4. Check trilingual weaving, relevant prose gates and diagram lint; preview desktop and
   narrow screens. A change to nesting or parsing also needs focused gate tests.
   Keep formal Agda tokens unchanged for a styling-only change.
5. This index records supported recipes, not every incidental selector. The normative
   constraints remain [STYLE-i18n.md](STYLE-i18n.md) and the gate implementations.
