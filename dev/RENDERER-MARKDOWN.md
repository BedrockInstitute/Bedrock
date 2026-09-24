# Textbook Markdown, version 1

This is the reusable renderer's input contract, not the Bedrock mathematical
style guide. A document is UTF-8 text. Its filename need not end in `.lagda.md`.
The core accepts a string and never discovers a repository, catalog or glossary:

```python
from document_renderer import MarkdownDocument
result = MarkdownDocument(text).render('en')
html, outline, markdown = result.body, result.toc, result.mirror
```

Put `scripts/site` on the Python import path. Python 3.11 or newer is required;
the core and static site builder do not invoke Agda. The current language set is
English (`en`), Chinese (`zh`) and Japanese (`ja`), not an arbitrary locale plugin
system. `examples/renderer/plain.md` is the minimal project-free example.

## Ordinary content

Supported blocks are ATX headings, paragraphs, bullet and numbered lists, fenced
code, pipe tables and authored HTML. Supported inline forms include emphasis,
strong emphasis, backtick code, links, images and math delimiters. This is a
deliberately small textbook Markdown dialect, not a claim of full CommonMark or
GFM conformance. Keep blank lines between blocks. A heading receives a stable
document-order `sec-N` anchor. Explicit HTML IDs are retained. Prose blocks receive
`p-N` anchors for selection and machine-readable citations. Changing block order
can change generated anchors; use explicit IDs for long-lived authored links.

Raw HTML and SVG are **trusted author input**, not sanitized user-generated
content. Do not render untrusted uploads into the site's origin. Configuration
strings, generated labels and normal code text are escaped separately. Script
execution is never a prerequisite for interpreting source Markdown.

Inline Agda uses `` `term`{.Agda} ``. A single linked name can be rendered unboxed;
composite expressions retain a code surface. ` ```agda ` fences retain the entire
code stream. Without compiler input they receive lexical syntax help, but no
invented definition links, expression ranges or types. Other fences are ordinary
escaped code. Math is retained for the shared KaTeX client.

## Language groups and fallback

Markers occupy their own lines, outside code fences:

```markdown
<!--en-->
## A heading
<!--zh-->
## 一个标题
<!--ja-->
## 見出し
<!--/-->
```

Content outside a group is shared. Within each group choose the requested
language, then English, then the first available supported language. The website
also labels English narrative fallback. A missing closing marker, stray closing
marker, unknown language marker, marker inside a fence, or Agda fence inside a
language group is a diagnostic. The pure renderer supports fallback; the default
strict textbook lint additionally requires parallel chapter outlines. A project
can explicitly set `policies.trilingual` to false for a monolingual ordinary
Markdown corpus. That does not disable marker integrity checks.

## Teaching structures

Statement labels use the established localized bold labels (Definition, Lemma,
Theorem, Construction, Corollary and their Chinese/Japanese counterparts). A
statement contains its own Agda fence and terminates with a standalone `∎` after
its last fence. The renderer places this exact Unicode rectangle at the preceding
block's lower outer edge. Adjacent independent statements must not share an end
marker. Proof labels are explanatory prose, not additional statement wrappers.
See `statement_structure.py` for the authoritative label vocabulary and
`prose_lint.py` for diagnostics. Numbered theorem allowances are explicit project
data, not an exception inferred from a chapter's name.

Use semantic `details.submodule-fold`, `summary.submodule-fold-heading` and
`div.submodule-fold-content` for a nested formal module. The declaration remains
its compact code surface; inner code retains its own indentation and horizontal
scroll area. Default-open and nested folds are supported. A private module's
`private module` must be on one code line even across fence boundaries. General
HTML details are supported too. The removed `prose.disclosure` convention is not
part of this dialect.

Annotations use the recipe's `span.prose-annotation-target` followed by
`aside.prose-annotation-note`, or the generated template form. They work in prose
and code without modifying the underlying Agda text. Tables scroll independently.
Single-line code, type popups, source popups and definition mirrors use the same
syntax-help and semantic code contract.

Figures are authored HTML/SVG with a stable `figure` ID, accessible labeling and
localized captions. A frame is a direct `div.diagram-framed` containing only the
diagram, followed by a direct, unframed sibling `figcaption`. Mathematical relation
arrows use semantic diagram colors, not link tokens. Put explanatory prose, not
an Agda fence, immediately after a figure in every language and fold. Shared
diagram classes, animation controls and static-print behavior are documented in
[RENDERER-RECIPES.md](RENDERER-RECIPES.md). These structural/accessibility rules are
reusable lint rules; the figure's mathematical meaning belongs to its author.

## Terms

The optional glossary supplies stable IDs, preferred `en`/`zh`/`ja` forms,
introduction locations, automatic matching and official-document links. Explicit
markers use the same `term-intro`/`term-ref` classes and `data-term` IDs as the
recipes. An introduction is unique and parallel across the configured textbook.
An explicit reference can look forward, in the same chapter or another chapter.
Bare automatic terminology remains subject to prerequisite/introduction order;
one explicit lookup does not exempt other bare occurrences. No glossary is read
unless supplied by the caller. Bedrock's particular translations are not built
into the renderer.

## Optional formal chapter convention

The complete site defaults to strict formal chapter setup. Set
`policies.formal_setup=false` for ordinary Markdown that has no formal module.
When enabled, a parameter-free chapter has OPTIONS/module, a title-only language
group, local prerequisite imports, then prose and external-library imports. The
title reveals the original OPTIONS and module through a source popup. Imports
become real prerequisite source popups. A parameterized module is different:
required early imports and parameter exposition may precede the declaration;
the declaration stays visible and only OPTIONS goes into the title popup.
Visible theorem imports at an overview chapter require an explicit
`visible_import_chapters` entry. There is no implicit `Origin` exception.

## Optional compiler evidence

`CodeContext` is the explicit enhanced-rendering input: semantic operations,
internal/rendered module sets, name and canonical-name indices, type records,
expression records, vocabulary/reexport index and token aspects. `SourceCorpus`
and `build_code_context` adapt a supplied compiler package for the website. The
core does not run a compiler or infer a type from displayed text.

The current Agda adapter accepts `--html --html-highlight=code` output: literate
module `.md` documents with `<pre class="Agda">` token HTML and external module
`.html` documents. Definition anchors are Agda's decimal source positions;
symbolic/Unicode anchors are retained. Source positions are **one-based Unicode
code-point offsets**, not UTF-8 byte or JavaScript UTF-16 offsets. Expression
intervals are half-open `[start,end)` and must refer to the exact source that
produced the highlighted document. Browser popup-local ranges are explicitly
rebased to code-point offsets; cloning removes source IDs, not semantic identity.

Raw type JSON maps module and definition positions to compiler-rendered types.
Raw expression JSON maps modules to compiler records containing `id`, `start`,
`end`, `source`, `type` and `kind`. The supplied extraction adapters validate source
hashes and filter compiler Dummy records before publication. The browser sidecars
contain position-to-HTML signatures plus `$names`, `$expressions` and `$syntax`
metadata. They are generated outputs, not an alternative handwritten AST format.
Use the example's `refresh_semantics.py` to reproduce a small genuine package.

Missing signatures leave code visible and links usable without a fake structural
node. Lexical syntax help remains available. Terminal universe-former signatures
and primitive sorts use precise semantic stop rules; this is not a general hover
depth limit. Modules are navigation targets, not ordinary result-typed terms.
Do not manufacture an application type for a module import.

## Links, assets and diagnostics

Ordinary prose links navigate normally, including inside a definition mirror.
Only code-definition actions enter the single-history modal. Internal module
addresses come from `BookCatalog`; external compiler modules retain flat module
filenames. Language, canonical URL and deployment prefix belong to `SiteConfig`.
Raw core documents without a rendered-module set retain ordinary links unchanged.

The website emits HTML, Markdown mirrors, type/search/route metadata, dependency
graphs, agent guides, sitemap, redirects and static assets. JavaScript modules are
published as one immutable content-hashed graph. CSS has content versions. Static
deployment needs no application server. `site_lint.py` reports source, line, rule
and message; invalid metadata/configuration raises an explicit error. It does not
silently repair mathematical content. See [SITE-CONFIG.md](SITE-CONFIG.md) for a
complete independent build and [SITE-ARCHITECTURE.md](SITE-ARCHITECTURE.md) for the
gate mapping and verification record.
