# site

The static-site **front-end assets** consumed by
[scripts/site/render-site.py](../scripts/site/render-site.py). These are committed source; the rendered
site they produce is generated into `_build/site/` (git-ignored). English developer doc; the
rule set is [AGENTS.md](../AGENTS.md).

**Read this file when your write scope names a path under `site/`.**

**The publishing pipeline runs outside `make check`:** `scripts/site/extract-types.py`,
`gen-depmap.py`, `link-check.py`, `render-site.py`, `weave-i18n.py`, `i18n_markers.py` and
`depmap-template.html`. `make html`, `make types`, `make site`, `make serve` and the two deploy
workflows run them. The one exception is `weave-i18n.py --check`, which `make lint` does run,
because a broken language marker is a defect in a master rather than in the site.

The dependency map derives its graph from fenced source imports and its learning
stages from `dev/reading-catalog.json`. Compact, learning-stage and namespace
layouts share the same nodes and edges; skeleton mode preserves reachability.
Milestones appears at the bottom as a dependency endpoint, although readers meet
its theorem statements first as a preview.

## Contents

- `template.html`: the page shell. The renderer fills `%%...%%` slots (content, navigation, the
  external-library banner, cache-busting `?v=` asset versions, the canonical link, the
  JSON-LD graph, the `window.bedrock` page config, and so on).
- `static/`: assets copied verbatim to the site root.
  - `bedrock.css`: styles (the palette and Agda token colours are **adapted from the 1lab**).
  - `bedrock.js`: theme toggle, KaTeX, type-on-hover, fuzzy search, language switch.
  - `ask-ai.js` / `ask-ai.css`: select a passage, get a handover text for an assistant.
  - `assets/`: the brand marks (`favicon.svg`, `brand.svg`, `banner.png`). `brand.svg` is a
    bottom-padded variant of the favicon mark, for inline use beside heading text in the READMEs;
    `banner.png` is the README/social hero card.
  - `fonts/`: self-hosted woff2 (EB Garamond, Inria Sans, JuliaMono); no runtime font CDN.
- `vendor/1lab/`: **vendored upstream 1lab assets** kept under their own license, with the
  upstream font and icon license texts under `vendor/1lab/static/licenses/`.

## The agent-readable layer

A reader who selects a sentence and asks an assistant about it, and the assistant that
then follows the link, need the same thing: a stable name for the block, and a cheap way
to read the rest. `make site` therefore emits, beside the pages:

- `/<lang>/<Module>.md`, a plain-Markdown twin of every chapter: the same prose, the same
  Agda in fenced blocks, and YAML front matter giving the chapter's stage, reading-order
  position, prerequisites, canonical URL and Agda master. Each page advertises its own
  twin with `<link rel="alternate" type="text/markdown">` and links it in the footer.
- `/llms.txt` (copied to `/.well-known/llms.txt`), the guide an agent reads first: what
  Bedrock is, how the site is addressed, what is fetchable, and every chapter in reading
  order. Generated from the reading catalog, so it cannot drift from the book.
- `/robots.txt` and `/sitemap.xml`, with hreflang alternates for the three editions.
- `_headers`, the Cloudflare Pages rules that serve `.md` as `text/markdown` and open the
  JSON endpoints to cross-origin fetches. GitHub Pages ignores this file; Cloudflare is
  the canonical deployment.

Anchors are the citable part. `sec-0` is a chapter's title and `sec-1`, `sec-2`, ... its
headings; `p-1`, `p-2`, ... number the prose blocks (paragraphs, list items, block quotes
and tables) in document order, the outermost block being the addressable unit. Inside a
displayed Agda block, Agda's own highlighter has already named every token by character
offset and every definition by its identifier, so code needs no scheme of Bedrock's.
`scripts/tests/test_agent_layer.py` pins all of this.

## Where a chapter lives

**One rule, in one place.** [scripts/site/reading_routes.py](../scripts/site/reading_routes.py)
decides a chapter's address and puts it on the catalog node as `page` and `anchor`. Every
consumer links through those two fields and none of them builds a filename from a module
name: the renderer (`chapter_href`), the reading-route explorer, the dependency map, the
search index, the glossary, the sitemap, the Markdown twins and llms.txt.

The rule exists because a preview chapter has **no page of its own**. The reading guide
embeds its entire body, so `Milestones` is read at `index.html#milestones` and no
`Milestones.html` is written. Because the guide embeds the whole chapter, every anchor
the chapter defines still resolves there, which is why an explicit anchor beats the
panel's own: `chapter_href("Milestones", "#1354")` is `index.html#1354`.

A module with no catalog entry is a Cubical library page rendered for reference, not a
chapter, and keeps its own filename.

The ask-an-assistant dialog is built entirely in the browser from `window.bedrock` and
the selection. It sends nothing anywhere: it produces text the reader copies into
whatever assistant they already use. Its three language editions live in `ask-ai.js`,
because the reader reads the handover before pasting it.

## Licensing

All first-party code here (`template.html`, `static/bedrock.css`, `static/bedrock.js`,
`static/ask-ai.js`, `static/ask-ai.css`, and the
renderer) is **AGPL-3.0-only**, the repository's default; that folds in the front-end assets
adapted from [the 1lab](https://1lab.dev) and the vendored 1lab tree under `vendor/1lab/` (also
AGPL-3.0). The self-hosted fonts under `static/fonts/` are **OFL-1.1**, and the brand assets
under `static/assets/` are **CC BY-NC-SA 4.0** (the project content
license). Per-file terms are
declared in [`REUSE.toml`](../REUSE.toml) and verified by `reuse lint`; attributions and the
AGPL section 13 source statement are in [NOTICE](../NOTICE).
