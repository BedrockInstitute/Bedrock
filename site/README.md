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
stages from the bilingual Everything catalog. Compact, learning-stage and namespace
layouts share the same nodes and edges; skeleton mode preserves reachability.
Landmarks appears at the bottom as a dependency endpoint, although readers meet
its theorem statements first as a preview.

## Contents

- `template.html`: the page shell. The renderer fills `%%...%%` slots (content, navigation, the
  external-library banner, cache-busting `?v=` asset versions, and so on).
- `static/`: assets copied verbatim to the site root.
  - `bedrock.css`: styles (the palette and Agda token colours are **adapted from the 1lab**).
  - `bedrock.js`: theme toggle, KaTeX, type-on-hover, fuzzy search, language switch.
  - `assets/`: the brand marks (`favicon.svg`, `brand.svg`, `banner.png`). `brand.svg` is a
    bottom-padded variant of the favicon mark, for inline use beside heading text in the READMEs;
    `banner.png` is the README/social hero card.
  - `fonts/`: self-hosted woff2 (EB Garamond, Inria Sans, JuliaMono); no runtime font CDN.
- `vendor/1lab/`: **vendored upstream 1lab assets** kept under their own license, with the
  upstream font and icon license texts under `vendor/1lab/static/licenses/`.

## Licensing

All first-party code here (`template.html`, `static/bedrock.css`, `static/bedrock.js`, and the
renderer) is **AGPL-3.0-only**, the repository's default; that folds in the front-end assets
adapted from [the 1lab](https://1lab.dev) and the vendored 1lab tree under `vendor/1lab/` (also
AGPL-3.0). The self-hosted fonts under `static/fonts/` are **OFL-1.1**, and the brand assets
under `static/assets/` are **CC BY-NC-SA 4.0** (the project content
license). Per-file terms are
declared in [`REUSE.toml`](../REUSE.toml) and verified by `reuse lint`; attributions and the
AGPL section 13 source statement are in [NOTICE](../NOTICE).
