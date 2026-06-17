# site

The static-site **front-end assets** consumed by
[scripts/render-site.py](../scripts/render-site.py). These are committed source; the rendered
site they produce is generated into `_build/site/` (git-ignored). English developer doc; see
[AGENTS.md](../AGENTS.md).

## Contents

- `template.html`: the page shell. The renderer fills `%%...%%` slots (content, navigation, the
  external-library banner, cache-busting `?v=` asset versions, and so on).
- `static/`: assets copied verbatim to the site root.
  - `bedrock.css`: styles (the palette and Agda token colours are **adapted from the 1lab**).
  - `bedrock.js`: theme toggle, KaTeX, type-on-hover, fuzzy search, language switch.
  - `favicon.svg`.
  - `fonts/`: self-hosted woff2 (EB Garamond, Inria Sans, JuliaMono); no runtime font CDN.
- `vendor/1lab/`: **vendored upstream 1lab assets** kept under their own license, with the
  upstream font and icon license texts under `vendor/1lab/static/licenses/`.

## Licensing

All first-party code here (`template.html`, `static/bedrock.css`, `static/bedrock.js`, and the
renderer) is **AGPL-3.0-only**, the repository's default; that folds in the front-end assets
adapted from [the 1lab](https://1lab.dev) and the vendored 1lab tree under `vendor/1lab/` (also
AGPL-3.0). The self-hosted fonts under `static/fonts/` are **OFL-1.1**, and the brand mark
`static/favicon.svg` is **CC BY-NC-SA 4.0** (the project content license). Per-file terms are
declared in [`REUSE.toml`](../REUSE.toml) and verified by `reuse lint`; attributions and the
AGPL section 13 source statement are in [NOTICE](../NOTICE).
