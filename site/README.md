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

The site front-end is **derived from [the 1lab](https://1lab.dev) and is AGPL-3.0**, which is
distinct from the project's CC BY-NC-SA content. Keep the two separated and credited; the
attributions are in [NOTICE](../NOTICE). Per AGPL section 13, this public repository is the
corresponding source of the deployed site.
