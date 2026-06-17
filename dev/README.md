# dev

**Developer-facing** documentation: conventions and specifications for contributors, written
primarily for AI-agent contributors (humans second). **English only** (developer docs are not
translated). The top-level index is [AGENTS.md](../AGENTS.md); this folder holds
the detailed specs it points to.

## Contents

- `STYLE-i18n.md`: the full i18n **marker grammar** (`<!--en|zh|ja|/-->`) used by the
  literate-Agda masters and shared by `scripts/i18n_markers.py`, `weave-i18n.py`, and
  `render-site.py`.
- `glossary.toml`: the canonical **translation glossary data**, the single source
  `scripts/check-glossary.py` reads (via `tomllib`). Add a `[[term]]` entry when you confirm a new
  load-bearing term.
- `GLOSSARY.md`: the human-readable **explanation** of the glossary, what the two checks do and how
  to maintain `glossary.toml`.

See [scripts/README.md](../scripts/README.md) for the tooling that consumes these.
