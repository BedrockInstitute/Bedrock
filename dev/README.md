# dev

**Developer-facing** documentation: conventions and specifications for contributors, written
primarily for AI-agent contributors (humans second). **English only** (developer docs are not
translated). The top-level index is [AGENTS.md](../AGENTS.md); this folder holds
the detailed specs it points to.

## Contents

- `STYLE-i18n.md`: the full i18n **marker grammar** (`<!--en|zh|ja|/-->`) used by the
  literate-Agda masters and shared by `scripts/i18n_markers.py`, `weave-i18n.py`, and
  `render-site.py`.
- `GLOSSARY.md`: the canonical **translation glossary**. It is both the human-readable
  reference and the **data source** for `scripts/check-glossary.py`, so there is no second copy
  to drift. Add a row when you confirm a new load-bearing term.

See [scripts/README.md](../scripts/README.md) for the tooling that consumes these.
