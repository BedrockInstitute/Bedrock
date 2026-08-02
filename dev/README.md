# dev

**Developer-facing** documentation: conventions and specifications for contributors, written
primarily for AI-agent contributors (humans second). **English only** (developer docs are not
translated). The top-level index is [AGENTS.md](../AGENTS.md); this folder holds
the detailed specs it points to.

## Contents

- `PLAN.md`: the **construction plan** for the current milestone (porting L ⊨ ZFC from
  `fol-reification`): ratified decisions, target skeleton, rename ledger, the route
  tree of goal codes (`[L0]` to `[L5]`), binding build constraints, and the live
  MASTER status table. Read it before touching `src/`; work carries a goal code.
- `literature/`: the **rud-route literature collection** (`[L3.30-L1]`): classified,
  citation-carrying notes on rudimentary functions, the J-hierarchy, the Devlin
  errata, and the formalization landscape, plus the bibliography, the owner's
  exploration note, and (once landed) the orthodox-form digest.
- `LESSONS.md`: the **measured lesson book**: every performance law, conversion rule,
  termination trap, inference trap, and design doctrine with its numbers and
  provenance, the living home for the substance that PLAN rows used to carry.
- `STYLE-agda.md`: the **Agda code and literate-chapter style** rules for `src/` masters:
  OPTIONS and assumption policy, naming, the layer-marking system, performance-idiom
  annotations, and the chapter template. Inherits the source project's finalized spec.
- `STYLE-i18n.md`: the full i18n **marker grammar** (`<!--en|zh|ja|/-->`) used by the
  literate-Agda masters and shared by `scripts/i18n_markers.py`, `weave-i18n.py`, and
  `render-site.py`.
- `glossary.toml`: the canonical **translation glossary data**, the single source
  `scripts/check-glossary.py` reads (via `tomllib`). Add a `[[term]]` entry when you confirm a new
  load-bearing term.
- `GLOSSARY.md`: the human-readable **explanation** of the glossary, what the two checks do and how
  to maintain `glossary.toml`.
- `memos/`: **goal deliverables** that are documents rather than code, one file per goal code
  (`L3.0.3-subsumption-probe.md` and so on). The route tree in `PLAN.md` §6.1 says which goals
  produce one; `PLAN.md` §11 records their status. Findings that outlive the goal are promoted
  into `PLAN.md` itself, so a memo is evidence and reasoning, never the current plan.

See [scripts/README.md](../scripts/README.md) for the tooling that consumes these.
