# dev

**Developer-facing** documentation: conventions and specifications for contributors, written
primarily for AI-agent contributors (humans second). **English only** (developer docs are not
translated). The top-level index is [AGENTS.md](../AGENTS.md); this folder holds
the detailed specs it points to.

## Contents

- `PLAN.md`: the **construction registry** for the campaign (the two-tower bridge,
  both trophies): section 0 for where the work stands, the `DD` rulings, the
  goal-coding rules, DD8's single best-effort projection that named its basis,
  and the live MASTER status table with the `LJ` task index. Pointers to the
  archived planning apparatus (target skeleton, route tree, source survey, build
  constraints, process tensions, risks, simplification register) in `dev/memos/`.
  Read it before touching `src/`; work carries a goal code.
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
  literate-Agda masters and shared by `scripts/site/i18n_markers.py`, `weave-i18n.py`, and
  `render-site.py`.
- `glossary.toml`: the canonical **translation glossary data**, the single source
  `scripts/gate/check-glossary.py` reads (via `tomllib`). Add a `[[term]]` entry when you confirm a new
  load-bearing term.
- `GLOSSARY.md`: the human-readable **explanation** of the glossary, what the two checks do and how
  to maintain `glossary.toml`.
- `ledger.toml`: the canonical **size ledger data**, the single source `scripts/measure/ledger.py` reads
  (via `tomllib`): the booked retirement set and the remaining-work rows with their bands,
  classes and provenance. It contains **no standing figure**; standing is measured from the tree,
  never written down.
- (`LEDGER.md` and `MAINTENANCE.md` were deleted 2026-08-06 by `[T115]`'s audit: no brief ever pointed an agent at either, and their agent-facing content moved into `ledger.toml`'s header comment and `check-dev-docs.py`'s docstring. The owner reads `scripts/measure/ledger.py --brief`.) The caliber convention, what a derived row is,
  and the rule for keeping it current when a chapter lands or a gate returns.
- `memos/`: **goal deliverables** that are documents rather than code, one file per goal code
  (`L3.0.3-subsumption-probe.md` and so on), plus the archived planning sections cut from
  `PLAN.md` by `[L3.32-T113]` (the target skeleton, route tree, source survey, build
  constraints, process tensions, risks and simplification register; each carries a status
  header and a pointer back). `PLAN.md` §11 records the status of the goals. Findings that
  outlive a goal are promoted into `PLAN.md` itself, so a memo is evidence and reasoning,
  never the current plan.

See [scripts/README.md](../scripts/README.md) for the tooling that consumes these.
