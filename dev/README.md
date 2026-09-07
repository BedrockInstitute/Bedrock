# dev

**Developer-facing** specifications: how the code and the prose must be written, and the
term data the glossary checker reads. English only, never translated; user-facing material
is trilingual and lives in [docs/](../docs/). The rule set is [AGENTS.md](../AGENTS.md).

## Contents

- `REFACTOR.md`: the current proof-size goal, line-count baseline, batch plan,
  and comparable typechecking measurements.
- `STYLE-agda.md`: the law for Agda inside the ```agda fences, enforced by
  `scripts/gate/lint-agda.py`. The OPTIONS pragma, no bare `open import`, no unused import,
  nothing that breaks `--safe`, and the symbol table `src/README.md` carries.
- `STYLE-i18n.md`: the marker convention for literate multilingual masters, enforced by
  `scripts/site/weave-i18n.py --check`. Prose outside every `<!--lang-->` group is shared
  and is copied to every language verbatim.
- `GLOSSARY.md`: how a term entry is proposed, reviewed and landed.
- `glossary.toml`: the term data itself, one entry per term with its Chinese and Japanese
  rendering and the renderings to avoid. `scripts/gate/check-glossary.py` reads it and
  reports off-glossary renderings, scoped by language. It never auto-fixes: the right
  rendering is a translation judgement.
- `literature/`: reading notes and source digests. Working material, not specification.

## What is not here any more

The POD program that ran this repository until 2026-09-04 kept its rulings, ledger, memos
and task history here. The program was ended by the owner and its documents left the tree
with it. The archive itself left the repository on 2026-09-06 and now sits outside it, at
`~/Agentic/Archive/Bedrock-archive`, mirroring the paths the files had here.
