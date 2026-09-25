# Bedrock scripts

These are Bedrock's command adapters, mathematical/editorial gates and
content-dependent tests. Reusable implementation lives in the pinned
[Outcrop submodule](../outcrop/README.md), not in a second framework here.
Run the commands below from the repository root, after initializing submodules
and installing the environment as described in the [project README](../README.md).

## Directory map

| Path | Responsibility |
| --- | --- |
| `gate/` | Bedrock source discovery, mathematical policies and adapters to shared lint engines |
| `site/` | Bedrock configuration and path defaults for Outcrop commands |
| `tests/` | Bedrock-content unit tests and real-browser fixtures |
| `git-hooks/` | Commit and push gates installed with `make hooks` |
| `repo_root.py` | Repository-root discovery helper for its script consumers |

Durable inputs and rules belong in [site/](../site/README.md). Research and
one-off investigations belong in [dev/](../dev/README.md); generated output goes
under ignored `_build/`. The former POD tooling is retired; do not restore its
orchestration or historical gates from the old scripts index.

## Checks and reports

Prefer the [Makefile](../Makefile), which sets the local toolchain, library
registry and resource limits:

| Command | Scope |
| --- | --- |
| `make check` | Pure Agda typechecking, `make lint` and both unit-test suites; no website build or browser acceptance |
| `make lint` | Source/prose, assumptions, glossary, terminology, fences, figures, reading order/routes, chapter structure, language markers and Outcrop site lint |
| `make milestone-lint` | Verify that the Origin import closure consumes the source development; also a push/CI gate |
| `make test` | Bedrock `scripts/tests/test_*.py` and reusable `outcrop/tests/test_*.py` |

The gate adapters are grouped by responsibility:

- `lint-agda.py`, `lint-prose.py`: source and literary conventions. The SPDX
  header check visits Bedrock-owned files only, excluding independent Git
  workspaces/submodules, generated products and third-party dependencies. Full
  and staged scans share the boundary in [STYLE-agda](../site/STYLE-agda.md).
- `check-host-lem.py`, `check-milestone-consumption.py`: Bedrock's mathematical
  assumption inventory and Origin reachability.
- `check-glossary.py`, `check-term-introductions.py`: canonical translations,
  reader introductions and explicit forward references.
- `check-fences.py`, `check-diagrams.py`, `check-chapter-framework.py`,
  `check-reading-order.py`: source structure, figure placement, chapter setup,
  outline and prerequisite order.
- `check-literary-exposition.py`: supplemental exposition audit, **not** part
  of `make check`. Without `--check`, it is an inventory and can report findings
  while exiting successfully.
- `count-agda.py`: source metrics, not a correctness gate.

For a focused audit or metrics report:

```sh
.venv/bin/python scripts/gate/check-literary-exposition.py --check src/Base/Choice.lagda.md
.venv/bin/python scripts/gate/count-agda.py
```

Statements/proofs still require accompanying code, but no authored QED mark.
Definition-ending overlays come from compiler evidence, independently of prose
labels; see the [Markdown contract](../outcrop/docs/RENDERER-MARKDOWN.md).

## Website adapters

| Script | Responsibility / usual caller |
| --- | --- |
| `site/site-cache.py` | Local `make site` content cache: reuse certified code on prose edits, refresh affected pages and search, rebuild Agda on code changes |
| `site/render-site.py` | Render the configured instance; `make site-render` |
| `site/extract-types.py` | Identifier type data; `make types-local-identifiers` |
| `site/extract-expression-types.py` | Compiler expression/definition evidence; `make types-local-expressions` |
| `site/weave-i18n.py` | Language-marker check and single-language source copies; `make gen` |
| `site/reading_routes.py` | Route validation (`--check`) or JSON inventory |
| `site/gen-depmap.py` | Standalone graph publishing adapter; normal site builds already publish the graph |

The optional compiler build, patch, dependency installer and scheduler live in
`outcrop/src/outcrop/adapters/agda/`. Their configuration and exact local output
paths are documented in [AGDA-ENVIRONMENT](../site/AGDA-ENVIRONMENT.md).
Do not use pure-check interfaces as a substitute for semantic backend data.

```sh
make site
.venv/bin/python -m outcrop check-links _build/site
.venv/bin/python -m outcrop check-search _build/site
make serve SITE_OUT=_build/site PORT=8000
```

`site/site-cache.py --backend-only` and `--render-only` let GitHub Actions
reuse the same content cache across its backend artifact and deployment jobs.
`make site-render` is sufficient only when existing compiler data remains valid.
Deployment is a separate authorized operation; see the
[workflow guide](../.github/workflows/README.md).

## Browser tests

Build the trilingual site first, then serve its actual runtime:

```sh
.venv/bin/python scripts/tests/serve-boilerplate-regression.py --site _build/site --port 18764
```

Open each fixture sequentially at `http://127.0.0.1:18764`, keeping the tested
tab active. The server routes are:

| Route | Coverage |
| --- | --- |
| `/regression` | Source/type hover branches and definition modal |
| `/padding-regression` | Code width, scroll padding, submodules and semantic QED |
| `/directory-regression` | Interactive contents and navigation |
| `/appearance-regression` | Theme and syntax palettes |
| `/universe-regression` | Universe notation and recursive hover |
| `/fonts-regression` | Selective mathematical fonts |
| `/mobile-reader` | Touch selection, compact controls and landscape code reading |

`--modal-delay 2` can expose loading states. `browser-mobile-probe.js` is a
test-only touch probe, not a production asset. Record browser, actions, output
directory and runtime digest alongside results under `_build/`. These fixtures
are not run by `make test`; simulated touch is not real iPhone Safari evidence.
Use the full [acceptance matrix](../site/ARCHITECTURE.md#acceptance-matrix) for
affected interactions and Outcrop's independent example for reusable behavior.

## Git hooks

`make hooks` installs the tracked hooks into `.git/hooks/`. Pre-commit runs
staged prose lint, whole-source language-marker checks, staged Agda/SPDX lint,
glossary, fence and chapter checks. Pre-push runs the Origin consumption gate.
Neither hook replaces `make check` or browser verification. Do not bypass gates
to obtain a successful commit or push.

CI uses the shared `outcrop.adapters.ci_scope` classifier with Bedrock's
`site/ci-docs.json` policy. It retains lint, tests and closure checks for documents
while skipping Agda and deployment when the complete diff is documentation-only.
`test_ci_scope.py` checks the instance boundary and workflow wiring; the reusable
Git/event/submodule cases are tested in Outcrop. Local Make targets and hooks
remain unchanged; see the [workflow guide](../.github/workflows/README.md).
