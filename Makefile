# Bedrock build orchestration.
#
#   make venv    create .venv (Python 3.11+) and install pinned tooling (requirements-dev.txt)
#   make check   typecheck + prose lint + marker + glossary + reuse-lint integrity (the gate)
#   make site    build the multilingual hyperlinked site into _build/site
#   make serve   preview the built site locally
#   make gen     weave per-language mono-lingual .lagda.md (agda --html compatibility)
#   make hooks   activate the version-controlled git pre-commit hook
#
# Run `make venv` once per clone; `make` then uses the venv interpreter and tools. Type-checking
# needs Agda; everything Python (lint, markers, glossary, reuse, the site build) runs from .venv
# (Python 3.11+). No node, no GHC; math fonts and KaTeX load from a CDN at view time. Everything
# generated lives under _build/ (git-ignored).

AGDA      := agda
VENV      := .venv
# GHC heap guard for every agda run: a runaway typecheck exits cleanly ("Heap
# exhausted") instead of OOM-killing the machine. -M caps the heap, -A64m -I0
# speed GC on big checks. Override per environment (GHCRTS="-M28g" make check).
export GHCRTS ?= -A64m -I0 -M16g
# Bootstrap interpreter for `make venv` (must be >= 3.11); override in CI, e.g. PYTHON=python3.
PYTHON    ?= python3.11
# Interpreter and tools used by all targets (the venv); override only if needed, e.g. PY=python3.
PY        ?= $(VENV)/bin/python
REUSE     ?= $(VENV)/bin/reuse
EVERYTHING := src/Everything.lagda.md
HTML_DIR  := _build/html
SITE_OUT  := _build/site
LANGS     := en,zh
BASE_URL  :=
PORT      := 8000
CF_PROJECT := bedrock

.PHONY: check typecheck lint lint-agda markers glossary ledger probes tree reuse ruleids taskindex devdocs agentsguard gen html types site serve clean hooks test deploy venv venv-check

check: venv-check typecheck markers lint lint-agda glossary ledger probes tree fences reuse ruleids devdocs taskindex agentsguard dispatchpolicy

venv:
	$(PYTHON) -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else "make venv: need Python 3.11+ (got %s); pass PYTHON=<python3.11+>" % sys.version.split()[0])'
	$(PYTHON) -m venv $(VENV)
	$(PY) -m pip install --quiet --upgrade pip
	$(PY) -m pip install --quiet -r requirements-dev.txt
	@echo "venv ready: $(VENV) ($$($(PY) --version))"

venv-check:
	@test -x $(PY) || { echo "No virtualenv at $(VENV)/. Run: make venv"; exit 1; }

typecheck:
	$(AGDA) $(EVERYTHING)

lint:
	$(PY) scripts/lint-prose.py --check

lint-agda:
	$(PY) scripts/lint-agda.py --check

markers:
	$(PY) scripts/weave-i18n.py --check

glossary:
	$(PY) scripts/check-glossary.py --check

ledger:
	$(PY) scripts/ledger.py --check

# DD24 makes the seconds-per-line ratio the ONLY threshold on the GCH wing.
#
# IT IS NOT IN `make check`, and that is deliberate. It runs Agda, and
# dev/ORCHESTRATION.md forbids a typecheck in the commit gate: the gate must
# stay cheap, and this tool fails closed whenever another agda process is
# live, so in the gate it would turn a busy machine into a red commit. It is
# an on-demand MEASUREMENT, in the same class as scripts/deletion-test.py.
#
# IT MEASURES COLD, because the baseline it compares against is cold. A warm
# run against a cold baseline is not a looser check, it is a WRONG one: warm
# is several times faster, so a wing far over the bar reads as under it.
# [LJ-0.1] caught the gate wired warm.
ratio:
	$(PY) scripts/check-ratio.py --check

probes:
	$(PY) scripts/check-probes.py --check

tree:
	$(PY) scripts/check-tree.py --check

# Agda outside a fence is invisible to Agda AND to ledger.py, so a green
# tree and a right line count both prove nothing about it. [LJ-1.41]
# reported two theorems CLOSED that sat in prose and carried four defects.
fences:
	$(PY) scripts/check-fences.py --check

# A dangling rule citation reads as authority. [L3.32-T105] found one in a
# document written ABOUT rule hygiene, which is the argument for gating it.
ruleids:
	$(PY) scripts/check-rule-ids.py
	$(PY) scripts/rules.py --check

# The dev/ documents decay; [L3.32-T110] built the maintenance mechanism so
# the decay is found here, not by accident. Six cheap subchecks: size caps on
# AGENTS.md and PLAN cells, routing of imported LESSONS entries, the section 0
# "as of" date, memo STATUS form, and that AGENTS.md's named enforcers exist.
# On-demand sweep (never a gate): scripts/check-dev-docs.py --sweep.
taskindex:
	$(PY) scripts/check-task-index.py

agentsguard:
	$(PY) scripts/check-agents-guard.py

# The head that runs a dispatch is DD17's, and since 2026-08-13 it has two
# versions with one switch selecting between them. This checks that briefs
# agree with the version in force. It cannot check which head actually RAN:
# an in-harness Opus dispatch passes through no tool at all.
dispatchpolicy:
	$(PY) scripts/check-dispatch-policy.py

devdocs:
	$(PY) scripts/check-dev-docs.py

# The generated dashboard was ABOLISHED by the owner on 2026-08-09. Its three
# scripts are frozen in archive/tooling/, with what they did right and the one
# thing they got wrong. The canonical figures are unchanged and are read with
# `python3 scripts/ledger.py --brief`.

reuse:
	$(REUSE) lint

gen:
	$(PY) scripts/weave-i18n.py --gen --out _build/woven

html:
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(EVERYTHING)

types:
	$(PY) scripts/extract-types.py --out _build/types.json

site: html types
	$(PY) scripts/render-site.py --html-dir $(HTML_DIR) --out $(SITE_OUT) \
		--langs $(LANGS) --base-url "$(BASE_URL)"
	$(PY) scripts/gen-depmap.py --src src --out $(SITE_OUT) --langs $(LANGS)

serve:
	@echo "Serving $(SITE_OUT) at http://localhost:$(PORT)/ (Ctrl-C to stop)"
	$(PY) -m http.server $(PORT) --directory $(SITE_OUT)

# Deploy the site (built at domain root) to Cloudflare Pages. Needs `wrangler login`
# or CLOUDFLARE_API_TOKEN + CLOUDFLARE_ACCOUNT_ID in the environment.
deploy: site
	npx wrangler pages deploy $(SITE_OUT) --project-name=$(CF_PROJECT)

# EVERY suite, not a subset. Until 2026-08-09 this target ran three of seven,
# and the four it skipped had been red for days: test_task_index.py broke when
# the LJ renumbering changed the checker's return shape, and it broke a real
# behaviour with it (a zero-padded citation stopped resolving). A test nobody
# runs is not a test. Add new suites HERE, in the same commit.
test:
	$(PY) scripts/tests/test_i18n.py
	$(PY) scripts/tests/test_glossary.py
	$(PY) scripts/tests/test_lint_agda.py
	$(PY) scripts/tests/test_dev_docs.py
	$(PY) scripts/tests/test_obligations.py
	$(PY) scripts/tests/test_task_index.py
	$(PY) scripts/tests/test_deletion_test.py
	$(PY) scripts/tests/test_ratio_baseline.py

# THE FETCHED PRIMARY SOURCES SURVIVE `clean`, added 2026-08-10 at the
# [LJ-0.4] closeout. _build/literature/ holds the OCR text and PDFs of Devlin,
# Jensen and Jech. They cannot be committed, because they are copyrighted, and
# `rm -rf _build` destroyed them along with the generated site.
#
# THE CITATIONS ARE WHAT BREAKS. [LJ-1.11] cites dev2.txt by LINE NUMBER 29
# times, and dev/literature/ cites it throughout. A re-fetch restores the
# text but not necessarily the same line numbers, because the files are OCR
# output; primary-sources.md records that the load-bearing pages needed a
# second OCR pass with a different engine. So a clean would silently turn every
# line citation in the corpus into a number pointing at nothing.
#
# Provenance for re-fetching is dev/literature/primary-sources.md.
clean:
	find _build -mindepth 1 -maxdepth 1 ! -name literature -exec rm -rf {} +

hooks:
	git config --local core.hooksPath scripts/git-hooks
	@echo "pre-commit hook activated (core.hooksPath = scripts/git-hooks)"
