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

.PHONY: check clean closure deploy fences gen glossary hooks html ledger lint lint-agda markers probes ratio reuse ruleids serve site specsurface test timing typecheck types venv venv-check survey

check: venv-check typecheck markers lint lint-agda glossary ledger probes \
       closure fences reuse ruleids specsurface

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
	$(PY) scripts/gate/lint-prose.py --check

lint-agda:
	$(PY) scripts/gate/lint-agda.py --check

markers:
	$(PY) scripts/site/weave-i18n.py --check

glossary:
	$(PY) scripts/gate/check-glossary.py --check

ledger:
	$(PY) scripts/measure/ledger.py --check

# DD24 makes the seconds-per-line ratio the ONLY threshold on the GCH wing.
#
# IT IS NOT IN `make check`, and that is deliberate. It runs Agda, and
# dev/ORCHESTRATION.md forbids a typecheck in the commit gate: the gate must
# stay cheap, and this tool fails closed whenever another agda process is
# live, so in the gate it would turn a busy machine into a red commit. It is
# an on-demand MEASUREMENT, in the same class as scripts/measure/deletion-test.py.
#
# IT MEASURES COLD, because the baseline it compares against is cold. A warm
# run against a cold baseline is not a looser check, it is a WRONG one: warm
# is several times faster, so a wing far over the bar reads as under it.
# [LJ-0.1] caught the gate wired warm.
ratio:
	$(PY) scripts/measure/check-ratio.py --check

# ADVISORY, never in check: it runs Agda and costs minutes, the same class as
# ratio and deletion-test. It had NO target until 2026-08-17, so the only way to
# run it was to remember its path, while its named sibling check-ratio.py had
# one. It is a maintainer profiler. Its thresholds are SUSPENDED, not absent.
timing:
	$(PY) scripts/measure/check-timing.py

# ONE gate, and it answers one question: did a probe get into git outside its
# home? The owner ruled on 2026-08-13 that a probe lives in agents/tasks/
# beside its report, is tracked, and is never deleted, so there is no lifecycle
# left to run. `make probes-sweep` and `--gate` are RETIRED with the rest of
# [LJ-1.138]'s sweep; the frozen code is archive/scripts/check-probes-lifecycle.py.
# src/ is still forbidden absolutely: that rule was bought on 2026-08-04 when
# one `git add -A src/` committed 13 probe files. Cost: 0.24 s, measured
# 2026-08-13 over 1,586 tracked files.
probes:
	$(PY) scripts/gate/check-probes.py --check

# The commit gate against a LIVE agent's write territory. [LJ-1.189]'s P3,
# built by [LJ-1.193]. Two `git add -A` sweeps on 2026-08-13 committed a
# sibling's work in progress; a staged file inside a live agent's task
# directory or brief write scope is refused by --staged, and the --check
# tracked-tree mode audits that nothing already landed there. The ONE
# exemption is a live record's own brief path, MEASURED: the orchestrator
# commits a brief while its agent is live (4ae98f3, 82dd1fb, 8eb2ba0). NO hook
# runs this checker: the pre-commit hook does not call it, MEASURED 2026-08-17.
# This target is the only place it fires, and it runs --staged, for the reason
# below. Cost: a registry read, a ps per live agent, one git ls-files.

closure:
	$(PY) scripts/pod/check-closure.py --check closure

specsurface:
	$(PY) scripts/pod/check-spec-surface.py --check

fences:
	$(PY) scripts/gate/check-fences.py --check

# A dangling rule citation reads as authority. [L3.32-T105] found one in a
# document written ABOUT rule hygiene, which is the argument for gating it.
ruleids:
	$(PY) scripts/gate/check-rule-ids.py

reuse:
	$(REUSE) lint

gen:
	$(PY) scripts/site/weave-i18n.py --gen --out _build/woven

html:
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(EVERYTHING)

types:
	$(PY) scripts/site/extract-types.py --out _build/types.json

site: html types
	$(PY) scripts/site/render-site.py --html-dir $(HTML_DIR) --out $(SITE_OUT) \
		--langs $(LANGS) --base-url "$(BASE_URL)"
	$(PY) scripts/site/gen-depmap.py --src src --out $(SITE_OUT) --langs $(LANGS)

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
	$(PY) scripts/tests/test_obligations.py
	$(PY) scripts/tests/test_probe_gate.py
	$(PY) scripts/tests/test_deletion_test.py
	$(PY) scripts/tests/test_ratio_baseline.py
	$(PY) scripts/tests/test_rule_series.py
	$(PY) scripts/tests/test_agents_tree.py
	$(PY) scripts/tests/test_archive_layout.py
	$(PY) scripts/tests/test_scripts_layout.py
# THE SAME DEFECT RECURRED, and the comment above was written for it. On
# 2026-08-16 four suites existed under scripts/tests/ and this target ran
# none of them: test_premises_stated (RED since check-premises-stated.py was
# routed through agents_tree, because its fixture root stopped resolving),
# test_dispatch_clock, test_quota_fallback and test_ratio_noise. Wired here.
	$(PY) scripts/tests/test_quota_fallback.py
	$(PY) scripts/tests/test_ratio_noise.py
	$(PY) scripts/tests/test_pod_launcher.py
	$(PY) scripts/tests/test_pod_facts.py
	$(PY) scripts/tests/test_pod_gates.py
	$(PY) scripts/tests/test_pod_table.py
	$(PY) scripts/tests/test_pod_loop.py
	$(PY) scripts/tests/test_pod_digest.py

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

# NOT A GATE, and check-survey-quotes.py's own docstring says so: `--all` sweeps the
# whole tree and MEASURED 2026-08-17 that 80 of 278 pairs fail, every one a record
# written before the 2026-08-16 amendment. A record is never rewritten, so a whole-tree
# sweep can only teach an author to ignore a red gate. THE GATE IS ONE TASK, at
# acceptance conjunct 6, and the POD runner fires it there.
survey:
	$(PY) scripts/pod/check-survey-quotes.py --all
