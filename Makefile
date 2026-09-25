# Bedrock. Three jobs: typecheck the tree, lint it, build the site.
#
#   make check       the full gate: typecheck, lint, test
#   make typecheck   pure incremental Agda check of the complete import closure
#   make typecheck-cold  benchmark a single-process pure cold check
#   make typecheck-cold-parallel  build cold interfaces with AGDA_JOBS workers
#   make typecheck-ci  use the cache, or parallelize a cold CI check
#   make lint        run source and reading-order gates over the whole tree
#   make milestone-lint  verify every source definition reaches Origin
#   make test        run the gate unit tests
#   make hooks       install scripts/git-hooks into the resolved Git hooks path
#   make html        one Agda traversal producing interfaces, HTML and type data
#   make html-cold   benchmark that single-process combined traversal
#   make html-cold-parallel  parallel check/trace, then run the HTML backend
#   make site        render the HTML site into _build/site
#   make site-cold   rebuild the cold Agda/HTML cache, then render the site
#   make site-backend  prepare cached HTML/type-data without rendering
#   make serve       serve _build/site locally
#   make deploy      push _build/site to Cloudflare Pages (owner only)
# Local builds use parallel checks by default; LOCAL_PARALLEL=0 restores the
# serial path, LOCAL_JOBS caps independent gates, and AGDA_JOBS defaults to 2.

.DEFAULT_GOAL := help

OUTCROP_AGDA := _build/outcrop-agda/bin/outcrop-agda
AGDA         := $(OUTCROP_AGDA)
VENV      := .venv
PYTHON    ?= python3.11
PY        ?= $(VENV)/bin/python
AGDA_JOBS ?= 2
# Local orchestration only. CI and the cold timing targets keep their existing
# recipes; Agda itself remains limited by AGDA_JOBS and the GHCRTS heap cap.
LOCAL_PARALLEL ?= $(if $(filter true 1,$(CI)),0,1)
LOCAL_JOBS ?= $(shell $(PYTHON) -c 'import os; print(min(os.cpu_count() or 2, 8))')
AGDA_DIR  ?= $(abspath _build/agda-home)
export AGDA_DIR

# GHC heap guard. The machine budget is 16 GB for Agda in total, two processes
# at most, so one run gets 8 GB. Raising either budget needs explicit approval.
export GHCRTS ?= -A64m -I0 -M8g

AGDA_ROOT  := src/Origin.lagda.md
SITE_IFACES := _build/2.8.0/agda/src
TYPECHECK_ROOT := _build/typecheck
TYPECHECK_LIB := $(TYPECHECK_ROOT)/bedrock.agda-lib
TYPECHECK_STAMP := $(TYPECHECK_ROOT)/_build/2.8.0/agda/src/Origin.agdai
HTML_DIR   := _build/html
AGDA_TRACE := _build/outcrop-agda-types.jsonl
AGDA_STAMP := $(HTML_DIR)/.bedrock-checked
BENCHMARK_DIR := _build/benchmarks
TYPECHECK_TIME := $(BENCHMARK_DIR)/typecheck-cold.time
TYPECHECK_PARALLEL_TIME := $(BENCHMARK_DIR)/typecheck-cold-parallel.time
HTML_TIME := $(BENCHMARK_DIR)/html-cold.time
HTML_PARALLEL_TIME := $(BENCHMARK_DIR)/html-cold-parallel.time
AGDA_PARALLEL := -m outcrop agda-check --options="--cubical --safe --guardedness"
AGDA_DRIVER := outcrop/src/outcrop/adapters/agda/parallel.py
AGDA_BACKEND_INPUTS := $(AGDA_DRIVER) outcrop/src/outcrop/core/source_syntax.py
AGDA_ENV_STAMP := $(AGDA_DIR)/.bedrock-library-lock.json
AGDA_ENV_INPUTS := site/agda-libraries.json \
	outcrop/src/outcrop/adapters/agda/libraries.py \
	outcrop/src/outcrop/adapters/agda/archive.py
SITE_OUT   := _build/site
LANGS      := en,zh,ja
BASE_URL   :=
PORT       := 8000
CF_PROJECT := bedrock
AGDA_SOURCES := $(shell find src -type f -name '*.lagda.md' | sort)
DIAGNOSTIC_GATES := lint-prose-gate lint-agda-gate host-lem-gate glossary-gate \
	term-gate fences-gate diagrams-gate reading-order-gate routes-gate \
	chapters-gate i18n-gate site-lint-gate
LINT_GATES := site-lint-gate docs-prose-gate glossary-extras-gate spdx-gate host-lem-gate
# Extraction has at most one Agda loader; the expression normalizer is Python.
# Do not start two compiler workflows against the same cache concurrently.
EXTRACT_JOBS = $(if $(filter 1,$(LOCAL_PARALLEL)),$(if $(filter 1,$(LOCAL_JOBS)),1,2),1)
RENDER_INCREMENTAL ?= 0
SITE_CACHE = $(PY) scripts/site/site-cache.py --site-out "$(SITE_OUT)" --langs "$(LANGS)" \
	--base-url "$(BASE_URL)" --py "$(PY)" --make "$(MAKE)" \
	--agda-jobs "$(AGDA_JOBS)" --local-parallel "$(LOCAL_PARALLEL)" \
	--html-dir "$(HTML_DIR)" --trace "$(AGDA_TRACE)" --agda-dir "$(AGDA_DIR)" \
	--interface-root "$(SITE_IFACES)"

.PHONY: help bootstrap toolchain check outcrop-agda typecheck-stage typecheck typecheck-cold typecheck-cold-parallel typecheck-ci lint milestone-lint test hooks venv gen html html-cold html-cold-parallel types _types types-local-identifiers types-local-expressions site-render site site-cold site-backend serve deploy clean distclean $(LINT_GATES) $(DIAGNOSTIC_GATES)

help:
	@printf '%s\n' \
	  'Setup:       bootstrap venv toolchain outcrop-agda hooks' \
	  'Checks:      check lint test milestone-lint typecheck typecheck-ci' \
	  'Website:     site site-backend site-render serve deploy' \
	  'Cold builds: typecheck-cold typecheck-cold-parallel html-cold html-cold-parallel site-cold' \
	  'Other:       html types gen clean distclean' \
	  'Diagnostic:  $(DIAGNOSTIC_GATES)' \
	  'Internal:    typecheck-stage _types types-local-identifiers types-local-expressions' \
	  'Lint extras: docs-prose-gate glossary-extras-gate spdx-gate' \
	  'Options: PY PYTHON LOCAL_PARALLEL LOCAL_JOBS AGDA_JOBS SITE_OUT LANGS BASE_URL PORT' \
	  'site-render forces rendering; RENDER_INCREMENTAL=1 reuses the CI artifact/render cache.' \
	  'Run one compiler workflow at a time; clean/distclean remove generated outputs.'

# One command for a fresh clone after GHC/Cabal, patch, make and Python exist.
bootstrap:
	$(MAKE) venv
	$(MAKE) toolchain

toolchain: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP)

$(AGDA_ENV_STAMP): $(AGDA_ENV_INPUTS)
	$(PY) -m outcrop agda-libraries --lock site/agda-libraries.json \
		--build-dir _build/dependencies --agda-dir $(AGDA_DIR)
	@cp site/agda-libraries.json $(AGDA_ENV_STAMP)

# The gate every document names. Local checks run independent gates alongside
# the Agda check; CI keeps its existing ordering.
ifeq ($(LOCAL_PARALLEL),1)
check:
	$(MAKE) -j$(LOCAL_JOBS) typecheck $(LINT_GATES) test
else
check: typecheck lint test
endif

outcrop-agda: $(OUTCROP_AGDA)

OUTCROP_AGDA_INPUTS := outcrop/src/outcrop/adapters/agda/build.py \
	outcrop/src/outcrop/adapters/agda/archive.py \
	$(shell find outcrop/src/outcrop/adapters/agda/resources -type f \
	\( -name '*.py' -o -name '*.json' -o -name '*.patch' -o -name '*.hs' \))

$(OUTCROP_AGDA): $(OUTCROP_AGDA_INPUTS)
	$(PY) -m outcrop agda-build --build-dir _build/outcrop-agda

# Keep pure-check interfaces in an isolated project root. A pure check therefore
# cannot make a later HTML traversal skip the elaboration events needed by the
# expression trace, and a site build cannot warm a benchmark accidentally.
$(TYPECHECK_LIB): bedrock.agda-lib
	@mkdir -p $(@D)
	@cp -p $< $@

typecheck-stage: $(TYPECHECK_LIB)
	$(PY) -m outcrop agda-stage --source src --destination $(TYPECHECK_ROOT)/src

# The ordinary proof gate uses only Agda's type checker. Its private interface
# tree makes repeat runs incremental without enabling HTML or type tracing.
typecheck: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) typecheck-stage
ifeq ($(LOCAL_PARALLEL),1)
	$(PY) $(AGDA_PARALLEL) --project-root $(TYPECHECK_ROOT) \
		--agda $(abspath $(AGDA)) --root Origin --jobs $(AGDA_JOBS) \
		--incremental --interface-root $(TYPECHECK_ROOT)/_build/2.8.0/agda/src
else
	cd $(TYPECHECK_ROOT) && $(abspath $(AGDA)) $(AGDA_ROOT)
endif

# A reproducible pure-Agda benchmark. Keep cubical's installed interfaces but
# discard every Bedrock interface, then run without HTML or tracing enabled.
typecheck-cold: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) typecheck-stage
	rm -rf $(TYPECHECK_ROOT)/_build
	@mkdir -p $(BENCHMARK_DIR)
	@echo "Cold pure Agda typecheck (cubical interfaces retained)"
	cd $(TYPECHECK_ROOT) && /usr/bin/time -p -o $(abspath $(TYPECHECK_TIME)) \
		$(abspath $(AGDA)) $(AGDA_ROOT)
	@cat $(TYPECHECK_TIME)

# Operational cold check: schedule project modules along their import DAG. The
# single-process target above remains the stable benchmark baseline.
typecheck-cold-parallel: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) typecheck-stage $(AGDA_BACKEND_INPUTS)
	rm -rf $(TYPECHECK_ROOT)/_build
	@mkdir -p $(BENCHMARK_DIR)
	@echo "Cold parallel Agda typecheck ($(AGDA_JOBS) workers; cubical interfaces retained)"
	/usr/bin/time -p -o $(abspath $(TYPECHECK_PARALLEL_TIME)) \
		$(PY) $(AGDA_PARALLEL) --project-root $(TYPECHECK_ROOT) \
		--agda $(abspath $(AGDA)) --root Origin --jobs $(AGDA_JOBS)
	@cat $(TYPECHECK_PARALLEL_TIME)

# CI restores this target's isolated interface tree. Preserve the cheap normal
# incremental path on a hit and use the DAG scheduler only on a cold runner.
typecheck-ci: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) typecheck-stage $(AGDA_BACKEND_INPUTS)
	@if [ -f $(TYPECHECK_STAMP) ]; then \
		$(MAKE) typecheck; \
	else \
		$(MAKE) typecheck-cold-parallel; \
	fi

# A separate official Agda traversal writes fresh .agdai interfaces, emits HTML,
# and records expression types for the renderer. It is the cached site-build path.
$(AGDA_STAMP): $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) $(AGDA_BACKEND_INPUTS) bedrock.agda-lib $(AGDA_SOURCES)
	@mkdir -p $(HTML_DIR)
	@if [ ! -s $(AGDA_TRACE) ] || [ $(OUTCROP_AGDA) -nt $(AGDA_TRACE) ] \
		|| [ $(AGDA_ENV_STAMP) -nt $(AGDA_TRACE) ] \
		|| [ bedrock.agda-lib -nt $(AGDA_TRACE) ] \
		|| [ $(AGDA_DRIVER) -nt $(AGDA_TRACE) ] \
		|| [ outcrop/src/outcrop/core/source_syntax.py -nt $(AGDA_TRACE) ]; then \
		rm -f $(AGDA_TRACE); \
		rm -rf $(SITE_IFACES); \
	fi
ifeq ($(LOCAL_PARALLEL),1)
	$(PY) $(AGDA_PARALLEL) --project-root . --agda $(abspath $(AGDA)) \
		--root Origin --jobs $(AGDA_JOBS) --incremental \
		--interface-root $(SITE_IFACES) --trace-out $(AGDA_TRACE) --html-dir $(HTML_DIR)
else
	OUTCROP_AGDA_TYPES="$(abspath $(AGDA_TRACE))" \
	OUTCROP_AGDA_RUN="$$(date +%s)-$$$$" \
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(AGDA_ROOT)
endif
	@touch $(AGDA_STAMP)

# Source and reading-order gates. These only read source, so local Make can
# run them on separate cores. CI invokes the same targets in their old order.
# --check makes a gate a gate: without it these report and exit 0.
lint-prose-gate:
	$(PY) scripts/gate/lint-prose.py --check

lint-agda-gate:
	$(PY) scripts/gate/lint-agda.py --check

host-lem-gate:
	$(PY) scripts/gate/check-host-lem.py

glossary-gate:
	$(PY) scripts/gate/check-glossary.py --check

term-gate:
	$(PY) scripts/gate/check-term-introductions.py

fences-gate:
	$(PY) scripts/gate/check-fences.py --check

diagrams-gate:
	$(PY) scripts/gate/check-diagrams.py

reading-order-gate:
	$(PY) scripts/gate/check-reading-order.py

routes-gate:
	$(PY) scripts/site/reading_routes.py --check

chapters-gate:
	$(PY) scripts/gate/check-chapter-framework.py

i18n-gate:
	$(PY) scripts/site/weave-i18n.py --check

site-lint-gate:
	$(PY) -m outcrop lint --config site/project.json --project-root .

# The shared gate owns src/. Retain only the adapters' additional scopes here;
# focused/staged diagnostic commands above and Git hooks remain unchanged.
docs-prose-gate:
	$(PY) scripts/gate/lint-prose.py --check --docs-only

glossary-extras-gate:
	$(PY) scripts/gate/check-glossary.py --check --extras-only

spdx-gate:
	$(PY) scripts/gate/lint-agda.py --spdx-only

ifeq ($(LOCAL_PARALLEL),1)
lint:
	$(MAKE) -j$(LOCAL_JOBS) $(LINT_GATES)
else
lint: $(LINT_GATES)
endif

# Final-tree gate: run by pre-push and CI, not by the pre-commit hook or make lint.
milestone-lint:
	$(PY) scripts/gate/check-milestone-consumption.py

test:
	$(PY) -m unittest discover -s scripts/tests -p "test_*.py" -t scripts/tests -v
	$(MAKE) -C outcrop test PY="$(if $(findstring /,$(PY)),$(abspath $(PY)),$(PY))"

hooks:
	@set -e; hook_dir="$$(git rev-parse --git-path hooks)"; \
		mkdir -p "$$hook_dir"; \
		install -m 755 scripts/git-hooks/pre-commit "$$hook_dir/pre-commit"; \
		install -m 755 scripts/git-hooks/pre-push "$$hook_dir/pre-push"
	@echo "pre-commit and pre-push hooks installed"

venv:
	$(PYTHON) -m venv $(VENV)
	$(PY) -m pip install -q -r requirements-dev.txt

gen:
	$(PY) scripts/site/weave-i18n.py --gen --out _build/woven

html: $(AGDA_STAMP)

# Measure the combined compiler/backend path independently of typecheck-cold.
# Clearing both sets of outputs guarantees that this invocation itself creates
# the project interfaces, HTML, and complete expression trace.
html-cold: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) bedrock.agda-lib $(AGDA_SOURCES)
	rm -rf $(SITE_IFACES) $(HTML_DIR)
	rm -f $(AGDA_TRACE)
	@mkdir -p $(HTML_DIR) $(BENCHMARK_DIR)
	@echo "Cold combined Agda interface + HTML + type-trace build"
	OUTCROP_AGDA_TYPES="$(abspath $(AGDA_TRACE))" \
	OUTCROP_AGDA_RUN="$$(date +%s)-$$$$" \
	/usr/bin/time -p -o $(abspath $(HTML_TIME)) \
		$(AGDA) --html --html-highlight=code \
		--html-dir=$(HTML_DIR) $(AGDA_ROOT)
	@cat $(HTML_TIME)
	@touch $(AGDA_STAMP)

# Fast cold site backend: build shared external dependencies once, elaborate
# independent project modules concurrently, and record one trace part per
# process. Then merge the trace and let the official HTML backend read the
# completed interfaces. No project module is checked twice.
html-cold-parallel: $(OUTCROP_AGDA) $(AGDA_ENV_STAMP) bedrock.agda-lib $(AGDA_SOURCES) $(AGDA_BACKEND_INPUTS)
	rm -rf $(SITE_IFACES) $(HTML_DIR)
	rm -f $(AGDA_TRACE)
	@mkdir -p $(HTML_DIR) $(BENCHMARK_DIR)
	@echo "Cold parallel Agda + HTML + type-trace build ($(AGDA_JOBS) workers)"
	/usr/bin/time -p -o $(abspath $(HTML_PARALLEL_TIME)) \
		$(PY) $(AGDA_PARALLEL) --project-root . \
		--agda $(abspath $(AGDA)) --root Origin --jobs $(AGDA_JOBS) \
		--trace-out $(AGDA_TRACE) --html-dir $(HTML_DIR)
	@cat $(HTML_PARALLEL_TIME)
	@touch $(AGDA_STAMP)

# Raw extraction consumes an already prepared backend. Only types/html own
# compiler freshness; the content-cache driver deliberately calls _types.
types-local-identifiers:
	$(PY) scripts/site/extract-types.py --agda $(abspath $(AGDA)) \
		--html-dir $(HTML_DIR) --out _build/types.json

types-local-expressions:
	$(PY) scripts/site/extract-expression-types.py --html-dir $(HTML_DIR) \
		--trace $(AGDA_TRACE) --out _build/expression-types.json

types: html
	$(MAKE) _types

_types:
	$(MAKE) -j$(EXTRACT_JOBS) types-local-identifiers types-local-expressions

# Host-specific jobs can render from an unpacked HTML/type-data artifact without
# Agda or its interfaces. The ordinary site target first produces that backend.
site-render:
	$(SITE_CACHE) --render-only $(if $(filter 1,$(RENDER_INCREMENTAL)),,--force-render)

# Local builds compare source content and reuse compiler evidence across prose
# edits. CI invokes this cache driver in separate backend and render jobs.
site:
	$(SITE_CACHE)

site-cold:
	$(SITE_CACHE) --cold

site-backend:
	$(SITE_CACHE) --backend-only

serve:
	$(PY) -m http.server $(PORT) --directory $(SITE_OUT)

deploy: site
	npx wrangler pages deploy $(SITE_OUT) --project-name=$(CF_PROJECT)

clean:
	rm -rf $(HTML_DIR) $(SITE_OUT) _build/woven _build/types.json \
		_build/expression-types.json $(AGDA_TRACE) $(AGDA_TRACE).parts \
		_build/expression-probe _build/cache/site-backend.json \
		_build/cache/code-context.json.gz \
		_build/cache/render-*.json _build/cache/site-*.json

distclean: clean
	rm -rf _build/outcrop-agda \
		_build/dependencies _build/agda-home $(TYPECHECK_ROOT) _build/2.8.0 \
		$(BENCHMARK_DIR)
