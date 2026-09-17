# Bedrock. Three jobs: typecheck the tree, lint it, build the site.
#
#   make check       the full gate: typecheck, lint, test
#   make typecheck   pure incremental Agda check of the complete import closure
#   make typecheck-cold  benchmark a pure check with cold project interfaces
#   make lint        run source and reading-order gates over the whole tree
#   make milestone-lint  verify every source definition reaches Milestones
#   make test        run the gate unit tests
#   make hooks       install scripts/git-hooks into .git/hooks
#   make html        one Agda traversal producing interfaces, HTML and type data
#   make html-cold   benchmark that traversal with cold project/site caches
#   make site        render the HTML site into _build/site
#   make site-cold   rebuild the cold Agda/HTML cache, then render the site
#   make serve       serve _build/site locally
#   make deploy      push _build/site to Cloudflare Pages (owner only)

BEDROCK_AGDA := _build/bin/bedrock-agda
AGDA         := $(BEDROCK_AGDA)
VENV      := .venv
PYTHON    ?= python3.11
PY        ?= $(VENV)/bin/python
AGDA_DIR  ?= $(abspath _build/agda-home)
export AGDA_DIR

# GHC heap guard. The machine budget is 16 GB for Agda in total, two processes
# at most, so one run gets 8 GB. Override per run: GHCRTS="-M12g" make typecheck.
export GHCRTS ?= -A64m -I0 -M8g

AGDA_ROOT  := src/Milestones.lagda.md
SITE_IFACES := _build/2.8.0/agda/src
TYPECHECK_ROOT := _build/typecheck
TYPECHECK_LIB := $(TYPECHECK_ROOT)/bedrock.agda-lib
HTML_DIR   := _build/html
AGDA_TRACE := _build/bedrock-agda-types.jsonl
AGDA_STAMP := $(HTML_DIR)/.bedrock-checked
BENCHMARK_DIR := _build/benchmarks
TYPECHECK_TIME := $(BENCHMARK_DIR)/typecheck-cold.time
HTML_TIME := $(BENCHMARK_DIR)/html-cold.time
SITE_OUT   := _build/site
LANGS      := en,zh,ja
BASE_URL   :=
PORT       := 8000
CF_PROJECT := bedrock
AGDA_SOURCES := $(shell find src -type f -name '*.lagda.md' | sort)
TYPECHECK_SOURCES := $(patsubst src/%,$(TYPECHECK_ROOT)/src/%,$(AGDA_SOURCES))

.PHONY: bootstrap toolchain check bedrock-agda typecheck-stage typecheck typecheck-cold lint milestone-lint test hooks venv gen html html-cold types types-refresh site site-cold serve deploy clean distclean

# One command for a fresh clone after GHC/Cabal, patch, make and Python exist.
bootstrap: venv toolchain

toolchain: $(BEDROCK_AGDA)
	$(PYTHON) tools/bedrock-agda/setup.py

# The gate every document names. CI runs it, the hook runs its cheap half.
check: typecheck lint test

bedrock-agda: $(BEDROCK_AGDA)

BEDROCK_AGDA_INPUTS := tools/bedrock-agda/build.py tools/bedrock-agda/manifest.json \
	$(wildcard tools/bedrock-agda/adapters/*.patch) \
	$(shell find tools/bedrock-agda/src -type f -name '*.hs' 2>/dev/null)

$(BEDROCK_AGDA): $(BEDROCK_AGDA_INPUTS)
	$(PYTHON) tools/bedrock-agda/build.py

# Keep pure-check interfaces in an isolated project root. A pure check therefore
# cannot make a later HTML traversal skip the elaboration events needed by the
# expression trace, and a site build cannot warm a benchmark accidentally.
$(TYPECHECK_ROOT)/src/%.lagda.md: src/%.lagda.md
	@mkdir -p $(@D)
	@cp -p $< $@

$(TYPECHECK_LIB): bedrock.agda-lib
	@mkdir -p $(@D)
	@cp -p $< $@

typecheck-stage: $(TYPECHECK_LIB) $(TYPECHECK_SOURCES)

# The ordinary proof gate uses only Agda's type checker. Its private interface
# tree makes repeat runs incremental without enabling HTML or type tracing.
typecheck: $(BEDROCK_AGDA) typecheck-stage
	cd $(TYPECHECK_ROOT) && $(abspath $(AGDA)) $(AGDA_ROOT)

# A reproducible pure-Agda benchmark. Keep cubical's installed interfaces but
# discard every Bedrock interface, then run without HTML or tracing enabled.
typecheck-cold: $(BEDROCK_AGDA) typecheck-stage
	rm -rf $(TYPECHECK_ROOT)/_build
	@mkdir -p $(BENCHMARK_DIR)
	@echo "Cold pure Agda typecheck (cubical interfaces retained)"
	cd $(TYPECHECK_ROOT) && /usr/bin/time -p -o $(abspath $(TYPECHECK_TIME)) \
		$(abspath $(AGDA)) $(AGDA_ROOT)
	@cat $(TYPECHECK_TIME)

# A separate official Agda traversal writes fresh .agdai interfaces, emits HTML,
# and records expression types for the renderer. It is the cached site-build path.
$(AGDA_STAMP): $(BEDROCK_AGDA) bedrock.agda-lib $(AGDA_SOURCES)
	@mkdir -p $(HTML_DIR)
	@if [ ! -s $(AGDA_TRACE) ] || [ $(BEDROCK_AGDA) -nt $(AGDA_TRACE) ]; then \
		rm -f $(AGDA_TRACE); \
		rm -rf $(SITE_IFACES); \
	fi
	BEDROCK_AGDA_TYPES="$(abspath $(AGDA_TRACE))" \
	BEDROCK_AGDA_RUN="$$(date +%s)-$$$$" \
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(AGDA_ROOT)
	@touch $(AGDA_STAMP)

# Source and reading-order gates. lint-prose and lint-agda take --staged; here they
# sweep the tree. check-glossary needs tomllib, so it wants the venv's 3.11.
# --check makes a gate a gate: without it these report and exit 0.
lint:
	$(PY) scripts/gate/lint-prose.py --check
	$(PY) scripts/gate/lint-agda.py --check
	$(PY) scripts/gate/check-glossary.py --check
	$(PY) scripts/gate/check-term-introductions.py
	$(PY) scripts/gate/check-fences.py --check
	$(PY) scripts/gate/check-reading-order.py
	$(PY) scripts/site/reading_routes.py --check
	$(PY) scripts/gate/check-chapter-framework.py
	$(PY) scripts/site/weave-i18n.py --check

# Final-tree gate: run by pre-push and CI, not by the pre-commit hook or make lint.
milestone-lint:
	$(PY) scripts/gate/check-milestone-consumption.py

test:
	$(PY) -m unittest discover -s scripts/tests -p "test_*.py" -t scripts/tests -v

hooks:
	install -m 755 scripts/git-hooks/pre-commit .git/hooks/pre-commit
	install -m 755 scripts/git-hooks/pre-push .git/hooks/pre-push
	@echo "pre-commit and pre-push hooks installed; bypass a commit with --no-verify"

venv:
	$(PYTHON) -m venv $(VENV)
	$(PY) -m pip install -q -r requirements-dev.txt

gen:
	$(PY) scripts/site/weave-i18n.py --gen --out _build/woven

html: $(AGDA_STAMP)

# Measure the combined compiler/backend path independently of typecheck-cold.
# Clearing both sets of outputs guarantees that this invocation itself creates
# the project interfaces, HTML, and complete expression trace.
html-cold: $(BEDROCK_AGDA) bedrock.agda-lib $(AGDA_SOURCES)
	rm -rf $(SITE_IFACES) $(HTML_DIR)
	rm -f $(AGDA_TRACE)
	@mkdir -p $(HTML_DIR) $(BENCHMARK_DIR)
	@echo "Cold combined Agda interface + HTML + type-trace build"
	BEDROCK_AGDA_TYPES="$(abspath $(AGDA_TRACE))" \
	BEDROCK_AGDA_RUN="$$(date +%s)-$$$$" \
	/usr/bin/time -p -o $(abspath $(HTML_TIME)) \
		$(AGDA) --html --html-highlight=code \
		--html-dir=$(HTML_DIR) $(AGDA_ROOT)
	@cat $(HTML_TIME)
	@touch $(AGDA_STAMP)

types: html
	$(PY) scripts/site/extract-types.py --html-dir $(HTML_DIR) --out _build/types.json
	$(PY) scripts/site/extract-expression-types.py --html-dir $(HTML_DIR) \
		--trace $(AGDA_TRACE) --out _build/expression-types.json

types-refresh: html
	$(PY) scripts/site/extract-types.py --html-dir $(HTML_DIR) --out _build/types.json
	$(PY) scripts/site/extract-expression-types.py --html-dir $(HTML_DIR) \
		--trace $(AGDA_TRACE) --out _build/expression-types.json

site: types
	$(PY) scripts/site/render-site.py --html-dir $(HTML_DIR) --out $(SITE_OUT) \
		--langs $(LANGS) --base-url "$(BASE_URL)"
	$(PY) scripts/site/gen-depmap.py --src src --out $(SITE_OUT) --langs $(LANGS)

site-cold: html-cold
	$(MAKE) site PY="$(PY)" LANGS="$(LANGS)" BASE_URL="$(BASE_URL)"

serve:
	$(PY) -m http.server $(PORT) --directory $(SITE_OUT)

deploy: site
	npx wrangler pages deploy $(SITE_OUT) --project-name=$(CF_PROJECT)

clean:
	rm -rf $(HTML_DIR) $(SITE_OUT) _build/woven _build/types.json \
		_build/expression-types.json $(AGDA_TRACE) _build/expression-probe

distclean: clean
	rm -rf _build/bedrock-agda _build/bin/bedrock-agda \
		_build/dependencies _build/agda-home $(TYPECHECK_ROOT) _build/2.8.0 \
		$(BENCHMARK_DIR)
