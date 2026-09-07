# Bedrock. Three jobs: typecheck the tree, lint it, build the site.
#
#   make check       the full gate: typecheck, lint, test
#   make typecheck   typecheck src/Everything.lagda.md
#   make lint        run source and reading-order gates over the whole tree
#   make test        run the gate unit tests
#   make hooks       install scripts/git-hooks into .git/hooks
#   make site        render the HTML site into _build/site
#   make serve       serve _build/site locally
#   make deploy      push _build/site to Cloudflare Pages (owner only)

AGDA      := agda
VENV      := .venv
PYTHON    ?= python3.11
PY        ?= $(VENV)/bin/python

# GHC heap guard. The machine budget is 16 GB for Agda in total, two processes
# at most, so one run gets 8 GB. Override per run: GHCRTS="-M12g" make typecheck.
export GHCRTS ?= -A64m -I0 -M8g

EVERYTHING := src/Everything.lagda.md
HTML_DIR   := _build/html
SITE_OUT   := _build/site
LANGS      := en,zh
BASE_URL   :=
PORT       := 8000
CF_PROJECT := bedrock

.PHONY: check typecheck lint test hooks venv gen html types site serve deploy clean

# The gate every document names. CI runs it, the hook runs its cheap half.
check: typecheck lint test

typecheck:
	$(AGDA) $(EVERYTHING)

# Source and reading-order gates. lint-prose and lint-agda take --staged; here they
# sweep the tree. check-glossary needs tomllib, so it wants the venv's 3.11.
# --check makes a gate a gate: without it these report and exit 0.
lint:
	$(PY) scripts/gate/lint-prose.py --check
	$(PY) scripts/gate/lint-agda.py --check
	$(PY) scripts/gate/check-glossary.py --check
	$(PY) scripts/gate/check-fences.py --check
	$(PY) scripts/gate/check-reading-order.py
	$(PY) scripts/site/weave-i18n.py --check

test:
	$(PY) -m unittest discover -s scripts/tests -p "test_*.py" -t scripts/tests -v

hooks:
	install -m 755 scripts/git-hooks/pre-commit .git/hooks/pre-commit
	@echo "pre-commit installed; bypass one commit with --no-verify"

venv:
	$(PYTHON) -m venv $(VENV)
	$(PY) -m pip install -q -r requirements-dev.txt

gen:
	$(PY) scripts/site/weave-i18n.py --gen --out _build/woven

html:
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(EVERYTHING)

types:
	$(PY) scripts/site/extract-types.py --html-dir $(HTML_DIR) --out _build/types.json

site: html types
	$(PY) scripts/site/render-site.py --html-dir $(HTML_DIR) --out $(SITE_OUT) \
		--langs $(LANGS) --base-url "$(BASE_URL)"
	$(PY) scripts/site/gen-depmap.py --src src --out $(SITE_OUT) --langs $(LANGS)

serve:
	$(PY) -m http.server $(PORT) --directory $(SITE_OUT)

deploy: site
	npx wrangler pages deploy $(SITE_OUT) --project-name=$(CF_PROJECT)

clean:
	rm -rf $(HTML_DIR) $(SITE_OUT) _build/woven _build/types.json
