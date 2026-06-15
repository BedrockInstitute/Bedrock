# Bedrock build orchestration.
#
#   make check   typecheck the masters + prose lint + marker + glossary integrity (the gate)
#   make site    build the multilingual hyperlinked site into _build/site
#   make serve   preview the built site locally
#   make gen     weave per-language mono-lingual .lagda.md (agda --html compatibility)
#   make hooks   activate the version-controlled git pre-commit hook
#
# Type-checking/linting need only Agda + Python; the site build also needs them (no node,
# no GHC). Math fonts and KaTeX load from a CDN at view time. Everything generated lives
# under _build/ (git-ignored).

AGDA      := agda
PY        := python3
EVERYTHING := src/Everything.lagda.md
HTML_DIR  := _build/html
SITE_OUT  := _build/site
LANGS     := en,zh
BASE_URL  :=
PORT      := 8000
CF_PROJECT := bedrock

.PHONY: check typecheck lint markers glossary gen html types site serve clean hooks test deploy

check: typecheck markers lint glossary

typecheck:
	$(AGDA) $(EVERYTHING)

lint:
	$(PY) scripts/lint-prose.py --check

markers:
	$(PY) scripts/weave-i18n.py --check

glossary:
	$(PY) scripts/check-glossary.py --check

gen:
	$(PY) scripts/weave-i18n.py --gen --out _build/woven

html:
	$(AGDA) --html --html-highlight=code --html-dir=$(HTML_DIR) $(EVERYTHING)

types:
	$(PY) scripts/extract-types.py --out _build/types.json

site: html types
	$(PY) scripts/render-site.py --html-dir $(HTML_DIR) --out $(SITE_OUT) \
		--langs $(LANGS) --base-url "$(BASE_URL)"

serve:
	@echo "Serving $(SITE_OUT) at http://localhost:$(PORT)/ (Ctrl-C to stop)"
	cd $(SITE_OUT) && $(PY) -m http.server $(PORT)

# Deploy the site (built at domain root) to Cloudflare Pages. Needs `wrangler login`
# or CLOUDFLARE_API_TOKEN + CLOUDFLARE_ACCOUNT_ID in the environment.
deploy: site
	npx wrangler pages deploy $(SITE_OUT) --project-name=$(CF_PROJECT)

test:
	$(PY) scripts/tests/test_i18n.py
	$(PY) scripts/tests/test_glossary.py

clean:
	rm -rf _build

hooks:
	git config --local core.hooksPath scripts/git-hooks
	@echo "pre-commit hook activated (core.hooksPath = scripts/git-hooks)"
