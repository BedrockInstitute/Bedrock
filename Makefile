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

.PHONY: check typecheck lint lint-agda markers glossary ledger probes liveterritory tree reuse ruleids taskindex devdocs agentsguard archivecited buildmanifest dd4 dd25 dd18survey baselinehome dispatchpolicy fences liverecord premises ratio timing gen html types site serve clean hooks test deploy venv venv-check

check: venv-check typecheck markers lint lint-agda glossary ledger probes liveterritory tree fences reuse ruleids devdocs taskindex agentsguard dispatchpolicy dd4 dd25 premises buildmanifest archivecited dd18survey baselinehome liverecord

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
liveterritory:
# THE STAGED MODE IS THE COMMIT GATE. `--check` audits every TRACKED file, which
# stays red for the whole life of any dispatch whose report was committed once,
# and `make check` would then be red for hours for a defect already made. The
# gate's job is to refuse the NEXT sweep, so it reads the index. MEASURED
# 2026-08-14: a `git add -- agents/tasks/<CODE>/` swept a live agent's report
# skeleton into a commit, the audit mode caught it, and the staged mode is what
# would have refused it at the moment it mattered.
	$(PY) scripts/gate/check-live-territory.py --staged

tree:
	$(PY) scripts/gate/check-tree.py --check

# Agda outside a fence is invisible to Agda AND to ledger.py, so a green
# tree and a right line count both prove nothing about it. [LJ-1.41]
# reported two theorems CLOSED that sat in prose and carried four defects.
fences:
	$(PY) scripts/gate/check-fences.py --check

# A dangling rule citation reads as authority. [L3.32-T105] found one in a
# document written ABOUT rule hygiene, which is the argument for gating it.
ruleids:
	$(PY) scripts/gate/check-rule-ids.py
	$(PY) scripts/dispatch/rules.py --check

taskindex:
	$(PY) scripts/gate/check-task-index.py

agentsguard:
	$(PY) scripts/gate/check-agents-guard.py

# The head that runs a dispatch is DD17's, and since 2026-08-13 it has two
# versions with one switch selecting between them. This checks that briefs
# agree with the version in force. It cannot check which head actually RAN:
# an in-harness Opus dispatch passes through no tool at all.
dispatchpolicy:
	$(PY) scripts/dispatch/check-dispatch-policy.py

# ADVISORY, and deliberately NOT in `check`. [LJ-1.157] measured that 164 of 164
# briefs carried the ARCHIVE heading while the CONTENT decayed: after [LJ-1.94]
# only process tasks cited a retired-route file. A red gate here would buy a
# pasted citation rather than a survey, so this prints and never fails.
# The ADVISORY reports. Neither gates and both exit 0 whatever they find, by
# their own design: check-archive-cited would buy a pasted citation instead of a
# survey, and check-build-manifest cannot tell an evidence file from a stray.
# [LJ-1.197] MEASURED that build-manifest's rules were SILENT, and the cause was
# not the checker: it was in NO make target, NO hook and NO CI, so it ran only
# when a human already suspected something. A rule whose enforcement point is
# "somebody runs a command" fires after the fact. Running them inside `check`
# makes them VISIBLE at the one moment everyone looks, without making them gate.
buildmanifest:
	$(PY) scripts/gate/check-build-manifest.py --check

archivecited:
	$(PY) scripts/gate/check-archive-cited.py

# DD18's amended enforcement (owner, 2026-08-16), [LJ-1.363]. The two halves
# are deliberately unequal, and the asymmetry is DD4's own ruling that a
# count is gamed the moment it gates. B2 GATES the return side: ARCHIVE USED
# must name every archive path its brief cited, took or declined, and quote
# one line read per archived file, verified at the cited line. B1 only PRINTS
# the brief side: which briefs name none of the four corpora, and TEMPLATE
# clusters of a bullet's reason text verbatim across five briefs. The frozen
# epochs and their measured scale live in the checker's own comments; a
# report still in progress is not judged, so a live dispatch never reddens
# the commit gate. Cost: 0.6 s over 259 pairs, measured 2026-08-16.
dd18survey:
	$(PY) scripts/gate/check-dd18-survey.py

dd4:
	$(PY) scripts/gate/check-dd4-stated.py

# DD25: a negative return's index row names its review's code. The verdict
# cell announces a negative in structured words, so this is mechanical: a row
# carrying the table's vocabulary must name a review code, declare why this
# verdict is not a DD25 negative, or be frozen pre-epoch history. It cannot
# tell whether a verdict is REALLY negative, whether the review was any good,
# or fire when the return lands; the honest enforcement point is this gate.
# The measured backlog of 42 pre-epoch rows is reported and never fails.
dd25:
	$(PY) scripts/gate/check-dd25-review-named.py

# THE PREMISES GATE, [LJ-1.212], from [LJ-1.211]'s change 1. A brief that
# carries a trigger token (a fixed gate, a named shape, a measurement
# mandate, or a threshold figure with a unit) must declare its load-bearing
# premises in a `## PREMISES` section, each with a basis at `file:line`.
# The trigger table was tuned against the live briefs: the raw [LJ-1.211]
# list fires on 118 of 118, so four of its tokens are measured unworkable
# and live in the tool's table as REFUSED rows instead of gating. The
# ACTIVE set fires on 28 of 118 live briefs (23.7 percent, measured
# 2026-08-14). Those 28 are frozen pre-epoch records, reported once and
# never failed. The gate cannot tell whether a premise is true, cannot tell
# whether the basis says what the author claims, and fires at the commit or
# the gate, never at the writing moment.
premises:
	$(PY) scripts/gate/check-premises-stated.py

# THE BASELINE-HOME GATE, [LJ-1.367], born 2026-08-16. DD24's numbers live
# in dev/ledger.toml and nowhere else: a live claim names the field
# (`ac_baseline_module_rate`, `tolerance`) and a record keeps its figure with
# HISTORICAL(YYYY-MM-DD) on the line. The guarded figures are DERIVED from
# the ledger at run time, so the gate catches the next figure and not only
# today's. Pre-gate restatements are frozen and reported: 12 lines in live
# files, and every task directory at or below LJ-1-367, because a brief and
# a report are records written once.
baselinehome:
	$(PY) scripts/gate/check-baseline-home.py

# LJ-1.377: a brief answers the live record its own words implicate. A
# negative-existence claim about the record ("the probe nobody has run") is
# searched against the task index and the section 0.0 screen as they stood
# when the brief was written, and every positive row it implicates must be
# answered in a ## LIVE RECORD section, quoted or declined in writing. A
# brief naming a goal code answers the open-work list: the journal's
# one-grep cure made mechanical. Pre-gate briefs are frozen and reported
# once: 74 of 275 on 2026-08-16, median 4 duties each, never failed.
liverecord:
	$(PY) scripts/gate/check-live-record-claims.py

# The dev/ documents decay; [L3.32-T110] built the maintenance mechanism so
# the decay is found here, not by accident. Six cheap subchecks: size caps on
# AGENTS.md and PLAN cells, routing of imported LESSONS entries, the section 0
# "as of" date, memo STATUS form, and that AGENTS.md's named enforcers exist.
# It sat on `taskindex` until 2026-08-17. The on-demand sweep is NEVER a gate:
# it prints and exits 0. Run it as
#   $(PY) scripts/gate/check-dev-docs.py --sweep --sweep-paths
devdocs:
	$(PY) scripts/gate/check-dev-docs.py

# The generated dashboard was ABOLISHED by the owner on 2026-08-09. Its three
# scripts are frozen in archive/scripts/, with what they did right and the one
# thing they got wrong. The canonical figures are unchanged and are read with
# `python3 scripts/measure/ledger.py --brief`.

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
	$(PY) scripts/tests/test_dev_docs.py
	$(PY) scripts/tests/test_obligations.py
	$(PY) scripts/tests/test_task_index.py
	$(PY) scripts/tests/test_probe_gate.py
	$(PY) scripts/tests/test_deletion_test.py
	$(PY) scripts/tests/test_ratio_baseline.py
	$(PY) scripts/tests/test_rule_series.py
	$(PY) scripts/tests/test_agents_tree.py
	$(PY) scripts/tests/test_archive_layout.py
	$(PY) scripts/tests/test_scripts_layout.py
	$(PY) scripts/tests/test_dd25_review_named.py
# THE SAME DEFECT RECURRED, and the comment above was written for it. On
# 2026-08-16 four suites existed under scripts/tests/ and this target ran
# none of them: test_premises_stated (RED since check-premises-stated.py was
# routed through agents_tree, because its fixture root stopped resolving),
# test_dispatch_clock, test_quota_fallback and test_ratio_noise. Wired here.
	$(PY) scripts/tests/test_premises_stated.py
	$(PY) scripts/tests/test_dispatch_clock.py
	$(PY) scripts/tests/test_quota_fallback.py
	$(PY) scripts/tests/test_ratio_noise.py

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
