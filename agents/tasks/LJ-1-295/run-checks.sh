#!/bin/sh
# LJ-1.295 baseline/after harness. Runs every checker that make check wires
# in, plus the no-Agda advisory tools and all 16 test suites, INDIVIDUALLY
# (the brief forbids make check and Agda). Captures stdout, stderr, exit code
# per name into $1/ (baseline/ or after/), plus an env snapshot.
# Usage: run-checks.sh <outdir>

set -u
OUT="$1"
mkdir -p "$OUT"
PY=.venv/bin/python
[ -x "$PY" ] || PY=python3

run() {
	name="$1"; shift
	"$@" >"$OUT/$name.out" 2>"$OUT/$name.err"
	echo $? >"$OUT/$name.exit"
}

{
	echo "date: $(date '+%F %T')"
	echo "head: $(git rev-parse HEAD)"
	echo "tracked: $(git ls-files | wc -l | tr -d ' ')"
	echo "porcelain: $(git status --porcelain | wc -l | tr -d ' ')"
	git status --porcelain | head -50
} >"$OUT/env.txt"

# The 20 python invocations make check wires in (Makefile check: line), in
# target order, then the no-Agda extras.
run markers    "$PY" scripts/site/weave-i18n.py --check
run lint       "$PY" scripts/gate/lint-prose.py --check
run lintagda   "$PY" scripts/gate/lint-agda.py --check
run glossary   "$PY" scripts/gate/check-glossary.py --check
run ledger     "$PY" scripts/measure/ledger.py --check
run probes     "$PY" scripts/gate/check-probes.py --check
run liveterr   "$PY" scripts/gate/check-live-territory.py --staged
run tree       "$PY" scripts/gate/check-tree.py --check
run fences     "$PY" scripts/gate/check-fences.py --check
run ruleids    "$PY" scripts/gate/check-rule-ids.py
run rules      "$PY" scripts/dispatch/rules.py --check
run devdocs    "$PY" scripts/gate/check-dev-docs.py
run taskindex  "$PY" scripts/gate/check-task-index.py
run agentsguard "$PY" scripts/gate/check-agents-guard.py
run dispatchpolicy "$PY" scripts/dispatch/check-dispatch-policy.py
run dd4        "$PY" scripts/gate/check-dd4-stated.py
run dd25       "$PY" scripts/gate/check-dd25-review-named.py
run premises   "$PY" scripts/gate/check-premises-stated.py
run buildmanifest "$PY" scripts/gate/check-build-manifest.py --check
run archivecited "$PY" scripts/gate/check-archive-cited.py
# Extras: no Agda, not all gated.
run ledgerbrief "$PY" scripts/measure/ledger.py --brief
run unboundhyp "$PY" scripts/measure/check-unbound-hyp.py
run switch     "$PY" scripts/dispatch/dispatch_policy.py
run sourcesread "$PY" scripts/dispatch/check-sources-read.py --all

# All 16 suites, individually.
run suite-01 "$PY" scripts/tests/test_i18n.py
run suite-02 "$PY" scripts/tests/test_glossary.py
run suite-03 "$PY" scripts/tests/test_lint_agda.py
run suite-04 "$PY" scripts/tests/test_dev_docs.py
run suite-05 "$PY" scripts/tests/test_obligations.py
run suite-06 "$PY" scripts/tests/test_task_index.py
run suite-07 "$PY" scripts/tests/test_probe_gate.py
run suite-08 "$PY" scripts/tests/test_deletion_test.py
run suite-09 "$PY" scripts/tests/test_ratio_baseline.py
run suite-10 "$PY" scripts/tests/test_rule_series.py
run suite-11 "$PY" scripts/tests/test_agents_tree.py
run suite-12 "$PY" scripts/tests/test_archive_layout.py
run suite-13 "$PY" scripts/tests/test_dd25_review_named.py
run suite-14 "$PY" scripts/tests/test_premises_stated.py
run suite-15 "$PY" scripts/tests/test_ratio_noise.py
run suite-16 "$PY" scripts/tests/test_dispatch_clock.py

echo "captured $(ls "$OUT" | wc -l | tr -d ' ') files into $OUT"
