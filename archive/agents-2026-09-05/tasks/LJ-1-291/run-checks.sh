#!/bin/sh
# LJ-1.291 harness: run every Agda-free checker and test suite, capture outputs.
# Usage: run-checks.sh <outdir>   (outdir is baseline/ or after/ beside this file)
set -u
ROOT=$(git rev-parse --show-toplevel)
PY="$ROOT/.venv/bin/python"
OUT="$1"
mkdir -p "$OUT"
cd "$ROOT" || exit 99

run() {  # run <name> <script-relative-path> [args...]
  name="$1"; shift
  "$PY" "scripts/$@" >"$OUT/$name.out" 2>"$OUT/$name.err"
  echo "$?" >"$OUT/$name.exit"
}

# --- the python checkers wired into `make check` (Makefile:36), typecheck/venv/reuse apart
run markers        weave-i18n.py            --check
run lint           lint-prose.py            --check
run lint-agda      lint-agda.py             --check
run glossary       check-glossary.py        --check
run ledger         ledger.py                --check
run probes         check-probes.py          --check
run liveterritory  check-live-territory.py  --staged
run tree           check-tree.py            --check
run fences         check-fences.py          --check
run ruleids-a      check-rule-ids.py
run ruleids-b      rules.py                 --check
run devdocs        check-dev-docs.py
run taskindex      check-task-index.py
run agentsguard    check-agents-guard.py
run dispatchpolicy check-dispatch-policy.py
run dd4            check-dd4-stated.py
run dd25           check-dd25-review-named.py
run premises       check-premises-stated.py
run buildmanifest  check-build-manifest.py  --check
run archivecited   check-archive-cited.py

# --- edited scripts that sit OUTSIDE `make check` and run without Agda
run sources-read   check-sources-read.py
run unbound-hyp    check-unbound-hyp.py
run dd25-record    dd25-record.py           --help

# --- the 16 test suites (Makefile wires 13; the tree holds 16)
i=1
for t in scripts/tests/test_*.py; do
  n=$(printf "%02d" "$i")
  "$PY" "$t" >"$OUT/suite-$n-$(basename "$t" .py).out" 2>"$OUT/suite-$n-$(basename "$t" .py).err"
  echo "$?" >"$OUT/suite-$n-$(basename "$t" .py).exit"
  i=$((i + 1))
done

# --- environment snapshot, so an external drift can be attributed
{
  echo "date: $(date)"
  echo "tracked files: $(git ls-files | wc -l | tr -d ' ')"
  echo "git head: $(git rev-parse HEAD)"
  git status --porcelain | sort
  echo "--- sha256 of every .md under agents/tasks (live tree)"
  find agents/tasks -name "*.md" -not -name "*.lagda.md" -exec sh -c 'sha256 -r "$1"' _ {} \; | sort
  echo "--- live python/agda processes"
  ps ax -o pid,lstart,command | grep -E "python|agda|pi " | grep -v grep
} >"$OUT/env.txt" 2>&1

echo "wrote $OUT"
