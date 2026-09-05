#!/bin/sh
# LJ-1.290: run every checker that does NOT invoke Agda, in a tree given as $1,
# and print one line per checker: NAME EXIT NLINES FIRSTLINE.
# It never runs `agda`, `make check`, or `deletion-test.py --run`.
# $2 is the subdirectory prefix under scripts/ (empty for the flat layout).
ROOT="$1"
PY=/Users/alsg/Agentic/Bedrock/.venv/bin/python
cd "$ROOT" || exit 2

run() {                       # run <label> <relative-script-path> [args...]
  label="$1"; shift
  script="$1"; shift
  if [ ! -f "$script" ]; then
    printf '%-26s %-4s %-6s %s\n' "$label" "MISS" "-" "no file at $script"
    return
  fi
  out=$("$PY" "$script" "$@" 2>&1)
  code=$?
  n=$(printf '%s' "$out" | wc -l | tr -d ' ')
  first=$(printf '%s' "$out" | head -1 | cut -c1-90)
  printf '%-26s %-4s %-6s %s\n' "$label" "$code" "$n" "$first"
}

P="$2"                        # "" for flat, e.g. "gate/" for a subdirectory
G="scripts/${P}"

run rules-check        "${G}rules.py" --check
run rule-ids           "${G}check-rule-ids.py"
run dev-docs           "${G}check-dev-docs.py"
run task-index         "${G}check-task-index.py"
run dd4-stated         "${G}check-dd4-stated.py"
run dd25-review        "${G}check-dd25-review-named.py"
run premises           "${G}check-premises-stated.py"
run archive-cited      "${G}check-archive-cited.py"
run dispatch-policy    "${G}check-dispatch-policy.py"
run build-manifest     "${G}check-build-manifest.py" --check
run fences             "${G}check-fences.py" --check
run probes             "${G}check-probes.py" --check
run tree               "${G}check-tree.py" --check
run ledger-check       "${G}ledger.py" --check
run ledger-brief       "${G}ledger.py" --brief
run lint-prose         "${G}lint-prose.py" --check
run lint-agda          "${G}lint-agda.py" --check
run glossary           "${G}check-glossary.py" --check
run markers            "${G}weave-i18n.py" --check
run live-territory     "${G}check-live-territory.py" --check
run dispatch-policy-cli "${G}dispatch_policy.py"
run dd25-record        "${G}dd25-record.py"
run agents-guard       "${G}check-agents-guard.py"
run unbound-hyp        "${G}check-unbound-hyp.py"
run deletion-shadow    "${G}deletion-test.py"
