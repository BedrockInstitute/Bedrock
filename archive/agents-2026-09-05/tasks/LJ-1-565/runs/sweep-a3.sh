#!/bin/sh
# [LJ-1.565] attempt 3.  THE ACCEPTANCE-EQUIVALENT SWEEP.
#
# `scripts/pod/facts.py:462-466` makes EVERY `.agda` file under
# `agents/tasks/<CODE>/` a verification target, in path order, and
# conjunct 1 stops at the first non-zero.  This script runs exactly that
# list, COLD (P-p, dev/LESSONS.md:2722: move the `.agdai` before you
# believe a price), ONE Agda process at a time.
#
# It sets no GHCRTS.  The program set the pane's caliber.
set -e
cd "$(dirname "$0")/../../../.."
R=agents/tasks/LJ-1-565
B=_build/2.8.0/agda
for t in "$R/Probe565.agda" $(ls -1 $R/runs/*.agda | sort); do
  n=$(basename "$t" .agda)
  rm -f "$B/${t%.agda}.agdai"
  printf '%-18s ' "$n"
  if /usr/bin/time -l agda "$t" >"$R/runs/a3-$n.out" 2>"$R/runs/a3-$n.time"; then
    printf 'rc 0   %s\n' "$(grep -o '[0-9.]* real' "$R/runs/a3-$n.time" | head -1)"
  else
    printf 'rc %s  FAILED\n' "$?"
  fi
done
